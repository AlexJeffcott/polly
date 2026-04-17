/**
 * Form primitive.
 *
 * `createForm` returns a typed form store: per-field signals, an aggregated
 * values signal, open/close/submit methods, and three auto-registered action
 * handlers (`{name}:open`, `{name}:close`, `{name}:submit`) that callers spread
 * into their global action registry.
 *
 * Lifecycle:
 *   open  → resets fields to initialValues, applies onOpen overrides,
 *           sets isOpen = true, records data-action-* data in openParams
 *   typing → uncontrolled inputs keep their own state; controlled inputs
 *           write fields.X.value directly
 *   submit → reads FormData from the form element, merges into fields,
 *           runs optional validate, calls user onSubmit with final values,
 *           closes on success, sets errorState on failure
 *   close  → resets and sets isOpen = false
 *   guard  → autonomous effect; if guard() returns false while open, close()
 */

import {
  computed,
  effect,
  type ReadonlySignal,
  type Signal,
  signal,
} from "@preact/signals";
import { submitError } from "./error.ts";
import type { ActionRegistry } from "./registry.ts";

function isFormElement(target: EventTarget | null): target is HTMLFormElement {
  if (!target) return false;
  if (typeof HTMLFormElement !== "undefined") {
    return target instanceof HTMLFormElement;
  }
  const t = target as unknown as { tagName?: unknown };
  return typeof t.tagName === "string" && t.tagName === "FORM";
}

export type FormOpenContext<TStores> = {
  data: Record<string, string>;
  stores: TStores;
};

export type FormSubmitContext<TValues, TStores> = {
  values: TValues;
  stores: TStores;
};

export type FormConfig<TValues extends Record<string, string>, TStores> = {
  /** Used as action namespace: `{name}:open`, `{name}:close`, `{name}:submit`. */
  name: string;
  initialValues: TValues;
  onSubmit: (
    ctx: FormSubmitContext<TValues, TStores>,
  ) => void | Promise<void>;
  /** Invoked on open; return partial overrides to pre-populate fields. */
  onOpen?: (ctx: FormOpenContext<TStores>) => Partial<TValues> | void;
  /** Returns false while open → form auto-closes (entity-deletion guard). */
  guard?: (ctx: { stores: TStores }) => boolean;
  /** Synchronous validation. Returning keys blocks submit. */
  validate?: (
    values: TValues,
  ) => Partial<Record<keyof TValues, string>> | null;
};

export type FormStore<
  TValues extends Record<string, string>,
  TStores,
> = {
  readonly name: string;
  readonly isOpen: ReadonlySignal<boolean>;
  readonly values: ReadonlySignal<TValues>;
  readonly fields: { [K in keyof TValues]: Signal<TValues[K]> };
  readonly errors: ReadonlySignal<Partial<Record<keyof TValues, string>>>;
  readonly isSubmitting: ReadonlySignal<boolean>;
  readonly openParams: ReadonlySignal<Record<string, string>>;
  open(override?: Partial<TValues>, params?: Record<string, string>): void;
  close(): void;
  submit(event?: Event): Promise<void>;
  /** Late-binds stores; required before guard/onOpen/onSubmit can access stores. */
  bindStores(getStores: () => TStores): void;
  /** Action handler entries. Spread into the user's ActionRegistry. */
  actions: ActionRegistry<TStores>;
};

export function createForm<
  TValues extends Record<string, string>,
  TStores,
>(config: FormConfig<TValues, TStores>): FormStore<TValues, TStores> {
  const fieldKeys = Object.keys(config.initialValues) as unknown as (keyof TValues)[];

  const fields = {} as unknown as { [K in keyof TValues]: Signal<TValues[K]> };
  for (const key of fieldKeys) {
    fields[key] = signal(config.initialValues[key]);
  }

  const values = computed<TValues>(() => {
    const v = {} as unknown as TValues;
    for (const key of fieldKeys) {
      v[key] = fields[key].value;
    }
    return v;
  });

  const isOpen = signal(false);
  const isSubmitting = signal(false);
  const errors = signal<Partial<Record<keyof TValues, string>>>({});
  const openParams = signal<Record<string, string>>({});

  let getStoresRef: (() => TStores) | null = null;
  let disposeGuardEffect: (() => void) | null = null;

  function getStoresOrThrow(): TStores {
    if (!getStoresRef) {
      throw new Error(
        `Form "${config.name}" used before bindStores(). Call form.bindStores(() => yourStores) at app init.`,
      );
    }
    return getStoresRef();
  }

  function resetToInitial(): void {
    for (const key of fieldKeys) {
      fields[key].value = config.initialValues[key];
    }
    errors.value = {};
  }

  function open(
    override?: Partial<TValues>,
    params: Record<string, string> = {},
  ): void {
    resetToInitial();
    openParams.value = params;
    if (config.onOpen && getStoresRef) {
      const onOpenOverride =
        config.onOpen({ data: params, stores: getStoresOrThrow() }) ?? {};
      for (const [k, v] of Object.entries(onOpenOverride)) {
        if (k in fields) {
          fields[k as keyof TValues].value = v as TValues[keyof TValues];
        }
      }
    }
    if (override) {
      for (const [k, v] of Object.entries(override)) {
        if (k in fields) {
          fields[k as keyof TValues].value = v as TValues[keyof TValues];
        }
      }
    }
    isOpen.value = true;
  }

  function close(): void {
    isOpen.value = false;
    resetToInitial();
    openParams.value = {};
  }

  async function submit(event?: Event): Promise<void> {
    if (event) event.preventDefault();
    if (event && isFormElement(event.target)) {
      const fd = new FormData(event.target);
      for (const key of fieldKeys) {
        const raw = fd.get(key as unknown as string);
        if (raw !== null) {
          fields[key].value = String(raw) as unknown as TValues[typeof key];
        }
      }
    }
    const current = values.value;
    const validationErrors = config.validate?.(current);
    if (
      validationErrors &&
      Object.keys(validationErrors).length > 0
    ) {
      errors.value = validationErrors;
      return;
    }
    errors.value = {};
    isSubmitting.value = true;
    try {
      await config.onSubmit({
        values: current,
        stores: getStoresOrThrow(),
      });
      close();
    } catch (err) {
      submitError(`${config.name}:submit`, err);
    } finally {
      isSubmitting.value = false;
    }
  }

  function bindStores(getStores: () => TStores): void {
    getStoresRef = getStores;
    disposeGuardEffect?.();
    const guardFn = config.guard;
    if (guardFn) {
      disposeGuardEffect = effect(() => {
        if (!isOpen.value) return;
        if (!guardFn({ stores: getStores() })) close();
      });
    }
  }

  const actions: ActionRegistry<TStores> = {
    [`${config.name}:open`]: ({ data }) => {
      open(undefined, data);
    },
    [`${config.name}:close`]: () => {
      close();
    },
    [`${config.name}:submit`]: async ({ event }) => {
      await submit(event);
    },
  };

  return {
    name: config.name,
    isOpen,
    values,
    fields,
    errors,
    isSubmitting,
    openParams,
    open,
    close,
    submit,
    bindStores,
    actions,
  };
}

/**
 * Compose many forms into a single set: merged actions, closeAll, openForm signal.
 */
export type FormSet<TStores> = {
  actions: ActionRegistry<TStores>;
  openForm: ReadonlySignal<string | null>;
  closeAll(): void;
  bindStores(getStores: () => TStores): void;
};

/* eslint-disable @typescript-eslint/no-explicit-any */
export function createFormSet<TStores>(
  forms: readonly FormStore<any, TStores>[],
): FormSet<TStores> {
  const merged: ActionRegistry<TStores> = {};
  for (const form of forms) {
    Object.assign(merged, form.actions);
  }

  const openForm = computed<string | null>(() => {
    for (const form of forms) {
      if (form.isOpen.value) return form.name;
    }
    return null;
  });

  return {
    actions: merged,
    openForm,
    closeAll() {
      for (const form of forms) form.close();
    },
    bindStores(getStores) {
      for (const form of forms) form.bindStores(getStores);
    },
  };
}
/* eslint-enable @typescript-eslint/no-explicit-any */
