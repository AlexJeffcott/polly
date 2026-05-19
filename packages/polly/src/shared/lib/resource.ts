/**
 * $resource — Async signal primitive that separates sync dependency tracking from async work.
 *
 * Reactive signal dependency tracking breaks at `await` boundaries. When a `computed()` or
 * `effect()` hits an `await`, JavaScript suspends the function and the tracking context is
 * lost. Signal reads after the `await` are silently dropped from the dependency graph.
 *
 * `$resource` solves this by splitting the problem:
 * - `source` is a synchronous function whose signal reads are fully tracked
 * - `fetcher` is an async function that receives source output — no signal access needed
 *
 * For verification, `$resource` emits three synthetic state machine transitions:
 * - `{name}_FetchStart`: source deps available, triggers loading
 * - `{name}_FetchSuccess`: fetch resolved, data updated
 * - `{name}_FetchError`: fetch rejected, error captured
 *
 * @example
 * ```ts
 * const todos = $resource("todos", {
 *   source: () => ({ userId: authState.value.userId }),
 *   fetcher: async ({ userId }) => {
 *     const res = await fetch(`/api/todos?userId=${userId}`);
 *     return await res.json();
 *   },
 *   initialValue: [],
 * });
 *
 * todos.data    // Signal<Todo[]>
 * todos.status  // Signal<"idle" | "loading" | "success" | "error">
 * todos.error   // Signal<Error | undefined>
 * todos.refetch()
 * ```
 */

import { effect, type Signal, signal } from "@preact/signals";
import { deepEqual } from "./state";

export type ResourceStatus = "idle" | "loading" | "success" | "error";

export type ResourceOptions<TSource, TData> = {
  /** Synchronous function that reads signals. Fully tracked by the reactivity system. */
  source: () => TSource;
  /** Async function that receives source output. Must not read any signals. */
  fetcher: (source: TSource) => Promise<TData>;
  /** Initial data value before first fetch completes. */
  initialValue: TData;
};

export type Resource<TData> = {
  /** The fetched data (or initialValue before first successful fetch). */
  data: Signal<TData>;
  /** Current lifecycle status: idle → loading → success | error. */
  status: Signal<ResourceStatus>;
  /** The error from the most recent failed fetch, or undefined. */
  error: Signal<Error | undefined>;
  /** Re-run the fetcher with the current source values. */
  refetch: () => void;
};

export function $resource<TSource, TData>(
  _name: string,
  options: ResourceOptions<TSource, TData>
): Resource<TData> {
  const { source, fetcher, initialValue } = options;

  const data = signal<TData>(initialValue);
  const status = signal<ResourceStatus>("idle");
  const error = signal<Error | undefined>(undefined);

  let generation = 0;
  let lastSource: TSource | undefined;

  function runFetch(sourceValue: TSource) {
    const thisGeneration = ++generation;
    status.value = "loading";
    error.value = undefined;

    fetcher(sourceValue).then(
      (result) => {
        if (thisGeneration !== generation) return; // stale
        data.value = result;
        status.value = "success";
        error.value = undefined;
      },
      (err) => {
        if (thisGeneration !== generation) return; // stale
        status.value = "error";
        error.value = err instanceof Error ? err : new Error(String(err));
      }
    );
  }

  // Track source synchronously — when source output changes, call fetcher
  effect(() => {
    const sourceValue = source();

    if (lastSource !== undefined && deepEqual(lastSource, sourceValue)) {
      return;
    }
    lastSource = sourceValue;
    runFetch(sourceValue);
  });

  function refetch() {
    if (lastSource !== undefined) {
      runFetch(lastSource);
    }
  }

  return { data, status, error, refetch };
}
