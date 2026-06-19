/**
 * The step-binding registry and matcher.
 *
 * `defineStep()` is the consumer-facing keystone: one call registers a binding
 * that the runner executes (`given`/`when`/`then`) AND the verify extractor
 * reads (`message`/`stateExpr`). `defineWorld()` records how to build and
 * cold-reset the real-factory world.
 *
 * Patterns use a small Cucumber-expression subset: `{string}`, `{int}`,
 * `{float}`, `{word}`. Everything else is matched literally. That covers
 * declarative steps without dragging in the full cucumber-expressions library.
 *
 * The registry lives on `globalThis`, not in a module-level array, on purpose:
 * `polly bdd` ships as two bundles (the CLI and the `@fairfox/polly/bdd`
 * library export). `build-lib` runs with `splitting: false`, so this module is
 * *inlined separately into each bundle* — a module-level array would give the
 * runner and the consumer's `defineWorld` two different registries. A single
 * global slot is the standard cross-bundle-singleton fix.
 */
import type { StepBinding, StepKeyword, WorldDef } from "./types.ts";

interface CompiledBinding {
  binding: StepBinding;
  regex: RegExp;
}

interface RegistryState {
  bindings: CompiledBinding[];
  worldDef: WorldDef | null;
}

declare global {
  // An ambient global declaration — `var` is the only legal form here.
  var __pollyBddRegistry__: RegistryState | undefined;
}

function state(): RegistryState {
  globalThis.__pollyBddRegistry__ ??= { bindings: [], worldDef: null };
  return globalThis.__pollyBddRegistry__;
}

/** Translate a Cucumber-expression pattern into an anchored RegExp. */
export function compilePattern(pattern: string): RegExp {
  // Escape regex metacharacters, then re-introduce capture groups for {tokens}.
  const escaped = pattern.replace(/[.*+?^${}()|[\]\\]/g, "\\$&");
  const withGroups = escaped
    // {string} — double- or single-quoted; capture the inner text. The
    // alternation MUST be wrapped in a non-capturing group, or the `|` would
    // bind to the whole pattern and shatter any step with two+ tokens.
    .replace(/\\\{string\\\}/g, `(?:"([^"]*)"|'([^']*)')`)
    .replace(/\\\{int\\\}/g, "([-+]?\\d+)")
    .replace(/\\\{float\\\}/g, "([-+]?\\d*\\.?\\d+)")
    .replace(/\\\{word\\\}/g, "([^\\s]+)");
  return new RegExp(`^${withGroups}$`);
}

export function defineStep(binding: StepBinding): void {
  state().bindings.push({ binding, regex: compilePattern(binding.pattern) });
}

export function defineWorld(def: WorldDef): void {
  state().worldDef = def;
}

export function getWorldDef(): WorldDef | null {
  return state().worldDef;
}

/** Drop all registrations — used between isolated runs/tests. */
export function resetRegistry(): void {
  const s = state();
  s.bindings.length = 0;
  s.worldDef = null;
}

export interface StepMatch {
  binding: StepBinding;
  args: string[];
}

/**
 * Find the binding whose pattern matches `text`. Captured groups become the
 * step arguments (the `{string}` alternation yields two groups per token, so
 * we drop the undefined half).
 *
 * When `keyword` is given, a binding that *has* the callback for that keyword
 * wins over one that merely matches the text — so the same phrase can serve as
 * a `given` precondition in one scenario and a `then` assertion in another.
 */
export function matchStep(text: string, keyword?: StepKeyword): StepMatch | null {
  let textOnlyFallback: StepMatch | null = null;
  for (const { binding, regex } of state().bindings) {
    const m = regex.exec(text);
    if (!m) continue;
    const args = m.slice(1).filter((g) => g !== undefined);
    if (!keyword || binding[keyword]) return { binding, args };
    textOnlyFallback ??= { binding, args };
  }
  return textOnlyFallback;
}

/** Snapshot of all registered bindings (for the verify extractor). */
export function registeredBindings(): StepBinding[] {
  return state().bindings.map((c) => c.binding);
}
