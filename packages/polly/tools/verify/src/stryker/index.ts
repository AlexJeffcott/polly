// Stryker mutation-testing ignorer for polly's verify primitives (polly#143).
//
// `requires`, `ensures`, `invariant`, `stateConstraint`, `forAllPeers`, and
// `somePeer` are runtime no-ops: in production they compile away, in
// verification they translate to TLA+ assertions. Nothing observes their
// condition or message argument at test runtime, so EVERY mutation inside one
// of these callsites is guaranteed to survive — a string-literal flip in an
// `ensures(...)` message, an `===` → equality mutation in a `requires(...)`
// condition. On a downstream project mutating six state-machine specs this
// dragged the mutation score down to 21%, all of it noise rather than real
// test-coverage gaps.
//
// Polly is the right place to ship this knowledge: it knows which of its
// primitives are no-ops. This module is a Stryker `Ignore` plugin that marks
// every mutant inside a verify callsite as ignored, plus a small config preset
// consumers can spread into their `stryker.conf.*`.
//
// Usage (stryker.conf.json):
//
//   {
//     "plugins": ["@fairfox/polly/stryker"],
//     "ignorers": ["polly-verify"]
//   }
//
// Or, in stryker.conf.mjs:
//
//   import pollyStrykerPreset from "@fairfox/polly/stryker";
//   export default { ...pollyStrykerPreset, mutate: ["src/**/*.ts"] };
//
// Set `"polly": { "excludeVerifyCallsites": false }` to keep the plugin listed
// but disable the ignoring (e.g. in a shared base config).

import type { StrykerOptions } from "@stryker-mutator/api/core";
import type { Ignorer, NodePath } from "@stryker-mutator/api/ignore";
import {
  commonTokens,
  declareFactoryPlugin,
  PluginKind,
  tokens,
} from "@stryker-mutator/api/plugin";

/**
 * The polly verify primitives whose argument expressions are runtime no-ops.
 * A mutation anywhere inside a call to one of these cannot be killed by a test,
 * so its mutants are excluded from scoring.
 */
export const VERIFY_PRIMITIVES: ReadonlySet<string> = new Set([
  "requires",
  "ensures",
  "invariant",
  "stateConstraint",
  "forAllPeers",
  "somePeer",
]);

/** The Stryker plugin name consumers reference in `ignorers`. */
export const POLLY_VERIFY_IGNORER_NAME = "polly-verify";

// The Stryker API types `NodePath` as an empty interface; at runtime it is a
// Babel NodePath. We narrow only the surface we touch — `isCallExpression()`
// and `node.callee` — without pulling in @babel/types as a dependency.
interface BabelIdentifier {
  type: "Identifier";
  name: string;
}
interface BabelMemberExpression {
  type: "MemberExpression";
  computed: boolean;
  property: { type: string; name?: string };
}
type BabelCallee = BabelIdentifier | BabelMemberExpression | { type: string };
interface CallExpressionPath extends NodePath {
  isCallExpression(): boolean;
  node: { callee?: BabelCallee };
}

/**
 * Resolve the simple name of a call's callee, covering both a bare call
 * (`ensures(...)`) and a member call (`verify.ensures(...)` / `polly.ensures(...)`).
 * Computed member access (`obj["ensures"](...)`) is intentionally not matched —
 * it cannot be resolved statically and is not a pattern polly emits.
 */
function calleeName(callee: BabelCallee | undefined): string | undefined {
  if (!callee) return undefined;
  if (callee.type === "Identifier") {
    return (callee as BabelIdentifier).name;
  }
  if (callee.type === "MemberExpression") {
    const member = callee as BabelMemberExpression;
    if (!member.computed && member.property.type === "Identifier") {
      return member.property.name;
    }
  }
  return undefined;
}

/**
 * A Stryker `Ignore` plugin. Stryker calls `shouldIgnore` on entering each AST
 * node; returning a message marks that node — and every descendant, until the
 * node is left — as ignored. So matching the verify `CallExpression` itself
 * covers its condition and message arguments in one shot.
 */
export class PollyVerifyIgnorer implements Ignorer {
  constructor(private readonly primitives: ReadonlySet<string> = VERIFY_PRIMITIVES) {}

  shouldIgnore(path: NodePath): string | undefined {
    const callPath = path as CallExpressionPath;
    if (typeof callPath.isCallExpression !== "function" || !callPath.isCallExpression()) {
      return undefined;
    }
    const name = calleeName(callPath.node.callee);
    if (name && this.primitives.has(name)) {
      return (
        `Inside polly's ${name}(...) — a runtime no-op (compiled away in production, ` +
        `translated to a TLA+ assertion in verification). No test can observe or kill ` +
        `mutations here, so they are excluded from the score (polly#143).`
      );
    }
    return undefined;
  }
}

/** Reads `polly.excludeVerifyCallsites` (default: enabled) off Stryker options. */
function isEnabled(options: StrykerOptions): boolean {
  const polly = (options as { polly?: { excludeVerifyCallsites?: boolean } }).polly;
  return polly?.excludeVerifyCallsites !== false;
}

// When disabled the plugin still loads but ignores nothing, so a shared config
// can list it unconditionally and individual projects opt out via options.
const NOOP_IGNORER: Ignorer = { shouldIgnore: () => undefined };

function pollyVerifyIgnorerFactory(options: StrykerOptions): Ignorer {
  return isEnabled(options) ? new PollyVerifyIgnorer() : NOOP_IGNORER;
}
pollyVerifyIgnorerFactory.inject = tokens(commonTokens.options);

/** The plugin array Stryker reads when this module is listed in `plugins`. */
export const strykerPlugins = [
  declareFactoryPlugin(PluginKind.Ignore, POLLY_VERIFY_IGNORER_NAME, pollyVerifyIgnorerFactory),
];

/**
 * A partial Stryker config that wires up the ignorer. Spread it into a
 * `stryker.conf.mjs` default export, or replicate its two keys in JSON.
 */
export const pollyStrykerPreset = {
  plugins: ["@fairfox/polly/stryker"],
  ignorers: [POLLY_VERIFY_IGNORER_NAME],
} as const;

// biome-ignore lint/style/noDefaultExport: ergonomic `import preset from "@fairfox/polly/stryker"`
export default pollyStrykerPreset;
