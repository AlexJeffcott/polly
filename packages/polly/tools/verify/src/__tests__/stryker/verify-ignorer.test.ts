// polly#143 — the Stryker ignorer must drop every mutant inside a verify
// primitive callsite (a runtime no-op) and nothing outside one. We exercise it
// against real Babel NodePaths, replicating Stryker's IgnorerBookkeeper: on
// entering a node we ask the ignorer; a returned message marks that node and
// all descendants ignored until the node is left.

import { describe, expect, test } from "bun:test";
import { parse } from "@babel/parser";
import _traverse from "@babel/traverse";
import type { Ignorer } from "@stryker-mutator/api/ignore";
import { PluginKind } from "@stryker-mutator/api/plugin";
import {
  POLLY_VERIFY_IGNORER_NAME,
  PollyVerifyIgnorer,
  pollyStrykerPreset,
  strykerPlugins,
  VERIFY_PRIMITIVES,
} from "../../stryker/index";

// @babel/traverse is CJS; the default export is the traverse function.
const traverse = (_traverse as unknown as { default?: typeof _traverse }).default ?? _traverse;

/**
 * Walk `code` and partition every string-literal value into those whose mutants
 * the ignorer would suppress vs those it would not, mirroring the bookkeeper.
 */
function partitionStringLiterals(
  code: string,
  ignorer: Ignorer
): { ignored: string[]; kept: string[] } {
  const ast = parse(code, { sourceType: "module", plugins: ["typescript"] });
  let activeNode: unknown = null;
  const ignored: string[] = [];
  const kept: string[] = [];

  traverse(ast, {
    enter(path) {
      if (!activeNode) {
        const message = ignorer.shouldIgnore(path);
        if (message) activeNode = path.node;
      }
      if (path.isStringLiteral()) {
        (activeNode ? ignored : kept).push(path.node.value);
      }
    },
    exit(path) {
      if (activeNode === path.node) activeNode = null;
    },
  });

  return { ignored, kept };
}

/**
 * Narrow a declared Stryker plugin to its factory. The runtime factory takes
 * StrykerOptions; the test feeds it minimal option objects, hence `unknown`.
 */
function hasIgnorerFactory(plugin: unknown): plugin is { factory: (options: unknown) => Ignorer } {
  return (
    typeof plugin === "object" &&
    plugin !== null &&
    "factory" in plugin &&
    typeof plugin.factory === "function"
  );
}

describe("PollyVerifyIgnorer", () => {
  const ignorer = new PollyVerifyIgnorer();

  test("ignores the exact survivors from the issue (string + operator mutants)", () => {
    // Mirrors ws-machine.ts:52/56 from polly#143.
    const code = `
      requires(wsMachine.value.state === 'connected' || wsMachine.value.state === 'error', 'pre');
      ensures(wsMachine.value.state === 'idle', 'disconnect: end idle');
      const realLogic = label === 'shown' ? 1 : 0;
    `;
    const { ignored, kept } = partitionStringLiterals(code, ignorer);

    // Everything inside requires(...)/ensures(...) is suppressed.
    expect(ignored).toContain("connected");
    expect(ignored).toContain("error");
    expect(ignored).toContain("idle");
    expect(ignored).toContain("disconnect: end idle");

    // Real production logic outside a verify call is still mutated.
    expect(kept).toContain("shown");
    expect(ignored).not.toContain("shown");
  });

  test("covers all six verify primitives", () => {
    const code = `
      requires(a === 'r');
      ensures(b === 'e');
      invariant('name', () => c === 'i');
      stateConstraint('field', () => d === 'sc');
      forAllPeers((p) => p.v === 'fap');
      somePeer((p) => p.v === 'sp');
    `;
    const { ignored } = partitionStringLiterals(code, ignorer);
    for (const marker of ["r", "e", "i", "sc", "fap", "sp"]) {
      expect(ignored).toContain(marker);
    }
  });

  test("matches member-expression calls (verify.ensures / polly.ensures)", () => {
    const code = `
      verify.ensures(x === 'member', 'msg');
      polly.requires(y === 'pre');
    `;
    const { ignored } = partitionStringLiterals(code, ignorer);
    expect(ignored).toContain("member");
    expect(ignored).toContain("msg");
    expect(ignored).toContain("pre");
  });

  test("does not ignore lookalike calls or plain code", () => {
    const code = `
      ensuresSomething(a === 'fake');
      doRequires(b === 'fake2');
      const greeting = 'hello';
      callMe('keep');
    `;
    const { ignored, kept } = partitionStringLiterals(code, ignorer);
    expect(ignored).toEqual([]);
    expect(kept).toContain("fake");
    expect(kept).toContain("fake2");
    expect(kept).toContain("hello");
    expect(kept).toContain("keep");
  });

  test("does not ignore a computed-member call obj['ensures'](...)", () => {
    const code = `obj['ensures'](z === 'computed');`;
    const { ignored, kept } = partitionStringLiterals(code, ignorer);
    expect(ignored).toEqual([]);
    expect(kept).toContain("computed");
  });

  test("shouldIgnore returns undefined for a non-call path-like object", () => {
    const notACall = { isCallExpression: () => false };
    expect(ignorer.shouldIgnore(notACall)).toBeUndefined();
  });

  test("a custom primitive set narrows what is ignored", () => {
    const onlyEnsures = new PollyVerifyIgnorer(new Set(["ensures"]));
    const code = `requires(a === 'req'); ensures(b === 'ens');`;
    const { ignored, kept } = partitionStringLiterals(code, onlyEnsures);
    expect(ignored).toContain("ens");
    expect(kept).toContain("req");
  });
});

describe("plugin + preset wiring", () => {
  test("exposes exactly one Ignore plugin named polly-verify", () => {
    expect(strykerPlugins).toHaveLength(1);
    expect(strykerPlugins[0]?.kind).toBe(PluginKind.Ignore);
    expect(strykerPlugins[0]?.name).toBe(POLLY_VERIFY_IGNORER_NAME);
  });

  test("the factory honours polly.excludeVerifyCallsites", () => {
    const plugin = strykerPlugins[0];
    if (!hasIgnorerFactory(plugin)) throw new Error("expected an Ignore plugin with a factory");
    const factory = plugin.factory;
    const code = `ensures(a === 'x');`;

    const enabled = factory({ polly: { excludeVerifyCallsites: true } });
    expect(partitionStringLiterals(code, enabled).ignored).toContain("x");

    const disabled = factory({ polly: { excludeVerifyCallsites: false } });
    expect(partitionStringLiterals(code, disabled).ignored).toEqual([]);

    // Default (no polly options) is enabled.
    const byDefault = factory({});
    expect(partitionStringLiterals(code, byDefault).ignored).toContain("x");
  });

  test("preset wires both plugins and ignorers to the same name", () => {
    expect(pollyStrykerPreset.plugins).toContain("@fairfox/polly/stryker");
    expect(pollyStrykerPreset.ignorers).toContain(POLLY_VERIFY_IGNORER_NAME);
  });

  test("VERIFY_PRIMITIVES lists the documented runtime no-ops", () => {
    expect([...VERIFY_PRIMITIVES].sort()).toEqual(
      ["ensures", "forAllPeers", "invariant", "requires", "somePeer", "stateConstraint"].sort()
    );
  });
});
