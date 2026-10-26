/**
 * Coverage probes: the target's source with a hit call at the innermost
 * place that runs whenever a mutant's code can run. The coverage pass
 * (coverage.ts) serves this text instead of the original; no mutant is
 * applied, so the tests see the original behaviour.
 *
 * A probe site is one of:
 *
 *   statement   a statement in a statement list: `;hit(n);` goes before it
 *   block       a block (a BlockStatement mutant's own span): after `{`
 *   lone        a statement that is not in a list (`if (a) return b;`):
 *               wrapped as `{;hit(n);…}`
 *   expression  an arrow's expression body, a class field value or a
 *               default value: wrapped as `(hit(n), …)`
 *
 * Each mutant takes the innermost site whose span holds its span. A site
 * that runs at least whenever the mutant's code runs over-approximates
 * coverage, which costs time but never a kill. Inserted text holds no
 * newline, so every line number in the target stays the same.
 */
import { loadToolPackage, MUTATE_FEATURE } from "../../../tool-deps/src/index.ts";
import { type AstNode, children, isAstNode } from "./ast.ts";
import type { Mutant } from "./types.ts";

// Optional peer dependency: loaded through the guard so a missing package names
// the install command instead of failing as a bare resolve error.
const { parseSync } = await loadToolPackage(
  "oxc-parser",
  MUTATE_FEATURE,
  () => import("oxc-parser")
);

export const HIT = "globalThis.__pollyMutateHit?.";

const PARSE_OPTIONS = { preserveParens: false };
const LIST_PARENTS = new Set(["Program", "BlockStatement", "StaticBlock", "TSModuleBlock"]);
const LONE_PARENTS: Record<string, readonly string[]> = {
  IfStatement: ["consequent", "alternate"],
  ForStatement: ["body"],
  ForInStatement: ["body"],
  ForOfStatement: ["body"],
  WhileStatement: ["body"],
  DoWhileStatement: ["body"],
  WithStatement: ["body"],
};
const ANONYMOUS = new Set(["FunctionExpression", "ArrowFunctionExpression", "ClassExpression"]);

type SiteKind = "statement" | "block" | "lone" | "expression";

interface Site {
  kind: SiteKind;
  start: number;
  end: number;
  /** Where `statement` and `block` probes go. */
  at: number;
}

export interface Instrumented {
  code: string;
  /** Mutant ids per probe, indexed by `probe - firstProbe`. */
  probes: string[][];
}

/** `"use strict"` and friends; a probe before one would end the directive prologue. */
function isDirective(node: AstNode | undefined): boolean {
  return node?.type === "ExpressionStatement" && typeof node["directive"] === "string";
}

function afterDirectives(statements: AstNode[], from: number): number {
  let at = from;
  for (const s of statements) {
    if (!isDirective(s)) break;
    at = s.end;
  }
  return at;
}

function inList(parent: AstNode, key: string): boolean {
  return (
    (LIST_PARENTS.has(parent.type) && key === "body") ||
    (parent.type === "SwitchCase" && key === "consequent")
  );
}

/** A statement that is not in a list; a wrapped declaration would change its scope. */
function isLone(node: AstNode, parent: AstNode, key: string): boolean {
  return (
    (LONE_PARENTS[parent.type]?.includes(key) ?? false) &&
    node.type !== "BlockStatement" &&
    !node.type.endsWith("Declaration")
  );
}

function isWrappedValue(node: AstNode, parent: AstNode, key: string): boolean {
  const value =
    (parent.type === "ArrowFunctionExpression" &&
      key === "body" &&
      parent["expression"] === true) ||
    ((parent.type === "PropertyDefinition" || parent.type === "AccessorProperty") &&
      key === "value") ||
    (parent.type === "AssignmentPattern" && key === "right");
  // `x = () => {}` names the function "x"; a comma expression would drop the name.
  const named = parent.type !== "ArrowFunctionExpression" && ANONYMOUS.has(node.type);
  return value && !named;
}

/** The sites `node` offers, given the key it hangs under in `parent`. */
function sitesOf(node: AstNode, parent: AstNode | undefined, key: string): Site[] {
  const sites: Site[] = [];
  const span = { start: node.start, end: node.end };
  if (node.type === "BlockStatement" || node.type === "StaticBlock") {
    sites.push({
      kind: "block",
      ...span,
      at: afterDirectives(children(node, "body"), node.start + 1),
    });
  }
  if (!parent) return sites;
  if (inList(parent, key)) {
    // A directive's own probe goes after it, where it cannot end the prologue.
    sites.push({ kind: "statement", ...span, at: isDirective(node) ? node.end : node.start });
  } else if (isLone(node, parent, key)) {
    sites.push({ kind: "lone", ...span, at: node.start });
  } else if (isWrappedValue(node, parent, key)) {
    sites.push({ kind: "expression", ...span, at: node.start });
  }
  return sites;
}

function collectSites(program: AstNode): Site[] {
  const sites: Site[] = [];
  const visit = (node: AstNode, parent: AstNode | undefined, key: string) => {
    sites.push(...sitesOf(node, parent, key));
    for (const [k, value] of Object.entries(node)) {
      const list = Array.isArray(value) ? value : [value];
      for (const c of list) if (isAstNode(c)) visit(c, node, k);
    }
  };
  for (const s of children(program, "body")) visit(s, program, "body");
  return sites;
}

/** The innermost site holding `[start, end)`; null for a span no site holds. */
function innermost(sites: readonly Site[], start: number, end: number): Site | null {
  let best: Site | null = null;
  for (const s of sites) {
    if (s.start > start || s.end < end) continue;
    if (!best || s.end - s.start < best.end - best.start) best = s;
    // A block mutant spans its block: its probe is the block's own, not the statement's.
    else if (s.end - s.start === best.end - best.start && s.kind === "block") best = s;
  }
  return best;
}

interface Edit {
  at: number;
  text: string;
  /** Closing text sorts before opening text at one offset; then by nesting. */
  order: [number, number];
}

function edits(site: Site, probe: number): Edit[] {
  const hit = `${HIT}(${probe})`;
  const open = (text: string): Edit => ({ at: site.at, text, order: [1, -site.end] });
  const close = (text: string): Edit => ({ at: site.end, text, order: [0, -site.start] });
  switch (site.kind) {
    case "statement":
    case "block":
      return [open(`;${hit};`)];
    case "lone":
      return [open(`{;${hit};`), close("}")];
    case "expression":
      return [open(`(${hit},`), close(")")];
  }
}

function applyEdits(src: string, all: Edit[]): string {
  all.sort((a, b) => a.at - b.at || a.order[0] - b.order[0] || a.order[1] - b.order[1]);
  let out = "";
  let from = 0;
  for (const e of all) {
    out += src.slice(from, e.at) + e.text;
    from = e.at;
  }
  return out + src.slice(from);
}

/**
 * Probe calls numbered from `firstProbe`. Null when the result does not
 * parse (the target then keeps static selection).
 */
export function instrument(
  file: string,
  src: string,
  mutants: readonly Mutant[],
  firstProbe: number
): Instrumented | null {
  const parsed = parseSync(file, src, PARSE_OPTIONS);
  if (parsed.errors.length > 0 || !isAstNode(parsed.program)) return null;
  const sites = collectSites(parsed.program);
  const bySite = new Map<Site, string[]>();
  for (const m of mutants) {
    const site = innermost(sites, m.start, m.end);
    if (!site) return null;
    bySite.set(site, [...(bySite.get(site) ?? []), m.id]);
  }
  const probes: string[][] = [];
  const all: Edit[] = [];
  for (const [site, ids] of bySite) {
    all.push(...edits(site, firstProbe + probes.length));
    probes.push(ids);
  }
  const code = applyEdits(src, all);
  if (parseSync(file, code, PARSE_OPTIONS).errors.length > 0) return null;
  return { code, probes };
}
