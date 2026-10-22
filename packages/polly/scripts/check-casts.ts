#!/usr/bin/env bun

/**
 * Type-assertion gate, built on the TypeScript 7.1 API (`typescript-7/async`).
 *
 *   bun scripts/check-casts.ts             # gate: exit 1 on a cast outside the baseline
 *   bun scripts/check-casts.ts --update    # rewrite casts-baseline.json from the tree
 *   bun scripts/check-casts.ts --fix       # delete every cast the compiler does not need
 *   bun scripts/check-casts.ts --probe     # probe every cast, baselined or not; print tables
 *   bun scripts/check-casts.ts --compare   # also run the regex check and diff the two
 *   bun scripts/check-casts.ts --json      # machine-readable report
 *   bun scripts/check-casts.ts --root DIR  # check another project (default: cwd)
 *
 * Policy. `as const` passes. Any other single cast (`x as T`, `<T>x`) is a
 * violation. A double cast (`x as unknown as T`) passes only when the compiler
 * needs it — `x` and `T` are not comparable, so a single `as` fails with
 * TS2352 — AND a comment on its line or the line above says why:
 * `// cast: <reason>`. A double cast the compiler does not need exists only to
 * get past this gate. One exception for single casts: a primitive cast to an
 * intersection that contains it (a branded type, `"a" as PeerId`) has no
 * alternative, so it passes with a `// cast:` comment. Put it in the brand's
 * constructor and call that, rather than marking every call site. The same
 * holds for `unknown` cast to a type parameter (`stored as T`, `T | null`):
 * at a generic deserialisation boundary nothing can test the value against
 * the caller's `T`, so a marked single cast passes.
 *
 * Hollow predicates. The compiler trusts a type predicate's body, so
 * `(x): x is T => true` is a cast without an `as`. A predicate whose every
 * `return` is the literal `true`, or whose body never mentions its parameter,
 * is a violation unless marked `// cast: <reason>`. Found by syntax; no
 * baseline, because the tree had none when the rule was added.
 *
 * Casts are found by syntax (`AsExpression` / `TypeAssertion` nodes), so a
 * cast that spans lines, or sits in an index, an array or a `${}`, is seen,
 * and ` as ` in prose, strings and comments never is.
 *
 * The probe. The 7.1 API has `isTypeAssignableTo` but not the comparability
 * relation that `as` checks; on polly, guessing from assignability was wrong
 * for 243 of 719 casts. So each cast is rewritten in a temporary snapshot
 * (`api.runWithTemporaryFileUpdate`, nothing written to disk) and the file's
 * errors are compared with the unmutated file's:
 *   remove   `x as T` → `x`. No new error: the cast is `removable`.
 *   single   `x as unknown as T` → `(x) as T`. No new error: `comparable`.
 *            A new error (TS2352): `incomparable`, the double cast is needed.
 * Only the rewritten file's diagnostics are read, and unused-binding codes are
 * ignored, since removing `as T` can leave the import of `T` unused. A removal
 * that changes an exported type and breaks an importer is not seen by the
 * probe; `--fix` runs a full typecheck pass afterwards for that reason.
 *
 * Baseline. `casts-baseline.json` lists the violations the tree had when the
 * gate was adopted, as `{ file, text }` (whitespace-collapsed cast text, so a
 * line move does not invalidate an entry). Baselined casts are not probed, so
 * the gate probes only new casts and stays fast.
 *
 * Projects. Each file is compiled under its nearest `tsconfig.json` (at or
 * below the root), through a virtual `tsconfig.casts-probe.json` beside it
 * that extends that config and lists the files, because a config's own
 * `include` misses some scanned files (`tools/` is in none) and `tests/` has
 * its own options: a removal that passes under the root options can fail
 * under `tests/tsconfig.json`.
 *
 * What the probe cannot see. Removing a cast can lose a type without any
 * error: an `any` operand fits every target, and an `any` beside the cast in a
 * `?:` / `??` / `||` / `&&` takes over the whole expression's type. A cast
 * whose operand or surrounding expression has `any` in its type is therefore
 * never `removable`; `any` is read from the printed type, so an `any` that
 * `typeToString` elides in a long type is missed. Nor can it see into a file
 * under `@ts-nocheck`, or a line under `@ts-expect-error` / `@ts-expect-error`: no
 * rewrite there produces an error, so such a cast is not probed at all.
 */

import { existsSync, readFileSync, writeFileSync } from "node:fs";
import { dirname, join, relative, resolve } from "node:path";
import { Glob } from "bun";
import type {
  ArrowFunction,
  AsExpression,
  FunctionDeclaration,
  FunctionExpression,
  MethodDeclaration,
  Node,
  SourceFile,
  TypeAssertion,
  TypePredicateNode,
} from "typescript-7/ast";
import { NodeFlags, SyntaxKind } from "typescript-7/ast";
import {
  isArrowFunction,
  isAsExpression,
  isBinaryExpression,
  isBlock,
  isConditionalExpression,
  isFunctionDeclaration,
  isFunctionExpression,
  isIdentifier,
  isMethodDeclaration,
  isParenthesizedExpression,
  isReturnStatement,
  isTypeAssertion,
  isTypePredicateNode,
  isTypeReferenceNode,
} from "typescript-7/ast/is";
import {
  API,
  type Diagnostic,
  DiagnosticCategory,
  type Snapshot,
  type Type,
  TypeFlags,
} from "typescript-7/async";
import { createFileSystemLayer } from "typescript-7/fs";
import { checkNoAsCasting } from "../tools/quality/src/no-as-casting";

const argv = process.argv.slice(2);
const args = new Set(argv);
const rootIdx = argv.indexOf("--root");
const ROOT = resolve(rootIdx >= 0 ? (argv[rootIdx + 1] ?? ".") : process.cwd());
const EXCLUDE = ["node_modules", "dist", ".git", ".bun", "examples"];
const PROBE_CONFIG = "tsconfig.casts-probe.json";
const BASELINE_PATH = `${ROOT}/casts-baseline.json`;
const UPDATE = args.has("--update");
const FIX = args.has("--fix");
const PROBE_ALL = UPDATE || FIX || args.has("--probe");
const TABLES = args.has("--probe");
const COMPARE = args.has("--compare");
const JSON_OUT = args.has("--json");

/** `noUnused*` diagnostics: removing `as T` can leave `T`'s import unused, which says nothing about the cast. */
const UNUSED_CODES = new Set([6133, 6138, 6192, 6196, 6198, 6199, 6205]);
/** `// cast: <reason>` or `/* cast: <reason>` on the cast's line or the line above. */
const JUSTIFICATION = /(?:\/\/|\/\*)\s*cast:\s*\S/;
const PRIMITIVE = TypeFlags.StringLike | TypeFlags.NumberLike | TypeFlags.BigIntLike;
/** A file the compiler does not check: no rewrite of it can produce an error. */
const NOCHECK = /^\s*\/\/\s*@ts-nocheck\b/m;
/** A line comment that hides the errors on the next line. */
const SUPPRESSION = /\/\/\s*@ts-(?:ignore|expect-error)\b/;

type Cast = AsExpression | TypeAssertion;
type Fast = "redundant" | "widening" | "narrowing" | "unrelated" | "any" | "error-type";
type Probe = "removable" | "required" | "comparable" | "incomparable";
type Status = "violation" | "baselined" | "allowed";

interface Finding {
  file: string;
  line: number;
  text: string;
  /** Baseline key text: the whole cast, whitespace collapsed. */
  key: string;
  /** `double` for `x as unknown as T`, `single` for any other cast. */
  kind: "single" | "double";
  fast: Fast;
  from: string;
  to: string;
  probe?: Probe;
  /** Codes of the new errors the probe's rewrite caused. */
  probeCodes?: number[];
  /**
   * Where an `any` (or an unresolved type) hides what removing the cast loses:
   * in the operand (`any`, `any[]`, `DocHandle<any>`) or in the expression
   * around the cast (`cond ? JSON.parse(s) : (x as T)`).
   */
  opaque?: "operand" | "context";
  /** Why the remove probe did not run or did not count. */
  blocked?: "opaque-operand" | "opaque-context" | "changes-exports" | "unchecked";
  /** `@ts-nocheck` on the file, or `@ts-expect-error` / `@ts-expect-error` over the cast's lines. */
  unchecked?: true;
  /** A primitive operand cast to an intersection with it: a branded type such as `string & { __brand }`. */
  brand?: true;
  /** `unknown` cast to a type parameter (`T`, `T | null`): a generic deserialisation boundary. */
  generic?: true;
  justified: boolean;
  status: Status;
  advice?: string;
}

const timings: Record<string, number> = {};
async function timed<T>(label: string, fn: () => Promise<T>): Promise<T> {
  const start = performance.now();
  const out = await fn();
  timings[label] = Math.round(performance.now() - start);
  return out;
}

async function scanFiles(): Promise<string[]> {
  const files: string[] = [];
  for await (const file of new Glob("**/*.{ts,tsx}").scan({ cwd: ROOT, absolute: true })) {
    if (
      relative(ROOT, file)
        .split("/")
        .some((s) => EXCLUDE.includes(s))
    )
      continue;
    files.push(file);
  }
  return files.sort();
}

/** Files grouped by the virtual probe config beside their nearest `tsconfig.json` at or below ROOT. */
function groupByConfig(files: string[]): Map<string, string[]> {
  const nearest = new Map<string, string>();
  const configDir = (dir: string): string => {
    const hit = nearest.get(dir);
    if (hit !== undefined) return hit;
    const parent = dirname(dir);
    const found =
      existsSync(join(dir, "tsconfig.json")) || dir === ROOT || parent === dir
        ? dir
        : configDir(parent);
    nearest.set(dir, found);
    return found;
  };
  const out = new Map<string, string[]>();
  for (const file of files) {
    const config = join(configDir(dirname(file)), PROBE_CONFIG);
    const list = out.get(config) ?? [];
    list.push(file);
    out.set(config, list);
  }
  return out;
}

function isCast(node: Node): node is Cast {
  return isAsExpression(node) || isTypeAssertion(node);
}

function isAsConst(cast: Cast): boolean {
  const t = cast.type;
  return isTypeReferenceNode(t) && isIdentifier(t.typeName) && t.typeName.text === "const";
}

function isUnknownCast(node: Node): node is Cast {
  return isCast(node) && node.type.kind === SyntaxKind.UnknownKeyword;
}

/** One cast to judge: its operand (the inner operand for a double cast) and target nodes. */
interface Site {
  cast: Cast;
  sf: SourceFile;
  /** The virtual probe config whose project compiles `sf`. */
  config: string;
  kind: Finding["kind"];
  operand: Node;
}

function collectSites(sf: SourceFile, config: string, out: Site[]): void {
  const visit = (node: Node): void => {
    if (isCast(node) && !isAsConst(node)) {
      const inner = node.expression;
      if (isUnknownCast(inner)) {
        // `x as unknown as T`: judge `x` against `T`. Skip `inner` itself.
        out.push({ cast: node, sf, config, kind: "double", operand: inner.expression });
        visit(inner.expression);
        node.type.forEachChild(visit);
        return;
      }
      const parent = node.parent;
      // The `x as unknown` half of a double cast is handled by its parent.
      if (!(isUnknownCast(node) && isCast(parent) && parent.expression === node)) {
        out.push({ cast: node, sf, config, kind: "single", operand: inner });
      }
    }
    node.forEachChild(visit);
  };
  sf.forEachChild(visit);
}

type PredicateFunction =
  | ArrowFunction
  | FunctionDeclaration
  | FunctionExpression
  | MethodDeclaration;

/**
 * A type predicate (`x is T`, `asserts x is T`) whose body cannot be testing
 * `x`. The compiler trusts a predicate's body, so such a predicate is a cast
 * with no `as` in it.
 */
interface HollowPredicate {
  file: string;
  line: number;
  text: string;
  reason: "always-true" | "unread-parameter";
  justified: boolean;
}

function isPredicateFunction(node: Node): node is PredicateFunction {
  return (
    isArrowFunction(node) ||
    isFunctionDeclaration(node) ||
    isFunctionExpression(node) ||
    isMethodDeclaration(node)
  );
}

/** Does `node` mention `name`, outside nested functions' own parameter lists? */
function reads(node: Node, name: string): boolean {
  if (isIdentifier(node)) return node.text === name;
  let found = false;
  node.forEachChild((child) => {
    if (!found && reads(child, name)) found = true;
  });
  return found;
}

/** The `return` statements that belong to `body`, not to functions nested in it. */
function ownReturns(body: Node): Node[] {
  const out: Node[] = [];
  const visit = (node: Node): void => {
    if (isPredicateFunction(node)) return;
    if (isReturnStatement(node)) out.push(node);
    node.forEachChild(visit);
  };
  body.forEachChild(visit);
  return out;
}

function hollowReason(
  fn: PredicateFunction,
  predicate: TypePredicateNode
): HollowPredicate["reason"] | undefined {
  const body = fn.body;
  // An overload or `declare` signature has no body to judge; `this is T` names no parameter.
  if (!body || !isIdentifier(predicate.parameterName)) return undefined;
  if (!predicate.assertsModifier) {
    const results = isBlock(body)
      ? ownReturns(body).map((r) => (isReturnStatement(r) ? r.expression : undefined))
      : [body];
    if (results.length > 0 && results.every((e) => e?.kind === SyntaxKind.TrueKeyword)) {
      return "always-true";
    }
  }
  return reads(body, predicate.parameterName.text) ? undefined : "unread-parameter";
}

function collectHollowPredicates(sf: SourceFile, src: string, out: HollowPredicate[]): void {
  const visit = (node: Node): void => {
    if (isPredicateFunction(node) && node.type && isTypePredicateNode(node.type)) {
      const reason = hollowReason(node, node.type);
      if (reason) {
        const start = node.getStart(sf);
        out.push({
          file: relative(ROOT, sf.fileName),
          line: sf.getLineAndCharacterOfPosition(start).line + 1,
          text: firstLine(node.getText(sf)),
          reason,
          justified: isJustified(src, sf, start),
        });
      }
    }
    node.forEachChild(visit);
  };
  sf.forEachChild(visit);
}

function firstLine(text: string): string {
  const line = text.split("\n")[0] ?? "";
  return line.length > 100 ? `${line.slice(0, 99)}…` : line;
}

function isUnchecked(src: string, sf: SourceFile, cast: Cast): boolean {
  if (NOCHECK.test(src)) return true;
  const first = sf.getLineAndCharacterOfPosition(cast.getStart(sf)).line;
  const last = sf.getLineAndCharacterOfPosition(cast.getEnd()).line;
  const lines = src.split("\n");
  // A directive covers the line after it; a cast spanning lines can error on any of them.
  for (let l = Math.max(0, first - 1); l < last; l++) {
    if (SUPPRESSION.test(lines[l] ?? "")) return true;
  }
  return false;
}

function isJustified(src: string, sf: SourceFile, start: number): boolean {
  const line = sf.getLineAndCharacterOfPosition(start).line;
  const lines = src.split("\n");
  const before = (lines[line] ?? "").slice(0, start - (sf.getLineStarts()[line] ?? 0));
  // The same line counts in full: a trailing `// cast:` after the expression is fine.
  return [lines[line - 1] ?? "", before, lines[line] ?? ""].some((l) => JUSTIFICATION.test(l));
}

interface Checker {
  isTypeAssignableTo(a: Type, b: Type): Promise<boolean>;
  typeToString(t: Type): Promise<string>;
}

/** `T`, or a union of type parameters with `null` / `undefined` (`T | null`). */
async function isTypeParameterTarget(to: Type): Promise<boolean> {
  if (to.flags & TypeFlags.TypeParameter) return true;
  if (!to.isUnionType()) return false;
  const members = await to.getTypes();
  const nullish = TypeFlags.Null | TypeFlags.Undefined;
  return (
    members.some((m) => (m.flags & TypeFlags.TypeParameter) !== 0) &&
    members.every((m) => (m.flags & (TypeFlags.TypeParameter | nullish)) !== 0)
  );
}

/** The fast reading: assignability both ways. Display only; the probe decides. */
async function judge(
  checker: Checker,
  from: Type,
  to: Type
): Promise<{ fast: Fast; from: string; to: string; brand: boolean; generic: boolean }> {
  const [fromText, toText, up, down] = await Promise.all([
    checker.typeToString(from),
    checker.typeToString(to),
    checker.isTypeAssignableTo(from, to),
    checker.isTypeAssignableTo(to, from),
  ]);
  let fast: Fast;
  if (from.isErrorType() || to.isErrorType()) fast = "error-type";
  else if ((from.flags | to.flags) & TypeFlags.Any) fast = "any";
  else if (up && down) fast = fromText === toText ? "redundant" : "widening";
  else if (up) fast = "widening";
  else if (down) fast = "narrowing";
  else fast = "unrelated";
  // Nothing produces a branded value but a cast; the brand's constructor needs one.
  const brand =
    (from.flags & PRIMITIVE) !== 0 &&
    (from.flags & TypeFlags.UnionOrIntersection) === 0 &&
    (to.flags & TypeFlags.Intersection) !== 0;
  // Nothing at runtime can test a value against a caller's `T`.
  const generic = from.flags === TypeFlags.Unknown && (await isTypeParameterTarget(to));
  return { fast, from: fromText, to: toText, brand, generic };
}

/**
 * Whether a printed type mentions `any` outside a string literal. Read from
 * the text because the API gives no walk over a type's arguments short of one
 * request per level; `typeToString` elides long types (`... 8 more ...`), so
 * an `any` deep in a large type can go unseen.
 */
function containsAny(typeText: string): boolean {
  return /\bany\b/.test(typeText.replace(/"(?:[^"\\]|\\.)*"/g, ""));
}

const ABSORBING_OPERATORS = new Set<SyntaxKind>([
  SyntaxKind.QuestionQuestionToken,
  SyntaxKind.BarBarToken,
  SyntaxKind.AmpersandAmpersandToken,
]);

/** The widest expression the cast's value reaches through `( )`, `?:`, `??`, `||` and `&&`, if any. */
function absorbingContext(cast: Cast): Node | undefined {
  let node: Node = cast;
  for (;;) {
    const p = node.parent;
    const absorbs =
      isParenthesizedExpression(p) ||
      (isConditionalExpression(p) && p.condition !== node) ||
      (isBinaryExpression(p) && ABSORBING_OPERATORS.has(p.operatorToken.kind));
    if (!absorbs) return node === cast ? undefined : node;
    node = p;
  }
}

function errorKeys(diagnostics: readonly Diagnostic[]): Map<string, number> {
  const out = new Map<string, number>();
  for (const d of diagnostics) {
    if (d.category !== DiagnosticCategory.Error) continue;
    if (UNUSED_CODES.has(d.code)) continue;
    out.set(`${d.code}|${d.text}`, d.code);
  }
  return out;
}

type Api = InstanceType<typeof API>;
type Program = NonNullable<ReturnType<Snapshot["getConfiguredProject"]>>["program"];

/** A file's errors and its declaration emit: what an importer can see of it. */
interface FileState {
  errors: Map<string, number>;
  decl: string;
}

async function fileState(program: Program, file: string): Promise<FileState> {
  const [syn, sem, emit] = await Promise.all([
    program.getSyntacticDiagnostics(file),
    program.getSemanticDiagnostics(file),
    program.getDeclarationEmit([file]),
  ]);
  const decl = [...emit.outputFiles.values()].map((o) => o.text).join("\n");
  return { errors: errorKeys([...syn, ...sem]), decl };
}

interface Change {
  /** Codes of the errors the new text adds. */
  codes: number[];
  /** The declaration emit differs, so the change reaches the file's importers. */
  exportsChanged: boolean;
}

/** What `text` in place of `file` changes against `base`. */
async function probeText(
  api: Api,
  snapshot: Snapshot,
  config: string,
  file: string,
  text: string,
  base: FileState
): Promise<Change> {
  let change: Change = { codes: [], exportsChanged: false };
  await api.runWithTemporaryFileUpdate(snapshot, file, text, async (snap) => {
    const program = snap.getConfiguredProject(config)?.program;
    if (!program) throw new Error("tsgo lost the probe project");
    const next = await fileState(program, file);
    change = {
      codes: [...next.errors].filter(([k]) => !base.errors.has(k)).map(([, code]) => code),
      exportsChanged: next.decl !== base.decl,
    };
  });
  return change;
}

/** Operand kinds that stand in for the cast with no parentheses around them. */
const BARE_OPERAND = new Set<SyntaxKind>([
  SyntaxKind.Identifier,
  SyntaxKind.PropertyAccessExpression,
  SyntaxKind.ElementAccessExpression,
  SyntaxKind.CallExpression,
  SyntaxKind.ParenthesizedExpression,
  SyntaxKind.ArrayLiteralExpression,
  SyntaxKind.StringLiteral,
  SyntaxKind.NumericLiteral,
  SyntaxKind.NoSubstitutionTemplateLiteral,
  SyntaxKind.TemplateExpression,
  SyntaxKind.TaggedTemplateExpression,
  SyntaxKind.ThisKeyword,
  SyntaxKind.NullKeyword,
  SyntaxKind.TrueKeyword,
  SyntaxKind.FalseKeyword,
  SyntaxKind.NonNullExpression,
]);

/** Parent kinds where an object literal at the start would parse as a block. */
const BLOCK_POSITION = new Set<SyntaxKind>([
  SyntaxKind.ArrowFunction,
  SyntaxKind.ExpressionStatement,
]);

interface Edit {
  start: number;
  end: number;
  text: string;
}

/**
 * The edit that deletes a cast and keeps its operand. `(x as T).y` becomes
 * `x.y` when dropping the parentheses cannot change the meaning (no optional
 * chain, no `new` without arguments); otherwise the operand is wrapped.
 */
function removalEdit(site: Site): Edit {
  const { cast, sf, operand } = site;
  const text = operand.getText(sf);
  const parent = cast.parent;
  const bare =
    BARE_OPERAND.has(operand.kind) ||
    (operand.kind === SyntaxKind.ObjectLiteralExpression && !BLOCK_POSITION.has(parent.kind));
  const chained = (operand.flags & NodeFlags.OptionalChain) !== 0 || text.includes("?.");
  if (bare && isParenthesizedExpression(parent) && !chained) {
    return { start: parent.getStart(sf), end: parent.getEnd(), text };
  }
  return {
    start: cast.getStart(sf),
    end: cast.getEnd(),
    text: bare || isParenthesizedExpression(parent) ? text : `(${text})`,
  };
}

function applyEdits(src: string, edits: Edit[]): string {
  let out = src;
  for (const e of [...edits].sort((a, b) => b.start - a.start)) {
    out = `${out.slice(0, e.start)}${e.text}${out.slice(e.end)}`;
  }
  return out;
}

/** Sets `probe` / `probeCodes` on each probed finding from the compiler's reading of two rewrites. */
/** Sets `probe`, `probeCodes` and `blocked` on one finding from the compiler's reading of two rewrites. */
async function probeOne(
  api: Api,
  snapshot: Snapshot,
  site: Site,
  finding: Finding,
  src: string,
  base: FileState
): Promise<void> {
  const file = site.sf.fileName;
  // The compiler reports nothing here, so every rewrite would look harmless.
  if (finding.unchecked) {
    finding.blocked = "unchecked";
    return;
  }
  let removed: Change | undefined;
  // Without the cast an `any` operand fits everywhere and nothing errors,
  // yet the value has lost its only type; such a cast is never removable.
  if (finding.opaque) finding.blocked = `opaque-${finding.opaque}`;
  else {
    const text = applyEdits(src, [removalEdit(site)]);
    removed = await probeText(api, snapshot, site.config, file, text, base);
    if (removed.codes.length === 0 && !removed.exportsChanged) {
      finding.probe = "removable";
      return;
    }
    if (removed.codes.length === 0) finding.blocked = "changes-exports";
  }
  const removedCodes = removed?.codes ?? [];
  if (site.kind === "single") {
    finding.probe = "required";
    finding.probeCodes = removedCodes;
    return;
  }
  const single = applyEdits(src, [
    {
      start: site.cast.getStart(site.sf),
      end: site.cast.getEnd(),
      text: `(${site.operand.getText(site.sf)}) as ${site.cast.type.getText(site.sf)}`,
    },
  ]);
  const { codes } = await probeText(api, snapshot, site.config, file, single, base);
  // A double cast that a single one cannot replace fails with TS2352 ("may be a mistake").
  finding.probe = codes.length === 0 ? "comparable" : "incomparable";
  finding.probeCodes = codes.length === 0 ? removedCodes : codes;
}

function programOf(programs: Map<string, Program>, site: Site): Program {
  const program = programs.get(site.config);
  if (!program) throw new Error(`no project for ${site.config}`);
  return program;
}

async function probeSites(
  api: Api,
  snapshot: Snapshot,
  programs: Map<string, Program>,
  sites: Site[],
  findings: Finding[],
  textOf: (file: string) => string,
  wanted: (i: number) => boolean
): Promise<void> {
  const states = new Map<string, FileState>();
  for (const [i, site] of sites.entries()) {
    const finding = findings[i];
    if (!finding || !wanted(i)) continue;
    const file = site.sf.fileName;
    let base = states.get(file);
    if (!base) {
      base = await fileState(programOf(programs, site), file);
      states.set(file, base);
    }
    await probeOne(api, snapshot, site, finding, textOf(file), base);
  }
}

interface BaselineEntry {
  file: string;
  text: string;
}

function isBaselineEntry(entry: unknown): entry is BaselineEntry {
  return (
    typeof entry === "object" &&
    entry !== null &&
    "file" in entry &&
    typeof entry.file === "string" &&
    "text" in entry &&
    typeof entry.text === "string"
  );
}

/** `file::text` → how many casts with that text the baseline allows in that file. */
function loadBaseline(): Map<string, number> {
  const out = new Map<string, number>();
  if (!existsSync(BASELINE_PATH)) return out;
  const raw: unknown = JSON.parse(readFileSync(BASELINE_PATH, "utf-8"));
  if (!Array.isArray(raw)) throw new Error(`${BASELINE_PATH} is not an array`);
  for (const e of raw.filter(isBaselineEntry)) {
    const k = `${e.file}::${e.text}`;
    out.set(k, (out.get(k) ?? 0) + 1);
  }
  return out;
}

function baselineKey(f: { file: string; key: string }): string {
  return `${f.file}::${f.key}`;
}

function singleAdvice(f: Finding): string {
  if (f.probe === "removable") return "delete the cast: the operand already fits (`--fix` does it)";
  if (f.blocked === "changes-exports") {
    return "removing it changes the file's exported types; annotate the declaration, or narrow with a type guard";
  }
  if (f.brand) {
    return "a branded type needs one cast, in its constructor; mark it `// cast: <reason>`, and call the constructor everywhere else";
  }
  if (f.generic) {
    return "nothing can test a value against a caller's type parameter; mark the cast `// cast: <reason>`, or take a validator from the caller";
  }
  return "narrow with a type guard, or fix the type where the value comes from";
}

function decideSingle(f: Finding): Pick<Finding, "status" | "advice"> {
  if ((f.brand || f.generic) && f.probe === "required" && f.justified) return { status: "allowed" };
  return { status: "violation", advice: singleAdvice(f) };
}

/** The verdict for a probed (or unprobed but double-cast-free) finding. */
function decide(f: Finding): Pick<Finding, "status" | "advice"> {
  if (f.blocked === "unchecked") {
    return {
      status: "violation",
      advice:
        "the compiler does not check this line; remove the `@ts-nocheck` / `@ts-ignore` first, then the probe can judge the cast",
    };
  }
  if (f.kind === "single") return decideSingle(f);
  if (f.probe === "removable") {
    return {
      status: "violation",
      advice: "delete the double cast: the operand already fits (`--fix` does it)",
    };
  }
  if (f.probe === "comparable") {
    return {
      status: "violation",
      advice:
        "a single `as` compiles here, so the double cast only gets past this gate; narrow with a type guard",
    };
  }
  if (!f.justified) {
    return {
      status: "violation",
      advice: "the double cast is needed; say why with `// cast: <reason>` on the line above",
    };
  }
  return { status: "allowed" };
}

interface Run {
  files: string[];
  findings: Finding[];
  fixed: { file: string; casts: number }[];
  fixRejected: { file: string; codes: number[]; exportsChanged: boolean }[];
  staleBaseline: number;
  hollow: HollowPredicate[];
}

/** Which findings the baseline covers, consumed in source order, and how many entries matched nothing. */
function matchBaseline(findings: Finding[]): { covered: boolean[]; stale: number } {
  const allowance = UPDATE ? new Map<string, number>() : loadBaseline();
  const covered = findings.map((f) => {
    const k = baselineKey(f);
    const left = allowance.get(k) ?? 0;
    if (left === 0) return false;
    allowance.set(k, left - 1);
    return true;
  });
  return { covered, stale: [...allowance.values()].reduce((a, b) => a + b, 0) };
}

function writeBaseline(findings: Finding[]): void {
  const entries = findings
    .filter((f) => f.status === "violation")
    .map((f) => ({ file: f.file, text: f.key }))
    .sort((a, b) =>
      a.file === b.file ? a.text.localeCompare(b.text) : a.file.localeCompare(b.file)
    );
  writeFileSync(BASELINE_PATH, `${JSON.stringify(entries, null, 2)}\n`);
}

/**
 * Deletes every removable cast, one file at a time. All of a file's removals
 * are checked together first (unused-binding codes aside), because two
 * removals that each pass alone can fail together; such a file is left as is.
 */
async function fixRemovable(
  api: Api,
  snapshot: Snapshot,
  programs: Map<string, Program>,
  sites: Site[],
  findings: Finding[],
  textOf: (file: string) => string
): Promise<Pick<Run, "fixed" | "fixRejected">> {
  const fixed: Run["fixed"] = [];
  const fixRejected: Run["fixRejected"] = [];
  const byFile = new Map<string, Site[]>();
  for (const [i, site] of sites.entries()) {
    if (findings[i]?.probe !== "removable") continue;
    const list = byFile.get(site.sf.fileName) ?? [];
    list.push(site);
    byFile.set(site.sf.fileName, list);
  }
  for (const [file, list] of byFile) {
    const first = list[0];
    if (!first) continue;
    const edits = list.map(removalEdit);
    // A removal inside another removal's span is left for the next run.
    const outer = edits.filter(
      (e) => !edits.some((o) => o !== e && o.start <= e.start && e.end <= o.end)
    );
    const next = applyEdits(textOf(file), outer);
    const base = await fileState(programOf(programs, first), file);
    const { codes, exportsChanged } = await probeText(
      api,
      snapshot,
      first.config,
      file,
      next,
      base
    );
    if (codes.length > 0 || exportsChanged) {
      fixRejected.push({ file: relative(ROOT, file), codes, exportsChanged });
      continue;
    }
    writeFileSync(file, next);
    fixed.push({ file: relative(ROOT, file), casts: outer.length });
  }
  return { fixed, fixRejected };
}

type Project = NonNullable<ReturnType<Snapshot["getConfiguredProject"]>>;

/** One finding before the probe: where the cast is, the fast reading, and what hides its loss. */
async function describe(
  site: Site,
  projects: Map<string, Project>,
  textOf: (file: string) => string
): Promise<Finding> {
  const checker = projects.get(site.config)?.checker;
  if (!checker) throw new Error(`no project for ${site.config}`);
  const context = absorbingContext(site.cast);
  // Each call is its own request; the async client sends the requests of one tick together.
  const [from, to, contextType] = await Promise.all([
    checker.getTypeAtLocation(site.operand),
    checker.getTypeAtLocation(site.cast.type),
    context ? checker.getTypeAtLocation(context) : undefined,
  ]);
  const { brand, generic, ...judged } = await judge(checker, from, to);
  const contextText = contextType ? await checker.typeToString(contextType) : "";
  let opaque: Finding["opaque"];
  if (from.isErrorType() || containsAny(judged.from)) opaque = "operand";
  else if (containsAny(contextText) && !containsAny(judged.to)) opaque = "context";
  const start = site.cast.getStart(site.sf);
  const full = site.cast.getText(site.sf);
  return {
    file: relative(ROOT, site.sf.fileName),
    line: site.sf.getLineAndCharacterOfPosition(start).line + 1,
    text: firstLine(full),
    key: full.replace(/\s+/g, " "),
    kind: site.kind,
    ...judged,
    ...(opaque ? { opaque } : {}),
    ...(brand ? { brand: true as const } : {}),
    ...(generic ? { generic: true as const } : {}),
    justified: isJustified(textOf(site.sf.fileName), site.sf, start),
    ...(isUnchecked(textOf(site.sf.fileName), site.sf, site.cast)
      ? { unchecked: true as const }
      : {}),
    status: "violation",
  };
}

async function run(): Promise<Run> {
  const files = await timed("scan", scanFiles);
  const api = new API({ cwd: ROOT });
  try {
    const groups = groupByConfig(files);
    const layer = [...groups].map(([config, list]): [string, string] => [
      config,
      JSON.stringify({ extends: "./tsconfig.json", files: list, include: [] }),
    ]);
    const snapshot = await timed("snapshot", () =>
      api.createSnapshot({
        openProjects: [...groups.keys()],
        fileSystem: createFileSystemLayer(layer),
        ensurePrograms: true,
      })
    );
    const projects = new Map(
      [...groups.keys()].map((config) => {
        const project = snapshot.getConfiguredProject(config);
        if (!project) throw new Error(`tsgo did not open ${config}`);
        return [config, project];
      })
    );
    const programs = new Map([...projects].map(([c, p]) => [c, p.program]));

    const sites: Site[] = [];
    const sourceFiles: SourceFile[] = [];
    await timed("walk", async () => {
      for (const [config, list] of groups) {
        const program = programs.get(config);
        const sources = await Promise.all(list.map((f) => program?.getSourceFile(f)));
        for (const sf of sources) {
          if (!sf) continue;
          collectSites(sf, config, sites);
          sourceFiles.push(sf);
        }
      }
    });

    const texts = new Map<string, string>();
    const textOf = (file: string): string => {
      let t = texts.get(file);
      if (t === undefined) {
        t = readFileSync(file, "utf-8");
        texts.set(file, t);
      }
      return t;
    };

    const hollow: HollowPredicate[] = [];
    for (const sf of sourceFiles) collectHollowPredicates(sf, textOf(sf.fileName), hollow);

    const findings = await timed("checker", () =>
      Promise.all(sites.map((site) => describe(site, projects, textOf)))
    );

    const { covered, stale: staleBaseline } = matchBaseline(findings);

    await timed("probe", () =>
      probeSites(api, snapshot, programs, sites, findings, textOf, (i) => PROBE_ALL || !covered[i])
    );
    for (const [i, f] of findings.entries()) {
      Object.assign(f, covered[i] && !PROBE_ALL ? { status: "baselined" } : decide(f));
      if (covered[i] && f.status === "violation") f.status = "baselined";
    }

    const { fixed, fixRejected } = FIX
      ? await timed("fix", () => fixRemovable(api, snapshot, programs, sites, findings, textOf))
      : { fixed: [], fixRejected: [] };
    if (UPDATE) writeBaseline(findings);

    await snapshot.dispose();
    return {
      files,
      findings,
      fixed,
      fixRejected,
      staleBaseline: UPDATE ? 0 : staleBaseline,
      hollow,
    };
  } finally {
    await api.close();
  }
}

function countBy<T>(items: T[], pick: (t: T) => string): Record<string, number> {
  const out: Record<string, number> = {};
  for (const item of items) out[pick(item)] = (out[pick(item)] ?? 0) + 1;
  return out;
}

function at(f: { file: string; line: number }): string {
  return `${f.file}:${f.line}`;
}

const totalStart = performance.now();
const result = await run();
timings["total"] = Math.round(performance.now() - totalStart);
const { files, findings } = result;
const violations = findings.filter((f) => f.status === "violation");
const hollowViolations = result.hollow.filter((h) => !h.justified);

let comparison: { regexOnly: string[]; apiOnly: string[]; both: number } | undefined;
if (COMPARE) {
  const regex = await timed("regex", () => checkNoAsCasting({ rootDir: ROOT, exclude: EXCLUDE }));
  const regexKeys = new Set(regex.violations.map(at));
  const single = findings.filter((f) => f.kind === "single");
  const apiKeys = new Set(single.map(at));
  comparison = {
    regexOnly: [...regexKeys].filter((k) => !apiKeys.has(k)),
    apiOnly: single.filter((v) => !regexKeys.has(at(v))).map((v) => `${at(v)}  ${v.text}`),
    both: [...apiKeys].filter((k) => regexKeys.has(k)).length,
  };
}

const log = (s = ""): void => void process.stdout.write(`${s}\n`);

if (JSON_OUT) {
  const { fixed, fixRejected, staleBaseline, hollow } = result;
  log(
    JSON.stringify(
      {
        files: files.length,
        timings,
        findings,
        hollow,
        fixed,
        fixRejected,
        staleBaseline,
        comparison,
      },
      null,
      2
    )
  );
} else {
  const counts = countBy(findings, (f) => f.status);
  log(
    `[casts] ${files.length} files, ${findings.length} casts: ${violations.length} violation(s), ${counts["baselined"] ?? 0} baselined, ${counts["allowed"] ?? 0} allowed`
  );
  for (const v of violations) {
    const probe = v.probe ? ` ${v.probe}` : "";
    log(`  ${at(v)}  [${v.kind}${probe}]  ${v.text}`);
    log(`    ${v.from}  →  ${v.to}`);
    if (v.advice) log(`    ${v.advice}`);
  }
  for (const h of hollowViolations) {
    log(`  ${at(h)}  [predicate ${h.reason}]  ${h.text}`);
    log(
      h.reason === "always-true"
        ? "    the predicate returns `true` whatever it is given: a cast in a function; test the value, or mark it `// cast: <reason>`"
        : "    the predicate never reads its parameter: a cast in a function; test the value, or mark it `// cast: <reason>`"
    );
  }
  if (result.hollow.length > 0) {
    log(
      `  ${result.hollow.length} hollow predicate(s): ${hollowViolations.length} unmarked, ${result.hollow.length - hollowViolations.length} marked \`// cast:\``
    );
  }
  if (result.staleBaseline > 0) {
    log(
      `  ${result.staleBaseline} baseline entr${result.staleBaseline === 1 ? "y matches" : "ies match"} no cast; \`--update\` prunes them`
    );
  }
  if (FIX) {
    log(
      `  --fix: deleted ${result.fixed.reduce((a, f) => a + f.casts, 0)} cast(s) in ${result.fixed.length} file(s)`
    );
    for (const r of result.fixRejected) {
      const why = r.exportsChanged
        ? "change its exported types"
        : `add errors ${r.codes.join(",")}`;
      log(`  --fix: left ${r.file} unchanged; the removals together ${why}`);
    }
    if (result.fixed.length > 0) {
      log("  --fix: run `bun run typecheck` and `biome check --write` (imports may now be unused)");
    }
  }
  if (UPDATE) log(`  --update: wrote ${violations.length} entr(ies) to casts-baseline.json`);
  if (TABLES) {
    const doubles = findings.filter((f) => f.kind === "double");
    log();
    log(`  double casts, probe: ${JSON.stringify(countBy(doubles, (h) => h.probe ?? "?"))}`);
    log(
      `  single casts, probe: ${JSON.stringify(
        countBy(
          findings.filter((f) => f.kind === "single"),
          (f) => f.probe ?? "?"
        )
      )}`
    );
    log();
    log("  fast (assignability) × probe (compiler):");
    const fasts = [...new Set(findings.map((f) => f.fast))].sort();
    const probes: Probe[] = ["removable", "comparable", "incomparable", "required"];
    log(`    ${"".padEnd(12)}${probes.map((p) => p.padStart(14)).join("")}`);
    for (const fast of fasts) {
      const row = probes.map((p) =>
        String(findings.filter((f) => f.fast === fast && f.probe === p).length).padStart(14)
      );
      log(`    ${fast.padEnd(12)}${row.join("")}`);
    }
  }
  if (comparison) {
    log();
    log(
      `  compare (single casts): both=${comparison.both}  regex-only=${comparison.regexOnly.length}  api-only=${comparison.apiOnly.length}`
    );
    for (const k of comparison.regexOnly) log(`    regex-only  ${k}`);
    for (const k of comparison.apiOnly) log(`    api-only    ${k}`);
  }
  log(
    `  timings (ms): ${Object.entries(timings)
      .map(([k, v]) => `${k}=${v}`)
      .join("  ")}`
  );
}

// Not process.exit(): it drops stdout still queued for a pipe, which cut `--json` short.
process.exitCode = !UPDATE && !FIX && violations.length + hollowViolations.length > 0 ? 1 : 0;
