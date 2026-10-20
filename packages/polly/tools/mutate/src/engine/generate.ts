/**
 * Mutant generation: parse a target with oxc-parser, walk the runtime part of
 * the tree, and collect span replacements from the operators.
 *
 * Type-only syntax is never mutated — a mutant there changes nothing Bun
 * executes — and neither are decorators or `declare` statements (Stryker's
 * skip rules). Mutants inside polly verify primitives are kept but marked
 * ignored, the way Stryker's polly-verify ignorer reports them.
 *
 * Parentheses are not nodes (`preserveParens: false`), as in the Babel AST
 * Stryker walks, so operators that look at a parent see the real one.
 */
import { parseSync } from "oxc-parser";
import { type AstNode, calleeName, children, isAstNode } from "./ast.ts";
import { OPERATORS, type OperatorContext } from "./operators.ts";
import type { ContractSite, Mutant, MutatorName, Position } from "./types.ts";
import { VERIFY_PRIMITIVES, verifyCallsiteReason } from "./verify-callsites.ts";

/** TS nodes that wrap a runtime expression. Every other `TS*` node is type-only. */
const TS_RUNTIME_WRAPPERS = new Set([
  "TSAsExpression",
  "TSSatisfiesExpression",
  "TSNonNullExpression",
  "TSInstantiationExpression",
  "TSTypeAssertion",
  // `constructor(private x = 1)`: the default is runtime code.
  "TSParameterProperty",
  // A namespace body runs; only `declare namespace` / `declare module` is type-only.
  "TSModuleBlock",
]);
const PARSE_OPTIONS = { preserveParens: false };
const TYPE_KEYS = new Set(["typeAnnotation", "returnType", "typeParameters", "typeArguments"]);
const SKIPPED_STATEMENTS = new Set(["ImportDeclaration", "ExportAllDeclaration", "Decorator"]);

function isSkipped(node: AstNode): boolean {
  if (SKIPPED_STATEMENTS.has(node.type)) return true;
  if (node.type === "VariableDeclaration") return node["declare"] === true;
  if (node.type === "TSModuleDeclaration") return node["declare"] === true;
  return node.type.startsWith("TS") && !TS_RUNTIME_WRAPPERS.has(node.type);
}

export interface GenerateOptions {
  ignoreVerifyCallsites?: boolean;
  /** Keep only mutants that start inside this 1-based inclusive line range. */
  lines?: { from: number; to: number };
  /** Prefix for mutant ids, so ids stay unique across files in one report. */
  idPrefix?: string;
  /** Mutators whose edits are dropped (polly.mutate.ts `mutators.exclude`). */
  exclude?: readonly MutatorName[];
}

export interface GenerateResult {
  mutants: Mutant[];
  /** Mutants whose mutated text no longer parses. Reported, never run. */
  compileErrors: Mutant[];
  /** Every requires/ensures call, whole file, whatever `lines` and the ignore flag say. */
  contracts: ContractSite[];
}

export function lineIndex(src: string): (offset: number) => Position {
  const starts = [0];
  for (let i = 0; i < src.length; i++) if (src.charCodeAt(i) === 10) starts.push(i + 1);
  return (offset) => {
    let lo = 0;
    let hi = starts.length - 1;
    while (lo < hi) {
      const mid = (lo + hi + 1) >> 1;
      if ((starts[mid] ?? 0) <= offset) lo = mid;
      else hi = mid - 1;
    }
    return { line: lo + 1, column: offset - (starts[lo] ?? 0) + 1 };
  };
}

export function applyMutant(src: string, m: Pick<Mutant, "start" | "end" | "replacement">): string {
  return src.slice(0, m.start) + m.replacement + src.slice(m.end);
}

/** The polly#143 reason when `node` is a call to a verify primitive. */
function verifyReason(node: AstNode): string | undefined {
  if (node.type !== "CallExpression") return undefined;
  const name = calleeName(node);
  return name && VERIFY_PRIMITIVES.has(name) ? verifyCallsiteReason(name) : undefined;
}

const FUNCTION_NODES = new Set([
  "FunctionDeclaration",
  "FunctionExpression",
  "ArrowFunctionExpression",
]);

/**
 * The contract site when `node` is a requires/ensures call: its line, its
 * message literal, and the handler it sits in — the nearest enclosing
 * `bus.on(...)` call, else the nearest enclosing function.
 */
function contractSite(
  file: string,
  node: AstNode,
  ancestors: readonly AstNode[],
  position: (offset: number) => Position
): ContractSite | undefined {
  if (node.type !== "CallExpression") return undefined;
  const name = calleeName(node);
  if (name !== "requires" && name !== "ensures") return undefined;
  const second = children(node, "arguments")[1];
  const message =
    second?.type === "Literal" && typeof second["value"] === "string" ? second["value"] : undefined;
  const handlerNode =
    [...ancestors].reverse().find((a) => a.type === "CallExpression" && calleeName(a) === "on") ??
    [...ancestors].reverse().find((a) => FUNCTION_NODES.has(a.type));
  const handler = handlerNode
    ? { from: position(handlerNode.start).line, to: position(handlerNode.end).line }
    : undefined;
  return {
    file,
    line: position(node.start).line,
    primitive: name,
    ...(message === undefined ? {} : { message }),
    ...(handler ? { handler } : {}),
  };
}

/** Child nodes with the key they hang under, minus type annotations. */
function runtimeChildren(node: AstNode): [string, AstNode][] {
  const out: [string, AstNode][] = [];
  for (const [k, value] of Object.entries(node)) {
    if (TYPE_KEYS.has(k)) continue;
    const list = Array.isArray(value) ? value : [value];
    for (const c of list) if (isAstNode(c)) out.push([k, c]);
  }
  return out;
}

export function generateMutants(
  file: string,
  src: string,
  opts: GenerateOptions = {}
): GenerateResult {
  const parsed = parseSync(file, src, PARSE_OPTIONS);
  const first = parsed.errors[0];
  if (first) throw new Error(`${file}: cannot parse target: ${first.message}`);

  const position = lineIndex(src);
  const ignoreVerify = opts.ignoreVerifyCallsites ?? true;
  const prefix = opts.idPrefix ?? "";
  const seen = new Set<string>();
  const excluded = new Set(opts.exclude ?? []);
  const all: Mutant[] = [];
  const contracts: ContractSite[] = [];

  const ancestors: AstNode[] = [];
  const visit = (node: AstNode, key: string, ignored: string | undefined) => {
    if (isSkipped(node)) return;
    const parent = ancestors[ancestors.length - 1];
    const site = contractSite(file, node, ancestors, position);
    if (site) contracts.push(site);

    const ignoredHere = ignored ?? (ignoreVerify ? verifyReason(node) : undefined);
    const ctx: OperatorContext = {
      src,
      parent,
      key,
      ancestors,
      emit(start: number, end: number, replacement: string, mutatorName: MutatorName) {
        if (excluded.has(mutatorName)) return;
        // Two operators can propose the same edit; keep one.
        const dedupe = `${start}:${end}:${replacement}`;
        if (seen.has(dedupe)) return;
        seen.add(dedupe);
        all.push({
          id: "",
          file,
          mutatorName,
          start,
          end,
          replacement,
          location: { start: position(start), end: position(end) },
          ...(ignoredHere ? { ignoredReason: ignoredHere } : {}),
        });
      },
    };
    for (const op of OPERATORS) op(node, ctx);

    ancestors.push(node);
    for (const [k, c] of runtimeChildren(node)) visit(c, k, ignoredHere);
    ancestors.pop();
  };

  for (const statement of parsed.program.body) {
    if (isAstNode(statement)) visit(statement, "body", undefined);
  }

  const inRange = opts.lines
    ? all.filter(
        (m) =>
          m.location.start.line >= (opts.lines?.from ?? 0) &&
          m.location.start.line <= (opts.lines?.to ?? 0)
      )
    : all;
  inRange.sort((a, b) => a.start - b.start || a.end - b.end);
  inRange.forEach((m, i) => {
    m.id = `${prefix}${i}`;
  });

  const mutants: Mutant[] = [];
  const compileErrors: Mutant[] = [];
  for (const m of inRange) {
    if (parseSync(file, applyMutant(src, m), PARSE_OPTIONS).errors.length > 0)
      compileErrors.push(m);
    else mutants.push(m);
  }
  return { mutants, compileErrors, contracts };
}
