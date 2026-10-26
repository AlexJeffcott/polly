/**
 * Mutation operators, named and shaped after Stryker's mutators so reports
 * stay comparable. Each operator looks at one node and proposes zero or more
 * span replacements through `emit`; the generator owns traversal, ids and
 * locations.
 *
 * Operators work on source spans, not on regenerated code: a mutant is the
 * original text with one slice swapped, so formatting, comments and every
 * other line stay byte-identical.
 *
 * The rules follow @stryker-mutator/instrumenter 9.6.1 (`dist/src/mutators/`).
 * Intended differences are listed in tools/mutate/README.md.
 */

import { isRecord } from "../../../../src/shared/lib/guards";
import { loadToolPackage, MUTATE_FEATURE } from "../../../tool-deps/src/index.ts";
import { type AstNode, calleeName, child, children, isAstNode, stringField } from "./ast.ts";
import type { MutatorName } from "./types.ts";

// Optional peer dependency: loaded through the guard so a missing package names
// the install command instead of failing as a bare resolve error.
const { mutate: mutateRegex } = await loadToolPackage(
  "weapon-regex",
  MUTATE_FEATURE,
  () => import("weapon-regex")
);

export interface OperatorContext {
  src: string;
  parent: AstNode | undefined;
  /** The key under which `node` hangs off `parent` (e.g. "test", "key"). */
  key: string;
  /** Every ancestor, outermost first; the last entry is `parent`. */
  ancestors: readonly AstNode[];
  emit(start: number, end: number, replacement: string, mutator: MutatorName): void;
}

type Operator = (node: AstNode, ctx: OperatorContext) => void;

const EQUALITY: Record<string, string[]> = {
  "<": ["<=", ">="],
  "<=": ["<", ">"],
  ">": [">=", "<="],
  ">=": [">", "<"],
  "==": ["!="],
  "!=": ["=="],
  "===": ["!=="],
  "!==": ["==="],
};
const ARITHMETIC: Record<string, string> = { "+": "-", "-": "+", "*": "/", "/": "*", "%": "*" };
const LOGICAL: Record<string, string> = { "&&": "||", "||": "&&", "??": "&&" };
const ASSIGNMENT: Record<string, string> = {
  "+=": "-=",
  "-=": "+=",
  "*=": "/=",
  "/=": "*=",
  "%=": "*=",
  "<<=": ">>=",
  ">>=": "<<=",
  "&=": "|=",
  "|=": "&=",
  "&&=": "||=",
  "||=": "&&=",
  "??=": "&&=",
};
/** Logical assignments still apply to a string right-hand side; the rest are concatenation-like. */
const STRING_SAFE_ASSIGNMENTS = new Set(["&&=", "||=", "??="]);
const BOOLEAN_OPERATORS = new Set(["!=", "!==", "&&", "<", "<=", "==", "===", ">", ">=", "||"]);
const LOOPS = new Set(["ForStatement", "WhileStatement", "DoWhileStatement"]);
const EMPTY_STRING_REPLACEMENT = '"Stryker was here!"';

/**
 * Method name → swap, or null to drop the call (`a.filter(f)` → `a`). Stryker
 * adds the reverse of each swap except for `setUTCDate`.
 */
const METHODS: ReadonlyMap<string, string | null> = (() => {
  const forward: [string, string | null][] = [
    ["charAt", null],
    ["endsWith", "startsWith"],
    ["every", "some"],
    ["filter", null],
    ["reverse", null],
    ["slice", null],
    ["sort", null],
    ["substr", null],
    ["substring", null],
    ["toLocaleLowerCase", "toLocaleUpperCase"],
    ["toLowerCase", "toUpperCase"],
    ["trim", null],
    ["trimEnd", "trimStart"],
    ["min", "max"],
    ["setDate", "setTime"],
    ["setFullYear", "setMonth"],
    ["setHours", "setMinutes"],
    ["setSeconds", "setMilliseconds"],
    ["setUTCDate", "setTime"],
    ["setUTCFullYear", "setUTCMonth"],
    ["setUTCHours", "setUTCMinutes"],
    ["setUTCSeconds", "setUTCMilliseconds"],
  ];
  const map = new Map(forward);
  for (const [name, swap] of forward) {
    if (swap && name !== "setUTCDate" && name !== "getUTCDate") map.set(swap, name);
  }
  return map;
})();

/** Offset of `op` between two operands, skipping comments and parentheses in the gap. */
function operatorOffset(src: string, op: string, left: AstNode, right: AstNode): number {
  const gap = src.slice(left.end, right.start);
  const at = gap.replace(/\/\*[\s\S]*?\*\/|\/\/[^\n]*/g, (c) => " ".repeat(c.length)).indexOf(op);
  return at === -1 ? -1 : left.end + at;
}

/** Babel's StringLiteral or TemplateLiteral, the two types Stryker's string checks name. */
function isStringNode(node: AstNode | undefined): boolean {
  if (!node) return false;
  return (
    (node.type === "Literal" && typeof node["value"] === "string") ||
    node.type === "TemplateLiteral"
  );
}

const text = (src: string, node: AstNode) => src.slice(node.start, node.end);

interface BinaryParts {
  op: string;
  left: AstNode;
  right: AstNode;
  /** Offset of the operator token in the source. */
  at: number;
}

function binaryParts(node: AstNode, src: string): BinaryParts | undefined {
  const op = stringField(node, "operator");
  const left = child(node, "left");
  const right = child(node, "right");
  if (!op || !left || !right) return undefined;
  const at = operatorOffset(src, op, left, right);
  return at === -1 ? undefined : { op, left, right, at };
}

const binary: Operator = (node, ctx) => {
  if (node.type !== "BinaryExpression") return;
  const parts = binaryParts(node, ctx.src);
  if (!parts) return;
  const { op, left, right, at } = parts;
  const span = (rep: string, mutator: MutatorName) => ctx.emit(at, at + op.length, rep, mutator);
  for (const rep of EQUALITY[op] ?? []) span(rep, "EqualityOperator");
  const arith = ARITHMETIC[op];
  // Stryker's concatenation guard, as written: the right operand, and the
  // left operand — or the left's own right operand when the left is binary.
  const leftProbe = left.type === "BinaryExpression" ? child(left, "right") : left;
  if (arith && !isStringNode(right) && !isStringNode(leftProbe)) span(arith, "ArithmeticOperator");
};

const logical: Operator = (node, ctx) => {
  if (node.type !== "LogicalExpression") return;
  const parts = binaryParts(node, ctx.src);
  const rep = parts && LOGICAL[parts.op];
  if (!parts || !rep) return;
  const { op, left, right, at } = parts;
  if (op !== "??") {
    ctx.emit(at, at + op.length, rep, "LogicalOperator");
    return;
  }
  // `??` cannot sit next to `&&`/`||` without parentheses, so in a chain such
  // as `a ?? b ?? c` the bare swap does not parse. Parenthesise the result and
  // any logical operand. Every slice between the operands is kept, because
  // parentheses in the source are not part of any node's span.
  const operand = (n: AstNode) =>
    n.type === "LogicalExpression" ? `(${text(ctx.src, n)})` : text(ctx.src, n);
  const slice = (from: number, to: number) => ctx.src.slice(from, to);
  ctx.emit(
    node.start,
    node.end,
    `(${slice(node.start, left.start)}${operand(left)}${slice(left.end, at)}${rep}${slice(at + op.length, right.start)}${operand(right)}${slice(right.end, node.end)})`,
    "LogicalOperator"
  );
};

const assignment: Operator = (node, ctx) => {
  if (node.type !== "AssignmentExpression") return;
  const parts = binaryParts(node, ctx.src);
  const rep = parts && ASSIGNMENT[parts.op];
  if (!parts || !rep) return;
  if (isStringNode(parts.right) && !STRING_SAFE_ASSIGNMENTS.has(parts.op)) return;
  ctx.emit(parts.at, parts.at + parts.op.length, rep, "AssignmentOperator");
};

const booleanLiteral: Operator = (node, ctx) => {
  if (node.type === "Literal" && typeof node["value"] === "boolean") {
    ctx.emit(node.start, node.end, String(!node["value"]), "BooleanLiteral");
  }
  // Stryker files `!x` → `x` under BooleanLiteral, not UnaryOperator. Only the
  // one-character operator goes: in `!(x)` the `(` sits before the argument's span.
  if (node.type === "UnaryExpression" && node["operator"] === "!") {
    ctx.emit(node.start, node.start + 1, "", "BooleanLiteral");
  }
};

const UNARY: Record<string, string> = { "+": "-", "-": "+", "~": "" };

const unary: Operator = (node, ctx) => {
  if (node.type !== "UnaryExpression") return;
  const op = stringField(node, "operator");
  const rep = op === undefined ? undefined : UNARY[op];
  // Every operator here is one character at the node's start.
  if (rep !== undefined) ctx.emit(node.start, node.start + 1, rep, "UnaryOperator");
};

const update: Operator = (node, ctx) => {
  if (node.type !== "UpdateExpression") return;
  const op = stringField(node, "operator");
  const arg = child(node, "argument");
  if (!op || !arg) return;
  const at = node["prefix"] === true ? node.start : arg.end;
  const opAt = ctx.src.indexOf(op, at);
  if (opAt === -1 || opAt >= node.end) return;
  ctx.emit(opAt, opAt + 2, op === "++" ? "--" : "++", "UpdateOperator");
};

/** Stryker's `isValidParent`: strings that are names or module specifiers, not values. */
function isStructuralString(node: AstNode, ctx: OperatorContext): boolean {
  const p = ctx.parent;
  if (!p) return false;
  if (p.type.startsWith("Export") || p.type === "ImportExpression") return true;
  if (p.type === "JSXAttribute" || p.type === "ExpressionStatement") return true;
  if ((p.type === "Property" || p.type === "PropertyDefinition") && child(p, "key") === node) {
    return true;
  }
  if (p.type !== "CallExpression") return false;
  const callee = child(p, "callee");
  return (
    callee?.type === "Identifier" && (callee["name"] === "require" || callee["name"] === "Symbol")
  );
}

const stringLiteral: Operator = (node, ctx) => {
  if (node.type === "TemplateLiteral") {
    const quasis = children(node, "quasis");
    const value = quasis[0]?.["value"];
    const empty = quasis.length === 1 && isRecord(value) && value["raw"] === "";
    ctx.emit(node.start, node.end, empty ? "`Stryker was here!`" : "``", "StringLiteral");
    return;
  }
  if (node.type !== "Literal" || typeof node["value"] !== "string") return;
  if (isStructuralString(node, ctx)) return;
  ctx.emit(
    node.start,
    node.end,
    node["value"] === "" ? EMPTY_STRING_REPLACEMENT : '""',
    "StringLiteral"
  );
};

function isBooleanExpression(node: AstNode): boolean {
  if (node.type !== "BinaryExpression" && node.type !== "LogicalExpression") return false;
  const op = stringField(node, "operator");
  return op !== undefined && BOOLEAN_OPERATORS.has(op);
}

/** Loop and `if` tests, then boolean expressions anywhere else. Returns whether it emitted. */
function conditionalTest(node: AstNode, ctx: OperatorContext): boolean {
  const p = ctx.parent;
  const emit = (rep: string) => ctx.emit(node.start, node.end, rep, "ConditionalExpression");
  // A loop forced to `true` never terminates; Stryker only tries `false`.
  if (p && ctx.key === "test" && LOOPS.has(p.type)) {
    emit("false");
    return true;
  }
  if (p?.type === "IfStatement" && ctx.key === "test") {
    emit("true");
    emit("false");
    return true;
  }
  if (!isBooleanExpression(node)) return false;
  // `true || y` is the same mutant as forcing the whole `||` to true, and
  // `false && y` the same as forcing the `&&` to false; Stryker skips both.
  const parentOp = p?.type === "LogicalExpression" ? stringField(p, "operator") : undefined;
  if (parentOp !== "||") emit("true");
  if (parentOp !== "&&") emit("false");
  return true;
}

/** `for (;;)` → `for (;false;)`. */
function forWithoutTest(node: AstNode, ctx: OperatorContext): void {
  const init = child(node, "init");
  const open = ctx.src.indexOf("(", node.start);
  const semi = open === -1 ? -1 : ctx.src.indexOf(";", init ? init.end : open);
  if (semi !== -1) ctx.emit(semi + 1, semi + 1, "false", "ConditionalExpression");
}

/** A non-fallthrough `case` loses its statements. */
function emptySwitchCase(node: AstNode, ctx: OperatorContext): void {
  const body = children(node, "consequent");
  const first = body[0];
  const last = body[body.length - 1];
  if (first && last) ctx.emit(first.start, last.end, "", "ConditionalExpression");
}

const conditional: Operator = (node, ctx) => {
  if (conditionalTest(node, ctx)) return;
  if (node.type === "ForStatement" && !child(node, "test")) forWithoutTest(node, ctx);
  if (node.type === "SwitchCase") emptySwitchCase(node, ctx);
};

function containsSuperCall(node: AstNode): boolean {
  if (node.type === "CallExpression" && child(node, "callee")?.type === "Super") return true;
  for (const value of Object.values(node)) {
    const list = Array.isArray(value) ? value : [value];
    for (const c of list) if (isAstNode(c) && containsSuperCall(c)) return true;
  }
  return false;
}

/**
 * Stryker's invalid-constructor rule (stryker-js#2314, #2474): emptying a
 * constructor that calls super() is skipped only when the class also has TS
 * parameter properties or initialised (non-private) fields, because only then
 * does the emptied body fail to compile.
 */
function isInvalidConstructorBody(ctx: OperatorContext, block: AstNode): boolean {
  const n = ctx.ancestors.length;
  const fn = ctx.ancestors[n - 1];
  const method = ctx.ancestors[n - 2];
  const classBody = ctx.ancestors[n - 3];
  if (!fn || method?.type !== "MethodDefinition" || method["kind"] !== "constructor") return false;
  const paramProps = children(fn, "params").some((param) => param.type === "TSParameterProperty");
  const initialisedFields =
    classBody?.type === "ClassBody" &&
    children(classBody, "body").some(
      (m) =>
        m.type === "PropertyDefinition" &&
        child(m, "value") !== undefined &&
        child(m, "key")?.type !== "PrivateIdentifier"
    );
  return (paramProps || initialisedFields) && containsSuperCall(block);
}

const block: Operator = (node, ctx) => {
  if (node.type !== "BlockStatement" || children(node, "body").length === 0) return;
  if (isInvalidConstructorBody(ctx, node)) return;
  ctx.emit(node.start, node.end, "{}", "BlockStatement");
};

const arrayDeclaration: Operator = (node, ctx) => {
  if (node.type === "ArrayExpression") {
    const empty = children(node, "elements").length === 0;
    ctx.emit(node.start, node.end, empty ? '["Stryker was here"]' : "[]", "ArrayDeclaration");
    return;
  }
  if (node.type !== "CallExpression" && node.type !== "NewExpression") return;
  const callee = child(node, "callee");
  if (callee?.type !== "Identifier" || callee["name"] !== "Array") return;
  const args = children(node, "arguments").length === 0 ? "[]" : "";
  const prefix = node.type === "NewExpression" ? "new " : "";
  ctx.emit(node.start, node.end, `${prefix}Array(${args})`, "ArrayDeclaration");
};

const objectLiteral: Operator = (node, ctx) => {
  if (node.type === "ObjectExpression" && children(node, "properties").length > 0) {
    ctx.emit(node.start, node.end, "{}", "ObjectLiteral");
  }
};

const arrowFunction: Operator = (node, ctx) => {
  if (node.type !== "ArrowFunctionExpression") return;
  const body = child(node, "body");
  if (!body || body.type === "BlockStatement" || node["expression"] === false) return;
  if (body.type === "Identifier" && body["name"] === "undefined") return;
  ctx.emit(node.start, node.end, "() => undefined", "ArrowFunction");
};

const optionalChaining: Operator = (node, ctx) => {
  if (node["optional"] !== true) return;
  if (node.type === "MemberExpression") {
    const object = child(node, "object");
    if (!object) return;
    const q = ctx.src.indexOf("?.", object.end);
    if (q === -1 || q >= node.end) return;
    ctx.emit(q, q + 2, node["computed"] === true ? "" : ".", "OptionalChaining");
  }
  if (node.type === "CallExpression") {
    const callee = child(node, "callee");
    if (!callee) return;
    const q = ctx.src.indexOf("?.", callee.end);
    if (q === -1 || q >= node.end) return;
    ctx.emit(q, q + 2, "", "OptionalChaining");
  }
};

const methodExpression: Operator = (node, ctx) => {
  if (node.type !== "CallExpression") return;
  const callee = child(node, "callee");
  if (callee?.type !== "MemberExpression" || callee["computed"] === true) return;
  const property = child(callee, "property");
  const object = child(callee, "object");
  if (property?.type !== "Identifier" || !object) return;
  const name = stringField(property, "name");
  const swap = name === undefined ? undefined : METHODS.get(name);
  if (swap === undefined) return;
  if (swap === null) ctx.emit(node.start, node.end, text(ctx.src, object), "MethodExpression");
  else ctx.emit(property.start, property.end, swap, "MethodExpression");
};

/** weapon-regex at mutation level 1, as Stryker calls it. An unparseable pattern yields none. */
function regexPatterns(pattern: string, flags: string | undefined): string[] {
  if (pattern.length === 0) return [];
  try {
    return mutateRegex(pattern, flags, { mutationLevels: [1] }).map((m) => m.pattern);
  } catch {
    return [];
  }
}

const regex: Operator = (node, ctx) => {
  if (node.type !== "Literal") return;
  const literal = node["regex"];
  if (isRecord(literal)) {
    const pattern = literal["pattern"];
    const flags = typeof literal["flags"] === "string" ? literal["flags"] : "";
    if (typeof pattern !== "string") return;
    for (const p of regexPatterns(pattern, flags)) {
      ctx.emit(node.start, node.end, `/${p}/${flags}`, "Regex");
    }
    return;
  }
  // `new RegExp("…")` — the pattern string, when it is the first argument.
  const p = ctx.parent;
  if (typeof node["value"] !== "string" || p?.type !== "NewExpression") return;
  if (calleeName(p) !== "RegExp" || child(p, "callee")?.type !== "Identifier") return;
  const [first, second] = children(p, "arguments");
  if (first !== node) return;
  const flags = second?.type === "Literal" ? stringField(second, "value") : undefined;
  for (const pattern of regexPatterns(node["value"], flags)) {
    ctx.emit(node.start, node.end, JSON.stringify(pattern), "Regex");
  }
};

export const OPERATORS: readonly Operator[] = [
  binary,
  logical,
  assignment,
  booleanLiteral,
  unary,
  update,
  stringLiteral,
  regex,
  conditional,
  block,
  arrayDeclaration,
  objectLiteral,
  arrowFunction,
  optionalChaining,
  methodExpression,
];
