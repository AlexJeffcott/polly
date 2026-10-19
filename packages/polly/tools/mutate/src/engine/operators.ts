/**
 * Mutation operators, named and shaped after Stryker's mutators so reports
 * stay comparable. Each operator looks at one node and proposes zero or more
 * span replacements through `emit`; the generator owns traversal, ids and
 * locations.
 *
 * Operators work on source spans, not on regenerated code: a mutant is the
 * original text with one slice swapped, so formatting, comments and every
 * other line stay byte-identical.
 */
import { type AstNode, calleeName, child, children, stringField } from "./ast.ts";
import type { MutatorName } from "./types.ts";

export interface OperatorContext {
  src: string;
  parent: AstNode | undefined;
  /** The key under which `node` hangs off `parent` (e.g. "test", "key"). */
  key: string;
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
const METHOD_SWAPS: Record<string, string> = {
  endsWith: "startsWith",
  startsWith: "endsWith",
  every: "some",
  some: "every",
  toLowerCase: "toUpperCase",
  toUpperCase: "toLowerCase",
  toLocaleLowerCase: "toLocaleUpperCase",
  toLocaleUpperCase: "toLocaleLowerCase",
  trimEnd: "trimStart",
  trimStart: "trimEnd",
  min: "max",
  max: "min",
};
const EMPTY_STRING_REPLACEMENT = '"Stryker was here!"';

/** Offset of `op` between two operands, skipping comments and parentheses in the gap. */
function operatorOffset(src: string, op: string, left: AstNode, right: AstNode): number {
  const gap = src.slice(left.end, right.start);
  const at = gap.replace(/\/\*[\s\S]*?\*\/|\/\/[^\n]*/g, (c) => " ".repeat(c.length)).indexOf(op);
  return at === -1 ? -1 : left.end + at;
}

function isStringish(node: AstNode | undefined): boolean {
  if (!node) return false;
  return (
    (node.type === "Literal" && typeof node["value"] === "string") ||
    node.type === "TemplateLiteral"
  );
}

const binary: Operator = (node, ctx) => {
  if (node.type !== "BinaryExpression" && node.type !== "LogicalExpression") return;
  const op = stringField(node, "operator");
  const left = child(node, "left");
  const right = child(node, "right");
  if (!op || !left || !right) return;
  const at = operatorOffset(ctx.src, op, left, right);
  if (at === -1) return;
  const span = (rep: string, mutator: MutatorName) => ctx.emit(at, at + op.length, rep, mutator);

  if (node.type === "LogicalExpression") {
    const rep = LOGICAL[op];
    if (rep) span(rep, "LogicalOperator");
    return;
  }
  for (const rep of EQUALITY[op] ?? []) span(rep, "EqualityOperator");
  const arith = ARITHMETIC[op];
  // `"a" + b` is concatenation; Stryker leaves it alone and so do we.
  if (arith && !(op === "+" && (isStringish(left) || isStringish(right)))) {
    span(arith, "ArithmeticOperator");
  }
};

const booleanLiteral: Operator = (node, ctx) => {
  if (node.type === "Literal" && typeof node["value"] === "boolean") {
    ctx.emit(node.start, node.end, String(!node["value"]), "BooleanLiteral");
  }
  // Stryker files `!x` → `x` under BooleanLiteral, not UnaryOperator.
  if (node.type === "UnaryExpression" && node["operator"] === "!") {
    const arg = child(node, "argument");
    if (arg) ctx.emit(node.start, arg.start, "", "BooleanLiteral");
  }
};

const unary: Operator = (node, ctx) => {
  if (node.type !== "UnaryExpression") return;
  const arg = child(node, "argument");
  if (!arg) return;
  const op = node["operator"];
  if (op === "+") ctx.emit(node.start, arg.start, "-", "UnaryOperator");
  if (op === "-") ctx.emit(node.start, arg.start, "+", "UnaryOperator");
  if (op === "~") ctx.emit(node.start, arg.start, "", "UnaryOperator");
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

/** Strings that are names, not values: module specifiers, object keys, directives. */
function isStructuralString(ctx: OperatorContext): boolean {
  const p = ctx.parent;
  if (!p) return false;
  if (ctx.key === "source") return true; // import/export … from "x", import("x")
  if (
    (p.type === "Property" || p.type === "MethodDefinition" || p.type === "PropertyDefinition") &&
    ctx.key === "key"
  ) {
    return p["computed"] !== true;
  }
  if (p.type === "ExpressionStatement" && typeof p["directive"] === "string") return true;
  if (p.type === "JSXAttribute" && ctx.key === "name") return true;
  return p.type === "CallExpression" && calleeName(p) === "require";
}

const stringLiteral: Operator = (node, ctx) => {
  if (node.type !== "Literal" || typeof node["value"] !== "string") return;
  if (isStructuralString(ctx)) return;
  ctx.emit(
    node.start,
    node.end,
    node["value"] === "" ? EMPTY_STRING_REPLACEMENT : '""',
    "StringLiteral"
  );
};

const conditional: Operator = (node, ctx) => {
  const test = child(node, "test");
  if (!test) return;
  switch (node.type) {
    case "IfStatement":
    case "ConditionalExpression":
      ctx.emit(test.start, test.end, "true", "ConditionalExpression");
      ctx.emit(test.start, test.end, "false", "ConditionalExpression");
      break;
    // A loop forced to `true` never terminates; Stryker only tries `false`.
    case "WhileStatement":
    case "DoWhileStatement":
    case "ForStatement":
      ctx.emit(test.start, test.end, "false", "ConditionalExpression");
      break;
  }
};

/** Emptying a derived constructor drops super(), so constructing it always throws: a mutant no test needs to pin. */
function callsSuper(block: AstNode): boolean {
  return children(block, "body").some((s) => {
    const expr = child(s, "expression");
    return expr?.type === "CallExpression" && child(expr, "callee")?.type === "Super";
  });
}

const block: Operator = (node, ctx) => {
  if (node.type !== "BlockStatement" || children(node, "body").length === 0) return;
  if (callsSuper(node)) return;
  ctx.emit(node.start, node.end, "{}", "BlockStatement");
};

const arrayDeclaration: Operator = (node, ctx) => {
  if (node.type !== "ArrayExpression") return;
  const empty = children(node, "elements").length === 0;
  ctx.emit(node.start, node.end, empty ? '["Stryker was here"]' : "[]", "ArrayDeclaration");
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
  if (node.type !== "MemberExpression" || node["computed"] === true) return;
  if (ctx.parent?.type !== "CallExpression" || ctx.key !== "callee") return;
  const property = child(node, "property");
  const name = property && stringField(property, "name");
  const swap = name ? METHOD_SWAPS[name] : undefined;
  if (property && swap) ctx.emit(property.start, property.end, swap, "MethodExpression");
};

export const OPERATORS: readonly Operator[] = [
  binary,
  booleanLiteral,
  unary,
  update,
  stringLiteral,
  conditional,
  block,
  arrayDeclaration,
  optionalChaining,
  methodExpression,
];
