/**
 * Narrow views over oxc-parser's ESTree / TS-ESTree output. The walker treats
 * the AST as plain data, so these guards replace casts: every field read goes
 * through a typeof check.
 */
import { isRecord } from "../../../../src/shared/lib/guards";

export interface AstNode {
  type: string;
  start: number;
  end: number;
  [key: string]: unknown;
}

export function isAstNode(value: unknown): value is AstNode {
  return (
    isRecord(value) &&
    typeof value["type"] === "string" &&
    typeof value["start"] === "number" &&
    typeof value["end"] === "number"
  );
}

/** The child node under `key`, or undefined when absent or not a node. */
export function child(node: AstNode, key: string): AstNode | undefined {
  const value = node[key];
  return isAstNode(value) ? value : undefined;
}

export function children(node: AstNode, key: string): AstNode[] {
  const value = node[key];
  return Array.isArray(value) ? value.filter(isAstNode) : [];
}

export function stringField(node: AstNode, key: string): string | undefined {
  const value = node[key];
  return typeof value === "string" ? value : undefined;
}

/** `foo(...)` → "foo"; `verify.foo(...)` → "foo"; computed access is not resolved. */
export function calleeName(call: AstNode): string | undefined {
  const callee = child(call, "callee");
  if (!callee) return undefined;
  if (callee.type === "Identifier") return stringField(callee, "name");
  if (callee.type === "MemberExpression" && callee["computed"] !== true) {
    const property = child(callee, "property");
    if (property?.type === "Identifier") return stringField(property, "name");
  }
  return undefined;
}
