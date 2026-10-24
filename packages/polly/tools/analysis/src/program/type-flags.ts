// ts-morph's synchronous `Type.isXxx()` predicates, re-expressed on
// typescript-7 type flags. Flags arrive with the type, so these cost no IPC.

import { type Type, TypeFlags } from "typescript-7/async";

const has = (type: Type, flag: TypeFlags): boolean => (type.flags & flag) !== 0;

/** ts-morph `type.isUnion()`, `isString()`, … — one predicate per ts-morph method the extractors called. */
export const typeIs = {
  union: (type: Type): boolean => has(type, TypeFlags.Union),
  boolean: (type: Type): boolean => has(type, TypeFlags.Boolean),
  booleanLiteral: (type: Type): boolean => has(type, TypeFlags.BooleanLiteral),
  string: (type: Type): boolean => has(type, TypeFlags.String),
  stringLiteral: (type: Type): boolean => has(type, TypeFlags.StringLiteral),
  number: (type: Type): boolean => has(type, TypeFlags.Number),
  numberLiteral: (type: Type): boolean => has(type, TypeFlags.NumberLiteral),
  object: (type: Type): boolean => has(type, TypeFlags.Object),
  null: (type: Type): boolean => has(type, TypeFlags.Null),
  undefined: (type: Type): boolean => has(type, TypeFlags.Undefined),
};

/**
 * ts-morph `type.getLiteralValue()` for string and number literal types.
 * Anything else is `undefined`, as in ts-morph (TS 6 keeps no `value` on a
 * boolean literal; TS 7 does, so it is not passed through).
 */
export function typeLiteralValue(type: Type): string | number | undefined {
  if (!type.isStringLiteralType() && !type.isNumberLiteralType()) return undefined;
  const value = type.value;
  return typeof value === "string" || typeof value === "number" ? value : undefined;
}
