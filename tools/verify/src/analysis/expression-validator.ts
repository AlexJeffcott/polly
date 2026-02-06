/**
 * Validates requires()/ensures() expressions before TLA+ codegen.
 * Catches patterns that produce broken TLA+ and gives actionable warnings.
 */

import type { MessageHandler } from "../core/model";

// ─────────────────────────────────────────────────────────────────
// Types
// ─────────────────────────────────────────────────────────────────

export type ExpressionWarning = {
  kind:
    | "unmodeled_field"
    | "unsupported_method"
    | "optional_chaining"
    | "null_comparison"
    | "weak_postcondition";
  message: string;
  messageType: string;
  conditionType: "requires" | "ensures";
  expression: string;
  location: { file: string; line: number; column: number };
  suggestion: string;
};

export type ValidationResult = {
  warnings: ExpressionWarning[];
  validCount: number;
  warnCount: number;
};

// ─────────────────────────────────────────────────────────────────
// Field reference extraction
// ─────────────────────────────────────────────────────────────────

// Same patterns the TLA+ generator uses (tla.ts Phase 2b/2c)
const SIGNAL_VALUE_FIELD = /([a-zA-Z_]\w*)\.value\.([a-zA-Z_][\w.]*)/g;
const SIGNAL_VALUE_BARE = /([a-zA-Z_]\w*)\.value\b(?!\.)/g;
const STATE_DOT_FIELD = /state\.([a-zA-Z_][\w.]*)/g;
const PAYLOAD_REF = /payload\.\w+/;

/**
 * Extract state field references from an expression, returning
 * config-compatible field names (dot-form and underscore-form).
 */
function extractFieldRefs(expression: string): string[] {
  const refs: string[] = [];

  // Pattern 1: xxx.value.yyy.zzz → xxx.yyy.zzz (strip .value.)
  for (const m of expression.matchAll(SIGNAL_VALUE_FIELD)) {
    const prefix = m[1];
    const suffix = m[2];
    refs.push(`${prefix}.${suffix}`);
  }

  // Pattern 2: xxx.value (no suffix) → xxx
  for (const m of expression.matchAll(SIGNAL_VALUE_BARE)) {
    refs.push(m[1]);
  }

  // Pattern 3: state.xxx.yyy → xxx.yyy
  for (const m of expression.matchAll(STATE_DOT_FIELD)) {
    refs.push(m[1]);
  }

  // Deduplicate
  return [...new Set(refs)];
}

/**
 * Check if a field reference matches a key in the state config.
 * Tries both dot-form (user.loggedIn) and underscore-form (user_loggedIn).
 */
function fieldInConfig(
  fieldRef: string,
  configKeys: Set<string>,
  stateConfig?: Record<string, unknown>
): boolean {
  if (configKeys.has(fieldRef)) return true;
  // Try underscore form
  const underscored = fieldRef.replace(/\./g, "_");
  if (configKeys.has(underscored)) return true;
  // Try dot form from underscore
  const dotted = fieldRef.replace(/_/g, ".");
  if (configKeys.has(dotted)) return true;

  // Handle .length on array/collection fields: "todos.length" is valid if "todos" is array-like
  if (stateConfig && fieldRef.endsWith(".length")) {
    const parent = fieldRef.slice(0, -".length".length);
    const parentEntry = resolveConfigEntry(parent, stateConfig);
    if (parentEntry !== undefined && isArrayLike(parentEntry)) return true;
  }

  return false;
}

/**
 * Resolve the config entry for a field ref, trying both dot and underscore forms.
 */
function resolveConfigEntry(
  fieldRef: string,
  stateConfig: Record<string, unknown>
): unknown | undefined {
  if (fieldRef in stateConfig) return stateConfig[fieldRef];
  const underscored = fieldRef.replace(/\./g, "_");
  if (underscored in stateConfig) return stateConfig[underscored];
  const dotted = fieldRef.replace(/_/g, ".");
  if (dotted in stateConfig) return stateConfig[dotted];
  return undefined;
}

// ─────────────────────────────────────────────────────────────────
// Type resolution helpers
// ─────────────────────────────────────────────────────────────────

function isArrayLike(configEntry: unknown): boolean {
  if (configEntry && typeof configEntry === "object") {
    const obj = configEntry as Record<string, unknown>;
    if (obj.type === "array") return true;
    if ("maxLength" in obj) return true;
    if ("maxSize" in obj) return true;
  }
  return false;
}

function isNullable(configEntry: unknown): boolean {
  if (Array.isArray(configEntry)) {
    return configEntry.includes(null);
  }
  if (configEntry && typeof configEntry === "object") {
    const obj = configEntry as Record<string, unknown>;
    // { abstract: true } allows extra values including null-like
    if (obj.abstract === true) return true;
    // { values: [...] } — check if null is in the values array
    if (Array.isArray(obj.values)) {
      return obj.values.includes(null);
    }
  }
  return false;
}

// ─────────────────────────────────────────────────────────────────
// 5 checks
// ─────────────────────────────────────────────────────────────────

const UNSUPPORTED_METHODS = /\.(some|every|find|filter)\s*\(/;
const OPTIONAL_CHAIN = /\?\./;
const NULL_COMPARISON = /(===?\s*null|!==?\s*null|null\s*===?|null\s*!==?)/;

function checkUnmodeledFields(
  expression: string,
  configKeys: Set<string>,
  stateConfig: Record<string, unknown>,
  messageType: string,
  conditionType: "requires" | "ensures",
  location: { file: string; line: number; column: number }
): ExpressionWarning[] {
  const warnings: ExpressionWarning[] = [];
  const refs = extractFieldRefs(expression);

  for (const ref of refs) {
    if (!fieldInConfig(ref, configKeys, stateConfig)) {
      warnings.push({
        kind: "unmodeled_field",
        message: `${conditionType}() in ${messageType} references unmodeled field '${ref}'`,
        messageType,
        conditionType,
        expression,
        location,
        suggestion: `Add '${ref}' to state config or remove from ${conditionType}()`,
      });
    }
  }

  return warnings;
}

function checkUnsupportedMethods(
  expression: string,
  configKeys: Set<string>,
  stateConfig: Record<string, unknown>,
  messageType: string,
  conditionType: "requires" | "ensures",
  location: { file: string; line: number; column: number }
): ExpressionWarning[] {
  const match = expression.match(UNSUPPORTED_METHODS);
  if (!match) return [];

  // If the method is called on a field not in config, the unmodeled check covers it
  const refs = extractFieldRefs(expression);
  const allUnmodeled =
    refs.length > 0 && refs.every((r) => !fieldInConfig(r, configKeys, stateConfig));
  if (allUnmodeled) return [];

  return [
    {
      kind: "unsupported_method",
      message: `${conditionType}() in ${messageType} uses .${match[1]}() which cannot be translated to TLA+`,
      messageType,
      conditionType,
      expression,
      location,
      suggestion: `Rewrite without .${match[1]}() or model the check as a boolean state field`,
    },
  ];
}

function checkOptionalChaining(
  expression: string,
  messageType: string,
  conditionType: "requires" | "ensures",
  location: { file: string; line: number; column: number }
): ExpressionWarning[] {
  if (!OPTIONAL_CHAIN.test(expression)) return [];

  return [
    {
      kind: "optional_chaining",
      message: `${conditionType}() in ${messageType} uses optional chaining (?.)`,
      messageType,
      conditionType,
      expression,
      location,
      suggestion:
        "Optional chaining translation is fragile — consider explicit null checks or restructuring",
    },
  ];
}

function checkNullComparisons(
  expression: string,
  stateConfig: Record<string, unknown>,
  configKeys: Set<string>,
  messageType: string,
  conditionType: "requires" | "ensures",
  location: { file: string; line: number; column: number }
): ExpressionWarning[] {
  if (!NULL_COMPARISON.test(expression)) return [];

  const warnings: ExpressionWarning[] = [];
  const refs = extractFieldRefs(expression);

  for (const ref of refs) {
    if (!fieldInConfig(ref, configKeys, stateConfig)) continue;
    const entry = resolveConfigEntry(ref, stateConfig);
    if (entry !== undefined && !isNullable(entry)) {
      warnings.push({
        kind: "null_comparison",
        message: `${conditionType}() in ${messageType} compares '${ref}' to null but field is not nullable`,
        messageType,
        conditionType,
        expression,
        location,
        suggestion: `Add null to '${ref}' values in state config, or remove the null check`,
      });
    }
  }

  return warnings;
}

// Pattern: fieldRef !== <literal>  (weak negation in ensures)
const WEAK_NEGATION =
  /([a-zA-Z_][\w.]*(?:\.value\.[\w.]+|\.value\b|))?\s*!==?\s*("[^"]*"|'[^']*'|\d+|true|false|null)/;

function checkWeakPostconditions(
  expression: string,
  handler: MessageHandler,
  messageType: string,
  conditionType: "requires" | "ensures",
  location: { file: string; line: number; column: number }
): ExpressionWarning[] {
  if (conditionType !== "ensures") return [];

  const match = expression.match(WEAK_NEGATION);
  if (!match) return [];

  // Extract the field being compared
  const refs = extractFieldRefs(expression);
  if (refs.length === 0) return [];

  // Check if any of the referenced fields have a concrete assignment in this handler
  for (const ref of refs) {
    const underscoredRef = ref.replace(/\./g, "_");
    const hasAssignment = handler.assignments.some(
      (a) => a.field === ref || a.field === underscoredRef || a.field.replace(/_/g, ".") === ref
    );
    if (hasAssignment) {
      const assignment = handler.assignments.find(
        (a) => a.field === ref || a.field === underscoredRef || a.field.replace(/_/g, ".") === ref
      );
      const assignedValue = assignment ? JSON.stringify(assignment.value) : "<value>";
      return [
        {
          kind: "weak_postcondition",
          message: `ensures() in ${messageType} uses !== for '${ref}' which has a concrete assignment`,
          messageType,
          conditionType,
          expression,
          location,
          suggestion: `Consider ensures(${ref} === ${assignedValue}) for a stronger postcondition`,
        },
      ];
    }
  }

  return [];
}

// ─────────────────────────────────────────────────────────────────
// Main validator
// ─────────────────────────────────────────────────────────────────

export function validateExpressions(
  handlers: MessageHandler[],
  stateConfig: Record<string, unknown>
): ValidationResult {
  const warnings: ExpressionWarning[] = [];
  let validCount = 0;
  const configKeys = new Set(Object.keys(stateConfig));

  for (const handler of handlers) {
    const conditions: Array<{
      cond: { expression: string; location: { line: number; column: number } };
      type: "requires" | "ensures";
    }> = [
      ...handler.preconditions.map((c) => ({
        cond: c,
        type: "requires" as const,
      })),
      ...handler.postconditions.map((c) => ({
        cond: c,
        type: "ensures" as const,
      })),
    ];

    for (const { cond, type } of conditions) {
      // Skip payload-only expressions (not state refs)
      const refs = extractFieldRefs(cond.expression);
      const isPayloadOnly = refs.length === 0 && PAYLOAD_REF.test(cond.expression);

      const loc = {
        file: handler.location.file,
        line: cond.location.line,
        column: cond.location.column,
      };

      const condWarnings: ExpressionWarning[] = [];

      if (!isPayloadOnly) {
        condWarnings.push(
          ...checkUnmodeledFields(
            cond.expression,
            configKeys,
            stateConfig,
            handler.messageType,
            type,
            loc
          )
        );
      }

      condWarnings.push(
        ...checkUnsupportedMethods(
          cond.expression,
          configKeys,
          stateConfig,
          handler.messageType,
          type,
          loc
        )
      );

      condWarnings.push(...checkOptionalChaining(cond.expression, handler.messageType, type, loc));

      condWarnings.push(
        ...checkNullComparisons(
          cond.expression,
          stateConfig,
          configKeys,
          handler.messageType,
          type,
          loc
        )
      );

      condWarnings.push(
        ...checkWeakPostconditions(cond.expression, handler, handler.messageType, type, loc)
      );

      if (condWarnings.length === 0) {
        validCount++;
      } else {
        warnings.push(...condWarnings);
      }
    }
  }

  return { warnings, validCount, warnCount: warnings.length };
}
