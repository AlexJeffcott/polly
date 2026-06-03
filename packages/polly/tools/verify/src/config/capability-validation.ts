// polly#160: config validation for `capabilities` and `coupledFields`.
//
// Pure functions returning ConfigIssue[] (the same shape the parser collects),
// so they are unit-testable without a config-file fixture.

import { extractFieldRefs, fieldInConfig } from "../analysis/expression-validator";
import type { ConfigIssue } from "../types";
import type { CapabilityConfig } from "./types";

/**
 * Validate capability declarations.
 *
 *  - G1: a non-empty `enabledBy`/`requires` expression that yields ZERO field
 *    references is a FATAL error. Bare identifiers ("authReady") pass through
 *    `tsExpressionToTLA` as free TLA+ identifiers AND `extractFieldRefs` returns
 *    `[]`, so without this guard the generated invariant is silently vacuous —
 *    exactly the silent-omission failure mode #160 exists to surface.
 *  - G2: every referenced field must resolve in the state config (reusing
 *    `fieldInConfig`), otherwise the invariant references an undeclared field.
 */
export function validateCapabilities(
  capabilities: CapabilityConfig[] | undefined,
  stateConfig: Record<string, unknown>
): ConfigIssue[] {
  if (!capabilities || capabilities.length === 0) return [];

  const issues: ConfigIssue[] = [];
  const configKeys = new Set(Object.keys(stateConfig));

  for (const cap of capabilities) {
    const name = cap.name?.trim();
    if (!name) {
      issues.push({
        type: "invalid_value",
        severity: "error",
        field: "capabilities",
        message: "Capability is missing a name.",
        suggestion: "Give each capability a unique name; it becomes the TLA+ invariant identifier.",
      });
      continue;
    }

    issues.push(
      ...validateExpression(name, "enabledBy", cap.enabledBy, configKeys, stateConfig),
      ...validateExpression(name, "requires", cap.requires, configKeys, stateConfig)
    );
  }

  return issues;
}

/** Validate one capability expression slot (enabledBy/requires): G1 + G2. */
function validateExpression(
  name: string,
  slot: "enabledBy" | "requires",
  expr: string | undefined,
  configKeys: Set<string>,
  stateConfig: Record<string, unknown>
): ConfigIssue[] {
  const field = `capabilities.${name}.${slot}`;

  if (!expr?.trim()) {
    return [
      {
        type: "capability_empty_expression",
        severity: "error",
        field,
        message: `Capability "${name}" has an empty ${slot} expression.`,
        suggestion: `Provide a state expression for ${slot}, e.g. "state.authenticated".`,
      },
    ];
  }

  const refs = extractFieldRefs(expr);

  // G1: a non-empty expression that references no modelled state field would
  // compile to a vacuous/free-identifier invariant.
  if (refs.length === 0) {
    return [
      {
        type: "capability_empty_expression",
        severity: "error",
        field,
        message: `Capability "${name}" ${slot} expression "${expr}" references no state field.`,
        suggestion:
          'Reference state via the state./.value form (e.g. "state.authReady"); a bare identifier produces a silently-vacuous invariant.',
      },
    ];
  }

  // G2: every referenced field must exist in the state config.
  return refs
    .filter((ref) => !fieldInConfig(ref, configKeys, stateConfig))
    .map((ref) => ({
      type: "capability_unknown_field",
      severity: "error",
      field,
      message: `Capability "${name}" ${slot} references "${ref}", which is not in the state config.`,
      suggestion: `Add "${ref}" to state, or correct the expression. Known fields: ${[...configKeys].join(", ")}`,
    }));
}

/**
 * Validate coupled-field groups: every field name must resolve in the state
 * config. (The strict-subset write detection itself is a runtime WARNING
 * produced later by `checkCoupledFields`, not here.)
 */
export function validateCoupledFields(
  coupledFields: string[][] | undefined,
  stateConfig: Record<string, unknown>
): ConfigIssue[] {
  if (!coupledFields || coupledFields.length === 0) return [];

  const issues: ConfigIssue[] = [];
  const configKeys = new Set(Object.keys(stateConfig));

  coupledFields.forEach((group, i) => {
    for (const field of group) {
      if (!fieldInConfig(field, configKeys, stateConfig)) {
        issues.push({
          type: "coupled_unknown_field",
          severity: "error",
          field: `coupledFields[${i}]`,
          message: `Coupled field "${field}" is not in the state config.`,
          suggestion: `Use a declared state field. Known fields: ${[...configKeys].join(", ")}`,
        });
      }
    }
  });

  return issues;
}
