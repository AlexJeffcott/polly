// State-field configuration for @fairfox/polly/verify.
//
// The one definition of the `state` and `mesh` config shapes. It imports
// nothing, so the dependency-light public entry point (config.ts) and the
// internal CLI types (types.ts) can both use it.

/**
 * A state field, or an object of them. The codegen flattens a nested object
 * into `parent_child` fields (`collectNestedFields`), matching the extractor's
 * `user.role` → `user_role`.
 */
export type StateConfig = { [field: string]: FieldConfig | StateConfig };

/** The `[false, true]` boolean shorthand of FieldConfig. */
export type BooleanPair = readonly [boolean, boolean];

export function isBooleanPair(config: FieldConfig | StateConfig): config is BooleanPair {
  return (
    Array.isArray(config) &&
    config.length === 2 &&
    typeof config[0] === "boolean" &&
    typeof config[1] === "boolean"
  );
}

/**
 * polly#117: mesh-document declarations. Maps docId → field schema.
 */
export type MeshConfig = Record<string, Record<string, FieldConfig>>;

export type FieldConfig =
  | { type: "boolean" }
  /** Boolean shorthand, e.g. `[false, true]`. The first element is the initial value. */
  | BooleanPair
  | { type: "array"; maxLength?: number | null; initial?: unknown[] }
  | { type: "string"; initial?: string }
  | { type: "number"; min?: number; max?: number }
  | { maxLength: number | null }
  | { min: number | null; max: number | null }
  | { type: "enum"; values: string[] }
  | { values: string[] | null; abstract?: boolean; nullable?: boolean }
  | { maxSize: number | null; valueType?: string }
  | { abstract: boolean; nullable?: boolean };
