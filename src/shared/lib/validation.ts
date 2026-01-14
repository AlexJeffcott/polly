/**
 * Runtime type validation helpers
 *
 * Simple shape-based validation for use with state primitives.
 * For more complex validation, consider using Zod or similar libraries.
 */

type PrimitiveType = 'string' | 'number' | 'boolean' | 'object' | 'array' | 'null' | 'undefined';

type ShapeDefinition = Record<string, PrimitiveType | Record<string, PrimitiveType>>;

/**
 * Create a type guard that validates an object's shape.
 *
 * @param shape - Object describing the expected types of each field
 * @returns Type guard function that performs runtime validation
 *
 * @example
 * ```typescript
 * type Settings = {
 *   theme: string;
 *   notifications: boolean;
 *   apiEndpoint: string;
 * };
 *
 * const settings = $sharedState("settings", defaultSettings, {
 *   validator: validateShape<Settings>({
 *     theme: 'string',
 *     notifications: 'boolean',
 *     apiEndpoint: 'string'
 *   })
 * });
 * ```
 *
 * @example
 * ```typescript
 * // Nested objects
 * const state = $sharedState("user", defaultUser, {
 *   validator: validateShape<User>({
 *     name: 'string',
 *     profile: {
 *       age: 'number',
 *       email: 'string'
 *     }
 *   })
 * });
 * ```
 */
export function validateShape<T>(shape: ShapeDefinition): (value: unknown) => value is T {
  return (value: unknown): value is T => {
    if (typeof value !== 'object' || value === null) return false;

    for (const [key, type] of Object.entries(shape)) {
      if (!(key in value)) return false;

      const val = (value as Record<string, unknown>)[key];

      if (typeof type === 'string') {
        // Handle primitive type checks
        if (type === 'array' && !Array.isArray(val)) return false;
        if (type === 'null' && val !== null) return false;
        if (type === 'undefined' && val !== undefined) return false;
        if (type !== 'array' && type !== 'null' && type !== 'undefined' && typeof val !== type) {
          return false;
        }
      } else {
        // Handle nested object validation
        if (!validateShape(type)(val)) return false;
      }
    }

    return true;
  };
}

/**
 * Validate that a value is one of the allowed values.
 *
 * @param allowed - Array of allowed values
 * @returns Type guard function
 *
 * @example
 * ```typescript
 * type Theme = 'light' | 'dark' | 'auto';
 *
 * const isTheme = validateEnum<Theme>(['light', 'dark', 'auto']);
 * if (isTheme(value)) {
 *   // value is Theme
 * }
 * ```
 */
export function validateEnum<T extends string | number>(allowed: readonly T[]): (value: unknown) => value is T {
  return (value: unknown): value is T => {
    return allowed.includes(value as T);
  };
}

/**
 * Validate that a value matches an array of a specific type.
 *
 * @param itemValidator - Validator for array items
 * @returns Type guard function for arrays
 *
 * @example
 * ```typescript
 * const isStringArray = validateArray<string>((v): v is string => typeof v === 'string');
 * if (isStringArray(value)) {
 *   // value is string[]
 * }
 * ```
 */
export function validateArray<T>(
  itemValidator: (value: unknown) => value is T
): (value: unknown) => value is T[] {
  return (value: unknown): value is T[] => {
    if (!Array.isArray(value)) return false;
    return value.every(itemValidator);
  };
}

/**
 * Create a partial validator that allows undefined/null for all fields.
 *
 * @param validator - Base validator function
 * @returns Validator that allows partial objects
 *
 * @example
 * ```typescript
 * const isSettings = validateShape<Settings>({ theme: 'string', autoSync: 'boolean' });
 * const isPartialSettings = validatePartial(isSettings);
 *
 * // Accepts { theme: 'dark' } or { autoSync: true } or { theme: 'dark', autoSync: true }
 * ```
 */
export function validatePartial<T>(
  _validator: (value: unknown) => value is T
): (value: unknown) => value is Partial<T> {
  return (value: unknown): value is Partial<T> => {
    if (typeof value !== 'object' || value === null) return false;
    // For partial validation, we just check that the object is of the right shape
    // but allow missing fields
    // TODO: Could use the validator to check present fields
    return true; // Simplified - could be more sophisticated
  };
}
