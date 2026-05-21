/**
 * polly#125: data-* / aria-* attribute passthrough for UI primitives.
 *
 * Primitives accept a fixed prop set. Without passthrough, a consumer
 * that needs a `data-*` test hook or an `aria-*` attribute on the
 * primitive's own element has to wrap it in an extra DOM node — a smell.
 *
 * {@link PassthroughAttrs} widens a primitive's props to accept any
 * `data-*` / `aria-*` key; {@link collectPassthrough} gathers them for
 * spreading onto the rendered root element. Spread the result *before*
 * the primitive's own attributes so a consumer key can never override
 * one the primitive sets itself (`data-polly-*`, etc.).
 */

/** Index signatures letting a primitive's props accept arbitrary
 *  `data-*` and `aria-*` attributes. */
export type PassthroughAttrs = {
  [dataAttr: `data-${string}`]: string | number | boolean | undefined;
  [ariaAttr: `aria-${string}`]: string | number | boolean | undefined;
};

/**
 * Collect `data-*` and `aria-*` attributes from a props object so they
 * can be spread onto a primitive's root element. `undefined` values and
 * non-attribute value types (functions, objects) are dropped.
 */
export function collectPassthrough(
  props: Record<string, unknown>
): Record<string, string | number | boolean> {
  const out: Record<string, string | number | boolean> = {};
  for (const key of Object.keys(props)) {
    if (!key.startsWith("data-") && !key.startsWith("aria-")) continue;
    const value = props[key];
    if (typeof value === "string" || typeof value === "number" || typeof value === "boolean") {
      out[key] = value;
    }
  }
  return out;
}
