/**
 * The element's inline style declaration, or `undefined` for an element
 * that has none (one outside the HTML, SVG and MathML namespaces).
 */
export function inlineStyleOf(el: Element): CSSStyleDeclaration | undefined {
  if (!("style" in el)) return undefined;
  const { style } = el;
  return style instanceof CSSStyleDeclaration ? style : undefined;
}
