/**
 * Minimal Popover-API no-op shim for happy-dom.
 *
 * happy-dom does not implement the Popover API: `element.showPopover` is
 * `undefined`, so Dropdown's open/close signal effect throws the moment
 * `isOpen` becomes true. This shim installs no-op `showPopover` /
 * `hidePopover` and a `matches(":popover-open")` that reflects the
 * tracked open set, so the open/close *orchestration* (call showPopover
 * when opening, hidePopover when closing, mirror onto `data-open`) is
 * exercisable. It deliberately does NOT emulate the top layer or layout:
 * Dropdown's `positionMenu` geometry depends on real getBoundingClientRect
 * /offsetWidth values and is verified by the issue's screenshot harness,
 * not here.
 *
 * Call `installPopoverShim()` after `GlobalRegistrator.register()` (the
 * DOM globals must exist first). Idempotent.
 */

const openEls = new WeakSet<Element>();

export function installPopoverShim(): void {
  const proto = (globalThis as unknown as { HTMLElement?: { prototype: Record<string, unknown> } })
    .HTMLElement?.prototype;
  if (!proto || proto["__pollyPopoverShim"]) return;
  proto["__pollyPopoverShim"] = true;

  proto["showPopover"] = function showPopover(this: Element): void {
    openEls.add(this);
  };
  proto["hidePopover"] = function hidePopover(this: Element): void {
    openEls.delete(this);
  };

  const origMatches = proto["matches"];
  if (typeof origMatches !== "function") {
    throw new Error("popover-shim: HTMLElement.prototype.matches is not a function");
  }
  proto["matches"] = function matches(this: Element, sel: string): boolean {
    if (sel === ":popover-open") return openEls.has(this);
    return Boolean(origMatches.call(this, sel));
  };
}
