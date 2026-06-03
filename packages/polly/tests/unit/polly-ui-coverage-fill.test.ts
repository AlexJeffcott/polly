/**
 * Targeted gap-fill for polly-ui mutation coverage (round 3).
 *
 * Kills the remaining *non-equivalent* survivors the broader suites left:
 * the trigger/option/wrapper class tokens on Select & ActionSelect, the
 * per-variant defaults and passthrough value-types on Surface, the
 * placeholder/aria/data-hook and actionData-merge paths on ActionInput,
 * Layout's aria forwarding, FileInput's fire-on-selection path, the
 * detached-button styling in dispatchAction, and Dropdown's
 * popovertarget / overlay:close effects.
 *
 * Equivalent survivors deliberately NOT chased here (documented in the
 * stryker_ui_coverage memory): the `if(prop) style[x]=prop` guards
 * (preact renders an undefined custom property identically to an absent
 * one), the `parts.filter(Boolean).join(" ")` method chains (every key
 * is truthy under the shim), the dashCase `toUpperCase` swap (HTML
 * attribute names are case-insensitive), and the ActionInput focus/select
 * effect (happy-dom does not move activeElement on focus()).
 */

import "./helpers/css-module-keys.ts";
import { afterAll, beforeAll, beforeEach, describe, expect, test } from "bun:test";
import { GlobalRegistrator } from "@happy-dom/global-registrator";
import type { VNode } from "preact";
import { installPopoverShim } from "./helpers/popover-shim.ts";

beforeAll(() => {
  GlobalRegistrator.register();
  installPopoverShim();
});

afterAll(async () => {
  await GlobalRegistrator.unregister();
});

const { h, render } = await import("preact");
const { act } = await import("preact/test-utils");
const { signal } = await import("@preact/signals");
const { Surface } = await import("../../src/polly-ui/Surface.tsx");
const { Layout } = await import("../../src/polly-ui/Layout.tsx");
const { Text } = await import("../../src/polly-ui/Text.tsx");
const { Output } = await import("../../src/polly-ui/Output.tsx");
const { ActionInput } = await import("../../src/polly-ui/ActionInput.tsx");
const { Select } = await import("../../src/polly-ui/Select.tsx");
const { ActionSelect } = await import("../../src/polly-ui/ActionSelect.tsx");
const { Dropdown } = await import("../../src/polly-ui/Dropdown.tsx");
const { FileInput } = await import("../../src/polly-ui/FileInput.tsx");
const { dispatchAction } = await import("../../src/polly-ui/internal/dispatch-action.ts");

function mount<P>(vnode: VNode<P>): HTMLElement {
  const host = document.createElement("div");
  document.body.appendChild(host);
  render(vnode, host);
  return host;
}
function rendered(host: HTMLElement): HTMLElement {
  const el = host.firstElementChild;
  if (!(el instanceof HTMLElement)) throw new Error("expected a rendered element");
  return el;
}
/** Mount and flush effects (useEffect) so post-mount DOM mutations land. */
async function mountActed<P>(vnode: VNode<P>): Promise<HTMLElement> {
  const host = document.createElement("div");
  document.body.appendChild(host);
  await act(async () => {
    render(vnode, host);
  });
  return host;
}
const cls = (el: Element | null | undefined): string[] =>
  (el?.getAttribute("class") ?? "").split(" ").filter(Boolean);
const sv = (el: HTMLElement, n: string): string => el.style.getPropertyValue(n);
const tick = (): Promise<void> => new Promise((r) => setTimeout(r, 0));
const triggerBtn = (host: HTMLElement): HTMLElement | null =>
  host.querySelector("[data-polly-dropdown] > button");

const OPTS = [
  { value: "a", label: "Alpha" },
  { value: "b", label: "Beta" },
  { value: "c", label: "Gamma" },
];

beforeEach(() => {
  document.body.innerHTML = "";
});

describe("Surface — remaining variant defaults", () => {
  test("sunken: sunken background, md radius, default border", () => {
    const el = rendered(mount(h(Surface, { variant: "sunken", children: "x" })));
    expect(sv(el, "--s-bg")).toBe("var(--polly-surface-sunken)");
    expect(sv(el, "--s-radius")).toBe("var(--polly-radius-md)");
    expect(sv(el, "--s-border-color")).toBe("var(--polly-border)");
  });
  test("bubble: md radius, default border, sm/md padding", () => {
    const el = rendered(mount(h(Surface, { variant: "bubble", children: "x" })));
    expect(sv(el, "--s-radius")).toBe("var(--polly-radius-md)");
    expect(sv(el, "--s-border-color")).toBe("var(--polly-border)");
    expect(sv(el, "--s-p")).toBe("var(--polly-space-sm) var(--polly-space-md)");
  });
  test("chip: xs/sm padding and inferred default border width", () => {
    const el = rendered(mount(h(Surface, { variant: "chip", children: "x" })));
    expect(sv(el, "--s-p")).toBe("var(--polly-space-xs) var(--polly-space-sm)");
    expect(sv(el, "--s-border-width")).toBe("var(--polly-border-width-default)");
  });
  test("callout: sm radius, default border, sm/md padding", () => {
    const el = rendered(mount(h(Surface, { variant: "callout", children: "x" })));
    expect(sv(el, "--s-radius")).toBe("var(--polly-radius-sm)");
    expect(sv(el, "--s-border-color")).toBe("var(--polly-border)");
    expect(sv(el, "--s-p")).toBe("var(--polly-space-sm) var(--polly-space-md)");
  });
  test("floating: raised background and large radius", () => {
    const el = rendered(mount(h(Surface, { variant: "floating", children: "x" })));
    expect(sv(el, "--s-bg")).toBe("var(--polly-surface-raised)");
    expect(sv(el, "--s-radius")).toBe("var(--polly-radius-lg)");
  });
});

describe("Surface — class/passthrough edges", () => {
  test("a non-inline Surface carries no inline class", () => {
    expect(cls(rendered(mount(h(Surface, { children: "x" }))))).not.toContain("inline");
  });
  test("className is appended, base class retained", () => {
    const el = rendered(mount(h(Surface, { className: "panel", children: "x" })));
    expect(cls(el)).toContain("surface");
    expect(cls(el)).toContain("panel");
  });
  test("numeric and boolean data-* values pass through", () => {
    const el = rendered(mount(h(Surface, { "data-count": 3, "data-live": true, children: "x" })));
    expect(el.getAttribute("data-count")).toBe("3");
    expect(el.getAttribute("data-live")).toBe("true");
  });
  test("an undefined data-* value is dropped, not rendered", () => {
    const el = rendered(mount(h(Surface, { "data-maybe": undefined, children: "x" })));
    expect(el.getAttribute("data-maybe")).toBeNull();
  });
  test("aria-labelledby and aria-describedby forward via explicit attrs", () => {
    const el = rendered(
      mount(h(Surface, { "aria-labelledby": "t1", "aria-describedby": "d1", children: "x" }))
    );
    expect(el.getAttribute("aria-labelledby")).toBe("t1");
    expect(el.getAttribute("aria-describedby")).toBe("d1");
  });
});

describe("Layout & Text — forwarded a11y / hooks", () => {
  test("Layout forwards aria-label/labelledby/describedby", () => {
    const el = rendered(
      mount(
        h(Layout, {
          "aria-label": "grid",
          "aria-labelledby": "h",
          "aria-describedby": "d",
          children: "x",
        })
      )
    );
    expect(el.getAttribute("aria-label")).toBe("grid");
    expect(el.getAttribute("aria-labelledby")).toBe("h");
    expect(el.getAttribute("aria-describedby")).toBe("d");
  });
  test("Text carries data-polly-ui=true and forwards className", () => {
    const el = rendered(mount(h(Text, { className: "mine", children: "x" })));
    expect(el.getAttribute("data-polly-ui")).toBe("true");
    expect(cls(el)).toContain("mine");
  });
  test("Output base class present and className appends", () => {
    const el = rendered(mount(h(Output, { className: "diag", children: "x" })));
    expect(cls(el)).toContain("output");
    expect(cls(el)).toContain("diag");
  });
});

describe("Select — class tokens & option marking", () => {
  test("trigger carries the trigger class; placeholder class only when empty", () => {
    const empty = mount(h(Select, { options: OPTS, selected: signal(new Set<string>()) }));
    expect(cls(triggerBtn(empty))).toContain("trigger");
    expect(cls(triggerBtn(empty))).toContain("placeholder");
    const filled = mount(h(Select, { options: OPTS, selected: signal(new Set(["a"])) }));
    expect(cls(triggerBtn(filled))).toContain("trigger");
    expect(cls(triggerBtn(filled))).not.toContain("placeholder");
  });
  test("wide adds the triggerWide class; default does not", () => {
    const wide = mount(h(Select, { options: OPTS, selected: signal(new Set(["a"])), wide: true }));
    expect(cls(triggerBtn(wide))).toContain("triggerWide");
    const narrow = mount(h(Select, { options: OPTS, selected: signal(new Set(["a"])) }));
    expect(cls(triggerBtn(narrow))).not.toContain("triggerWide");
  });
  test("wrapper has select class and appends className; label renders only when given", () => {
    const withLabel = rendered(
      mount(
        h(Select, {
          options: OPTS,
          selected: signal(new Set<string>()),
          label: "Status",
          className: "w",
        })
      )
    );
    expect(cls(withLabel)).toContain("select");
    expect(cls(withLabel)).toContain("w");
    const hasLabelSpan = (host: HTMLElement): boolean =>
      Array.from(host.querySelectorAll("span")).some((s) => cls(s).includes("label"));
    expect(hasLabelSpan(withLabel)).toBe(true);
    const noLabel = rendered(
      mount(h(Select, { options: OPTS, selected: signal(new Set<string>()) }))
    );
    expect(hasLabelSpan(noLabel)).toBe(false);
  });
  test("the selected option row carries optionSelected; others only option", () => {
    const host = mount(h(Select, { options: OPTS, selected: signal(new Set(["b"])) }));
    const rows = Array.from(host.querySelectorAll("[role='listbox'] button")) as HTMLElement[];
    const beta = rows.find((b) => b.textContent?.includes("Beta"));
    const alpha = rows.find((b) => b.textContent?.includes("Alpha"));
    expect(cls(beta)).toContain("optionSelected");
    expect(cls(alpha)).toContain("option");
    expect(cls(alpha)).not.toContain("optionSelected");
  });
  test("multi-select rows carry a readonly, unfocusable checkbox reflecting selection", () => {
    const host = mount(
      h(Select, { options: OPTS, selected: signal(new Set(["a"])), multiSelect: true })
    );
    const rows = Array.from(host.querySelectorAll("[role='listbox'] button")) as HTMLElement[];
    const alpha = rows.find((b) => b.textContent?.includes("Alpha"));
    const beta = rows.find((b) => b.textContent?.includes("Beta"));
    const box = (row: HTMLElement | undefined): HTMLInputElement =>
      row?.querySelector("input[type='checkbox']") as HTMLInputElement;
    expect(box(alpha).checked).toBe(true);
    expect(box(beta).checked).toBe(false);
    expect(box(alpha).readOnly).toBe(true);
    expect(box(alpha).tabIndex).toBe(-1);
  });
  test("single-select rows have no checkbox", () => {
    const host = mount(h(Select, { options: OPTS, selected: signal(new Set(["a"])) }));
    expect(host.querySelector("input[type='checkbox']")).toBeNull();
  });
  test("formatSelected output is exact (no stray labels)", () => {
    const single = mount(h(Select, { options: OPTS, selected: signal(new Set(["b"])) }));
    expect(triggerBtn(single)?.textContent?.trim()).toBe("Beta");
    const two = mount(
      h(Select, { options: OPTS, selected: signal(new Set(["a", "b"])), multiSelect: true })
    );
    expect(two.querySelector("[class~='triggerLabel']")?.textContent).toBe("Alpha, Beta");
  });
  test("the dropdown starts closed", () => {
    const host = mount(h(Select, { options: OPTS, selected: signal(new Set(["a"])) }));
    expect(triggerBtn(host)?.getAttribute("data-open")).toBe("false");
  });
});

describe("ActionSelect — class tokens & option marking", () => {
  test("trigger carries trigger/placeholder/triggerWide classes appropriately", () => {
    const empty = mount(h(ActionSelect, { value: "zz", action: "s", options: OPTS }));
    expect(cls(triggerBtn(empty))).toContain("trigger");
    expect(cls(triggerBtn(empty))).toContain("placeholder");
    const wide = mount(h(ActionSelect, { value: "a", action: "s", options: OPTS, wide: true }));
    expect(cls(triggerBtn(wide))).toContain("triggerWide");
    expect(cls(triggerBtn(wide))).not.toContain("placeholder");
  });
  test("wrapper has select class, appends className, and renders a label only when given", () => {
    const el = rendered(
      mount(h(ActionSelect, { value: "a", action: "s", options: OPTS, label: "L", className: "w" }))
    );
    expect(cls(el)).toContain("select");
    expect(cls(el)).toContain("w");
    expect(el.textContent).toContain("L");
    const noLabel = rendered(mount(h(ActionSelect, { value: "a", action: "s", options: OPTS })));
    expect(Array.from(noLabel.querySelectorAll("span")).some((s) => cls(s).includes("label"))).toBe(
      false
    );
  });
  test("selected option carries optionSelected; others only option", () => {
    const host = mount(h(ActionSelect, { value: "a", action: "s", options: OPTS }));
    const opts = Array.from(host.querySelectorAll("[role='option']")) as HTMLElement[];
    const alpha = opts.find((o) => o.textContent?.includes("Alpha"));
    const beta = opts.find((o) => o.textContent?.includes("Beta"));
    expect(cls(alpha)).toContain("optionSelected");
    expect(cls(beta)).not.toContain("optionSelected");
  });
  test("the dropdown starts closed", () => {
    const host = mount(h(ActionSelect, { value: "a", action: "s", options: OPTS }));
    expect(triggerBtn(host)?.getAttribute("data-open")).toBe("false");
  });
});

describe("ActionInput — class, a11y, placeholder, data hooks", () => {
  test("view element carries root+view classes and the data hooks", () => {
    const el = rendered(mount(h(ActionInput, { value: "v", action: "a", className: "mine" })));
    expect(cls(el)).toContain("root");
    expect(cls(el)).toContain("view");
    expect(cls(el)).toContain("mine");
    expect(el.getAttribute("data-polly-ui")).toBe("true");
    expect(el.getAttribute("data-polly-interactive")).not.toBeNull();
  });
  test("edit element carries edit+root classes", () => {
    const el = rendered(mount(h(ActionInput, { value: "", action: "a", saveOn: "input" })));
    expect(cls(el)).toContain("edit");
    expect(cls(el)).toContain("root");
  });
  test("default aria-label is 'Edit' in both modes", () => {
    expect(
      rendered(mount(h(ActionInput, { value: "v", action: "a" }))).getAttribute("aria-label")
    ).toBe("Edit");
    expect(
      rendered(mount(h(ActionInput, { value: "", action: "a", saveOn: "input" }))).getAttribute(
        "aria-label"
      )
    ).toBe("Edit");
  });
  test("placeholder shows only for an empty value, never when filled", () => {
    const empty = rendered(mount(h(ActionInput, { value: "", action: "a", placeholder: "ph" })));
    expect(empty.textContent).toContain("ph");
    expect(
      Array.from(empty.querySelectorAll("span")).some((s) => cls(s).includes("placeholder"))
    ).toBe(true);
    const filled = rendered(mount(h(ActionInput, { value: "hi", action: "a", placeholder: "ph" })));
    expect(filled.textContent).toBe("hi");
    expect(filled.textContent).not.toContain("ph");
  });
  test("actionData extras are merged into the commit, not dropped", async () => {
    const seen: Record<string, string> = {};
    const onClick = (e: Event): void => {
      const el = e.target;
      if (el instanceof Element && el.getAttribute("data-action") === "save") {
        seen["value"] = el.getAttribute("data-action-value") ?? "";
        seen["tid"] = el.getAttribute("data-action-tid") ?? "";
      }
    };
    document.addEventListener("click", onClick);
    const host = mount(
      h(ActionInput, { value: "old", action: "save", saveOn: "enter", actionData: { tid: "7" } })
    );
    rendered(host).dispatchEvent(new MouseEvent("click", { bubbles: true }));
    await tick();
    const input = rendered(host) as HTMLInputElement;
    input.value = "new";
    input.dispatchEvent(new Event("input", { bubbles: true }));
    await tick();
    input.dispatchEvent(new KeyboardEvent("keydown", { key: "Enter", bubbles: true }));
    document.removeEventListener("click", onClick);
    expect(seen["value"]).toBe("new");
    expect(seen["tid"]).toBe("7");
  });
});

describe("FileInput — fires on a non-empty selection; class tokens", () => {
  test("a non-empty change fires onFiles with the FileList", () => {
    const calls: FileList[] = [];
    const el = rendered(
      mount(
        h(FileInput, {
          onFiles: (f) => {
            calls.push(f);
          },
        })
      )
    );
    const input = el.querySelector("input") as HTMLInputElement;
    const file = new File(["x"], "a.txt", { type: "text/plain" });
    const list = { 0: file, length: 1, item: () => file } as unknown as FileList;
    Object.defineProperty(input, "files", { value: list, configurable: true });
    input.dispatchEvent(new Event("change", { bubbles: true }));
    expect(calls[0]).toBe(list);
  });
  test("base class present; disabled adds disabled class; native input carries the native class", () => {
    const el = rendered(mount(h(FileInput, { onFiles: () => {}, disabled: true, className: "k" })));
    expect(cls(el)).toContain("fileInput");
    expect(cls(el)).toContain("disabled");
    expect(cls(el)).toContain("k");
    expect(cls(el.querySelector("input"))).toContain("native");
  });
  test("an enabled FileInput has no disabled class", () => {
    expect(cls(rendered(mount(h(FileInput, { onFiles: () => {} }))))).not.toContain("disabled");
  });
});

describe("dispatchAction — detached button styling and cleanup", () => {
  test("the dispatched button is fixed, invisible, click-through, and unfocusable", () => {
    const seen: Record<string, string> = {};
    const onClick = (e: Event): void => {
      const el = e.target as HTMLElement;
      if (el.getAttribute?.("data-action") === "noop") {
        seen["position"] = el.style.position;
        seen["opacity"] = el.style.opacity;
        seen["pointerEvents"] = el.style.pointerEvents;
        seen["tabIndex"] = String(el.tabIndex);
      }
    };
    document.addEventListener("click", onClick);
    dispatchAction("noop", { value: "v" });
    document.removeEventListener("click", onClick);
    expect(seen["position"]).toBe("fixed");
    expect(seen["opacity"]).toBe("0");
    expect(seen["pointerEvents"]).toBe("none");
    expect(seen["tabIndex"]).toBe("-1");
  });
});

describe("Dropdown — popovertarget & overlay:close effects", () => {
  test("the trigger's popovertarget points at the menu id (after effects run)", async () => {
    const el = rendered(
      await mountActed(h(Dropdown, { isOpen: signal(false), trigger: "t", children: "m" }))
    );
    const button = el.querySelector("button") as HTMLElement;
    const menu = el.querySelector("[role='listbox']") as HTMLElement;
    expect(button.getAttribute("popovertarget")).toBe(menu.id);
  });
  test("an overlay:close for this menu id closes it; a different id does not", async () => {
    const isOpen = signal(true);
    const el = rendered(await mountActed(h(Dropdown, { isOpen, trigger: "t", children: "m" })));
    const menu = el.querySelector("[role='listbox']") as HTMLElement;
    menu.dispatchEvent(
      new CustomEvent("overlay:close", { detail: { id: "other" }, bubbles: true })
    );
    expect(isOpen.value).toBe(true);
    menu.dispatchEvent(
      new CustomEvent("overlay:close", { detail: { id: menu.id }, bubbles: true })
    );
    expect(isOpen.value).toBe(false);
  });
  test("className appends to the dropdown wrapper", () => {
    const el = rendered(
      mount(
        h(Dropdown, { isOpen: signal(false), trigger: "t", className: "menu-wrap", children: "m" })
      )
    );
    expect(cls(el)).toContain("dropdown");
    expect(cls(el)).toContain("menu-wrap");
  });
});
