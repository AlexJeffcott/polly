/**
 * Round-5 gap-fill: the last clearly-killable survivors —
 * Dropdown's open/close signal effect and default trigger/menu class
 * tokens, and the nested-element class tokens on Select & ActionSelect
 * (actions bar, Select All / Clear buttons, option / optionSelected
 * rows, the multi-select checkbox, the label and disabled-trigger spans).
 *
 * `act` flushes the useSignalEffect so showPopover/hidePopover (no-op
 * shimmed) run and `:popover-open` reflects the open state.
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
const { Dropdown } = await import("../../src/polly-ui/Dropdown.tsx");
const { Select } = await import("../../src/polly-ui/Select.tsx");
const { ActionSelect } = await import("../../src/polly-ui/ActionSelect.tsx");

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
const cls = (el: Element | null | undefined): string[] =>
  (el?.getAttribute("class") ?? "").split(" ").filter(Boolean);
const triggerBtn = (host: HTMLElement): HTMLElement | null =>
  host.querySelector("[data-polly-dropdown] > button");

const OPTS = [
  { value: "a", label: "Alpha" },
  { value: "b", label: "Beta" },
];

beforeEach(() => {
  document.body.innerHTML = "";
});

describe("Dropdown — open/close effect and default classes", () => {
  test("the signal effect shows the popover when opened and hides it when closed", async () => {
    const isOpen = signal(false);
    const host = document.createElement("div");
    document.body.appendChild(host);
    await act(async () => {
      render(h(Dropdown, { isOpen, trigger: "t", children: "m" }), host);
    });
    const menu = host.querySelector("[role='listbox']") as HTMLElement & {
      matches: (s: string) => boolean;
    };
    expect(menu.matches(":popover-open")).toBe(false);
    await act(async () => {
      isOpen.value = true;
    });
    expect(menu.matches(":popover-open")).toBe(true);
    await act(async () => {
      isOpen.value = false;
    });
    expect(menu.matches(":popover-open")).toBe(false);
  });

  test("with no triggerClassName the trigger uses the default trigger class", () => {
    const el = rendered(mount(h(Dropdown, { isOpen: signal(false), trigger: "t", children: "m" })));
    expect(cls(el.querySelector("button"))).toContain("trigger");
  });

  test("the menu carries the menu class", () => {
    const el = rendered(mount(h(Dropdown, { isOpen: signal(false), trigger: "t", children: "m" })));
    expect(cls(el.querySelector("[role='listbox']"))).toContain("menu");
  });
});

describe("Select — nested element class tokens", () => {
  test("multi-select renders an actions bar with Select All / Clear actionBtns", () => {
    const host = mount(
      h(Select, { options: OPTS, selected: signal(new Set<string>()), multiSelect: true })
    );
    const actions = host.querySelector("[class~='actions']");
    expect(actions).not.toBeNull();
    const btns = Array.from(host.querySelectorAll("button")).filter((b) =>
      ["Select All", "Clear"].includes(b.textContent?.trim() ?? "")
    );
    expect(btns.length).toBe(2);
    for (const b of btns) expect(cls(b)).toContain("actionBtn");
  });

  test("the selected option row has both option and optionSelected; unselected has option only", () => {
    const host = mount(h(Select, { options: OPTS, selected: signal(new Set(["a"])) }));
    const rows = Array.from(host.querySelectorAll("[role='listbox'] button")) as HTMLElement[];
    const alpha = rows.find((b) => b.textContent?.includes("Alpha"));
    const beta = rows.find((b) => b.textContent?.includes("Beta"));
    expect(cls(alpha)).toContain("option");
    expect(cls(alpha)).toContain("optionSelected");
    expect(cls(beta)).toContain("option");
    expect(cls(beta)).not.toContain("optionSelected");
  });

  test("the multi-select checkbox carries the optionCheck class", () => {
    const host = mount(
      h(Select, { options: OPTS, selected: signal(new Set(["a"])), multiSelect: true })
    );
    expect(cls(host.querySelector("input[type='checkbox']"))).toContain("optionCheck");
  });

  test("the dropdown trigger is not disabled by default", () => {
    const host = mount(h(Select, { options: OPTS, selected: signal(new Set(["a"])) }));
    expect((triggerBtn(host) as HTMLButtonElement).disabled).toBe(false);
  });

  test("disabled propagates to the trigger button", () => {
    const host = mount(
      h(Select, { options: OPTS, selected: signal(new Set(["a"])), disabled: true })
    );
    expect((triggerBtn(host) as HTMLButtonElement).disabled).toBe(true);
  });
});

describe("ActionSelect — nested element class tokens", () => {
  test("the visible label renders inside a span carrying the label class", () => {
    const host = mount(
      h(ActionSelect, { value: "a", action: "s", options: OPTS, label: "Status" })
    );
    const labelSpan = Array.from(host.querySelectorAll("span")).find(
      (s) => s.textContent === "Status" && cls(s).includes("label")
    );
    expect(labelSpan).not.toBeUndefined();
  });

  test("the disabled trigger text sits in a triggerLabel span", () => {
    const el = rendered(
      mount(h(ActionSelect, { value: "a", action: "s", options: OPTS, disabled: true }))
    );
    const span = el.querySelector("[class~='triggerLabel']");
    expect(span?.textContent).toBe("Alpha");
  });

  test("selected option has option+optionSelected; unselected has option only", () => {
    const host = mount(h(ActionSelect, { value: "a", action: "s", options: OPTS }));
    const opts = Array.from(host.querySelectorAll("[role='option']")) as HTMLElement[];
    const alpha = opts.find((o) => o.textContent?.includes("Alpha"));
    const beta = opts.find((o) => o.textContent?.includes("Beta"));
    expect(cls(alpha)).toContain("option");
    expect(cls(alpha)).toContain("optionSelected");
    expect(cls(beta)).toContain("option");
    expect(cls(beta)).not.toContain("optionSelected");
  });
});
