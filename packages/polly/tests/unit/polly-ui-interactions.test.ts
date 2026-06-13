/**
 * Interaction mutation coverage for the stateful primitives:
 * ActionInput (view/edit modes, the saveOn × variant keyboard matrix,
 * commit/cancel), Select (formatSelected, single/multi option handling,
 * select-all/clear), ActionSelect (label lookup, commit, disabled
 * branch), and Dropdown (toggle/menu-click/escape handlers, trigger and
 * menu attributes). Commit paths are observed through the real
 * dispatchAction click, signal paths through the bound Signal's value.
 *
 * Not covered here: Dropdown.positionMenu — pure viewport geometry that
 * needs a real layout engine + Popover top layer (happy-dom has neither);
 * it is verified by the issue's ui-screenshots harness.
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
const { signal } = await import("@preact/signals");
const { ActionInput } = await import("../../src/polly-ui/ActionInput.tsx");
const { Select } = await import("../../src/polly-ui/Select.tsx");
const { ActionSelect } = await import("../../src/polly-ui/ActionSelect.tsx");
const { Dropdown } = await import("../../src/polly-ui/Dropdown.tsx");

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

/** Narrow to a concrete element type via instanceof; throws instead of casting. */
function asElement<T extends Element>(v: unknown, ctor: new () => T): T {
  if (!(v instanceof ctor)) throw new Error(`expected ${ctor.name}`);
  return v;
}

const tick = (): Promise<void> => new Promise((r) => setTimeout(r, 0));

/** Capture data-action-value strings dispatched for `action`. */
function captureActions(action: string): { values: string[]; stop: () => void } {
  const values: string[] = [];
  const onClick = (e: Event): void => {
    const el = e.target;
    if (el instanceof Element && el.getAttribute("data-action") === action) {
      values.push(el.getAttribute("data-action-value") ?? "");
    }
  };
  document.addEventListener("click", onClick);
  return { values, stop: () => document.removeEventListener("click", onClick) };
}

beforeEach(() => {
  document.body.innerHTML = "";
});

// ── ActionInput ──────────────────────────────────────────────────────

describe("ActionInput — view mode", () => {
  test("default saveOn renders a role=button view with state/variant hooks", () => {
    const el = rendered(mount(h(ActionInput, { value: "Title", action: "a" })));
    expect(el.getAttribute("role")).toBe("button");
    expect(el.getAttribute("data-polly-action-input")).not.toBeNull();
    expect(el.getAttribute("data-state")).toBe("filled");
    expect(el.getAttribute("data-variant")).toBe("single");
    expect(el.getAttribute("tabindex")).toBe("0");
  });

  test("empty value is data-state=empty and shows the placeholder", () => {
    const el = rendered(
      mount(h(ActionInput, { value: "", action: "a", placeholder: "Add a title" }))
    );
    expect(el.getAttribute("data-state")).toBe("empty");
    expect(el.textContent).toContain("Add a title");
  });

  test("disabled view has tabindex -1, aria-disabled, and ignores clicks", async () => {
    const host = mount(h(ActionInput, { value: "v", action: "a", disabled: true }));
    const el = rendered(host);
    expect(el.getAttribute("tabindex")).toBe("-1");
    expect(el.getAttribute("aria-disabled")).toBe("true");
    el.dispatchEvent(new MouseEvent("click", { bubbles: true }));
    await tick();
    expect(rendered(host).tagName).not.toBe("INPUT");
  });

  test("ariaLabel overrides the default edit affordance label", () => {
    const el = rendered(mount(h(ActionInput, { value: "v", action: "a", ariaLabel: "Rename" })));
    expect(el.getAttribute("aria-label")).toBe("Rename");
  });

  test("renderView customises view-mode output", () => {
    const el = rendered(
      mount(h(ActionInput, { value: "raw", action: "a", renderView: (v) => `[${v}]` }))
    );
    expect(el.textContent).toBe("[raw]");
  });

  test("click enters edit mode as an input", async () => {
    const host = mount(h(ActionInput, { value: "v", action: "a" }));
    rendered(host).dispatchEvent(new MouseEvent("click", { bubbles: true }));
    await tick();
    expect(rendered(host).tagName).toBe("INPUT");
    expect(rendered(host).getAttribute("data-state")).toBe("editing");
  });

  test("Enter and Space from view enter edit mode and preventDefault", async () => {
    for (const key of ["Enter", " "]) {
      const host = mount(h(ActionInput, { value: "v", action: "a" }));
      const ev = new KeyboardEvent("keydown", { key, bubbles: true, cancelable: true });
      rendered(host).dispatchEvent(ev);
      expect(ev.defaultPrevented).toBe(true);
      await tick();
      expect(rendered(host).tagName).toBe("INPUT");
    }
  });

  test("an unrelated key does not enter edit mode", async () => {
    const host = mount(h(ActionInput, { value: "v", action: "a" }));
    rendered(host).dispatchEvent(new KeyboardEvent("keydown", { key: "a", bubbles: true }));
    await tick();
    expect(rendered(host).tagName).not.toBe("INPUT");
  });
});

describe("ActionInput — edit mode shape", () => {
  test("saveOn='input' starts editing immediately", () => {
    const el = rendered(mount(h(ActionInput, { value: "", action: "a", saveOn: "input" })));
    expect(el.tagName).toBe("INPUT");
    expect(el.getAttribute("data-state")).toBe("editing");
  });

  test("inputType sets the native input type", () => {
    const el = asElement(
      rendered(
        mount(
          h(ActionInput, { value: "2026-01-01", action: "a", saveOn: "input", inputType: "date" })
        )
      ),
      HTMLInputElement
    );
    expect(el.type).toBe("date");
  });

  test("variant='multi' renders a textarea in edit mode", () => {
    const el = rendered(
      mount(h(ActionInput, { value: "x", action: "a", saveOn: "input", variant: "multi" }))
    );
    expect(el.tagName).toBe("TEXTAREA");
  });
});

describe("ActionInput — commit matrix", () => {
  test("saveOn='input' commits every keystroke and stays in edit", async () => {
    const cap = captureActions("filter");
    const host = mount(h(ActionInput, { value: "", action: "filter", saveOn: "input" }));
    const input = asElement(rendered(host), HTMLInputElement);
    input.value = "ab";
    input.dispatchEvent(new Event("input", { bubbles: true }));
    cap.stop();
    expect(cap.values).toContain("ab");
    await tick();
    expect(rendered(host).tagName).toBe("INPUT"); // never toggles to view
  });

  test("saveOn='enter' single-line commits on Enter and prevents default", async () => {
    const cap = captureActions("rename");
    const host = mount(h(ActionInput, { value: "old", action: "rename", saveOn: "enter" }));
    rendered(host).dispatchEvent(new MouseEvent("click", { bubbles: true }));
    await tick();
    const input = asElement(rendered(host), HTMLInputElement);
    input.value = "new";
    input.dispatchEvent(new Event("input", { bubbles: true }));
    await tick(); // let the new draft bind into the keydown handler
    const ev = new KeyboardEvent("keydown", { key: "Enter", bubbles: true, cancelable: true });
    input.dispatchEvent(ev);
    cap.stop();
    expect(ev.defaultPrevented).toBe(true);
    expect(cap.values).toContain("new");
  });

  test("saveOn='cmd-enter' commits only with the modifier", async () => {
    const cap = captureActions("note");
    const host = mount(
      h(ActionInput, { value: "old", action: "note", saveOn: "cmd-enter", variant: "multi" })
    );
    rendered(host).dispatchEvent(new MouseEvent("click", { bubbles: true }));
    await tick();
    const input = asElement(rendered(host), HTMLTextAreaElement);
    input.value = "new";
    input.dispatchEvent(new Event("input", { bubbles: true }));
    await tick();
    // plain Enter: no commit
    input.dispatchEvent(new KeyboardEvent("keydown", { key: "Enter", bubbles: true }));
    expect(cap.values).not.toContain("new");
    // Cmd+Enter: commit
    input.dispatchEvent(
      new KeyboardEvent("keydown", { key: "Enter", metaKey: true, bubbles: true })
    );
    cap.stop();
    expect(cap.values).toContain("new");
  });

  test("saveOn='enter' multi-line needs the modifier (plain Enter inserts a newline)", async () => {
    const cap = captureActions("desc");
    const host = mount(
      h(ActionInput, { value: "old", action: "desc", saveOn: "enter", variant: "multi" })
    );
    rendered(host).dispatchEvent(new MouseEvent("click", { bubbles: true }));
    await tick();
    const input = asElement(rendered(host), HTMLTextAreaElement);
    input.value = "new";
    input.dispatchEvent(new Event("input", { bubbles: true }));
    await tick();
    input.dispatchEvent(new KeyboardEvent("keydown", { key: "Enter", bubbles: true }));
    expect(cap.values).not.toContain("new");
    input.dispatchEvent(
      new KeyboardEvent("keydown", { key: "Enter", ctrlKey: true, bubbles: true })
    );
    cap.stop();
    expect(cap.values).toContain("new");
  });

  test("saveOn='blur' commits the draft when focus leaves", async () => {
    const cap = captureActions("title");
    const host = mount(h(ActionInput, { value: "old", action: "title", saveOn: "blur" }));
    rendered(host).dispatchEvent(new MouseEvent("click", { bubbles: true }));
    await tick();
    const input = asElement(rendered(host), HTMLInputElement);
    input.value = "new";
    input.dispatchEvent(new Event("input", { bubbles: true }));
    await tick();
    input.dispatchEvent(new FocusEvent("blur", { bubbles: true }));
    cap.stop();
    expect(cap.values).toContain("new");
  });

  test("commit is suppressed when the value is unchanged", async () => {
    const cap = captureActions("same");
    const host = mount(h(ActionInput, { value: "x", action: "same", saveOn: "enter" }));
    rendered(host).dispatchEvent(new MouseEvent("click", { bubbles: true }));
    await tick();
    const input = asElement(rendered(host), HTMLInputElement);
    // leave value as "x"
    input.dispatchEvent(new KeyboardEvent("keydown", { key: "Enter", bubbles: true }));
    cap.stop();
    expect(cap.values).toEqual([]);
  });

  test("Escape cancels: prevents default and returns to view mode", async () => {
    const host = mount(h(ActionInput, { value: "v", action: "a", saveOn: "enter" }));
    rendered(host).dispatchEvent(new MouseEvent("click", { bubbles: true }));
    await tick();
    const input = asElement(rendered(host), HTMLInputElement);
    input.value = "changed";
    input.dispatchEvent(new Event("input", { bubbles: true }));
    const ev = new KeyboardEvent("keydown", { key: "Escape", bubbles: true, cancelable: true });
    input.dispatchEvent(ev);
    expect(ev.defaultPrevented).toBe(true);
    await tick();
    expect(rendered(host).getAttribute("role")).toBe("button"); // back in view
  });

  test("blur outside blur-mode cancels back to view rather than committing", async () => {
    const cap = captureActions("x");
    const host = mount(h(ActionInput, { value: "v", action: "x", saveOn: "enter" }));
    rendered(host).dispatchEvent(new MouseEvent("click", { bubbles: true }));
    await tick();
    const input = asElement(rendered(host), HTMLInputElement);
    input.value = "changed";
    input.dispatchEvent(new Event("input", { bubbles: true }));
    input.dispatchEvent(new FocusEvent("blur", { bubbles: true }));
    cap.stop();
    expect(cap.values).toEqual([]);
    await tick();
    expect(rendered(host).getAttribute("role")).toBe("button");
  });
});

// ── Select ───────────────────────────────────────────────────────────

const OPTS = [
  { value: "a", label: "Alpha" },
  { value: "b", label: "Beta" },
  { value: "c", label: "Gamma" },
];

function triggerLabel(host: HTMLElement): string {
  return host.querySelector("[data-polly-dropdown] > button")?.textContent ?? "";
}

describe("Select — formatSelected", () => {
  test("empty selection shows the placeholder", () => {
    const host = mount(
      h(Select, { options: OPTS, selected: signal(new Set<string>()), placeholder: "Pick" })
    );
    expect(triggerLabel(host)).toContain("Pick");
  });

  test("single-select shows the chosen label", () => {
    const host = mount(h(Select, { options: OPTS, selected: signal(new Set(["b"])) }));
    expect(triggerLabel(host)).toContain("Beta");
  });

  test("multi-select at or below the threshold joins labels", () => {
    const host = mount(
      h(Select, { options: OPTS, selected: signal(new Set(["a", "b"])), multiSelect: true })
    );
    expect(triggerLabel(host)).toContain("Alpha, Beta");
  });

  test("multi-select above the threshold collapses to a count", () => {
    const host = mount(
      h(Select, { options: OPTS, selected: signal(new Set(["a", "b", "c"])), multiSelect: true })
    );
    expect(triggerLabel(host)).toContain("3 selected");
  });
});

describe("Select — option handling", () => {
  test("single-select replaces the set and closes", () => {
    const selected = signal(new Set(["a"]));
    const host = mount(h(Select, { options: OPTS, selected }));
    const optionButtons = host.querySelectorAll("[role='listbox'] button");
    asElement(optionButtons[1], HTMLButtonElement).click(); // Beta
    expect([...selected.value]).toEqual(["b"]);
  });

  test("multi-select toggles membership without closing", () => {
    const selected = signal(new Set(["a"]));
    const host = mount(h(Select, { options: OPTS, selected, multiSelect: true }));
    const buttons = Array.from(host.querySelectorAll<HTMLButtonElement>("[role='listbox'] button"));
    const beta = buttons.find((b) => b.textContent?.includes("Beta"));
    const alpha = buttons.find((b) => b.textContent?.includes("Alpha"));
    beta?.click();
    expect(selected.value.has("b")).toBe(true);
    alpha?.click(); // toggling an already-selected one removes it
    expect(selected.value.has("a")).toBe(false);
  });

  test("Select All selects every option; Clear empties the set", () => {
    const selected = signal(new Set<string>());
    const host = mount(h(Select, { options: OPTS, selected, multiSelect: true }));
    const byText = (t: string): HTMLButtonElement | undefined =>
      Array.from(host.querySelectorAll("button")).find((b) => b.textContent?.trim() === t);
    byText("Select All")?.click();
    expect(selected.value.size).toBe(3);
    byText("Clear")?.click();
    expect(selected.value.size).toBe(0);
  });

  test("single-select renders no Select All / Clear actions", () => {
    const host = mount(h(Select, { options: OPTS, selected: signal(new Set<string>()) }));
    const labels = Array.from(host.querySelectorAll("button")).map((b) => b.textContent);
    expect(labels.some((l) => l?.includes("Select All"))).toBe(false);
  });

  test("a visible label renders above the trigger", () => {
    const host = mount(
      h(Select, { options: OPTS, selected: signal(new Set<string>()), label: "Status" })
    );
    expect(host.textContent).toContain("Status");
  });

  test("clearable single-select prepends a placeholder option that empties the set", () => {
    const selected = signal(new Set(["a"]));
    const host = mount(
      h(Select, { options: OPTS, selected, clearable: true, placeholder: "Any stage" })
    );
    const clear = host.querySelector("[data-polly-select-clear]");
    const first = host.querySelector("[role='listbox'] button");
    expect(clear).not.toBeNull();
    expect(clear).toBe(first); // sits above the real options
    expect(clear?.textContent).toContain("Any stage");
    asElement(clear, HTMLButtonElement).click();
    expect(selected.value.size).toBe(0);
  });

  test("the clear option is marked selected only while the set is empty", () => {
    const emptyHost = mount(
      h(Select, { options: OPTS, selected: signal(new Set<string>()), clearable: true })
    );
    const emptyClear = asElement(
      emptyHost.querySelector("[data-polly-select-clear]"),
      HTMLButtonElement
    );
    expect(emptyClear.className).toContain("optionSelected");

    const filledHost = mount(
      h(Select, { options: OPTS, selected: signal(new Set(["a"])), clearable: true })
    );
    const filledClear = asElement(
      filledHost.querySelector("[data-polly-select-clear]"),
      HTMLButtonElement
    );
    expect(filledClear.className).not.toContain("optionSelected");
  });

  test("clearable is ignored in multi-select, which has Clear already", () => {
    const host = mount(
      h(Select, {
        options: OPTS,
        selected: signal(new Set<string>()),
        clearable: true,
        multiSelect: true,
      })
    );
    expect(host.querySelector("[data-polly-select-clear]")).toBeNull();
  });

  test("without clearable, single-select renders no clear option", () => {
    const host = mount(h(Select, { options: OPTS, selected: signal(new Set<string>()) }));
    expect(host.querySelector("[data-polly-select-clear]")).toBeNull();
  });
});

// ── ActionSelect ─────────────────────────────────────────────────────

describe("ActionSelect", () => {
  test("renders the matching option label and data-state=filled", () => {
    const el = rendered(mount(h(ActionSelect, { value: "a", action: "s", options: OPTS })));
    expect(el.getAttribute("data-state")).toBe("filled");
    expect(el.textContent).toContain("Alpha");
  });

  test("an unmatched value shows the placeholder and data-state=empty", () => {
    const el = rendered(
      mount(h(ActionSelect, { value: "zzz", action: "s", options: OPTS, placeholder: "Choose" }))
    );
    expect(el.getAttribute("data-state")).toBe("empty");
    expect(el.textContent).toContain("Choose");
  });

  test("disabled renders static text with no dropdown, button, or caret", () => {
    const el = rendered(
      mount(h(ActionSelect, { value: "a", action: "s", options: OPTS, disabled: true }))
    );
    expect(el.querySelector("[data-polly-dropdown]")).toBeNull();
    expect(el.querySelector("button")).toBeNull();
    expect(el.querySelector('[aria-hidden="true"]')).toBeNull();
    expect(el.textContent).toContain("Alpha");
  });

  test("choosing an option commits its value through the action system", () => {
    const cap = captureActions("set");
    const host = mount(h(ActionSelect, { value: "a", action: "set", options: OPTS }));
    const opt = Array.from(host.querySelectorAll<HTMLButtonElement>("[role='option']")).find((o) =>
      o.textContent?.includes("Beta")
    );
    opt?.click();
    cap.stop();
    expect(cap.values).toContain("b");
  });

  test("re-choosing the current value commits nothing", () => {
    const cap = captureActions("set");
    const host = mount(h(ActionSelect, { value: "a", action: "set", options: OPTS }));
    const opt = Array.from(host.querySelectorAll<HTMLButtonElement>("[role='option']")).find((o) =>
      o.textContent?.includes("Alpha")
    );
    opt?.click();
    cap.stop();
    expect(cap.values).toEqual([]);
  });

  test("the selected option is marked aria-selected", () => {
    const host = mount(h(ActionSelect, { value: "a", action: "s", options: OPTS }));
    const opts = Array.from(host.querySelectorAll("[role='option']"));
    const alpha = opts.find((o) => o.textContent?.includes("Alpha"));
    const beta = opts.find((o) => o.textContent?.includes("Beta"));
    expect(alpha?.getAttribute("aria-selected")).toBe("true");
    expect(beta?.getAttribute("aria-selected")).toBe("false");
  });

  test("data-* passthrough rides the outer element", () => {
    const el = rendered(
      mount(h(ActionSelect, { value: "a", action: "s", options: OPTS, "data-x": "1" }))
    );
    expect(el.getAttribute("data-x")).toBe("1");
  });
});

// ── Dropdown ─────────────────────────────────────────────────────────

describe("Dropdown — handlers and attributes", () => {
  test("data-open mirrors isOpen in both states", () => {
    const closed = rendered(
      mount(h(Dropdown, { isOpen: signal(false), trigger: "t", children: "m" }))
    );
    expect(closed.querySelector("button")?.getAttribute("data-open")).toBe("false");
    const open = rendered(
      mount(h(Dropdown, { isOpen: signal(true), trigger: "t", children: "m" }))
    );
    expect(open.querySelector("button")?.getAttribute("data-open")).toBe("true");
  });

  test("the menu carries popover, role, align, and overlay-id attributes", () => {
    const el = rendered(
      mount(h(Dropdown, { isOpen: signal(false), trigger: "t", align: "right", children: "m" }))
    );
    const menu = asElement(el.querySelector("[role='listbox']"), HTMLElement);
    expect(menu.getAttribute("popover")).toBe("auto");
    expect(menu.getAttribute("data-align")).toBe("right");
    expect(menu.getAttribute("data-overlay-id")).toBe(menu.id);
    expect(menu.id.length).toBeGreaterThan(0);
  });

  test("align defaults to left", () => {
    const el = rendered(mount(h(Dropdown, { isOpen: signal(false), trigger: "t", children: "m" })));
    expect(el.querySelector("[role='listbox']")?.getAttribute("data-align")).toBe("left");
  });

  test("triggerClassName replaces the default trigger class; triggerDisabled disables it", () => {
    const el = rendered(
      mount(
        h(Dropdown, {
          isOpen: signal(false),
          trigger: "t",
          triggerClassName: "myTrigger",
          triggerDisabled: true,
          children: "m",
        })
      )
    );
    const button = asElement(el.querySelector("button"), HTMLButtonElement);
    expect((button.getAttribute("class") ?? "").split(" ")).toContain("myTrigger");
    expect(button.disabled).toBe(true);
  });

  test("clicking the menu closes a single-select dropdown", () => {
    const isOpen = signal(true);
    const el = rendered(mount(h(Dropdown, { isOpen, trigger: "t", children: "m" })));
    asElement(el.querySelector("[role='listbox']"), HTMLElement).dispatchEvent(
      new MouseEvent("click", { bubbles: true })
    );
    expect(isOpen.value).toBe(false);
  });

  test("clicking the menu keeps a multiSelect dropdown open", () => {
    const isOpen = signal(true);
    const el = rendered(
      mount(h(Dropdown, { isOpen, trigger: "t", multiSelect: true, children: "m" }))
    );
    asElement(el.querySelector("[role='listbox']"), HTMLElement).dispatchEvent(
      new MouseEvent("click", { bubbles: true })
    );
    expect(isOpen.value).toBe(true);
  });

  test("Escape on the menu closes the dropdown", () => {
    const isOpen = signal(true);
    const el = rendered(mount(h(Dropdown, { isOpen, trigger: "t", children: "m" })));
    asElement(el.querySelector("[role='listbox']"), HTMLElement).dispatchEvent(
      new KeyboardEvent("keydown", { key: "Escape", bubbles: true })
    );
    expect(isOpen.value).toBe(false);
  });

  test("a non-Escape key on the menu does not close it", () => {
    const isOpen = signal(true);
    const el = rendered(mount(h(Dropdown, { isOpen, trigger: "t", children: "m" })));
    asElement(el.querySelector("[role='listbox']"), HTMLElement).dispatchEvent(
      new KeyboardEvent("keydown", { key: "ArrowDown", bubbles: true })
    );
    expect(isOpen.value).toBe(true);
  });

  test("each Dropdown gets a distinct overlay id", () => {
    const a = rendered(mount(h(Dropdown, { isOpen: signal(false), trigger: "t", children: "m" })));
    const b = rendered(mount(h(Dropdown, { isOpen: signal(false), trigger: "t", children: "m" })));
    const idA = a.querySelector("[role='listbox']")?.id;
    const idB = b.querySelector("[role='listbox']")?.id;
    expect(idA).not.toBe(idB);
  });
});
