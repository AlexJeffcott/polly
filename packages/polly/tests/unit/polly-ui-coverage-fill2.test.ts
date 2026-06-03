/**
 * Round-4 gap-fill: the last batch of non-equivalent survivors —
 * default placeholders, boolean defaults (`wide`), nested span class
 * tokens (caret/triggerLabel/label/summary/content), the ActionSelect
 * actionData merge, the remaining ActionInput commit-matrix paths
 * (default-blur commit, commit→view, printable-key no-commit, edit-mode
 * data hooks, blur-in-non-blur-mode), and the data-polly-ui/-html
 * boolean attributes on Cluster/Html.
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
const { Select } = await import("../../src/polly-ui/Select.tsx");
const { ActionSelect } = await import("../../src/polly-ui/ActionSelect.tsx");
const { ActionInput } = await import("../../src/polly-ui/ActionInput.tsx");
const { Cluster } = await import("../../src/polly-ui/Cluster.tsx");
const { Html } = await import("../../src/polly-ui/Html.tsx");
const { Collapsible } = await import("../../src/polly-ui/Collapsible.tsx");

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
const tick = (): Promise<void> => new Promise((r) => setTimeout(r, 0));
const triggerBtn = (host: HTMLElement): HTMLElement | null =>
  host.querySelector("[data-polly-dropdown] > button");
const trigLabel = (host: HTMLElement): string =>
  host.querySelector("[class~='triggerLabel']")?.textContent ?? "";

function captureAll(action: string): { rows: Record<string, string>[]; stop: () => void } {
  const rows: Record<string, string>[] = [];
  const onClick = (e: Event): void => {
    const el = e.target;
    if (el instanceof Element && el.getAttribute("data-action") === action) {
      const row: Record<string, string> = {};
      for (const a of el.getAttributeNames()) {
        if (a.startsWith("data-action")) row[a] = el.getAttribute(a) ?? "";
      }
      rows.push(row);
    }
  };
  document.addEventListener("click", onClick);
  return { rows, stop: () => document.removeEventListener("click", onClick) };
}

const OPTS = [
  { value: "a", label: "Alpha" },
  { value: "b", label: "Beta" },
];

beforeEach(() => {
  document.body.innerHTML = "";
});

describe("Select / ActionSelect — defaults and nested class tokens", () => {
  test("Select default placeholder is the ellipsis 'Select…'", () => {
    const host = mount(h(Select, { options: OPTS, selected: signal(new Set<string>()) }));
    expect(trigLabel(host)).toBe("Select…");
  });
  test("ActionSelect default placeholder is 'Select…' for an unmatched value", () => {
    const host = mount(h(ActionSelect, { value: "zz", action: "s", options: OPTS }));
    expect(trigLabel(host)).toBe("Select…");
  });
  test("wide defaults off: no triggerWide class on either Select or ActionSelect", () => {
    const s = mount(h(Select, { options: OPTS, selected: signal(new Set(["a"])) }));
    expect(cls(triggerBtn(s))).not.toContain("triggerWide");
    const as = mount(h(ActionSelect, { value: "a", action: "s", options: OPTS }));
    expect(cls(triggerBtn(as))).not.toContain("triggerWide");
  });
  test("the trigger carries a triggerLabel span and an aria-hidden caret", () => {
    const host = mount(h(Select, { options: OPTS, selected: signal(new Set(["a"])) }));
    const btn = triggerBtn(host);
    expect(cls(btn?.querySelector("[class~='triggerLabel']"))).toContain("triggerLabel");
    const caret = btn?.querySelector("[class~='caret']");
    expect(caret).not.toBeNull();
    expect(caret?.getAttribute("aria-hidden")).toBe("true");
  });
  test("ActionSelect options render their label inside a span and mark the caret", () => {
    const host = mount(h(ActionSelect, { value: "a", action: "s", options: OPTS }));
    const opt = host.querySelector("[role='option']");
    expect(opt?.querySelector("span")?.textContent).toBe("Alpha");
    expect(host.querySelector("[class~='caret']")?.getAttribute("aria-hidden")).toBe("true");
  });
});

describe("ActionSelect — actionData merge on commit", () => {
  test("extra actionData rides onto the committed action", () => {
    const cap = captureAll("set");
    const host = mount(
      h(ActionSelect, { value: "a", action: "set", options: OPTS, actionData: { tid: "7" } })
    );
    const beta = Array.from(host.querySelectorAll("[role='option']")).find((o) =>
      o.textContent?.includes("Beta")
    ) as HTMLButtonElement | undefined;
    beta?.click();
    cap.stop();
    expect(cap.rows.length).toBe(1);
    expect(cap.rows[0]?.["data-action-value"]).toBe("b");
    expect(cap.rows[0]?.["data-action-tid"]).toBe("7");
  });
});

describe("ActionInput — remaining commit-matrix paths", () => {
  test("the default (no saveOn) commits on blur", async () => {
    const cap = captureAll("t");
    const host = mount(h(ActionInput, { value: "old", action: "t" }));
    rendered(host).dispatchEvent(new MouseEvent("click", { bubbles: true }));
    await tick();
    const input = rendered(host) as HTMLInputElement;
    input.value = "new";
    input.dispatchEvent(new Event("input", { bubbles: true }));
    await tick();
    input.dispatchEvent(new FocusEvent("blur", { bubbles: true }));
    cap.stop();
    expect(cap.rows.map((r) => r["data-action-value"])).toContain("new");
  });

  test("a successful Enter commit returns the field to view mode", async () => {
    const host = mount(h(ActionInput, { value: "old", action: "t", saveOn: "enter" }));
    rendered(host).dispatchEvent(new MouseEvent("click", { bubbles: true }));
    await tick();
    const input = rendered(host) as HTMLInputElement;
    input.value = "new";
    input.dispatchEvent(new Event("input", { bubbles: true }));
    await tick();
    input.dispatchEvent(new KeyboardEvent("keydown", { key: "Enter", bubbles: true }));
    await tick();
    expect(rendered(host).getAttribute("role")).toBe("button");
  });

  test("a printable key in edit mode does not commit (only Enter/Escape act)", async () => {
    const cap = captureAll("t");
    const host = mount(h(ActionInput, { value: "old", action: "t", saveOn: "enter" }));
    rendered(host).dispatchEvent(new MouseEvent("click", { bubbles: true }));
    await tick();
    const input = rendered(host) as HTMLInputElement;
    input.value = "new";
    input.dispatchEvent(new Event("input", { bubbles: true }));
    await tick();
    input.dispatchEvent(new KeyboardEvent("keydown", { key: "x", bubbles: true }));
    cap.stop();
    expect(cap.rows).toEqual([]);
  });

  test("single-line cmd-enter mode ignores a plain Enter and commits on Cmd+Enter", async () => {
    const cap = captureAll("t");
    const host = mount(h(ActionInput, { value: "old", action: "t", saveOn: "cmd-enter" }));
    rendered(host).dispatchEvent(new MouseEvent("click", { bubbles: true }));
    await tick();
    const input = rendered(host) as HTMLInputElement;
    input.value = "new";
    input.dispatchEvent(new Event("input", { bubbles: true }));
    await tick();
    input.dispatchEvent(new KeyboardEvent("keydown", { key: "Enter", bubbles: true }));
    expect(cap.rows).toEqual([]);
    input.dispatchEvent(
      new KeyboardEvent("keydown", { key: "Enter", metaKey: true, bubbles: true })
    );
    cap.stop();
    expect(cap.rows.map((r) => r["data-action-value"])).toContain("new");
  });

  test("the edit element carries the data-polly-ui/-action-input hooks", () => {
    const el = rendered(mount(h(ActionInput, { value: "", action: "t", saveOn: "input" })));
    expect(el.getAttribute("data-polly-ui")).toBe("true");
    expect(el.getAttribute("data-polly-action-input")).not.toBeNull();
  });

  test("blur in a non-blur mode neither commits a changed value nor stays in edit", async () => {
    const cap = captureAll("t");
    const host = mount(h(ActionInput, { value: "old", action: "t", saveOn: "enter" }));
    rendered(host).dispatchEvent(new MouseEvent("click", { bubbles: true }));
    await tick();
    const input = rendered(host) as HTMLInputElement;
    input.value = "new";
    input.dispatchEvent(new Event("input", { bubbles: true }));
    await tick();
    input.dispatchEvent(new FocusEvent("blur", { bubbles: true }));
    cap.stop();
    expect(cap.rows).toEqual([]); // cancel, not commit
    await tick();
    expect(rendered(host).getAttribute("role")).toBe("button"); // back to view
  });
});

describe("boolean data hooks render as 'true' (removed when mutated false)", () => {
  test("Cluster sets data-polly-ui=true", () => {
    expect(rendered(mount(h(Cluster, { children: "x" }))).getAttribute("data-polly-ui")).toBe(
      "true"
    );
  });
  test("Html sets data-polly-ui=true and data-polly-html=true", () => {
    const el = rendered(mount(h(Html, { html: "<i>x</i>" })));
    expect(el.getAttribute("data-polly-ui")).toBe("true");
    expect(el.getAttribute("data-polly-html")).toBe("true");
  });
});

describe("Collapsible — summary/content structure", () => {
  test("summary and content carry their class tokens", () => {
    const el = rendered(mount(h(Collapsible, { summary: "H", children: "B" })));
    const summary = el.querySelector("summary");
    const content = el.querySelector("div");
    expect(cls(summary)).toContain("summary");
    expect(summary?.textContent).toBe("H");
    expect(cls(content)).toContain("content");
    expect(content?.textContent).toBe("B");
  });
  test("data-polly-ui hook is present", () => {
    expect(
      rendered(mount(h(Collapsible, { summary: "s", children: "b" }))).getAttribute("data-polly-ui")
    ).toBe("true");
  });
});
