/**
 * Render tests for the issue-123 UI primitives.
 *
 * These exercise the components against a real (happy-dom) DOM rather
 * than only typechecking them — markup, polymorphic `as`, the
 * data-polly-* hooks, the CSS-custom-property style bridge, and the
 * action-dispatch path that <ActionInput>/<ActionSelect> commit
 * through. Assertions target attributes and structure, not the hashed
 * CSS-module class names, so they stay stable across builds.
 */

import { afterAll, beforeAll, beforeEach, describe, expect, test } from "bun:test";
import { GlobalRegistrator } from "@happy-dom/global-registrator";
import type { VNode } from "preact";

beforeAll(() => {
  GlobalRegistrator.register();
});

afterAll(async () => {
  await GlobalRegistrator.unregister();
});

// Imported after the DOM globals exist so preact renders into happy-dom.
const { h, render } = await import("preact");
const { Text } = await import("../../src/polly-ui/Text.tsx");
const { Cluster } = await import("../../src/polly-ui/Cluster.tsx");
const { Code } = await import("../../src/polly-ui/Code.tsx");
const { Surface } = await import("../../src/polly-ui/Surface.tsx");
const { Button } = await import("../../src/polly-ui/Button.tsx");
const { ActionInput } = await import("../../src/polly-ui/ActionInput.tsx");
const { ActionSelect } = await import("../../src/polly-ui/ActionSelect.tsx");
const { Select } = await import("../../src/polly-ui/Select.tsx");
const { signal } = await import("@preact/signals");
const { dispatchAction } = await import("../../src/polly-ui/internal/dispatch-action.ts");

function mount<P>(vnode: VNode<P>): HTMLElement {
  const host = document.createElement("div");
  document.body.appendChild(host);
  render(vnode, host);
  return host;
}

/** The single rendered element, narrowed without a type assertion. */
function rendered(host: HTMLElement): HTMLElement {
  const el = host.firstElementChild;
  if (!(el instanceof HTMLElement)) throw new Error("expected a rendered element");
  return el;
}

function asInput(el: Element): HTMLInputElement {
  if (!(el instanceof HTMLInputElement)) throw new Error("expected an <input>");
  return el;
}

beforeEach(() => {
  document.body.innerHTML = "";
});

describe("Text", () => {
  test("a no-prop Text is a plain <span> at default tone", () => {
    const el = rendered(mount(h(Text, { children: "hello" })));
    expect(el.tagName).toBe("SPAN");
    expect(el.getAttribute("data-polly-text")).toBe("default");
    expect(el.textContent).toBe("hello");
  });

  test("tone='muted' marks the element via the data hook", () => {
    const el = rendered(mount(h(Text, { tone: "muted", children: "subtitle" })));
    expect(el.getAttribute("data-polly-text")).toBe("muted");
  });

  test("polymorphic `as` renders the requested element", () => {
    const el = rendered(mount(h(Text, { as: "p", children: "para" })));
    expect(el.tagName).toBe("P");
  });

  test("as='label' forwards htmlFor to the native `for` attribute", () => {
    const el = rendered(mount(h(Text, { as: "label", htmlFor: "field-1", children: "Name" })));
    expect(el.tagName).toBe("LABEL");
    expect(el.getAttribute("for")).toBe("field-1");
  });

  // polly#126: status tones, italic, leading.
  test("status tones mark the element via the data hook", () => {
    for (const tone of ["danger", "warning", "success"] as const) {
      const el = rendered(mount(h(Text, { tone, children: "status" })));
      expect(el.getAttribute("data-polly-text")).toBe(tone);
    }
  });

  test("italic and leading apply without an inline style", () => {
    const el = rendered(mount(h(Text, { italic: true, leading: "loose", children: "body" })));
    // The classes are hashed; assert no inline style leaked in instead.
    expect(el.getAttribute("style")).toBeNull();
    expect(el.textContent).toBe("body");
  });

  // polly#125: data-* / aria-* passthrough.
  test("forwards data-* and aria-* attributes onto the element", () => {
    const el = rendered(
      mount(h(Text, { as: "p", "data-tasks-empty": "true", "aria-label": "empty", children: "" }))
    );
    expect(el.tagName).toBe("P");
    expect(el.getAttribute("data-tasks-empty")).toBe("true");
    expect(el.getAttribute("aria-label")).toBe("empty");
  });

  test("passthrough cannot override the primitive's own data-polly-* attrs", () => {
    const el = rendered(
      mount(h(Text, { tone: "muted", "data-polly-text": "hacked", children: "x" }))
    );
    expect(el.getAttribute("data-polly-text")).toBe("muted");
  });
});

describe("Cluster", () => {
  test("renders a flex-wrap container with the data hook", () => {
    const el = rendered(mount(h(Cluster, { children: "x" })));
    expect(el.tagName).toBe("DIV");
    expect(el.getAttribute("data-polly-cluster")).toBe("true");
  });

  test("gap/justify/align/padding bridge to CSS custom properties", () => {
    const el = rendered(
      mount(
        h(Cluster, {
          gap: "8px",
          justify: "center",
          align: "start",
          padding: "4px",
          children: "x",
        })
      )
    );
    expect(el.style.getPropertyValue("--c-gap")).toBe("8px");
    expect(el.style.getPropertyValue("--c-jc")).toBe("center");
    expect(el.style.getPropertyValue("--c-ai")).toBe("start");
    expect(el.style.getPropertyValue("--c-p")).toBe("4px");
  });

  test("forwards data-* passthrough attributes (polly#125)", () => {
    const el = rendered(mount(h(Cluster, { "data-chip-row": "true", children: "x" })));
    expect(el.getAttribute("data-chip-row")).toBe("true");
    expect(el.getAttribute("data-polly-cluster")).toBe("true");
  });
});

describe("Code", () => {
  test("inline variant renders a <code>", () => {
    const el = rendered(mount(h(Code, { children: "npm i" })));
    expect(el.tagName).toBe("CODE");
    expect(el.getAttribute("data-polly-code")).toBe("inline");
  });

  test("block variant renders <pre><code>", () => {
    const pre = rendered(mount(h(Code, { block: true, children: "line1\nline2" })));
    expect(pre.tagName).toBe("PRE");
    expect(pre.getAttribute("data-polly-code")).toBe("block");
    expect(pre.firstElementChild?.tagName).toBe("CODE");
  });

  test("forwards data-* passthrough on both inline and block (polly#125)", () => {
    const inline = rendered(mount(h(Code, { "data-token": "abc", children: "x" })));
    expect(inline.getAttribute("data-token")).toBe("abc");
    const block = rendered(mount(h(Code, { block: true, "data-token": "abc", children: "x" })));
    expect(block.getAttribute("data-token")).toBe("abc");
    expect(block.getAttribute("data-polly-code")).toBe("block");
  });
});

describe("Surface (polly#126)", () => {
  test("position='absolute' bridges to the --s-position custom property", () => {
    const el = rendered(mount(h(Surface, { position: "absolute", children: "x" })));
    expect(el.style.getPropertyValue("--s-position")).toBe("absolute");
  });

  test("maxHeight, overflow, borderStyle and transform bridge to custom properties", () => {
    const el = rendered(
      mount(
        h(Surface, {
          maxHeight: "70vh",
          overflow: "auto",
          borderStyle: "dashed",
          transform: "translateX(-50%)",
          children: "x",
        })
      )
    );
    expect(el.style.getPropertyValue("--s-maxh")).toBe("70vh");
    expect(el.style.getPropertyValue("--s-overflow")).toBe("auto");
    expect(el.style.getPropertyValue("--s-border-style")).toBe("dashed");
    expect(el.style.getPropertyValue("--s-transform")).toBe("translateX(-50%)");
  });
});

describe("Button (polly#126)", () => {
  test("forwards `download` when rendering as a link", () => {
    const el = rendered(
      mount(h(Button, { href: "/extension.zip", download: "extension.zip", label: "Download" }))
    );
    expect(el.tagName).toBe("A");
    expect(el.getAttribute("download")).toBe("extension.zip");
  });

  test("a plain <button> Button has no download attribute", () => {
    const el = rendered(mount(h(Button, { label: "Click" })));
    expect(el.tagName).toBe("BUTTON");
    expect(el.getAttribute("download")).toBeNull();
  });
});

describe("dispatchAction", () => {
  test("clicks a detached button carrying the action and dash-cased data", () => {
    const seen: { action?: string; value?: string; taskId?: string } = {};
    const onClick = (e: Event): void => {
      const el = e.target;
      if (el instanceof Element && el.getAttribute("data-action")) {
        seen.action = el.getAttribute("data-action") ?? undefined;
        seen.value = el.getAttribute("data-action-value") ?? undefined;
        seen.taskId = el.getAttribute("data-action-task-id") ?? undefined;
      }
    };
    document.addEventListener("click", onClick);
    dispatchAction("task:set-status", { value: "done", taskId: "t-1" });
    document.removeEventListener("click", onClick);

    expect(seen.action).toBe("task:set-status");
    expect(seen.value).toBe("done");
    expect(seen.taskId).toBe("t-1");
  });

  test("removes the detached button after dispatch", () => {
    dispatchAction("noop:test", { value: "v" });
    expect(document.querySelector("[data-action='noop:test']")).toBeNull();
  });
});

describe("ActionInput", () => {
  test("default saveOn renders view mode (role=button)", () => {
    const el = rendered(mount(h(ActionInput, { value: "Title", action: "todo:rename" })));
    expect(el.getAttribute("data-polly-action-input")).not.toBeNull();
    expect(el.getAttribute("role")).toBe("button");
  });

  test("saveOn='input' starts in edit mode as a live <input>", () => {
    const el = rendered(
      mount(h(ActionInput, { value: "", action: "tasks:filter", saveOn: "input" }))
    );
    expect(el.tagName).toBe("INPUT");
    expect(el.getAttribute("data-state")).toBe("editing");
  });

  test("inputType='date' produces a native date input", () => {
    const el = asInput(
      rendered(
        mount(
          h(ActionInput, {
            value: "2026-05-21",
            action: "task:due",
            saveOn: "input",
            inputType: "date",
          })
        )
      )
    );
    expect(el.type).toBe("date");
  });

  test("saveOn='input' commits each keystroke through the action system", () => {
    const seen: string[] = [];
    const onClick = (e: Event): void => {
      const el = e.target;
      if (el instanceof Element && el.getAttribute("data-action") === "tasks:filter") {
        seen.push(el.getAttribute("data-action-value") ?? "");
      }
    };
    document.addEventListener("click", onClick);
    const input = asInput(
      rendered(mount(h(ActionInput, { value: "", action: "tasks:filter", saveOn: "input" })))
    );
    input.value = "ab";
    input.dispatchEvent(new Event("input", { bubbles: true }));
    document.removeEventListener("click", onClick);

    expect(seen).toContain("ab");
  });

  test("forwards data-* passthrough in both view and edit modes (polly#125)", () => {
    const view = rendered(
      mount(h(ActionInput, { value: "v", action: "a", "data-field": "title" }))
    );
    expect(view.getAttribute("data-field")).toBe("title");
    const edit = rendered(
      mount(h(ActionInput, { value: "", action: "a", saveOn: "input", "data-field": "q" }))
    );
    expect(edit.tagName).toBe("INPUT");
    expect(edit.getAttribute("data-field")).toBe("q");
  });
});

describe("ActionSelect", () => {
  test("renders the label of the option matching `value`", () => {
    const el = rendered(
      mount(
        h(ActionSelect, {
          value: "open",
          action: "task:set-status",
          disabled: true,
          options: [
            { value: "open", label: "Open" },
            { value: "done", label: "Done" },
          ],
        })
      )
    );
    expect(el.getAttribute("data-polly-action-select")).not.toBeNull();
    expect(el.getAttribute("data-state")).toBe("filled");
    expect(el.textContent).toContain("Open");
  });

  test("shows the placeholder when `value` matches no option", () => {
    const el = rendered(
      mount(
        h(ActionSelect, {
          value: "",
          action: "task:set-status",
          placeholder: "Pick one",
          disabled: true,
          options: [{ value: "open", label: "Open" }],
        })
      )
    );
    expect(el.getAttribute("data-state")).toBe("empty");
    expect(el.textContent).toContain("Pick one");
  });

  test("forwards data-* passthrough onto the outermost element (polly#125)", () => {
    const el = rendered(
      mount(
        h(ActionSelect, {
          value: "open",
          action: "task:set-status",
          disabled: true,
          "data-status-select": "true",
          options: [{ value: "open", label: "Open" }],
        })
      )
    );
    expect(el.getAttribute("data-status-select")).toBe("true");
    expect(el.getAttribute("data-polly-action-select")).not.toBeNull();
  });

  test("trigger is a single <button> carrying a caret affordance (polly#131)", () => {
    const el = rendered(
      mount(
        h(ActionSelect, {
          value: "open",
          action: "task:set-status",
          options: [
            { value: "open", label: "Open" },
            { value: "done", label: "Done" },
          ],
        })
      )
    );
    const button = el.querySelector("[data-polly-dropdown] > button");
    // The interactive element is the styled box itself — not a styled
    // <span> nested inside an unstyled <button>.
    expect(button).not.toBeNull();
    expect(button?.textContent).toContain("Open");
    // A caret marks it as a dropdown; it is hidden from the a11y tree.
    const caret = button?.querySelector('[aria-hidden="true"]');
    expect(caret).not.toBeNull();
    // Nothing interactive is nested inside the trigger button.
    expect(button?.querySelector("button, select, input")).toBeNull();
  });

  test("disabled trigger renders as static text with no caret (polly#131)", () => {
    const el = rendered(
      mount(
        h(ActionSelect, {
          value: "open",
          action: "task:set-status",
          disabled: true,
          options: [{ value: "open", label: "Open" }],
        })
      )
    );
    // No Dropdown, no interactive trigger, no caret affordance.
    expect(el.querySelector("[data-polly-dropdown]")).toBeNull();
    expect(el.querySelector("button")).toBeNull();
    expect(el.querySelector('[aria-hidden="true"]')).toBeNull();
    expect(el.textContent).toContain("Open");
  });
});

describe("Select", () => {
  test("trigger is the <button> itself, with a caret, no nested button (polly#131)", () => {
    const el = rendered(
      mount(
        h(Select, {
          selected: signal(new Set(["a"])),
          options: [
            { value: "a", label: "Alpha" },
            { value: "b", label: "Beta" },
          ],
        })
      )
    );
    const button = el.querySelector("[data-polly-dropdown] > button");
    expect(button).not.toBeNull();
    expect(button?.textContent).toContain("Alpha");
    expect(button?.querySelector('[aria-hidden="true"]')).not.toBeNull();
    // The old shape nested a styled <button> inside Dropdown's button.
    expect(button?.querySelector("button")).toBeNull();
  });

  test("disabled propagates to the trigger button (polly#131)", () => {
    const el = rendered(
      mount(
        h(Select, {
          selected: signal(new Set<string>()),
          disabled: true,
          options: [{ value: "a", label: "Alpha" }],
        })
      )
    );
    const button = el.querySelector("[data-polly-dropdown] > button");
    expect(button).not.toBeNull();
    expect((button as HTMLButtonElement).disabled).toBe(true);
  });
});
