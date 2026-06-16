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
import type { ComponentChildren, VNode } from "preact";

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
const { TextInput } = await import("../../src/polly-ui/TextInput.tsx");
const { Badge } = await import("../../src/polly-ui/Badge.tsx");
const { Dropdown } = await import("../../src/polly-ui/Dropdown.tsx");
const { Layout } = await import("../../src/polly-ui/Layout.tsx");
const { Collapsible } = await import("../../src/polly-ui/Collapsible.tsx");
const { Output } = await import("../../src/polly-ui/Output.tsx");
const { Link } = await import("../../src/polly-ui/Link.tsx");
const { Html } = await import("../../src/polly-ui/Html.tsx");
const { FileInput } = await import("../../src/polly-ui/FileInput.tsx");
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

function asInput(el: Element | null): HTMLInputElement {
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

  test("hover title falls back to the string label", () => {
    const el = rendered(mount(h(Button, { label: "Save changes" })));
    expect(el.getAttribute("title")).toBe("Save changes");
  });

  test("an icon-only button (no label) requires + surfaces its aria-label", () => {
    // The type makes `aria-label` mandatory when there's no text label;
    // it becomes both the accessible name and the hover title.
    const el = rendered(mount(h(Button, { icon: h("i", {}, "x"), "aria-label": "Close" })));
    expect(el.getAttribute("aria-label")).toBe("Close");
    expect(el.getAttribute("title")).toBe("Close");
    // Icon-only renders no empty label span next to the icon.
    const emptySpans = Array.from(el.querySelectorAll("span")).filter((s) => s.textContent === "");
    expect(emptySpans.length).toBe(0);
  });

  test("an explicit title wins over the label", () => {
    const el = rendered(mount(h(Button, { label: "Save", title: "Persist to disk" })));
    expect(el.getAttribute("title")).toBe("Persist to disk");
  });

  test('title="" opts out of the label fallback (empty title shows no tooltip)', () => {
    const el = rendered(mount(h(Button, { label: "Save", title: "" })));
    // An explicit empty string wins over the label fallback; an empty
    // title attribute produces no visible tooltip.
    expect(el.getAttribute("title")).toBe("");
  });
});

describe("Badge", () => {
  test("forwards a hover title to explain an abbreviated badge", () => {
    const el = rendered(mount(h(Badge, { title: "3 peers connected", children: "3" })));
    expect(el.getAttribute("title")).toBe("3 peers connected");
    expect(el.textContent).toBe("3");
  });

  test("omits the title attribute when none is given", () => {
    const el = rendered(mount(h(Badge, { children: "ok" })));
    expect(el.getAttribute("title")).toBeNull();
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
    if (!(button instanceof HTMLButtonElement)) throw new Error("expected a <button>");
    expect(button.disabled).toBe(true);
  });

  test("option rows carry role=option and aria-selected", () => {
    const el = rendered(
      mount(
        h(Select, {
          selected: signal(new Set(["b"])),
          options: [
            { value: "a", label: "Alpha" },
            { value: "b", label: "Beta" },
          ],
        })
      )
    );
    const opts = Array.from(el.querySelectorAll("[role='option']"));
    expect(opts.length).toBe(2);
    const beta = opts.find((o) => o.textContent?.includes("Beta"));
    const alpha = opts.find((o) => o.textContent?.includes("Alpha"));
    expect(beta?.getAttribute("aria-selected")).toBe("true");
    expect(alpha?.getAttribute("aria-selected")).toBe("false");
  });

  test("the trigger carries the current selection as a hover title", () => {
    const el = rendered(
      mount(
        h(Select, {
          selected: signal(new Set(["a"])),
          options: [{ value: "a", label: "Alpha" }],
        })
      )
    );
    const button = el.querySelector("[data-polly-dropdown] > button");
    expect(button?.getAttribute("title")).toBe("Alpha");
  });

  test("multi-select marks the listbox aria-multiselectable", () => {
    const single = rendered(
      mount(
        h(Select, { selected: signal(new Set<string>()), options: [{ value: "a", label: "A" }] })
      )
    );
    const multi = rendered(
      mount(
        h(Select, {
          selected: signal(new Set<string>()),
          multiSelect: true,
          options: [{ value: "a", label: "A" }],
        })
      )
    );
    expect(
      single.querySelector("[role='listbox']")?.getAttribute("aria-multiselectable")
    ).toBeNull();
    expect(multi.querySelector("[role='listbox']")?.getAttribute("aria-multiselectable")).toBe(
      "true"
    );
  });
});

describe("TextInput", () => {
  test("inputType sets the native single-line type; defaults to text", () => {
    const def = rendered(mount(h(TextInput, { name: "a" })));
    expect(asInput(def).getAttribute("type")).toBe("text");
    const email = rendered(mount(h(TextInput, { name: "b", inputType: "email" })));
    expect(asInput(email).getAttribute("type")).toBe("email");
  });

  test("min/max/step reach the single-line input", () => {
    const el = rendered(
      mount(h(TextInput, { name: "n", inputType: "number", min: 0, max: 10, step: 2 }))
    );
    const input = asInput(el);
    expect(input.getAttribute("min")).toBe("0");
    expect(input.getAttribute("max")).toBe("10");
    expect(input.getAttribute("step")).toBe("2");
  });

  test("without error the primitive stays a bare input (no wrapper)", () => {
    const el = rendered(mount(h(TextInput, { name: "q" })));
    expect(el.tagName).toBe("INPUT");
    expect(el.hasAttribute("data-polly-field")).toBe(false);
  });

  test("error renders a message, links it, and marks the field invalid", () => {
    const el = rendered(mount(h(TextInput, { name: "email", error: "Enter a valid email" })));
    expect(el.getAttribute("data-polly-field")).toBe("true");
    const input = asInput(el.querySelector("input"));
    const msg = el.querySelector("[role='alert']");
    if (!(msg instanceof HTMLElement)) throw new Error("expected an alert element");
    expect(msg.textContent).toBe("Enter a valid email");
    expect(input.getAttribute("aria-invalid")).toBe("true");
    // aria-describedby points at the message element's id.
    expect(input.getAttribute("aria-describedby")).toBe(msg.id);
  });

  test("error composes with a consumer-supplied describedBy", () => {
    const el = rendered(
      mount(h(TextInput, { name: "x", describedBy: "hint-1", error: "Required" }))
    );
    const input = asInput(el.querySelector("input"));
    const msg = el.querySelector("[role='alert']");
    if (!(msg instanceof HTMLElement)) throw new Error("expected an alert element");
    const tokens = input.getAttribute("aria-describedby")?.split(" ") ?? [];
    expect(tokens).toContain("hint-1");
    expect(tokens).toContain(msg.id);
  });

  test("variant=multi renders a textarea carrying the multi data hook", () => {
    const el = rendered(mount(h(TextInput, { name: "bio", variant: "multi", rows: 4 })));
    const textarea = el instanceof HTMLTextAreaElement ? el : el.querySelector("textarea");
    if (!(textarea instanceof HTMLTextAreaElement)) throw new Error("expected a textarea");
    expect(textarea.getAttribute("data-polly-input-variant")).toBe("multi");
    expect(textarea.getAttribute("rows")).toBe("4");
  });

  test("a signal value is controlled: onInput writes the typed value back", () => {
    const value = signal("");
    const input = asInput(rendered(mount(h(TextInput, { name: "c", value }))));
    input.value = "hello";
    input.dispatchEvent(new Event("input", { bubbles: true }));
    expect(value.value).toBe("hello");
  });
});

describe("Dropdown", () => {
  test("closed trigger carries data-open=false for open-state styling", () => {
    const el = rendered(
      mount(h(Dropdown, { isOpen: signal(false), trigger: "Pick", children: h("div", {}, "menu") }))
    );
    // The caret-rotation CSS keys off data-open on the trigger; the
    // attribute must be present (not just absent) so the closed state
    // is an explicit selector target.
    const button = el.querySelector("[data-polly-dropdown] > button");
    expect(button?.getAttribute("data-open")).toBe("false");
  });
});

// ── polly#135: gaps surfaced migrating fairfox off raw HTML ──────────

describe("Text — strikethrough (polly#135)", () => {
  test("strikethrough applies without an inline style", () => {
    const el = rendered(mount(h(Text, { strikethrough: true, children: "done" })));
    expect(el.getAttribute("style")).toBeNull();
    expect(el.textContent).toBe("done");
  });
});

describe("title passthrough (polly#135)", () => {
  test("Text forwards the native title attribute", () => {
    const el = rendered(mount(h(Text, { title: "relay online", children: "●" })));
    expect(el.getAttribute("title")).toBe("relay online");
  });

  test("Layout forwards title and data-* attributes", () => {
    const el = rendered(mount(h(Layout, { title: "grid", "data-region": "main", children: "x" })));
    expect(el.getAttribute("title")).toBe("grid");
    expect(el.getAttribute("data-region")).toBe("main");
    expect(el.getAttribute("data-polly-layout")).toBe("true");
  });

  test("Surface forwards the native title attribute", () => {
    const el = rendered(mount(h(Surface, { title: "peer status", children: "x" })));
    expect(el.getAttribute("title")).toBe("peer status");
  });
});

describe("Collapsible — node summary (polly#135)", () => {
  test("summary accepts a styled node, not only a string", () => {
    const el = rendered(
      mount(
        h(Collapsible, {
          summary: h(Text, { tone: "muted", children: "Done (3)" }),
          children: "body",
        })
      )
    );
    const summary = el.querySelector("summary");
    expect(summary?.textContent).toBe("Done (3)");
    // The styled node survives — a bare-string summary could not carry this.
    expect(summary?.querySelector("[data-polly-text]")).not.toBeNull();
  });
});

describe("Collapsible — Space/Enter guard for editable summary fields", () => {
  // Chromium toggles a <details> on the Space/Enter keyup of its <summary>,
  // even when focus is in a nested text field. The guard cancels that keyup
  // default for text-entry targets so typing in a header field can't collapse
  // the card. happy-dom doesn't reproduce the native toggle, so we assert the
  // observable contract: defaultPrevented is set for text fields and only them.
  function keyUpFrom(el: Element, key: string): boolean {
    const event = new KeyboardEvent("keyup", { key, bubbles: true, cancelable: true });
    el.dispatchEvent(event);
    return event.defaultPrevented;
  }

  function summaryWith(node: ComponentChildren): HTMLElement {
    const el = rendered(mount(h(Collapsible, { summary: node, children: "body" })));
    const summary = el.querySelector("summary");
    if (!(summary instanceof HTMLElement)) throw new Error("expected a summary");
    return summary;
  }

  test("Space in a TextInput inside the summary is prevented (no collapse)", () => {
    const summary = summaryWith(h(TextInput, { name: "demo-guard", value: "" }));
    const input = summary.querySelector("input");
    if (!(input instanceof HTMLInputElement)) throw new Error("expected an input");
    expect(keyUpFrom(input, " ")).toBe(true);
  });

  test("Enter in a textarea inside the summary is prevented", () => {
    const summary = summaryWith(h("textarea", {}));
    const textarea = summary.querySelector("textarea");
    if (!(textarea instanceof HTMLElement)) throw new Error("expected a textarea");
    expect(keyUpFrom(textarea, "Enter")).toBe(true);
  });

  test("a non-activation key in a text field is left alone", () => {
    const summary = summaryWith(h(TextInput, { name: "demo-guard-2", value: "" }));
    const input = summary.querySelector("input");
    if (!(input instanceof HTMLInputElement)) throw new Error("expected an input");
    expect(keyUpFrom(input, "a")).toBe(false);
  });

  test("Space on a button in the summary keeps its own activation", () => {
    const summary = summaryWith(h("button", { type: "button" }, "go"));
    const button = summary.querySelector("button");
    if (!(button instanceof HTMLElement)) throw new Error("expected a button");
    expect(keyUpFrom(button, " ")).toBe(false);
  });

  test("Space on a checkbox in the summary keeps its own activation", () => {
    const summary = summaryWith(h("input", { type: "checkbox" }));
    const checkbox = summary.querySelector("input");
    if (!(checkbox instanceof HTMLInputElement)) throw new Error("expected a checkbox");
    expect(keyUpFrom(checkbox, " ")).toBe(false);
  });

  test("Space on the bare summary keeps normal keyboard disclosure", () => {
    const summary = summaryWith(h(Text, { children: "Details" }));
    expect(keyUpFrom(summary, " ")).toBe(false);
  });
});

describe("Surface — dark-scheme theming (polly#135)", () => {
  test("scheme sets data-polly-theme so the token subtree retints", () => {
    const el = rendered(mount(h(Surface, { scheme: "dark", children: "x" })));
    expect(el.getAttribute("data-polly-theme")).toBe("dark");
  });

  test("no scheme leaves data-polly-theme unset", () => {
    const el = rendered(mount(h(Surface, { children: "x" })));
    expect(el.getAttribute("data-polly-theme")).toBeNull();
  });

  test("borderColor overrides the token and infers a width", () => {
    const el = rendered(mount(h(Surface, { borderColor: "#ff8680", children: "x" })));
    expect(el.style.getPropertyValue("--s-border-color")).toBe("#ff8680");
    // A raw colour with no explicit width still renders a border.
    expect(el.style.getPropertyValue("--s-border-width")).not.toBe("");
  });

  test("pointerEvents bridges to the --s-pe custom property", () => {
    const el = rendered(mount(h(Surface, { pointerEvents: "none", children: "x" })));
    expect(el.style.getPropertyValue("--s-pe")).toBe("none");
  });
});

// renderMarkdown's data-polly-markdown hook (polly#135) is not unit-tested
// here: DOMPurify only exposes `.sanitize` against a real browser window,
// which happy-dom does not provide. The change is a two-attribute addition
// to the returned wrapper; the issue's `ui-screenshots` harness verifies
// the overflow behaviour it enables.

describe("Output (polly#135)", () => {
  test("renders a read-only <pre> with the data hook", () => {
    const el = rendered(mount(h(Output, { children: "mesh snapshot" })));
    expect(el.tagName).toBe("PRE");
    expect(el.getAttribute("data-polly-output")).not.toBeNull();
    expect(el.textContent).toBe("mesh snapshot");
  });

  test("forwards data-action for a tap-to-select-all gesture", () => {
    const el = rendered(
      mount(h(Output, { "data-action": "diag:select-all", tabIndex: 0, children: "x" }))
    );
    expect(el.getAttribute("data-action")).toBe("diag:select-all");
    expect(el.getAttribute("tabindex")).toBe("0");
  });
});

describe("Link (polly#135)", () => {
  test("renders an <a> with href and the data hook", () => {
    const el = rendered(mount(h(Link, { href: "/extension.zip", children: "Download" })));
    expect(el.tagName).toBe("A");
    expect(el.getAttribute("href")).toBe("/extension.zip");
    expect(el.getAttribute("data-polly-link")).not.toBeNull();
  });

  test("external opens a new tab with a safe rel", () => {
    const el = rendered(mount(h(Link, { href: "https://x.test", external: true, children: "x" })));
    expect(el.getAttribute("target")).toBe("_blank");
    expect(el.getAttribute("rel")).toContain("noopener");
  });

  test("a non-external Link sets no target", () => {
    const el = rendered(mount(h(Link, { href: "/local", children: "x" })));
    expect(el.getAttribute("target")).toBeNull();
  });
});

describe("Html (polly#135)", () => {
  test("renders trusted raw markup inside the data-hooked wrapper", () => {
    const el = rendered(mount(h(Html, { html: "<b>bold</b>" })));
    expect(el.getAttribute("data-polly-html")).not.toBeNull();
    expect(el.querySelector("b")?.textContent).toBe("bold");
  });

  test("polymorphic `as` picks the wrapper element", () => {
    const el = rendered(mount(h(Html, { html: "x", as: "span" })));
    expect(el.tagName).toBe("SPAN");
  });
});

describe("FileInput (polly#135)", () => {
  test("renders a label wrapping a hidden native file input", () => {
    const el = rendered(
      mount(h(FileInput, { onFiles: () => {}, label: "Scan image", accept: "image/*" }))
    );
    expect(el.tagName).toBe("LABEL");
    expect(el.getAttribute("data-polly-file-input")).not.toBeNull();
    const input = asInput(el.querySelector("input"));
    expect(input.type).toBe("file");
    expect(input.accept).toBe("image/*");
    expect(el.textContent).toContain("Scan image");
  });

  test("disabled propagates to the native input", () => {
    const el = rendered(mount(h(FileInput, { onFiles: () => {}, disabled: true })));
    const input = asInput(el.querySelector("input"));
    expect(input.disabled).toBe(true);
  });

  test("an empty selection does not fire onFiles", () => {
    let called = false;
    const el = rendered(mount(h(FileInput, { onFiles: () => (called = true) })));
    const input = asInput(el.querySelector("input"));
    input.dispatchEvent(new Event("change", { bubbles: true }));
    expect(called).toBe(false);
  });
});
