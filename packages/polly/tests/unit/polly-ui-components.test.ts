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
const { ActionInput } = await import("../../src/polly-ui/ActionInput.tsx");
const { ActionSelect } = await import("../../src/polly-ui/ActionSelect.tsx");
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
});
