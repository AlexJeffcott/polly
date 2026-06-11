/**
 * Class-selection and attribute mutation coverage for the presentational
 * primitives (Button, Text, Code, Link, Output, Collapsible, FileInput,
 * Html). The CSS-module key shim (imported first) makes `classes[key]`
 * return `key`, so "which class did this branch pick" is observable —
 * the tier/color/size/tone maps and the boolean-prop class toggles all
 * become killable, alongside the native-attribute and structure logic.
 */

import "./helpers/css-module-keys.ts";
import { afterAll, beforeAll, beforeEach, describe, expect, test } from "bun:test";
import { GlobalRegistrator } from "@happy-dom/global-registrator";
import type { VNode } from "preact";

beforeAll(() => {
  GlobalRegistrator.register();
});

afterAll(async () => {
  await GlobalRegistrator.unregister();
});

const { h } = await import("preact");
const { render } = await import("preact");
const { Button } = await import("../../src/polly-ui/Button.tsx");
const { Text } = await import("../../src/polly-ui/Text.tsx");
const { Code } = await import("../../src/polly-ui/Code.tsx");
const { Link } = await import("../../src/polly-ui/Link.tsx");
const { Output } = await import("../../src/polly-ui/Output.tsx");
const { Collapsible } = await import("../../src/polly-ui/Collapsible.tsx");
const { FileInput } = await import("../../src/polly-ui/FileInput.tsx");
const { Html } = await import("../../src/polly-ui/Html.tsx");

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

const classList = (el: HTMLElement): string[] =>
  (el.getAttribute("class") ?? "").split(" ").filter(Boolean);

beforeEach(() => {
  document.body.innerHTML = "";
});

describe("Button — tier class", () => {
  test("default tier is secondary", () => {
    const el = rendered(mount(h(Button, { label: "x" })));
    expect(classList(el)).toContain("tierSecondary");
    expect(el.getAttribute("data-polly-button")).toBe("secondary");
  });
  test("primary and tertiary map to their own classes", () => {
    expect(classList(rendered(mount(h(Button, { tier: "primary", label: "x" }))))).toContain(
      "tierPrimary"
    );
    expect(classList(rendered(mount(h(Button, { tier: "tertiary", label: "x" }))))).toContain(
      "tierTertiary"
    );
  });
  test("explicit secondary stays secondary (not primary/tertiary)", () => {
    const list = classList(rendered(mount(h(Button, { tier: "secondary", label: "x" }))));
    expect(list).toContain("tierSecondary");
    expect(list).not.toContain("tierPrimary");
    expect(list).not.toContain("tierTertiary");
  });
});

describe("Button — color class", () => {
  const cases: Array<["info" | "success" | "warning" | "danger", string]> = [
    ["info", "colorInfo"],
    ["success", "colorSuccess"],
    ["warning", "colorWarning"],
    ["danger", "colorDanger"],
  ];
  for (const [color, cls] of cases) {
    test(`color='${color}' adds ${cls}`, () => {
      expect(classList(rendered(mount(h(Button, { color, label: "x" }))))).toContain(cls);
    });
  }
  test("default color adds no color class", () => {
    expect(
      classList(rendered(mount(h(Button, { label: "x" })))).some((c) => c.startsWith("color"))
    ).toBe(false);
  });
});

describe("Button — size class", () => {
  test("small and large map to their classes; normal adds none", () => {
    expect(classList(rendered(mount(h(Button, { size: "small", label: "x" }))))).toContain(
      "btnSmall"
    );
    expect(classList(rendered(mount(h(Button, { size: "large", label: "x" }))))).toContain(
      "btnLarge"
    );
    const normal = classList(rendered(mount(h(Button, { size: "normal", label: "x" }))));
    expect(normal).not.toContain("btnSmall");
    expect(normal).not.toContain("btnLarge");
  });
});

describe("Button — boolean modifier classes", () => {
  test("btn base is always present", () => {
    expect(classList(rendered(mount(h(Button, { label: "x" }))))).toContain("btn");
  });
  test("circle, fullWidth, bounded each add their class only when set", () => {
    expect(classList(rendered(mount(h(Button, { circle: true, label: "x" }))))).toContain(
      "btnCircle"
    );
    expect(classList(rendered(mount(h(Button, { fullWidth: true, label: "x" }))))).toContain(
      "btnFullWidth"
    );
    expect(classList(rendered(mount(h(Button, { bounded: true, label: "x" }))))).toContain(
      "btnBounded"
    );
    const plain = classList(rendered(mount(h(Button, { label: "x" }))));
    expect(plain).not.toContain("btnCircle");
    expect(plain).not.toContain("btnFullWidth");
    expect(plain).not.toContain("btnBounded");
  });
  test("className appends", () => {
    expect(classList(rendered(mount(h(Button, { className: "mine", label: "x" }))))).toContain(
      "mine"
    );
  });
});

describe("Button — content", () => {
  test("with an icon, label sits next to it inside a Layout", () => {
    const icon = h("svg", { "data-icon": "true" }) as unknown as VNode;
    const el = rendered(mount(h(Button, { icon, label: "Save" })));
    expect(el.querySelector("[data-polly-layout]")).not.toBeNull();
    expect(el.querySelector("[data-icon]")).not.toBeNull();
    expect(el.querySelector("span")?.textContent).toBe("Save");
  });
  test("without an icon, the label is rendered directly with no Layout", () => {
    const el = rendered(mount(h(Button, { label: "Save" })));
    expect(el.querySelector("[data-polly-layout]")).toBeNull();
    expect(el.textContent).toBe("Save");
  });
});

describe("Button — button vs link branch", () => {
  test("no href renders a <button> with default type button", () => {
    const el = rendered(mount(h(Button, { label: "x" })));
    expect(el.tagName).toBe("BUTTON");
    expect(el.getAttribute("type")).toBe("button");
  });
  test("an explicit type is honoured", () => {
    expect(rendered(mount(h(Button, { type: "submit", label: "x" }))).getAttribute("type")).toBe(
      "submit"
    );
  });
  test("disabled button carries the disabled attribute", () => {
    expect(
      asElement(rendered(mount(h(Button, { disabled: true, label: "x" }))), HTMLButtonElement)
        .disabled
    ).toBe(true);
  });
  test("href renders an <a> with href, target, rel, download forwarded", () => {
    const el = rendered(
      mount(
        h(Button, {
          href: "/f.zip",
          target: "_blank",
          rel: "noopener",
          download: "f.zip",
          label: "x",
        })
      )
    );
    expect(el.tagName).toBe("A");
    expect(el.getAttribute("href")).toBe("/f.zip");
    expect(el.getAttribute("target")).toBe("_blank");
    expect(el.getAttribute("rel")).toBe("noopener");
    expect(el.getAttribute("download")).toBe("f.zip");
  });
  test("a disabled link drops its href and marks aria-disabled", () => {
    const el = rendered(mount(h(Button, { href: "/f.zip", disabled: true, label: "x" })));
    expect(el.tagName).toBe("A");
    expect(el.getAttribute("href")).toBeNull();
    expect(el.getAttribute("aria-disabled")).toBe("true");
  });
});

describe("Button — action data attributes", () => {
  test("data-action and every data-action-* extra forward; aria-label rides through", () => {
    const el = rendered(
      mount(
        h(Button, {
          label: "x",
          "data-action": "task:done",
          "data-action-tid": "t-7",
          "data-action-item-id": "i-1",
          "aria-label": "complete",
        })
      )
    );
    expect(el.getAttribute("data-action")).toBe("task:done");
    expect(el.getAttribute("data-action-tid")).toBe("t-7");
    expect(el.getAttribute("data-action-item-id")).toBe("i-1");
    expect(el.getAttribute("aria-label")).toBe("complete");
  });
  test("non data-action-* props are not swept into action attributes", () => {
    const el = rendered(mount(h(Button, { label: "x", id: "the-id" })));
    expect(el.getAttribute("id")).toBe("the-id");
    // id must not be duplicated as a data-action-* attribute.
    expect(el.getAttribute("data-action-the-id")).toBeNull();
  });
});

describe("Text — class selection", () => {
  test("default tone adds only the base text class", () => {
    const list = classList(rendered(mount(h(Text, { children: "x" }))));
    expect(list).toContain("text");
    expect(list).not.toContain("muted");
  });
  test("non-default tones push the tone class", () => {
    for (const tone of ["muted", "danger", "warning", "success"] as const) {
      expect(classList(rendered(mount(h(Text, { tone, children: "x" }))))).toContain(tone);
    }
  });
  test("size, weight, italic, strikethrough, leading each add their class", () => {
    expect(classList(rendered(mount(h(Text, { size: "lg", children: "x" }))))).toContain("lg");
    expect(classList(rendered(mount(h(Text, { weight: "bold", children: "x" }))))).toContain(
      "bold"
    );
    expect(classList(rendered(mount(h(Text, { italic: true, children: "x" }))))).toContain(
      "italic"
    );
    expect(classList(rendered(mount(h(Text, { strikethrough: true, children: "x" }))))).toContain(
      "strikethrough"
    );
    expect(classList(rendered(mount(h(Text, { leading: "loose", children: "x" }))))).toContain(
      "loose"
    );
  });
  test("absent optional axes add no class", () => {
    const list = classList(rendered(mount(h(Text, { children: "x" }))));
    expect(list).toEqual(["text"]);
  });
  test("htmlFor maps to the native for attribute", () => {
    expect(
      rendered(mount(h(Text, { as: "label", htmlFor: "f1", children: "x" }))).getAttribute("for")
    ).toBe("f1");
  });
});

describe("Code — variant branch", () => {
  test("inline renders <code> with the inline marker and code class", () => {
    const el = rendered(mount(h(Code, { children: "x" })));
    expect(el.tagName).toBe("CODE");
    expect(el.getAttribute("data-polly-code")).toBe("inline");
    expect(classList(el)).toContain("code");
  });
  test("block renders <pre><code> with the block marker and block class", () => {
    const el = rendered(mount(h(Code, { block: true, children: "x" })));
    expect(el.tagName).toBe("PRE");
    expect(el.getAttribute("data-polly-code")).toBe("block");
    expect(classList(el)).toContain("block");
    expect(el.firstElementChild?.tagName).toBe("CODE");
  });
  test("className appends on both variants", () => {
    expect(classList(rendered(mount(h(Code, { className: "k", children: "x" }))))).toContain("k");
    expect(
      classList(rendered(mount(h(Code, { block: true, className: "k", children: "x" }))))
    ).toContain("k");
  });
});

describe("Link — external, subtle, download", () => {
  test("external opens a new tab with a safe rel", () => {
    const el = rendered(mount(h(Link, { href: "https://x.test", external: true, children: "x" })));
    expect(el.getAttribute("target")).toBe("_blank");
    expect(el.getAttribute("rel")).toBe("noopener noreferrer");
  });
  test("non-external sets neither target nor rel", () => {
    const el = rendered(mount(h(Link, { href: "/local", children: "x" })));
    expect(el.getAttribute("target")).toBeNull();
    expect(el.getAttribute("rel")).toBeNull();
  });
  test("subtle adds its class; default does not", () => {
    expect(
      classList(rendered(mount(h(Link, { href: "/x", subtle: true, children: "x" }))))
    ).toContain("subtle");
    expect(
      classList(rendered(mount(h(Link, { href: "/x", children: "x" })))).includes("subtle")
    ).toBe(false);
    expect(classList(rendered(mount(h(Link, { href: "/x", children: "x" }))))).toContain("link");
  });
  test("download forwards onto the anchor", () => {
    expect(
      rendered(mount(h(Link, { href: "/f.zip", download: "f.zip", children: "x" }))).getAttribute(
        "download"
      )
    ).toBe("f.zip");
  });
});

describe("Output — scroll, tabIndex, passthrough", () => {
  test("renders a <pre> with the data hook", () => {
    const el = rendered(mount(h(Output, { children: "out" })));
    expect(el.tagName).toBe("PRE");
    expect(el.getAttribute("data-polly-output")).not.toBeNull();
    expect(el.textContent).toBe("out");
  });
  test("scroll adds its class; default does not", () => {
    expect(classList(rendered(mount(h(Output, { scroll: true, children: "x" }))))).toContain(
      "scroll"
    );
    expect(classList(rendered(mount(h(Output, { children: "x" })))).includes("scroll")).toBe(false);
  });
  test("tabIndex and data-action pass through", () => {
    const el = rendered(
      mount(h(Output, { tabIndex: 0, "data-action": "diag:select-all", children: "x" }))
    );
    expect(el.getAttribute("tabindex")).toBe("0");
    expect(el.getAttribute("data-action")).toBe("diag:select-all");
  });
});

describe("Collapsible", () => {
  test("renders <details>/<summary>/<div> with the data hook", () => {
    const el = rendered(mount(h(Collapsible, { summary: "Head", children: "Body" })));
    expect(el.tagName).toBe("DETAILS");
    expect(el.getAttribute("data-polly-collapsible")).not.toBeNull();
    expect(el.querySelector("summary")?.textContent).toBe("Head");
    expect(classList(el)).toContain("collapsible");
  });
  test("defaultOpen toggles the open attribute", () => {
    expect(
      asElement(
        rendered(mount(h(Collapsible, { summary: "s", defaultOpen: true, children: "b" }))),
        HTMLDetailsElement
      ).open
    ).toBe(true);
    expect(
      asElement(
        rendered(mount(h(Collapsible, { summary: "s", children: "b" }))),
        HTMLDetailsElement
      ).open
    ).toBe(false);
  });
  test("className appends and id forwards", () => {
    const el = rendered(
      mount(h(Collapsible, { summary: "s", className: "mine", id: "c1", children: "b" }))
    );
    expect(classList(el)).toContain("mine");
    expect(el.getAttribute("id")).toBe("c1");
  });
  test("a node summary survives as markup", () => {
    const el = rendered(
      mount(
        h(Collapsible, { summary: h(Text, { tone: "muted", children: "Done" }), children: "b" })
      )
    );
    expect(el.querySelector("summary [data-polly-text]")).not.toBeNull();
  });
});

describe("FileInput", () => {
  test("renders a label wrapping a hidden native file input with accept", () => {
    const el = rendered(
      mount(h(FileInput, { onFiles: () => {}, accept: "image/*", label: "Scan" }))
    );
    expect(el.tagName).toBe("LABEL");
    expect(el.getAttribute("data-polly-file-input")).not.toBeNull();
    const input = asElement(el.querySelector("input"), HTMLInputElement);
    expect(input.type).toBe("file");
    expect(input.accept).toBe("image/*");
    expect(el.textContent).toContain("Scan");
  });
  test("default label is 'Choose file'", () => {
    expect(rendered(mount(h(FileInput, { onFiles: () => {} }))).textContent).toContain(
      "Choose file"
    );
  });
  test("multiple and disabled forward to the input; disabled adds its class", () => {
    const el = rendered(mount(h(FileInput, { onFiles: () => {}, multiple: true, disabled: true })));
    const input = asElement(el.querySelector("input"), HTMLInputElement);
    expect(input.multiple).toBe(true);
    expect(input.disabled).toBe(true);
    expect(classList(el)).toContain("disabled");
  });
  test("an empty selection does not fire onFiles", () => {
    let called = false;
    const el = rendered(mount(h(FileInput, { onFiles: () => (called = true) })));
    el.querySelector("input")?.dispatchEvent(new Event("change", { bubbles: true }));
    expect(called).toBe(false);
  });
});

describe("Html", () => {
  test("injects raw markup inside the data-hooked wrapper", () => {
    const el = rendered(mount(h(Html, { html: "<b>bold</b>" })));
    expect(el.getAttribute("data-polly-html")).not.toBeNull();
    expect(el.querySelector("b")?.textContent).toBe("bold");
  });
  test("polymorphic `as` and className forward", () => {
    const el = rendered(mount(h(Html, { html: "x", as: "span", className: "raw" })));
    expect(el.tagName).toBe("SPAN");
    expect(classList(el)).toContain("raw");
  });
  test("default wrapper is a div carrying data-polly-ui", () => {
    const el = rendered(mount(h(Html, { html: "x" })));
    expect(el.tagName).toBe("DIV");
    expect(el.getAttribute("data-polly-ui")).not.toBeNull();
  });
});
