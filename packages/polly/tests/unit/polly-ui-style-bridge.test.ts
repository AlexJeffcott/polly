/**
 * Style-bridge mutation coverage for the layout/surface primitives.
 *
 * Surface, Layout, and Cluster map their props onto `--s-*` / `--l-*` /
 * `--c-*` CSS custom properties and onto CSS-module class tokens. These
 * tests assert the exact custom-property value and class token each prop
 * produces, so a mutation that drops a bridge, swaps a token string, or
 * flips a branch is observable. The CSS-module key shim (imported first)
 * makes `classes[key] === key`, so class-selection logic is assertable.
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

const { h, render } = await import("preact");
const { Surface } = await import("../../src/polly-ui/Surface.tsx");
const { Layout } = await import("../../src/polly-ui/Layout.tsx");
const { Cluster } = await import("../../src/polly-ui/Cluster.tsx");

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

const sv = (el: HTMLElement, name: string): string => el.style.getPropertyValue(name);
const classList = (el: HTMLElement): string[] =>
  (el.getAttribute("class") ?? "").split(" ").filter(Boolean);

beforeEach(() => {
  document.body.innerHTML = "";
});

describe("Surface — value helpers", () => {
  test("background names map to surface tokens, raw colours pass through", () => {
    expect(sv(rendered(mount(h(Surface, { background: "raised", children: "x" }))), "--s-bg")).toBe(
      "var(--polly-surface-raised)"
    );
    expect(sv(rendered(mount(h(Surface, { background: "sunken", children: "x" }))), "--s-bg")).toBe(
      "var(--polly-surface-sunken)"
    );
    expect(
      sv(rendered(mount(h(Surface, { background: "transparent", children: "x" }))), "--s-bg")
    ).toBe("transparent");
    expect(
      sv(rendered(mount(h(Surface, { background: "#abcdef", children: "x" }))), "--s-bg")
    ).toBe("#abcdef");
  });

  test("radius 'none' is 0, named radii map to radius tokens", () => {
    expect(sv(rendered(mount(h(Surface, { radius: "none", children: "x" }))), "--s-radius")).toBe(
      "0"
    );
    for (const r of ["sm", "md", "lg", "full"] as const) {
      expect(sv(rendered(mount(h(Surface, { radius: r, children: "x" }))), "--s-radius")).toBe(
        `var(--polly-radius-${r})`
      );
    }
  });

  test("border names map to border-colour tokens", () => {
    expect(
      sv(rendered(mount(h(Surface, { border: "none", children: "x" }))), "--s-border-color")
    ).toBe("transparent");
    expect(
      sv(rendered(mount(h(Surface, { border: "strong", children: "x" }))), "--s-border-color")
    ).toBe("var(--polly-border-strong)");
    expect(
      sv(rendered(mount(h(Surface, { border: "default", children: "x" }))), "--s-border-color")
    ).toBe("var(--polly-border)");
  });

  test("borderWidth 'none' is 0, named widths map to width tokens", () => {
    expect(
      sv(
        rendered(mount(h(Surface, { border: "default", borderWidth: "none", children: "x" }))),
        "--s-border-width"
      )
    ).toBe("0");
    for (const w of ["default", "medium", "thick"] as const) {
      expect(
        sv(rendered(mount(h(Surface, { borderWidth: w, children: "x" }))), "--s-border-width")
      ).toBe(`var(--polly-border-width-${w})`);
    }
  });

  test("shadow 'none' is none, named shadows map to shadow tokens", () => {
    expect(sv(rendered(mount(h(Surface, { shadow: "none", children: "x" }))), "--s-shadow")).toBe(
      "none"
    );
    for (const s of ["sm", "md", "lg"] as const) {
      expect(sv(rendered(mount(h(Surface, { shadow: s, children: "x" }))), "--s-shadow")).toBe(
        `var(--polly-shadow-${s})`
      );
    }
  });
});

describe("Surface — custom-property bridges", () => {
  test("each length/position prop bridges to its own custom property", () => {
    const el = rendered(
      mount(
        h(Surface, {
          padding: "1rem",
          width: "10px",
          height: "20px",
          minHeight: "30px",
          maxHeight: "40px",
          maxInlineSize: "50px",
          overflow: "scroll",
          position: "sticky",
          inset: "0 0 auto 0",
          transform: "rotate(1deg)",
          zIndex: 7,
          pointerEvents: "none",
          borderStyle: "dashed",
          children: "x",
        })
      )
    );
    expect(sv(el, "--s-p")).toBe("1rem");
    expect(sv(el, "--s-w")).toBe("10px");
    expect(sv(el, "--s-h")).toBe("20px");
    expect(sv(el, "--s-mh")).toBe("30px");
    expect(sv(el, "--s-maxh")).toBe("40px");
    expect(sv(el, "--s-mis")).toBe("50px");
    expect(sv(el, "--s-overflow")).toBe("scroll");
    expect(sv(el, "--s-position")).toBe("sticky");
    expect(sv(el, "--s-inset")).toBe("0 0 auto 0");
    expect(sv(el, "--s-transform")).toBe("rotate(1deg)");
    expect(sv(el, "--s-z")).toBe("7");
    expect(sv(el, "--s-pe")).toBe("none");
    expect(sv(el, "--s-border-style")).toBe("dashed");
  });

  test("zIndex 0 still bridges (guarded on !== undefined, not truthiness)", () => {
    expect(sv(rendered(mount(h(Surface, { zIndex: 0, children: "x" }))), "--s-z")).toBe("0");
  });

  test("absent props leave their custom property unset", () => {
    const el = rendered(mount(h(Surface, { children: "x" })));
    expect(sv(el, "--s-p")).toBe("");
    expect(sv(el, "--s-bg")).toBe("");
    expect(sv(el, "--s-shadow")).toBe("");
    expect(sv(el, "--s-z")).toBe("");
  });

  test("per-instance style overrides merge onto the computed style", () => {
    const el = rendered(
      mount(
        h(Surface, {
          style: { "--polly-surface-raised": "#fef3c7" } as Record<string, string>,
          children: "x",
        })
      )
    );
    expect(sv(el, "--polly-surface-raised")).toBe("#fef3c7");
  });
});

describe("Surface — variant defaults", () => {
  test("raised resolves background, radius, shadow, border, and inferred width", () => {
    const el = rendered(mount(h(Surface, { variant: "raised", children: "x" })));
    expect(sv(el, "--s-bg")).toBe("var(--polly-surface-raised)");
    expect(sv(el, "--s-radius")).toBe("var(--polly-radius-md)");
    expect(sv(el, "--s-shadow")).toBe("var(--polly-shadow-md)");
    expect(sv(el, "--s-border-color")).toBe("var(--polly-border)");
    expect(sv(el, "--s-border-width")).toBe("var(--polly-border-width-default)");
    expect(el.getAttribute("data-polly-surface")).toBe("raised");
  });

  test("chip is inline with full radius", () => {
    const el = rendered(mount(h(Surface, { variant: "chip", children: "x" })));
    expect(sv(el, "--s-radius")).toBe("var(--polly-radius-full)");
    expect(classList(el)).toContain("inline");
  });

  test("floating fixes position and sets a z-index from the variant", () => {
    const el = rendered(mount(h(Surface, { variant: "floating", children: "x" })));
    expect(sv(el, "--s-position")).toBe("fixed");
    expect(sv(el, "--s-z")).toBe("9999");
    expect(sv(el, "--s-shadow")).toBe("var(--polly-shadow-lg)");
  });

  test("sticky-bar sets a block-end border side class and sticky position", () => {
    const el = rendered(mount(h(Surface, { variant: "sticky-bar", children: "x" })));
    expect(sv(el, "--s-position")).toBe("sticky");
    expect(sv(el, "--s-inset")).toBe("0 0 auto 0");
    expect(classList(el)).toContain("sides-block-end");
  });

  test("an explicit prop overrides the variant default", () => {
    const el = rendered(mount(h(Surface, { variant: "raised", radius: "lg", children: "x" })));
    expect(sv(el, "--s-radius")).toBe("var(--polly-radius-lg)");
  });

  test("plain variant sets no surface chrome", () => {
    const el = rendered(mount(h(Surface, { variant: "plain", children: "x" })));
    expect(sv(el, "--s-bg")).toBe("");
    expect(sv(el, "--s-radius")).toBe("");
    expect(sv(el, "--s-border-color")).toBe("");
    expect(sv(el, "--s-border-width")).toBe("");
  });
});

describe("Surface — border-width inference (wantsBorder)", () => {
  test("a named border with no width infers the default width", () => {
    expect(
      sv(rendered(mount(h(Surface, { border: "default", children: "x" }))), "--s-border-width")
    ).toBe("var(--polly-border-width-default)");
  });

  test("a raw borderColor with no border infers the default width and wins the colour", () => {
    const el = rendered(mount(h(Surface, { borderColor: "#ff8680", children: "x" })));
    expect(sv(el, "--s-border-color")).toBe("#ff8680");
    expect(sv(el, "--s-border-width")).toBe("var(--polly-border-width-default)");
  });

  test("borderColor overrides the token the border prop resolved", () => {
    const el = rendered(
      mount(h(Surface, { border: "strong", borderColor: "#123456", children: "x" }))
    );
    expect(sv(el, "--s-border-color")).toBe("#123456");
  });

  test("border='none' is not a border: no width inferred", () => {
    const el = rendered(mount(h(Surface, { border: "none", children: "x" })));
    expect(sv(el, "--s-border-color")).toBe("transparent");
    expect(sv(el, "--s-border-width")).toBe("");
  });
});

describe("Surface — border sides class mapping", () => {
  const cases: Array<[string, string | null]> = [
    ["all", null],
    ["block-start", "sides-block-start"],
    ["block-end", "sides-block-end"],
    ["inline-start", "sides-inline-start"],
    ["inline-end", "sides-inline-end"],
    ["block", "sides-block"],
    ["inline", "sides-inline"],
  ];
  for (const [sides, cls] of cases) {
    test(`borderSides='${sides}' ${cls ? `adds ${cls}` : "adds no side class"}`, () => {
      const el = rendered(mount(h(Surface, { borderSides: sides as never, children: "x" })));
      const list = classList(el);
      if (cls) expect(list).toContain(cls);
      else expect(list.some((c) => c.startsWith("sides-"))).toBe(false);
    });
  }
});

describe("Surface — element, class, theme, passthrough", () => {
  test("polymorphic `as` renders the requested element", () => {
    expect(rendered(mount(h(Surface, { as: "section", children: "x" }))).tagName).toBe("SECTION");
    expect(rendered(mount(h(Surface, { children: "x" }))).tagName).toBe("DIV");
  });

  test("base class is always present; className appends", () => {
    const el = rendered(mount(h(Surface, { className: "mine", children: "x" })));
    expect(classList(el)).toContain("surface");
    expect(classList(el)).toContain("mine");
  });

  test("scheme sets data-polly-theme; absent leaves it unset", () => {
    expect(
      rendered(mount(h(Surface, { scheme: "dark", children: "x" }))).getAttribute(
        "data-polly-theme"
      )
    ).toBe("dark");
    expect(
      rendered(mount(h(Surface, { children: "x" }))).getAttribute("data-polly-theme")
    ).toBeNull();
  });

  test("data-*/title pass through but the primitive's data-polly-surface cannot be overridden", () => {
    const el = rendered(
      mount(
        h(Surface, {
          "data-card": "true",
          title: "tip",
          "data-polly-surface": "hacked",
          children: "x",
        })
      )
    );
    expect(el.getAttribute("data-card")).toBe("true");
    expect(el.getAttribute("title")).toBe("tip");
    expect(el.getAttribute("data-polly-surface")).toBe("plain");
  });

  test("aria-label rides the explicit attribute, not the passthrough loop", () => {
    const el = rendered(mount(h(Surface, { "aria-label": "panel", children: "x" })));
    expect(el.getAttribute("aria-label")).toBe("panel");
  });
});

describe("Layout — grid bridges", () => {
  test("each grid/spacing/sizing/alignment prop bridges to its custom property", () => {
    const el = rendered(
      mount(
        h(Layout, {
          padding: "1px",
          height: "2px",
          minHeight: "3px",
          maxInlineSize: "4px",
          rows: "auto",
          columns: "1fr 1fr",
          gap: "5px",
          justifyItems: "center",
          alignItems: "end",
          justifyContent: "space-between",
          alignContent: "stretch",
          autoFlow: "column",
          autoRows: "min-content",
          autoColumns: "max-content",
          justifySelf: "start",
          alignSelf: "center",
          children: "x",
        })
      )
    );
    expect(sv(el, "--l-p")).toBe("1px");
    expect(sv(el, "--l-h")).toBe("2px");
    expect(sv(el, "--l-mh")).toBe("3px");
    expect(sv(el, "--l-mis")).toBe("4px");
    expect(sv(el, "--l-rows")).toBe("auto");
    expect(sv(el, "--l-cols")).toBe("1fr 1fr");
    expect(sv(el, "--l-gap")).toBe("5px");
    expect(sv(el, "--l-ji")).toBe("center");
    expect(sv(el, "--l-ai")).toBe("end");
    expect(sv(el, "--l-jc")).toBe("space-between");
    expect(sv(el, "--l-ac")).toBe("stretch");
    expect(sv(el, "--l-flow")).toBe("column");
    expect(sv(el, "--l-arows")).toBe("min-content");
    expect(sv(el, "--l-acols")).toBe("max-content");
    expect(sv(el, "--l-js")).toBe("start");
    expect(sv(el, "--l-as")).toBe("center");
    expect(el.getAttribute("data-polly-layout")).toBe("true");
  });

  test("contents short-circuits to display:contents and sets no grid vars", () => {
    const el = rendered(
      mount(h(Layout, { contents: true, gap: "9px", columns: "1fr", children: "x" }))
    );
    expect(el.style.getPropertyValue("display")).toBe("contents");
    expect(sv(el, "--l-gap")).toBe("");
    expect(sv(el, "--l-cols")).toBe("");
  });

  test("contents drops the base class but keeps a caller className", () => {
    expect(
      classList(rendered(mount(h(Layout, { contents: true, className: "mine", children: "x" }))))
    ).toEqual(["mine"]);
    expect(
      rendered(mount(h(Layout, { contents: true, children: "x" }))).getAttribute("class")
    ).toBeFalsy();
  });

  test("subgrid sets the subgrid vars plus its allowed subset only", () => {
    const el = rendered(
      mount(
        h(Layout, {
          subgrid: true,
          padding: "1px",
          alignItems: "center",
          gap: "2px",
          columns: "1fr 1fr",
          children: "x",
        })
      )
    );
    expect(sv(el, "--l-col")).toBe("1 / -1");
    expect(sv(el, "--l-cols")).toBe("subgrid");
    expect(sv(el, "--l-p")).toBe("1px");
    expect(sv(el, "--l-ai")).toBe("center");
    expect(sv(el, "--l-gap")).toBe("2px");
    // `columns` is ignored in subgrid mode — the subgrid keyword wins.
    expect(sv(el, "--l-rows")).toBe("");
  });

  test("inline and stackOnMobile add their class tokens", () => {
    const el = rendered(mount(h(Layout, { inline: true, stackOnMobile: true, children: "x" })));
    expect(classList(el)).toContain("layout");
    expect(classList(el)).toContain("inline");
    expect(classList(el)).toContain("stackOnMobile");
  });

  test("base+className compose when not in contents mode", () => {
    const el = rendered(mount(h(Layout, { className: "extra", children: "x" })));
    expect(classList(el)).toContain("layout");
    expect(classList(el)).toContain("extra");
  });

  test("polymorphic `as` and passthrough", () => {
    const el = rendered(
      mount(h(Layout, { as: "section", "data-region": "main", title: "grid", children: "x" }))
    );
    expect(el.tagName).toBe("SECTION");
    expect(el.getAttribute("data-region")).toBe("main");
    expect(el.getAttribute("title")).toBe("grid");
  });
});

describe("Cluster — bridges and classes", () => {
  test("gap/padding/justify/align bridge to --c-* properties", () => {
    const el = rendered(
      mount(
        h(Cluster, { gap: "8px", padding: "4px", justify: "center", align: "start", children: "x" })
      )
    );
    expect(sv(el, "--c-gap")).toBe("8px");
    expect(sv(el, "--c-p")).toBe("4px");
    expect(sv(el, "--c-jc")).toBe("center");
    expect(sv(el, "--c-ai")).toBe("start");
  });

  test("absent props leave --c-* unset", () => {
    const el = rendered(mount(h(Cluster, { children: "x" })));
    expect(sv(el, "--c-gap")).toBe("");
    expect(sv(el, "--c-jc")).toBe("");
  });

  test("inline and className add class tokens; data hook always present", () => {
    const el = rendered(mount(h(Cluster, { inline: true, className: "chips", children: "x" })));
    expect(classList(el)).toContain("cluster");
    expect(classList(el)).toContain("inline");
    expect(classList(el)).toContain("chips");
    expect(el.getAttribute("data-polly-cluster")).toBe("true");
  });

  test("polymorphic `as`, role, aria-label, and passthrough", () => {
    const el = rendered(
      mount(
        h(Cluster, {
          as: "nav",
          role: "toolbar",
          "aria-label": "filters",
          "data-chip-row": "true",
          children: "x",
        })
      )
    );
    expect(el.tagName).toBe("NAV");
    expect(el.getAttribute("role")).toBe("toolbar");
    expect(el.getAttribute("aria-label")).toBe("filters");
    expect(el.getAttribute("data-chip-row")).toBe("true");
  });
});
