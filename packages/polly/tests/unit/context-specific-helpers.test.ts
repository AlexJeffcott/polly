/**
 * Tests for context-specific-helpers.ts — the six per-context helper
 * factories (content script, devtools, popup, options, side panel,
 * background).
 *
 * Every helper touches the DOM (window/document), chrome.* APIs, or
 * ExtensionAdapters, none of which exist under bun. Each describe block
 * installs the minimal fakes it needs onto globalThis and clears them
 * afterwards; adapters are a hand-built stub (only tabs/runtime are used) and
 * setTimeout is captured so the options-page notifications don't schedule
 * real timers.
 */

import { afterEach, beforeEach, describe, expect, test } from "bun:test";
import type { ExtensionAdapters } from "@/shared/adapters";
import {
  createBackgroundHelpers,
  createContentScriptHelpers,
  createDevToolsHelpers,
  createOptionsHelpers,
  createPopupHelpers,
  createSidePanelHelpers,
} from "@/shared/lib/context-specific-helpers";

type AnyGlobal = Record<string, unknown>;
function setGlobal(name: string, value: unknown): void {
  (globalThis as AnyGlobal)[name] = value;
}
function clearGlobals(...names: string[]): void {
  for (const name of names) delete (globalThis as AnyGlobal)[name];
}

/** Adapters stub — the helpers only ever reach for tabs and runtime. */
function makeAdapters() {
  const calls = {
    query: [] as unknown[],
    create: [] as unknown[],
    openOptionsPage: 0,
  };
  const adapters = {
    tabs: {
      query: async (filter: unknown) => {
        calls.query.push(filter);
        return [{ id: 1, active: true }];
      },
      create: (options: unknown) => {
        calls.create.push(options);
      },
    },
    runtime: {
      openOptionsPage: () => {
        calls.openOptionsPage += 1;
      },
    },
  } as unknown as ExtensionAdapters;
  return { adapters, calls };
}

// ---------------------------------------------------------------------------
// createContentScriptHelpers
// ---------------------------------------------------------------------------

describe("createContentScriptHelpers", () => {
  afterEach(() => clearGlobals("window", "document"));

  test("getPageInfo reads location and document fields", () => {
    setGlobal("window", {
      location: { href: "https://example.com/path?q=1", host: "example.com", pathname: "/path" },
    });
    setGlobal("document", { title: "Doc Title", readyState: "interactive" });
    expect(createContentScriptHelpers().getPageInfo()).toEqual({
      url: "https://example.com/path?q=1",
      title: "Doc Title",
      host: "example.com",
      pathname: "/path",
      readyState: "interactive",
    });
  });

  test("queryElements serializes elements and truncates textContent to 100 chars", () => {
    const long = "a".repeat(150);
    setGlobal("document", {
      querySelectorAll: () => [{ tagName: "DIV", id: "x", className: "c1 c2", textContent: long }],
    });
    const [el] = createContentScriptHelpers().queryElements(".sel");
    expect(el).toEqual({
      tagName: "DIV",
      id: "x",
      className: "c1 c2",
      textContent: "a".repeat(100),
    });
  });

  test("queryElements coerces missing textContent to an empty string", () => {
    setGlobal("document", {
      querySelectorAll: () => [{ tagName: "SPAN", id: "", className: "", textContent: null }],
    });
    const [el] = createContentScriptHelpers().queryElements("span");
    expect(el?.textContent).toBe("");
  });

  test("getPageMetadata maps name/property meta tags, skipping incomplete ones", () => {
    const tag = (attrs: Record<string, string>) => ({
      getAttribute: (n: string) => attrs[n] ?? null,
    });
    setGlobal("document", {
      querySelectorAll: (sel: string) =>
        sel === "meta"
          ? [
              tag({ name: "description", content: "a desc" }),
              tag({ property: "og:title", content: "a title" }), // falls back to property
              tag({ name: "no-content" }), // skipped: no content
              tag({ content: "orphan" }), // skipped: no name/property
            ]
          : [],
    });
    expect(createContentScriptHelpers().getPageMetadata()).toEqual({
      description: "a desc",
      "og:title": "a title",
    });
  });

  test("injectCSS appends a <style> element carrying the CSS to document.head", () => {
    const created: AnyGlobal[] = [];
    const headAppended: AnyGlobal[] = [];
    setGlobal("document", {
      createElement: (tag: string) => {
        const el = { tagName: tag.toUpperCase(), id: "", textContent: "" };
        created.push(el);
        return el;
      },
      head: { appendChild: (el: AnyGlobal) => headAppended.push(el) },
    });
    createContentScriptHelpers().injectCSS("body { color: red; }");
    expect(created).toHaveLength(1);
    const style = created[0]!;
    expect(style.tagName).toBe("STYLE");
    expect(style.textContent).toBe("body { color: red; }");
    expect(String(style.id)).toMatch(/^ext-injected-/);
    expect(headAppended).toEqual([style]);
  });

  test("removeCSS removes a found element and is a no-op when absent", () => {
    let removed = false;
    const byId: Record<string, unknown> = {
      "style-1": { remove: () => (removed = true) },
    };
    setGlobal("document", { getElementById: (id: string) => byId[id] });
    const helpers = createContentScriptHelpers();
    helpers.removeCSS("style-1");
    expect(removed).toBe(true);
    expect(() => helpers.removeCSS("missing")).not.toThrow();
  });
});

// ---------------------------------------------------------------------------
// createDevToolsHelpers
// ---------------------------------------------------------------------------

describe("createDevToolsHelpers", () => {
  afterEach(() => clearGlobals("chrome"));

  test("inspectedTabId returns the inspected window's tab id", () => {
    setGlobal("chrome", { devtools: { inspectedWindow: { tabId: 99 } } });
    expect(createDevToolsHelpers().inspectedTabId).toBe(99);
  });

  test("inspectedTabId is undefined when devtools is entirely absent", () => {
    setGlobal("chrome", {});
    expect(createDevToolsHelpers().inspectedTabId).toBeUndefined();
  });

  test("inspectedTabId is undefined when inspectedWindow is absent", () => {
    setGlobal("chrome", { devtools: {} });
    expect(createDevToolsHelpers().inspectedTabId).toBeUndefined();
  });

  test("evalInPage resolves the eval result", async () => {
    setGlobal("chrome", {
      devtools: {
        inspectedWindow: {
          eval: (_code: string, cb: (r: unknown, e?: unknown) => void) => cb("RESULT"),
        },
      },
    });
    await expect(createDevToolsHelpers().evalInPage("1+1")).resolves.toBe("RESULT");
  });

  test("evalInPage rejects with the exception value when error.isException", async () => {
    setGlobal("chrome", {
      devtools: {
        inspectedWindow: {
          eval: (_code: string, cb: (r: unknown, e?: unknown) => void) =>
            cb(undefined, { isException: true, value: "boom value" }),
        },
      },
    });
    await expect(createDevToolsHelpers().evalInPage("x")).rejects.toThrow("boom value");
  });

  test("evalInPage rejects with a generic message for non-exception errors", async () => {
    setGlobal("chrome", {
      devtools: {
        inspectedWindow: {
          eval: (_code: string, cb: (r: unknown, e?: unknown) => void) =>
            cb(undefined, { isException: false, value: "ignored" }),
        },
      },
    });
    await expect(createDevToolsHelpers().evalInPage("x")).rejects.toThrow("Execution error");
  });

  test("evalInPage rejects when inspectedWindow is unavailable", async () => {
    // chrome.devtools itself absent — the `chrome.devtools?.` guard must hold.
    setGlobal("chrome", {});
    await expect(createDevToolsHelpers().evalInPage("x")).rejects.toThrow(
      "DevTools inspectedWindow not available"
    );
  });

  test("getPageResource resolves plain content for a matched url", async () => {
    setGlobal("chrome", {
      devtools: {
        inspectedWindow: {
          getResources: (cb: (resources: unknown[]) => void) =>
            cb([
              {
                url: "https://x/app.js",
                getContent: (gc: (c: string, enc?: string) => void) => gc("console.log(1)"),
              },
            ]),
        },
      },
    });
    await expect(createDevToolsHelpers().getPageResource("https://x/app.js")).resolves.toBe(
      "console.log(1)"
    );
  });

  test("getPageResource base64-decodes content when encoding is base64", async () => {
    setGlobal("chrome", {
      devtools: {
        inspectedWindow: {
          getResources: (cb: (resources: unknown[]) => void) =>
            cb([
              {
                url: "u",
                getContent: (gc: (c: string, enc?: string) => void) =>
                  gc(btoa("hi there"), "base64"),
              },
            ]),
        },
      },
    });
    await expect(createDevToolsHelpers().getPageResource("u")).resolves.toBe("hi there");
  });

  test("getPageResource rejects when the resource is not found", async () => {
    setGlobal("chrome", {
      devtools: {
        inspectedWindow: {
          getResources: (cb: (resources: unknown[]) => void) => cb([{ url: "other" }]),
        },
      },
    });
    await expect(createDevToolsHelpers().getPageResource("missing")).rejects.toThrow(
      "Resource not found: missing"
    );
  });

  test("getPageResource rejects when inspectedWindow is unavailable", async () => {
    setGlobal("chrome", {});
    await expect(createDevToolsHelpers().getPageResource("u")).rejects.toThrow(
      "DevTools inspectedWindow not available"
    );
  });

  test("reloadInspectedPage forwards options to reload", () => {
    const reloads: unknown[] = [];
    setGlobal("chrome", {
      devtools: { inspectedWindow: { reload: (o: unknown) => reloads.push(o) } },
    });
    createDevToolsHelpers().reloadInspectedPage({ ignoreCache: true });
    expect(reloads).toEqual([{ ignoreCache: true }]);
  });

  test("reloadInspectedPage defaults options to {} when none given", () => {
    const reloads: unknown[] = [];
    setGlobal("chrome", {
      devtools: { inspectedWindow: { reload: (o: unknown) => reloads.push(o) } },
    });
    createDevToolsHelpers().reloadInspectedPage();
    expect(reloads).toEqual([{}]);
  });

  test("reloadInspectedPage warns and does not reload when unavailable", () => {
    const warnings: unknown[][] = [];
    const realWarn = console.warn;
    console.warn = (...a: unknown[]) => warnings.push(a);
    try {
      setGlobal("chrome", {});
      createDevToolsHelpers().reloadInspectedPage();
      expect(warnings.some((w) => String(w[0]).includes("inspectedWindow not available"))).toBe(
        true
      );
    } finally {
      console.warn = realWarn;
    }
  });
});

// ---------------------------------------------------------------------------
// createPopupHelpers
// ---------------------------------------------------------------------------

describe("createPopupHelpers", () => {
  afterEach(() => clearGlobals("window", "document"));

  test("getCurrentTab queries the active tab in the current window", async () => {
    const { adapters, calls } = makeAdapters();
    const tab = await createPopupHelpers(adapters).getCurrentTab();
    expect(tab as unknown).toEqual({ id: 1, active: true });
    expect(calls.query).toEqual([{ active: true, currentWindow: true }]);
  });

  test("closePopup calls window.close", () => {
    let closed = false;
    setGlobal("window", { close: () => (closed = true) });
    createPopupHelpers(makeAdapters().adapters).closePopup();
    expect(closed).toBe(true);
  });

  test("setDimensions writes pixel width and height to the body style", () => {
    const style = { width: "", height: "" };
    setGlobal("document", { body: { style } });
    createPopupHelpers(makeAdapters().adapters).setDimensions(320, 480);
    expect(style).toEqual({ width: "320px", height: "480px" });
  });
});

// ---------------------------------------------------------------------------
// createOptionsHelpers
// ---------------------------------------------------------------------------

describe("createOptionsHelpers", () => {
  let timers: Array<{ fn: () => void; ms: number }>;
  const realSetTimeout = globalThis.setTimeout;

  beforeEach(() => {
    timers = [];
    (globalThis as AnyGlobal).setTimeout = ((fn: () => void, ms: number) => {
      timers.push({ fn, ms });
      return 0;
    }) as unknown as typeof setTimeout;
  });

  afterEach(() => {
    (globalThis as AnyGlobal).setTimeout = realSetTimeout;
    clearGlobals("document");
  });

  interface FakeNotification {
    textContent: string;
    style: { cssText: string; animation: string };
    removed: boolean;
    remove: () => void;
  }

  function captureBody(): { appended: FakeNotification[]; createdTags: string[] } {
    const appended: FakeNotification[] = [];
    const createdTags: string[] = [];
    setGlobal("document", {
      createElement: (tag: string) => {
        createdTags.push(tag);
        const el: FakeNotification = {
          textContent: "",
          style: { cssText: "", animation: "" },
          removed: false,
          remove() {
            this.removed = true;
          },
        };
        return el;
      },
      body: { appendChild: (el: FakeNotification) => appended.push(el) },
    });
    return { appended, createdTags };
  }

  test("openInNewTab creates a tab at the given path", () => {
    const { adapters, calls } = makeAdapters();
    createOptionsHelpers(adapters).openInNewTab("/settings");
    expect(calls.create).toEqual([{ url: "/settings" }]);
  });

  test("showSaveConfirmation appends a styled <div> with the default message and duration", () => {
    const { appended, createdTags } = captureBody();
    createOptionsHelpers(makeAdapters().adapters).showSaveConfirmation();
    expect(createdTags).toEqual(["div"]);
    expect(appended).toHaveLength(1);
    expect(appended[0]!.textContent).toBe("Settings saved!");
    expect(appended[0]!.style.cssText).toContain("position: fixed");
    expect(timers[0]!.ms).toBe(3000);
  });

  test("showSaveConfirmation honors a custom message and duration", () => {
    const { appended } = captureBody();
    createOptionsHelpers(makeAdapters().adapters).showSaveConfirmation("Done", 1000);
    expect(appended[0]!.textContent).toBe("Done");
    expect(timers[0]!.ms).toBe(1000);
  });

  test("the notification dismissal animates out and then removes itself", () => {
    const { appended } = captureBody();
    createOptionsHelpers(makeAdapters().adapters).showSaveConfirmation();
    const notification = appended[0]!;
    // Fire the outer (duration) timer: it sets the slide-out animation and
    // schedules the removal at 300ms.
    timers[0]!.fn();
    expect(notification.style.animation).toBe("slideOut 0.3s ease");
    expect(timers[1]!.ms).toBe(300);
    expect(notification.removed).toBe(false);
    // Fire the inner (300ms) timer: the notification is removed.
    timers[1]!.fn();
    expect(notification.removed).toBe(true);
  });

  test("showError appends a <div> with the default 5s duration", () => {
    const { appended, createdTags } = captureBody();
    createOptionsHelpers(makeAdapters().adapters).showError("Oops");
    expect(createdTags).toEqual(["div"]);
    expect(appended[0]!.textContent).toBe("Oops");
    expect(appended[0]!.style.cssText).toContain("position: fixed");
    expect(timers[0]!.ms).toBe(5000);
  });

  test("showError honors a custom duration and animates out before removal", () => {
    const { appended } = captureBody();
    createOptionsHelpers(makeAdapters().adapters).showError("Oops", 2000);
    expect(timers[0]!.ms).toBe(2000);
    const notification = appended[0]!;
    timers[0]!.fn();
    expect(notification.style.animation).toBe("slideOut 0.3s ease");
    expect(timers[1]!.ms).toBe(300);
    timers[1]!.fn();
    expect(notification.removed).toBe(true);
  });
});

// ---------------------------------------------------------------------------
// createSidePanelHelpers
// ---------------------------------------------------------------------------

describe("createSidePanelHelpers", () => {
  afterEach(() => clearGlobals("document"));

  test("getCurrentTab queries the active tab in the current window", async () => {
    const { adapters, calls } = makeAdapters();
    const tab = await createSidePanelHelpers(adapters).getCurrentTab();
    expect(tab as unknown).toEqual({ id: 1, active: true });
    expect(calls.query).toEqual([{ active: true, currentWindow: true }]);
  });

  test("isVisible is true only when the document is visible", () => {
    setGlobal("document", { visibilityState: "visible" });
    expect(createSidePanelHelpers(makeAdapters().adapters).isVisible()).toBe(true);
    setGlobal("document", { visibilityState: "hidden" });
    expect(createSidePanelHelpers(makeAdapters().adapters).isVisible()).toBe(false);
  });

  test("setWidth writes a pixel width to the body style", () => {
    const style = { width: "" };
    setGlobal("document", { body: { style } });
    createSidePanelHelpers(makeAdapters().adapters).setWidth(280);
    expect(style.width).toBe("280px");
  });
});

// ---------------------------------------------------------------------------
// createBackgroundHelpers
// ---------------------------------------------------------------------------

describe("createBackgroundHelpers", () => {
  afterEach(() => clearGlobals("chrome"));

  test("getAllTabs queries with an empty filter", async () => {
    const { adapters, calls } = makeAdapters();
    const tabs = await createBackgroundHelpers(adapters).getAllTabs();
    expect(tabs as unknown).toEqual([{ id: 1, active: true }]);
    expect(calls.query).toEqual([{}]);
  });

  test("openOptionsPage delegates to the runtime adapter", () => {
    const { adapters, calls } = makeAdapters();
    createBackgroundHelpers(adapters).openOptionsPage();
    expect(calls.openOptionsPage).toBe(1);
  });

  test("getExtensionViews passes {type} only for popup and tab", () => {
    const getViewsArgs: unknown[] = [];
    setGlobal("chrome", {
      extension: {
        getViews: (arg: unknown) => {
          getViewsArgs.push(arg);
          return [];
        },
      },
    });
    const helpers = createBackgroundHelpers(makeAdapters().adapters);
    helpers.getExtensionViews("popup");
    helpers.getExtensionViews("tab");
    helpers.getExtensionViews("notification");
    helpers.getExtensionViews();
    expect(getViewsArgs).toEqual([{ type: "popup" }, { type: "tab" }, undefined, undefined]);
  });

  test("setBadge sets text and the default background color", () => {
    const texts: unknown[] = [];
    const colors: unknown[] = [];
    setGlobal("chrome", {
      action: {
        setBadgeText: (o: unknown) => texts.push(o),
        setBadgeBackgroundColor: (o: unknown) => colors.push(o),
      },
    });
    createBackgroundHelpers(makeAdapters().adapters).setBadge("5");
    expect(texts).toEqual([{ text: "5" }]);
    expect(colors).toEqual([{ color: "#f44336" }]);
  });

  test("setBadge honors a custom color", () => {
    const colors: unknown[] = [];
    setGlobal("chrome", {
      action: { setBadgeText: () => {}, setBadgeBackgroundColor: (o: unknown) => colors.push(o) },
    });
    createBackgroundHelpers(makeAdapters().adapters).setBadge("5", "#000000");
    expect(colors).toEqual([{ color: "#000000" }]);
  });

  test("clearBadge sets the badge text to an empty string", () => {
    const texts: unknown[] = [];
    setGlobal("chrome", {
      action: { setBadgeText: (o: unknown) => texts.push(o) },
    });
    createBackgroundHelpers(makeAdapters().adapters).clearBadge();
    expect(texts).toEqual([{ text: "" }]);
  });
});
