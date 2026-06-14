/**
 * Coverage for the action testing helpers polly ships to consumers
 * (`@fairfox/polly` → src/actions/testing.ts). They had no unit test of their
 * own, so the surface other projects build their handler tests on was itself
 * unverified. Each helper is exercised here through its public shape.
 */

import { describe, expect, test } from "bun:test";
import type { ActionRegistry } from "@/actions/registry";
import {
  createMockElement,
  createMockStores,
  createMockSubmitEvent,
  runAction,
} from "@/actions/testing";

describe("createMockElement", () => {
  test("reads, writes, checks and removes attributes", () => {
    const el = createMockElement({ "data-id": "7" }, "BUTTON");
    expect(el.tagName).toBe("BUTTON");
    expect(el.getAttribute("data-id")).toBe("7");
    expect(el.getAttribute("missing")).toBeNull();
    expect(el.hasAttribute("data-id")).toBe(true);

    el.setAttribute("data-id", "9");
    expect(el.getAttribute("data-id")).toBe("9");

    el.removeAttribute("data-id");
    expect(el.hasAttribute("data-id")).toBe(false);
  });

  test("defaults to a DIV with no attributes", () => {
    expect(createMockElement().tagName).toBe("DIV");
  });
});

describe("createMockSubmitEvent", () => {
  test("wraps a plain field record as a form target and tracks preventDefault", () => {
    const event = createMockSubmitEvent({ name: "ada", role: "admin" });
    expect(event.type).toBe("submit");
    expect(event.defaultPrevented).toBe(false);
    event.preventDefault();
    expect(event.defaultPrevented).toBe(true);
  });
});

describe("createMockStores", () => {
  test("returns the supplied partial as the store object", () => {
    const stores = createMockStores<{ count: number }>({ count: 3 });
    expect(stores.count).toBe(3);
  });
});

describe("runAction", () => {
  test("invokes the registered handler with a filled-in context", async () => {
    let seenData: unknown;
    let seenTag: string | undefined;
    const registry: ActionRegistry<{ n: number }> = {
      bump: (ctx) => {
        seenData = ctx.data;
        seenTag = ctx.element.tagName;
      },
    };

    await runAction(registry, "bump", { stores: { n: 1 }, data: { id: "x" } });

    expect(seenData).toEqual({ id: "x" });
    expect(seenTag).toBe("DIV");
  });

  test("throws for an unregistered action", async () => {
    const registry: ActionRegistry<object> = {};
    await expect(runAction(registry, "nope", { stores: {} })).rejects.toThrow(
      'No handler registered for action "nope"'
    );
  });
});
