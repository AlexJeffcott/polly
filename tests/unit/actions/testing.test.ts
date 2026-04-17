import { expect, test } from "bun:test";
import {
  createMockElement,
  createMockStores,
  createMockSubmitEvent,
  parseActionData,
  runAction,
} from "@fairfox/polly/actions";
import type { ActionRegistry } from "@fairfox/polly/actions";

test("createMockElement exposes attributes compatible with parseActionData", () => {
  const el = createMockElement({
    "data-action-foo-bar": "x",
    "data-action-value": "y",
  });
  expect(parseActionData(el)).toEqual({ fooBar: "x", value: "y" });
});

test("createMockSubmitEvent has preventDefault behaviour", () => {
  const event = createMockSubmitEvent({});
  expect(event.type).toBe("submit");
  expect(event.defaultPrevented).toBe(false);
  event.preventDefault();
  expect(event.defaultPrevented).toBe(true);
});

test("createMockStores returns the partial cast as the stores type", () => {
  const stores = createMockStores<{ count: number }>({ count: 1 });
  expect(stores.count).toBe(1);
});

test("runAction invokes the registered handler with context defaults", async () => {
  let seen: Record<string, string> | undefined;
  const registry: ActionRegistry<{ x: number }> = {
    "ping": ({ data }) => {
      seen = data;
    },
  };
  await runAction(registry, "ping", { stores: { x: 1 }, data: { a: "1" } });
  expect(seen).toEqual({ a: "1" });
});

test("runAction throws when the handler is absent", async () => {
  const registry: ActionRegistry<{}> = {};
  await expect(runAction(registry, "missing", { stores: {} })).rejects.toThrow(
    /No handler registered/,
  );
});
