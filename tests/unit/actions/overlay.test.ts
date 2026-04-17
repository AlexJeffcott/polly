import { beforeEach, expect, test } from "bun:test";
import {
  closeTopOverlay,
  hasOpenOverlay,
  overlayStack,
  popOverlay,
  pushOverlay,
  resetOverlayStack,
  topOverlay,
} from "@fairfox/polly/actions";

beforeEach(() => {
  resetOverlayStack();
});

test("push then top returns the pushed entry", () => {
  pushOverlay({ id: "modal-a" });
  expect(topOverlay()?.id).toBe("modal-a");
  expect(hasOpenOverlay()).toBe(true);
});

test("stack order reflects push order; top is last pushed", () => {
  pushOverlay({ id: "a" });
  pushOverlay({ id: "b" });
  pushOverlay({ id: "c" });
  expect(overlayStack().map((e) => e.id)).toEqual(["a", "b", "c"]);
  expect(topOverlay()?.id).toBe("c");
});

test("popOverlay without id pops top and returns it", () => {
  pushOverlay({ id: "a" });
  pushOverlay({ id: "b" });
  const popped = popOverlay();
  expect(popped?.id).toBe("b");
  expect(topOverlay()?.id).toBe("a");
});

test("popOverlay with id removes the named entry wherever it is", () => {
  pushOverlay({ id: "a" });
  pushOverlay({ id: "b" });
  pushOverlay({ id: "c" });
  const popped = popOverlay("b");
  expect(popped?.id).toBe("b");
  expect(overlayStack().map((e) => e.id)).toEqual(["a", "c"]);
});

test("popOverlay returns undefined when id not found", () => {
  pushOverlay({ id: "a" });
  expect(popOverlay("missing")).toBeUndefined();
  expect(overlayStack().map((e) => e.id)).toEqual(["a"]);
});

test("closeTopOverlay fires onClose and pops the top", () => {
  let closedId: string | undefined;
  pushOverlay({ id: "a" });
  pushOverlay({ id: "b", onClose: () => (closedId = "b") });
  closeTopOverlay();
  expect(closedId).toBe("b");
  expect(topOverlay()?.id).toBe("a");
});

test("closeTopOverlay on empty stack is a no-op", () => {
  expect(closeTopOverlay()).toBeUndefined();
  expect(hasOpenOverlay()).toBe(false);
});
