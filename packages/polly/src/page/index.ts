// Page script - runs in page's JavaScript environment

import { getMessageBus } from "@/shared/lib/message-bus";

const bus = getMessageBus("page");

// Register handlers for page JS environment access
bus.on("PAGE_GET_VAR", async (payload) => {
  const value: unknown = Reflect.get(window, payload.varName);
  return {
    value,
    exists: payload.varName in window,
  };
});

bus.on("PAGE_CALL_FN", async (payload) => {
  try {
    const fn: unknown = Reflect.get(window, payload.fnName);
    if (typeof fn !== "function") {
      return { result: null, error: "Not a function" };
    }
    const result = fn(...payload.args);
    return { result };
  } catch (error) {
    return {
      result: null,
      error: error instanceof Error ? error.message : "Call error",
    };
  }
});

bus.on("PAGE_SET_VAR", async (payload) => {
  try {
    // Reflect.set reports a refused write (non-writable or setter-less
    // property) as false where strict-mode assignment would throw.
    return { success: Reflect.set(window, payload.varName, payload.value) };
  } catch (_error) {
    return { success: false };
  }
});
