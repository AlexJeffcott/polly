// Page script - runs in page's JavaScript environment

import { getMessageBus } from "@/shared/lib/message-bus";

const bus = getMessageBus("page");

// Register handlers for page JS environment access
bus.on("PAGE_EVAL", async (payload) => {
  try {
    // Execute in page context
    // biome-ignore lint/security/noGlobalEval: This is intentional for page script eval
    const result = eval(payload.code);
    return { result };
  } catch (error) {
    return {
      result: null,
      error: error instanceof Error ? error.message : "Eval error",
    };
  }
});

bus.on("PAGE_GET_VAR", async (payload) => {
  // biome-ignore lint/suspicious/noExplicitAny: accessing arbitrary window properties
  const value = (window as any)[payload.varName];
  return {
    value,
    exists: payload.varName in window,
  };
});

bus.on("PAGE_CALL_FN", async (payload) => {
  try {
    // biome-ignore lint/suspicious/noExplicitAny: accessing arbitrary window properties
    const fn = (window as any)[payload.fnName];
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
    // biome-ignore lint/suspicious/noExplicitAny: setting arbitrary window properties
    (window as any)[payload.varName] = payload.value;
    return { success: true };
  } catch (_error) {
    return { success: false };
  }
});
