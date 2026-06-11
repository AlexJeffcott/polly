/**
 * Tests for context-helpers.ts — createContext (the extension-context
 * bootstrapper) and the deprecated runInContext gate.
 *
 * createContext builds a MessageBus via getMessageBus, wires an optional
 * error handler onto the bus, and then runs an async initialize() either
 * immediately or deferred to DOMContentLoaded depending on window / context /
 * waitForDOM / document.readyState. bun has no window or document, so the DOM
 * branch is driven against a faked window+document; the behaviour that
 * distinguishes the deferred path from the immediate path is *when* onInit
 * runs while the document is still "loading".
 *
 * All buses are built with mock ExtensionAdapters so no chrome API is touched.
 */

import { afterEach, beforeEach, describe, expect, test } from "bun:test";
import { createMockAdapters } from "@fairfox/polly/test";
import { createContext, runInContext } from "@/shared/lib/context-helpers";
import { MessageBus } from "@/shared/lib/message-bus";
import type { Context } from "@/shared/types/messages";

/** Let fire-and-forget async init settle before asserting. */
const flush = () => new Promise<void>((resolve) => setTimeout(resolve, 0));

// ---------------------------------------------------------------------------
// console.error capture + window/document faking
// ---------------------------------------------------------------------------

let errors: unknown[][];
const realError = console.error;

function installDom(readyState: "loading" | "complete"): { fire: (type: string) => void } {
  const listeners: Record<string, Array<() => void>> = {};
  // Partial window/document fakes installed via Reflect — the real globals
  // don't exist under bun, and the helpers only touch these members.
  Reflect.set(globalThis, "window", {
    addEventListener: () => {},
    removeEventListener: () => {},
  });
  Reflect.set(globalThis, "document", {
    readyState,
    addEventListener: (type: string, cb: () => void) => {
      (listeners[type] ??= []).push(cb);
    },
  });
  return {
    fire: (type: string) => {
      for (const cb of listeners[type] ?? []) cb();
    },
  };
}

function uninstallDom(): void {
  Reflect.deleteProperty(globalThis, "window");
  Reflect.deleteProperty(globalThis, "document");
}

beforeEach(() => {
  errors = [];
  console.error = (...args: unknown[]) => errors.push(args);
});

afterEach(() => {
  console.error = realError;
  uninstallDom();
});

function uncaughtLog(): unknown[] | undefined {
  return errors.find((e) => String(e[0]).includes("Uncaught initialization error"));
}

// ---------------------------------------------------------------------------
// createContext — non-DOM (background) path
// ---------------------------------------------------------------------------

describe("createContext (non-DOM context)", () => {
  test("returns a MessageBus for the requested context", () => {
    const bus = createContext("background", { adapters: createMockAdapters() });
    expect(bus).toBeInstanceOf(MessageBus);
    expect(bus.context).toBe("background");
  });

  test("runs onInit with the created bus", async () => {
    let received: unknown;
    const bus = createContext("background", {
      adapters: createMockAdapters(),
      onInit: (b) => {
        received = b;
      },
    });
    await flush();
    expect(received).toBe(bus);
  });

  test("logs nothing when there is no onInit", async () => {
    createContext("background", { adapters: createMockAdapters() });
    await flush();
    expect(errors).toEqual([]);
  });

  test("does not log a failure when onInit succeeds", async () => {
    createContext("background", {
      adapters: createMockAdapters(),
      onInit: () => {
        /* ok */
      },
    });
    await flush();
    expect(errors).toEqual([]);
  });

  test("routes an Error thrown by onInit to onError unchanged", async () => {
    const boom = new Error("init boom");
    let caught: Error | undefined;
    createContext("background", {
      adapters: createMockAdapters(),
      onInit: () => {
        throw boom;
      },
      onError: (e) => {
        caught = e;
      },
    });
    await flush();
    expect(caught).toBe(boom);
  });

  test("wraps a non-Error thrown value in an Error before routing it", async () => {
    let caught: Error | undefined;
    createContext("background", {
      adapters: createMockAdapters(),
      onInit: () => {
        throw "string failure";
      },
      onError: (e) => {
        caught = e;
      },
    });
    await flush();
    expect(caught).toBeInstanceOf(Error);
    expect(caught?.message).toBe("string failure");
  });

  test("logs an init failure with the default capitalized prefix", async () => {
    createContext("background", {
      adapters: createMockAdapters(),
      onInit: () => {
        throw new Error("x");
      },
      onError: () => {},
    });
    await flush();
    expect(errors.some((e) => e[0] === "[Background] Initialization failed:")).toBe(true);
  });

  test("honors a custom logPrefix", async () => {
    createContext("background", {
      adapters: createMockAdapters(),
      logPrefix: "CUSTOM",
      onInit: () => {
        throw new Error("x");
      },
      onError: () => {},
    });
    await flush();
    expect(errors.some((e) => e[0] === "CUSTOM Initialization failed:")).toBe(true);
  });

  test("without an onError, the original error is rethrown to the uncaught log", async () => {
    createContext("background", {
      adapters: createMockAdapters(),
      onInit: () => {
        throw new Error("nope");
      },
    });
    await flush();
    const entry = uncaughtLog();
    expect(entry).toBeDefined();
    // The rethrown value is the original error (not a TypeError from calling a
    // missing onError) — proving the `if (onError) … else throw err` branch.
    const rethrown = entry?.[1];
    if (!(rethrown instanceof Error)) throw new Error("expected the rethrown Error");
    expect(rethrown.message).toBe("nope");
  });
});

// ---------------------------------------------------------------------------
// createContext — onError wiring onto the bus (line 91)
// ---------------------------------------------------------------------------

describe("createContext (bus.onError registration)", () => {
  test("registers the onError handler on the bus when provided", () => {
    const original = MessageBus.prototype.onError;
    const registered: unknown[] = [];
    MessageBus.prototype.onError = function (
      this: MessageBus,
      handler: Parameters<typeof original>[0]
    ) {
      registered.push(handler);
      return original.call(this, handler);
    };
    try {
      const handler = () => {};
      createContext("background", { adapters: createMockAdapters(), onError: handler });
      expect(registered).toContain(handler);
    } finally {
      MessageBus.prototype.onError = original;
    }
  });

  test("does not touch bus.onError when no handler is provided", () => {
    const original = MessageBus.prototype.onError;
    let calls = 0;
    MessageBus.prototype.onError = function (
      this: MessageBus,
      handler: Parameters<typeof original>[0]
    ) {
      calls += 1;
      return original.call(this, handler);
    };
    try {
      createContext("background", { adapters: createMockAdapters() });
      expect(calls).toBe(0);
    } finally {
      MessageBus.prototype.onError = original;
    }
  });
});

// ---------------------------------------------------------------------------
// createContext — DOM path (faked window + document)
// ---------------------------------------------------------------------------

const DOM_CONTEXTS: Context[] = ["popup", "options", "devtools", "sidepanel", "content"];

describe("createContext (DOM context)", () => {
  for (const ctx of DOM_CONTEXTS) {
    test(`defers init to DOMContentLoaded while loading (${ctx})`, async () => {
      const dom = installDom("loading");
      let initialized = false;
      createContext(ctx, {
        adapters: createMockAdapters(),
        onInit: () => {
          initialized = true;
        },
      });
      await flush();
      expect(initialized).toBe(false);
      dom.fire("DOMContentLoaded");
      await flush();
      expect(initialized).toBe(true);
    });
  }

  test("initializes immediately when the document is already loaded", async () => {
    installDom("complete");
    let initialized = false;
    createContext("popup", {
      adapters: createMockAdapters(),
      onInit: () => {
        initialized = true;
      },
    });
    await flush();
    expect(initialized).toBe(true);
  });

  test("waitForDOM:false initializes immediately even while loading", async () => {
    installDom("loading");
    let initialized = false;
    createContext("popup", {
      adapters: createMockAdapters(),
      waitForDOM: false,
      onInit: () => {
        initialized = true;
      },
    });
    await flush();
    expect(initialized).toBe(true);
  });

  test("a non-DOM context initializes immediately even while the document loads", async () => {
    installDom("loading");
    let initialized = false;
    createContext("background", {
      adapters: createMockAdapters(),
      onInit: () => {
        initialized = true;
      },
    });
    await flush();
    expect(initialized).toBe(true);
  });

  test("a DOM context with no window present still initializes immediately", async () => {
    // No installDom(): window and document are both absent. The
    // `typeof window !== "undefined"` guard must keep us out of the DOM branch
    // (where `document.readyState` would throw).
    let initialized = false;
    expect(() =>
      createContext("popup", {
        adapters: createMockAdapters(),
        onInit: () => {
          initialized = true;
        },
      })
    ).not.toThrow();
    await flush();
    expect(initialized).toBe(true);
  });

  test("logs an uncaught error when a loaded-DOM init fails without onError", async () => {
    installDom("complete");
    createContext("popup", {
      adapters: createMockAdapters(),
      onInit: () => {
        throw new Error("loaded-fail");
      },
    });
    await flush();
    expect(uncaughtLog()).toBeDefined();
  });

  test("logs an uncaught error when a deferred init fails without onError", async () => {
    const dom = installDom("loading");
    createContext("popup", {
      adapters: createMockAdapters(),
      onInit: () => {
        throw new Error("deferred-fail");
      },
    });
    dom.fire("DOMContentLoaded");
    await flush();
    expect(uncaughtLog()).toBeDefined();
  });
});

// ---------------------------------------------------------------------------
// runInContext
// ---------------------------------------------------------------------------

describe("runInContext", () => {
  test("runs fn with a bus when the context matches a single target", async () => {
    let busArg: unknown;
    runInContext(
      "popup",
      "popup",
      (b) => {
        busArg = b;
      },
      createMockAdapters()
    );
    await flush();
    expect(busArg).toBeInstanceOf(MessageBus);
  });

  test("runs fn when the context is in a target array", async () => {
    let called = false;
    runInContext(
      "options",
      ["popup", "options"],
      () => {
        called = true;
      },
      createMockAdapters()
    );
    await flush();
    expect(called).toBe(true);
  });

  test("does not run fn when the context is not targeted", async () => {
    let called = false;
    runInContext(
      "background",
      ["popup", "options"],
      () => {
        called = true;
      },
      createMockAdapters()
    );
    await flush();
    expect(called).toBe(false);
  });

  test("wraps a single string target in an array (no substring matching)", async () => {
    let called = false;
    // "option" is a substring of the target "options" — array membership must
    // not treat it as a match (a defeated Array.isArray wrap would). The
    // escape hatch forces a deliberately out-of-union context value through.
    runInContext(
      "option" as unknown as Context,
      "options",
      () => {
        called = true;
      },
      createMockAdapters()
    );
    await flush();
    expect(called).toBe(false);
  });
});
