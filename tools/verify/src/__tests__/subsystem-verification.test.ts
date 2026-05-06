import { describe, expect, test } from "bun:test";
import { checkNonInterference } from "../analysis/non-interference";
import { checkPreconditionLocality } from "../analysis/precondition-locality";
import type { MessageHandler, VerificationCondition } from "../types";

function makeHandler(messageType: string, fields: string[]): MessageHandler {
  return {
    messageType,
    node: "test",
    assignments: fields.map((field) => ({
      field,
      value: "true",
    })),
    preconditions: [],
    postconditions: [],
    constraints: [],
    context: "background",
    filePath: "test.ts",
    lineNumber: 1,
  };
}

function makeHandlerWithRequires(
  messageType: string,
  writes: string[],
  requires: string[]
): MessageHandler {
  const preconditions: VerificationCondition[] = requires.map((expression, i) => ({
    expression,
    location: { line: i + 1, column: 1 },
  }));
  return {
    ...makeHandler(messageType, writes),
    preconditions,
    location: { file: "test.ts", line: 1 },
  };
}

describe("Non-interference checker", () => {
  test("passes when subsystems have disjoint state writes", () => {
    const subsystems = {
      auth: {
        state: ["loggedIn"],
        handlers: ["Login", "Logout"],
      },
      connection: {
        state: ["status"],
        handlers: ["Connect", "Disconnect"],
      },
    };

    const handlers = [
      makeHandler("Login", ["loggedIn"]),
      makeHandler("Logout", ["loggedIn"]),
      makeHandler("Connect", ["status"]),
      makeHandler("Disconnect", ["status"]),
    ];

    const result = checkNonInterference(subsystems, handlers);
    expect(result.valid).toBe(true);
    expect(result.violations).toHaveLength(0);
  });

  test("detects cross-subsystem state writes", () => {
    const subsystems = {
      auth: {
        state: ["loggedIn"],
        handlers: ["Login", "Logout"],
      },
      connection: {
        state: ["status"],
        handlers: ["Connect"],
      },
    };

    const handlers = [
      makeHandler("Login", ["loggedIn"]),
      makeHandler("Logout", ["loggedIn"]),
      // Connect writes to loggedIn which is owned by auth
      makeHandler("Connect", ["status", "loggedIn"]),
    ];

    const result = checkNonInterference(subsystems, handlers);
    expect(result.valid).toBe(false);
    expect(result.violations).toHaveLength(1);
    expect(result.violations[0]).toEqual({
      handler: "Connect",
      subsystem: "connection",
      writesTo: "loggedIn",
      ownedBy: "auth",
    });
  });

  test("ignores handlers not assigned to any subsystem", () => {
    const subsystems = {
      auth: {
        state: ["loggedIn"],
        handlers: ["Login"],
      },
    };

    // UnassignedHandler writes to loggedIn but is not in any subsystem
    const handlers = [
      makeHandler("Login", ["loggedIn"]),
      makeHandler("UnassignedHandler", ["loggedIn"]),
    ];

    const result = checkNonInterference(subsystems, handlers);
    expect(result.valid).toBe(true);
  });

  test("ignores writes to unowned fields", () => {
    const subsystems = {
      auth: {
        state: ["loggedIn"],
        handlers: ["Login"],
      },
    };

    // Login writes to both loggedIn (owned) and timestamp (not owned by any subsystem)
    const handlers = [makeHandler("Login", ["loggedIn", "timestamp"])];

    const result = checkNonInterference(subsystems, handlers);
    expect(result.valid).toBe(true);
  });

  test("detects multiple violations", () => {
    const subsystems = {
      auth: {
        state: ["loggedIn", "authToken"],
        handlers: ["Login"],
      },
      ui: {
        state: ["theme"],
        handlers: ["SetTheme"],
      },
    };

    const handlers = [
      // Login writes to theme (owned by ui)
      makeHandler("Login", ["loggedIn", "theme"]),
      // SetTheme writes to authToken (owned by auth)
      makeHandler("SetTheme", ["theme", "authToken"]),
    ];

    const result = checkNonInterference(subsystems, handlers);
    expect(result.valid).toBe(false);
    expect(result.violations).toHaveLength(2);
  });
});

describe("Precondition-locality checker", () => {
  test("passes when handlers only read state owned by their subsystem", () => {
    const subsystems = {
      auth: {
        state: ["user.loggedIn"],
        handlers: ["Login", "Logout"],
      },
      todos: {
        state: ["todos"],
        handlers: ["AddTodo"],
      },
    };

    const handlers = [
      makeHandlerWithRequires("Login", ["user.loggedIn"], ["state.user.loggedIn === false"]),
      makeHandlerWithRequires("Logout", ["user.loggedIn"], ["user.value.loggedIn === true"]),
      makeHandlerWithRequires("AddTodo", ["todos"], ["todos.value.length < 100"]),
    ];

    const result = checkPreconditionLocality(subsystems, handlers);
    expect(result.valid).toBe(true);
    expect(result.violations).toHaveLength(0);
  });

  test("flags a handler whose requires() reads state owned by another subsystem", () => {
    const subsystems = {
      auth: {
        state: ["user.loggedIn"],
        handlers: ["Login"],
      },
      connection: {
        state: ["connectionState.phase"],
        handlers: ["Disconnect"],
      },
    };

    const handlers = [
      makeHandlerWithRequires("Login", ["user.loggedIn"], ["state.user.loggedIn === false"]),
      // Disconnect lives in `connection` but reads `user.loggedIn` owned by `auth`
      makeHandlerWithRequires(
        "Disconnect",
        ["connectionState.phase"],
        ["state.user.loggedIn === true"]
      ),
    ];

    const result = checkPreconditionLocality(subsystems, handlers);
    expect(result.valid).toBe(false);
    expect(result.violations).toHaveLength(1);
    expect(result.violations[0]).toMatchObject({
      handler: "Disconnect",
      subsystem: "connection",
      readsFrom: "user.loggedIn",
      ownedBy: "auth",
      expression: "state.user.loggedIn === true",
    });
  });

  test("ignores handlers not assigned to any subsystem", () => {
    const subsystems = {
      auth: { state: ["user.loggedIn"], handlers: ["Login"] },
    };

    const handlers = [
      makeHandlerWithRequires("Login", ["user.loggedIn"], ["state.user.loggedIn === false"]),
      // Orphan handler reads auth state but is not in any subsystem
      makeHandlerWithRequires("Orphan", [], ["state.user.loggedIn === true"]),
    ];

    const result = checkPreconditionLocality(subsystems, handlers);
    expect(result.valid).toBe(true);
  });

  test("ignores reads of fields owned by no subsystem", () => {
    const subsystems = {
      auth: { state: ["user.loggedIn"], handlers: ["Login"] },
    };

    // Login reads `system.timestamp` which no subsystem claims; this is not a
    // cross-subsystem read because no other subsystem could produce it either.
    const handlers = [
      makeHandlerWithRequires(
        "Login",
        ["user.loggedIn"],
        ["state.user.loggedIn === false && state.system.timestamp > 0"]
      ),
    ];

    const result = checkPreconditionLocality(subsystems, handlers);
    expect(result.valid).toBe(true);
  });

  test("detects multiple cross-subsystem reads in the same expression", () => {
    const subsystems = {
      auth: { state: ["user.loggedIn"], handlers: ["Login"] },
      ui: { state: ["theme"], handlers: ["SetTheme"] },
      connection: { state: ["connectionState.phase"], handlers: ["Disconnect"] },
    };

    const handlers = [
      makeHandlerWithRequires(
        "Disconnect",
        ["connectionState.phase"],
        ["state.user.loggedIn === true && state.theme === 'dark'"]
      ),
    ];

    const result = checkPreconditionLocality(subsystems, handlers);
    expect(result.valid).toBe(false);
    expect(result.violations).toHaveLength(2);
    const ownersFlagged = result.violations.map((v) => v.ownedBy).sort();
    expect(ownersFlagged).toEqual(["auth", "ui"]);
  });

  test("normalizes dot-form refs against underscore-form state keys", () => {
    // Some configs declare state with underscore form (user_loggedIn) rather
    // than dot form (user.loggedIn); the analyzer should still resolve the
    // owner regardless of which form the ref or the config uses.
    const subsystems = {
      auth: { state: ["user_loggedIn"], handlers: ["Login"] },
      connection: { state: ["connectionState_phase"], handlers: ["Disconnect"] },
    };

    const handlers = [
      makeHandlerWithRequires(
        "Disconnect",
        ["connectionState_phase"],
        ["user.value.loggedIn === true"]
      ),
    ];

    const result = checkPreconditionLocality(subsystems, handlers);
    expect(result.valid).toBe(false);
    expect(result.violations[0]?.ownedBy).toBe("auth");
  });

  test("strips .length suffix to find the owning array field", () => {
    // requires(todos.value.length > 0) extracts `todos.length`; the owner is
    // the parent `todos` field.
    const subsystems = {
      auth: { state: ["user.loggedIn"], handlers: ["Login"] },
      todos: { state: ["todos"], handlers: ["AddTodo"] },
    };

    const handlers = [
      // Login (auth) reads todos.length — owned by todos subsystem
      makeHandlerWithRequires(
        "Login",
        ["user.loggedIn"],
        ["state.user.loggedIn === false && todos.value.length > 0"]
      ),
    ];

    const result = checkPreconditionLocality(subsystems, handlers);
    expect(result.valid).toBe(false);
    expect(result.violations[0]).toMatchObject({
      handler: "Login",
      subsystem: "auth",
      readsFrom: "todos.length",
      ownedBy: "todos",
    });
  });

  test("ignores payload-only preconditions", () => {
    const subsystems = {
      auth: { state: ["user.loggedIn"], handlers: ["Login"] },
    };

    const handlers = [
      makeHandlerWithRequires("Login", ["user.loggedIn"], ["payload.role !== 'guest'"]),
    ];

    const result = checkPreconditionLocality(subsystems, handlers);
    expect(result.valid).toBe(true);
  });

  test("attaches expression and location to each violation", () => {
    const subsystems = {
      auth: { state: ["user.loggedIn"], handlers: ["Login"] },
      connection: { state: ["connectionState.phase"], handlers: ["Disconnect"] },
    };

    const handlers = [
      makeHandlerWithRequires(
        "Disconnect",
        ["connectionState.phase"],
        ["state.user.loggedIn === true"]
      ),
    ];

    const result = checkPreconditionLocality(subsystems, handlers);
    expect(result.violations[0]).toMatchObject({
      expression: "state.user.loggedIn === true",
      location: { file: "test.ts", line: 1, column: 1 },
    });
  });
});

describe("Subsystem TLA+ generation", () => {
  test("generateSubsystemTLA filters config and analysis", async () => {
    const { generateSubsystemTLA } = await import("../codegen/tla");

    const config = {
      state: {
        loggedIn: [false, true],
        status: { type: "enum" as const, values: ["idle", "connected"] },
        theme: { type: "enum" as const, values: ["light", "dark"] },
      },
      messages: {
        maxInFlight: 2,
        maxTabs: 1,
        include: ["Login", "Logout", "Connect", "Disconnect", "SetTheme"],
        perMessageBounds: { Login: 1, Logout: 1, Connect: 2 },
      },
      onBuild: "warn" as const,
      onRelease: "error" as const,
    };

    const analysis = {
      stateType: null,
      messageTypes: ["Login", "Logout", "Connect", "Disconnect", "SetTheme"],
      fields: [],
      handlers: [
        makeHandler("Login", ["loggedIn"]),
        makeHandler("Logout", ["loggedIn"]),
        makeHandler("Connect", ["status"]),
        makeHandler("Disconnect", ["status"]),
        makeHandler("SetTheme", ["theme"]),
      ],
      stateConstraints: [],
    };

    const subsystem = {
      state: ["loggedIn"],
      handlers: ["Login", "Logout"],
    };

    const result = await generateSubsystemTLA("auth", subsystem, config, analysis);

    // The spec should contain Login/Logout handlers but not Connect/Disconnect/SetTheme handlers
    expect(result.spec).toContain("HandleLogin");
    expect(result.spec).toContain("HandleLogout");
    expect(result.spec).not.toContain("HandleConnect");
    expect(result.spec).not.toContain("HandleSetTheme");

    // MessageTypes should only include the subsystem's handlers
    expect(result.spec).toContain('"Login"');
    expect(result.spec).toContain('"Logout"');
    expect(result.spec).not.toContain('"SetTheme"');

    // The cfg should exist
    expect(result.cfg).toBeTruthy();
  });

  test("subsystem bounds.maxInFlight overrides the top-level maxInFlight", async () => {
    const { generateSubsystemTLA } = await import("../codegen/tla");

    const config = {
      state: {
        loggedIn: { type: "boolean" as const },
        status: { type: "enum" as const, values: ["idle", "connected"] },
      },
      messages: {
        maxInFlight: 1, // global stays cheap (e.g. unbounded payloads elsewhere)
        maxTabs: 1,
        include: ["Login", "Logout", "Connect", "Disconnect"],
      },
      onBuild: "warn" as const,
      onRelease: "error" as const,
    };

    const analysis = {
      stateType: null,
      messageTypes: ["Login", "Logout", "Connect", "Disconnect"],
      fields: [],
      handlers: [
        makeHandler("Login", ["loggedIn"]),
        makeHandler("Logout", ["loggedIn"]),
        makeHandler("Connect", ["status"]),
        makeHandler("Disconnect", ["status"]),
      ],
      stateConstraints: [],
    };

    const subsystem = {
      state: ["status"],
      handlers: ["Connect", "Disconnect"],
      bounds: { maxInFlight: 3 },
    };

    const result = await generateSubsystemTLA("connection", subsystem, config, analysis);

    // The override must reach the .cfg as MaxMessages = 3, not the global 1.
    expect(result.cfg).toContain("MaxMessages = 3");
    expect(result.cfg).not.toContain("MaxMessages = 1");
  });

  test("subsystem bounds.perMessageBounds merges over the top-level perMessageBounds", async () => {
    const { generateSubsystemTLA } = await import("../codegen/tla");

    const config = {
      state: {
        status: { type: "enum" as const, values: ["idle", "connected"] },
      },
      messages: {
        maxInFlight: 1,
        maxTabs: 1,
        include: ["Connect", "Disconnect"],
        perMessageBounds: { Connect: 1 }, // global default
      },
      onBuild: "warn" as const,
      onRelease: "error" as const,
    };

    const analysis = {
      stateType: null,
      messageTypes: ["Connect", "Disconnect"],
      fields: [],
      handlers: [makeHandler("Connect", ["status"]), makeHandler("Disconnect", ["status"])],
      stateConstraints: [],
    };

    const subsystem = {
      state: ["status"],
      handlers: ["Connect", "Disconnect"],
      bounds: {
        maxInFlight: 2,
        perMessageBounds: { Connect: 2, Disconnect: 2 },
      },
    };

    const result = await generateSubsystemTLA("connection", subsystem, config, analysis);

    expect(result.cfg).toContain("MaxMessages = 2");
    expect(result.cfg).toContain("MaxMessages_Connect = 2");
    expect(result.cfg).toContain("MaxMessages_Disconnect = 2");
    expect(result.cfg).not.toContain("MaxMessages_Connect = 1");
  });
});
