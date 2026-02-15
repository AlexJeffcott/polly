import { describe, expect, test } from "bun:test";
import { checkNonInterference } from "../analysis/non-interference";
import type { MessageHandler } from "../types";

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
});
