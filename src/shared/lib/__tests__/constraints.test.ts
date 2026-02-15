/**
 * Tests for DX Enhancement #2: Runtime Constraint Checking
 *
 * Tests constraint registration, precondition/postcondition checking,
 * and runtime enforcement.
 */

import { afterEach, describe, expect, test } from "bun:test";
import {
  checkPostconditions,
  checkPreconditions,
  clearConstraints,
  getRegisteredConstraints,
  isRuntimeConstraintsEnabled,
  registerConstraint,
  registerConstraints,
} from "../constraints";

describe("registerConstraint", () => {
  afterEach(() => {
    clearConstraints();
  });

  test("should register a constraint for a message type", () => {
    const constraint = {
      requires: (state: any) => state.loggedIn === true,
      message: "Must be logged in",
    };

    registerConstraint("auth", "USER_LOGOUT", constraint);

    const registered = getRegisteredConstraints();
    expect(registered.has("auth")).toBe(true);
    expect(registered.get("auth")?.has("USER_LOGOUT")).toBe(true);
  });

  test("should register multiple constraints for different message types", () => {
    registerConstraint("auth", "USER_LOGOUT", {
      requires: (state: any) => state.loggedIn,
    });

    registerConstraint("auth", "BOOKMARK_ADD", {
      requires: (state: any) => state.loggedIn,
    });

    const registered = getRegisteredConstraints();
    const authConstraints = registered.get("auth");

    expect(authConstraints?.has("USER_LOGOUT")).toBe(true);
    expect(authConstraints?.has("BOOKMARK_ADD")).toBe(true);
  });

  test("should register constraints for different state fields", () => {
    registerConstraint("auth", "USER_LOGOUT", {
      requires: (state: any) => state.loggedIn,
    });

    registerConstraint("bookmarks", "BOOKMARK_ADD", {
      requires: (state: any) => state.bookmarks.length < 100,
    });

    const registered = getRegisteredConstraints();
    expect(registered.has("auth")).toBe(true);
    expect(registered.has("bookmarks")).toBe(true);
  });

  test("should register both requires and ensures constraints", () => {
    const constraint = {
      requires: (state: any) => state.count >= 0,
      ensures: (state: any) => state.count > 0,
      message: "Count must increase",
    };

    registerConstraint("counter", "INCREMENT", constraint);

    const registered = getRegisteredConstraints();
    const counterConstraints = registered.get("counter");
    const incrementConstraint = counterConstraints?.get("INCREMENT");

    expect(incrementConstraint?.requires).toBeDefined();
    expect(incrementConstraint?.ensures).toBeDefined();
    expect(incrementConstraint?.message).toBe("Count must increase");
  });
});

describe("registerConstraints", () => {
  afterEach(() => {
    clearConstraints();
  });

  test("should register multiple constraints at once", () => {
    registerConstraints("auth", {
      USER_LOGOUT: {
        requires: (state: any) => state.loggedIn === true,
        message: "Must be logged in to logout",
      },
      BOOKMARK_ADD: {
        requires: (state: any) => state.loggedIn === true,
        message: "Must be logged in to add bookmarks",
      },
    });

    const registered = getRegisteredConstraints();
    const authConstraints = registered.get("auth");

    expect(authConstraints?.has("USER_LOGOUT")).toBe(true);
    expect(authConstraints?.has("BOOKMARK_ADD")).toBe(true);
  });

  test("should filter out string-only constraints (TLA+ generation)", () => {
    registerConstraints("auth", {
      USER_LOGOUT: {
        requires: "state.loggedIn === true", // String - for TLA+ only
        message: "Must be logged in",
      },
    });

    const registered = getRegisteredConstraints();
    // String-only constraints should not be registered for runtime
    expect(registered.has("auth")).toBe(false);
  });

  test("should register function-based constraints only", () => {
    registerConstraints("auth", {
      USER_LOGOUT: {
        requires: (state: any) => state.loggedIn === true,
        message: "Must be logged in",
      },
      BOOKMARK_ADD: {
        requires: "state.loggedIn === true", // String - should be filtered
      },
    });

    const registered = getRegisteredConstraints();
    const authConstraints = registered.get("auth");

    expect(authConstraints?.has("USER_LOGOUT")).toBe(true);
    expect(authConstraints?.has("BOOKMARK_ADD")).toBe(false); // Filtered out
  });

  test("should handle mixed requires and ensures", () => {
    registerConstraints("counter", {
      INCREMENT: {
        requires: (state: any) => state.count < 100,
        ensures: (state: any) => state.count > 0,
        message: "Count operations",
      },
    });

    const registered = getRegisteredConstraints();
    const counterConstraints = registered.get("counter");
    const incrementConstraint = counterConstraints?.get("INCREMENT");

    expect(incrementConstraint?.requires).toBeDefined();
    expect(incrementConstraint?.ensures).toBeDefined();
  });
});

describe("checkPreconditions", () => {
  afterEach(() => {
    clearConstraints();
  });

  test("should pass when precondition is met", () => {
    const state = { loggedIn: true };

    registerConstraint("auth", "USER_LOGOUT", {
      requires: (s: any) => s.loggedIn === true,
      message: "Must be logged in to logout",
    });

    // Should not throw
    expect(() => checkPreconditions("USER_LOGOUT", state)).not.toThrow();
  });

  test("should throw when precondition fails", () => {
    const state = { loggedIn: false };

    registerConstraint("auth", "USER_LOGOUT", {
      requires: (s: any) => s.loggedIn === true,
      message: "Must be logged in to logout",
    });

    expect(() => checkPreconditions("USER_LOGOUT", state)).toThrow("Must be logged in to logout");
  });

  test("should use default message when custom message not provided", () => {
    const state = { count: 0 };

    registerConstraint("counter", "INCREMENT", {
      requires: (s: any) => s.count > 0,
    });

    expect(() => checkPreconditions("INCREMENT", state)).toThrow(
      /Precondition failed for INCREMENT/
    );
  });

  test("should check multiple constraints for the same message", () => {
    const state = { loggedIn: true, count: 0 };

    registerConstraint("auth", "COMPLEX_OPERATION", {
      requires: (s: any) => s.loggedIn === true,
      message: "Must be logged in",
    });

    registerConstraint("counter", "COMPLEX_OPERATION", {
      requires: (s: any) => s.count > 0,
      message: "Count must be positive",
    });

    // Should fail on counter constraint
    expect(() => checkPreconditions("COMPLEX_OPERATION", state)).toThrow("Count must be positive");
  });

  test("should pass when no constraints are registered", () => {
    const state = { anything: true };

    // Should not throw
    expect(() => checkPreconditions("UNKNOWN_MESSAGE", state)).not.toThrow();
  });

  test("should handle constraint function errors gracefully", () => {
    const state = { value: null };

    registerConstraint("broken", "TEST", {
      requires: (s: any) => s.value.property.deep.access, // Will throw
      message: "Broken constraint",
    });

    expect(() => checkPreconditions("TEST", state)).toThrow();
  });
});

describe("checkPostconditions", () => {
  afterEach(() => {
    clearConstraints();
  });

  test("should pass when postcondition is met", () => {
    const state = { count: 5 };

    registerConstraint("counter", "INCREMENT", {
      ensures: (s: any) => s.count > 0,
      message: "Count must be positive after increment",
    });

    // Should not throw
    expect(() => checkPostconditions("INCREMENT", state)).not.toThrow();
  });

  test("should throw when postcondition fails", () => {
    const state = { count: 0 };

    registerConstraint("counter", "INCREMENT", {
      ensures: (s: any) => s.count > 0,
      message: "Count must be positive after increment",
    });

    expect(() => checkPostconditions("INCREMENT", state)).toThrow(
      "Count must be positive after increment"
    );
  });

  test("should use default message when custom message not provided", () => {
    const state = { valid: false };

    registerConstraint("validation", "PROCESS", {
      ensures: (s: any) => s.valid === true,
    });

    expect(() => checkPostconditions("PROCESS", state)).toThrow(/Postcondition failed for PROCESS/);
  });

  test("should check multiple postconditions", () => {
    const state = { count: 5, validated: false };

    registerConstraint("counter", "PROCESS", {
      ensures: (s: any) => s.count > 0,
    });

    registerConstraint("validation", "PROCESS", {
      ensures: (s: any) => s.validated === true,
      message: "Must be validated",
    });

    // Should fail on validation constraint
    expect(() => checkPostconditions("PROCESS", state)).toThrow("Must be validated");
  });

  test("should pass when no postconditions are registered", () => {
    const state = { anything: true };

    // Should not throw
    expect(() => checkPostconditions("UNKNOWN_MESSAGE", state)).not.toThrow();
  });
});

describe("clearConstraints", () => {
  test("should remove all registered constraints", () => {
    registerConstraint("auth", "USER_LOGOUT", {
      requires: (state: any) => state.loggedIn,
    });

    registerConstraint("counter", "INCREMENT", {
      requires: (state: any) => state.count < 100,
    });

    let registered = getRegisteredConstraints();
    expect(registered.size).toBe(2);

    clearConstraints();

    registered = getRegisteredConstraints();
    expect(registered.size).toBe(0);
  });
});

describe("getRegisteredConstraints", () => {
  afterEach(() => {
    clearConstraints();
  });

  test("should return copy of registry", () => {
    registerConstraint("auth", "USER_LOGOUT", {
      requires: (state: any) => state.loggedIn,
    });

    const registered = getRegisteredConstraints();
    expect(registered.size).toBe(1);

    // Modifying the returned map should not affect the registry
    registered.clear();

    const registeredAgain = getRegisteredConstraints();
    expect(registeredAgain.size).toBe(1); // Still has the original entry
  });

  test("should return empty map when no constraints registered", () => {
    const registered = getRegisteredConstraints();
    expect(registered.size).toBe(0);
  });
});

describe("isRuntimeConstraintsEnabled", () => {
  test("should return false by default", () => {
    // Without setting the environment variable
    expect(isRuntimeConstraintsEnabled()).toBe(false);
  });

  test("should return true when POLLY_RUNTIME_CONSTRAINTS=true in process.env", () => {
    // Set the environment variable
    if (typeof process !== "undefined" && process.env) {
      const original = process.env["POLLY_RUNTIME_CONSTRAINTS"];
      process.env["POLLY_RUNTIME_CONSTRAINTS"] = "true";

      expect(isRuntimeConstraintsEnabled()).toBe(true);

      // Restore
      if (original !== undefined) {
        process.env["POLLY_RUNTIME_CONSTRAINTS"] = original;
      } else {
        process.env["POLLY_RUNTIME_CONSTRAINTS"] = undefined;
      }
    }
  });

  test("should return true when POLLY_RUNTIME_CONSTRAINTS=true in Bun.env", () => {
    // Set the environment variable for Bun
    if (typeof Bun !== "undefined" && Bun.env) {
      const original = Bun.env["POLLY_RUNTIME_CONSTRAINTS"];
      Bun.env["POLLY_RUNTIME_CONSTRAINTS"] = "true";

      expect(isRuntimeConstraintsEnabled()).toBe(true);

      // Restore
      if (original !== undefined) {
        Bun.env["POLLY_RUNTIME_CONSTRAINTS"] = original;
      } else {
        Bun.env["POLLY_RUNTIME_CONSTRAINTS"] = undefined;
      }
    }
  });

  test("should return false when POLLY_RUNTIME_CONSTRAINTS=false", () => {
    if (typeof process !== "undefined" && process.env) {
      const original = process.env["POLLY_RUNTIME_CONSTRAINTS"];
      process.env["POLLY_RUNTIME_CONSTRAINTS"] = "false";

      expect(isRuntimeConstraintsEnabled()).toBe(false);

      // Restore
      if (original !== undefined) {
        process.env["POLLY_RUNTIME_CONSTRAINTS"] = original;
      } else {
        process.env["POLLY_RUNTIME_CONSTRAINTS"] = undefined;
      }
    }
  });
});

describe("Integration: Constraint workflow", () => {
  afterEach(() => {
    clearConstraints();
  });

  test("should enforce complete precondition -> execution -> postcondition flow", () => {
    const state = { count: 5, validated: false };

    // Register constraints
    registerConstraints("counter", {
      INCREMENT: {
        requires: (s: any) => s.count < 100,
        ensures: (s: any) => s.count > 5,
        message: "Increment constraints",
      },
    });

    // Check preconditions before execution
    expect(() => checkPreconditions("INCREMENT", state)).not.toThrow();

    // Simulate handler execution
    state.count = 10;
    state.validated = true;

    // Check postconditions after execution
    expect(() => checkPostconditions("INCREMENT", state)).not.toThrow();
  });

  test("should fail precondition before execution", () => {
    const state = { count: 150 }; // Over limit

    registerConstraints("counter", {
      INCREMENT: {
        requires: (s: any) => s.count < 100,
        message: "Count exceeds maximum",
      },
    });

    // Should fail before handler even executes
    expect(() => checkPreconditions("INCREMENT", state)).toThrow("Count exceeds maximum");
  });

  test("should fail postcondition after execution", () => {
    const state = { count: 5 };

    registerConstraints("counter", {
      DECREMENT: {
        ensures: (s: any) => s.count >= 0,
        message: "Count cannot be negative",
      },
    });

    // Preconditions pass (no requires)
    expect(() => checkPreconditions("DECREMENT", state)).not.toThrow();

    // Simulate buggy handler
    state.count = -1;

    // Postcondition should fail
    expect(() => checkPostconditions("DECREMENT", state)).toThrow("Count cannot be negative");
  });
});
