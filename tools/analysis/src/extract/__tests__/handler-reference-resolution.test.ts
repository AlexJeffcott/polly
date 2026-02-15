import { afterEach, beforeEach, describe, expect, test } from "bun:test";
import * as fs from "node:fs";
import * as os from "node:os";
import * as path from "node:path";
import { HandlerExtractor } from "../handlers";

describe("HandlerExtractor - Function Reference Resolution", () => {
  let tempDir: string;

  beforeEach(() => {
    tempDir = fs.mkdtempSync(path.join(os.tmpdir(), "polly-handler-ref-test-"));
  });

  afterEach(() => {
    if (fs.existsSync(tempDir)) {
      fs.rmSync(tempDir, { recursive: true });
    }
  });

  test("DEBUG: check what is extracted", () => {
    const testFile = path.join(tempDir, "test.ts");
    fs.writeFileSync(
      testFile,
      `
const state = { count: 0 };

export const handlers = {
  increment: handleIncrement,
};

function handleIncrement() {
  state.count++;
}
`
    );

    const tsConfigPath = path.join(tempDir, "tsconfig.json");
    fs.writeFileSync(
      tsConfigPath,
      JSON.stringify({
        compilerOptions: {
          target: "ES2020",
          module: "ESNext",
        },
      })
    );

    const extractor = new HandlerExtractor(tsConfigPath);
    const result = extractor.extractHandlers([testFile], testFile);

    console.log("Handlers found:", result.handlers.length);
    for (const handler of result.handlers) {
      console.log("  - messageType:", handler.messageType);
      console.log("    assignments:", handler.assignments);
      console.log("    preconditions:", handler.preconditions);
      console.log("    postconditions:", handler.postconditions);
    }

    expect(result.handlers.length).toBeGreaterThan(0);
  });

  test("should discover handlers from bus.on() with function references", () => {
    // Create test file with bus.on() pattern using function references
    const testFile = path.join(tempDir, "verification-handlers.ts");
    fs.writeFileSync(
      testFile,
      `
const state = {
  authenticated: false,
  count: 0,
};

function handleQuery() {
  if (state.count < 5) {
    state.count++;
  }
}

function handleAuthenticate() {
  state.authenticated = true;
}

const bus = {
  on: (type: string, handler: () => void) => {}
};

bus.on("query", handleQuery);
bus.on("authenticate", handleAuthenticate);
`
    );

    // Create minimal tsconfig.json
    const tsConfigPath = path.join(tempDir, "tsconfig.json");
    fs.writeFileSync(
      tsConfigPath,
      JSON.stringify({
        compilerOptions: {
          target: "ES2020",
          module: "ESNext",
          strict: true,
        },
      })
    );

    // Extract handlers
    const extractor = new HandlerExtractor(tsConfigPath);
    const result = extractor.extractHandlers([testFile], testFile);

    // Should discover both handlers
    expect(result.handlers.length).toBeGreaterThanOrEqual(2);

    // Find query handler
    const queryHandler = result.handlers.find((h) => h.messageType === "query");
    expect(queryHandler).toBeDefined();
    expect(queryHandler?.assignments.length).toBeGreaterThan(0);
    expect(queryHandler?.assignments[0]?.field).toBe("count");

    // Find authenticate handler
    const authHandler = result.handlers.find((h) => h.messageType === "authenticate");
    expect(authHandler).toBeDefined();
    expect(authHandler?.assignments.length).toBeGreaterThan(0);
    expect(authHandler?.assignments[0]?.field).toBe("authenticated");
    expect(authHandler?.assignments[0]?.value).toBe(true);
  });

  test("should extract state transitions from referenced functions", () => {
    const testFile = path.join(tempDir, "handlers-with-transitions.ts");
    fs.writeFileSync(
      testFile,
      `
const state = {
  count: 0,
  items: [] as string[],
};

export const handlers = {
  increment: handleIncrement,
  addItem: handleAddItem,
};

function handleIncrement() {
  state.count++;
}

function handleAddItem() {
  state.items.push("new");
}
`
    );

    const tsConfigPath = path.join(tempDir, "tsconfig.json");
    fs.writeFileSync(
      tsConfigPath,
      JSON.stringify({
        compilerOptions: {
          target: "ES2020",
          module: "ESNext",
        },
      })
    );

    const extractor = new HandlerExtractor(tsConfigPath);
    const result = extractor.extractHandlers([testFile], testFile);

    const incrementHandler = result.handlers.find((h) => h.messageType === "increment");
    expect(incrementHandler).toBeDefined();
    expect(incrementHandler?.assignments.length).toBeGreaterThan(0);
    expect(incrementHandler?.assignments[0]?.field).toBe("count");

    const addItemHandler = result.handlers.find((h) => h.messageType === "addItem");
    expect(addItemHandler).toBeDefined();
    expect(addItemHandler?.assignments.length).toBeGreaterThan(0);
    expect(addItemHandler?.assignments[0]?.field).toBe("items");
  });

  test("should handle inline arrow functions in handler maps", () => {
    const testFile = path.join(tempDir, "inline-handlers.ts");
    fs.writeFileSync(
      testFile,
      `
const state = { active: false };

export const handlers = {
  activate: () => { state.active = true; },
  deactivate: () => { state.active = false; },
};
`
    );

    const tsConfigPath = path.join(tempDir, "tsconfig.json");
    fs.writeFileSync(
      tsConfigPath,
      JSON.stringify({
        compilerOptions: {
          target: "ES2020",
          module: "ESNext",
        },
      })
    );

    const extractor = new HandlerExtractor(tsConfigPath);
    const result = extractor.extractHandlers([testFile], testFile);

    const activateHandler = result.handlers.find((h) => h.messageType === "activate");
    expect(activateHandler).toBeDefined();
    expect(activateHandler?.assignments[0]?.field).toBe("active");
    expect(activateHandler?.assignments[0]?.value).toBe(true);
  });

  test("should extract verification conditions from referenced functions", () => {
    const testFile = path.join(tempDir, "handlers-with-conditions.ts");
    fs.writeFileSync(
      testFile,
      `
import { requires, ensures } from "@fairfox/polly-verify";

const state = {
  authenticated: false,
  count: 0,
};

export const handlers = {
  query: handleQuery,
};

function handleQuery() {
  requires(state.authenticated === true, "Must be authenticated");
  state.count++;
  ensures(state.count > 0, "Count must be positive");
}
`
    );

    const tsConfigPath = path.join(tempDir, "tsconfig.json");
    fs.writeFileSync(
      tsConfigPath,
      JSON.stringify({
        compilerOptions: {
          target: "ES2020",
          module: "ESNext",
        },
      })
    );

    const extractor = new HandlerExtractor(tsConfigPath);
    const result = extractor.extractHandlers([testFile], testFile);

    const queryHandler = result.handlers.find((h) => h.messageType === "query");
    expect(queryHandler).toBeDefined();

    // Check preconditions
    expect(queryHandler?.preconditions.length).toBeGreaterThan(0);
    expect(queryHandler?.preconditions[0]?.expression).toContain("authenticated");

    // Check postconditions
    expect(queryHandler?.postconditions.length).toBeGreaterThan(0);
    expect(queryHandler?.postconditions[0]?.expression).toContain("count");
  });

  test("should resolve function references in bus.on() patterns", () => {
    const testFile = path.join(tempDir, "bus-on-references.ts");
    fs.writeFileSync(
      testFile,
      `
const state = {
  count: 0,
  active: false,
};

export function handleIncrement() {
  state.count++;
}

export function handleActivate() {
  state.active = true;
}

// Simulate bus.on() pattern
const bus = {
  on: (type: string, handler: () => void) => {}
};

bus.on("increment", handleIncrement);
bus.on("activate", handleActivate);
`
    );

    const tsConfigPath = path.join(tempDir, "tsconfig.json");
    fs.writeFileSync(
      tsConfigPath,
      JSON.stringify({
        compilerOptions: {
          target: "ES2020",
          module: "ESNext",
        },
      })
    );

    const extractor = new HandlerExtractor(tsConfigPath);
    const result = extractor.extractHandlers([testFile], testFile);

    // Should discover both handlers via bus.on() with function references
    const incrementHandler = result.handlers.find((h) => h.messageType === "increment");
    expect(incrementHandler).toBeDefined();
    expect(incrementHandler?.assignments.length).toBeGreaterThan(0);
    expect(incrementHandler?.assignments[0]?.field).toBe("count");

    const activateHandler = result.handlers.find((h) => h.messageType === "activate");
    expect(activateHandler).toBeDefined();
    expect(activateHandler?.assignments.length).toBeGreaterThan(0);
    expect(activateHandler?.assignments[0]?.field).toBe("active");
    expect(activateHandler?.assignments[0]?.value).toBe(true);
  });

  test("should handle complex state mutations in referenced functions", () => {
    const testFile = path.join(tempDir, "complex-mutations.ts");
    fs.writeFileSync(
      testFile,
      `
const state = {
  count: 0,
  authenticated: false,
  items: [] as string[],
};

export const handlers = {
  connect: handleConnect,
};

function handleConnect() {
  state.count = 0;
  state.authenticated = false;
  state.items.length = 0;
}
`
    );

    const tsConfigPath = path.join(tempDir, "tsconfig.json");
    fs.writeFileSync(
      tsConfigPath,
      JSON.stringify({
        compilerOptions: {
          target: "ES2020",
          module: "ESNext",
        },
      })
    );

    const extractor = new HandlerExtractor(tsConfigPath);
    const result = extractor.extractHandlers([testFile], testFile);

    const connectHandler = result.handlers.find((h) => h.messageType === "connect");
    expect(connectHandler).toBeDefined();
    expect(connectHandler?.assignments.length).toBeGreaterThanOrEqual(2);

    // Should extract count and authenticated assignments
    const countAssignment = connectHandler?.assignments.find((a) => a.field === "count");
    expect(countAssignment).toBeDefined();
    expect(countAssignment?.value).toBe(0);

    const authAssignment = connectHandler?.assignments.find((a) => a.field === "authenticated");
    expect(authAssignment).toBeDefined();
    expect(authAssignment?.value).toBe(false);
  });

  test("should extract state mutations from .value pattern (signal-based state)", () => {
    const testFile = path.join(tempDir, "signal-state-handlers.ts");
    fs.writeFileSync(
      testFile,
      `
// Simulate $sharedState signal pattern
const connectionState = {
  value: {
    authenticated: false,
    connected: false,
    user: null as { userId: number; handle: string } | null,
  }
};

// Plain state object for verification
const state = {
  authenticated: false,
  connected: false,
  user: null as { userId: number; handle: string } | null,
};

const bus = {
  on: (type: string, handler: () => void) => {}
};

// Handler using .value pattern (currently not extracted)
bus.on("authenticate", async () => {
  connectionState.value = {
    ...connectionState.value,
    authenticated: true,
    user: { userId: 1, handle: 'testuser' },
  };
});

// Handler using direct state mutation (currently works)
bus.on("connect", async () => {
  state.connected = true;
});
`
    );

    const tsConfigPath = path.join(tempDir, "tsconfig.json");
    fs.writeFileSync(
      tsConfigPath,
      JSON.stringify({
        compilerOptions: {
          target: "ES2020",
          module: "ESNext",
        },
      })
    );

    const extractor = new HandlerExtractor(tsConfigPath);
    const result = extractor.extractHandlers([testFile], testFile);

    // Should find both handlers
    expect(result.handlers.length).toBeGreaterThanOrEqual(2);

    // Direct state mutation should work (baseline)
    const connectHandler = result.handlers.find((h) => h.messageType === "connect");
    expect(connectHandler).toBeDefined();
    expect(connectHandler?.assignments.length).toBeGreaterThan(0);
    expect(connectHandler?.assignments[0]?.field).toBe("connected");
    expect(connectHandler?.assignments[0]?.value).toBe(true);

    // .value pattern should also work (ISSUE #25)
    const authHandler = result.handlers.find((h) => h.messageType === "authenticate");
    expect(authHandler).toBeDefined();
    expect(authHandler?.assignments.length).toBeGreaterThan(0);

    // Should extract authenticated field from object spread
    // Field names are prefixed with signal name for TLA+ verification
    const authAssignment = authHandler?.assignments.find(
      (a) => a.field === "connectionState_authenticated"
    );
    expect(authAssignment).toBeDefined();
    expect(authAssignment?.value).toBe(true);
  });

  test("should extract nested .value.field assignments", () => {
    const testFile = path.join(tempDir, "nested-value-assignments.ts");
    fs.writeFileSync(
      testFile,
      `
const connectionState = {
  value: {
    authenticated: false,
    count: 0,
  }
};

const bus = {
  on: (type: string, handler: () => void) => {}
};

bus.on("authenticate", async () => {
  // Direct nested property assignment
  connectionState.value.authenticated = true;
});

bus.on("increment", async () => {
  connectionState.value.count++;
});
`
    );

    const tsConfigPath = path.join(tempDir, "tsconfig.json");
    fs.writeFileSync(
      tsConfigPath,
      JSON.stringify({
        compilerOptions: {
          target: "ES2020",
          module: "ESNext",
        },
      })
    );

    const extractor = new HandlerExtractor(tsConfigPath);
    const result = extractor.extractHandlers([testFile], testFile);

    // Find authenticate handler with nested .value.field assignment
    const authHandler = result.handlers.find((h) => h.messageType === "authenticate");
    expect(authHandler).toBeDefined();
    expect(authHandler?.assignments.length).toBeGreaterThan(0);
    // Field names are prefixed with signal name for TLA+ verification
    expect(authHandler?.assignments[0]?.field).toBe("connectionState_authenticated");
    expect(authHandler?.assignments[0]?.value).toBe(true);

    // Find increment handler with unary operator on nested property
    const incrementHandler = result.handlers.find((h) => h.messageType === "increment");
    expect(incrementHandler).toBeDefined();
    expect(incrementHandler?.assignments.length).toBeGreaterThan(0);
    expect(incrementHandler?.assignments[0]?.field).toBe("count");
  });
});
