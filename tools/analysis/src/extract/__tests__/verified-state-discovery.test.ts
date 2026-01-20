import { afterEach, beforeEach, describe, expect, test } from "bun:test";
import * as fs from "node:fs";
import * as os from "node:os";
import * as path from "node:path";
import { HandlerExtractor } from "../handlers";

/**
 * Tests for Issue #27: TLA+ verification for standalone $sharedState handlers
 *
 * These tests verify that the handler extractor can:
 * 1. Detect $sharedState declarations with { verify: true }
 * 2. Find functions that modify verified states
 * 3. Extract requires()/ensures() annotations from those functions
 * 4. Generate appropriate message types from function names
 */
describe("HandlerExtractor - Verified State Discovery (Issue #27)", () => {
  let tempDir: string;

  beforeEach(() => {
    tempDir = fs.mkdtempSync(path.join(os.tmpdir(), "polly-verified-state-test-"));
  });

  afterEach(() => {
    if (fs.existsSync(tempDir)) {
      fs.rmSync(tempDir, { recursive: true });
    }
  });

  function createTsConfig(): string {
    const tsConfigPath = path.join(tempDir, "tsconfig.json");
    fs.writeFileSync(
      tsConfigPath,
      JSON.stringify({
        compilerOptions: {
          target: "ES2020",
          module: "ESNext",
          strict: true,
        },
        include: ["*.ts"],
      })
    );
    return tsConfigPath;
  }

  test("should detect $sharedState with verify: true", () => {
    const testFile = path.join(tempDir, "auth-state.ts");
    fs.writeFileSync(
      testFile,
      `
// Mock the $sharedState function
function $sharedState<T>(key: string, initial: T, options?: { verify?: boolean }) {
  return { value: initial };
}

const initialAuthState = {
  isAuthenticated: false,
  isLoading: false,
  userProfile: null,
  error: null,
};

export const authState = $sharedState('auth', initialAuthState, { verify: true });
`
    );

    const tsConfigPath = createTsConfig();
    const extractor = new HandlerExtractor(tsConfigPath);
    const result = extractor.extractHandlers();

    expect(result.verifiedStates.length).toBe(1);
    expect(result.verifiedStates[0].key).toBe("auth");
    expect(result.verifiedStates[0].variableName).toBe("authState");
    expect(result.verifiedStates[0].fields).toContain("isAuthenticated");
    expect(result.verifiedStates[0].fields).toContain("isLoading");
    expect(result.verifiedStates[0].fields).toContain("userProfile");
    expect(result.verifiedStates[0].fields).toContain("error");
  });

  test("should ignore $sharedState without verify: true", () => {
    const testFile = path.join(tempDir, "settings-state.ts");
    fs.writeFileSync(
      testFile,
      `
function $sharedState<T>(key: string, initial: T, options?: { verify?: boolean }) {
  return { value: initial };
}

// No verify option
export const settingsA = $sharedState('settings-a', { theme: 'dark' });

// verify: false
export const settingsB = $sharedState('settings-b', { theme: 'dark' }, { verify: false });

// verify: true - should be detected
export const settingsC = $sharedState('settings-c', { theme: 'dark' }, { verify: true });
`
    );

    const tsConfigPath = createTsConfig();
    const extractor = new HandlerExtractor(tsConfigPath);
    const result = extractor.extractHandlers();

    expect(result.verifiedStates.length).toBe(1);
    expect(result.verifiedStates[0].key).toBe("settings-c");
  });

  test("should discover exported functions that modify verified state", () => {
    const testFile = path.join(tempDir, "auth-handlers.ts");
    fs.writeFileSync(
      testFile,
      `
function $sharedState<T>(key: string, initial: T, options?: { verify?: boolean }) {
  return { value: initial };
}

const initialAuthState = {
  isAuthenticated: false,
  userProfile: null,
};

export const authState = $sharedState('auth', initialAuthState, { verify: true });

export function handleAuthSuccess(userProfile: { name: string }): void {
  authState.value = {
    ...authState.value,
    isAuthenticated: true,
    userProfile,
  };
}

export function handleLogout(): void {
  authState.value = {
    ...authState.value,
    isAuthenticated: false,
    userProfile: null,
  };
}

// Not exported - should be ignored
function internalHelper(): void {
  authState.value.isAuthenticated = true;
}
`
    );

    const tsConfigPath = createTsConfig();
    const extractor = new HandlerExtractor(tsConfigPath);
    const result = extractor.extractHandlers();

    // Should find 2 handlers from the exported functions
    const authHandlers = result.handlers.filter(
      (h) => h.messageType === "AuthSuccess" || h.messageType === "Logout"
    );
    expect(authHandlers.length).toBe(2);

    // Check AuthSuccess handler
    const authSuccessHandler = result.handlers.find((h) => h.messageType === "AuthSuccess");
    expect(authSuccessHandler).toBeDefined();
    expect(authSuccessHandler?.assignments.length).toBeGreaterThan(0);
    // Field names are prefixed with signal name for TLA+ verification
    expect(
      authSuccessHandler?.assignments.some((a) => a.field === "authState_isAuthenticated")
    ).toBe(true);

    // Check Logout handler
    const logoutHandler = result.handlers.find((h) => h.messageType === "Logout");
    expect(logoutHandler).toBeDefined();
  });

  test("should extract requires() and ensures() from state-modifying functions", () => {
    const testFile = path.join(tempDir, "verified-handlers.ts");
    fs.writeFileSync(
      testFile,
      `
function $sharedState<T>(key: string, initial: T, options?: { verify?: boolean }) {
  return { value: initial };
}

function requires(condition: boolean, message?: string): void {
  if (!condition) throw new Error(message);
}

function ensures(condition: boolean, message?: string): void {
  if (!condition) throw new Error(message);
}

const initialState = {
  isAuthenticated: false,
  userProfile: null,
};

export const authState = $sharedState('auth', initialState, { verify: true });

export function handleAuthSuccess(userProfile: { name: string }): void {
  requires(!authState.value.isAuthenticated, 'Must not already be authenticated');

  authState.value = {
    ...authState.value,
    isAuthenticated: true,
    userProfile,
  };

  ensures(authState.value.isAuthenticated, 'Must be authenticated after success');
  ensures(authState.value.userProfile !== null, 'Must have user profile');
}
`
    );

    const tsConfigPath = createTsConfig();
    const extractor = new HandlerExtractor(tsConfigPath);
    const result = extractor.extractHandlers();

    const authHandler = result.handlers.find((h) => h.messageType === "AuthSuccess");
    expect(authHandler).toBeDefined();

    // Should have precondition from requires()
    expect(authHandler?.preconditions.length).toBeGreaterThanOrEqual(1);
    expect(authHandler?.preconditions[0].expression).toContain("isAuthenticated");

    // Should have postconditions from ensures()
    expect(authHandler?.postconditions.length).toBeGreaterThanOrEqual(1);
  });

  test("should convert function names to message types correctly", () => {
    const testFile = path.join(tempDir, "name-conversion.ts");
    fs.writeFileSync(
      testFile,
      `
function $sharedState<T>(key: string, initial: T, options?: { verify?: boolean }) {
  return { value: initial };
}

export const state = $sharedState('test', { count: 0 }, { verify: true });

// handleX -> X
export function handleIncrement(): void {
  state.value.count = state.value.count + 1;
}

// onX -> X
export function onDecrement(): void {
  state.value.count = state.value.count - 1;
}

// setX -> SetX
export function setCount(n: number): void {
  state.value.count = n;
}

// updateX -> UpdateX
export function updateCounter(): void {
  state.value.count = 0;
}

// Regular name -> PascalCase
export function resetAll(): void {
  state.value.count = 0;
}
`
    );

    const tsConfigPath = createTsConfig();
    const extractor = new HandlerExtractor(tsConfigPath);
    const result = extractor.extractHandlers();

    const messageTypes = result.handlers.map((h) => h.messageType);

    expect(messageTypes).toContain("Increment");
    expect(messageTypes).toContain("Decrement");
    expect(messageTypes).toContain("SetCount");
    expect(messageTypes).toContain("UpdateCounter");
    expect(messageTypes).toContain("ResetAll");
  });

  test("should handle arrow functions exported as const", () => {
    const testFile = path.join(tempDir, "arrow-handlers.ts");
    fs.writeFileSync(
      testFile,
      `
function $sharedState<T>(key: string, initial: T, options?: { verify?: boolean }) {
  return { value: initial };
}

export const state = $sharedState('counter', { count: 0 }, { verify: true });

export const handleIncrement = (): void => {
  state.value.count = state.value.count + 1;
};

export const handleDecrement = (): void => {
  state.value.count = state.value.count - 1;
};
`
    );

    const tsConfigPath = createTsConfig();
    const extractor = new HandlerExtractor(tsConfigPath);
    const result = extractor.extractHandlers();

    expect(result.handlers.some((h) => h.messageType === "Increment")).toBe(true);
    expect(result.handlers.some((h) => h.messageType === "Decrement")).toBe(true);
  });

  test("should detect field updates via dot notation", () => {
    const testFile = path.join(tempDir, "field-updates.ts");
    fs.writeFileSync(
      testFile,
      `
function $sharedState<T>(key: string, initial: T, options?: { verify?: boolean }) {
  return { value: initial };
}

export const state = $sharedState('user', {
  name: '',
  email: '',
  active: false
}, { verify: true });

export function handleSetName(name: string): void {
  state.value.name = name;
}

export function handleActivate(): void {
  state.value.active = true;
}
`
    );

    const tsConfigPath = createTsConfig();
    const extractor = new HandlerExtractor(tsConfigPath);
    const result = extractor.extractHandlers();

    const setNameHandler = result.handlers.find((h) => h.messageType === "SetName");
    expect(setNameHandler).toBeDefined();
    // Field names are prefixed with signal name for TLA+ verification
    expect(setNameHandler?.assignments.some((a) => a.field === "state_name")).toBe(true);

    const activateHandler = result.handlers.find((h) => h.messageType === "Activate");
    expect(activateHandler).toBeDefined();
    // Field names are prefixed with signal name for TLA+ verification
    expect(
      activateHandler?.assignments.some((a) => a.field === "state_active" && a.value === true)
    ).toBe(true);
  });

  test("should handle multiple verified states in same file", () => {
    const testFile = path.join(tempDir, "multi-state.ts");
    fs.writeFileSync(
      testFile,
      `
function $sharedState<T>(key: string, initial: T, options?: { verify?: boolean }) {
  return { value: initial };
}

export const authState = $sharedState('auth', { loggedIn: false }, { verify: true });
export const uiState = $sharedState('ui', { theme: 'light' }, { verify: true });

export function handleLogin(): void {
  authState.value.loggedIn = true;
}

export function handleSetTheme(theme: string): void {
  uiState.value.theme = theme;
}
`
    );

    const tsConfigPath = createTsConfig();
    const extractor = new HandlerExtractor(tsConfigPath);
    const result = extractor.extractHandlers();

    expect(result.verifiedStates.length).toBe(2);
    expect(result.verifiedStates.map((s) => s.key)).toContain("auth");
    expect(result.verifiedStates.map((s) => s.key)).toContain("ui");

    expect(result.handlers.some((h) => h.messageType === "Login")).toBe(true);
    expect(result.handlers.some((h) => h.messageType === "SetTheme")).toBe(true);
  });
});
