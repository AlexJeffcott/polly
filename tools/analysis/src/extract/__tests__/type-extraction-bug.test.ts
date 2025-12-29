import { afterEach, beforeEach, describe, expect, test } from "bun:test";
import * as fs from "node:fs";
import * as os from "node:os";
import * as path from "node:path";
import { analyzeCodebase } from "../types";

/**
 * Tests to reproduce and prevent the bug from issue #11:
 * The code analyzer was picking up TypeScript type syntax like
 * `{ ok: true; value: t }` and treating it as message types,
 * causing TLA+ generation to fail.
 *
 * These tests ensure that ONLY valid message types are extracted,
 * and complex TypeScript type definitions are ignored.
 */
describe("Bug #11: Type Extraction Should Ignore Complex Type Definitions", () => {
  let tempDir: string;

  beforeEach(() => {
    tempDir = fs.mkdtempSync(path.join(os.tmpdir(), "polly-bug-11-"));
  });

  afterEach(() => {
    if (fs.existsSync(tempDir)) {
      fs.rmSync(tempDir, { recursive: true });
    }
  });

  /**
   * This test reproduces the exact scenario from issue #11
   * where a Result<T, E> type was being picked up as message types
   */
  test("should not extract type definition syntax as message types", async () => {
    const tsConfigPath = path.join(tempDir, "tsconfig.json");
    fs.writeFileSync(
      tsConfigPath,
      JSON.stringify({
        compilerOptions: {
          target: "ES2020",
          module: "commonjs",
          strict: true,
          esModuleInterop: true,
          skipLibCheck: true,
          forceConsistentCasingInFileNames: true,
        },
        include: ["**/*.ts"],
      })
    );

    // Create a file with Result type (from the bug report)
    const typesFile = path.join(tempDir, "types.ts");
    fs.writeFileSync(
      typesFile,
      `
// This is the exact type from the bug report
export type Result<T, E = Error> =
  | { ok: true; value: T }
  | { ok: false; error: E };

export interface QueryResponse {
  data: Result<string>;
}
`
    );

    // Create a messages file with valid message types and a handler
    const messagesFile = path.join(tempDir, "messages.ts");
    fs.writeFileSync(
      messagesFile,
      `
export type Message =
  | { type: 'query' }
  | { type: 'command' }
  | { type: 'subscribe' };

// Handler that uses the message types (so they get extracted)
export function handleMessage(msg: Message) {
  switch (msg.type) {
    case 'query':
      break;
    case 'command':
      break;
    case 'subscribe':
      break;
  }
}
`
    );

    // Analyze the codebase
    const analysis = await analyzeCodebase({
      tsConfigPath,
    });

    // Should extract ONLY the valid message types
    expect(analysis.messageTypes).toContain("query");
    expect(analysis.messageTypes).toContain("command");
    expect(analysis.messageTypes).toContain("subscribe");

    // Should NOT extract the Result type syntax
    const invalidTypes = [
      "{ ok: true; value: t }",
      "{ ok: false; error: e }",
      "{ ok: true; value: T }",
      "{ ok: false; error: E }",
      "ok",
      "value",
      "error",
    ];

    for (const invalidType of invalidTypes) {
      expect(analysis.messageTypes).not.toContain(invalidType);
    }

    // ALL extracted types should be valid TLA+ identifiers
    for (const msgType of analysis.messageTypes) {
      expect(msgType).toMatch(/^[a-zA-Z][a-zA-Z0-9_]*$/);
    }
  });

  /**
   * Test that object type literals in unions don't pollute message types
   */
  test("should ignore object type literals without 'type' property", async () => {
    const tsConfigPath = path.join(tempDir, "tsconfig.json");
    fs.writeFileSync(
      tsConfigPath,
      JSON.stringify({
        compilerOptions: {
          target: "ES2020",
          module: "commonjs",
          strict: true,
        },
        include: ["**/*.ts"],
      })
    );

    const messagesFile = path.join(tempDir, "messages.ts");
    fs.writeFileSync(
      messagesFile,
      `
// Valid message types
export type ValidMessage =
  | { type: 'authenticate' }
  | { type: 'logout' };

// Complex types that should be ignored
export type Option<T> =
  | { some: T }
  | { none: true };

export type Either<L, R> =
  | { left: L }
  | { right: R };

// Handler that uses the message types
export function handleValidMessage(msg: ValidMessage) {
  switch (msg.type) {
    case 'authenticate':
      break;
    case 'logout':
      break;
  }
}
`
    );

    const analysis = await analyzeCodebase({ tsConfigPath });

    // Should only extract the valid message types
    expect(analysis.messageTypes).toContain("authenticate");
    expect(analysis.messageTypes).toContain("logout");
    expect(analysis.messageTypes.length).toBe(2);
  });

  /**
   * Test that type guards with complex generic types don't leak
   */
  test("should not extract type guard predicates with complex types", async () => {
    const tsConfigPath = path.join(tempDir, "tsconfig.json");
    fs.writeFileSync(
      tsConfigPath,
      JSON.stringify({
        compilerOptions: {
          target: "ES2020",
          module: "commonjs",
          strict: true,
        },
        include: ["**/*.ts"],
      })
    );

    const handlersFile = path.join(tempDir, "handlers.ts");
    fs.writeFileSync(
      handlersFile,
      `
// Result type (should be ignored)
type Result<T> = { ok: true; value: T } | { ok: false; error: Error };

// Valid message types with type guards
type QueryMessage = { type: 'query'; payload: string };

function isQueryMessage(msg: any): msg is QueryMessage {
  return msg.type === 'query';
}

function handleMessage(msg: any) {
  if (isQueryMessage(msg)) {
    // Handle query
    console.log(msg.payload);
  }
}

// Using Result type (shouldn't extract Result's internals)
function processResult(r: Result<string>) {
  if ('ok' in r && r.ok) {
    console.log(r.value);
  }
}
`
    );

    const analysis = await analyzeCodebase({ tsConfigPath });

    // Should only extract 'query' from the type guard
    expect(analysis.messageTypes).toContain("query");

    // Should NOT extract anything from Result type
    const invalidTypes = ["ok", "value", "error", "{ ok: true; value: T }"];
    for (const invalid of invalidTypes) {
      expect(analysis.messageTypes).not.toContain(invalid);
    }

    // All types should be valid TLA+ identifiers
    for (const msgType of analysis.messageTypes) {
      expect(msgType).toMatch(/^[a-zA-Z][a-zA-Z0-9_]*$/);
    }
  });

  /**
   * Test that switch cases with property checks don't leak
   */
  test("should not extract property names from object checks in switch", async () => {
    const tsConfigPath = path.join(tempDir, "tsconfig.json");
    fs.writeFileSync(
      tsConfigPath,
      JSON.stringify({
        compilerOptions: {
          target: "ES2020",
          module: "commonjs",
          strict: true,
        },
        include: ["**/*.ts"],
      })
    );

    const handlersFile = path.join(tempDir, "handlers.ts");
    fs.writeFileSync(
      handlersFile,
      `
type Message = { type: 'query' } | { type: 'command' };
type Result<T> = { ok: true; value: T } | { ok: false; error: Error };

function handleMessage(msg: Message) {
  switch (msg.type) {
    case 'query':
      // Handle query
      break;
    case 'command':
      // Handle command
      break;
  }
}

function handleResult<T>(result: Result<T>) {
  // This should NOT extract 'ok', 'value', or 'error' as message types
  if ('ok' in result) {
    if (result.ok) {
      console.log(result.value);
    } else {
      console.log(result.error);
    }
  }
}
`
    );

    const analysis = await analyzeCodebase({ tsConfigPath });

    // Should extract valid message types
    expect(analysis.messageTypes).toContain("query");
    expect(analysis.messageTypes).toContain("command");

    // Should NOT extract Result properties
    const invalidTypes = ["ok", "value", "error"];
    for (const invalid of invalidTypes) {
      expect(analysis.messageTypes).not.toContain(invalid);
    }
  });

  /**
   * Test with the exact file structure from issue #11
   */
  test("should handle realistic CMS codebase structure (from issue #11)", async () => {
    const tsConfigPath = path.join(tempDir, "tsconfig.json");
    fs.writeFileSync(
      tsConfigPath,
      JSON.stringify({
        compilerOptions: {
          target: "ES2020",
          module: "ESNext",
          strict: true,
          esModuleInterop: true,
          skipLibCheck: true,
        },
        include: ["src/**/*.ts"],
      })
    );

    // Create src directory
    const srcDir = path.join(tempDir, "src");
    fs.mkdirSync(srcDir, { recursive: true });

    // Create types file (should be ignored by analyzer)
    const typesFile = path.join(srcDir, "types.ts");
    fs.writeFileSync(
      typesFile,
      `
export type Result<T, E = Error> =
  | { ok: true; value: T }
  | { ok: false; error: E };

export type Option<T> =
  | { some: T }
  | { none: true };
`
    );

    // Create WebSocket message types (should be extracted)
    const wsMessagesFile = path.join(srcDir, "ws-messages.ts");
    fs.writeFileSync(
      wsMessagesFile,
      `
export type WSMessage =
  | { type: 'authenticate'; token: string }
  | { type: 'query'; resource: string }
  | { type: 'command'; action: string }
  | { type: 'subscribe'; topic: string }
  | { type: 'unsubscribe'; topic: string };
`
    );

    // Create message handlers file
    const handlersFile = path.join(srcDir, "message-handlers.ts");
    fs.writeFileSync(
      handlersFile,
      `
import type { WSMessage } from './ws-messages';
import type { Result } from './types';

export function handleWSMessage(msg: WSMessage): Result<void> {
  switch (msg.type) {
    case 'authenticate':
      return { ok: true, value: undefined };
    case 'query':
      return { ok: true, value: undefined };
    case 'command':
      return { ok: true, value: undefined };
    case 'subscribe':
      return { ok: true, value: undefined };
    case 'unsubscribe':
      return { ok: true, value: undefined };
    default:
      return { ok: false, error: new Error('Unknown message') };
  }
}
`
    );

    const analysis = await analyzeCodebase({ tsConfigPath });

    // Should extract WebSocket message types
    const expectedTypes = ["authenticate", "query", "command", "subscribe", "unsubscribe"];
    for (const msgType of expectedTypes) {
      expect(analysis.messageTypes).toContain(msgType);
    }

    // Should NOT extract Result or Option type internals
    const invalidTypes = [
      "{ ok: true; value: t }",
      "{ ok: false; error: e }",
      "{ some: t }",
      "{ none: true }",
      "ok",
      "value",
      "error",
      "some",
      "none",
      "true", // literal 'true' should not be a message type
    ];

    for (const invalid of invalidTypes) {
      expect(analysis.messageTypes).not.toContain(invalid);
    }

    // All types must be valid TLA+ identifiers
    for (const msgType of analysis.messageTypes) {
      expect(msgType).toMatch(/^[a-zA-Z][a-zA-Z0-9_]*$/);
    }
  });
});
