import { afterEach, beforeEach, describe, expect, test } from "bun:test";
import * as fs from "node:fs";
import * as os from "node:os";
import * as path from "node:path";
import { analyzeCodebase } from "../types";

/**
 * Regression test for issue #11: Handlers with invalid TLA+ message types
 * should be filtered from the analysis results.
 *
 * The bug was that even though messageTypes were correctly filtered,
 * handlers with invalid message types (like "{ ok: true; value: t }")
 * were still included in the handlers array, causing TLA+ generation to fail.
 */
describe("Bug #11: Handler Filtering", () => {
  let tempDir: string;

  beforeEach(() => {
    tempDir = fs.mkdtempSync(path.join(os.tmpdir(), "polly-handler-filter-"));
  });

  afterEach(() => {
    if (fs.existsSync(tempDir)) {
      fs.rmSync(tempDir, { recursive: true });
    }
  });

  test("should filter handlers with invalid TLA+ message types", async () => {
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

    // Create types file with Result type
    const typesFile = path.join(tempDir, "types.ts");
    fs.writeFileSync(
      typesFile,
      `
export type Result<T, E = Error> =
  | { ok: true; value: T }
  | { ok: false; error: E };
`
    );

    // Create handlers file with switch-case pattern (recognized by extractor)
    const handlersFile = path.join(tempDir, "handlers.ts");
    fs.writeFileSync(
      handlersFile,
      `
import type { Result } from './types';

type Message = { type: 'query' } | { type: 'command' } | { type: '{ ok: true; value: t }' };

// Switch case pattern - extractor will find these
export function routeMessage(msg: Message) {
  switch (msg.type) {
    case 'query':
      console.log('query');
      break;
    case 'command':
      console.log('command');
      break;
    case '{ ok: true; value: t }':  // Invalid TLA+ identifier!
      console.log('invalid');
      break;
  }
}
`
    );

    const analysis = await analyzeCodebase({ tsConfigPath });

    // messageTypes should only contain valid types
    expect(analysis.messageTypes).toContain("query");
    expect(analysis.messageTypes).toContain("command");
    expect(analysis.messageTypes).not.toContain("{ ok: true; value: t }");
    expect(analysis.messageTypes).not.toContain("ok");

    // **CRITICAL**: handlers array should also be filtered!
    // This is what the bug was about - handlers with invalid message types
    // were not filtered even though messageTypes was filtered
    for (const handler of analysis.handlers) {
      // Every handler should have a valid TLA+ identifier as messageType
      expect(handler.messageType).toMatch(
        /^[a-zA-Z][a-zA-Z0-9_]*$/,
        `Handler at ${handler.location.file}:${handler.location.line} has invalid messageType: "${handler.messageType}"`
      );
    }

    // Verify we have the expected valid handlers
    const handlerTypes = analysis.handlers.map((h) => h.messageType);
    expect(handlerTypes).toContain("query");
    expect(handlerTypes).toContain("command");

    // Verify invalid handlers are NOT present
    expect(handlerTypes).not.toContain("{ ok: true; value: t }");
    expect(handlerTypes).not.toContain("ok");
    expect(handlerTypes).not.toContain("value");
  });

  test("should handle switch cases with complex type checks", async () => {
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

    const handlersFile = path.join(tempDir, "router.ts");
    fs.writeFileSync(
      handlersFile,
      `
type Message = { type: 'query' } | { type: 'command' };
type Result<T> = { ok: true; value: T } | { ok: false; error: Error };

export function routeMessage(msg: Message) {
  switch (msg.type) {
    case 'query':
      return handleQuery();
    case 'command':
      return handleCommand();
  }
}

function handleQuery(): Result<string> {
  return { ok: true, value: "data" };
}

function handleCommand(): Result<void> {
  return { ok: true, value: undefined };
}
`
    );

    const analysis = await analyzeCodebase({ tsConfigPath });

    // Should extract handlers for query and command
    const handlerTypes = analysis.handlers.map((h) => h.messageType);
    expect(handlerTypes).toContain("query");
    expect(handlerTypes).toContain("command");

    // Should NOT extract handlers for Result type internals
    expect(handlerTypes).not.toContain("ok");
    expect(handlerTypes).not.toContain("value");
    expect(handlerTypes).not.toContain("error");

    // All handlers must have valid TLA+ identifiers
    for (const handler of analysis.handlers) {
      expect(handler.messageType).toMatch(/^[a-zA-Z][a-zA-Z0-9_]*$/);
    }
  });

  test("should filter handlers extracted via .on() with invalid types", async () => {
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

    const handlersFile = path.join(tempDir, "listeners.ts");
    fs.writeFileSync(
      handlersFile,
      `
interface EventEmitter {
  on(event: string, handler: (data: any) => void): void;
}

declare const emitter: EventEmitter;

// Valid handlers
emitter.on('authenticate', (data) => {
  console.log('auth:', data);
});

emitter.on('query', (data) => {
  console.log('query:', data);
});

// Invalid handler (contains special characters)
emitter.on('user:login', (data) => {
  console.log('login:', data);
});

// Invalid handler (object literal syntax)
emitter.on('{ type: error }', (data) => {
  console.log('error:', data);
});
`
    );

    const analysis = await analyzeCodebase({ tsConfigPath });

    // Should only include handlers with valid TLA+ identifiers
    const handlerTypes = analysis.handlers.map((h) => h.messageType);
    expect(handlerTypes).toContain("authenticate");
    expect(handlerTypes).toContain("query");

    // Should NOT include handlers with invalid identifiers
    expect(handlerTypes).not.toContain("user:login");
    expect(handlerTypes).not.toContain("{ type: error }");

    // All handlers must be valid
    for (const handler of analysis.handlers) {
      expect(handler.messageType).toMatch(/^[a-zA-Z][a-zA-Z0-9_]*$/);
    }
  });
});
