import { describe, test, expect, beforeEach, afterEach } from "bun:test";
import * as fs from "node:fs";
import * as path from "node:path";
import * as os from "node:os";
import { analyzeCodebase } from "../types";

describe("TLA+ Identifier Validation", () => {
	let tempDir: string;

	beforeEach(() => {
		tempDir = fs.mkdtempSync(path.join(os.tmpdir(), "polly-tla-validation-"));
	});

	afterEach(() => {
		if (fs.existsSync(tempDir)) {
			fs.rmSync(tempDir, { recursive: true });
		}
	});

	test("should filter out invalid TLA+ identifiers from message types", async () => {
		// Create a tsconfig.json
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

		// Create a test file with both valid and invalid message types
		const testFile = path.join(tempDir, "messages.ts");
		fs.writeFileSync(
			testFile,
			`
export type Result<T, E = Error> = { ok: true; value: T } | { ok: false; error: E };

export interface ValidMessage {
  type: 'query' | 'command' | 'subscribe';
}

export interface InvalidTypeDefinition {
  result: Result<string>;
}

// Handler using valid message types
export function handleMessage(msg: ValidMessage) {
  switch (msg.type) {
    case 'query':
      // Handle query
      break;
    case 'command':
      // Handle command
      break;
    case 'subscribe':
      // Handle subscribe
      break;
  }
}
`
		);

		// Analyze the codebase
		const analysis = await analyzeCodebase({
			tsConfigPath,
		});

		// Check that only valid TLA+ identifiers are in the message types
		expect(analysis.messageTypes).toBeArray();

		// Valid types should be included
		const validTypes = ['query', 'command', 'subscribe'];
		for (const validType of validTypes) {
			expect(analysis.messageTypes).toContain(validType);
		}

		// Invalid types should be filtered out
		const invalidTypes = ['{ ok: true; value: t }', '{ ok: false; error: e }'];
		for (const invalidType of invalidTypes) {
			expect(analysis.messageTypes).not.toContain(invalidType);
		}

		// All message types should be valid TLA+ identifiers
		for (const msgType of analysis.messageTypes) {
			expect(msgType).toMatch(/^[a-zA-Z][a-zA-Z0-9_]*$/);
		}
	});

	test("should accept valid TLA+ identifiers", async () => {
		// Create a tsconfig.json
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

		// Create a test file with valid message types
		const testFile = path.join(tempDir, "valid-messages.ts");
		fs.writeFileSync(
			testFile,
			`
export interface Message {
  type: 'authenticate' | 'user_login' | 'API_REQUEST' | 'event123';
}

export function handleMessage(msg: Message) {
  switch (msg.type) {
    case 'authenticate':
      break;
    case 'user_login':
      break;
    case 'API_REQUEST':
      break;
    case 'event123':
      break;
  }
}
`
		);

		// Analyze the codebase
		const analysis = await analyzeCodebase({
			tsConfigPath,
		});

		// Check that all valid types are included
		const validTypes = ['authenticate', 'user_login', 'API_REQUEST', 'event123'];
		for (const validType of validTypes) {
			expect(analysis.messageTypes).toContain(validType);
		}
	});

	test("should reject invalid TLA+ identifiers", async () => {
		// Create a tsconfig.json
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

		// Create a test file with invalid message types
		const testFile = path.join(tempDir, "invalid-messages.ts");
		fs.writeFileSync(
			testFile,
			`
// These should be filtered out:
// - Starting with digit: '123event'
// - Containing special chars: 'event-type', 'event.type', 'event:type'
// - Complex types: '{ ok: true }'

export interface Message {
  type: '123event' | 'event-type' | 'event.type' | 'event:type' | '{ ok: true }';
}

export function handleMessage(msg: Message) {
  switch (msg.type) {
    case '123event':
      break;
    case 'event-type':
      break;
    case 'event.type':
      break;
    case 'event:type':
      break;
    case '{ ok: true }':
      break;
  }
}
`
		);

		// Analyze the codebase
		const analysis = await analyzeCodebase({
			tsConfigPath,
		});

		// Check that invalid types are filtered out
		const invalidTypes = ['123event', 'event-type', 'event.type', 'event:type', '{ ok: true }'];
		for (const invalidType of invalidTypes) {
			expect(analysis.messageTypes).not.toContain(invalidType);
		}
	});
});
