import { afterEach, beforeEach, describe, expect, test } from "bun:test";
import * as fs from "node:fs";
import * as os from "node:os";
import * as path from "node:path";
import { HandlerExtractor } from "../handlers";

describe("HandlerExtractor - Type Guard Detection", () => {
  let tempDir: string;

  beforeEach(() => {
    tempDir = fs.mkdtempSync(path.join(os.tmpdir(), "polly-handlers-test-"));
  });

  afterEach(() => {
    if (fs.existsSync(tempDir)) {
      fs.rmSync(tempDir, { recursive: true });
    }
  });

  describe("Local type guards (same file)", () => {
    test("should detect type guards defined in the same file", () => {
      // Create test file with local type guards
      const testFile = path.join(tempDir, "local-guards.ts");
      fs.writeFileSync(
        testFile,
        `
export interface QueryMessage {
  type: 'query';
  data: string;
}

export interface CommandMessage {
  type: 'command';
  action: string;
}

export type RequestMessage = QueryMessage | CommandMessage;

// Type guard functions
export function isQueryMessage(msg: RequestMessage): msg is QueryMessage {
  return msg.type === 'query';
}

export function isCommandMessage(msg: RequestMessage): msg is CommandMessage {
  return msg.type === 'command';
}

// Handler using type guards
export function handleMessage(message: RequestMessage) {
  if (isQueryMessage(message)) {
    console.log('Handling query:', message.data);
  } else if (isCommandMessage(message)) {
    console.log('Handling command:', message.action);
  }
}
`
      );

      // Create tsconfig
      const tsconfig = path.join(tempDir, "tsconfig.json");
      fs.writeFileSync(
        tsconfig,
        JSON.stringify({
          compilerOptions: {
            target: "ES2020",
            module: "ESNext",
            moduleResolution: "bundler",
            strict: true,
          },
          include: ["*.ts"],
        })
      );

      const extractor = new HandlerExtractor(tsconfig);
      const result = extractor.extractHandlers();

      expect(result.handlers.length).toBe(2);
      expect(result.messageTypes.has("query")).toBe(true);
      expect(result.messageTypes.has("command")).toBe(true);

      const queryHandler = result.handlers.find((h) => h.messageType === "query");
      expect(queryHandler).toBeDefined();
      expect(queryHandler?.location.file).toBe(testFile);

      const commandHandler = result.handlers.find((h) => h.messageType === "command");
      expect(commandHandler).toBeDefined();
    });
  });

  describe("Imported type guards", () => {
    test("should detect type guards imported from another file", () => {
      // Create type guards file
      const guardsFile = path.join(tempDir, "guards.ts");
      fs.writeFileSync(
        guardsFile,
        `
export interface QueryMessage {
  type: 'query';
  data: string;
}

export interface CommandMessage {
  type: 'command';
  action: string;
}

export type RequestMessage = QueryMessage | CommandMessage;

export function isQueryMessage(msg: RequestMessage): msg is QueryMessage {
  return msg.type === 'query';
}

export function isCommandMessage(msg: RequestMessage): msg is CommandMessage {
  return msg.type === 'command';
}
`
      );

      // Create handler file that imports type guards
      const handlerFile = path.join(tempDir, "handler.ts");
      fs.writeFileSync(
        handlerFile,
        `
import { isQueryMessage, isCommandMessage, type RequestMessage } from './guards';

export function handleMessage(message: RequestMessage) {
  if (isQueryMessage(message)) {
    console.log('Handling query:', message.data);
  } else if (isCommandMessage(message)) {
    console.log('Handling command:', message.action);
  }
}
`
      );

      // Create tsconfig
      const tsconfig = path.join(tempDir, "tsconfig.json");
      fs.writeFileSync(
        tsconfig,
        JSON.stringify({
          compilerOptions: {
            target: "ES2020",
            module: "ESNext",
            moduleResolution: "bundler",
            strict: true,
          },
          include: ["*.ts"],
        })
      );

      const extractor = new HandlerExtractor(tsconfig);
      const result = extractor.extractHandlers();

      expect(result.handlers.length).toBe(2);
      expect(result.messageTypes.has("query")).toBe(true);
      expect(result.messageTypes.has("command")).toBe(true);

      // Handlers should be found in the handler file, not the guards file
      const queryHandler = result.handlers.find((h) => h.messageType === "query");
      expect(queryHandler).toBeDefined();
      expect(queryHandler?.location.file).toBe(handlerFile);
    });

    test("should detect type guards imported with .ts extension (Bun/Deno style)", () => {
      // Create type guards file
      const guardsFile = path.join(tempDir, "messages.ts");
      fs.writeFileSync(
        guardsFile,
        `
export interface SubscribeMessage {
  type: 'subscribe';
  channel: string;
}

export interface UnsubscribeMessage {
  type: 'unsubscribe';
  channel: string;
}

export type RequestMessage = SubscribeMessage | UnsubscribeMessage;

export function isSubscribeMessage(msg: RequestMessage): msg is SubscribeMessage {
  return msg.type === 'subscribe';
}

export function isUnsubscribeMessage(msg: RequestMessage): msg is UnsubscribeMessage {
  return msg.type === 'unsubscribe';
}
`
      );

      // Create handler file with .ts extension in import
      const handlerFile = path.join(tempDir, "server.ts");
      fs.writeFileSync(
        handlerFile,
        `
import { isSubscribeMessage, isUnsubscribeMessage, type RequestMessage } from './messages.ts';

export function handleRequest(message: RequestMessage) {
  if (isSubscribeMessage(message)) {
    console.log('Subscribing to:', message.channel);
  } else if (isUnsubscribeMessage(message)) {
    console.log('Unsubscribing from:', message.channel);
  }
}
`
      );

      // Create tsconfig
      const tsconfig = path.join(tempDir, "tsconfig.json");
      fs.writeFileSync(
        tsconfig,
        JSON.stringify({
          compilerOptions: {
            target: "ES2020",
            module: "ESNext",
            moduleResolution: "bundler",
            allowImportingTsExtensions: true,
            strict: true,
          },
          include: ["*.ts"],
        })
      );

      const extractor = new HandlerExtractor(tsconfig);
      const result = extractor.extractHandlers();

      expect(result.handlers.length).toBe(2);
      expect(result.messageTypes.has("subscribe")).toBe(true);
      expect(result.messageTypes.has("unsubscribe")).toBe(true);
    });

    test("should detect type guards imported with path aliases", () => {
      // Create directory structure
      const srcDir = path.join(tempDir, "src");
      const wsDir = path.join(srcDir, "ws");
      fs.mkdirSync(srcDir, { recursive: true });
      fs.mkdirSync(wsDir, { recursive: true });

      // Create type guards file
      const guardsFile = path.join(wsDir, "messages.ts");
      fs.writeFileSync(
        guardsFile,
        `
export interface AuthMessage {
  type: 'auth';
  token: string;
}

export interface DataMessage {
  type: 'data';
  payload: unknown;
}

export type RequestMessage = AuthMessage | DataMessage;

export function isAuthMessage(msg: RequestMessage): msg is AuthMessage {
  return msg.type === 'auth';
}

export function isDataMessage(msg: RequestMessage): msg is DataMessage {
  return msg.type === 'data';
}
`
      );

      // Create handler file using path alias
      const handlerFile = path.join(srcDir, "server.ts");
      fs.writeFileSync(
        handlerFile,
        `
import { isAuthMessage, isDataMessage, type RequestMessage } from '@ws/messages';

export function handleWebSocketMessage(message: RequestMessage) {
  if (isAuthMessage(message)) {
    console.log('Authenticating with token:', message.token);
  } else if (isDataMessage(message)) {
    console.log('Processing data:', message.payload);
  }
}
`
      );

      // Create tsconfig with path alias
      const tsconfig = path.join(tempDir, "tsconfig.json");
      fs.writeFileSync(
        tsconfig,
        JSON.stringify({
          compilerOptions: {
            target: "ES2020",
            module: "ESNext",
            moduleResolution: "bundler",
            baseUrl: ".",
            paths: {
              "@ws/*": ["./src/ws/*"],
            },
            strict: true,
          },
          include: ["src/**/*"],
        })
      );

      const extractor = new HandlerExtractor(tsconfig);
      const result = extractor.extractHandlers();

      expect(result.handlers.length).toBe(2);
      expect(result.messageTypes.has("auth")).toBe(true);
      expect(result.messageTypes.has("data")).toBe(true);
    });
  });

  describe("Type name extraction", () => {
    test("should extract message type from type name with Message suffix", () => {
      const testFile = path.join(tempDir, "extraction.ts");
      fs.writeFileSync(
        testFile,
        `
export interface QueryMessage {
  type: 'query';
}

export interface CommandMessage {
  type: 'command';
}

export interface SubscribeMessage {
  type: 'subscribe';
}

export type RequestMessage = QueryMessage | CommandMessage | SubscribeMessage;

export function isQueryMessage(msg: RequestMessage): msg is QueryMessage {
  return msg.type === 'query';
}

export function isCommandMessage(msg: RequestMessage): msg is CommandMessage {
  return msg.type === 'command';
}

export function isSubscribeMessage(msg: RequestMessage): msg is SubscribeMessage {
  return msg.type === 'subscribe';
}

export function process(message: RequestMessage) {
  if (isQueryMessage(message)) {
    console.log('query');
  } else if (isCommandMessage(message)) {
    console.log('command');
  } else if (isSubscribeMessage(message)) {
    console.log('subscribe');
  }
}
`
      );

      const tsconfig = path.join(tempDir, "tsconfig.json");
      fs.writeFileSync(
        tsconfig,
        JSON.stringify({
          compilerOptions: {
            target: "ES2020",
            module: "ESNext",
            moduleResolution: "bundler",
            strict: true,
          },
          include: ["*.ts"],
        })
      );

      const extractor = new HandlerExtractor(tsconfig);
      const result = extractor.extractHandlers();

      // Should extract "query", "command", "subscribe" (lowercase, without "Message")
      expect(result.messageTypes.has("query")).toBe(true);
      expect(result.messageTypes.has("command")).toBe(true);
      expect(result.messageTypes.has("subscribe")).toBe(true);
      expect(result.handlers.length).toBe(3);
    });
  });

  describe("Edge cases", () => {
    test("should handle else-if chains with multiple type guards", () => {
      const testFile = path.join(tempDir, "chain.ts");
      fs.writeFileSync(
        testFile,
        `
export interface CreateMessage { type: 'create'; }
export interface UpdateMessage { type: 'update'; }
export interface DeleteMessage { type: 'delete'; }
export interface ReadMessage { type: 'read'; }

export type Message = CreateMessage | UpdateMessage | DeleteMessage | ReadMessage;

function isCreateMessage(m: Message): m is CreateMessage { return m.type === 'create'; }
function isUpdateMessage(m: Message): m is UpdateMessage { return m.type === 'update'; }
function isDeleteMessage(m: Message): m is DeleteMessage { return m.type === 'delete'; }
function isReadMessage(m: Message): m is ReadMessage { return m.type === 'read'; }

function handle(m: Message) {
  if (isCreateMessage(m)) {
    console.log('create');
  } else if (isUpdateMessage(m)) {
    console.log('update');
  } else if (isDeleteMessage(m)) {
    console.log('delete');
  } else if (isReadMessage(m)) {
    console.log('read');
  }
}
`
      );

      const tsconfig = path.join(tempDir, "tsconfig.json");
      fs.writeFileSync(
        tsconfig,
        JSON.stringify({
          compilerOptions: {
            target: "ES2020",
            module: "ESNext",
            moduleResolution: "bundler",
            strict: true,
          },
          include: ["*.ts"],
        })
      );

      const extractor = new HandlerExtractor(tsconfig);
      const result = extractor.extractHandlers();

      expect(result.handlers.length).toBe(4);
      expect(result.messageTypes.has("create")).toBe(true);
      expect(result.messageTypes.has("update")).toBe(true);
      expect(result.messageTypes.has("delete")).toBe(true);
      expect(result.messageTypes.has("read")).toBe(true);
    });

    test("should not detect non-type-guard functions", () => {
      const testFile = path.join(tempDir, "non-guard.ts");
      fs.writeFileSync(
        testFile,
        `
export interface Message {
  type: string;
}

// Regular boolean function (not a type guard)
function isValid(msg: Message): boolean {
  return msg.type.length > 0;
}

function handle(msg: Message) {
  if (isValid(msg)) {
    console.log('valid');
  }
}
`
      );

      const tsconfig = path.join(tempDir, "tsconfig.json");
      fs.writeFileSync(
        tsconfig,
        JSON.stringify({
          compilerOptions: {
            target: "ES2020",
            module: "ESNext",
            moduleResolution: "bundler",
            strict: true,
          },
          include: ["*.ts"],
        })
      );

      const extractor = new HandlerExtractor(tsconfig);
      const result = extractor.extractHandlers();

      // Should not detect any handlers (isValid is not a type guard)
      expect(result.handlers.length).toBe(0);
    });
  });
});
