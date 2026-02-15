import { afterEach, beforeEach, describe, expect, test } from "bun:test";
import * as fs from "node:fs";
import * as os from "node:os";
import * as path from "node:path";
import { HandlerExtractor } from "../handlers";

describe("Elysia .ws() Handler Extraction", () => {
  let tempDir: string;

  beforeEach(() => {
    tempDir = fs.mkdtempSync(path.join(os.tmpdir(), "polly-elysia-ws-"));
  });

  afterEach(() => {
    if (fs.existsSync(tempDir)) {
      fs.rmSync(tempDir, { recursive: true });
    }
  });

  function setupProject(serverCode: string) {
    fs.writeFileSync(
      path.join(tempDir, "package.json"),
      JSON.stringify({ name: "test", version: "1.0.0" })
    );

    fs.writeFileSync(
      path.join(tempDir, "tsconfig.json"),
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

    fs.writeFileSync(path.join(tempDir, "server.ts"), serverCode);
  }

  test("extracts type guard handlers from .ws() message callback", () => {
    setupProject(`
import { Elysia } from 'elysia';

const app = new Elysia()
  .ws('/ws', {
    message(ws, data: any) {
      if (data.type === 'subscribe') {
        // handle subscribe
      } else if (data.type === 'unsubscribe') {
        // handle unsubscribe
      }
    }
  });
`);

    const extractor = new HandlerExtractor(path.join(tempDir, "tsconfig.json"));
    const { handlers } = extractor.extractHandlers();

    const messageTypes = handlers.map((h) => h.messageType);
    expect(messageTypes).toContain("subscribe");
    expect(messageTypes).toContain("unsubscribe");
  });

  test("extracts open and close lifecycle handlers", () => {
    setupProject(`
import { Elysia } from 'elysia';

const app = new Elysia()
  .ws('/chat', {
    open(ws) {
      console.log('connected');
    },
    message(ws, data: any) {
      ws.send(data);
    },
    close(ws) {
      console.log('disconnected');
    }
  });
`);

    const extractor = new HandlerExtractor(path.join(tempDir, "tsconfig.json"));
    const { handlers } = extractor.extractHandlers();

    const messageTypes = handlers.map((h) => h.messageType);
    expect(messageTypes).toContain("ws_open");
    expect(messageTypes).toContain("ws_message");
    expect(messageTypes).toContain("ws_close");
  });

  test("extracts from arrow function style callbacks", () => {
    setupProject(`
import { Elysia } from 'elysia';

const app = new Elysia()
  .ws('/ws', {
    message: (ws: any, data: any) => {
      if (data.type === 'ping') {
        ws.send({ type: 'pong' });
      }
    },
    open: (ws: any) => {
      console.log('open');
    }
  });
`);

    const extractor = new HandlerExtractor(path.join(tempDir, "tsconfig.json"));
    const { handlers } = extractor.extractHandlers();

    const messageTypes = handlers.map((h) => h.messageType);
    expect(messageTypes).toContain("ping");
    expect(messageTypes).toContain("ws_open");
  });
});

describe("REST Route Handler Extraction", () => {
  let tempDir: string;

  beforeEach(() => {
    tempDir = fs.mkdtempSync(path.join(os.tmpdir(), "polly-rest-"));
  });

  afterEach(() => {
    if (fs.existsSync(tempDir)) {
      fs.rmSync(tempDir, { recursive: true });
    }
  });

  function setupProject(serverCode: string) {
    fs.writeFileSync(
      path.join(tempDir, "package.json"),
      JSON.stringify({ name: "test", version: "1.0.0" })
    );

    fs.writeFileSync(
      path.join(tempDir, "tsconfig.json"),
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

    fs.writeFileSync(path.join(tempDir, "server.ts"), serverCode);
  }

  test("extracts Elysia REST handlers", () => {
    setupProject(`
import { Elysia } from 'elysia';

const app = new Elysia()
  .get('/todos', () => {
    return [];
  })
  .post('/todos', ({ body }: any) => {
    return { id: 1, ...body };
  })
  .delete('/todos/:id', ({ params }: any) => {
    return { deleted: true };
  });
`);

    const extractor = new HandlerExtractor(path.join(tempDir, "tsconfig.json"));
    const { handlers } = extractor.extractHandlers();

    const restHandlers = handlers.filter((h) => h.handlerKind === "rest");
    expect(restHandlers.length).toBe(3);

    const messageTypes = restHandlers.map((h) => h.messageType);
    expect(messageTypes).toContain("GET /todos");
    expect(messageTypes).toContain("POST /todos");
    expect(messageTypes).toContain("DELETE /todos/:id");

    const getHandler = restHandlers.find((h) => h.messageType === "GET /todos");
    expect(getHandler?.httpMethod).toBe("GET");
    expect(getHandler?.routePath).toBe("/todos");
  });

  test("ignores .get() on non-framework objects", () => {
    setupProject(`
// No elysia import — plain object
const map = new Map<string, number>();
map.get('key');
map.delete('key');

const arr = [1, 2, 3];
const val = arr.pop();
`);

    const extractor = new HandlerExtractor(path.join(tempDir, "tsconfig.json"));
    const { handlers } = extractor.extractHandlers();

    const restHandlers = handlers.filter((h) => h.handlerKind === "rest");
    expect(restHandlers.length).toBe(0);
  });
});
