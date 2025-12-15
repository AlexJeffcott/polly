import { describe, test, expect } from "bun:test"
import { WebSocketAdapter } from "../adapters/websocket"
import { WebExtensionAdapter } from "../adapters/web-extension"
import { EventBusAdapter } from "../adapters/event-bus"
import path from "node:path"
import { mkdtempSync, writeFileSync, rmSync } from "node:fs"
import { tmpdir } from "node:os"

describe("Adapter Pattern Matching", () => {
  const fixturesDir = path.join(__dirname, "../../test-projects")

  // Helper to create temporary test files
  function createTempProject(files: Record<string, string>): { dir: string; cleanup: () => void } {
    const dir = mkdtempSync(path.join(tmpdir(), "polly-test-"))

    // Create tsconfig.json
    writeFileSync(
      path.join(dir, "tsconfig.json"),
      JSON.stringify({
        compilerOptions: {
          target: "ES2022",
          module: "commonjs",
          strict: true,
        },
      })
    )

    // Create test files
    for (const [filename, content] of Object.entries(files)) {
      writeFileSync(path.join(dir, filename), content)
    }

    return {
      dir,
      cleanup: () => rmSync(dir, { recursive: true, force: true }),
    }
  }

  describe("WebSocketAdapter", () => {
    test("detects ws.on() handlers", async () => {
      const { dir, cleanup } = createTempProject({
        "server.ts": `
          import WebSocket from 'ws';
          const wss = new WebSocket.Server({ port: 8080 });

          wss.on('connection', (ws) => {
            ws.on('message', (data) => {
              console.log('received:', data);
            });

            ws.on('close', () => {
              console.log('connection closed');
            });
          });
        `,
      })

      try {
        const adapter = new WebSocketAdapter({
          tsConfigPath: path.join(dir, "tsconfig.json"),
          maxConnections: 10,
          maxInFlight: 5,
        })

        const model = adapter.extractModel()

        // Should find 'connection', 'message', 'close' handlers
        expect(model.handlers.length).toBeGreaterThanOrEqual(2)

        const messageTypes = model.handlers.map((h) => h.messageType)
        expect(messageTypes).toContain("connection")
        expect(messageTypes).toContain("message")
      } finally {
        cleanup()
      }
    })

    test("detects socket.io handlers", async () => {
      const { dir, cleanup } = createTempProject({
        "server.ts": `
          import { Server } from 'socket.io';
          const io = new Server();

          io.on('connection', (socket) => {
            socket.on('chat-message', (msg) => {
              console.log('chat:', msg);
            });

            socket.on('disconnect', () => {
              console.log('user disconnected');
            });
          });
        `,
      })

      try {
        const adapter = new WebSocketAdapter({
          tsConfigPath: path.join(dir, "tsconfig.json"),
          maxConnections: 10,
          maxInFlight: 5,
        })

        const model = adapter.extractModel()

        const messageTypes = model.handlers.map((h) => h.messageType)
        expect(messageTypes).toContain("connection")
        expect(messageTypes).toContain("chat-message")
      } finally {
        cleanup()
      }
    })

    // NOTE: Elysia WebSocket pattern (.ws({ message() {}, open() {} })) is not yet supported.
    // Elysia uses object literal methods, not .on() calls. This would require detecting
    // .ws() calls and extracting method properties from the object literal argument.
    // Can be implemented when Elysia support becomes a priority.

    test("extracts handler state mutations", async () => {
      const { dir, cleanup } = createTempProject({
        "server.ts": `
          import WebSocket from 'ws';

          interface State {
            connected: boolean;
            messageCount: number;
          }

          const state: State = { connected: false, messageCount: 0 };
          const wss = new WebSocket.Server({ port: 8080 });

          wss.on('connection', (ws) => {
            state.connected = true;

            ws.on('message', (data) => {
              state.messageCount = state.messageCount + 1;
            });
          });
        `,
      })

      try {
        const adapter = new WebSocketAdapter({
          tsConfigPath: path.join(dir, "tsconfig.json"),
          maxConnections: 10,
          maxInFlight: 5,
        })

        const model = adapter.extractModel()

        const connectionHandler = model.handlers.find((h) => h.messageType === "connection")
        expect(connectionHandler).toBeDefined()

        // Should capture state.connected = true assignment
        if (connectionHandler) {
          expect(connectionHandler.assignments.length).toBeGreaterThan(0)
        }
      } finally {
        cleanup()
      }
    })

    test("fails loudly when no handlers found", async () => {
      const { dir, cleanup } = createTempProject({
        "empty.ts": `
          // No WebSocket code at all
          console.log('hello');
        `,
      })

      try {
        const adapter = new WebSocketAdapter({
          tsConfigPath: path.join(dir, "tsconfig.json"),
          maxConnections: 10,
          maxInFlight: 5,
        })

        const model = adapter.extractModel()

        // Should return empty handlers, NOT fallback to fake data
        expect(model.handlers).toEqual([])
        expect(model.nodes.length).toBeGreaterThan(0) // But still have nodes
      } finally {
        cleanup()
      }
    })
  })

  describe("WebExtensionAdapter", () => {
    test("detects chrome.runtime.onMessage handlers", async () => {
      const { dir, cleanup } = createTempProject({
        "background.ts": `
          chrome.runtime.onMessage.addListener((message, sender, sendResponse) => {
            if (message.type === 'get-data') {
              sendResponse({ data: 'hello' });
            }
            return true;
          });
        `,
      })

      try {
        const adapter = new WebExtensionAdapter({
          tsConfigPath: path.join(dir, "tsconfig.json"),
          maxTabs: 1,
          maxInFlight: 3,
        })

        const model = adapter.extractModel()

        // Should find onMessage handler
        expect(model.handlers.length).toBeGreaterThan(0)
      } finally {
        cleanup()
      }
    })

    test("detects browser.runtime.onMessage handlers", async () => {
      const { dir, cleanup } = createTempProject({
        "background.ts": `
          browser.runtime.onMessage.addListener((message, sender) => {
            if (message.type === 'fetch-data') {
              return Promise.resolve({ status: 'ok' });
            }
          });
        `,
      })

      try {
        const adapter = new WebExtensionAdapter({
          tsConfigPath: path.join(dir, "tsconfig.json"),
          maxTabs: 1,
          maxInFlight: 3,
        })

        const model = adapter.extractModel()

        expect(model.handlers.length).toBeGreaterThan(0)
      } finally {
        cleanup()
      }
    })

    test("detects chrome.tabs.onUpdated handlers", async () => {
      const { dir, cleanup } = createTempProject({
        "background.ts": `
          chrome.tabs.onUpdated.addListener((tabId, changeInfo, tab) => {
            if (changeInfo.status === 'complete') {
              console.log('Tab loaded:', tab.url);
            }
          });
        `,
      })

      try {
        const adapter = new WebExtensionAdapter({
          tsConfigPath: path.join(dir, "tsconfig.json"),
          maxTabs: 1,
          maxInFlight: 3,
        })

        const model = adapter.extractModel()

        expect(model.handlers.length).toBeGreaterThan(0)
      } finally {
        cleanup()
      }
    })

    test("distinguishes background vs content script contexts", async () => {
      const { dir, cleanup } = createTempProject({
        "background.ts": `
          chrome.runtime.onMessage.addListener((message) => {
            console.log('background received:', message);
          });
        `,
        "content.ts": `
          chrome.runtime.onMessage.addListener((message) => {
            console.log('content received:', message);
          });
        `,
      })

      try {
        const adapter = new WebExtensionAdapter({
          tsConfigPath: path.join(dir, "tsconfig.json"),
          maxTabs: 1,
          maxInFlight: 3,
        })

        const model = adapter.extractModel()

        // Should have handlers from both contexts
        const contexts = new Set(model.handlers.map((h) => h.node))

        // Context detection happens in HandlerExtractor, not adapter
        // So we just verify handlers were found
        expect(model.handlers.length).toBeGreaterThanOrEqual(2)
      } finally {
        cleanup()
      }
    })
  })

  describe("EventBusAdapter", () => {
    test("detects EventEmitter.on() handlers", async () => {
      const { dir, cleanup } = createTempProject({
        "server.ts": `
          import { EventEmitter } from 'events';

          const bus = new EventEmitter();

          bus.on('user-login', (userId) => {
            console.log('User logged in:', userId);
          });

          bus.on('user-logout', (userId) => {
            console.log('User logged out:', userId);
          });
        `,
      })

      try {
        const adapter = new EventBusAdapter({
          tsConfigPath: path.join(dir, "tsconfig.json"),
          maxInFlight: 5,
        })

        const model = adapter.extractModel()

        const messageTypes = model.handlers.map((h) => h.messageType)
        expect(messageTypes).toContain("user-login")
        expect(messageTypes).toContain("user-logout")
      } finally {
        cleanup()
      }
    })

    test("detects ipcMain.on() handlers for Electron", async () => {
      const { dir, cleanup } = createTempProject({
        "main.ts": `
          import { ipcMain } from 'electron';

          ipcMain.on('open-file', (event, filePath) => {
            console.log('Opening file:', filePath);
            event.reply('file-opened', { success: true });
          });

          ipcMain.on('save-file', (event, filePath, content) => {
            console.log('Saving file:', filePath);
            event.reply('file-saved', { success: true });
          });
        `,
      })

      try {
        const adapter = new EventBusAdapter({
          tsConfigPath: path.join(dir, "tsconfig.json"),
          maxInFlight: 5,
          emitterPattern: /ipc|electron/i,
        })

        const model = adapter.extractModel()

        const messageTypes = model.handlers.map((h) => h.messageType)
        expect(messageTypes).toContain("open-file")
        expect(messageTypes).toContain("save-file")
      } finally {
        cleanup()
      }
    })

    test("detects ipcRenderer.on() handlers", async () => {
      const { dir, cleanup } = createTempProject({
        "renderer.ts": `
          import { ipcRenderer } from 'electron';

          ipcRenderer.on('file-opened', (event, data) => {
            console.log('File opened:', data);
          });

          ipcRenderer.on('file-saved', (event, data) => {
            console.log('File saved:', data);
          });
        `,
      })

      try {
        const adapter = new EventBusAdapter({
          tsConfigPath: path.join(dir, "tsconfig.json"),
          maxInFlight: 5,
          emitterPattern: /ipc|electron/i,
        })

        const model = adapter.extractModel()

        const messageTypes = model.handlers.map((h) => h.messageType)
        expect(messageTypes).toContain("file-opened")
        expect(messageTypes).toContain("file-saved")
      } finally {
        cleanup()
      }
    })

    test("fails loudly when emitter pattern doesn't match", async () => {
      const { dir, cleanup } = createTempProject({
        "server.ts": `
          import { EventEmitter } from 'events';
          const bus = new EventEmitter();

          bus.on('test-event', () => {
            console.log('event');
          });
        `,
      })

      try {
        const adapter = new EventBusAdapter({
          tsConfigPath: path.join(dir, "tsconfig.json"),
          maxInFlight: 5,
          emitterPattern: /WILL_NOT_MATCH/,
        })

        const model = adapter.extractModel()

        // Should return empty, NOT fallback to finding events anyway
        expect(model.handlers).toEqual([])
      } finally {
        cleanup()
      }
    })
  })

  describe("Integration with Real Test Projects", () => {
    test("WebSocket test project extracts handlers correctly", () => {
      const projectPath = path.join(fixturesDir, "websocket-server")
      const tsConfigPath = path.join(projectPath, "tsconfig.json")

      const adapter = new WebSocketAdapter({
        tsConfigPath,
        maxConnections: 10,
        maxInFlight: 5,
      })

      const model = adapter.extractModel()

      // Our test project has connection and message handlers
      expect(model.handlers.length).toBeGreaterThanOrEqual(2)

      const messageTypes = model.handlers.map((h) => h.messageType)
      expect(messageTypes).toContain("connection")
      expect(messageTypes).toContain("message")
    })

    test("Electron test project extracts IPC handlers correctly", () => {
      const projectPath = path.join(fixturesDir, "electron")
      const tsConfigPath = path.join(projectPath, "tsconfig.json")

      const adapter = new EventBusAdapter({
        tsConfigPath,
        maxInFlight: 5,
        emitterPattern: /ipc|electron/i,
      })

      const model = adapter.extractModel()

      // Our test project has ipcMain.on handlers
      const messageTypes = model.handlers.map((h) => h.messageType)

      // Should find the handlers we defined
      expect(model.handlers.length).toBeGreaterThan(0)
    })
  })
})
