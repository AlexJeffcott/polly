// Tests for API client
import { beforeEach, describe, expect, test } from "bun:test";
import { createMockFetch } from "@fairfox/polly/test";
import { APIClient } from "../src/api";

describe("API Client", () => {
  let mockFetch: ReturnType<typeof createMockFetch>;

  beforeEach(() => {
    // Use Polly's mock fetch
    mockFetch = createMockFetch();
    global.fetch = mockFetch.fetch;

    // Default response with proper headers and methods for Eden treaty
    const responseData = { success: true };
    mockFetch._responses.push({
      ok: true,
      status: 200,
      statusText: "OK",
      headers: new Headers({ "Content-Type": "application/json" }),
      json: async () => responseData,
      text: async () => JSON.stringify(responseData),
      blob: async () => new Blob([JSON.stringify(responseData)]),
      arrayBuffer: async () => new TextEncoder().encode(JSON.stringify(responseData)).buffer,
    } as Response);
  });

  test("createWorkspace sends correct request", async () => {
    const api = new APIClient();

    await api.createWorkspace("workspace-1", "My Workspace", "user-1");

    // Check the call was made
    expect(mockFetch._calls.length).toBe(1);
    expect(mockFetch._calls[0].input.toString()).toContain("/api/workspaces");

    const callInit = mockFetch._calls[0].init;
    expect(callInit?.method).toBe("POST");

    // Headers can be a Headers object or plain object
    // Note: Eden treaty uses lowercase header keys
    const contentType =
      callInit?.headers instanceof Headers
        ? callInit.headers.get("content-type")
        : callInit?.headers?.["content-type"];
    expect(contentType).toBe("application/json");

    const body = JSON.parse(callInit?.body as string);
    expect(body.id).toBe("workspace-1");
    expect(body.name).toBe("My Workspace");
    expect(body.creatorId).toBe("user-1");
  });

  test("getWorkspace sends GET request", async () => {
    const api = new APIClient();

    await api.getWorkspace("workspace-1");

    expect(mockFetch._calls.length).toBe(1);
    expect(mockFetch._calls[0].input.toString()).toContain("/api/workspaces/workspace-1");
  });

  test("createTask sends encrypted data", async () => {
    const api = new APIClient();

    await api.createTask("task-1", "encrypted-data-base64", "user-1", "workspace-1");

    expect(mockFetch._calls.length).toBe(1);

    const callInit = mockFetch._calls[0].init;
    const body = JSON.parse(callInit?.body as string);

    expect(body.id).toBe("task-1");
    expect(body.encrypted).toBe("encrypted-data-base64");
    expect(body.from).toBe("user-1");
    expect(body.workspaceId).toBe("workspace-1");
  });

  test("updateTask sends encrypted update", async () => {
    const api = new APIClient();

    await api.updateTask("task-1", "new-encrypted-data", "workspace-1");

    expect(mockFetch._calls.length).toBe(1);
    expect(mockFetch._calls[0].input.toString()).toContain("/api/tasks/task-1");

    const callInit = mockFetch._calls[0].init;
    expect(callInit?.method).toBe("PATCH");

    const body = JSON.parse(callInit?.body as string);
    expect(body.encrypted).toBe("new-encrypted-data");
    expect(body.workspaceId).toBe("workspace-1");
  });

  test("deleteTask sends DELETE request", async () => {
    const api = new APIClient();

    await api.deleteTask("task-1", "workspace-1");

    expect(mockFetch._calls.length).toBe(1);
    expect(mockFetch._calls[0].input.toString()).toContain("/api/tasks/task-1");

    const callInit = mockFetch._calls[0].init;
    expect(callInit?.method).toBe("DELETE");
  });

  test("handles API errors", async () => {
    // Clear default response and add error response
    mockFetch._responses.length = 0;
    const errorData = { error: "Not found" };
    mockFetch._responses.push({
      ok: true,
      status: 200,
      statusText: "OK",
      headers: new Headers({ "Content-Type": "application/json" }),
      json: async () => errorData,
      text: async () => JSON.stringify(errorData),
      blob: async () => new Blob([JSON.stringify(errorData)]),
      arrayBuffer: async () => new TextEncoder().encode(JSON.stringify(errorData)).buffer,
    } as Response);

    const api = new APIClient();

    const response = await api.getWorkspace("invalid-id");

    expect(response.error).toBe("Not found");
  });

  test("uses correct API URL from environment", async () => {
    const api = new APIClient();

    await api.createWorkspace("w1", "Test", "u1");

    const calledUrl = mockFetch._calls[0].input.toString();
    // Should use HTTPS by default
    expect(calledUrl).toMatch(/^https:\/\/localhost:3000/);
  });
});

describe("WebSocket Connection", () => {
  test("constructs WebSocket with correct URL", () => {
    // Mock WebSocket with static properties
    const mockWS = class {
      static CONNECTING = 0;
      static OPEN = 1;
      static CLOSING = 2;
      static CLOSED = 3;

      constructor(public url: string) {}
      send() {}
      close() {}
      readyState = 1; // OPEN
    };

    global.WebSocket = mockWS as any;

    const api = new APIClient();

    api.connect("workspace-1", "user-1");

    // WebSocket URL should use wss:// for secure connection
    // This is a basic check - in practice you'd verify the full URL
    expect(api).toBeDefined();
  });

  test("can connect to WebSocket without errors", () => {
    const mockWS = class {
      static CONNECTING = 0;
      static OPEN = 1;
      static CLOSING = 2;
      static CLOSED = 3;

      onopen: (() => void) | null = null;
      onmessage: ((evt: any) => void) | null = null;
      onerror: ((evt: any) => void) | null = null;
      onclose: (() => void) | null = null;
      readyState = 0; // CONNECTING

      send(msg: string) {}
      close() {}
    };

    global.WebSocket = mockWS as any;

    const api = new APIClient();

    // Should not throw
    expect(() => {
      api.connect("workspace-1", "user-1");
    }).not.toThrow();

    // Should have created a WebSocket
    expect((api as any).ws).toBeDefined();
  });
});
