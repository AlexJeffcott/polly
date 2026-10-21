/**
 * Pins the polly plugin configuration: which routes queue offline, what their
 * optimistic responses return, and which routes broadcast.
 */
import { describe, expect, test } from "bun:test";
import { createApp, POLLY_CONFIG } from "../src/app";

const offline = POLLY_CONFIG.offline ?? {};
const effects = POLLY_CONFIG.effects ?? {};

describe("offline routes", () => {
  test("every mutating route queues with replace-merge", () => {
    const routes = Object.keys(offline).sort();
    expect(routes).toEqual([
      "DELETE /api/tasks/:id",
      "PATCH /api/tasks/:id",
      "POST /api/comments",
      "POST /api/tasks",
      "POST /api/workspaces",
      "POST /api/workspaces/:id/members",
    ]);
    for (const route of routes) {
      expect(offline[route]?.queue).toBe(true);
      expect(offline[route]?.merge).toBe("replace");
    }
  });

  test("workspace creation answers optimistically with the workspace", () => {
    const before = Date.now();
    const result = offline["POST /api/workspaces"]?.optimistic?.({ id: "w1", name: "Name" }) as {
      success: boolean;
      workspace: { id: string; name: string; createdAt: number };
    };
    expect(result.success).toBe(true);
    expect(result.workspace.id).toBe("w1");
    expect(result.workspace.name).toBe("Name");
    expect(result.workspace.createdAt).toBeGreaterThanOrEqual(before);
  });

  test("task creation answers optimistically with the task id", () => {
    expect(offline["POST /api/tasks"]?.optimistic?.({ id: "t1" })).toEqual({
      success: true,
      taskId: "t1",
    });
  });

  test("task deletion answers optimistically with success", () => {
    expect(offline["DELETE /api/tasks/:id"]?.optimistic?.({})).toEqual({ success: true });
  });

  test("comment creation answers optimistically with the comment id", () => {
    expect(offline["POST /api/comments"]?.optimistic?.({ id: "c1" })).toEqual({
      success: true,
      commentId: "c1",
    });
  });

  test("member add and task update have no optimistic response", () => {
    expect(offline["POST /api/workspaces/:id/members"]?.optimistic).toBeUndefined();
    expect(offline["PATCH /api/tasks/:id"]?.optimistic).toBeUndefined();
  });
});

describe("effects", () => {
  test("task and comment routes broadcast", () => {
    const routes = Object.keys(effects).sort();
    expect(routes).toEqual([
      "DELETE /api/tasks/:id",
      "PATCH /api/tasks/:id",
      "POST /api/comments",
      "POST /api/tasks",
    ]);
    for (const route of routes) expect(effects[route]?.broadcast).toBe(true);
  });

  test("the polly websocket is mounted at /polly/ws", () => {
    expect(POLLY_CONFIG.websocketPath).toBe("/polly/ws");
  });
});

describe("live metadata", () => {
  test("a queued, broadcast route reports both in X-Polly-Metadata", async () => {
    const app = createApp();
    const response = await app.handle(
      new Request("http://localhost/api/tasks", {
        method: "POST",
        headers: { "content-type": "application/json" },
        body: JSON.stringify({ id: "t1", encrypted: "x", from: "u1", workspaceId: "w1" }),
      })
    );
    const metadata = JSON.parse(response.headers.get("X-Polly-Metadata") ?? "{}");
    expect(metadata.hasClientEffect).toBe(true);
    expect(metadata.offline).toEqual({ queue: true, merge: "replace" });
  });

  test("a queued route without an effect reports no client effect", async () => {
    const app = createApp();
    const response = await app.handle(
      new Request("http://localhost/api/workspaces/w1/members", {
        method: "POST",
        headers: { "content-type": "application/json" },
        body: JSON.stringify({ userId: "u2" }),
      })
    );
    const metadata = JSON.parse(response.headers.get("X-Polly-Metadata") ?? "{}");
    expect(metadata.hasClientEffect).toBe(false);
    expect(metadata.offline).toEqual({ queue: true, merge: "replace" });
  });
});
