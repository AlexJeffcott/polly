/**
 * Relay tests: drive the real app (createApp, the same builder index.ts uses)
 * over a live listener on an ephemeral port, with real WebSocket clients, and
 * check every route broadcasts to exactly the workspace members it should.
 */
import { afterAll, beforeAll, describe, expect, test } from "bun:test";
import { createApp } from "../src/app";

type Json = Record<string, unknown>;

const app = createApp();
let base = "";

class Client {
  private queue: Json[] = [];
  private waiters: Array<(m: Json) => void> = [];
  private ws!: WebSocket;

  static async open(): Promise<Client> {
    const c = new Client();
    c.ws = new WebSocket(`${base.replace("http", "ws")}/ws`);
    c.ws.onmessage = (event) => {
      const message = JSON.parse(String(event.data)) as Json;
      const waiter = c.waiters.shift();
      if (waiter) waiter(message);
      else c.queue.push(message);
    };
    await new Promise<void>((resolve, reject) => {
      c.ws.onopen = () => resolve();
      c.ws.onerror = (e) => reject(e);
    });
    return c;
  }

  send(message: Json): void {
    this.ws.send(JSON.stringify(message));
  }

  next(timeoutMs = 1000): Promise<Json> {
    const queued = this.queue.shift();
    if (queued) return Promise.resolve(queued);
    return new Promise((resolve, reject) => {
      const waiter = (m: Json) => {
        clearTimeout(timer);
        resolve(m);
      };
      const timer = setTimeout(() => {
        // A timed-out waiter must not swallow the next message.
        this.waiters = this.waiters.filter((w) => w !== waiter);
        reject(new Error("no message within timeout"));
      }, timeoutMs);
      this.waiters.push(waiter);
    });
  }

  /** Resolves true when a message arrives within the window, false otherwise. */
  async received(windowMs = 150): Promise<boolean> {
    try {
      await this.next(windowMs);
      return true;
    } catch {
      return false;
    }
  }

  async join(workspaceId: string, userId: string): Promise<Json> {
    this.send({ type: "join", workspaceId, userId });
    return this.next();
  }

  close(): void {
    this.ws.close();
  }
}

async function call(method: string, path: string, body?: Json): Promise<Json> {
  const response = await fetch(`${base}${path}`, {
    method,
    headers: { "content-type": "application/json" },
    body: body ? JSON.stringify(body) : undefined,
  });
  return (await response.json()) as Json;
}

beforeAll(() => {
  app.listen(0);
  base = `http://localhost:${app.server?.port}`;
});

afterAll(() => {
  app.stop();
});

describe("workspaces", () => {
  test("POST creates and GET finds it inactive", async () => {
    const created = await call("POST", "/api/workspaces", {
      id: "ws-create",
      name: "Created",
      creatorId: "u-creator",
    });

    expect(created.success).toBe(true);
    const workspace = created.workspace as Json;
    expect(workspace.id).toBe("ws-create");
    expect(workspace.name).toBe("Created");
    expect(typeof workspace.createdAt).toBe("number");

    const found = await call("GET", "/api/workspaces/ws-create");
    expect(found.id).toBe("ws-create");
    expect(found.active).toBe(false);
    expect(typeof found.createdAt).toBe("number");
  });

  test("GET of an unknown workspace is an error", async () => {
    expect(await call("GET", "/api/workspaces/nope")).toEqual({ error: "Workspace not found" });
  });

  test("a joined workspace is active and found without a POST", async () => {
    const c = await Client.open();
    expect(await c.join("ws-joined", "u1")).toEqual({ type: "joined", workspaceId: "ws-joined" });

    const found = await call("GET", "/api/workspaces/ws-joined");
    expect(found.active).toBe(true);

    c.close();
  });

  test("POST broadcasts workspace_created to members", async () => {
    const c = await Client.open();
    await c.join("ws-bc", "u1");

    await call("POST", "/api/workspaces", { id: "ws-bc", name: "N", creatorId: "u-c" });

    const m = await c.next();
    expect(m.type).toBe("workspace_created");
    expect(m.workspaceId).toBe("ws-bc");
    expect(m.creatorId).toBe("u-c");
    expect(typeof m.timestamp).toBe("number");
    c.close();
  });
});

describe("broadcast scope", () => {
  let u1: Client;
  let u2: Client;
  let other: Client;

  beforeAll(async () => {
    u1 = await Client.open();
    u2 = await Client.open();
    other = await Client.open();
    await u1.join("w1", "u1");
    await u2.join("w1", "u2");
    await other.join("w2", "u3");
  });

  afterAll(() => {
    u1.close();
    u2.close();
    other.close();
  });

  test("member_joined reaches every member of that workspace only", async () => {
    expect(await call("POST", "/api/workspaces/w1/members", { userId: "u9" })).toEqual({
      success: true,
    });

    for (const c of [u1, u2]) {
      const m = await c.next();
      expect(m.type).toBe("member_joined");
      expect(m.userId).toBe("u9");
      expect(typeof m.timestamp).toBe("number");
    }
    expect(await other.received()).toBe(false);
  });

  test("task_created carries the encrypted task", async () => {
    const response = await call("POST", "/api/tasks", {
      id: "t1",
      encrypted: "ciphertext",
      from: "u1",
      workspaceId: "w1",
    });
    expect(response).toEqual({ success: true, taskId: "t1" });

    for (const c of [u1, u2]) {
      const m = await c.next();
      expect(m.type).toBe("task_created");
      const task = m.task as Json;
      expect(task.id).toBe("t1");
      expect(task.encrypted).toBe("ciphertext");
      expect(task.from).toBe("u1");
      expect(task.workspaceId).toBe("w1");
      expect(typeof task.timestamp).toBe("number");
    }
    expect(await other.received()).toBe(false);
  });

  test("task_updated carries the id from the path", async () => {
    expect(await call("PATCH", "/api/tasks/t1", { encrypted: "v2", workspaceId: "w1" })).toEqual({
      success: true,
    });

    for (const c of [u1, u2]) {
      const m = await c.next();
      expect(m.type).toBe("task_updated");
      const task = m.task as Json;
      expect(task.id).toBe("t1");
      expect(task.encrypted).toBe("v2");
      expect(task.workspaceId).toBe("w1");
      expect(typeof task.timestamp).toBe("number");
    }
    expect(await other.received()).toBe(false);
  });

  test("task_deleted carries the id from the path", async () => {
    expect(await call("DELETE", "/api/tasks/t1", { workspaceId: "w1" })).toEqual({
      success: true,
    });

    for (const c of [u1, u2]) {
      const m = await c.next();
      expect(m.type).toBe("task_deleted");
      expect(m.taskId).toBe("t1");
      expect(typeof m.timestamp).toBe("number");
    }
    expect(await other.received()).toBe(false);
  });

  test("comment_added carries the encrypted comment", async () => {
    const response = await call("POST", "/api/comments", {
      id: "c1",
      taskId: "t1",
      encrypted: "comment-ct",
      from: "u2",
      workspaceId: "w1",
    });
    expect(response).toEqual({ success: true, commentId: "c1" });

    for (const c of [u1, u2]) {
      const m = await c.next();
      expect(m.type).toBe("comment_added");
      const comment = m.comment as Json;
      expect(comment.id).toBe("c1");
      expect(comment.taskId).toBe("t1");
      expect(comment.encrypted).toBe("comment-ct");
      expect(comment.from).toBe("u2");
      expect(typeof comment.timestamp).toBe("number");
    }
    expect(await other.received()).toBe(false);
  });

  test("sync_request skips the requester", async () => {
    expect(await call("POST", "/api/sync/request", { workspaceId: "w1", userId: "u1" })).toEqual({
      success: true,
    });

    const m = await u2.next();
    expect(m.type).toBe("sync_request");
    expect(m.requesterId).toBe("u1");
    expect(typeof m.timestamp).toBe("number");
    expect(await u1.received()).toBe(false);
    expect(await other.received()).toBe(false);
  });

  test("sync_response is forwarded to the target user only", async () => {
    // u1 joined first, so a relay that ignores targetUserId would hit u1.
    const payload = {
      type: "sync_response",
      workspaceId: "w1",
      targetUserId: "u2",
      data: "state",
    };
    u1.send(payload);

    expect(await u2.next()).toEqual(payload);
    expect(await u1.received()).toBe(false);
    expect(await other.received()).toBe(false);
  });

  test("sync_response to a user in another workspace is dropped", async () => {
    u1.send({ type: "sync_response", workspaceId: "w2", targetUserId: "u2" });

    expect(await u2.received()).toBe(false);
    expect(await other.received()).toBe(false);
  });

  test("after leave, a member gets no more broadcasts", async () => {
    u2.send({ type: "leave" });
    await new Promise((r) => setTimeout(r, 50));

    await call("POST", "/api/workspaces/w1/members", { userId: "u10" });

    expect((await u1.next()).type).toBe("member_joined");
    expect(await u2.received()).toBe(false);
  });

  test("after close, the workspace is no longer active", async () => {
    u1.close();
    await new Promise((r) => setTimeout(r, 50));

    const found = await call("GET", "/api/workspaces/w1");
    expect(found.active).toBe(false);
    expect(found.id).toBe("w1");
  });

  test("an unparseable frame is ignored", async () => {
    const c = await Client.open();
    await c.join("w3", "u-x");
    c.send({ type: "unknown" });
    expect(await c.received()).toBe(false);
    await call("POST", "/api/workspaces/w3/members", { userId: "u11" });
    expect((await c.next()).type).toBe("member_joined");
    c.close();
  });
});
