/**
 * The `polly()` plugin's lifecycle hooks must run for the CONSUMER's routes.
 * An Elysia plugin's hooks are local to the plugin instance unless it widens
 * their scope, so a hook that fires for the plugin's own `/polly/ws` route but
 * not for `.use(polly()).post("/todos")` is the exact defect pinned here.
 */
import { afterAll, beforeAll, describe, expect, test } from "bun:test";
import { Elysia } from "elysia";
import { polly } from "@/elysia/plugin";
import type { PollyResponseMetadata } from "@/elysia/types";

type Handles = { handle: (request: Request) => Promise<Response> };

function consumerApp() {
  const denied: string[] = [];
  const app = new Elysia()
    .use(
      polly({
        offline: { "POST /todos": { queue: true, merge: "replace" } },
        effects: { "POST /todos": { broadcast: true } },
        authorization: {
          "DELETE /todos/:id": ({ headers }) => {
            const ok = headers["x-role"] === "admin";
            if (!ok) denied.push("DELETE /todos/:id");
            return ok;
          },
        },
      })
    )
    .post("/todos", ({ body }) => ({ created: body }))
    .get("/todos", () => ({ items: [] }))
    .delete("/todos/:id", ({ params }) => ({ deleted: params.id }))
    .get("/raw", () => new Response("plain", { status: 201, headers: { "x-own": "kept" } }));
  return { app, denied };
}

function post(app: Handles, path: string, body: unknown, headers: Record<string, string> = {}) {
  return app.handle(
    new Request(`http://localhost${path}`, {
      method: "POST",
      headers: { "content-type": "application/json", ...headers },
      body: JSON.stringify(body),
    })
  );
}

function metadataOf(response: Response): PollyResponseMetadata | undefined {
  const header = response.headers.get("X-Polly-Metadata");
  return header ? (JSON.parse(header) as PollyResponseMetadata) : undefined;
}

describe("polly() hooks on consumer routes", () => {
  test("after-handle attaches X-Polly-Metadata with the matched effect and offline config", async () => {
    const { app } = consumerApp();

    const response = await post(app, "/todos", { text: "a" });

    expect(await response.json()).toEqual({ created: { text: "a" } });
    const metadata = metadataOf(response);
    expect(metadata?.hasClientEffect).toBe(true);
    expect(metadata?.offline).toEqual({ queue: true, merge: "replace" });
    expect(typeof metadata?.clock.tick).toBe("number");
  });

  test("a route with no config still carries metadata, with no effect and no offline entry", async () => {
    const { app } = consumerApp();

    const response = await app.handle(new Request("http://localhost/todos"));

    const metadata = metadataOf(response);
    expect(metadata?.hasClientEffect).toBe(false);
    expect(metadata?.offline).toBeUndefined();
  });

  test("the clock ticks once per handled request", async () => {
    const { app } = consumerApp();

    const first = metadataOf(await post(app, "/todos", {}))?.clock.tick;
    const second = metadataOf(await post(app, "/todos", {}))?.clock.tick;

    expect(typeof first).toBe("number");
    expect(second).toBe((first as number) + 1);
  });

  test("before-handle authorization denies the consumer's route with 403", async () => {
    const { app, denied } = consumerApp();

    const refused = await app.handle(new Request("http://localhost/todos/7", { method: "DELETE" }));
    const allowed = await app.handle(
      new Request("http://localhost/todos/7", { method: "DELETE", headers: { "x-role": "admin" } })
    );

    expect(refused.status).toBe(403);
    expect(await refused.text()).toBe("Unauthorized");
    expect(denied).toEqual(["DELETE /todos/:id"]);
    expect(await allowed.json()).toEqual({ deleted: "7" });
  });

  test("a handler's own Response keeps its status, headers and body", async () => {
    const { app } = consumerApp();

    const response = await app.handle(new Request("http://localhost/raw"));

    expect(response.status).toBe(201);
    expect(response.headers.get("x-own")).toBe("kept");
    expect(await response.text()).toBe("plain");
    expect(metadataOf(response)?.hasClientEffect).toBe(false);
  });
});

describe("polly() broadcast to connected clients", () => {
  const { app } = consumerApp();
  let base = "";

  beforeAll(() => {
    app.listen(0);
    base = `localhost:${app.server?.port}`;
  });

  afterAll(() => {
    app.stop();
  });

  test("an effect route broadcasts its result to the websocket client", async () => {
    const messages: unknown[] = [];
    const ws = new WebSocket(`ws://${base}/polly/ws`);
    ws.onmessage = (event) => messages.push(JSON.parse(String(event.data)));
    await new Promise<void>((resolve) => {
      ws.onopen = () => resolve();
    });
    // state-sync arrives on open
    await Bun.sleep(20);
    expect(messages).toHaveLength(1);
    expect((messages[0] as { type: string }).type).toBe("state-sync");

    const response = await fetch(`http://${base}/todos`, {
      method: "POST",
      headers: { "content-type": "application/json" },
      body: JSON.stringify({ text: "b" }),
    });
    expect(response.ok).toBe(true);
    await Bun.sleep(20);

    expect(messages).toHaveLength(2);
    expect(messages[1]).toMatchObject({
      type: "effect",
      path: "/todos",
      method: "POST",
      result: { created: { text: "b" } },
    });
    ws.close();
  });
});
