/**
 * The `polly()` plugin's lifecycle hooks must run for the CONSUMER's routes.
 * An Elysia plugin's hooks are local to the plugin instance unless it widens
 * their scope, so a hook that fires for the plugin's own `/polly/ws` route but
 * not for `.use(polly()).post("/todos")` is the exact defect pinned here.
 */
import { afterAll, afterEach, beforeAll, describe, expect, test } from "bun:test";
import type { Treaty } from "@elysiajs/eden";
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

/**
 * The hooks are scoped to the consumer, so Elysia folds their return types
 * into every consumer route's response map. These assertions are checked by
 * `bun run typecheck` (the tests workspace): a hook that returns a bare
 * `Response` puts it under 200, and every Eden `data` becomes `T | Response`.
 */
type ConsumerApp = ReturnType<typeof consumerApp>["app"];
type EdenResult<F extends (...args: never[]) => unknown> = Awaited<ReturnType<F>>;
type PostTodos = EdenResult<Treaty.Create<ConsumerApp>["todos"]["post"]>;
type DeleteTodo = EdenResult<ReturnType<Treaty.Create<ConsumerApp>["todos"]>["delete"]>;
type Equal<A, B> =
  (<T>() => T extends A ? 1 : 2) extends <T>() => T extends B ? 1 : 2 ? true : false;

describe("polly() hook types on consumer routes", () => {
  test("Eden data is the handler's own result, with no Response folded in", () => {
    const postData: Equal<NonNullable<PostTodos["data"]>, { created: unknown }> = true;
    const deleteData: Equal<NonNullable<DeleteTodo["data"]>, { deleted: string }> = true;
    expect([postData, deleteData]).toEqual([true, true]);
  });

  test("the authorization 403 is typed as an Eden error, not as data", () => {
    const forbidden: Equal<
      Extract<NonNullable<DeleteTodo["error"]>, { status: 403 }>["value"],
      "Unauthorized"
    > = true;
    expect(forbidden).toBe(true);
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

type Received = { type: string; result?: unknown };

/**
 * Per-client broadcast filtering. A client reports its state over the socket
 * (`state-update`), keyed by its `x-client-id`; `broadcastFilter` decides from
 * that state whether the client receives an effect. Closing the socket must
 * drop the stored state, or a reconnecting client inherits whatever it
 * reported last time.
 */
describe("polly() broadcastFilter and connection lifecycle", () => {
  const app = new Elysia()
    .use(
      polly({
        effects: {
          "POST /alerts": {
            broadcast: true,
            broadcastFilter: (state) => (state as Record<string, unknown>).role === "admin",
          },
          // Unfiltered: every open client receives it. A socket delivers in
          // order, so once a client has seen a ping it has seen every effect
          // broadcast before it — the barrier the negative assertions need.
          "POST /pings": { broadcast: true },
        },
      })
    )
    .post("/alerts", ({ body }) => ({ alert: body }))
    .post("/pings", ({ body }) => ({ ping: body }));
  let base = "";
  let pingSeq = 0;
  const sockets: Array<{ ws: WebSocket; messages: Received[] }> = [];

  beforeAll(() => {
    app.listen(0);
    base = `localhost:${app.server?.port}`;
  });

  afterEach(() => {
    for (const { ws } of sockets.splice(0)) ws.close();
  });

  afterAll(() => {
    app.stop();
  });

  async function waitFor(predicate: () => boolean, label: string, timeoutMs = 2000) {
    const deadline = Date.now() + timeoutMs;
    while (!predicate()) {
      if (Date.now() > deadline) throw new Error(`timed out waiting for ${label}`);
      await new Promise<void>((resolve) => setTimeout(() => resolve(), 5));
    }
  }

  async function connect(clientId: string) {
    const client = {
      ws: new WebSocket(`ws://${base}/polly/ws`, { headers: { "x-client-id": clientId } }),
      messages: [] as Received[],
    };
    sockets.push(client);
    client.ws.onmessage = (event) => client.messages.push(JSON.parse(String(event.data)));
    await waitFor(
      () => client.messages.some((m) => m.type === "state-sync"),
      `${clientId} state-sync`
    );
    return client;
  }

  function sendState(ws: WebSocket, type: string, state: Record<string, unknown>) {
    ws.send(JSON.stringify({ type, state }));
  }

  // A client's own frames reach the server on its socket; the HTTP request
  // that triggers a broadcast does not, so there is no ordering between them
  // to wait on. Give the server a beat to read the frame.
  const letServerRead = () => Bun.sleep(20);

  function closeAndWait(ws: WebSocket) {
    return new Promise<void>((resolve) => {
      ws.onclose = () => resolve();
      ws.close();
    });
  }

  async function post(path: string, body: unknown) {
    const response = await fetch(`http://${base}${path}`, {
      method: "POST",
      headers: { "content-type": "application/json" },
      body: JSON.stringify(body),
    });
    expect(response.ok).toBe(true);
  }

  /** Post an alert, then wait until every open client has seen the ping after it. */
  async function postAlertAndDrain(text: string) {
    await post("/alerts", { text });
    const seq = ++pingSeq;
    await post("/pings", { seq });
    const open = sockets.filter(({ ws }) => ws.readyState === WebSocket.OPEN);
    await waitFor(
      () =>
        open.every(({ messages }) =>
          messages.some((m) => (m.result as { ping?: { seq: number } })?.ping?.seq === seq)
        ),
      `ping ${seq}`
    );
  }

  const alerts = (messages: Received[]) =>
    messages
      .filter((m) => m.type === "effect" && (m.result as { alert?: unknown }).alert)
      .map((m) => m.result);

  test("only clients whose reported state passes the filter receive the effect", async () => {
    const admin = await connect("filter-admin");
    const viewer = await connect("filter-viewer");
    const silent = await connect("filter-silent");
    sendState(admin.ws, "state-update", { role: "admin" });
    sendState(viewer.ws, "state-update", { role: "viewer" });
    await letServerRead();

    await postAlertAndDrain("x");

    expect(alerts(admin.messages)).toEqual([{ alert: { text: "x" } }]);
    expect(alerts(viewer.messages)).toEqual([]);
    // Never reported state: the filter sees `{}` and rejects it.
    expect(alerts(silent.messages)).toEqual([]);
  });

  test("a later state-update replaces the earlier one", async () => {
    const client = await connect("filter-demoted");
    sendState(client.ws, "state-update", { role: "admin" });
    await letServerRead();
    await postAlertAndDrain("as-admin");

    sendState(client.ws, "state-update", { role: "viewer" });
    await letServerRead();
    await postAlertAndDrain("as-viewer");

    expect(alerts(client.messages)).toEqual([{ alert: { text: "as-admin" } }]);
  });

  test("a message that is not a state-update leaves the stored state alone", async () => {
    const client = await connect("filter-noise");
    sendState(client.ws, "state-update", { role: "admin" });
    sendState(client.ws, "presence", { role: "viewer" });
    await letServerRead();

    await postAlertAndDrain("z");

    expect(alerts(client.messages)).toEqual([{ alert: { text: "z" } }]);
  });

  test("closing drops the stored state, so a reconnect under the same id is filtered afresh", async () => {
    const first = await connect("filter-reconnect");
    sendState(first.ws, "state-update", { role: "admin" });
    await letServerRead();
    await postAlertAndDrain("before-close");
    expect(alerts(first.messages)).toEqual([{ alert: { text: "before-close" } }]);
    await closeAndWait(first.ws);

    const second = await connect("filter-reconnect");
    await postAlertAndDrain("after-reconnect");

    expect(alerts(second.messages)).toEqual([]);
  });
});
