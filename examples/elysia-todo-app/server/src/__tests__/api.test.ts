import { beforeAll, describe, expect, test } from "bun:test";
import { treaty } from "@elysiajs/eden";
import { app } from "../app";

// Eden drives the app in process (`treaty(app)` calls `app.handle`), so these
// run without a server on :3000. The app is a module singleton and bun runs a
// file's tests in order, so each block states the session it starts from.
const api = treaty(app);

describe("Authentication", () => {
  test("should login with valid credentials", async () => {
    const response = await api.auth.login.post({
      username: "demo",
    });

    expect(response.data).toBeDefined();
    expect(response.data?.user.username).toBe("demo");
    expect(response.data?.token).toBeDefined();
  });

  test("should fail login with invalid credentials", async () => {
    const response = await api.auth.login.post({
      username: "invalid",
    });

    expect(response.error).toBeDefined();
  });

  test("should logout successfully", async () => {
    const response = await api.auth.logout.post({});

    expect(response.data?.success).toBe(true);
  });
});

describe("Authorization (logged out)", () => {
  test("should reject todo creation when not logged in", async () => {
    const before = await api.todos.get();

    const response = await api.todos.post({ text: "refused" });

    expect(response.status).toBe(403);
    expect(response.error?.value).toBe("Unauthorized");
    expect(response.data).toBeNull();
    const after = await api.todos.get();
    expect(after.data).toEqual(before.data);
  });
});

describe("Todo Operations (logged in)", () => {
  beforeAll(async () => {
    const login = await api.auth.login.post({ username: "demo" });
    expect(login.status).toBe(200);
  });

  test("should get empty todos list initially", async () => {
    const response = await api.todos.get();

    expect(response.data).toEqual([]);
  });

  test("should create a new todo", async () => {
    const response = await api.todos.post({
      text: "Test todo",
    });

    expect(response.data).toBeDefined();
    expect(response.data?.text).toBe("Test todo");
    expect(response.data?.completed).toBe(false);
    expect(response.data?.id).toBeGreaterThan(0);
  });

  test("should update a todo", async () => {
    const createResponse = await api.todos.post({
      text: "Test todo",
    });
    const todoId = createResponse.data?.id;
    expect(todoId).toBeNumber();

    const updateResponse = await api.todos({ id: String(todoId) }).patch({
      completed: true,
    });

    expect(updateResponse.data?.completed).toBe(true);
  });

  test("should delete a todo", async () => {
    const createResponse = await api.todos.post({
      text: "Test todo",
    });
    const todoId = createResponse.data?.id;
    expect(todoId).toBeNumber();

    const deleteResponse = await api.todos({ id: String(todoId) }).delete();

    expect(deleteResponse.data?.success).toBe(true);
    const remaining = await api.todos.get();
    expect(remaining.data?.some((t) => t.id === todoId)).toBe(false);
  });
});
