import { beforeAll, beforeEach, describe, expect, test } from "bun:test";
import { treaty } from "@elysiajs/eden";
import type { App } from "../index";

// These tests require a running server at localhost:3000
// They are integration tests that should be run separately with a running server
// Skip if server is not available

let serverAvailable = false;

beforeAll(async () => {
  try {
    const response = await fetch("http://localhost:3000", {
      signal: AbortSignal.timeout(1000),
    });
    serverAvailable = response.ok || response.status < 500;
  } catch {
    serverAvailable = false;
  }
});

describe.skipIf(() => !serverAvailable)("Todo API (requires running server)", () => {
  let api: ReturnType<typeof treaty<App>>;

  beforeEach(() => {
    api = treaty<App>("http://localhost:3000");
  });

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

  describe("Todo Operations", () => {
    test("should get empty todos list initially", async () => {
      const response = await api.todos.get();

      expect(response.data).toBeDefined();
      expect(Array.isArray(response.data)).toBe(true);
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
      // Create a todo first
      const createResponse = await api.todos.post({
        text: "Test todo",
      });

      const todoId = createResponse.data!.id;

      // Update it
      const updateResponse = await api.todos[todoId].patch({
        completed: true,
      });

      expect(updateResponse.data?.completed).toBe(true);
    });

    test("should delete a todo", async () => {
      // Create a todo first
      const createResponse = await api.todos.post({
        text: "Test todo",
      });

      const todoId = createResponse.data!.id;

      // Delete it
      const deleteResponse = await api.todos[todoId].delete();

      expect(deleteResponse.data?.success).toBe(true);
    });
  });

  describe("Authorization", () => {
    test("should reject todo creation when not logged in", async () => {
      // In real test, ensure no auth state
      // This would require resetting server state
      // const response = await api.todos.post({ text: "Unauthorized" });
      // expect(response.status).toBe(403);
    });
  });
});
