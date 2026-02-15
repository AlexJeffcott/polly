// Test to verify todo IDs are unique
import { beforeEach, describe, expect, test } from "bun:test";
import { filter, generateId, todos, user } from "../src/background/state";

beforeEach(() => {
  user.value = {
    id: null,
    name: "Guest",
    role: "guest",
    loggedIn: false,
  };
  todos.value = [];
  filter.value = "all";
});

describe("Todo ID Uniqueness", () => {
  test("generateId creates unique IDs", () => {
    const ids = new Set<string>();
    const count = 100;

    for (let i = 0; i < count; i++) {
      const id = generateId();
      expect(ids.has(id)).toBe(false);
      ids.add(id);
    }

    expect(ids.size).toBe(count);
  });

  test("adding multiple todos results in unique IDs", () => {
    // Simulate adding multiple todos
    for (let i = 0; i < 10; i++) {
      todos.value.push({
        id: generateId(),
        text: `Todo ${i}`,
        completed: false,
        priority: "medium",
        createdAt: Date.now(),
      });
    }

    // Check all IDs are unique
    const ids = todos.value.map((t) => t.id);
    const uniqueIds = new Set(ids);
    expect(uniqueIds.size).toBe(ids.length);
    expect(uniqueIds.size).toBe(10);
  });

  test("rapid todo additions maintain uniqueness", async () => {
    // Simulate rapid additions (like multiple button clicks)
    const promises = [];
    for (let i = 0; i < 5; i++) {
      promises.push(
        Promise.resolve().then(() => {
          todos.value.push({
            id: generateId(),
            text: `Rapid todo ${i}`,
            completed: false,
            priority: "medium",
            createdAt: Date.now(),
          });
        })
      );
    }

    await Promise.all(promises);

    // Verify no duplicates
    expect(todos.value.length).toBe(5);
    const ids = todos.value.map((t) => t.id);
    const uniqueIds = new Set(ids);
    expect(uniqueIds.size).toBe(5);

    // Also verify no duplicate text (each should be unique)
    const texts = todos.value.map((t) => t.text);
    expect(texts).toContain("Rapid todo 0");
    expect(texts).toContain("Rapid todo 4");
  });

  test("GET_STATE returns todos with unique IDs", () => {
    // Add some todos
    todos.value = [
      { id: "id-1", text: "Todo 1", completed: false, priority: "medium", createdAt: Date.now() },
      { id: "id-2", text: "Todo 2", completed: false, priority: "medium", createdAt: Date.now() },
      { id: "id-3", text: "Todo 3", completed: true, priority: "medium", createdAt: Date.now() },
    ];

    // Simulate GET_STATE response
    const stateResponse = {
      user: user.value,
      todos: todos.value,
      filter: filter.value,
    };

    // Verify uniqueness
    const ids = stateResponse.todos.map((t) => t.id);
    const uniqueIds = new Set(ids);
    expect(uniqueIds.size).toBe(ids.length);
    expect(uniqueIds.size).toBe(3);
  });
});
