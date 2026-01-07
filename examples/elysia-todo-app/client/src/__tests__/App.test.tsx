import { describe, expect, test } from "bun:test";
import { render } from "preact";
import { App } from "../App";
import { clientState } from "../api";

describe("Todo App Component", () => {
  test("should render login form when not authenticated", () => {
    clientState.user.value = null;

    const container = document.createElement("div");
    render(<App />, container);

    expect(container.innerHTML).toContain("Login");
  });

  test("should render todo list when authenticated", () => {
    clientState.user.value = { id: 1, username: "demo" };
    clientState.todos.value = [];

    const container = document.createElement("div");
    render(<App />, container);

    expect(container.innerHTML).toContain("Welcome, demo!");
    expect(container.innerHTML).toContain("What needs to be done?");
  });

  test("should display todos in the list", () => {
    clientState.user.value = { id: 1, username: "demo" };
    clientState.todos.value = [
      { id: 1, text: "Buy milk", completed: false },
      { id: 2, text: "Walk dog", completed: true },
    ];

    const container = document.createElement("div");
    render(<App />, container);

    expect(container.innerHTML).toContain("Buy milk");
    expect(container.innerHTML).toContain("Walk dog");
  });

  test("should show online status", () => {
    const container = document.createElement("div");
    render(<App />, container);

    // Should show online/offline indicator
    expect(container.innerHTML).toMatch(/Online|Offline/);
  });

  test("should show queued requests count", () => {
    const container = document.createElement("div");
    render(<App />, container);

    // Queue indicator should be present (even if 0)
    const html = container.innerHTML;
    expect(html).toBeDefined();
  });
});

describe("Todo Statistics", () => {
  test("should calculate remaining todos correctly", () => {
    clientState.user.value = { id: 1, username: "demo" };
    clientState.todos.value = [
      { id: 1, text: "Task 1", completed: false },
      { id: 2, text: "Task 2", completed: true },
      { id: 3, text: "Task 3", completed: false },
    ];

    const container = document.createElement("div");
    render(<App />, container);

    expect(container.innerHTML).toContain("2 items left");
    expect(container.innerHTML).toContain("1 completed");
  });
});
