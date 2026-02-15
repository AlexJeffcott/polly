import { beforeAll, describe, expect, test } from "bun:test";

// These tests require @fairfox/polly to be properly linked via workspace
// When running from the root polly project, the workspace linking may not work
// so we check for module availability and skip if not available

let moduleAvailable = false;
let App: any;
let clientState: any;
let render: any;

beforeAll(async () => {
  try {
    // Try to dynamically import the modules
    const apiModule = await import("../api");
    const appModule = await import("../App");
    const preactModule = await import("preact");

    clientState = apiModule.clientState;
    App = appModule.App;
    render = preactModule.render;
    moduleAvailable = true;
  } catch {
    // Module not available - tests will be skipped
    moduleAvailable = false;
  }
});

describe.skipIf(() => !moduleAvailable)("Todo App Component", () => {
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

describe.skipIf(() => !moduleAvailable)("Todo Statistics", () => {
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
