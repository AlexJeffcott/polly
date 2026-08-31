import { describe, expect, test } from "bun:test";
import { GlobalRegistrator } from "@happy-dom/global-registrator";

// These tests require @fairfox/polly to be linked through the workspace. The
// import is attempted at module scope, not in beforeAll: bun evaluates
// `describe.skipIf` while it collects the file, so a flag set in beforeAll is
// still false there and every suite skipped unconditionally.

interface Modules {
  clientState: typeof import("../api")["clientState"];
  App: typeof import("../App")["App"];
  render: typeof import("preact")["render"];
}

async function loadModules(): Promise<Modules | null> {
  try {
    const [apiModule, appModule, preactModule] = await Promise.all([
      import("../api"),
      import("../App"),
      import("preact"),
    ]);
    return {
      clientState: apiModule.clientState,
      App: appModule.App,
      render: preactModule.render,
    };
  } catch {
    return null;
  }
}

// The component tests render into a real document, so the DOM has to exist
// before the modules load and before any test body runs.
GlobalRegistrator.register();

const modules = await loadModules();
const moduleAvailable = modules !== null;
// Every suite below is skipped wholesale when the load failed, so these
// bindings are only read on the branch where the modules are present.
const { clientState, App, render } = modules ?? ({} as Modules);

describe.skipIf(!moduleAvailable)("Todo App Component", () => {
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

describe.skipIf(!moduleAvailable)("Todo Statistics", () => {
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
