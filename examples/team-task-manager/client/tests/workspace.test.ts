// Tests for workspace and user management
import { beforeEach, describe, expect, test } from "bun:test";
import { bytesToHex } from "../src/crypto";
import { currentUser, resetState, tasks, workspace } from "../src/state";

// Mock crypto.randomUUID
const originalRandomUUID = crypto.randomUUID;
let mockUUIDCounter = 0;

beforeEach(() => {
  // Reset state before each test
  resetState();
  mockUUIDCounter = 0;

  // Mock crypto.randomUUID for predictable IDs
  global.crypto.randomUUID = () => `test-uuid-${++mockUUIDCounter}`;
});

describe("User Management", () => {
  test("initial state has no user", () => {
    expect(currentUser.value).toBeNull();
  });

  test("can create user with name", () => {
    const mockKeypair = {
      publicKey: new Uint8Array([1, 2, 3, 4]),
      privateKey: new Uint8Array([5, 6, 7, 8]),
    };

    currentUser.value = {
      id: bytesToHex(mockKeypair.publicKey),
      name: "Alice",
      publicKey: mockKeypair.publicKey,
      privateKey: mockKeypair.privateKey,
    };

    expect(currentUser.value).not.toBeNull();
    expect(currentUser.value?.name).toBe("Alice");
    expect(currentUser.value?.id).toBe("01020304");
  });

  test("user ID is derived from public key", () => {
    const publicKey = new Uint8Array([0xab, 0xcd, 0xef]);
    const expectedId = "abcdef";

    currentUser.value = {
      id: bytesToHex(publicKey),
      name: "Bob",
      publicKey: publicKey,
      privateKey: new Uint8Array([1, 2, 3]),
    };

    expect(currentUser.value?.id).toBe(expectedId);
  });

  test("resetState clears user", () => {
    currentUser.value = {
      id: "test-id",
      name: "Test User",
      publicKey: new Uint8Array([1]),
      privateKey: new Uint8Array([2]),
    };

    resetState();

    expect(currentUser.value).toBeNull();
  });
});

describe("Workspace Management", () => {
  test("initial state has no workspace", () => {
    expect(workspace.value).toBeNull();
  });

  test("can create workspace", () => {
    const workspaceKey = crypto.getRandomValues(new Uint8Array(32));

    workspace.value = {
      id: "workspace-123",
      name: "Team Tasks",
      workspaceKey,
      maxUrgentTasks: 3,
      createdAt: Date.now(),
    };

    expect(workspace.value).not.toBeNull();
    expect(workspace.value?.name).toBe("Team Tasks");
    expect(workspace.value?.maxUrgentTasks).toBe(3);
  });

  test("workspace has encryption key", () => {
    const workspaceKey = crypto.getRandomValues(new Uint8Array(32));

    workspace.value = {
      id: "workspace-123",
      name: "Test",
      workspaceKey,
      maxUrgentTasks: 3,
      createdAt: Date.now(),
    };

    expect(workspace.value?.workspaceKey).toBeInstanceOf(Uint8Array);
    expect(workspace.value?.workspaceKey.length).toBe(32);
  });

  test("resetState clears workspace", () => {
    workspace.value = {
      id: "test",
      name: "Test",
      workspaceKey: new Uint8Array(32),
      maxUrgentTasks: 3,
      createdAt: Date.now(),
    };

    resetState();

    expect(workspace.value).toBeNull();
  });
});

describe("Task State Management", () => {
  test("initial state has no tasks", () => {
    expect(tasks.value).toEqual([]);
  });

  test("can add task", () => {
    const task = {
      id: "task-1",
      text: "Buy milk",
      description: "",
      priority: "medium" as const,
      status: "todo" as const,
      createdBy: "user-1",
      createdAt: Date.now(),
    };

    tasks.value = [task];

    expect(tasks.value.length).toBe(1);
    expect(tasks.value[0]).toEqual(task);
  });

  test("can update task immutably", () => {
    const task = {
      id: "task-1",
      text: "Buy milk",
      description: "",
      priority: "medium" as const,
      status: "todo" as const,
      createdBy: "user-1",
      createdAt: Date.now(),
    };

    tasks.value = [task];

    // Update immutably
    tasks.value = tasks.value.map((t) =>
      t.id === "task-1" ? { ...t, status: "done" as const } : t
    );

    expect(tasks.value[0]?.status).toBe("done");
  });

  test("can delete task", () => {
    const task1 = {
      id: "task-1",
      text: "Task 1",
      description: "",
      priority: "medium" as const,
      status: "todo" as const,
      createdBy: "user-1",
      createdAt: Date.now(),
    };
    const task2 = {
      id: "task-2",
      text: "Task 2",
      description: "",
      priority: "low" as const,
      status: "todo" as const,
      createdBy: "user-1",
      createdAt: Date.now(),
    };

    tasks.value = [task1, task2];

    // Delete task-1
    tasks.value = tasks.value.filter((t) => t.id !== "task-1");

    expect(tasks.value.length).toBe(1);
    expect(tasks.value[0]?.id).toBe("task-2");
  });

  test("resetState clears tasks", () => {
    tasks.value = [
      {
        id: "task-1",
        text: "Test",
        description: "",
        priority: "low",
        status: "todo",
        createdBy: "user-1",
        createdAt: Date.now(),
      },
    ];

    resetState();

    expect(tasks.value).toEqual([]);
  });
});

describe("Urgent Task Constraints", () => {
  beforeEach(() => {
    workspace.value = {
      id: "workspace-1",
      name: "Test Workspace",
      workspaceKey: new Uint8Array(32),
      maxUrgentTasks: 3,
      createdAt: Date.now(),
    };
  });

  test("can create urgent tasks up to limit", () => {
    const createUrgentTask = (id: string) => ({
      id,
      text: `Urgent task ${id}`,
      description: "",
      priority: "urgent" as const,
      status: "todo" as const,
      createdBy: "user-1",
      createdAt: Date.now(),
    });

    tasks.value = [
      createUrgentTask("task-1"),
      createUrgentTask("task-2"),
      createUrgentTask("task-3"),
    ];

    const urgentCount = tasks.value.filter(
      (t) => t.priority === "urgent" && t.status !== "done"
    ).length;

    expect(urgentCount).toBe(3);
    expect(urgentCount).toBeLessThanOrEqual(workspace.value!.maxUrgentTasks);
  });

  test("completed urgent tasks don't count toward limit", () => {
    tasks.value = [
      {
        id: "task-1",
        text: "Urgent 1",
        description: "",
        priority: "urgent",
        status: "done",
        createdBy: "user-1",
        createdAt: Date.now(),
      },
      {
        id: "task-2",
        text: "Urgent 2",
        description: "",
        priority: "urgent",
        status: "done",
        createdBy: "user-1",
        createdAt: Date.now(),
      },
      {
        id: "task-3",
        text: "Urgent 3",
        description: "",
        priority: "urgent",
        status: "todo",
        createdBy: "user-1",
        createdAt: Date.now(),
      },
    ];

    const activeUrgentCount = tasks.value.filter(
      (t) => t.priority === "urgent" && t.status !== "done"
    ).length;

    expect(activeUrgentCount).toBe(1);
    expect(activeUrgentCount).toBeLessThan(workspace.value!.maxUrgentTasks);
  });

  test("non-urgent tasks don't count toward limit", () => {
    tasks.value = [
      {
        id: "task-1",
        text: "High priority",
        description: "",
        priority: "high",
        status: "todo",
        createdBy: "user-1",
        createdAt: Date.now(),
      },
      {
        id: "task-2",
        text: "Medium priority",
        description: "",
        priority: "medium",
        status: "todo",
        createdBy: "user-1",
        createdAt: Date.now(),
      },
    ];

    const urgentCount = tasks.value.filter(
      (t) => t.priority === "urgent" && t.status !== "done"
    ).length;

    expect(urgentCount).toBe(0);
  });
});
