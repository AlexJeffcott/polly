import { describe, expect, test } from "bun:test";
import { signal } from "@preact/signals";
import { $resource } from "@/shared/lib/resource";

describe("$resource", () => {
  test("initial state is idle with initialValue", () => {
    const resource = $resource("test", {
      source: () => ({}),
      fetcher: async () => "data",
      initialValue: "default",
    });

    expect(resource.data.value).toBe("default");
    // After construction, the effect runs synchronously and triggers loading
    expect(resource.status.value).toBe("loading");
    expect(resource.error.value).toBeUndefined();
  });

  test("successful fetch updates data and status", async () => {
    const resource = $resource("test", {
      source: () => ({ id: 1 }),
      fetcher: async ({ id }) => `result-${id}`,
      initialValue: "",
    });

    // Wait for the microtask to resolve
    await new Promise((resolve) => setTimeout(resolve, 10));

    expect(resource.data.value).toBe("result-1");
    expect(resource.status.value).toBe("success");
    expect(resource.error.value).toBeUndefined();
  });

  test("failed fetch sets error and status", async () => {
    const resource = $resource("test", {
      source: () => ({}),
      fetcher: async () => {
        throw new Error("Network error");
      },
      initialValue: null,
    });

    await new Promise((resolve) => setTimeout(resolve, 10));

    expect(resource.status.value).toBe("error");
    expect(resource.error.value).toBeInstanceOf(Error);
    expect(resource.error.value?.message).toBe("Network error");
    expect(resource.data.value).toBeNull(); // unchanged from initialValue
  });

  test("non-Error throw is wrapped in Error", async () => {
    const resource = $resource("test", {
      source: () => ({}),
      fetcher: async () => {
        throw "string error";
      },
      initialValue: null,
    });

    await new Promise((resolve) => setTimeout(resolve, 10));

    expect(resource.error.value).toBeInstanceOf(Error);
    expect(resource.error.value?.message).toBe("string error");
  });

  test("source change triggers re-fetch", async () => {
    const userId = signal(1);
    const fetchCount = { count: 0 };

    const resource = $resource("test", {
      source: () => ({ userId: userId.value }),
      fetcher: async ({ userId }) => {
        fetchCount.count++;
        return `user-${userId}`;
      },
      initialValue: "",
    });

    await new Promise((resolve) => setTimeout(resolve, 10));
    expect(resource.data.value).toBe("user-1");
    expect(fetchCount.count).toBe(1);

    // Change source dependency
    userId.value = 2;
    await new Promise((resolve) => setTimeout(resolve, 10));

    expect(resource.data.value).toBe("user-2");
    expect(fetchCount.count).toBe(2);
  });

  test("stale responses are discarded", async () => {
    const userId = signal(1);
    let resolveFirst: ((v: string) => void) | undefined;
    let resolveSecond: ((v: string) => void) | undefined;

    const resource = $resource("test", {
      source: () => ({ userId: userId.value }),
      fetcher: async ({ userId }) => {
        if (userId === 1) {
          return new Promise<string>((resolve) => {
            resolveFirst = resolve;
          });
        }
        return new Promise<string>((resolve) => {
          resolveSecond = resolve;
        });
      },
      initialValue: "",
    });

    // Wait for effect to run
    await new Promise((resolve) => setTimeout(resolve, 5));

    // Change source before first fetch resolves
    userId.value = 2;
    await new Promise((resolve) => setTimeout(resolve, 5));

    // Resolve second fetch first
    resolveSecond?.("second-result");
    await new Promise((resolve) => setTimeout(resolve, 5));
    expect(resource.data.value).toBe("second-result");

    // Resolve first fetch (stale — should be discarded)
    resolveFirst?.("first-result");
    await new Promise((resolve) => setTimeout(resolve, 5));

    // Data should still be second result
    expect(resource.data.value).toBe("second-result");
    expect(resource.status.value).toBe("success");
  });

  test("deep equality skip — same source values don't re-fetch", async () => {
    const trigger = signal(0);
    let fetchCount = 0;

    const _resource = $resource("test", {
      source: () => {
        // Read trigger to re-run, but always return same object shape
        void trigger.value;
        return { key: "same" };
      },
      fetcher: async () => {
        fetchCount++;
        return "data";
      },
      initialValue: "",
    });

    await new Promise((resolve) => setTimeout(resolve, 10));
    expect(fetchCount).toBe(1);

    // Trigger effect re-run with same source output
    trigger.value = 1;
    await new Promise((resolve) => setTimeout(resolve, 10));

    // Should NOT have re-fetched
    expect(fetchCount).toBe(1);
  });

  test("refetch() re-runs fetcher with current source", async () => {
    let fetchCount = 0;

    const resource = $resource("test", {
      source: () => ({ id: 42 }),
      fetcher: async ({ id }) => {
        fetchCount++;
        return `data-${id}-${fetchCount}`;
      },
      initialValue: "",
    });

    await new Promise((resolve) => setTimeout(resolve, 10));
    expect(fetchCount).toBe(1);
    expect(resource.data.value).toBe("data-42-1");

    resource.refetch();
    await new Promise((resolve) => setTimeout(resolve, 10));

    expect(fetchCount).toBe(2);
    expect(resource.data.value).toBe("data-42-2");
  });
});
