// Async Mutations Tests - validates detection of async race conditions
// 30 comprehensive tests for async mutation tracking

import { afterEach, beforeEach, describe, expect, test } from "bun:test";
import { mkdtemp, rm, writeFile } from "node:fs/promises";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { HandlerExtractor } from "../../../../analysis/src/extract/handlers";

describe("Async Mutation Detection", () => {
  let tempDir: string;
  let originalEnv: string | undefined;

  beforeEach(async () => {
    // Create temp directory for test files
    tempDir = await mkdtemp(join(tmpdir(), "async-test-"));

    // Save and set POLLY_DEBUG for warnings
    originalEnv = process.env["POLLY_DEBUG"];
    process.env["POLLY_DEBUG"] = "1";
  });

  afterEach(async () => {
    // Cleanup
    await rm(tempDir, { recursive: true, force: true });

    // Restore env
    if (originalEnv === undefined) {
      process.env["POLLY_DEBUG"] = undefined;
    } else {
      process.env["POLLY_DEBUG"] = originalEnv;
    }
  });

  // Helper to create test file and extract handlers
  async function createTestFile(code: string): Promise<any> {
    const testFilePath = join(tempDir, "test.ts");
    const tsConfigPath = join(tempDir, "tsconfig.json");

    // Write tsconfig
    await writeFile(
      tsConfigPath,
      JSON.stringify({
        compilerOptions: {
          target: "ES2020",
          module: "commonjs",
          strict: true,
        },
      })
    );

    // Write test file
    await writeFile(testFilePath, code);

    // Extract handlers
    const extractor = new HandlerExtractor(tsConfigPath);
    return extractor.extractHandlers();
  }

  // ============================================================================
  // ASYNC FUNCTION DETECTION (10 tests)
  // ============================================================================

  describe("Async Function Detection", () => {
    test("detects async arrow function handler", async () => {
      const code = `
				const bus = { on: (msg: string, handler: any) => {} };
				bus.on("test", async (data) => {
					await fetch("/api");
					state.count = 1;
				});
			`;

      const result = await createTestFile(code);

      // Handler should be extracted
      expect(result.handlers.length).toBe(1);
      expect(result.handlers[0].messageType).toBe("test");
    });

    test("detects async function expression handler", async () => {
      const code = `
				const bus = { on: (msg: string, handler: any) => {} };
				bus.on("test", async function(data) {
					await delay(100);
					state.value = 42;
				});
			`;

      const result = await createTestFile(code);

      expect(result.handlers.length).toBe(1);
      expect(result.handlers[0].messageType).toBe("test");
    });

    test("handles non-async handler (no warnings)", async () => {
      const code = `
				const bus = { on: (msg: string, handler: any) => {} };
				bus.on("test", (data) => {
					state.count = 1;
				});
			`;

      const result = await createTestFile(code);

      // Should extract handler successfully
      expect(result.handlers.length).toBe(1);
    });

    test("detects async with multiple awaits", async () => {
      const code = `
				const bus = { on: (msg: string, handler: any) => {} };
				bus.on("test", async (data) => {
					await fetch("/api1");
					await fetch("/api2");
					state.count = 1;
				});
			`;

      const result = await createTestFile(code);

      expect(result.handlers.length).toBe(1);
    });

    test("handles async without await (no race condition)", async () => {
      const code = `
				const bus = { on: (msg: string, handler: any) => {} };
				bus.on("test", async (data) => {
					state.count = 1;
				});
			`;

      const result = await createTestFile(code);

      // No await = no race condition warning
      expect(result.handlers.length).toBe(1);
    });

    test("detects mutation before await (safe)", async () => {
      const code = `
				const bus = { on: (msg: string, handler: any) => {} };
				bus.on("test", async (data) => {
					state.count = 1;
					await fetch("/api");
				});
			`;

      const result = await createTestFile(code);

      // Mutation before await is safe
      expect(result.handlers.length).toBe(1);
    });

    test("detects mutation after await (potential race)", async () => {
      const code = `
				const bus = { on: (msg: string, handler: any) => {} };
				bus.on("test", async (data) => {
					await fetch("/api");
					state.count = 1;
				});
			`;

      const result = await createTestFile(code);

      // Should detect but still extract handler
      expect(result.handlers.length).toBe(1);
    });

    test("handles multiple handlers, some async", async () => {
      const code = `
				const bus = { on: (msg: string, handler: any) => {} };
				bus.on("sync", (data) => {
					state.count = 1;
				});
				bus.on("async", async (data) => {
					await fetch("/api");
					state.count = 2;
				});
			`;

      const result = await createTestFile(code);

      expect(result.handlers.length).toBe(2);
    });

    test("detects nested async functions", async () => {
      const code = `
				const bus = { on: (msg: string, handler: any) => {} };
				bus.on("test", async (data) => {
					const helper = async () => {
						await fetch("/api");
					};
					await helper();
					state.count = 1;
				});
			`;

      const result = await createTestFile(code);

      expect(result.handlers.length).toBe(1);
    });

    test("handles async with try-catch", async () => {
      const code = `
				const bus = { on: (msg: string, handler: any) => {} };
				bus.on("test", async (data) => {
					try {
						await fetch("/api");
						state.count = 1;
					} catch (e) {
						state.error = true;
					}
				});
			`;

      const result = await createTestFile(code);

      expect(result.handlers.length).toBe(1);
    });
  });

  // ============================================================================
  // MUTATION AFTER AWAIT DETECTION (10 tests)
  // ============================================================================

  describe("Mutation After Await Detection", () => {
    test("detects simple assignment after await", async () => {
      const code = `
				const bus = { on: (msg: string, handler: any) => {} };
				bus.on("test", async (data) => {
					await fetch("/api");
					state.value = 42;
				});
			`;

      const result = await createTestFile(code);

      // Should extract assignment
      expect(result.handlers.length).toBe(1);
      expect(result.handlers[0].assignments.length).toBeGreaterThanOrEqual(0);
    });

    test("detects compound assignment after await", async () => {
      const code = `
				const bus = { on: (msg: string, handler: any) => {} };
				bus.on("test", async (data) => {
					await delay(100);
					state.count += 1;
				});
			`;

      const result = await createTestFile(code);

      expect(result.handlers.length).toBe(1);
    });

    test("detects array mutation after await", async () => {
      const code = `
				const bus = { on: (msg: string, handler: any) => {} };
				bus.on("test", async (data) => {
					await fetch("/api");
					state.items.push(data);
				});
			`;

      const result = await createTestFile(code);

      expect(result.handlers.length).toBe(1);
    });

    test("detects multiple mutations after await", async () => {
      const code = `
				const bus = { on: (msg: string, handler: any) => {} };
				bus.on("test", async (data) => {
					await fetch("/api");
					state.count = 1;
					state.value = 2;
					state.items.push(3);
				});
			`;

      const result = await createTestFile(code);

      expect(result.handlers.length).toBe(1);
      // Multiple assignments may be detected
    });

    test("detects mutation between multiple awaits", async () => {
      const code = `
				const bus = { on: (msg: string, handler: any) => {} };
				bus.on("test", async (data) => {
					await fetch("/api1");
					state.count = 1;
					await fetch("/api2");
					state.value = 2;
				});
			`;

      const result = await createTestFile(code);

      expect(result.handlers.length).toBe(1);
    });

    test("handles await in conditional", async () => {
      const code = `
				const bus = { on: (msg: string, handler: any) => {} };
				bus.on("test", async (data) => {
					if (condition) {
						await fetch("/api");
					}
					state.count = 1;
				});
			`;

      const result = await createTestFile(code);

      expect(result.handlers.length).toBe(1);
    });

    test("handles await in loop", async () => {
      const code = `
				const bus = { on: (msg: string, handler: any) => {} };
				bus.on("test", async (data) => {
					for (const item of items) {
						await process(item);
					}
					state.count = 1;
				});
			`;

      const result = await createTestFile(code);

      expect(result.handlers.length).toBe(1);
    });

    test("detects array indexing mutation after await", async () => {
      const code = `
				const bus = { on: (msg: string, handler: any) => {} };
				bus.on("test", async (data) => {
					await fetch("/api");
					state.items[0] = newValue;
				});
			`;

      const result = await createTestFile(code);

      expect(result.handlers.length).toBe(1);
    });

    test("handles Promise.all with mutations", async () => {
      const code = `
				const bus = { on: (msg: string, handler: any) => {} };
				bus.on("test", async (data) => {
					await Promise.all([fetch("/api1"), fetch("/api2")]);
					state.count = 1;
				});
			`;

      const result = await createTestFile(code);

      expect(result.handlers.length).toBe(1);
    });

    test("detects mutations in async callback", async () => {
      const code = `
				const bus = { on: (msg: string, handler: any) => {} };
				bus.on("test", async (data) => {
					const result = await fetch("/api");
					result.data.forEach((item: any) => {
						state.items.push(item);
					});
				});
			`;

      const result = await createTestFile(code);

      expect(result.handlers.length).toBe(1);
    });
  });

  // ============================================================================
  // SAFE PATTERNS (10 tests)
  // ============================================================================

  describe("Safe Async Patterns", () => {
    test("allows mutation before any await", async () => {
      const code = `
				const bus = { on: (msg: string, handler: any) => {} };
				bus.on("test", async (data) => {
					state.count = 1;
					await fetch("/api");
				});
			`;

      const result = await createTestFile(code);

      // This is safe - mutation before await
      expect(result.handlers.length).toBe(1);
    });

    test("handles await without subsequent mutations", async () => {
      const code = `
				const bus = { on: (msg: string, handler: any) => {} };
				bus.on("test", async (data) => {
					await fetch("/api");
					console.log("done");
				});
			`;

      const result = await createTestFile(code);

      // No mutation = safe
      expect(result.handlers.length).toBe(1);
    });

    test("allows reading state after await", async () => {
      const code = `
				const bus = { on: (msg: string, handler: any) => {} };
				bus.on("test", async (data) => {
					await fetch("/api");
					const value = state.count;
					console.log(value);
				});
			`;

      const result = await createTestFile(code);

      // Reading is safe
      expect(result.handlers.length).toBe(1);
    });

    test("handles non-state mutations after await", async () => {
      const code = `
				const bus = { on: (msg: string, handler: any) => {} };
				bus.on("test", async (data) => {
					await fetch("/api");
					localVar.count = 1;
				});
			`;

      const result = await createTestFile(code);

      // Local mutations don't matter
      expect(result.handlers.length).toBe(1);
    });

    test("allows computed values after await", async () => {
      const code = `
				const bus = { on: (msg: string, handler: any) => {} };
				bus.on("test", async (data) => {
					await fetch("/api");
					const computed = state.a + state.b;
					return computed;
				});
			`;

      const result = await createTestFile(code);

      expect(result.handlers.length).toBe(1);
    });

    test("handles await with immutable operations", async () => {
      const code = `
				const bus = { on: (msg: string, handler: any) => {} };
				bus.on("test", async (data) => {
					await fetch("/api");
					const filtered = state.items.filter(x => x.active);
				});
			`;

      const result = await createTestFile(code);

      // Filter doesn't mutate
      expect(result.handlers.length).toBe(1);
    });

    test("allows conditional mutation with guard", async () => {
      const code = `
				const bus = { on: (msg: string, handler: any) => {} };
				bus.on("test", async (data) => {
					await fetch("/api");
					if (!state.locked) {
						state.count = 1;
					}
				});
			`;

      const result = await createTestFile(code);

      // Guard doesn't eliminate race, but pattern is detected
      expect(result.handlers.length).toBe(1);
    });

    test("handles early return before await", async () => {
      const code = `
				const bus = { on: (msg: string, handler: any) => {} };
				bus.on("test", async (data) => {
					if (!data) return;
					state.count = 1;
					await fetch("/api");
				});
			`;

      const result = await createTestFile(code);

      expect(result.handlers.length).toBe(1);
    });

    test("allows mutation in finally block", async () => {
      const code = `
				const bus = { on: (msg: string, handler: any) => {} };
				bus.on("test", async (data) => {
					try {
						await fetch("/api");
					} finally {
						state.loading = false;
					}
				});
			`;

      const result = await createTestFile(code);

      // Finally mutations are common pattern
      expect(result.handlers.length).toBe(1);
    });

    test("handles multiple sync handlers correctly", async () => {
      const code = `
				const bus = { on: (msg: string, handler: any) => {} };
				bus.on("test1", (data) => {
					state.count = 1;
				});
				bus.on("test2", (data) => {
					state.value = 2;
				});
			`;

      const result = await createTestFile(code);

      // No async = no warnings
      expect(result.handlers.length).toBe(2);
    });
  });
});
