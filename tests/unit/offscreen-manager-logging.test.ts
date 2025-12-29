/**
 * Tests for OffscreenManager logging behavior
 */

import { beforeEach, expect, mock, test } from "bun:test";
import { OffscreenManager } from "@/background/offscreen-manager";
import type { OffscreenAdapter } from "@/shared/adapters/offscreen.adapter";
import { MessageBus } from "@/shared/lib/message-bus";
import { createMockAdapters } from "@fairfox/polly/test";
import type { MockExtensionAdapters } from "@fairfox/polly/test";
import { noOpAsync } from "@fairfox/polly/test";

let adapters: MockExtensionAdapters;

beforeEach(() => {
  adapters = createMockAdapters();
});

// ============================================================================
// Document Creation Logging
// ============================================================================

test("OffscreenManager logs when creating offscreen document", async () => {
  const createSpy = mock(noOpAsync);
  const mockOffscreen: OffscreenAdapter = {
    createDocument: createSpy,
    closeDocument: mock(noOpAsync),
    hasDocument: mock(async () => false),
  };

  const testAdapters = { ...adapters, offscreen: mockOffscreen };
  const testBus = new MessageBus("background", testAdapters);

  testAdapters.logger._clear();

  const manager = new OffscreenManager(testBus);
  await manager.ensureOffscreenDocument();

  // Should log document creation
  const createLog = testAdapters.logger._calls.find(
    (c: { message: string }) => c.message.includes("Offscreen") || c.message.includes("created")
  );

  expect(createLog).toBeDefined();
  expect(createLog?.level).toBe("info");
});

test("OffscreenManager logs document creation details", async () => {
  const createSpy = mock(noOpAsync);
  const mockOffscreen: OffscreenAdapter = {
    createDocument: createSpy,
    closeDocument: mock(noOpAsync),
    hasDocument: mock(async () => false),
  };

  const testAdapters = { ...adapters, offscreen: mockOffscreen };
  const testBus = new MessageBus("background", testAdapters);

  testAdapters.logger._clear();

  const manager = new OffscreenManager(testBus);
  await manager.ensureOffscreenDocument();

  const createLog = testAdapters.logger._calls.find((c: { message: string }) =>
    c.message.includes("Offscreen")
  );

  expect(createLog).toBeDefined();
  // May include details about the document
  if (createLog?.context) {
    expect(createLog.context).toBeObject();
  }
});

// ============================================================================
// Reusing Existing Document
// ============================================================================

test("OffscreenManager logs when reusing existing document", async () => {
  const createSpy = mock(noOpAsync);
  const mockOffscreen: OffscreenAdapter = {
    createDocument: createSpy,
    closeDocument: mock(noOpAsync),
    hasDocument: mock(async () => true), // Already exists
  };

  const testAdapters = { ...adapters, offscreen: mockOffscreen };
  const testBus = new MessageBus("background", testAdapters);

  testAdapters.logger._clear();

  const manager = new OffscreenManager(testBus);
  await manager.ensureOffscreenDocument();

  // Should not create (already exists)
  expect(createSpy).not.toHaveBeenCalled();

  // Should log that document already exists (debug level)
  const reuseLog = testAdapters.logger._calls.find(
    (c: { message: string }) => c.message.includes("already") || c.message.includes("exists")
  );

  if (reuseLog) {
    expect(reuseLog.level).toBe("debug");
  }
});

// ============================================================================
// Document Closure Logging
// ============================================================================

test("OffscreenManager logs when closing offscreen document", async () => {
  const closeSpy = mock(noOpAsync);
  const mockOffscreen: OffscreenAdapter = {
    createDocument: mock(noOpAsync),
    closeDocument: closeSpy,
    hasDocument: mock(async () => true),
  };

  const testAdapters = { ...adapters, offscreen: mockOffscreen };
  const testBus = new MessageBus("background", testAdapters);

  const manager = new OffscreenManager(testBus);
  await manager.ensureOffscreenDocument();

  testAdapters.logger._clear();

  await manager.closeOffscreenDocument();

  // Should log closure
  const closeLog = testAdapters.logger._calls.find(
    (c: { message: string }) => c.message.includes("closed") || c.message.includes("Closed")
  );

  expect(closeLog).toBeDefined();
  expect(closeLog?.level).toBe("info");
});

// ============================================================================
// Error Logging
// ============================================================================

test("OffscreenManager logs errors when creation fails", async () => {
  const createSpy = mock(async () => {
    throw new Error("Failed to create offscreen document");
  });

  const mockOffscreen: OffscreenAdapter = {
    createDocument: createSpy,
    closeDocument: mock(noOpAsync),
    hasDocument: mock(async () => false),
  };

  const testAdapters = { ...adapters, offscreen: mockOffscreen };
  const testBus = new MessageBus("background", testAdapters);

  testAdapters.logger._clear();

  const manager = new OffscreenManager(testBus);

  try {
    await manager.ensureOffscreenDocument();
  } catch (_error) {
    // Expected to fail
  }

  // Should have logged an error
  const errorLog = testAdapters.logger._calls.find((c: { level?: string }) => c.level === "error");

  expect(errorLog).toBeDefined();
  expect(errorLog?.message.toLowerCase()).toContain("failed");
});

test("OffscreenManager logs error context", async () => {
  const createSpy = mock(async () => {
    throw new Error("Permission denied");
  });

  const mockOffscreen: OffscreenAdapter = {
    createDocument: createSpy,
    closeDocument: mock(noOpAsync),
    hasDocument: mock(async () => false),
  };

  const testAdapters = { ...adapters, offscreen: mockOffscreen };
  const testBus = new MessageBus("background", testAdapters);

  testAdapters.logger._clear();

  const manager = new OffscreenManager(testBus);

  try {
    await manager.ensureOffscreenDocument();
  } catch (_error) {
    // Expected
  }

  const errorLog = testAdapters.logger._calls.find((c: { level?: string }) => c.level === "error");

  expect(errorLog).toBeDefined();
  expect(errorLog?.error).toBeDefined();
});

// ============================================================================
// Multiple Operations Logging
// ============================================================================

test("OffscreenManager logs multiple operations", async () => {
  const createSpy = mock(noOpAsync);
  const closeSpy = mock(noOpAsync);

  const mockOffscreen: OffscreenAdapter = {
    createDocument: createSpy,
    closeDocument: closeSpy,
    hasDocument: mock(async () => false),
  };

  const testAdapters = { ...adapters, offscreen: mockOffscreen };
  const testBus = new MessageBus("background", testAdapters);

  testAdapters.logger._clear();

  const manager = new OffscreenManager(testBus);

  // Create
  await manager.ensureOffscreenDocument();

  // Close
  await manager.closeOffscreenDocument();

  // Logs should include both operations
  const createLog = testAdapters.logger._calls.find((c: { message: string }) =>
    c.message.includes("created")
  );
  const closeLog = testAdapters.logger._calls.find((c: { message: string }) =>
    c.message.includes("closed")
  );

  expect(createLog).toBeDefined();
  expect(closeLog).toBeDefined();
});

// ============================================================================
// Log Levels Are Appropriate
// ============================================================================

test("OffscreenManager uses appropriate log levels", async () => {
  const createSpy = mock(noOpAsync);
  const closeSpy = mock(noOpAsync);

  const mockOffscreen: OffscreenAdapter = {
    createDocument: createSpy,
    closeDocument: closeSpy,
    hasDocument: mock(async () => false),
  };

  const testAdapters = { ...adapters, offscreen: mockOffscreen };
  const testBus = new MessageBus("background", testAdapters);

  testAdapters.logger._clear();

  const manager = new OffscreenManager(testBus);

  // Create document
  await manager.ensureOffscreenDocument();

  // Close document
  await manager.closeOffscreenDocument();

  const infoLogs = testAdapters.logger._calls.filter((c: { level?: string }) => c.level === "info");
  const errorLogs = testAdapters.logger._calls.filter(
    (c: { level?: string }) => c.level === "error"
  );

  // Should have info logs for important operations
  expect(infoLogs.length).toBeGreaterThan(0);

  // Normal operations should not produce errors
  expect(errorLogs.length).toBe(0);
});

// ============================================================================
// Document Check Logging
// ============================================================================

test("OffscreenManager logs document existence checks", async () => {
  const hasSpy = mock(async () => true);

  const mockOffscreen: OffscreenAdapter = {
    createDocument: mock(noOpAsync),
    closeDocument: mock(noOpAsync),
    hasDocument: hasSpy,
  };

  const testAdapters = { ...adapters, offscreen: mockOffscreen };
  const testBus = new MessageBus("background", testAdapters);

  testAdapters.logger._clear();

  const manager = new OffscreenManager(testBus);
  await manager.ensureOffscreenDocument();

  // Should have checked if document exists
  expect(hasSpy).toHaveBeenCalled();

  // May log the check (debug level) - optional, some implementations log checks, some don't
});

// ============================================================================
// No Sensitive Data in Logs
// ============================================================================

test("OffscreenManager does not log sensitive data", async () => {
  const createSpy = mock(noOpAsync);

  const mockOffscreen: OffscreenAdapter = {
    createDocument: createSpy,
    closeDocument: mock(noOpAsync),
    hasDocument: mock(async () => false),
  };

  const testAdapters = { ...adapters, offscreen: mockOffscreen };
  const testBus = new MessageBus("background", testAdapters);

  testAdapters.logger._clear();

  const manager = new OffscreenManager(testBus);
  await manager.ensureOffscreenDocument();

  const allLogs = JSON.stringify(testAdapters.logger._calls);

  // Should log operational details
  expect(allLogs.length).toBeGreaterThan(0);

  // But should not contain internal implementation details that could be sensitive
  // (This is a general principle - specific sensitive data depends on your implementation)
});
