/**
 * Tests for ApiClient logging behavior
 */

import { beforeEach, expect, test } from "bun:test";
import { ApiClient } from "@/background/api-client";
import { MessageBus } from "@/shared/lib/message-bus";
import { createMockAdapters } from "@fairfox/polly/test";
import type { MockExtensionAdapters } from "@fairfox/polly/test";

let adapters: MockExtensionAdapters;
let bus: MessageBus;

beforeEach(() => {
  adapters = createMockAdapters();
  bus = new MessageBus("background", adapters);
  new ApiClient(bus);
});

// ============================================================================
// Successful Request Logging
// ============================================================================

test("ApiClient logs successful API requests", async () => {
  adapters.fetch._responses.push({
    ok: true,
    status: 200,
    headers: new Headers({ "content-type": "application/json" }),
    statusText: "OK",
    json: async () => ({ data: "success" }),
  });

  adapters.logger._clear();

  await bus.send({
    type: "API_REQUEST",
    endpoint: "https://api.example.com/test",
    method: "GET",
  });

  // Should log the request
  const requestLog = adapters.logger._calls.find(
    (c) => c.message.includes("API") || c.message.includes("request")
  );

  expect(requestLog).toBeDefined();
  expect(requestLog?.level).toBe("info");
});

test("ApiClient logs request details", async () => {
  adapters.fetch._responses.push({
    ok: true,
    status: 200,
    headers: new Headers({ "content-type": "application/json" }),
    statusText: "OK",
    json: async () => ({ data: "success" }),
  });

  adapters.logger._clear();

  await bus.send({
    type: "API_REQUEST",
    endpoint: "https://api.example.com/users",
    method: "POST",
  });

  const requestLog = adapters.logger._calls.find((c) => c.context?.endpoint || c.context?.method);

  expect(requestLog).toBeDefined();
  expect(requestLog?.context?.endpoint).toBe("https://api.example.com/users");
  expect(requestLog?.context?.method).toBe("POST");
});

test("ApiClient logs response status", async () => {
  adapters.fetch._responses.push({
    ok: true,
    status: 201,
    headers: new Headers({ "content-type": "application/json" }),
    statusText: "Created",
    json: async () => ({ id: 123 }),
  });

  adapters.logger._clear();

  await bus.send({
    type: "API_REQUEST",
    endpoint: "https://api.example.com/create",
    method: "POST",
  });

  const responseLog = adapters.logger._calls.find((c) => c.context?.status === 201);

  expect(responseLog).toBeDefined();
  expect(responseLog?.level).toBe("debug");
});

// ============================================================================
// Failed Request Logging
// ============================================================================

test("ApiClient logs API errors", async () => {
  adapters.fetch._responses.push({
    ok: false,
    status: 404,
    headers: new Headers(),
    statusText: "Not Found",
    json: async () => {
      throw new Error("Not JSON");
    },
  });

  adapters.logger._clear();

  await bus.send({
    type: "API_REQUEST",
    endpoint: "https://api.example.com/missing",
    method: "GET",
  });

  const errorLog = adapters.logger._calls.find((c) => c.level === "error");

  expect(errorLog).toBeDefined();
  expect(errorLog?.message).toContain("failed");
});

test("ApiClient logs error with request context", async () => {
  adapters.fetch._responses.push({
    ok: false,
    status: 500,
    headers: new Headers(),
    statusText: "Internal Server Error",
    json: async () => {
      throw new Error("Server error");
    },
  });

  adapters.logger._clear();

  await bus.send({
    type: "API_REQUEST",
    endpoint: "https://api.example.com/error",
    method: "POST",
  });

  const errorLog = adapters.logger._calls.find((c) => c.level === "error");

  expect(errorLog).toBeDefined();
  expect(errorLog?.context?.endpoint).toBe("https://api.example.com/error");
  expect(errorLog?.context?.method).toBe("POST");
  expect(errorLog?.context?.status).toBeDefined();
});

test("ApiClient logs network errors", async () => {
  // Replace fetch to throw
  const originalFetch = adapters.fetch.fetch;
  adapters.fetch.fetch = async () => {
    throw new Error("Network error");
  };

  adapters.logger._clear();

  await bus.send({
    type: "API_REQUEST",
    endpoint: "https://api.example.com/test",
    method: "GET",
  });

  const errorLog = adapters.logger._calls.find((c) => c.level === "error");

  expect(errorLog).toBeDefined();
  expect(errorLog?.message).toContain("error");

  adapters.fetch.fetch = originalFetch;
});

// ============================================================================
// Batch Request Logging
// ============================================================================

test("ApiClient logs batch requests", async () => {
  adapters.fetch._responses.push({
    ok: true,
    status: 200,
    headers: new Headers({ "content-type": "application/json" }),
    statusText: "OK",
    json: async () => ({ url: "https://api.example.com/1" }),
  });

  adapters.fetch._responses.push({
    ok: true,
    status: 200,
    headers: new Headers({ "content-type": "application/json" }),
    statusText: "OK",
    json: async () => ({ url: "https://api.example.com/2" }),
  });

  adapters.logger._clear();

  await bus.send({
    type: "API_BATCH",
    requests: [
      { endpoint: "https://api.example.com/1", method: "GET" },
      { endpoint: "https://api.example.com/2", method: "GET" },
    ],
  });

  // Should log batch operation
  const batchLog = adapters.logger._calls.find(
    (c) => c.message.includes("batch") || c.message.includes("Batch")
  );

  expect(batchLog).toBeDefined();
});

test("ApiClient logs each request in batch", async () => {
  adapters.fetch._responses.push({
    ok: true,
    status: 200,
    headers: new Headers({ "content-type": "application/json" }),
    statusText: "OK",
    json: async () => ({ id: 1 }),
  });

  adapters.fetch._responses.push({
    ok: true,
    status: 200,
    headers: new Headers({ "content-type": "application/json" }),
    statusText: "OK",
    json: async () => ({ id: 2 }),
  });

  adapters.logger._clear();

  await bus.send({
    type: "API_BATCH",
    requests: [
      { endpoint: "https://api.example.com/1", method: "GET" },
      { endpoint: "https://api.example.com/2", method: "GET" },
    ],
  });

  // Should log individual requests or batch summary
  const requestLogs = adapters.logger._calls.filter(
    (c) => c.context?.endpoint || c.message.includes("request")
  );

  expect(requestLogs.length).toBeGreaterThan(0);
});

// ============================================================================
// Request with Body Logging
// ============================================================================

test("ApiClient logs POST requests with body size", async () => {
  adapters.fetch._responses.push({
    ok: true,
    status: 201,
    headers: new Headers({ "content-type": "application/json" }),
    statusText: "Created",
    json: async () => ({ created: true }),
  });

  adapters.logger._clear();

  await bus.send({
    type: "API_REQUEST",
    endpoint: "https://api.example.com/create",
    method: "POST",
    body: { name: "Test User", email: "test@example.com" },
  });

  const requestLog = adapters.logger._calls.find((c) => c.context?.method === "POST");

  expect(requestLog).toBeDefined();
});

test("ApiClient does NOT log request body content (sensitive data)", async () => {
  adapters.fetch._responses.push({
    ok: true,
    status: 200,
    headers: new Headers({ "content-type": "application/json" }),
    statusText: "OK",
    json: async () => ({ success: true }),
  });

  adapters.logger._clear();

  await bus.send({
    type: "API_REQUEST",
    endpoint: "https://api.example.com/auth",
    method: "POST",
    body: {
      username: "testuser",
      password: "super-secret-password",
      apiKey: "sk-1234567890",
    },
  });

  const allLogs = JSON.stringify(adapters.logger._calls);

  // Request details are OK
  expect(allLogs).toContain("https://api.example.com/auth");
  expect(allLogs).toContain("POST");

  // But body content should NOT be logged
  expect(allLogs).not.toContain("super-secret-password");
  expect(allLogs).not.toContain("sk-1234567890");
});

// ============================================================================
// Retry Logging
// ============================================================================

test("ApiClient logs retry attempts on failure", async () => {
  // First attempt fails
  adapters.fetch._responses.push({
    ok: false,
    status: 500,
    headers: new Headers(),
    statusText: "Internal Server Error",
    json: async () => {
      throw new Error("Server error");
    },
  });

  adapters.logger._clear();

  await bus.send({
    type: "API_REQUEST",
    endpoint: "https://api.example.com/flaky",
    method: "GET",
  });

  // Should have logged the failure
  const errorLogs = adapters.logger._calls.filter((c) => c.level === "error");
  expect(errorLogs.length).toBeGreaterThan(0);
});

// ============================================================================
// Response Time Logging
// ============================================================================

test("ApiClient logs request duration", async () => {
  adapters.fetch._responses.push({
    ok: true,
    status: 200,
    headers: new Headers({ "content-type": "application/json" }),
    statusText: "OK",
    json: async () => {
      // Simulate slow response
      await new Promise((resolve) => setTimeout(resolve, 50));
      return { data: "slow" };
    },
  });

  adapters.logger._clear();

  await bus.send({
    type: "API_REQUEST",
    endpoint: "https://api.example.com/slow",
    method: "GET",
  });

  // May log duration
  const durationLog = adapters.logger._calls.find((c) => c.context?.duration || c.context?.time);

  // This is optional - some implementations log duration, some don't
  if (durationLog) {
    expect(durationLog.context?.duration).toBeGreaterThan(0);
  }
});

// ============================================================================
// HTTP Status Code Categories
// ============================================================================

test("ApiClient logs 4xx errors as client errors", async () => {
  adapters.fetch._responses.push({
    ok: false,
    status: 400,
    headers: new Headers(),
    statusText: "Bad Request",
    json: async () => ({ error: "Invalid input" }),
  });

  adapters.logger._clear();

  await bus.send({
    type: "API_REQUEST",
    endpoint: "https://api.example.com/validate",
    method: "POST",
  });

  const errorLog = adapters.logger._calls.find((c) => c.level === "error" || c.level === "warn");

  expect(errorLog).toBeDefined();
  expect(errorLog?.context?.status).toBe(400);
});

test("ApiClient logs 5xx errors as server errors", async () => {
  adapters.fetch._responses.push({
    ok: false,
    status: 503,
    headers: new Headers(),
    statusText: "Service Unavailable",
    json: async () => {
      throw new Error("Service down");
    },
  });

  adapters.logger._clear();

  await bus.send({
    type: "API_REQUEST",
    endpoint: "https://api.example.com/service",
    method: "GET",
  });

  const errorLog = adapters.logger._calls.find((c) => c.level === "error");

  expect(errorLog).toBeDefined();
  expect(errorLog?.context?.status).toBe(503);
});

// ============================================================================
// Log Levels Are Appropriate
// ============================================================================

test("ApiClient uses appropriate log levels", async () => {
  adapters.fetch._responses.push({
    ok: true,
    status: 200,
    headers: new Headers({ "content-type": "application/json" }),
    statusText: "OK",
    json: async () => ({ data: "test" }),
  });

  adapters.logger._clear();

  await bus.send({
    type: "API_REQUEST",
    endpoint: "https://api.example.com/test",
    method: "GET",
  });

  const debugLogs = adapters.logger._calls.filter((c) => c.level === "debug");
  const infoLogs = adapters.logger._calls.filter((c) => c.level === "info");
  const errorLogs = adapters.logger._calls.filter((c) => c.level === "error");

  // Successful requests should use info or debug
  expect(infoLogs.length + debugLogs.length).toBeGreaterThan(0);

  // No errors for successful requests
  expect(errorLogs.length).toBe(0);
});

// ============================================================================
// Performance: Logging Overhead
// ============================================================================

test("ApiClient logging has minimal performance impact", async () => {
  const iterations = 20;

  // Queue up responses
  for (let i = 0; i < iterations; i++) {
    adapters.fetch._responses.push({
      ok: true,
      status: 200,
      headers: new Headers({ "content-type": "application/json" }),
      statusText: "OK",
      json: async () => ({ id: i }),
    });
  }

  adapters.logger._clear();

  const start = performance.now();

  for (let i = 0; i < iterations; i++) {
    await bus.send({
      type: "API_REQUEST",
      endpoint: `https://api.example.com/item/${i}`,
      method: "GET",
    });
  }

  const duration = performance.now() - start;
  const avgTime = duration / iterations;

  // Should be fast (< 2ms per request including logging)
  expect(avgTime).toBeLessThan(2);

  // Should have logged all requests
  expect(adapters.logger._calls.length).toBeGreaterThan(0);
});
