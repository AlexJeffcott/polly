/**
 * Test Extension - Background Script
 *
 * This demonstrates how users would add their own message handlers.
 * Imports framework components and extends them.
 */

import { getMessageBus } from "@fairfox/web-ext/message-bus";
import { MessageRouter } from "@fairfox/web-ext/message-router";
import { $sharedState } from "@fairfox/web-ext/state";
import type { Settings } from "@fairfox/web-ext/types";
import type { AllMessages } from "../shared/types/messages";

const settings = $sharedState<Settings>("app-settings", {
  theme: "auto",
  autoSync: true,
  debugMode: false,
  notifications: true,
  apiEndpoint: "",
  refreshInterval: 60000,
});

// Initialize background script with message router and custom messages
const bus = getMessageBus<AllMessages>("background");
new MessageRouter(bus);

// Register custom test message handlers (user pattern)
bus.on("TEST_STORAGE", async (payload) => {
  const testData = { testKey: payload.testValue || "test", timestamp: Date.now() };
  await bus.adapters.storage.set(testData);
  const retrieved = await bus.adapters.storage.get("testKey");

  return {
    success: true,
    written: testData,
    retrieved: retrieved.testKey,
    matches: retrieved.testKey === testData.testKey,
  };
});

bus.on("TEST_TABS", async () => {
  const tabs = await bus.adapters.tabs.query({});
  const currentTab = tabs.find((t) => t.active);

  return {
    success: true,
    tabCount: tabs.length,
    hasTabs: tabs.length > 0,
    currentTab: currentTab
      ? {
          id: currentTab.id,
          url: currentTab.url,
          title: currentTab.title,
        }
      : null,
  };
});

bus.on("TEST_MESSAGE_ROUNDTRIP", async (payload) => {
  return {
    success: true,
    received: payload,
    processed: true,
    timestamp: Date.now(),
    context: "background",
  };
});

bus.on("TEST_SIGNAL_STATE", async () => {
  return {
    success: true,
    settingsValue: settings.value,
    hasSettings: !!settings.value,
  };
});

bus.on("TEST_RUNTIME", async () => {
  const extensionId = bus.adapters.runtime.getId();
  return {
    success: true,
    extensionId,
    hasId: !!extensionId,
  };
});

bus.on("GET_ALL_TEST_RESULTS", async () => {
  try {
    const storage = await bus.send(
      { type: "TEST_STORAGE", testValue: "end-to-end-test" },
      { target: "background" }
    );
    const tabs = await bus.send({ type: "TEST_TABS" }, { target: "background" });
    const roundtrip = await bus.send(
      { type: "TEST_MESSAGE_ROUNDTRIP", data: "test-payload" },
      { target: "background" }
    );
    const signal = await bus.send({ type: "TEST_SIGNAL_STATE" }, { target: "background" });
    const runtime = await bus.send({ type: "TEST_RUNTIME" }, { target: "background" });

    const results = {
      timestamp: Date.now(),
      context: "background",
      tests: { storage, tabs, roundtrip, signal, runtime },
    };

    return {
      success: true,
      results,
      allPassed: Object.values(results.tests).every(
        (t) => typeof t === "object" && t !== null && "success" in t && t.success !== false
      ),
    };
  } catch (error) {
    console.error("[BACKGROUND] Error in GET_ALL_TEST_RESULTS:", error);
    throw error;
  }
});

console.log("[Test Extension] Background initialized with test handlers");
