/**
 * Test Extension - Popup
 *
 * Renders framework state to DOM for Playwright validation.
 * Demonstrates real framework usage with reactive UI.
 */

import { getMessageBus } from "@fairfox/web-ext/message-bus";
import { $sharedState } from "@fairfox/web-ext/state";
import type { BaseMessage, Settings } from "@fairfox/web-ext/types";
import { signal } from "@preact/signals";
import { render } from "preact";
import {
  simpleSharedCounter,
  simpleSyncedCounter,
  testCounter,
  testLocalCounter,
  testMessage,
  testPreferences,
  testResults,
  testStatus,
} from "../shared/state/test-state";

// Custom message types for testing
type SimplePingMessage = BaseMessage & { type: "SIMPLE_PING"; timestamp: number };
type SimplePongMessage = BaseMessage & { type: "SIMPLE_PONG"; timestamp: number };
type TestMessage = SimplePingMessage | SimplePongMessage;

// Settings from framework
const settings = $sharedState<Settings>("app-settings", {
  theme: "auto",
  autoSync: true,
  debugMode: false,
  notifications: true,
  apiEndpoint: "",
  refreshInterval: 60000,
});

const bus = getMessageBus("popup");

// Super simple cross-context test state
const lastPing = signal("");

// Listen for pong responses
bus.on("SIMPLE_PONG", async (payload: SimplePongMessage) => {
  lastPing.value = `Received pong at ${Date.now()}`;
  return undefined;
});

function Popup() {
  const sendSimplePing = () => {
    console.log("[POPUP] Sending SIMPLE_PING");
    const pingMessage: SimplePingMessage = { type: "SIMPLE_PING", timestamp: Date.now() };
    bus.broadcast(pingMessage);
    lastPing.value = `Sent ping at ${Date.now()}`;
  };

  const runTest = async (testType: string) => {
    testStatus.value = "running";
    try {
      const testMessage: BaseMessage = { type: `TEST_${testType.toUpperCase()}` };
      const result = await bus.send(testMessage);
      testResults.value = { ...testResults.value, [testType]: result };
      testStatus.value = "success";
    } catch (error) {
      testStatus.value = "error";
      testResults.value = {
        ...testResults.value,
        [testType]: { success: false, error: String(error) },
      };
    }
  };

  const runAllTests = async () => {
    testStatus.value = "running";
    try {
      const testMessage: BaseMessage = { type: "GET_ALL_TEST_RESULTS" };
      const result = await bus.send(testMessage);
      if (result && typeof result === "object" && "results" in result) {
        const resultsObj = result.results;
        if (resultsObj && typeof resultsObj === "object" && "tests" in resultsObj) {
          testResults.value = resultsObj.tests || {};
        }
      }
      testStatus.value = "success";
    } catch (error) {
      console.error("[POPUP] Error running tests:", error);
      testStatus.value = "error";
    }
  };

  return (
    <div className="test-popup" data-testid="test-popup">
      <header>
        <h1>Framework Test Extension</h1>
        <div data-testid="context">popup</div>
      </header>

      <main>
        {/* Simple $sharedState test */}
        <section>
          <h2>Simple $sharedState</h2>
          <div data-testid="simple-shared-value">{simpleSharedCounter.value}</div>
          <button data-testid="simple-shared-increment" onClick={() => simpleSharedCounter.value++}>
            +1
          </button>
        </section>

        {/* Simple $syncedState test */}
        <section>
          <h2>Simple $syncedState</h2>
          <div data-testid="simple-synced-value">{simpleSyncedCounter.value}</div>
          <button data-testid="simple-synced-increment" onClick={() => simpleSyncedCounter.value++}>
            +1
          </button>
        </section>

        {/* Simple cross-context test */}
        <section>
          <h2>Simple Broadcast Test</h2>
          <button data-testid="send-ping" onClick={sendSimplePing}>
            Send Ping
          </button>
          <div data-testid="ping-status">{lastPing.value || "No pings sent"}</div>
        </section>

        {/* Test 1: $sharedState (syncs + persists) */}
        <section>
          <h2>$sharedState Test</h2>
          <p>Counter syncs across all contexts and persists</p>
          <div data-testid="test-counter">{testCounter.value}</div>
          <button data-testid="increment-counter" onClick={() => testCounter.value++}>
            +1
          </button>
          <button data-testid="decrement-counter" onClick={() => testCounter.value--}>
            -1
          </button>
          <button data-testid="reset-counter" onClick={() => (testCounter.value = 0)}>
            Reset
          </button>

          <div data-testid="test-color">{testPreferences.value.color}</div>
          <select
            data-testid="select-color"
            value={testPreferences.value.color}
            onChange={(e) => {
              const target = e.target as HTMLSelectElement;
              const value = target.value;
              if (value === "blue" || value === "red" || value === "green") {
                testPreferences.value = {
                  ...testPreferences.value,
                  color: value,
                };
              }
            }}
          >
            <option value="blue">Blue</option>
            <option value="red">Red</option>
            <option value="green">Green</option>
          </select>
        </section>

        {/* Test 2: $syncedState (syncs, no persist) */}
        <section>
          <h2>$syncedState Test</h2>
          <p>Message syncs across contexts but doesn't persist</p>
          <div data-testid="test-message">{testMessage.value}</div>
          <input
            data-testid="input-message"
            type="text"
            value={testMessage.value}
            onInput={(e) => (testMessage.value = (e.target as HTMLInputElement).value)}
            placeholder="Type here..."
          />
        </section>

        {/* Test 3: Local signal (no sync) */}
        <section>
          <h2>Local Signal Test</h2>
          <p>Counter is local to popup context only</p>
          <div data-testid="local-counter">{testLocalCounter.value}</div>
          <button data-testid="increment-local" onClick={() => testLocalCounter.value++}>
            +1 Local
          </button>
        </section>

        {/* Test 4: Framework settings (from framework) */}
        <section>
          <h2>Framework Settings</h2>
          <div data-testid="settings-theme">{settings.value.theme}</div>
          <div data-testid="settings-debug">
            {settings.value.debugMode ? "enabled" : "disabled"}
          </div>
        </section>

        {/* Test 5: Framework tests */}
        <section>
          <h2>Framework Tests</h2>
          <div data-testid="test-status">{testStatus.value}</div>
          <button data-testid="run-storage-test" onClick={() => runTest("storage")}>
            Test Storage
          </button>
          <button data-testid="run-tabs-test" onClick={() => runTest("tabs")}>
            Test Tabs
          </button>
          <button data-testid="run-roundtrip-test" onClick={() => runTest("message_roundtrip")}>
            Test Roundtrip
          </button>
          <button data-testid="run-all-tests" onClick={runAllTests}>
            Run All Tests
          </button>
        </section>

        {/* Test results */}
        <section>
          <h2>Test Results</h2>
          <div data-testid="test-results-json">{JSON.stringify(testResults.value)}</div>
          {testResults.value.storage && (
            <div data-testid="result-storage-success">
              {testResults.value.storage.success ? "pass" : "fail"}
            </div>
          )}
          {testResults.value.tabs && (
            <div data-testid="result-tabs-count">{testResults.value.tabs.tabCount}</div>
          )}
        </section>
      </main>
    </div>
  );
}

const root = document.getElementById("root");
if (root) {
  render(<Popup />, root);
}
