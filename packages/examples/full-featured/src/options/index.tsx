/**
 * Test Extension - Options
 *
 * Renders framework state to DOM for cross-context sync testing.
 * When popup updates state, options page should automatically reflect changes.
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

const bus = getMessageBus("options");

// Super simple cross-context test state
const lastPingReceived = signal("");

// Listen for pings from popup
bus.on("SIMPLE_PING", async (payload: SimplePingMessage) => {
  console.log("[OPTIONS] Received SIMPLE_PING", payload);
  lastPingReceived.value = `Received ping at ${Date.now()}: ${payload.timestamp}`;
  // Send pong back
  const pongMessage: SimplePongMessage = { type: "SIMPLE_PONG", timestamp: Date.now() };
  bus.broadcast(pongMessage);
  return undefined;
});

function Options() {
  return (
    <div className="test-options" data-testid="test-options">
      <header>
        <h1>Framework Test Extension - Options</h1>
        <div data-testid="context">options</div>
      </header>

      <main>
        {/* Simple $sharedState test */}
        <section>
          <h2>Simple $sharedState (from popup)</h2>
          <div data-testid="options-simple-shared-value">{simpleSharedCounter.value}</div>
        </section>

        {/* Simple $syncedState test */}
        <section>
          <h2>Simple $syncedState (from popup)</h2>
          <div data-testid="options-simple-synced-value">{simpleSyncedCounter.value}</div>
        </section>

        {/* Simple cross-context test */}
        <section>
          <h2>Simple Broadcast Test</h2>
          <div data-testid="ping-received">{lastPingReceived.value || "No pings received"}</div>
        </section>

        {/* Same state as popup - should sync automatically */}
        <section>
          <h2>$sharedState (Synced from Popup)</h2>
          <p>These values sync automatically when changed in popup:</p>
          <div data-testid="options-counter">{testCounter.value}</div>
          <div data-testid="options-color">{testPreferences.value.color}</div>
          <button data-testid="options-increment" onClick={() => testCounter.value++}>
            +1 from Options
          </button>
        </section>

        <section>
          <h2>$syncedState (Synced from Popup)</h2>
          <div data-testid="options-message">{testMessage.value}</div>
          <input
            data-testid="options-input-message"
            type="text"
            value={testMessage.value}
            onInput={(e) => (testMessage.value = (e.target as HTMLInputElement).value)}
            placeholder="Type from options..."
          />
        </section>

        <section>
          <h2>Local Signal (NOT Synced)</h2>
          <p>This counter is independent in options context:</p>
          <div data-testid="options-local-counter">{testLocalCounter.value}</div>
          <button data-testid="options-increment-local" onClick={() => testLocalCounter.value++}>
            +1 Local (Options)
          </button>
        </section>

        <section>
          <h2>Framework Settings (Synced)</h2>
          <div data-testid="options-settings-theme">{settings.value.theme}</div>
          <div data-testid="options-settings-debug">
            {settings.value.debugMode ? "enabled" : "disabled"}
          </div>
        </section>

        <section>
          <h2>Test Results (Synced)</h2>
          <div data-testid="options-test-status">{testStatus.value}</div>
          <div data-testid="options-test-results">{JSON.stringify(testResults.value)}</div>
        </section>
      </main>
    </div>
  );
}

const root = document.getElementById("root");
if (root) {
  render(<Options />, root);
}
