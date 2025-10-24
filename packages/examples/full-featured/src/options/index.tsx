/**
 * Full-Featured Example - Options Page
 *
 * Demonstrates settings management with persistent state
 */

import { $sharedState } from "@fairfox/web-ext/state";
import { render } from "preact";
import type { Settings } from "../shared/types/messages";

const settings = $sharedState<Settings>("app-settings", {
  theme: "auto",
  autoSync: true,
  debugMode: false,
  notifications: true,
  apiEndpoint: "",
  refreshInterval: 60000,
});

function Options() {
  return (
    <div style={{ padding: "32px", maxWidth: "600px", margin: "0 auto" }}>
      <h1 style={{ marginBottom: "24px" }}>Extension Settings</h1>

      <section style={{ marginBottom: "24px" }}>
        <h2 style={{ fontSize: "18px", marginBottom: "12px" }}>Appearance</h2>
        <label style={{ display: "block", marginBottom: "8px" }}>
          Theme:
          <select
            value={settings.value.theme}
            onChange={(e) =>
              (settings.value = {
                ...settings.value,
                theme: (e.target as HTMLSelectElement).value as
                  | "light"
                  | "dark"
                  | "auto",
              })
            }
            style={{ marginLeft: "8px", padding: "4px" }}
          >
            <option value="auto">Auto</option>
            <option value="light">Light</option>
            <option value="dark">Dark</option>
          </select>
        </label>
      </section>

      <section style={{ marginBottom: "24px" }}>
        <h2 style={{ fontSize: "18px", marginBottom: "12px" }}>
          Sync & Storage
        </h2>
        <label style={{ display: "block", marginBottom: "8px" }}>
          <input
            type="checkbox"
            checked={settings.value.autoSync}
            onChange={(e) =>
              (settings.value = {
                ...settings.value,
                autoSync: (e.target as HTMLInputElement).checked,
              })
            }
          />{" "}
          Auto-sync data across devices
        </label>
        <label style={{ display: "block", marginBottom: "8px" }}>
          Refresh Interval (ms):
          <input
            type="number"
            value={settings.value.refreshInterval}
            onInput={(e) =>
              (settings.value = {
                ...settings.value,
                refreshInterval: Number((e.target as HTMLInputElement).value),
              })
            }
            style={{ marginLeft: "8px", padding: "4px", width: "100px" }}
          />
        </label>
      </section>

      <section style={{ marginBottom: "24px" }}>
        <h2 style={{ fontSize: "18px", marginBottom: "12px" }}>
          Notifications
        </h2>
        <label style={{ display: "block", marginBottom: "8px" }}>
          <input
            type="checkbox"
            checked={settings.value.notifications}
            onChange={(e) =>
              (settings.value = {
                ...settings.value,
                notifications: (e.target as HTMLInputElement).checked,
              })
            }
          />{" "}
          Enable notifications
        </label>
      </section>

      <section style={{ marginBottom: "24px" }}>
        <h2 style={{ fontSize: "18px", marginBottom: "12px" }}>
          API Configuration
        </h2>
        <label style={{ display: "block", marginBottom: "8px" }}>
          API Endpoint:
          <input
            type="text"
            value={settings.value.apiEndpoint}
            onInput={(e) =>
              (settings.value = {
                ...settings.value,
                apiEndpoint: (e.target as HTMLInputElement).value,
              })
            }
            placeholder="https://api.example.com"
            style={{
              display: "block",
              marginTop: "4px",
              padding: "4px",
              width: "100%",
            }}
          />
        </label>
      </section>

      <section style={{ marginBottom: "24px" }}>
        <h2 style={{ fontSize: "18px", marginBottom: "12px" }}>Developer</h2>
        <label style={{ display: "block", marginBottom: "8px" }}>
          <input
            type="checkbox"
            checked={settings.value.debugMode}
            onChange={(e) =>
              (settings.value = {
                ...settings.value,
                debugMode: (e.target as HTMLInputElement).checked,
              })
            }
          />{" "}
          Enable debug mode
        </label>
      </section>

      <div
        style={{
          padding: "12px",
          background: "#f0f0f0",
          borderRadius: "4px",
          fontSize: "12px",
        }}
      >
        <strong>Note:</strong> Settings are automatically saved and synced
        across all extension contexts.
      </div>
    </div>
  );
}

const root = document.getElementById("root");
if (root) {
  render(<Options />, root);
}
