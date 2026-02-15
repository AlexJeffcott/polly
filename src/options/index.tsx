// Options page UI

import { signal } from "@preact/signals";
import { render } from "preact";
import { defaultSettings, settings } from "@/shared/state/app-state";

// Local state
const saveStatus = signal<"idle" | "saving" | "saved" | "error">("idle");
const errorMessage = signal("");

// Save settings (state is already auto-persisted, just show feedback)
async function saveSettings() {
  saveStatus.value = "saving";
  try {
    // Settings are automatically persisted by $sharedState
    // Just show success feedback
    saveStatus.value = "saved";
    setTimeout(() => {
      saveStatus.value = "idle";
    }, 2000);
  } catch (error) {
    saveStatus.value = "error";
    errorMessage.value = error instanceof Error ? error.message : "Failed to save settings";
  }
}

// Reset settings
async function resetSettings() {
  if (!confirm("Are you sure you want to reset all settings to defaults?")) {
    return;
  }

  try {
    // Reset to default settings (automatically persisted)
    settings.value = defaultSettings;
    saveStatus.value = "saved";
    setTimeout(() => {
      saveStatus.value = "idle";
    }, 2000);
  } catch (error) {
    saveStatus.value = "error";
    errorMessage.value = error instanceof Error ? error.message : "Failed to reset settings";
  }
}

function Options() {
  return (
    <div className="options">
      <header>
        <h1>{process.env["EXTENSION_NAME"]} - Settings</h1>
        <span className="version">v{process.env["VERSION"]}</span>
      </header>

      <main>
        <section>
          <h2>Appearance</h2>

          <div className="setting">
            <label htmlFor="theme">Theme</label>
            <select
              id="theme"
              value={settings.value.theme}
              onChange={(e) => {
                settings.value = {
                  ...settings.value,
                  theme: (e.target as HTMLSelectElement).value as "light" | "dark" | "auto",
                };
              }}
            >
              <option value="light">Light</option>
              <option value="dark">Dark</option>
              <option value="auto">Auto (follow system)</option>
            </select>
            <p className="description">Choose the theme for the extension UI</p>
          </div>
        </section>

        <section>
          <h2>Behavior</h2>

          <div className="setting">
            <label>
              <input
                type="checkbox"
                checked={settings.value.autoSync}
                onChange={(e) => {
                  settings.value = {
                    ...settings.value,
                    autoSync: (e.target as HTMLInputElement).checked,
                  };
                }}
              />
              Auto-sync state across contexts
            </label>
            <p className="description">
              Automatically synchronize state between all extension contexts
            </p>
          </div>

          <div className="setting">
            <label>
              <input
                type="checkbox"
                checked={settings.value.notifications}
                onChange={(e) => {
                  settings.value = {
                    ...settings.value,
                    notifications: (e.target as HTMLInputElement).checked,
                  };
                }}
              />
              Show notifications
            </label>
            <p className="description">Display notifications for important events</p>
          </div>
        </section>

        <section>
          <h2>Advanced</h2>

          <div className="setting">
            <label>
              <input
                type="checkbox"
                checked={settings.value.debugMode}
                onChange={(e) => {
                  settings.value = {
                    ...settings.value,
                    debugMode: (e.target as HTMLInputElement).checked,
                  };
                }}
              />
              Debug mode
            </label>
            <p className="description">Enable verbose logging for debugging</p>
          </div>

          <div className="setting">
            <label htmlFor="apiEndpoint">API Endpoint</label>
            <input
              id="apiEndpoint"
              type="text"
              value={settings.value.apiEndpoint}
              onInput={(e) => {
                settings.value = {
                  ...settings.value,
                  apiEndpoint: (e.target as HTMLInputElement).value,
                };
              }}
              placeholder="https://api.example.com"
            />
            <p className="description">Base URL for API requests</p>
          </div>

          <div className="setting">
            <label htmlFor="refreshInterval">Refresh Interval (ms)</label>
            <input
              id="refreshInterval"
              type="number"
              value={settings.value.refreshInterval}
              onInput={(e) => {
                settings.value = {
                  ...settings.value,
                  refreshInterval:
                    Number.parseInt((e.target as HTMLInputElement).value, 10) || 60000,
                };
              }}
              min="1000"
              step="1000"
            />
            <p className="description">How often to refresh data (milliseconds)</p>
          </div>
        </section>

        <footer>
          <div className="actions">
            <button type="button" onClick={saveSettings} disabled={saveStatus.value === "saving"}>
              {saveStatus.value === "saving" ? "Saving..." : "Save Settings"}
            </button>
            <button type="button" onClick={resetSettings} className="secondary">
              Reset to Defaults
            </button>
          </div>

          {saveStatus.value === "saved" && <div className="status success">Settings saved!</div>}
          {saveStatus.value === "error" && <div className="status error">{errorMessage.value}</div>}
        </footer>
      </main>
    </div>
  );
}

const root = document.getElementById("root");
if (root) {
  render(<Options />, root);
}
