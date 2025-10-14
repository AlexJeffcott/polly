// Popup UI

import { getMessageBus } from "@/shared/lib/message-bus";
import { settings } from "@/shared/state/app-state";
import { computed, signal } from "@preact/signals";
import { render } from "preact";

const bus = getMessageBus("popup");

// Local state
const currentTabUrl = signal("");
const elementCount = signal(0);
const isLoading = signal(false);

// Get current tab
async function getCurrentTab() {
  const tabs = await bus.adapters.tabs.query({
    active: true,
    currentWindow: true,
  });
  if (tabs[0]) {
    currentTabUrl.value = tabs[0].url || "";
    return tabs[0];
  }
  return null;
}

// Query DOM in current tab
async function queryCurrentTab() {
  isLoading.value = true;
  try {
    const tab = await getCurrentTab();
    if (!tab?.id) return;

    const response = await bus.send({ type: "DOM_QUERY", selector: "*" }, { tabId: tab.id });

    if (response && "elements" in response) {
      elementCount.value = response.elements.length;
    }
  } catch (error) {
    console.error("Failed to query tab:", error);
  } finally {
    isLoading.value = false;
  }
}

// Initialize
getCurrentTab();

function Popup() {
  const isDark = computed(() => settings.value.theme === "dark");

  return (
    <div className={`popup ${isDark.value ? "dark" : "light"}`}>
      <header>
        <h1>{process.env["EXTENSION_NAME"]}</h1>
        <span className="version">v{process.env["VERSION"]}</span>
      </header>

      <main>
        <section>
          <h2>Current Tab</h2>
          <div className="url">{currentTabUrl.value || "No active tab"}</div>
        </section>

        <section>
          <h2>Quick Actions</h2>
          <button type="button" onClick={queryCurrentTab} disabled={isLoading.value}>
            {isLoading.value ? "Loading..." : "Count Elements"}
          </button>
          {elementCount.value > 0 && <div className="result">{elementCount.value} elements</div>}
        </section>

        <section>
          <h2>Settings</h2>
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
            Debug Mode
          </label>

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
            Notifications
          </label>

          <div className="theme-selector">
            <label htmlFor="theme-select">Theme:</label>
            <select
              id="theme-select"
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
              <option value="auto">Auto</option>
            </select>
          </div>
        </section>

        <footer>
          <button
            type="button"
            onClick={() => {
              chrome.runtime.openOptionsPage();
            }}
          >
            Open Options
          </button>
        </footer>
      </main>
    </div>
  );
}

const root = document.getElementById("root");
if (root) {
  render(<Popup />, root);
}
