// DevTools panel UI

import { signal } from "@preact/signals";
import { render } from "preact";
import { getMessageBus } from "@/shared/lib/message-bus";
import { settings } from "@/shared/state/app-state";

const bus = getMessageBus("devtools");
const tabId = chrome.devtools.inspectedWindow.tabId;

// Connect with long-lived port
bus.connect(`devtools-${tabId}`);

// Local state
type DOMElement = {
  tag: string;
  text: string;
  html: string;
  attrs: Record<string, string>;
  rect?: DOMRect;
};
type LogEntry = {
  id: string;
  message: string;
};
const elements = signal<DOMElement[]>([]);
const selectedSelector = signal(".example");
const isQuerying = signal(false);
const logs = signal<LogEntry[]>([]);

// Query DOM
async function queryDOM() {
  if (isQuerying.value) return;

  isQuerying.value = true;
  logs.value = [
    ...logs.value,
    { id: crypto.randomUUID(), message: `Querying: ${selectedSelector.value}` },
  ];

  try {
    const response = await bus.send(
      { type: "DOM_QUERY", selector: selectedSelector.value },
      { tabId }
    );

    if (response && "elements" in response) {
      elements.value = response.elements;
      logs.value = [
        ...logs.value,
        { id: crypto.randomUUID(), message: `Found ${response.elements.length} elements` },
      ];
    }
  } catch (error) {
    logs.value = [...logs.value, { id: crypto.randomUUID(), message: `Error: ${error}` }];
  } finally {
    isQuerying.value = false;
  }
}

// Inspect element
async function inspectElement(selector: string) {
  try {
    await bus.send({ type: "DEVTOOLS_INSPECT_ELEMENT", selector }, { tabId });
    logs.value = [...logs.value, { id: crypto.randomUUID(), message: `Inspecting: ${selector}` }];
  } catch (error) {
    logs.value = [...logs.value, { id: crypto.randomUUID(), message: `Error: ${error}` }];
  }
}

// Call page function
async function callPageFunction() {
  try {
    const response = await bus.send(
      {
        type: "PAGE_CALL_FN",
        fnName: "console.log",
        args: ["Hello from DevTools!"],
      },
      { tabId }
    );
    logs.value = [
      ...logs.value,
      { id: crypto.randomUUID(), message: `Called function: ${JSON.stringify(response)}` },
    ];
  } catch (error) {
    logs.value = [...logs.value, { id: crypto.randomUUID(), message: `Error: ${error}` }];
  }
}

function Panel() {
  return (
    <div className="panel">
      <header className="header">
        <h1>{process.env["EXTENSION_NAME"]}</h1>
        <span className="version">v{process.env["VERSION"]}</span>
      </header>

      <div className="content">
        <section className="query-section">
          <h2>DOM Query</h2>
          <div className="input-group">
            <input
              type="text"
              value={selectedSelector.value}
              onInput={(e) => {
                selectedSelector.value = (e.target as HTMLInputElement).value;
              }}
              placeholder="CSS selector"
              disabled={isQuerying.value}
            />
            <button type="button" onClick={queryDOM} disabled={isQuerying.value}>
              {isQuerying.value ? "Querying..." : "Query"}
            </button>
          </div>

          {elements.value.length > 0 && (
            <div className="results">
              <h3>Results ({elements.value.length})</h3>
              <ul>
                {elements.value.map((el, i) => (
                  <li key={`${el.tag}-${el.text.substring(0, 20)}-${i}`}>
                    <code>&lt;{el.tag}&gt;</code>
                    <span className="text">{el.text.substring(0, 50)}</span>
                    <button
                      type="button"
                      onClick={() => inspectElement(`.${el.attrs["class"] || el.tag}`)}
                    >
                      Inspect
                    </button>
                  </li>
                ))}
              </ul>
            </div>
          )}
        </section>

        <section className="actions-section">
          <h2>Actions</h2>
          <button type="button" onClick={callPageFunction}>
            Call Page Function
          </button>
          <button
            type="button"
            onClick={() => {
              settings.value = { ...settings.value, theme: "dark" };
              logs.value = [
                ...logs.value,
                { id: crypto.randomUUID(), message: "Theme updated to dark" },
              ];
            }}
          >
            Set Dark Theme
          </button>
        </section>

        <section className="logs-section">
          <h2>Logs</h2>
          <div className="logs">
            {logs.value.map((log) => (
              <div key={log.id} className="log-entry">
                {log.message}
              </div>
            ))}
          </div>
          <button
            type="button"
            onClick={() => {
              logs.value = [];
            }}
          >
            Clear Logs
          </button>
        </section>

        <section className="settings-section">
          <h2>Settings</h2>
          <div>Theme: {settings.value.theme}</div>
          <div>Debug Mode: {settings.value.debugMode ? "On" : "Off"}</div>
        </section>
      </div>
    </div>
  );
}

const root = document.getElementById("root");
if (root) {
  render(<Panel />, root);
}
