/**
 * Popup UI
 */

import { getMessageBus } from "@fairfox/web-ext/message-bus";

const bus = getMessageBus("popup");

// Simple example without UI framework
const root = document.getElementById("root");

if (root) {
  root.innerHTML = `
    <div style="padding: 16px; min-width: 200px;">
      <h1 style="margin: 0 0 8px 0; font-size: 18px;">my-awesome-extension</h1>
      <button id="ping-btn" style="padding: 8px 16px;">Ping Background</button>
      <p id="response" style="margin-top: 8px; font-size: 14px;"></p>
    </div>
  `;

  const btn = document.getElementById("ping-btn");
  const response = document.getElementById("response");

  btn?.addEventListener("click", async () => {
    const result = await bus.send({ type: "PING" });
    if (response) {
      response.textContent = JSON.stringify(result);
    }
  });
}
