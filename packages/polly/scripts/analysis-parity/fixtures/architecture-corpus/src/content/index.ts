// Content script: talks to remote services.

import { thing } from "@scope/pkg/sub";
import { serve } from "bun";
import { chunk } from "lodash";
import { local } from "./local";

declare const host: string;

export async function load(): Promise<void> {
  await fetch("https://api.example.com/v1/items");
  await fetch(`https://${host}/v2/things`);
  await fetch("https://api.example.com/v1/items", { method: "post" });
  await fetch("https://www.github.com/repos", { method: "DELETE", headers: {} });
  await fetch(String(host));
  /** Opens the live feed. */
  const socket = new WebSocket("wss://ws.example.org/feed");
  socket.send(JSON.stringify({ type: "PING" }));
  window.postMessage({ type: "USER_CREATE" }, "*");
  postMessage({ type: "AUDIT" });
  chunk([1, 2], 1);
  thing();
  local();
  serve({ fetch: () => new Response("ok") });
}
