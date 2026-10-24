/**
 * Background service worker.
 *
 * @description Routes messages between the popup, the content script
 * and the server.
 */

import { db } from "../db/client";
import { repositories } from "../db/repositories";
import { createUser, getDatabase, notifyAll } from "../services/user-service";

declare const bus: {
  on(type: string, handler: (payload: unknown) => unknown): void;
  send(message: unknown): void;
  emit(type: string, payload?: unknown): void;
  adapters: { storage: { get(key: string): unknown }; tabs: { query(): unknown } };
};

chrome.runtime.onMessage.addListener(() => true);
chrome.storage.local.get("key");
browser.tabs.query({});
bus.adapters.storage.get("settings");
bus.adapters.tabs.query();

bus.on("USER_CREATE", async (payload) => {
  await db.query("select 1");
  await db.insert("users", payload);
  const user = createUser(payload);
  await repositories.users.create(user);
  await fetch("https://api.openai.com/v1/chat");
  getDatabase();
  bus.send({ type: "USER_CREATED" });
  return user;
});

bus.on("USER_CREATED", async () => {
  notifyAll();
  bus.emit("AUDIT");
  return true;
});

bus.on("AUDIT", () => {
  const cache = initCache();
  return cache;
});

bus.on("PING", () => ({ pong: true }));

function initCache(): number {
  return 1;
}

/**
 * Start the pipeline.
 * @flow user-signup
 * @trigger User clicks sign up
 * @description Creates the user and fans out
 */
export const start = () => bus.send({ type: "USER_CREATE" });

/** @flow ping-flow */
bus.send("PING");

// biome-ignore format: the annotated function must start on the sender's line
bus.send({ type: "PING", reply: /** @flow ping-reply @trigger Pong arrives @description Replies */ function ()
  { return this !== undefined; } });
