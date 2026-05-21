// Message handlers for the mesh chat fixture.
// @ts-nocheck

import { presence, rooms } from "./mesh";
import type { RequestMessage } from "./types";

export async function handleJoin(_msg: RequestMessage): Promise<string> {
  rooms.value = { ...rooms.value, count: rooms.value.count + 1 };
  presence.value = { ...presence.value, online: true };
  return JSON.stringify({ type: "joined" });
}

export async function handleLeave(_msg: RequestMessage): Promise<string> {
  rooms.value = { ...rooms.value, count: rooms.value.count - 1 };
  presence.value = { ...presence.value, online: false };
  return JSON.stringify({ type: "left" });
}

export async function routeMessage(message: RequestMessage): Promise<string> {
  if (message.type === "join") return handleJoin(message);
  if (message.type === "leave") return handleLeave(message);
  return JSON.stringify({ type: "error" });
}
