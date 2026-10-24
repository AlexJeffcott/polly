export interface PingMessage {
  type: "ping";
}
export interface PongMessage {
  type: "pong";
}
export interface ResetRequest {
  type: "reset";
}
export type Msg = PingMessage | PongMessage | ResetRequest | { type: "custom" };

export function isPing(m: Msg): m is PingMessage {
  return m.type === "ping";
}

export const isPong = (m: Msg): m is PongMessage => m.type === "pong";

export const isReset = function (m: Msg): m is ResetRequest {
  return m.type === "reset";
};

// No predicate: the message type comes from the body.
export function looksCustom(m: Msg): boolean {
  return m.type === "custom";
}

// An assertion predicate has no type node.
export function assertPing(m: Msg): asserts m is PingMessage {
  if (m.type !== "ping") throw new Error("not a ping");
}
