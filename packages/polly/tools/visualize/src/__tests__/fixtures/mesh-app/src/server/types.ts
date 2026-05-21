// Message types for the mesh chat fixture.
// @ts-nocheck

export type RequestMessage =
  | { type: "join"; room: string }
  | { type: "leave"; room: string };
