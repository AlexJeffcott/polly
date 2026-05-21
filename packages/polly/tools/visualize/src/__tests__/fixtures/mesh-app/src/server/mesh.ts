// Mesh-replicated state for the chat fixture — two $meshState documents
// the visualiser should render as first-class nodes (polly#114).
// @ts-nocheck

import { $meshState } from "@fairfox/polly/mesh";

/** Room occupancy, replicated across every peer. Public read, members write. */
export const rooms = $meshState(
  "chat-rooms",
  { __schemaVersion: 1, count: 0 },
  { access: { read: () => true, write: (identity) => identity !== undefined } }
);

/** Per-peer presence, replicated across every peer. */
export const presence = $meshState("chat-presence", { __schemaVersion: 1, online: false });
