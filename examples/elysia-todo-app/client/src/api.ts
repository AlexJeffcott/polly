import { $syncedState } from "@fairfox/polly";
import { createPollyClient } from "@fairfox/polly/client";
import type { App } from "server/src/index";

// Define client state (must match server state keys)
export const clientState = {
  todos: $syncedState<Array<{ id: number; text: string; completed: boolean }>>("todos", []),
  user: $syncedState<{ id: number; username: string } | null>("user", null),
};

// Create Polly-enhanced Eden client
// Types are automatically inferred from the server!
export const api = createPollyClient<App>("http://localhost:3000", {
  state: clientState,
  websocket: true, // Enable real-time updates
  onOfflineChange: (isOnline) => {
    console.log(`[Polly] Connection: ${isOnline ? "ONLINE" : "OFFLINE"}`);
  },
});
