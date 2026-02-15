// Test fixture for naming collision between DOM event handlers and state handlers
// Issue #27: https://github.com/AlexJeffcott/polly/issues/27

import { $sharedState } from "@anthropic/polly/state";
import { ensures, requires } from "@anthropic/polly/verify";

// Mock message bus for DOM event handlers
const messageBus = {
  on: (_event: string, _handler: () => void) => {
    // Mock implementation for testing
  },
};

// ============================================================================
// State declarations with verify: true
// ============================================================================

export const connectionState = $sharedState(
  "connection",
  {
    status: "disconnected" as "disconnected" | "connecting" | "connected",
    lastError: null as string | null,
  },
  { verify: true }
);

// ============================================================================
// DOM Event Handlers - these produce messageType like "connected"
// ============================================================================

// This will produce: messageType = "connected" → HandleConnected
messageBus.on("connected", () => {
  console.log("WebSocket connected event");
});

// This will produce: messageType = "disconnected" → HandleDisconnected
messageBus.on("disconnected", () => {
  console.log("WebSocket disconnected event");
});

// ============================================================================
// State Handlers - these produce messageType like "Connected" (after stripping "handle")
// ============================================================================

// This will produce: messageType = "Connected" → HandleConnected (COLLISION!)
export function handleConnected(): void {
  requires(connectionState.value.status === "connecting", "Must be in connecting state");

  connectionState.value = {
    ...connectionState.value,
    status: "connected",
    lastError: null,
  };

  ensures(connectionState.value.status === "connected", "Must be connected after success");
}

// This will produce: messageType = "Disconnected" → HandleDisconnected (COLLISION!)
export function handleDisconnected(): void {
  requires(connectionState.value.status === "connected", "Must be connected to disconnect");

  connectionState.value = {
    ...connectionState.value,
    status: "disconnected",
  };

  ensures(connectionState.value.status === "disconnected", "Must be disconnected after");
}
