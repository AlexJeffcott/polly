// State model for verification
export const state = {
  authenticated: false,
  connected: false,
  pendingOperations: 0,
};

// Import constraints and handlers for analysis
import "./verification-constraints.ts";
import "./verification-handlers.ts";
