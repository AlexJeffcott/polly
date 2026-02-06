// Verification configuration for WebRTC P2P Chat
// Demonstrates verification for real-time connection state management
import { defineVerification } from "@fairfox/polly/verify";

// biome-ignore lint/style/noDefaultExport: verification configs use default export by convention
export default defineVerification({
  state: {
    // Verified peer count (exercises { type: "number" })
    peerCount: { type: "number", min: 0, max: 5 },
  },

  messages: {
    maxInFlight: 2,
    maxTabs: 1,
  },

  tier2: {
    temporalConstraints: [
      {
        before: "JOIN_ROOM",
        after: "LEAVE_ROOM",
        description: "Must join room before leaving",
      },
    ],
  },

  onBuild: "warn",
  onRelease: "error",
});
