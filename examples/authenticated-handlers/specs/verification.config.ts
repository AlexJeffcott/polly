import { defineVerification } from "../../../tools/verify/src/index";
import "./verification-state.ts";

export default defineVerification({
  state: {
    authenticated: { type: "boolean", initial: false },
    connected: { type: "boolean", initial: false },
    pendingOperations: { type: "number", initial: 0, min: 0, max: 2 },
  },
  messages: {
    maxInFlight: 3,
    maxTabs: 1,
  },
  tier2: {
    boundedExploration: { maxDepth: 8 },
    temporalConstraints: [
      {
        before: "authenticate",
        after: "query",
        description: "Must authenticate before querying",
      },
      {
        before: "connect",
        after: "authenticate",
        description: "Must connect before authenticating",
      },
    ],
  },
});
