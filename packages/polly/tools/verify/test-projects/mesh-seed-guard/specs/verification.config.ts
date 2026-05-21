// Verification config for the mesh-seed-guard fixture (polly#114).
//
// Declaring `mesh:` makes the two $meshState documents first-class to the
// verifier: the polly#117 codegen emits a `meshState` variable and a
// PropagateMeshOp action, and — because mesh documents are declared — the
// CLI also runs the polly#113 concurrent-seed guard (MeshSeed.tla).

import { defineVerification } from "@fairfox/polly/verify";

export const verificationConfig = defineVerification({
  state: {
    // Device-local session state (see background/index.ts).
    "session.active": { type: "boolean" },
  },

  // polly#117: each $meshState document, with the bounded shape TLC
  // explores cross-peer via PropagateMeshOp.
  mesh: {
    "mesh-todos": {
      count: { type: "number", min: 0, max: 3 },
    },
    "mesh-presence": {
      online: { type: "boolean" },
    },
  },

  messages: {
    maxInFlight: 2,
    maxTabs: 1,
  },

  onBuild: "warn",
  onRelease: "error",
});
