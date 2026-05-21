// Verify fixture for polly#114: an app that uses $meshState end-to-end.
//
// It declares two mesh documents (multiple keys), one carrying an access
// predicate and a schema migration, alongside ordinary $sharedState and a
// verified message handler. Running `polly verify` against this project
// exercises the polly#117 mesh codegen and — because `mesh:` is declared
// in the config — triggers the polly#113 concurrent-seed guard
// (MeshSeed.tla).

import { createBackground } from "@fairfox/polly/background";
import { $meshState } from "@fairfox/polly/mesh";
import { $sharedState } from "@fairfox/polly/state";
import { ensures, requires } from "@fairfox/polly/verify";

// Ordinary device-local state.
export const session = $sharedState("session", { active: false });

// Mesh-replicated todo count. Carries a schema migration (v1 → v2) and a
// declarative access predicate — the surface polly#114 asks a fixture to
// cover end-to-end.
export const todos = $meshState(
  "mesh-todos",
  { __schemaVersion: 2, count: 0 },
  {
    schemaVersion: 2,
    migrations: {
      // v1 → v2: introduce the count field on documents that predate it.
      2: (doc) => {
        if (typeof doc["count"] !== "number") doc["count"] = 0;
      },
    },
    access: {
      // Public to read, members-only to write.
      read: () => true,
      write: (identity) => identity !== undefined,
    },
  }
);

// A second mesh document — presence — so the fixture declares multiple
// mesh keys.
export const presence = $meshState("mesh-presence", { __schemaVersion: 1, online: false });

const bus = createBackground();

// A verified handler over the device-local session state. Its pre- and
// postconditions keep the generated project spec (UserApp.tla) small and
// trivially convergent, so the only interesting TLC work is the mesh
// codegen and the seed-race guard.
bus.on("PING", async () => {
  requires(session.value.active === true, "session must be active to ping");

  ensures(session.value.active === true, "session stays active after ping");

  return { pong: true };
});

console.log("mesh-seed-guard fixture loaded");
