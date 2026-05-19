/**
 * @fairfox/polly/test/e2e-mesh — end-to-end test kit for the mesh.
 *
 * Centralises the patterns every consumer's e2e scripts reinvent today:
 * pairing-ceremony driving, convergence polling, console-noise filtering,
 * screenshot-on-failure, and an embedded signalling relay. Fairfox and
 * lingua import from this subpath rather than reimplementing.
 *
 * The kit is opinionated about the shape of the consumer it drives —
 * pairing UI exposes stable `data-e2e-*` attributes, the bootstrap path
 * goes through `createMeshClient`, the document state is observable via
 * a polled DOM predicate. Consumers that follow the conventions get the
 * full kit for free; those that diverge supply their own driver per
 * primitive.
 *
 * Diagnostic obligation runs by default through {@link startDiagnosticRecorder}:
 * unexpected silent drops on the diagnostic stream fail the script. A
 * scenario that legitimately exercises a drop branch (e.g. revocation)
 * passes the expected kinds to `assertNoSilentDrops({ allow: [...] })`.
 */

export {
  type ConsolePattern,
  isAllowedConsoleLine,
  MESH_CONSOLE_ALLOWLIST,
} from "./console-allowlist";
export {
  knownPeersFor,
  type PrebakedKeyringPair,
  type PrebakedKeyringSet,
  type PrebakedPeer,
  prebakeKeyringPair,
  prebakeKeyringSet,
} from "./keys";
export {
  type CapturedConsoleLine,
  type LaunchedPeer,
  type LaunchPeerOptions,
  type LaunchSecondTabOptions,
  launchPeer,
  launchSecondTab,
} from "./launch-peer";
export {
  type DiagnosticRecorder,
  MeshAssertionError,
  type MeshAssertionFailure,
  startDiagnosticRecorder,
} from "./mesh-assertions";
export {
  type ServeConsumerOptions,
  type ServeConsumerResult,
  serveConsumer,
} from "./serve-consumer";
export {
  type ConvergencePredicate,
  type PeerSnapshot,
  type WaitForConvergenceOptions,
  waitForConvergence,
  waitForMeshConnected,
} from "./wait-for-convergence";
export { type WithRelayOptions, type WithRelayResult, withRelay } from "./with-relay";
