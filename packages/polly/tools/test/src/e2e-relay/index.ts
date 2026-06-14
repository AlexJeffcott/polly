/**
 * @fairfox/polly/test/e2e-relay — end-to-end test kit for the peer-relay
 * transport ($peerState over createPeerStateClient / createPeerRepoServer).
 *
 * The relay counterpart to the mesh kit. Where the mesh kit drives browser
 * peers over WebRTC, this drives in-process clients over a WebSocket relay —
 * no Puppeteer, no signalling, just real `createPeerStateClient` instances
 * speaking to a real `createPeerRepoServer` and converging through the
 * Automerge sync protocol the relay forwards.
 */

export {
  type RelayConvergenceTarget,
  type WaitForRelayConvergenceOptions,
  waitForRelayConvergence,
} from "./wait-for-relay-convergence";
export { relayStats, type WithRepoServerResult, withRepoServer } from "./with-repo-server";
