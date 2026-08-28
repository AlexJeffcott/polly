/**
 * Worker half of the approach-B spike for polly#111. See
 * `spike-111-worker-apply.ts` for what is being measured.
 *
 * The worker owns the Automerge apply. It answers two requests:
 *
 *   load          apply the snapshot, reply with the sentinel only
 *   materialise   reply with the whole document value, which is what a
 *                 `$meshState` consumer on the main thread reads
 */
import * as Automerge from "@automerge/automerge";

interface LargeDocShape {
  sentinel: string;
  payload: string;
}

let doc: Automerge.Doc<LargeDocShape> | undefined;

declare const self: Worker;

self.onmessage = (event: MessageEvent) => {
  const message = event.data;
  if (message?.kind === "load") {
    const started = performance.now();
    doc = Automerge.load<LargeDocShape>(message.bytes);
    self.postMessage({
      kind: "loaded",
      sentinel: doc.sentinel,
      applyMs: performance.now() - started,
    });
    return;
  }
  if (message?.kind === "materialise") {
    if (!doc) {
      self.postMessage({ kind: "materialised", error: "no document loaded" });
      return;
    }
    // A structured clone of the whole value — the naive bridge a
    // main-thread `$meshState` read would need.
    self.postMessage({
      kind: "materialised",
      value: { sentinel: doc.sentinel, payload: doc.payload },
    });
  }
};
