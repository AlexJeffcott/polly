/**
 * Coverage for the MessageBus surface the core suite leaves untested: the
 * explicit-target send wrappers (sendToBackground/Popup/Options/DevTools/
 * SidePanel/ContentScript/AllTabs), bulk handler registration, the user error
 * hook, and the runtime-constraint state accessor.
 *
 * The wrappers are thin — each forwards to send({ target }) — but the target
 * each encodes is real routing behaviour. Spying sendMessage captures the
 * routed envelope so a wrapper that learns to point at the wrong context fails
 * here instead of in a misdelivered message at runtime.
 */

import { afterEach, beforeEach, expect, mock, test } from "bun:test";
import { createMockAdapters, waitFor } from "@fairfox/polly/test";
import { globalExecutionTracker } from "@/shared/lib/handler-execution-tracker";
import { MessageBus } from "@/shared/lib/message-bus";
import type { ExtensionMessage } from "@/shared/types/messages";

let bus: MessageBus;

beforeEach(() => {
  bus = new MessageBus("background", createMockAdapters());
});

afterEach(() => {
  bus.destroy();
  globalExecutionTracker.reset();
});

/** Replace sendMessage with a capturing spy and return it. send() calls
 *  sendMessage synchronously before awaiting a response, so the routed
 *  envelope is captured even though we never await (and never resolve) the
 *  pending request — destroy() clears it in afterEach. */
function spyOnSend() {
  const spy = mock();
  bus.sendMessage = spy;
  return spy;
}

const ROUTERS: ReadonlyArray<{
  name: string;
  target: string;
  send: (b: MessageBus, p: ExtensionMessage) => unknown;
}> = [
  { name: "sendToBackground", target: "background", send: (b, p) => b.sendToBackground(p) },
  { name: "sendToPopup", target: "popup", send: (b, p) => b.sendToPopup(p) },
  { name: "sendToOptions", target: "options", send: (b, p) => b.sendToOptions(p) },
  { name: "sendToDevTools", target: "devtools", send: (b, p) => b.sendToDevTools(p) },
  { name: "sendToSidePanel", target: "sidepanel", send: (b, p) => b.sendToSidePanel(p) },
];

for (const { name, target, send } of ROUTERS) {
  test(`${name} routes to ${target}`, () => {
    const spy = spyOnSend();
    send(bus, { type: "SETTINGS_GET" });

    const envelope = spy.mock.calls[0]?.[0];
    expect(envelope?.targets).toEqual([target]);
  });
}

test("sendToContentScript routes to content with the tab id", () => {
  const spy = spyOnSend();
  bus.sendToContentScript(42, { type: "DOM_QUERY", selector: ".x" });

  const envelope = spy.mock.calls[0]?.[0];
  expect(envelope?.targets).toEqual(["content"]);
  expect(envelope?.tabId).toBe(42);
});

test("sendToAllTabs fans out one content message per open tab", async () => {
  await bus.adapters.tabs.create({ url: "https://a.test" });
  await bus.adapters.tabs.create({ url: "https://b.test" });
  const spy = spyOnSend();

  bus.sendToAllTabs({ type: "DOM_QUERY", selector: ".x" });
  await waitFor(10);

  expect(spy).toHaveBeenCalledTimes(2);
  for (const call of spy.mock.calls) {
    expect(call[0]?.targets).toEqual(["content"]);
  }
});

test("registerHandlers registers every defined handler and skips undefined", async () => {
  const settings = mock(async () => ({ settings: {} }));
  const dom = mock(async () => ({ elements: [] }));
  bus.registerHandlers({ SETTINGS_GET: settings, DOM_QUERY: dom, NOOP: undefined });

  await bus.handleMessage({
    id: "1",
    source: "content",
    targets: ["background"],
    timestamp: Date.now(),
    payload: { type: "SETTINGS_GET" },
  });

  expect(settings).toHaveBeenCalled();
  expect(dom).not.toHaveBeenCalled();
});

test("onError handlers are notified when a send times out", async () => {
  const onErr = mock();
  bus.onError(onErr);

  await expect(
    bus.send({ type: "SETTINGS_GET" }, { target: "background", timeout: 30 })
  ).rejects.toThrow();

  expect(onErr).toHaveBeenCalled();
  expect(onErr.mock.calls[0]?.[0]).toBeInstanceOf(Error);
});

test("setStateAccessor accepts an accessor without throwing", () => {
  expect(() => bus.setStateAccessor(() => ({ loggedIn: true }))).not.toThrow();
});
