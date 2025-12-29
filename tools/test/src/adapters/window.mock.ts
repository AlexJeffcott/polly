import type { WindowAdapter } from "@/shared/adapters/window.adapter";

export interface MockWindow extends WindowAdapter {
  _messageListeners: Set<(event: MessageEvent) => void>;
}

export function createMockWindow(): MockWindow {
  const messageListeners = new Set<(event: MessageEvent) => void>();

  return {
    postMessage: (message: unknown, targetOrigin: string) => {
      const event = new MessageEvent("message", {
        data: message,
        origin: targetOrigin,
        source: null,
      });
      for (const listener of messageListeners) {
        listener(event);
      }
    },
    addEventListener: (type: string, listener: (event: MessageEvent) => void) => {
      if (type === "message") {
        messageListeners.add(listener);
      }
    },
    removeEventListener: (type: string, listener: (event: MessageEvent) => void) => {
      if (type === "message") {
        messageListeners.delete(listener);
      }
    },
    _messageListeners: messageListeners,
  };
}
