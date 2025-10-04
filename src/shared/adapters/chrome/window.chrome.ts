// Chrome window adapter implementation

import type { WindowAdapter } from "../window.adapter";

export class ChromeWindowAdapter implements WindowAdapter {
  postMessage(message: unknown, targetOrigin: string): void {
    window.postMessage(message, targetOrigin);
  }

  addEventListener(type: "message", listener: (event: MessageEvent) => void): void {
    window.addEventListener(type, listener as EventListener);
  }

  removeEventListener(type: "message", listener: (event: MessageEvent) => void): void {
    window.removeEventListener(type, listener as EventListener);
  }
}
