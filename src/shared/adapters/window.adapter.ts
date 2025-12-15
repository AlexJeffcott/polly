// Window adapter interface (wraps window for content/page script communication)

export interface WindowAdapter {
  /**
   * Post message to window
   */
  postMessage(message: unknown, targetOrigin: string): void;

  /**
   * Listen for messages
   */
  addEventListener(type: "message", listener: (event: MessageEvent) => void): void;

  /**
   * Remove message listener
   */
  removeEventListener(type: "message", listener: (event: MessageEvent) => void): void;
}
