// Runtime adapter interface (wraps chrome.runtime)

export interface RuntimeAdapter {
  /**
   * Send a one-off message to another context
   */
  sendMessage<T>(message: T): Promise<unknown>;

  /**
   * Listen for one-off messages
   * Return true from callback to indicate async response
   */
  onMessage(
    callback: (
      message: unknown,
      sender: MessageSender,
      sendResponse: (response: unknown) => void
    ) => undefined | boolean
  ): void;

  /**
   * Remove a previously registered message listener
   */
  removeMessageListener(
    callback: (
      message: unknown,
      sender: MessageSender,
      sendResponse: (response: unknown) => void
    ) => undefined | boolean
  ): void;

  /**
   * Create a long-lived connection
   */
  connect(name: string): PortAdapter;

  /**
   * Listen for incoming connections
   */
  onConnect(callback: (port: PortAdapter) => void): void;

  /**
   * Get URL for extension resource
   */
  getURL(path: string): string;

  /**
   * Get extension ID
   */
  getId(): string;

  /**
   * Open the extension's options page
   */
  openOptionsPage(): void;
}

export interface PortAdapter {
  /**
   * Port name
   */
  readonly name: string;

  /**
   * Send message through port
   */
  postMessage(message: unknown): void;

  /**
   * Listen for messages on port
   */
  onMessage(callback: (message: unknown) => void): void;

  /**
   * Listen for disconnection
   */
  onDisconnect(callback: () => void): void;

  /**
   * Disconnect port
   */
  disconnect(): void;
}

export interface MessageSender {
  tab?: {
    id: number;
    url: string;
    title: string;
  };
  frameId?: number;
  url?: string;
}
