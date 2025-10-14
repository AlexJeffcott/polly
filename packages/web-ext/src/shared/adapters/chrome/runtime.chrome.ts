// Chrome runtime adapter implementation

import type { MessageSender, PortAdapter, RuntimeAdapter } from "../runtime.adapter";

export class ChromeRuntimeAdapter implements RuntimeAdapter {
  private messageListeners = new Map<Function, Function>();
  private static listenerCount = 0;

  sendMessage<T>(message: T): Promise<unknown> {
    return chrome.runtime.sendMessage(message);
  }

  onMessage(
    callback: (
      message: unknown,
      sender: MessageSender,
      sendResponse: (response: unknown) => void
    ) => undefined | boolean
  ): void {
    const wrappedCallback = (
      message: unknown,
      sender: chrome.runtime.MessageSender,
      sendResponse: (response?: unknown) => void
    ) => {
      const mappedSender: MessageSender = {
        ...(sender.tab && {
          tab: {
            id: sender.tab.id ?? 0,
            url: sender.tab.url ?? "",
            title: sender.tab.title ?? "",
          },
        }),
        ...(sender.frameId !== undefined && { frameId: sender.frameId }),
        ...(sender.url && { url: sender.url }),
      };
      return callback(message, mappedSender, sendResponse);
    };

    this.messageListeners.set(callback, wrappedCallback);
    // Chrome's listener signature uses void | boolean, ours uses undefined | boolean
    // These are compatible - undefined is assignable to void for return types
    chrome.runtime.onMessage.addListener(
      wrappedCallback as (
        message: unknown,
        sender: chrome.runtime.MessageSender,
        sendResponse: (response?: unknown) => void
      ) => void | boolean
    );

    // Track listener count and warn if multiple listeners registered
    ChromeRuntimeAdapter.listenerCount++;

    if (ChromeRuntimeAdapter.listenerCount > 1) {
      console.warn(
        `⚠️  WARNING: ${ChromeRuntimeAdapter.listenerCount} chrome.runtime.onMessage listeners registered!\n\n` +
          `Multiple listeners will cause message handlers to execute multiple times.\n` +
          `This is usually caused by:\n` +
          `  1. Creating both MessageBus and MessageRouter with separate listeners\n` +
          `  2. Calling createBackground() multiple times\n` +
          `  3. Calling getMessageBus('background') after createBackground()\n\n` +
          `Fix: In background scripts, use createBackground() ONCE at startup.\n` +
          `Do not call getMessageBus('background') separately.`
      );
    }
  }

  removeMessageListener(
    callback: (
      message: unknown,
      sender: MessageSender,
      sendResponse: (response: unknown) => void
    ) => undefined | boolean
  ): void {
    const wrappedCallback = this.messageListeners.get(callback);
    if (wrappedCallback) {
      // Type-safe cast: wrappedCallback is stored with compatible signature
      chrome.runtime.onMessage.removeListener(
        wrappedCallback as (
          message: unknown,
          sender: chrome.runtime.MessageSender,
          sendResponse: (response?: unknown) => void
        ) => void | boolean
      );
      this.messageListeners.delete(callback);

      // Decrement listener count
      ChromeRuntimeAdapter.listenerCount = Math.max(0, ChromeRuntimeAdapter.listenerCount - 1);
    }
  }

  connect(name: string): PortAdapter {
    const port = chrome.runtime.connect({ name });
    return new ChromePortAdapter(port);
  }

  onConnect(callback: (port: PortAdapter) => void): void {
    chrome.runtime.onConnect.addListener((port) => {
      callback(new ChromePortAdapter(port));
    });
  }

  getURL(path: string): string {
    return chrome.runtime.getURL(path);
  }

  getId(): string {
    return chrome.runtime.id;
  }

  openOptionsPage(): void {
    chrome.runtime.openOptionsPage();
  }
}

class ChromePortAdapter implements PortAdapter {
  private listeners = {
    message: new Set<(message: unknown) => void>(),
    disconnect: new Set<() => void>(),
  };

  constructor(private port: chrome.runtime.Port) {
    // Set up Chrome port listeners
    this.port.onMessage.addListener((message) => {
      for (const callback of this.listeners.message) {
        callback(message);
      }
    });

    this.port.onDisconnect.addListener(() => {
      for (const callback of this.listeners.disconnect) {
        callback();
      }
    });
  }

  get name(): string {
    return this.port.name;
  }

  postMessage(message: unknown): void {
    this.port.postMessage(message);
  }

  onMessage(callback: (message: unknown) => void): void {
    this.listeners.message.add(callback);
  }

  onDisconnect(callback: () => void): void {
    this.listeners.disconnect.add(callback);
  }

  disconnect(): void {
    this.port.disconnect();
  }
}
