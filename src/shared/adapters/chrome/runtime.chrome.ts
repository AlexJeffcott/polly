// Chrome runtime adapter implementation

import type { MessageSender, PortAdapter, RuntimeAdapter } from "../runtime.adapter";

export class ChromeRuntimeAdapter implements RuntimeAdapter {
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
    chrome.runtime.onMessage.addListener((message, sender, sendResponse) => {
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
    });
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
