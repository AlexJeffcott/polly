import type { MessageSender, PortAdapter, RuntimeAdapter } from "@/shared/adapters/runtime.adapter";

export interface MockPort extends PortAdapter {
  _listeners: Set<(message: unknown) => void>;
  _disconnectListeners: Set<() => void>;
}

export function createMockPort(name: string): MockPort {
  const listeners = new Set<(message: unknown) => void>();
  const disconnectListeners = new Set<() => void>();

  return {
    name,
    onMessage: (callback) => listeners.add(callback),
    onDisconnect: (callback) => disconnectListeners.add(callback),
    postMessage: (message) => {
      for (const listener of listeners) {
        listener(message);
      }
    },
    disconnect: () => {
      for (const listener of disconnectListeners) {
        listener();
      }
    },
    _listeners: listeners,
    _disconnectListeners: disconnectListeners,
  };
}

export interface MockRuntime extends RuntimeAdapter {
  id: string;
  _messageListeners: Set<
    (message: unknown, sender: MessageSender, sendResponse: (response: unknown) => void) => void
  >;
  _connectListeners: Set<(port: PortAdapter) => void>;
}

export function createMockRuntime(id = "test-extension-id"): MockRuntime {
  const messageListeners = new Set<
    (message: unknown, sender: MessageSender, sendResponse: (response: unknown) => void) => void
  >();
  const connectListeners = new Set<(port: PortAdapter) => void>();

  return {
    id,
    sendMessage: async <T>(message: T): Promise<unknown> => {
      // Check if this is a response message
      if (typeof message === "object" && message !== null && "success" in message) {
        // This is a response, route it back to all listeners
        for (const listener of messageListeners) {
          listener(message, { url: "" }, () => {});
        }
        return undefined;
      }

      // This is a request, call listeners and wait for response
      if (messageListeners.size === 0) {
        return undefined;
      }

      return new Promise((resolve) => {
        // Call the first listener (Chrome only uses first response)
        const listener = messageListeners.values().next().value;
        if (listener) {
          const result = listener(message, { url: "" }, (res) => {
            resolve(res);
          });
          // If listener returns true, it will send response asynchronously
          // If it doesn't return true or returns undefined, resolve immediately
          if (result === undefined || result === false) {
            resolve(undefined);
          }
        } else {
          resolve(undefined);
        }
      });
    },
    onMessage: (
      callback: (
        message: unknown,
        sender: MessageSender,
        sendResponse: (response: unknown) => void
      ) => void
    ) => {
      messageListeners.add(callback);
    },
    connect: (name: string): PortAdapter => {
      const port = createMockPort(name);
      for (const listener of connectListeners) {
        listener(port);
      }
      return port;
    },
    onConnect: (callback: (port: PortAdapter) => void) => {
      connectListeners.add(callback);
    },
    getURL: (path: string): string => {
      return `chrome-extension://${id}/${path}`;
    },
    getId: (): string => {
      return id;
    },
    openOptionsPage: (): void => {
      // Mock implementation - no-op for tests
    },
    _messageListeners: messageListeners,
    _connectListeners: connectListeners,
  };
}
