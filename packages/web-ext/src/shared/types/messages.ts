// Type definitions for all messages in the extension

/**
 * Base message interface that all messages must satisfy.
 * This allows users to define custom messages alongside framework messages.
 */
export interface BaseMessage {
  type: string
}

export type Context =
  | "background"
  | "content"
  | "page"
  | "devtools"
  | "popup"
  | "options"
  | "sidepanel"
  | "offscreen";

// All contexts (useful for broadcast)
export const ALL_CONTEXTS: Context[] = [
  "background",
  "content",
  "page",
  "devtools",
  "popup",
  "options",
  "sidepanel",
  "offscreen",
] as const;

// Settings schema
export type Settings = {
  theme: "light" | "dark" | "auto";
  autoSync: boolean;
  debugMode: boolean;
  notifications: boolean;
  apiEndpoint: string;
  refreshInterval: number;
};

export const defaultSettings: Settings = {
  theme: "auto",
  autoSync: true,
  debugMode: false,
  notifications: true,
  apiEndpoint: process.env["RELEASE_SPACE_URL"] || "https://api.example.com",
  refreshInterval: 60000,
};

// Logging types
export type LogLevel = "debug" | "info" | "warn" | "error";

export type LogEntry = {
  id: string;
  level: LogLevel;
  message: string;
  context?: Record<string, unknown>;
  error?: string;
  stack?: string;
  source: Context;
  timestamp: number;
};

// All possible messages (discriminated union)
export type ExtensionMessage =
  // DOM Operations (handled by Content Script)
  | { type: "DOM_QUERY"; selector: string }
  | { type: "DOM_UPDATE"; selector: string; content: string }
  | {
      type: "DOM_INSERT";
      position: "beforebegin" | "afterbegin" | "beforeend" | "afterend";
      html: string;
    }
  | { type: "DOM_REMOVE"; selector: string }

  // Page Script Operations (handled by Page Script)
  | { type: "PAGE_EVAL"; code: string }
  | { type: "PAGE_GET_VAR"; varName: string }
  | { type: "PAGE_CALL_FN"; fnName: string; args: unknown[] }
  | { type: "PAGE_SET_VAR"; varName: string; value: unknown }

  // API Operations (handled by Background)
  | {
      type: "API_REQUEST";
      endpoint: string;
      method: "GET" | "POST" | "PUT" | "DELETE";
      body?: unknown;
      headers?: Record<string, string>;
    }
  | {
      type: "API_BATCH";
      requests: Array<{ endpoint: string; method: string; body?: unknown }>;
    }

  // Clipboard Operations (handled by Offscreen)
  | { type: "CLIPBOARD_WRITE"; text: string }
  | { type: "CLIPBOARD_WRITE_HTML"; html: string }
  | { type: "CLIPBOARD_WRITE_RICH"; data: { text: string; html: string } }
  | { type: "CLIPBOARD_READ" }

  // Context Menu (handled by Background)
  | {
      type: "CONTEXT_MENU_CLICKED";
      menuId: string;
      info: chrome.contextMenus.OnClickData;
      tabId: number;
    }
  | {
      type: "CONTEXT_MENU_CREATE";
      id: string;
      title: string;
      contexts: chrome.contextMenus.ContextType[];
    }
  | { type: "CONTEXT_MENU_REMOVE"; id: string }

  // State Sync (broadcast) - Internal only, handled by state primitives
  | {
      type: "STATE_SYNC";
      key: string;
      value: unknown;
      clock: number;
    }

  // Tab Operations (handled by Background)
  | { type: "TAB_QUERY"; queryInfo: chrome.tabs.QueryInfo }
  | { type: "TAB_GET_CURRENT" }
  | { type: "TAB_RELOAD"; tabId: number }

  // DevTools Operations
  | { type: "DEVTOOLS_INSPECT_ELEMENT"; selector: string }
  | {
      type: "DEVTOOLS_LOG";
      level: "log" | "warn" | "error";
      message: string;
      data?: unknown;
    }

  // Logging (handled by Background LogStore)
  | {
      type: "LOG";
      level: LogLevel;
      message: string;
      context?: Record<string, unknown>;
      error?: string;
      stack?: string;
      source: Context;
      timestamp: number;
    }
  | {
      type: "LOGS_GET";
      filters?: {
        level?: LogLevel;
        source?: Context;
        since?: number;
        limit?: number;
      };
    }
  | { type: "LOGS_CLEAR" }
  | { type: "LOGS_EXPORT" }

  // Test Messages (only used in tests)
  | { type: "TEST_MESSAGE"; data?: unknown }
  | { type: "TEST"; iteration?: number }
  | { type: "CUSTOM_MESSAGE"; data?: unknown }
  | { type: "SETTINGS_GET" }
  | {
      type: "SIGNAL_UPDATE";
      key?: string;
      value?: unknown;
      signalId?: string;
      source?: Context;
    }
  | {
      type: "USER_DATA";
      password?: string;
      apiKey?: string;
      [key: string]: unknown;
    };

// Response types for each message
export type MessageResponse<T extends BaseMessage> =
  T extends ExtensionMessage ?
  // DOM Operations
  T extends { type: "DOM_QUERY" }
    ? {
        elements: Array<{
          tag: string;
          text: string;
          html: string;
          attrs: Record<string, string>;
          rect?: DOMRect;
        }>;
      }
    : T extends { type: "DOM_UPDATE" }
      ? { success: boolean }
      : T extends { type: "DOM_INSERT" }
        ? { success: boolean }
        : T extends { type: "DOM_REMOVE" }
          ? { success: boolean; count: number }
          : // Page Script Operations
            T extends { type: "PAGE_EVAL" }
            ? { result: unknown; error?: string }
            : T extends { type: "PAGE_GET_VAR" }
              ? { value: unknown; exists: boolean }
              : T extends { type: "PAGE_CALL_FN" }
                ? { result: unknown; error?: string }
                : T extends { type: "PAGE_SET_VAR" }
                  ? { success: boolean }
                  : // API Operations
                    T extends { type: "API_REQUEST" }
                    ? {
                        data: unknown;
                        status: number;
                        statusText: string;
                        headers: Record<string, string>;
                        error?: string;
                      }
                    : T extends { type: "API_BATCH" }
                      ? {
                          results: Array<{
                            data: unknown;
                            status: number;
                            error?: string;
                          }>;
                        }
                      : // Clipboard Operations
                        T extends { type: "CLIPBOARD_WRITE" }
                        ? { success: boolean }
                        : T extends { type: "CLIPBOARD_WRITE_HTML" }
                          ? { success: boolean }
                          : T extends { type: "CLIPBOARD_WRITE_RICH" }
                            ? { success: boolean }
                            : T extends { type: "CLIPBOARD_READ" }
                              ? { text: string }
                              : // Context Menu
                                T extends { type: "CONTEXT_MENU_CLICKED" }
                                ? undefined
                                : T extends { type: "CONTEXT_MENU_CREATE" }
                                  ? { success: boolean }
                                  : T extends { type: "CONTEXT_MENU_REMOVE" }
                                    ? { success: boolean }
                                    : // State Sync
                                      T extends { type: "STATE_SYNC" }
                                      ? undefined
                                      : // Tab Operations
                                        T extends { type: "TAB_QUERY" }
                                        ? { tabs: chrome.tabs.Tab[] }
                                        : T extends {
                                              type: "TAB_GET_CURRENT";
                                            }
                                          ? { tab: chrome.tabs.Tab }
                                          : T extends {
                                                type: "TAB_RELOAD";
                                              }
                                            ? { success: boolean }
                                            : // DevTools Operations
                                              T extends {
                                                  type: "DEVTOOLS_INSPECT_ELEMENT";
                                                }
                                              ? {
                                                  success: boolean;
                                                }
                                              : T extends {
                                                    type: "DEVTOOLS_LOG";
                                                  }
                                                ? undefined
                                                : // Logging Operations
                                                  T extends {
                                                      type: "LOG";
                                                    }
                                                  ? {
                                                      success: boolean;
                                                    }
                                                  : T extends {
                                                        type: "LOGS_GET";
                                                      }
                                                    ? {
                                                        logs: LogEntry[];
                                                      }
                                                    : T extends {
                                                          type: "LOGS_CLEAR";
                                                        }
                                                      ? {
                                                          success: boolean;
                                                          count: number;
                                                        }
                                                      : T extends {
                                                            type: "LOGS_EXPORT";
                                                          }
                                                        ? {
                                                            json: string;
                                                            count: number;
                                                          }
                                                        : T extends {
                                                              type: "SETTINGS_GET";
                                                            }
                                                          ? {
                                                              settings: unknown;
                                                            }
                                                          : undefined
  : unknown; // For custom messages outside ExtensionMessage

// Message handler mapping (which context handles which message)
// Can be a single context or an array for multi-target routing
export type MessageHandler = {
  DOM_QUERY: "content";
  DOM_UPDATE: "content";
  DOM_INSERT: "content";
  DOM_REMOVE: "content";

  PAGE_EVAL: "page";
  PAGE_GET_VAR: "page";
  PAGE_CALL_FN: "page";
  PAGE_SET_VAR: "page";

  API_REQUEST: "background";
  API_BATCH: "background";

  CLIPBOARD_WRITE: "offscreen";
  CLIPBOARD_WRITE_HTML: "offscreen";
  CLIPBOARD_WRITE_RICH: "offscreen";
  CLIPBOARD_READ: "offscreen";

  CONTEXT_MENU_CLICKED: "background";
  CONTEXT_MENU_CREATE: "background";
  CONTEXT_MENU_REMOVE: "background";

  STATE_SYNC: Context[];  // Broadcast to all contexts

  TAB_QUERY: "background";
  TAB_GET_CURRENT: "background";
  TAB_RELOAD: "background";

  DEVTOOLS_INSPECT_ELEMENT: "content";
  DEVTOOLS_LOG: "background";

  LOG: "background";
  LOGS_GET: "background";
  LOGS_CLEAR: "background";
  LOGS_EXPORT: "background";
};

// Routed message envelope
export type RoutedMessage<T extends BaseMessage = ExtensionMessage> = {
  id: string; // Correlation ID (UUID)
  source: Context; // Which context sent it
  targets: Context[]; // Which contexts should receive this (can be multiple)
  tabId?: number; // Required for per-tab contexts
  timestamp: number; // When it was sent
  payload: T; // The actual message
};

// Routed response envelope
export type RoutedResponse<T extends BaseMessage = ExtensionMessage> = {
  id: string; // Matches request ID
  success: boolean; // Whether operation succeeded
  data?: MessageResponse<T>; // Response data
  error?: string; // Error message if failed
  timestamp: number; // When response was sent
};
