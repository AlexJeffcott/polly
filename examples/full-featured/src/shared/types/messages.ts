/**
 * Custom message types for full-featured example
 */

import type { ExtensionMessage } from "@fairfox/polly/types";

export interface Bookmark {
  id: string;
  url: string;
  title: string;
  timestamp: number;
}

export interface User {
  username: string;
  token?: string;
  loginTime?: number;
}

export interface Settings {
  theme: "auto" | "light" | "dark";
  autoSync: boolean;
  debugMode: boolean;
  notifications: boolean;
  apiEndpoint: string;
  refreshInterval: number;
}

export type CustomMessages =
  // Authentication
  | { type: "USER_LOGIN"; username: string; token: string }
  | { type: "USER_LOGOUT" }
  // Bookmarks
  | { type: "BOOKMARK_ADD"; url: string; title: string }
  | { type: "BOOKMARK_REMOVE"; id: string }
  | { type: "GET_BOOKMARKS" }
  // Tabs
  | { type: "TAB_GET_CURRENT" }
  | { type: "TAB_OPEN"; url: string }
  // Settings
  | {
      type: "SETTINGS_UPDATE";
      theme?: "auto" | "light" | "dark";
      autoSync?: boolean;
      debugMode?: boolean;
      notifications?: boolean;
      apiEndpoint?: string;
      refreshInterval?: number;
    }
  | { type: "GET_SETTINGS" };

// Combined message type - includes both framework and custom messages
export type AllMessages = ExtensionMessage | CustomMessages;
