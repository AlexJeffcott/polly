// Test fixture: WebSocket server state types

export type AppState = {
  authenticated: boolean;
  subscriptions: string[];
  messageCount: number;
};

export type ServerState = {
  connections: number;
  messages: string[];
};

export type ClientState = {
  connected: boolean;
  userId: string | null;
};
