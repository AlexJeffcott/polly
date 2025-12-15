// Application state type for WebSocket server

export interface AppState {
  authenticated: boolean
  subscriptions: Set<string>
  messageCount: number
}
