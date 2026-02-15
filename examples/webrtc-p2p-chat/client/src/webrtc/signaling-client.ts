import type { SignalingMessage } from "../types";

type MessageHandler = (message: SignalingMessage) => void;

/**
 * SignalingClient - Manages WebSocket connection to signaling server
 *
 * Responsibilities:
 * - Connect to signaling server
 * - Send/receive signaling messages
 * - Handle reconnection on disconnect
 * - Notify handlers of incoming messages
 */
export class SignalingClient {
  private ws: WebSocket | null = null;
  private handlers = new Set<MessageHandler>();
  private reconnectAttempts = 0;
  private maxReconnectAttempts = 5;
  private reconnectDelay = 1000;
  private reconnectTimeout: number | null = null;

  constructor(private url: string) {}

  /**
   * Connect to signaling server
   */
  connect(): Promise<void> {
    return new Promise((resolve, reject) => {
      try {
        this.ws = new WebSocket(this.url);

        this.ws.onopen = () => {
          console.log("✅ Signaling connected");
          this.reconnectAttempts = 0;
          resolve();
        };

        this.ws.onmessage = (event) => {
          try {
            const message = JSON.parse(event.data) as SignalingMessage;
            console.log("📨 Received signaling:", message.type);
            this.handlers.forEach((h) => h(message));
          } catch (error) {
            console.error("Failed to parse signaling message:", error);
          }
        };

        this.ws.onerror = (error) => {
          console.error("❌ Signaling error:", error);
          reject(error);
        };

        this.ws.onclose = () => {
          console.log("🔌 Signaling disconnected");
          this.attemptReconnect();
        };
      } catch (error) {
        reject(error);
      }
    });
  }

  /**
   * Send a message to the signaling server
   */
  send(message: SignalingMessage) {
    if (this.ws?.readyState === WebSocket.OPEN) {
      this.ws.send(JSON.stringify(message));
      console.log("📤 Sent signaling:", message.type);
    } else {
      console.error("❌ Cannot send, signaling not connected");
    }
  }

  /**
   * Register a message handler
   * Returns unsubscribe function
   */
  onMessage(handler: MessageHandler): () => void {
    this.handlers.add(handler);
    return () => this.handlers.delete(handler);
  }

  /**
   * Disconnect from signaling server
   */
  disconnect() {
    if (this.reconnectTimeout) {
      clearTimeout(this.reconnectTimeout);
      this.reconnectTimeout = null;
    }

    if (this.ws) {
      this.ws.close();
      this.ws = null;
    }

    this.handlers.clear();
  }

  /**
   * Check if connected
   */
  get isConnected(): boolean {
    return this.ws?.readyState === WebSocket.OPEN;
  }

  /**
   * Attempt to reconnect after disconnect
   */
  private attemptReconnect() {
    if (this.reconnectAttempts >= this.maxReconnectAttempts) {
      console.error("❌ Max reconnection attempts reached");
      return;
    }

    this.reconnectAttempts++;
    const delay = this.reconnectDelay * 2 ** (this.reconnectAttempts - 1);

    console.log(`🔄 Reconnecting in ${delay}ms (attempt ${this.reconnectAttempts})`);

    this.reconnectTimeout = window.setTimeout(() => {
      this.connect().catch(console.error);
    }, delay);
  }
}
