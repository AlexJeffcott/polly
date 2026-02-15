// API client using Eden treaty for type-safe communication
import { treaty } from "@elysiajs/eden";
import type { App } from "../../server/src/index";
import { currentUser, tasks, workspace } from "./state";

// @ts-expect-error - injected at build time
const API_URL = process.env.API_URL || "https://localhost:3000";
// @ts-expect-error - injected at build time
const WS_URL = process.env.WS_URL || "wss://localhost:3000/ws";

// Create Eden treaty client with full type safety
const client = treaty<App>(API_URL);

export type APIResponse<T = any> = {
  success?: boolean;
  error?: string;
} & T;

/**
 * API Client class wrapping Eden treaty
 * Provides a clean interface matching our previous API while using treaty under the hood
 */
export class APIClient {
  private ws: WebSocket | null = null;
  private messageHandlers = new Map<string, (data: any) => void>();

  async createWorkspace(id: string, name: string, creatorId: string): Promise<APIResponse> {
    const { data, error } = await client.api.workspaces.post({
      id,
      name,
      creatorId,
    });

    if (error) {
      return { error: error.value as string };
    }

    return data as APIResponse;
  }

  async getWorkspace(id: string): Promise<APIResponse> {
    const { data, error } = await client.api.workspaces({ id }).get();

    if (error) {
      return { error: error.value as string };
    }

    return data as APIResponse;
  }

  async addMember(workspaceId: string, userId: string): Promise<APIResponse> {
    const { data, error } = await client.api.workspaces({ id: workspaceId }).members.post({
      userId,
    });

    if (error) {
      return { error: error.value as string };
    }

    return data as APIResponse;
  }

  async createTask(
    id: string,
    encrypted: string,
    from: string,
    workspaceId: string
  ): Promise<APIResponse> {
    const { data, error } = await client.api.tasks.post({
      id,
      encrypted,
      from,
      workspaceId,
    });

    if (error) {
      return { error: error.value as string };
    }

    return data as APIResponse;
  }

  async updateTask(taskId: string, encrypted: string, workspaceId: string): Promise<APIResponse> {
    const { data, error } = await client.api.tasks({ id: taskId }).patch({
      encrypted,
      workspaceId,
    });

    if (error) {
      return { error: error.value as string };
    }

    return data as APIResponse;
  }

  async deleteTask(taskId: string, workspaceId: string): Promise<APIResponse> {
    const { data, error } = await client.api.tasks({ id: taskId }).delete({
      workspaceId,
    });

    if (error) {
      return { error: error.value as string };
    }

    return data as APIResponse;
  }

  async createComment(
    id: string,
    taskId: string,
    encrypted: string,
    from: string,
    workspaceId: string
  ): Promise<APIResponse> {
    const { data, error } = await client.api.comments.post({
      id,
      taskId,
      encrypted,
      from,
      workspaceId,
    });

    if (error) {
      return { error: error.value as string };
    }

    return data as APIResponse;
  }

  async requestSync(workspaceId: string, userId: string): Promise<APIResponse> {
    const { data, error } = await client.api.sync.request.post({
      workspaceId,
      userId,
    });

    if (error) {
      return { error: error.value as string };
    }

    return data as APIResponse;
  }

  sendSyncResponse(targetUserId: string, tasks: any[], comments: any[]) {
    if (this.ws?.readyState === WebSocket.OPEN) {
      this.ws.send(
        JSON.stringify({
          type: "sync_response",
          workspaceId: workspace.value?.id,
          targetUserId,
          tasks,
          comments,
          timestamp: Date.now(),
        })
      );
    }
  }

  // WebSocket for real-time updates
  connect(workspaceId: string, userId: string) {
    console.log("[WS] connect() called with:", { workspaceId, userId });

    // Check if already connected or connecting
    if (this.ws?.readyState === WebSocket.OPEN || this.ws?.readyState === WebSocket.CONNECTING) {
      console.log("[WS] Already connected/connecting (state:", this.ws.readyState, "), skipping");
      return;
    }

    console.log("[WS] Connecting to:", WS_URL);
    this.ws = new WebSocket(WS_URL);

    this.ws.onopen = () => {
      console.log("[WS] WebSocket connected, sending join message");
      this.ws?.send(JSON.stringify({ type: "join", workspaceId, userId }));
    };

    this.ws.onmessage = (event) => {
      const data = JSON.parse(event.data);
      console.log("[WS] Received message:", data.type, data);

      // Handle sync requests from peers
      if (data.type === "sync_request") {
        console.log("[WS] Peer requesting sync, sending our tasks");
        // Another peer is requesting our data
        // Send them our local tasks and comments
        this.sendSyncResponse(
          data.requesterId,
          tasks.value,
          [] // comments.value when implemented
        );
      }

      // Call registered handlers
      console.log("[WS] Calling", this.messageHandlers.size, "registered handlers");
      for (const handler of this.messageHandlers.values()) {
        handler(data);
      }
    };

    this.ws.onclose = (event) => {
      console.log("[WS] WebSocket disconnected", {
        code: event.code,
        reason: event.reason,
        wasClean: event.wasClean,
      });
      // Reconnect after delay
      setTimeout(() => this.connect(workspaceId, userId), 2000);
    };

    this.ws.onerror = (error) => {
      // Don't log as error since reconnection will handle it
      console.warn("[WS] WebSocket error (will retry on close):", error);
    };
  }

  disconnect() {
    if (this.ws) {
      console.log("[WS] Disconnecting, current state:", this.ws.readyState);

      // Only send leave message if connection is open
      if (this.ws.readyState === WebSocket.OPEN) {
        try {
          this.ws.send(JSON.stringify({ type: "leave" }));
        } catch (error) {
          console.warn("[WS] Failed to send leave message:", error);
        }
      }

      this.ws.close();
      this.ws = null;
    }
  }

  onMessage(id: string, handler: (data: any) => void) {
    this.messageHandlers.set(id, handler);
    return () => this.messageHandlers.delete(id);
  }
}

// Export singleton instance
export const api = new APIClient();

// Also export the underlying treaty client for advanced use
export { client };
