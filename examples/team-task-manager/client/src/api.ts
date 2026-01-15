// API client using Eden treaty for type-safe communication
import { treaty } from "@elysiajs/eden";
import type { App } from "../../server/src/index";
import { currentUser, workspace, tasks } from "./state";

// @ts-ignore - injected at build time
const API_URL = process.env.API_URL || "https://localhost:3000";
// @ts-ignore - injected at build time
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

  async createWorkspace(
    id: string,
    name: string,
    creatorId: string
  ): Promise<APIResponse> {
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

  async updateTask(
    taskId: string,
    encrypted: string,
    workspaceId: string
  ): Promise<APIResponse> {
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
    const { data, error} = await client.api.tasks({ id: taskId }).delete({
      workspaceId,
    });

    if (error) {
      return { error: error.value as string };
    }

    return data as APIResponse;
  }

  async getTasks(workspaceId: string): Promise<APIResponse<{ tasks: any[] }>> {
    const { data, error } = await client.api.workspaces({ id: workspaceId }).tasks.get();

    if (error) {
      return { error: error.value as string, tasks: [] };
    }

    return data as APIResponse<{ tasks: any[] }>;
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

  async getComments(
    taskId: string,
    workspaceId: string
  ): Promise<APIResponse<{ comments: any[] }>> {
    const { data, error } = await client.api.tasks({ taskId }).comments.get({
      query: { workspaceId },
    });

    if (error) {
      return { error: error.value as string, comments: [] };
    }

    return data as APIResponse<{ comments: any[] }>;
  }

  // WebSocket for real-time updates
  connect(workspaceId: string, userId: string) {
    if (this.ws?.readyState === WebSocket.OPEN) {
      return;
    }

    this.ws = new WebSocket(WS_URL);

    this.ws.onopen = () => {
      console.log("WebSocket connected");
      this.ws?.send(JSON.stringify({ type: "join", workspaceId, userId }));
    };

    this.ws.onmessage = (event) => {
      const data = JSON.parse(event.data);
      console.log("WebSocket message:", data);

      // Call registered handlers
      for (const handler of this.messageHandlers.values()) {
        handler(data);
      }
    };

    this.ws.onclose = () => {
      console.log("WebSocket disconnected");
      // Reconnect after delay
      setTimeout(() => this.connect(workspaceId, userId), 2000);
    };

    this.ws.onerror = (error) => {
      console.error("WebSocket error:", error);
    };
  }

  disconnect() {
    if (this.ws) {
      this.ws.send(JSON.stringify({ type: "leave" }));
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
