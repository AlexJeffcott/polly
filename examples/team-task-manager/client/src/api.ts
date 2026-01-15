// API client for communicating with the zero-knowledge server

// @ts-ignore - injected at build time
const API_URL = process.env.API_URL || "https://localhost:3000";
// @ts-ignore - injected at build time
const WS_URL = process.env.WS_URL || "wss://localhost:3000/ws";

export type APIResponse<T = any> = {
  success?: boolean;
  error?: string;
} & T;

export class APIClient {
  private ws: WebSocket | null = null;
  private messageHandlers = new Map<string, (data: any) => void>();

  async createWorkspace(
    id: string,
    name: string,
    creatorId: string
  ): Promise<APIResponse> {
    const res = await fetch(`${API_URL}/api/workspaces`, {
      method: "POST",
      headers: { "Content-Type": "application/json" },
      body: JSON.stringify({ id, name, creatorId }),
    });
    return res.json();
  }

  async getWorkspace(id: string): Promise<APIResponse> {
    const res = await fetch(`${API_URL}/api/workspaces/${id}`);
    return res.json();
  }

  async addMember(workspaceId: string, userId: string): Promise<APIResponse> {
    const res = await fetch(`${API_URL}/api/workspaces/${workspaceId}/members`, {
      method: "POST",
      headers: { "Content-Type": "application/json" },
      body: JSON.stringify({ userId }),
    });
    return res.json();
  }

  async createTask(
    id: string,
    encrypted: string,
    from: string,
    workspaceId: string
  ): Promise<APIResponse> {
    const res = await fetch(`${API_URL}/api/tasks`, {
      method: "POST",
      headers: { "Content-Type": "application/json" },
      body: JSON.stringify({ id, encrypted, from, workspaceId }),
    });
    return res.json();
  }

  async updateTask(
    taskId: string,
    encrypted: string,
    workspaceId: string
  ): Promise<APIResponse> {
    const res = await fetch(`${API_URL}/api/tasks/${taskId}`, {
      method: "PATCH",
      headers: { "Content-Type": "application/json" },
      body: JSON.stringify({ encrypted, workspaceId }),
    });
    return res.json();
  }

  async deleteTask(taskId: string, workspaceId: string): Promise<APIResponse> {
    const res = await fetch(`${API_URL}/api/tasks/${taskId}`, {
      method: "DELETE",
      headers: { "Content-Type": "application/json" },
      body: JSON.stringify({ workspaceId }),
    });
    return res.json();
  }

  async getTasks(workspaceId: string): Promise<APIResponse<{ tasks: any[] }>> {
    const res = await fetch(`${API_URL}/api/workspaces/${workspaceId}/tasks`);
    return res.json();
  }

  async createComment(
    id: string,
    taskId: string,
    encrypted: string,
    from: string,
    workspaceId: string
  ): Promise<APIResponse> {
    const res = await fetch(`${API_URL}/api/comments`, {
      method: "POST",
      headers: { "Content-Type": "application/json" },
      body: JSON.stringify({ id, taskId, encrypted, from, workspaceId }),
    });
    return res.json();
  }

  async getComments(
    taskId: string,
    workspaceId: string
  ): Promise<APIResponse<{ comments: any[] }>> {
    const res = await fetch(
      `${API_URL}/api/tasks/${taskId}/comments?workspaceId=${workspaceId}`
    );
    return res.json();
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

export const api = new APIClient();
