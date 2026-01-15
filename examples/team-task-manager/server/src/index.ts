import { Elysia, t } from "elysia";
import { cors } from "@elysiajs/cors";
import { polly } from "@fairfox/polly/elysia";

// Zero-knowledge server - stores only encrypted blobs
// The server has NO ability to read tasks, comments, or any user data

type EncryptedTask = {
  id: string;
  encrypted: string; // Base64 encoded encrypted data
  from: string; // Creator's public key
  workspaceId: string;
  timestamp: number;
};

type EncryptedComment = {
  id: string;
  taskId: string;
  encrypted: string;
  from: string;
  timestamp: number;
};

type Workspace = {
  id: string;
  name: string; // Plaintext name for discovery
  tasks: Map<string, EncryptedTask>;
  comments: Map<string, EncryptedComment>;
  members: Set<string>; // Public keys
  createdAt: number;
};

// In-memory storage (ephemeral - resets on server restart)
const workspaces = new Map<string, Workspace>();

// Connected clients for real-time sync
const connections = new Map<
  string,
  { ws: any; workspaceId: string; userId: string }
>();

const app = new Elysia()
  .use(cors())

  // Polly middleware for offline-first, real-time sync
  .use(
    polly({
      // Offline configuration - queue mutations when offline
      offline: {
        // Workspaces
        "POST /api/workspaces": {
          queue: true,
          optimistic: (body) => ({
            success: true,
            workspace: {
              id: body.id,
              name: body.name,
              createdAt: Date.now(),
            },
          }),
          merge: "replace",
        },
        "POST /api/workspaces/:id/members": {
          queue: true,
          merge: "replace",
        },

        // Tasks
        "POST /api/tasks": {
          queue: true,
          optimistic: (body) => ({
            success: true,
            taskId: body.id,
          }),
          merge: "replace",
        },
        "PATCH /api/tasks/:id": {
          queue: true,
          merge: "replace",
        },
        "DELETE /api/tasks/:id": {
          queue: true,
          optimistic: () => ({ success: true }),
          merge: "replace",
        },

        // Comments
        "POST /api/comments": {
          queue: true,
          optimistic: (body) => ({
            success: true,
            commentId: body.id,
          }),
          merge: "replace",
        },
      },

      // Effects - broadcast changes to all connected clients in the workspace
      effects: {
        "POST /api/tasks": {
          broadcast: true,
        },
        "PATCH /api/tasks/:id": {
          broadcast: true,
        },
        "DELETE /api/tasks/:id": {
          broadcast: true,
        },
        "POST /api/comments": {
          broadcast: true,
        },
        "POST /api/workspaces/:id/members": {
          broadcast: true,
        },
      },

      // Custom WebSocket path (different from app's existing /ws)
      websocketPath: "/polly/ws",
    })
  )

  // Health check
  .get("/", () => ({
    message: "Team Task Manager - Zero-Knowledge Server",
    version: "1.0.0",
    encrypted: true,
  }))

  // Create workspace
  .post(
    "/api/workspaces",
    ({ body }) => {
      const workspace: Workspace = {
        id: body.id,
        name: body.name,
        tasks: new Map(),
        comments: new Map(),
        members: new Set([body.creatorId]),
        createdAt: Date.now(),
      };

      workspaces.set(workspace.id, workspace);

      return {
        success: true,
        workspace: {
          id: workspace.id,
          name: workspace.name,
          createdAt: workspace.createdAt,
        },
      };
    },
    {
      body: t.Object({
        id: t.String(),
        name: t.String(),
        creatorId: t.String(), // Creator's public key
      }),
    }
  )

  // Get workspace metadata (no encrypted data)
  .get("/api/workspaces/:id", ({ params }) => {
    const workspace = workspaces.get(params.id);
    if (!workspace) {
      return { error: "Workspace not found" };
    }

    return {
      id: workspace.id,
      name: workspace.name,
      memberCount: workspace.members.size,
      taskCount: workspace.tasks.size,
      createdAt: workspace.createdAt,
    };
  })

  // Add member to workspace
  .post(
    "/api/workspaces/:id/members",
    ({ params, body }) => {
      const workspace = workspaces.get(params.id);
      if (!workspace) {
        return { error: "Workspace not found" };
      }

      workspace.members.add(body.userId);

      // Broadcast member joined to all connected clients
      broadcastToWorkspace(params.id, {
        type: "member_joined",
        userId: body.userId,
        timestamp: Date.now(),
      });

      return { success: true };
    },
    {
      body: t.Object({
        userId: t.String(), // New member's public key
      }),
    }
  )

  // Create encrypted task
  .post(
    "/api/tasks",
    ({ body }) => {
      const workspace = workspaces.get(body.workspaceId);
      if (!workspace) {
        return { error: "Workspace not found" };
      }

      const task: EncryptedTask = {
        id: body.id,
        encrypted: body.encrypted,
        from: body.from,
        workspaceId: body.workspaceId,
        timestamp: Date.now(),
      };

      workspace.tasks.set(task.id, task);

      // Broadcast encrypted task to all workspace members
      broadcastToWorkspace(body.workspaceId, {
        type: "task_created",
        task,
      });

      return { success: true, taskId: task.id };
    },
    {
      body: t.Object({
        id: t.String(),
        encrypted: t.String(), // Server can't decrypt this
        from: t.String(),
        workspaceId: t.String(),
      }),
    }
  )

  // Update encrypted task
  .patch(
    "/api/tasks/:id",
    ({ params, body }) => {
      const workspace = workspaces.get(body.workspaceId);
      if (!workspace) {
        return { error: "Workspace not found" };
      }

      const existingTask = workspace.tasks.get(params.id);
      if (!existingTask) {
        return { error: "Task not found" };
      }

      const updatedTask: EncryptedTask = {
        ...existingTask,
        encrypted: body.encrypted,
        timestamp: Date.now(),
      };

      workspace.tasks.set(params.id, updatedTask);

      // Broadcast update
      broadcastToWorkspace(body.workspaceId, {
        type: "task_updated",
        task: updatedTask,
      });

      return { success: true };
    },
    {
      body: t.Object({
        encrypted: t.String(),
        workspaceId: t.String(),
      }),
    }
  )

  // Delete task
  .delete(
    "/api/tasks/:id",
    ({ params, body }) => {
      const workspace = workspaces.get(body.workspaceId);
      if (!workspace) {
        return { error: "Workspace not found" };
      }

      workspace.tasks.delete(params.id);

      // Also delete associated comments
      for (const [commentId, comment] of workspace.comments) {
        if (comment.taskId === params.id) {
          workspace.comments.delete(commentId);
        }
      }

      // Broadcast deletion
      broadcastToWorkspace(body.workspaceId, {
        type: "task_deleted",
        taskId: params.id,
      });

      return { success: true };
    },
    {
      body: t.Object({
        workspaceId: t.String(),
      }),
    }
  )

  // Get all encrypted tasks for workspace
  .get("/api/workspaces/:id/tasks", ({ params }) => {
    const workspace = workspaces.get(params.id);
    if (!workspace) {
      return { error: "Workspace not found" };
    }

    return {
      tasks: Array.from(workspace.tasks.values()),
    };
  })

  // Create encrypted comment
  .post(
    "/api/comments",
    ({ body }) => {
      const workspace = workspaces.get(body.workspaceId);
      if (!workspace) {
        return { error: "Workspace not found" };
      }

      const comment: EncryptedComment = {
        id: body.id,
        taskId: body.taskId,
        encrypted: body.encrypted,
        from: body.from,
        timestamp: Date.now(),
      };

      workspace.comments.set(comment.id, comment);

      // Broadcast encrypted comment
      broadcastToWorkspace(body.workspaceId, {
        type: "comment_added",
        comment,
      });

      return { success: true, commentId: comment.id };
    },
    {
      body: t.Object({
        id: t.String(),
        taskId: t.String(),
        encrypted: t.String(),
        from: t.String(),
        workspaceId: t.String(),
      }),
    }
  )

  // Get encrypted comments for task
  .get("/api/tasks/:taskId/comments", ({ params, query }) => {
    const workspace = workspaces.get(query.workspaceId as string);
    if (!workspace) {
      return { error: "Workspace not found" };
    }

    const comments = Array.from(workspace.comments.values()).filter(
      (c) => c.taskId === params.taskId
    );

    return { comments };
  })

  // WebSocket for real-time sync
  .ws("/ws", {
    open(ws) {
      console.log("WebSocket connected");
    },

    message(ws, message: any) {
      const data = JSON.parse(message as string);

      if (data.type === "join") {
        // Register connection
        connections.set(ws.data.id || crypto.randomUUID(), {
          ws,
          workspaceId: data.workspaceId,
          userId: data.userId,
        });

        ws.send(
          JSON.stringify({
            type: "joined",
            workspaceId: data.workspaceId,
          })
        );
      } else if (data.type === "leave") {
        // Remove connection
        for (const [id, conn] of connections) {
          if (conn.ws === ws) {
            connections.delete(id);
            break;
          }
        }
      }
    },

    close(ws) {
      // Remove connection
      for (const [id, conn] of connections) {
        if (conn.ws === ws) {
          connections.delete(id);
          break;
        }
      }
      console.log("WebSocket disconnected");
    },
  })

// Helper function to broadcast to all workspace members
function broadcastToWorkspace(workspaceId: string, data: any) {
  for (const [, conn] of connections) {
    if (conn.workspaceId === workspaceId) {
      try {
        conn.ws.send(JSON.stringify(data));
      } catch (error) {
        console.error("Failed to send message:", error);
      }
    }
  }
}

// Check if SSL certificates exist
const CERTS_DIR = `${import.meta.dir}/../certs`;
const certFile = Bun.file(`${CERTS_DIR}/cert.pem`);
const keyFile = Bun.file(`${CERTS_DIR}/key.pem`);
const hasCerts = (await certFile.exists()) && (await keyFile.exists());

if (!hasCerts) {
  console.error("❌ SSL certificates not found!");
  console.error("   This example requires HTTPS for E2EE to work properly.");
  console.error("");
  console.error("   Run the following command to generate certificates:");
  console.error("   bun run setup:ssl");
  console.error("");
  process.exit(1);
}

// Start server with HTTPS
app.listen({
  port: 3000,
  tls: {
    cert: certFile,
    key: keyFile,
  },
});

const port = app.server?.port ?? 3000;
const hostname = app.server?.hostname ?? "localhost";

console.log(
  `🦊 Team Task Manager server running at https://${hostname}:${port}`
);
console.log("🔒 Zero-knowledge mode: Server cannot decrypt any user data");
console.log("🔐 HTTPS enabled");

// Export app type for Eden treaty client
export type App = typeof app;
