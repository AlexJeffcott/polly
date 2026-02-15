import { cors } from "@elysiajs/cors";
import { polly } from "@fairfox/polly/elysia";
import { Elysia, t } from "elysia";

// Pure local-first server - NO DATA STORAGE
// Server is a stateless message relay that broadcasts updates between clients
// All data lives only in client IndexedDB

// Connected clients for real-time sync
const connections = new Map<string, { ws: any; workspaceId: string; userId: string }>();

// Track active workspaces (just for connection management, no data)
const activeWorkspaces = new Set<string>();

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
      },

      websocketPath: "/polly/ws",
    })
  )

  // Create workspace (just track that it exists, no data storage)
  .post(
    "/api/workspaces",
    ({ body }) => {
      activeWorkspaces.add(body.id);

      // Broadcast to anyone watching this workspace
      broadcastToWorkspace(body.id, {
        type: "workspace_created",
        workspaceId: body.id,
        creatorId: body.creatorId,
        timestamp: Date.now(),
      });

      return {
        success: true,
        workspace: {
          id: body.id,
          name: body.name,
          createdAt: Date.now(),
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

  // Check if workspace exists (just checks active connections)
  .get("/api/workspaces/:id", ({ params }) => {
    const hasConnections = Array.from(connections.values()).some(
      (conn) => conn.workspaceId === params.id
    );

    if (!hasConnections && !activeWorkspaces.has(params.id)) {
      return { error: "Workspace not found" };
    }

    return {
      id: params.id,
      active: hasConnections,
      createdAt: Date.now(), // Not actually tracked, just return current time
    };
  })

  // Add member to workspace (broadcast only, no storage)
  .post(
    "/api/workspaces/:id/members",
    ({ params, body }) => {
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

  // Relay encrypted task creation
  .post(
    "/api/tasks",
    ({ body }) => {
      // Broadcast encrypted task to all workspace members
      broadcastToWorkspace(body.workspaceId, {
        type: "task_created",
        task: {
          id: body.id,
          encrypted: body.encrypted,
          from: body.from,
          workspaceId: body.workspaceId,
          timestamp: Date.now(),
        },
      });

      return { success: true, taskId: body.id };
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

  // Relay encrypted task update
  .patch(
    "/api/tasks/:id",
    ({ params, body }) => {
      // Broadcast update to all workspace members
      broadcastToWorkspace(body.workspaceId, {
        type: "task_updated",
        task: {
          id: params.id,
          encrypted: body.encrypted,
          workspaceId: body.workspaceId,
          timestamp: Date.now(),
        },
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

  // Relay task deletion
  .delete(
    "/api/tasks/:id",
    ({ params, body }) => {
      // Broadcast deletion to all workspace members
      broadcastToWorkspace(body.workspaceId, {
        type: "task_deleted",
        taskId: params.id,
        timestamp: Date.now(),
      });

      return { success: true };
    },
    {
      body: t.Object({
        workspaceId: t.String(),
      }),
    }
  )

  // Relay encrypted comment creation
  .post(
    "/api/comments",
    ({ body }) => {
      // Broadcast encrypted comment to all workspace members
      broadcastToWorkspace(body.workspaceId, {
        type: "comment_added",
        comment: {
          id: body.id,
          taskId: body.taskId,
          encrypted: body.encrypted,
          from: body.from,
          timestamp: Date.now(),
        },
      });

      return { success: true, commentId: body.id };
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

  // Request sync from peers (new peer joining workspace)
  .post(
    "/api/sync/request",
    ({ body }) => {
      // Broadcast sync request to all other connected clients in workspace
      // They will respond with their data via WebSocket
      broadcastToWorkspace(
        body.workspaceId,
        {
          type: "sync_request",
          requesterId: body.userId,
          timestamp: Date.now(),
        },
        body.userId
      ); // Exclude the requester

      return { success: true };
    },
    {
      body: t.Object({
        workspaceId: t.String(),
        userId: t.String(),
      }),
    }
  )

  // WebSocket for real-time sync
  .ws("/ws", {
    open(ws) {
      console.log("[SERVER WS] WebSocket connection opened");
    },

    message(ws, message: any) {
      console.log("[SERVER WS] Received message:", message);

      try {
        // Elysia may already parse the message as an object
        const data = typeof message === "string" ? JSON.parse(message) : message;
        console.log("[SERVER WS] Parsed message type:", data.type);

        if (data.type === "join") {
          // Register connection
          const connId = crypto.randomUUID();
          connections.set(connId, {
            ws,
            workspaceId: data.workspaceId,
            userId: data.userId,
          });

          // Store connection ID in ws data for cleanup
          (ws as any).connId = connId;

          activeWorkspaces.add(data.workspaceId);

          console.log(
            `[SERVER WS] User ${data.userId.substring(0, 20)}... joined workspace ${data.workspaceId}`
          );
          console.log(`[SERVER WS] Total connections: ${connections.size}`);

          ws.send(
            JSON.stringify({
              type: "joined",
              workspaceId: data.workspaceId,
            })
          );

          console.log("[SERVER WS] Sent 'joined' confirmation");
        } else if (data.type === "leave") {
          // Remove connection
          const connId = (ws as any).connId;
          if (connId) {
            connections.delete(connId);
          }
        } else if (data.type === "sync_response") {
          // A peer is responding to a sync request with their data
          // Forward it to the requester
          for (const [, conn] of connections) {
            if (conn.workspaceId === data.workspaceId && conn.userId === data.targetUserId) {
              try {
                conn.ws.send(JSON.stringify(data));
              } catch (error) {
                console.error("Failed to send sync response:", error);
              }
              break;
            }
          }
        }
      } catch (error) {
        console.error("[SERVER WS] Error handling message:", error);
      }
    },

    close(ws, code, reason) {
      console.log("[SERVER WS] Connection closing, code:", code, "reason:", reason);

      // Remove connection
      const connId = (ws as any).connId;
      if (connId) {
        const conn = connections.get(connId);
        if (conn) {
          console.log(
            `[SERVER WS] User ${conn.userId.substring(0, 20)}... left workspace ${conn.workspaceId}`
          );
        }
        connections.delete(connId);
      }
      console.log("[SERVER WS] WebSocket disconnected, total connections:", connections.size);
    },
  });

// Helper function to broadcast to all workspace members
function broadcastToWorkspace(workspaceId: string, data: any, excludeUserId?: string) {
  for (const [, conn] of connections) {
    if (conn.workspaceId === workspaceId && conn.userId !== excludeUserId) {
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
  console.error("ERROR: SSL certificates not found!");
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

console.log(`Team Task Manager server running at https://${hostname}:${port}`);
console.log("Pure local-first mode: Server stores NO data, only relays messages");
console.log("All data lives in client IndexedDB - server is a stateless message broker");
console.log("HTTPS enabled");

// Export app type for Eden treaty client
export type App = typeof app;
