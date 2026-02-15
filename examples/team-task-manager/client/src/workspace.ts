// Workspace management with encryption

import type { Task, User, Workspace, WorkspaceMember } from "../../shared/types";
import { api } from "./api";
import {
  base64ToBytes,
  bytesToBase64,
  bytesToHex,
  decryptText,
  encryptText,
  generateWorkspaceKey,
  KeyPair,
} from "./crypto";
import { comments, currentUser, tasks, workspace, workspaces } from "./state";

// Create a new user identity
export async function createUser(name: string): Promise<User> {
  const keypair = await KeyPair.generate();

  const user: User = {
    id: bytesToHex(keypair.publicKey), // Public key as user ID
    name,
    publicKey: bytesToBase64(keypair.publicKey),
    privateKey: bytesToBase64(keypair.privateKey),
  };

  // Save to local state (auto-persists)
  currentUser.value = user;

  return user;
}

// Export user key for backup
export function exportUserKey(user: User): string {
  const data = {
    id: user.id,
    name: user.name,
    publicKey: user.publicKey,
    privateKey: user.privateKey,
  };
  return JSON.stringify(data, null, 2);
}

// Import user key from backup
export function importUserKey(exported: string): User {
  const data = JSON.parse(exported);
  const user: User = {
    id: data.id,
    name: data.name,
    publicKey: data.publicKey,
    privateKey: data.privateKey,
  };

  currentUser.value = user;
  return user;
}

// Create a new workspace
export async function createWorkspace(name: string): Promise<Workspace> {
  if (!currentUser.value) {
    throw new Error("No user logged in");
  }

  // Generate workspace key
  const workspaceKeyBytes = await generateWorkspaceKey();
  const workspaceKey = bytesToBase64(workspaceKeyBytes);
  const workspaceId = crypto.randomUUID();

  const newWorkspace: Workspace = {
    id: workspaceId,
    name,
    workspaceKey,
    members: [
      {
        userId: currentUser.value.id,
        name: currentUser.value.name,
        publicKey: currentUser.value.publicKey,
        role: "admin",
        joinedAt: Date.now(),
        encryptedWorkspaceKey: workspaceKey, // Creator has plaintext key
      },
    ],
    maxUrgentTasks: 3,
    createdAt: Date.now(),
  };

  // Create on server
  await api.createWorkspace(workspaceId, name, currentUser.value.id);

  // Save locally as active workspace
  workspace.value = newWorkspace;

  // Add to workspaces list if not already there
  if (!workspaces.value.find((w) => w.id === workspaceId)) {
    workspaces.value = [...workspaces.value, newWorkspace];
  }

  // WebSocket connection is handled by App.tsx useEffect
  // No need to connect here

  return newWorkspace;
}

// Join existing workspace (requires encrypted workspace key from invite)
export async function joinWorkspace(
  workspaceId: string,
  workspaceName: string,
  encryptedKey: string
): Promise<Workspace> {
  if (!currentUser.value) {
    throw new Error("No user logged in");
  }

  // For demo, we're using symmetric encryption so just use the key directly
  // In production, you'd decrypt with your private key here
  const workspaceKey = encryptedKey;

  const newWorkspace: Workspace = {
    id: workspaceId,
    name: workspaceName,
    workspaceKey,
    members: [
      {
        userId: currentUser.value.id,
        name: currentUser.value.name,
        publicKey: currentUser.value.publicKey,
        role: "member",
        joinedAt: Date.now(),
        encryptedWorkspaceKey: workspaceKey,
      },
    ],
    maxUrgentTasks: 3,
    createdAt: Date.now(),
  };

  // Save locally as active workspace
  workspace.value = newWorkspace;

  // Add to workspaces list if not already there
  if (workspaces.value.find((w) => w.id === workspaceId)) {
    // Update existing workspace in list
    workspaces.value = workspaces.value.map((w) => (w.id === workspaceId ? newWorkspace : w));
  } else {
    workspaces.value = [...workspaces.value, newWorkspace];
  }

  // WebSocket connection is handled by App.tsx useEffect
  // No need to connect here

  // Add self as member on server (just broadcasts to peers)
  await api.addMember(workspaceId, currentUser.value.id);

  // Request sync from peers (they will send us their data)
  await requestPeerSync(workspaceId);

  return newWorkspace;
}

// Request sync from peers (they will send us their data via WebSocket)
async function requestPeerSync(workspaceId: string) {
  if (!currentUser.value) return;

  await api.requestSync(workspaceId, currentUser.value.id);
}

// Generate invite link
export function generateInviteLink(): string {
  if (!workspace.value) {
    throw new Error("No workspace selected");
  }

  const inviteData = {
    workspaceId: workspace.value.id,
    workspaceName: workspace.value.name,
    encryptedKey: workspace.value.workspaceKey,
  };

  const encoded = btoa(JSON.stringify(inviteData));
  return `${window.location.origin}?invite=${encoded}`;
}

// Parse invite link
export function parseInviteLink(inviteCode: string): {
  workspaceId: string;
  workspaceName: string;
  encryptedKey: string;
} {
  const decoded = atob(inviteCode);
  const data = JSON.parse(decoded);

  return {
    workspaceId: data.workspaceId,
    workspaceName: data.workspaceName,
    encryptedKey: data.encryptedKey,
  };
}

// Switch to a different workspace
export async function switchWorkspace(workspaceId: string) {
  if (!currentUser.value) {
    throw new Error("No user logged in");
  }

  const targetWorkspace = workspaces.value.find((w) => w.id === workspaceId);
  if (!targetWorkspace) {
    throw new Error("Workspace not found");
  }

  // Disconnect from current workspace
  if (workspace.value) {
    api.disconnect();
  }

  // Switch to new workspace
  workspace.value = targetWorkspace;

  // Don't clear tasks/comments - they're filtered by workspaceId in state helpers
  // Tasks from all workspaces stay in IndexedDB for offline access

  // WebSocket connection is handled by App.tsx useEffect
  // The cleanup function will disconnect, then reconnect with new workspace

  // Request sync from peers to get any new tasks for this workspace
  await requestPeerSync(workspaceId);
}

// Leave workspace
export function leaveWorkspace() {
  if (workspace.value) {
    api.disconnect();
  }

  workspace.value = null;
  tasks.value = [];
  comments.value = [];
}
