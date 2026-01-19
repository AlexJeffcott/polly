// Shared types for team task manager

export type Priority = "low" | "medium" | "high" | "urgent";
export type TaskStatus = "todo" | "in_progress" | "review" | "done";
export type UserRole = "admin" | "member" | "viewer";

export type User = {
  id: string; // Derived from public key
  name: string;
  publicKey: string; // base64 encoded
  privateKey: string; // base64 encoded
  avatar?: string;
};

export type WorkspaceMember = {
  userId: string;
  name: string;
  publicKey: string; // base64 encoded
  role: UserRole;
  joinedAt: number;
  encryptedWorkspaceKey: string; // base64 encoded workspace key
};

export type Workspace = {
  id: string;
  name: string;
  workspaceKey: string; // base64 encoded symmetric key for encrypting workspace data
  members: WorkspaceMember[];
  maxUrgentTasks: number;
  createdAt: number;
};

export type Task = {
  id: string;
  workspaceId: string; // Which workspace this task belongs to
  text: string;
  description?: string;
  createdBy: string; // User ID
  assignedTo: string | null;
  priority: Priority;
  status: TaskStatus;
  dependencies: string[]; // Task IDs that must be completed first
  requiresApproval: boolean;
  approvedBy?: string;
  createdAt: number;
  updatedAt: number;
  completedAt?: number;
};

export type Comment = {
  id: string;
  workspaceId: string; // Which workspace this comment belongs to
  taskId: string;
  authorId: string;
  text: string;
  createdAt: number;
  updatedAt?: number;
};

export type Activity = {
  id: string;
  type:
    | "task_created"
    | "task_updated"
    | "task_completed"
    | "task_assigned"
    | "comment_added"
    | "member_joined";
  userId: string;
  taskId?: string;
  timestamp: number;
  metadata?: Record<string, any>;
};

// Server-side encrypted payload
export type EncryptedPayload = {
  encrypted: string; // Base64 encoded encrypted data
  from: string; // Sender's user ID (public key)
  nonce?: string; // Optional nonce for additional security
};

// Server-side stored task (encrypted)
export type EncryptedTask = {
  id: string;
  encrypted: string; // Encrypted task data
  from: string; // Creator's user ID
  workspaceId: string;
  timestamp: number;
};

// Server-side stored comment (encrypted)
export type EncryptedComment = {
  id: string;
  taskId: string;
  encrypted: string; // Encrypted comment data
  from: string;
  timestamp: number;
};

// Client-side state
export type AppState = {
  currentUser: User | null;
  workspace: Workspace | null;
  tasks: Task[];
  comments: Comment[];
  activities: Activity[];
  isOnline: boolean;
};

// Constraint error
export type ConstraintError = {
  constraint: string;
  message: string;
  field?: string;
};
