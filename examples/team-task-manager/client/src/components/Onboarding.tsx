import { useEffect, useMemo, useState } from "preact/hooks";
import { currentUser } from "../state";
import { createUser, createWorkspace, importUserKey, parseInviteLink } from "../workspace";
import { Button } from "./Button";
import { Layout } from "./Layout";

type Screen = "main" | "restore";

export function Onboarding() {
  const [screen, setScreen] = useState<Screen>("main");
  const [name, setName] = useState("");
  const [workspaceName, setWorkspaceName] = useState("");
  const [importKey, setImportKey] = useState("");
  const [error, setError] = useState("");
  const [isLoading, setIsLoading] = useState(false);

  // Parse invite link if present
  const invite = useMemo(() => {
    const params = new URLSearchParams(window.location.search);
    const inviteCode = params.get("invite");
    if (!inviteCode) return null;

    try {
      return parseInviteLink(inviteCode);
    } catch {
      return null;
    }
  }, []);

  // If user already exists (loaded from IndexedDB), just need workspace
  const hasUser = !!currentUser.value;

  // Auto-populate workspace name from invite
  useEffect(() => {
    if (invite && !workspaceName) {
      setWorkspaceName(invite.workspaceName);
    }
  }, [invite]);

  const handleGetStarted = async () => {
    setError("");

    if (!name.trim()) {
      setError("Please enter your name");
      return;
    }

    // If not joining via invite, need workspace name
    if (!invite && !workspaceName.trim()) {
      setError("Please enter a workspace name");
      return;
    }

    setIsLoading(true);

    try {
      // Create user identity (this auto-joins invite workspace via App.tsx effect)
      await createUser(name);

      // If no invite, create the workspace
      if (!invite) {
        await createWorkspace(workspaceName);
      }
      // If there IS an invite, App.tsx will handle joining automatically
    } catch (err: any) {
      setError(err.message);
      setIsLoading(false);
    }
  };

  const handleCreateWorkspace = async () => {
    setError("");

    if (!workspaceName.trim()) {
      setError("Please enter a workspace name");
      return;
    }

    setIsLoading(true);

    try {
      await createWorkspace(workspaceName);
    } catch (err: any) {
      setError(err.message);
      setIsLoading(false);
    }
  };

  const handleRestore = () => {
    setError("");

    if (!importKey.trim()) {
      setError("Please paste your backup key");
      return;
    }

    try {
      importUserKey(importKey);
      // After import, if no workspace + no invite, show workspace creation
      // If invite exists, App.tsx will auto-join
      if (!invite) {
        setScreen("main");
      }
    } catch (err: any) {
      setError("Invalid key format. Please check and try again.");
    }
  };

  // Restore key screen
  if (screen === "restore") {
    return (
      <Layout justifyContent="center" alignContent="center" className="onboarding">
        <div class="onboarding-card">
          <h2>Restore Your Account</h2>
          <p class="subtitle-small">Paste your backup key to continue</p>

          {error && <div class="error">{error}</div>}

          <textarea
            value={importKey}
            onInput={(e) => setImportKey((e.target as HTMLTextAreaElement).value)}
            placeholder="Paste your backup key here..."
            class="input"
            rows={6}
          />

          <Button onPress={handleRestore} tier="primary" fullWidth>
            Restore
          </Button>

          <Button
            onPress={() => {
              setScreen("main");
              setError("");
            }}
            tier="tertiary"
            fullWidth
          >
            Back
          </Button>
        </div>
      </Layout>
    );
  }

  // User exists but no workspace (and no invite to auto-join)
  if (hasUser && !invite) {
    return (
      <Layout justifyContent="center" alignContent="center" className="onboarding">
        <div class="onboarding-card">
          <h2>Create a Workspace</h2>
          <p class="subtitle-small">Workspaces let you organize and share tasks</p>

          {error && <div class="error">{error}</div>}

          <input
            type="text"
            value={workspaceName}
            onInput={(e) => setWorkspaceName((e.target as HTMLInputElement).value)}
            placeholder="Workspace name"
            class="input"
            onKeyDown={(e) => e.key === "Enter" && handleCreateWorkspace()}
          />

          <Button onPress={handleCreateWorkspace} tier="primary" fullWidth disabled={isLoading}>
            {isLoading ? "Creating..." : "Create Workspace"}
          </Button>

          <p class="hint-text">Have an invite link? Just paste it in your browser.</p>
        </div>
      </Layout>
    );
  }

  // Main screen: Get Started (with or without invite)
  return (
    <Layout justifyContent="center" alignContent="center" className="onboarding">
      <div class="onboarding-card">
        <h1>Team Task Manager</h1>
        <p class="subtitle">Private task management for teams</p>

        {invite && <div class="invite-badge">Joining "{invite.workspaceName}"</div>}

        {error && <div class="error">{error}</div>}

        <input
          type="text"
          value={name}
          onInput={(e) => setName((e.target as HTMLInputElement).value)}
          placeholder="Your name"
          class="input"
          onKeyDown={(e) =>
            e.key === "Enter" && !invite && document.getElementById("workspace-input")?.focus()
          }
        />

        {!invite && (
          <input
            id="workspace-input"
            type="text"
            value={workspaceName}
            onInput={(e) => setWorkspaceName((e.target as HTMLInputElement).value)}
            placeholder="Workspace name"
            class="input"
            onKeyDown={(e) => e.key === "Enter" && handleGetStarted()}
          />
        )}

        <Button onPress={handleGetStarted} tier="primary" fullWidth disabled={isLoading}>
          {isLoading ? "Setting up..." : invite ? "Join Workspace" : "Get Started"}
        </Button>

        <div class="footer-links">
          <Button onPress={() => setScreen("restore")} tier="tertiary">
            Restore from backup
          </Button>
        </div>

        <p class="privacy-note">Your data stays on your device</p>
      </div>
    </Layout>
  );
}
