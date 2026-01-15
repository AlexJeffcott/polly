import { useState } from "preact/hooks";
import { currentUser } from "../state";
import {
  createUser,
  importUserKey,
  exportUserKey,
  createWorkspace,
} from "../workspace";
import "./Onboarding.css";

export function Onboarding() {
  const [step, setStep] = useState<"welcome" | "create-user" | "import-user" | "create-workspace">(
    currentUser.value ? "create-workspace" : "welcome"
  );
  const [name, setName] = useState("");
  const [workspaceName, setWorkspaceName] = useState("");
  const [importKey, setImportKey] = useState("");
  const [showBackup, setShowBackup] = useState(false);
  const [error, setError] = useState("");

  const handleCreateUser = async () => {
    if (!name.trim()) {
      setError("Please enter your name");
      return;
    }

    try {
      await createUser(name);
      setShowBackup(true);
      setTimeout(() => {
        setShowBackup(false);
        setStep("create-workspace");
      }, 5000);
    } catch (err: any) {
      setError(err.message);
    }
  };

  const handleImportUser = () => {
    if (!importKey.trim()) {
      setError("Please paste your key");
      return;
    }

    try {
      importUserKey(importKey);
      setStep("create-workspace");
    } catch (err: any) {
      setError("Invalid key format");
    }
  };

  const handleCreateWorkspace = async () => {
    if (!workspaceName.trim()) {
      setError("Please enter a workspace name");
      return;
    }

    try {
      await createWorkspace(workspaceName);
    } catch (err: any) {
      setError(err.message);
    }
  };

  const downloadBackup = () => {
    if (!currentUser.value) return;

    const backup = exportUserKey(currentUser.value);
    const blob = new Blob([backup], { type: "application/json" });
    const url = URL.createObjectURL(blob);
    const a = document.createElement("a");
    a.href = url;
    a.download = `team-task-manager-key-${currentUser.value.id.slice(0, 8)}.json`;
    a.click();
    URL.revokeObjectURL(url);
  };

  if (showBackup && currentUser.value) {
    return (
      <div class="onboarding">
        <div class="onboarding-card backup-card">
          <h2>Backup Your Key</h2>
          <p class="warning">
            Your key is your identity. If you lose it, you lose access to all your data permanently.
          </p>

          <div class="backup-key">
            <pre>{exportUserKey(currentUser.value)}</pre>
          </div>

          <button onClick={downloadBackup} class="primary">
            Download Backup
          </button>

          <button onClick={() => { setShowBackup(false); setStep("create-workspace"); }}>
            Skip (Not Recommended)
          </button>
        </div>
      </div>
    );
  }

  if (step === "welcome") {
    return (
      <div class="onboarding">
        <div class="onboarding-card">
          <h1>Team Task Manager</h1>
          <p class="subtitle">End-to-end encrypted, local-first task management</p>

          <div class="features">
            <div class="feature">
              <h3>Zero-Knowledge</h3>
              <p>Server can't read your data</p>
            </div>
            <div class="feature">
              <h3>Local-First</h3>
              <p>Works offline, syncs online</p>
            </div>
            <div class="feature">
              <h3>Real-Time</h3>
              <p>Collaborate with your team</p>
            </div>
          </div>

          <div class="actions">
            <button onClick={() => setStep("create-user")} class="primary">
              Create Identity
            </button>
            <button onClick={() => setStep("import-user")}>
              Import Key
            </button>
          </div>
        </div>
      </div>
    );
  }

  if (step === "create-user") {
    return (
      <div class="onboarding">
        <div class="onboarding-card">
          <h2>Create Your Identity</h2>
          <p>Your identity is a cryptographic keypair. No passwords needed.</p>

          {error && <div class="error">{error}</div>}

          <input
            type="text"
            value={name}
            onInput={(e) => setName((e.target as HTMLInputElement).value)}
            placeholder="Your name"
            class="input"
          />

          <div class="actions">
            <button onClick={handleCreateUser} class="primary">
              Generate Key
            </button>
            <button onClick={() => setStep("welcome")}>
              Back
            </button>
          </div>
        </div>
      </div>
    );
  }

  if (step === "import-user") {
    return (
      <div class="onboarding">
        <div class="onboarding-card">
          <h2>Import Your Key</h2>
          <p>Paste your backup key to restore your identity.</p>

          {error && <div class="error">{error}</div>}

          <textarea
            value={importKey}
            onInput={(e) => setImportKey((e.target as HTMLTextAreaElement).value)}
            placeholder="Paste your key backup here..."
            class="input"
            rows={8}
          />

          <div class="actions">
            <button onClick={handleImportUser} class="primary">
              Import
            </button>
            <button onClick={() => setStep("welcome")}>
              Back
            </button>
          </div>
        </div>
      </div>
    );
  }

  if (step === "create-workspace") {
    return (
      <div class="onboarding">
        <div class="onboarding-card">
          <h2>Create Workspace</h2>
          <p>Workspaces keep your projects organized.</p>

          {error && <div class="error">{error}</div>}

          <input
            type="text"
            value={workspaceName}
            onInput={(e) => setWorkspaceName((e.target as HTMLInputElement).value)}
            placeholder="Workspace name"
            class="input"
          />

          <div class="actions">
            <button onClick={handleCreateWorkspace} class="primary">
              Create Workspace
            </button>
          </div>

          <div class="hint">
            Or ask a teammate for an invite link
          </div>
        </div>
      </div>
    );
  }

  return null;
}
