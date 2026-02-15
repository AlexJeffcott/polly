import { useEffect, useState } from "preact/hooks";
import { isInstallPromptAvailable, isPWA, showInstallPrompt } from "../pwa";

export function InstallPrompt() {
  const [showPrompt, setShowPrompt] = useState(false);
  const [installing, setInstalling] = useState(false);

  useEffect(() => {
    // Don't show if already installed
    if (isPWA()) {
      return;
    }

    // Check if install prompt is available
    const checkPrompt = () => {
      setShowPrompt(isInstallPromptAvailable());
    };

    // Check immediately
    checkPrompt();

    // Check again after a delay (in case prompt becomes available later)
    const timer = setTimeout(checkPrompt, 1000);

    return () => clearTimeout(timer);
  }, []);

  const handleInstall = async () => {
    setInstalling(true);

    const result = await showInstallPrompt();

    if (result === "accepted") {
      setShowPrompt(false);
    } else if (result === "dismissed") {
      setInstalling(false);
    } else {
      setInstalling(false);
      alert(
        "Install is not available. You may already have the app installed or your browser does not support PWA installation."
      );
    }
  };

  const handleDismiss = () => {
    setShowPrompt(false);
    // Don't show again this session
    sessionStorage.setItem("installPromptDismissed", "true");
  };

  // Don't show if dismissed this session
  if (sessionStorage.getItem("installPromptDismissed")) {
    return null;
  }

  if (!showPrompt) {
    return null;
  }

  return (
    <div
      style={{
        position: "fixed",
        bottom: "20px",
        right: "20px",
        background: "white",
        padding: "16px 20px",
        borderRadius: "12px",
        boxShadow: "0 4px 12px rgba(0, 0, 0, 0.15)",
        maxWidth: "320px",
        zIndex: 1000,
        animation: "slideIn 0.3s ease-out",
      }}
    >
      <button
        onClick={handleDismiss}
        style={{
          position: "absolute",
          top: "8px",
          right: "8px",
          background: "none",
          border: "none",
          fontSize: "20px",
          cursor: "pointer",
          color: "#666",
          padding: "4px",
          lineHeight: 1,
        }}
        aria-label="Dismiss"
      >
        ×
      </button>

      <div style={{ display: "flex", alignItems: "center", gap: "12px", marginBottom: "12px" }}>
        <div>
          <h3 style={{ margin: 0, fontSize: "16px", fontWeight: 600 }}>Install App</h3>
          <p style={{ margin: "4px 0 0", fontSize: "14px", color: "#666" }}>
            Works offline & faster
          </p>
        </div>
      </div>

      <button
        onClick={handleInstall}
        disabled={installing}
        style={{
          width: "100%",
          padding: "10px",
          background: "#4f46e5",
          color: "white",
          border: "none",
          borderRadius: "8px",
          fontSize: "14px",
          fontWeight: 600,
          cursor: installing ? "not-allowed" : "pointer",
          opacity: installing ? 0.6 : 1,
        }}
      >
        {installing ? "Installing..." : "Install Now"}
      </button>

      <style>{`
        @keyframes slideIn {
          from {
            transform: translateY(20px);
            opacity: 0;
          }
          to {
            transform: translateY(0);
            opacity: 1;
          }
        }
      `}</style>
    </div>
  );
}
