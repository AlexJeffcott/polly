import { isOnline, isSyncing, pendingSync, syncStatus } from "../network";

export function NetworkStatus() {
  // Don't show anything if online and not syncing
  if (isOnline.value && !isSyncing.value && pendingSync.value === 0) {
    return null;
  }

  return (
    <div
      style={{
        position: "fixed",
        bottom: "80px",
        right: "20px",
        background: isOnline.value ? "#10b981" : "#f59e0b",
        color: "white",
        padding: "8px 16px",
        borderRadius: "8px",
        fontSize: "14px",
        fontWeight: 500,
        boxShadow: "0 2px 8px rgba(0, 0, 0, 0.15)",
        zIndex: 999,
        display: "flex",
        alignItems: "center",
        gap: "8px",
        animation: "slideIn 0.3s ease-out",
      }}
    >
      <span>{syncStatus.value}</span>

      <style>{`
        @keyframes slideIn {
          from {
            transform: translateX(100%);
            opacity: 0;
          }
          to {
            transform: translateX(0);
            opacity: 1;
          }
        }

        @keyframes spin {
          from {
            transform: rotate(0deg);
          }
          to {
            transform: rotate(360deg);
          }
        }
      `}</style>
    </div>
  );
}
