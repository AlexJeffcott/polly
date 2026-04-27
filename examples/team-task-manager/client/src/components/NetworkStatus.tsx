import { Surface } from "@fairfox/polly/ui";
import { isOnline, isSyncing, pendingSync, syncStatus } from "../network";

export function NetworkStatus() {
  // Don't show anything if online and not syncing
  if (isOnline.value && !isSyncing.value && pendingSync.value === 0) {
    return null;
  }

  const tintToken = isOnline.value
    ? "var(--polly-status-success-bg)"
    : "var(--polly-status-warning-bg)";
  const textToken = isOnline.value
    ? "var(--polly-status-success-text)"
    : "var(--polly-status-warning-text)";

  return (
    <Surface
      variant="floating"
      shadow="sm"
      radius="md"
      inset="auto 20px 80px auto"
      padding="var(--polly-space-sm) var(--polly-space-lg)"
      style={{
        "--polly-surface-raised": tintToken,
        color: textToken,
        fontSize: "14px",
        fontWeight: 500,
        display: "flex",
        alignItems: "center",
        gap: "8px",
        animation: "slideIn 0.3s ease-out",
      }}
    >
      <span>{syncStatus.value}</span>
      <style>{`
        @keyframes slideIn {
          from { transform: translateX(100%); opacity: 0; }
          to { transform: translateX(0); opacity: 1; }
        }
      `}</style>
    </Surface>
  );
}
