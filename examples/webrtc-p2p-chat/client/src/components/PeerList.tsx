import type { Peer } from "../types";

interface Props {
  peers: Peer[];
}

/**
 * PeerList - Show connected peers and their status
 */
export function PeerList({ peers }: Props) {
  const getStatusColor = (state: RTCPeerConnectionState) => {
    switch (state) {
      case "connected":
        return "#00ff00";
      case "connecting":
        return "#ffaa00";
      case "failed":
      case "closed":
      case "disconnected":
        return "#ff0000";
      default:
        return "#888";
    }
  };

  const getStatusText = (state: RTCPeerConnectionState) => {
    switch (state) {
      case "connected":
        return "Connected";
      case "connecting":
        return "Establishing connection...";
      case "failed":
        return "Connection failed";
      case "closed":
        return "Left room";
      case "disconnected":
        return "Disconnected";
      default:
        return "Unknown";
    }
  };

  const getStatusIcon = (state: RTCPeerConnectionState) => {
    switch (state) {
      case "connected":
        return "✓";
      case "connecting":
        return "⟳";
      case "failed":
        return "✗";
      case "closed":
        return "—";
      case "disconnected":
        return "✗";
      default:
        return "?";
    }
  };

  const connectedCount = peers.filter((p) => p.connectionState === "connected").length;
  const connectingCount = peers.filter((p) => p.connectionState === "connecting").length;

  return (
    <div
      style={{
        padding: "1rem",
        background: "#1a1a1a",
        borderRadius: "8px",
        border: "1px solid #333",
        flex: 1,
        overflowY: "auto",
      }}
    >
      <div
        style={{
          display: "flex",
          alignItems: "center",
          justifyContent: "space-between",
          marginBottom: "1rem",
        }}
      >
        <h3 style={{ fontSize: "0.9rem", color: "#aaa", margin: 0 }}>People in Room</h3>
        {peers.length > 0 && (
          <div style={{ fontSize: "0.75rem", color: "#666" }}>
            {connectedCount > 0 && (
              <span style={{ color: "#00ff00" }}>{connectedCount} online</span>
            )}
            {connectingCount > 0 && (
              <span style={{ color: "#ffaa00", marginLeft: "0.5rem" }}>
                {connectingCount} connecting
              </span>
            )}
          </div>
        )}
      </div>

      {peers.length === 0 ? (
        <div
          style={{
            padding: "1.5rem",
            textAlign: "center",
            color: "#666",
            fontSize: "0.85rem",
          }}
        >
          <div style={{ fontSize: "2rem", marginBottom: "0.5rem", opacity: 0.3 }}>👥</div>
          <div style={{ marginBottom: "0.5rem" }}>No one else here yet</div>
          <div style={{ fontSize: "0.75rem", color: "#555" }}>
            Share the invite link to get started
          </div>
        </div>
      ) : (
        <div style={{ display: "flex", flexDirection: "column", gap: "0.5rem" }}>
          {peers.map((peer) => (
            <div
              key={peer.id}
              style={{
                padding: "0.75rem",
                background:
                  peer.connectionState === "connected" ? "#0f0f0f" : "rgba(255, 170, 0, 0.05)",
                borderRadius: "6px",
                border: `1px solid ${
                  peer.connectionState === "connected" ? "#222" : "rgba(255, 170, 0, 0.2)"
                }`,
                transition: "all 0.3s ease",
              }}
            >
              <div
                style={{
                  display: "flex",
                  alignItems: "center",
                  justifyContent: "space-between",
                }}
              >
                <div style={{ display: "flex", alignItems: "center", gap: "0.75rem" }}>
                  <div
                    style={{
                      position: "relative",
                      width: "10px",
                      height: "10px",
                    }}
                  >
                    <div
                      style={{
                        width: "10px",
                        height: "10px",
                        borderRadius: "50%",
                        background: getStatusColor(peer.connectionState),
                        animation:
                          peer.connectionState === "connecting"
                            ? "pulse 2s cubic-bezier(0.4, 0, 0.6, 1) infinite"
                            : "none",
                      }}
                    />
                    {peer.connectionState === "connecting" && (
                      <style>{`
                        @keyframes pulse {
                          0%, 100% { opacity: 1; }
                          50% { opacity: 0.3; }
                        }
                      `}</style>
                    )}
                  </div>
                  <div>
                    <div
                      style={{
                        fontSize: "0.9rem",
                        fontWeight: peer.connectionState === "connected" ? "bold" : "normal",
                        color: peer.connectionState === "connected" ? "#fff" : "#aaa",
                      }}
                    >
                      {peer.displayName}
                    </div>
                    <div
                      style={{
                        fontSize: "0.7rem",
                        color: "#666",
                        marginTop: "0.15rem",
                      }}
                    >
                      {getStatusText(peer.connectionState)}
                    </div>
                  </div>
                </div>

                {peer.latency !== undefined && peer.connectionState === "connected" && (
                  <div
                    style={{
                      fontSize: "0.7rem",
                      color:
                        peer.latency < 100 ? "#00ff00" : peer.latency < 300 ? "#ffaa00" : "#ff6666",
                      background: "rgba(0, 0, 0, 0.3)",
                      padding: "0.25rem 0.5rem",
                      borderRadius: "4px",
                      fontFamily: "monospace",
                    }}
                  >
                    {peer.latency}ms
                  </div>
                )}
              </div>
            </div>
          ))}
        </div>
      )}
    </div>
  );
}
