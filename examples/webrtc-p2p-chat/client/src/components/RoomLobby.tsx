import { useEffect, useState } from "preact/hooks";
import { displayName as savedDisplayName } from "../state";

interface Props {
  onJoin: (roomId: string, displayName: string) => Promise<void>;
}

/**
 * RoomLobby - Join or create a room
 */
export function RoomLobby({ onJoin }: Props) {
  const [roomId, setRoomId] = useState("");
  const [name, setName] = useState(savedDisplayName.value || "");
  const [isJoining, setIsJoining] = useState(false);
  const [error, setError] = useState<string | null>(null);
  const [hasInviteLink, setHasInviteLink] = useState(false);

  // Auto-fill room ID from URL parameter
  useEffect(() => {
    const params = new URLSearchParams(window.location.search);
    const roomParam = params.get("room");
    if (roomParam) {
      setRoomId(roomParam);
      setHasInviteLink(true);
    }
  }, []);

  const handleSubmit = async (e: Event) => {
    e.preventDefault();
    setError(null);

    if (!roomId.trim() || !name.trim()) {
      setError("Please enter both name and room ID");
      return;
    }

    setIsJoining(true);
    try {
      await onJoin(roomId.trim(), name.trim());
    } catch (err) {
      setError(err instanceof Error ? err.message : "Failed to join room");
      setIsJoining(false);
    }
  };

  const generateRoomId = () => {
    const id = Math.random().toString(36).substring(2, 8);
    setRoomId(id);
  };

  return (
    <div
      style={{
        minHeight: "100vh",
        display: "flex",
        flexDirection: "column",
        alignItems: "center",
        justifyContent: "center",
        padding: "2rem",
      }}
    >
      {/* Hero Section */}
      {!hasInviteLink && (
        <div
          style={{
            maxWidth: "600px",
            textAlign: "center",
            marginBottom: "3rem",
          }}
        >
          <h1
            style={{
              fontSize: "2.5rem",
              marginBottom: "1rem",
              background: "linear-gradient(135deg, #0066ff 0%, #00ccff 100%)",
              WebkitBackgroundClip: "text",
              WebkitTextFillColor: "transparent",
              backgroundClip: "text",
            }}
          >
            Private P2P Chat
          </h1>
          <p
            style={{
              fontSize: "1.1rem",
              color: "#aaa",
              marginBottom: "1.5rem",
            }}
          >
            End-to-end encrypted conversations that travel directly between browsers. No server
            storage, no data collection.
          </p>
          <div
            style={{
              display: "flex",
              gap: "2rem",
              justifyContent: "center",
              fontSize: "0.9rem",
              color: "#666",
            }}
          >
            <div style={{ display: "flex", alignItems: "center", gap: "0.5rem" }}>
              <span style={{ color: "#00ff00" }}>✓</span>
              <span>Direct P2P</span>
            </div>
            <div style={{ display: "flex", alignItems: "center", gap: "0.5rem" }}>
              <span style={{ color: "#00ff00" }}>✓</span>
              <span>No tracking</span>
            </div>
            <div style={{ display: "flex", alignItems: "center", gap: "0.5rem" }}>
              <span style={{ color: "#00ff00" }}>✓</span>
              <span>Open source</span>
            </div>
          </div>
        </div>
      )}

      {/* Invite Link Banner */}
      {hasInviteLink && (
        <div
          style={{
            maxWidth: "500px",
            width: "100%",
            padding: "1rem 1.5rem",
            background: "linear-gradient(135deg, #0066ff20 0%, #00ccff20 100%)",
            border: "1px solid #0066ff",
            borderRadius: "8px",
            marginBottom: "2rem",
            textAlign: "center",
          }}
        >
          <div style={{ fontSize: "1.1rem", fontWeight: "bold", marginBottom: "0.25rem" }}>
            You've been invited to join a room
          </div>
          <div style={{ fontSize: "0.85rem", color: "#aaa" }}>
            Enter your name below to join the conversation
          </div>
        </div>
      )}

      {/* Main Form Card */}
      <div
        style={{
          maxWidth: "500px",
          width: "100%",
          padding: "2rem",
          background: "#1a1a1a",
          borderRadius: "12px",
          border: "1px solid #333",
          boxShadow: "0 4px 24px rgba(0, 0, 0, 0.5)",
        }}
      >
        <h2
          style={{
            marginBottom: "1.5rem",
            fontSize: "1.5rem",
            textAlign: "center",
          }}
        >
          {hasInviteLink ? "Join Chat Room" : "Start a New Chat"}
        </h2>

        {error && (
          <div
            style={{
              padding: "0.75rem",
              marginBottom: "1rem",
              background: "#ff000020",
              border: "1px solid #ff0000",
              borderRadius: "4px",
              color: "#ff6666",
            }}
          >
            {error}
          </div>
        )}

        <form onSubmit={handleSubmit}>
          <div style={{ marginBottom: "1rem" }}>
            <label
              htmlFor="name"
              style={{
                display: "block",
                marginBottom: "0.5rem",
                fontSize: "0.9rem",
                color: "#aaa",
              }}
            >
              Your Name
            </label>
            <input
              id="name"
              type="text"
              value={name}
              onInput={(e) => setName(e.currentTarget.value)}
              placeholder="How should others see you?"
              style={{
                width: "100%",
                padding: "0.75rem",
                background: "#0f0f0f",
                border: "1px solid #333",
                borderRadius: "6px",
                color: "#fff",
                fontSize: "1rem",
              }}
              disabled={isJoining}
              required
              autoFocus
            />
          </div>

          {!hasInviteLink && (
            <div style={{ marginBottom: "1.5rem" }}>
              <label
                htmlFor="roomId"
                style={{
                  display: "block",
                  marginBottom: "0.5rem",
                  fontSize: "0.9rem",
                  color: "#aaa",
                }}
              >
                Room ID
              </label>
              <div style={{ display: "flex", gap: "0.5rem" }}>
                <input
                  id="roomId"
                  type="text"
                  value={roomId}
                  onInput={(e) => setRoomId(e.currentTarget.value)}
                  placeholder="Enter or generate ID"
                  style={{
                    flex: 1,
                    padding: "0.75rem",
                    background: "#0f0f0f",
                    border: "1px solid #333",
                    borderRadius: "6px",
                    color: "#fff",
                    fontSize: "1rem",
                  }}
                  disabled={isJoining}
                  required
                />
                <button
                  type="button"
                  onClick={generateRoomId}
                  disabled={isJoining}
                  style={{
                    padding: "0.75rem 1.5rem",
                    background: "linear-gradient(135deg, #333 0%, #444 100%)",
                    border: "none",
                    borderRadius: "6px",
                    color: "#fff",
                    cursor: "pointer",
                    fontWeight: "bold",
                    fontSize: "0.9rem",
                  }}
                >
                  Generate
                </button>
              </div>
              <small
                style={{
                  color: "#666",
                  marginTop: "0.5rem",
                  display: "block",
                  fontSize: "0.85rem",
                }}
              >
                You'll get a shareable link after creating the room
              </small>
            </div>
          )}

          {hasInviteLink && (
            <div style={{ marginBottom: "1.5rem" }}>
              <label
                style={{
                  display: "block",
                  marginBottom: "0.5rem",
                  fontSize: "0.9rem",
                  color: "#aaa",
                }}
              >
                Joining Room
              </label>
              <div
                style={{
                  padding: "0.75rem",
                  background: "#0f0f0f",
                  border: "1px solid #0066ff",
                  borderRadius: "6px",
                  fontFamily: "monospace",
                  fontSize: "1rem",
                  color: "#0066ff",
                  textAlign: "center",
                  fontWeight: "bold",
                }}
              >
                {roomId}
              </div>
            </div>
          )}

          <button
            type="submit"
            disabled={isJoining}
            style={{
              width: "100%",
              padding: "1rem",
              background: isJoining ? "#666" : "linear-gradient(135deg, #0066ff 0%, #0088ff 100%)",
              border: "none",
              borderRadius: "6px",
              color: "#fff",
              fontSize: "1rem",
              fontWeight: "bold",
              cursor: isJoining ? "not-allowed" : "pointer",
              transition: "transform 0.2s, box-shadow 0.2s",
              boxShadow: isJoining ? "none" : "0 4px 12px rgba(0, 102, 255, 0.3)",
            }}
            onMouseOver={(e) => {
              if (!isJoining) {
                e.currentTarget.style.transform = "translateY(-2px)";
                e.currentTarget.style.boxShadow = "0 6px 16px rgba(0, 102, 255, 0.4)";
              }
            }}
            onMouseOut={(e) => {
              e.currentTarget.style.transform = "translateY(0)";
              e.currentTarget.style.boxShadow = "0 4px 12px rgba(0, 102, 255, 0.3)";
            }}
          >
            {isJoining ? "Connecting..." : hasInviteLink ? "Join Room" : "Create & Join Room"}
          </button>
        </form>
      </div>

      {/* Info Section - Only for new visitors */}
      {!hasInviteLink && (
        <div
          style={{
            maxWidth: "500px",
            width: "100%",
            marginTop: "2rem",
            padding: "1.5rem",
            background: "#0f0f0f",
            borderRadius: "8px",
            border: "1px solid #333",
          }}
        >
          <h3
            style={{
              fontSize: "0.95rem",
              marginBottom: "1rem",
              color: "#aaa",
            }}
          >
            How it works
          </h3>
          <div
            style={{
              display: "grid",
              gap: "0.75rem",
              fontSize: "0.85rem",
              color: "#888",
            }}
          >
            <div style={{ display: "flex", gap: "0.75rem" }}>
              <span style={{ color: "#0066ff", minWidth: "20px" }}>1.</span>
              <span>Create a room and get a shareable link</span>
            </div>
            <div style={{ display: "flex", gap: "0.75rem" }}>
              <span style={{ color: "#0066ff", minWidth: "20px" }}>2.</span>
              <span>Share the link with people you want to chat with</span>
            </div>
            <div style={{ display: "flex", gap: "0.75rem" }}>
              <span style={{ color: "#0066ff", minWidth: "20px" }}>3.</span>
              <span>Messages travel directly between your browsers via WebRTC</span>
            </div>
            <div style={{ display: "flex", gap: "0.75rem" }}>
              <span style={{ color: "#0066ff", minWidth: "20px" }}>4.</span>
              <span>The server only helps establish connections - it never sees your messages</span>
            </div>
          </div>
        </div>
      )}
    </div>
  );
}
