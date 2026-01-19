import { useState } from "preact/hooks";
import { ChatRoom } from "./components/ChatRoom";
import { RoomLobby } from "./components/RoomLobby";
import { currentRoom, displayName as displayNameState } from "./state";
import { PeerManager } from "./webrtc/peer-manager";

/**
 * Main App Component
 */

// Signaling server URL (adjust if needed)
const SIGNALING_URL = "ws://localhost:3001/signaling";

let peerManager: PeerManager | null = null;

export function App() {
  const [error, setError] = useState<string | null>(null);

  const handleJoinRoom = async (roomId: string, displayName: string) => {
    try {
      setError(null);

      // Store display name
      displayNameState.value = displayName;

      // Create peer manager
      peerManager = new PeerManager(SIGNALING_URL);

      // Connect to signaling server
      await peerManager.connect();

      // Join room
      peerManager.joinRoom(roomId);

      // Update state
      currentRoom.value = {
        id: roomId,
        joinedAt: Date.now(),
      };
    } catch (err) {
      setError(err instanceof Error ? err.message : "Failed to join room");
      throw err;
    }
  };

  const handleLeaveRoom = () => {
    if (peerManager) {
      peerManager.disconnect();
      peerManager = null;
    }
    currentRoom.value = null;
    setError(null);
  };

  const handleSendMessage = (text: string) => {
    if (peerManager) {
      peerManager.sendMessage(text);
    }
  };

  return (
    <div>
      {error && (
        <div
          style={{
            position: "fixed",
            top: "1rem",
            left: "50%",
            transform: "translateX(-50%)",
            zIndex: 1000,
            padding: "1rem 1.5rem",
            background: "#ff000020",
            border: "1px solid #ff0000",
            borderRadius: "4px",
            color: "#ff6666",
          }}
        >
          {error}
          <button
            onClick={() => setError(null)}
            style={{
              marginLeft: "1rem",
              padding: "0.25rem 0.5rem",
              background: "transparent",
              border: "1px solid #ff6666",
              borderRadius: "4px",
              color: "#ff6666",
              cursor: "pointer",
            }}
          >
            Dismiss
          </button>
        </div>
      )}

      {currentRoom.value ? (
        <ChatRoom onLeave={handleLeaveRoom} onSendMessage={handleSendMessage} />
      ) : (
        <RoomLobby onJoin={handleJoinRoom} />
      )}
    </div>
  );
}
