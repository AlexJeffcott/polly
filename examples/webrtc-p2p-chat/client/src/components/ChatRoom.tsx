import { useState } from "preact/hooks";
import { currentRoom, isSignalingConnected, messages, peers } from "../state";
import { MessageList } from "./MessageList";
import { PeerList } from "./PeerList";
import { ShareInvite } from "./ShareInvite";

interface Props {
  onLeave: () => void;
  onSendMessage: (text: string) => void;
}

/**
 * ChatRoom - Main chat interface
 */
export function ChatRoom({ onLeave, onSendMessage }: Props) {
  const [input, setInput] = useState("");

  const handleSubmit = (e: Event) => {
    e.preventDefault();

    if (input.trim()) {
      onSendMessage(input.trim());
      setInput("");
    }
  };

  return (
    <div
      style={{
        display: "flex",
        height: "100vh",
        background: "#0f0f0f",
      }}
    >
      {/* Sidebar */}
      <aside
        style={{
          width: "300px",
          padding: "1rem",
          background: "#0f0f0f",
          borderRight: "1px solid #333",
          display: "flex",
          flexDirection: "column",
          gap: "1rem",
        }}
      >
        {/* Header */}
        <div
          style={{
            padding: "1rem",
            background: "#1a1a1a",
            borderRadius: "8px",
            border: "1px solid #333",
          }}
        >
          <div style={{ fontSize: "0.8rem", color: "#888", marginBottom: "0.25rem" }}>Room</div>
          <div style={{ fontWeight: "bold", wordBreak: "break-all" }}>{currentRoom.value?.id}</div>
        </div>

        {/* Share Invite */}
        {currentRoom.value && <ShareInvite roomId={currentRoom.value.id} />}

        {/* Connection Status */}
        <div
          style={{
            padding: "0.75rem",
            background: "#1a1a1a",
            borderRadius: "8px",
            border: "1px solid #333",
            display: "flex",
            alignItems: "center",
            gap: "0.5rem",
          }}
        >
          <div
            style={{
              width: "8px",
              height: "8px",
              borderRadius: "50%",
              background: isSignalingConnected.value ? "#00ff00" : "#ff0000",
            }}
          />
          <span style={{ fontSize: "0.85rem" }}>
            {isSignalingConnected.value ? "Connected" : "Disconnected"}
          </span>
        </div>

        {/* Peer List */}
        <PeerList peers={peers.value} />

        {/* Leave Button */}
        <button
          onClick={onLeave}
          style={{
            marginTop: "auto",
            padding: "0.75rem",
            background: "#333",
            border: "none",
            borderRadius: "4px",
            color: "#fff",
            fontSize: "0.9rem",
            cursor: "pointer",
          }}
        >
          Leave Room
        </button>
      </aside>

      {/* Main Chat Area */}
      <main
        style={{
          flex: 1,
          display: "flex",
          flexDirection: "column",
        }}
      >
        {/* Messages */}
        <MessageList messages={messages.value} />

        {/* Input */}
        <form
          onSubmit={handleSubmit}
          style={{
            padding: "1rem",
            background: "#1a1a1a",
            borderTop: "1px solid #333",
            display: "flex",
            gap: "0.5rem",
          }}
        >
          <input
            type="text"
            value={input}
            onInput={(e) => setInput(e.currentTarget.value)}
            placeholder="Type a message..."
            style={{
              flex: 1,
              padding: "0.75rem",
              background: "#0f0f0f",
              border: "1px solid #333",
              borderRadius: "4px",
              color: "#fff",
              fontSize: "1rem",
            }}
          />
          <button
            type="submit"
            disabled={!input.trim() || peers.value.length === 0}
            style={{
              padding: "0.75rem 1.5rem",
              background: "#0066ff",
              border: "none",
              borderRadius: "4px",
              color: "#fff",
              fontSize: "1rem",
              fontWeight: "bold",
              cursor: input.trim() && peers.value.length > 0 ? "pointer" : "not-allowed",
              opacity: input.trim() && peers.value.length > 0 ? 1 : 0.5,
            }}
          >
            Send
          </button>
        </form>

        {peers.value.length === 0 && (
          <div
            style={{
              position: "absolute",
              top: "50%",
              left: "50%",
              transform: "translate(-50%, -50%)",
              textAlign: "center",
              color: "#666",
            }}
          >
            <div style={{ fontSize: "2rem", marginBottom: "0.5rem" }}>👥</div>
            <div>Waiting for peers to join...</div>
            <div style={{ fontSize: "0.85rem", marginTop: "0.5rem" }}>
              Share room ID: <strong style={{ color: "#0066ff" }}>{currentRoom.value?.id}</strong>
            </div>
          </div>
        )}
      </main>
    </div>
  );
}
