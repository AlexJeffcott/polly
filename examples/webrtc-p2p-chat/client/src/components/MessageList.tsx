import { useEffect, useRef } from "preact/hooks";
import { displayName } from "../state";
import type { ChatMessage } from "../types";

interface Props {
  messages: ChatMessage[];
}

/**
 * MessageList - Display chat messages
 */
export function MessageList({ messages }: Props) {
  const scrollRef = useRef<HTMLDivElement>(null);

  // Auto-scroll to bottom on new messages
  useEffect(() => {
    if (scrollRef.current) {
      scrollRef.current.scrollTop = scrollRef.current.scrollHeight;
    }
  }, [messages]);

  const formatTime = (timestamp: number) => {
    const date = new Date(timestamp);
    return date.toLocaleTimeString("en-US", {
      hour: "2-digit",
      minute: "2-digit",
    });
  };

  return (
    <div
      ref={scrollRef}
      style={{
        flex: 1,
        overflowY: "auto",
        padding: "1rem",
        display: "flex",
        flexDirection: "column",
        gap: "0.75rem",
        background: "#0a0a0a",
      }}
    >
      {messages.length === 0 ? (
        <div
          style={{
            display: "flex",
            flexDirection: "column",
            alignItems: "center",
            justifyContent: "center",
            height: "100%",
            color: "#666",
            textAlign: "center",
            padding: "2rem",
          }}
        >
          <div
            style={{
              fontSize: "3rem",
              marginBottom: "1rem",
              opacity: 0.2,
            }}
          >
            💬
          </div>
          <div
            style={{
              fontSize: "1rem",
              marginBottom: "0.5rem",
              color: "#888",
            }}
          >
            No messages yet
          </div>
          <div
            style={{
              fontSize: "0.85rem",
              color: "#555",
              maxWidth: "300px",
            }}
          >
            Type a message below to start the conversation. Messages are sent peer-to-peer!
          </div>
        </div>
      ) : (
        messages.map((message) => {
          const isOwnMessage = message.fromName === displayName.value;

          return (
            <div
              key={message.id}
              style={{
                display: "flex",
                flexDirection: "column",
                alignItems: isOwnMessage ? "flex-end" : "flex-start",
                animation: "slideIn 0.2s ease-out",
              }}
            >
              {/* Add animation keyframes once */}
              {messages.indexOf(message) === 0 && (
                <style>{`
                  @keyframes slideIn {
                    from {
                      opacity: 0;
                      transform: translateY(10px);
                    }
                    to {
                      opacity: 1;
                      transform: translateY(0);
                    }
                  }
                `}</style>
              )}

              <div
                style={{
                  fontSize: "0.7rem",
                  color: "#666",
                  marginBottom: "0.25rem",
                  marginLeft: isOwnMessage ? "0" : "0.5rem",
                  marginRight: isOwnMessage ? "0.5rem" : "0",
                }}
              >
                <span style={{ fontWeight: "bold", color: "#888" }}>{message.fromName}</span>{" "}
                <span style={{ color: "#555" }}>{formatTime(message.timestamp)}</span>
              </div>
              <div
                style={{
                  maxWidth: "70%",
                  padding: "0.75rem 1rem",
                  borderRadius: isOwnMessage ? "12px 12px 4px 12px" : "12px 12px 12px 4px",
                  background: isOwnMessage
                    ? "linear-gradient(135deg, #0066ff 0%, #0088ff 100%)"
                    : "#1a1a1a",
                  border: isOwnMessage ? "none" : "1px solid #333",
                  wordWrap: "break-word",
                  boxShadow: isOwnMessage
                    ? "0 2px 8px rgba(0, 102, 255, 0.3)"
                    : "0 2px 4px rgba(0, 0, 0, 0.2)",
                  fontSize: "0.95rem",
                  lineHeight: "1.5",
                }}
              >
                {message.text}
              </div>
              {isOwnMessage && !message.delivered && (
                <div
                  style={{
                    fontSize: "0.65rem",
                    color: "#ffaa00",
                    marginTop: "0.25rem",
                    marginRight: "0.5rem",
                    display: "flex",
                    alignItems: "center",
                    gap: "0.25rem",
                  }}
                >
                  <div
                    style={{
                      width: "6px",
                      height: "6px",
                      borderRadius: "50%",
                      background: "#ffaa00",
                      animation: "pulse 2s cubic-bezier(0.4, 0, 0.6, 1) infinite",
                    }}
                  />
                  Sending...
                </div>
              )}
            </div>
          );
        })
      )}
    </div>
  );
}
