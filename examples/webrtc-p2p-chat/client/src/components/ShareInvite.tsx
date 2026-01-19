import { useState } from "preact/hooks";

interface Props {
  roomId: string;
}

/**
 * ShareInvite - Share room invitation link
 */
export function ShareInvite({ roomId }: Props) {
  const [copied, setCopied] = useState(false);
  const inviteUrl = `${window.location.origin}/?room=${roomId}`;

  const handleCopyLink = async () => {
    try {
      await navigator.clipboard.writeText(inviteUrl);
      setCopied(true);
      setTimeout(() => setCopied(false), 2000);
    } catch (error) {
      console.error("Failed to copy:", error);
      // Fallback: select the text
      const input = document.querySelector<HTMLInputElement>("#invite-url");
      if (input) {
        input.select();
        document.execCommand("copy");
        setCopied(true);
        setTimeout(() => setCopied(false), 2000);
      }
    }
  };

  const handleShare = async () => {
    if (navigator.share !== undefined) {
      try {
        await navigator.share({
          title: "Join my chat room",
          text: `Join me in this private P2P chat room!`,
          url: inviteUrl,
        });
      } catch (error) {
        // User cancelled or error - ignore
        if ((error as Error).name !== "AbortError") {
          console.error("Share failed:", error);
        }
      }
    } else {
      // Fallback to copy
      handleCopyLink();
    }
  };

  return (
    <div
      style={{
        padding: "1rem",
        background: "#1a1a1a",
        borderRadius: "8px",
        border: "1px solid #333",
      }}
    >
      <div
        style={{
          display: "flex",
          alignItems: "center",
          justifyContent: "space-between",
          marginBottom: "0.75rem",
        }}
      >
        <h3 style={{ fontSize: "0.9rem", color: "#aaa", margin: 0 }}>Invite Others</h3>
        {navigator.share !== undefined && (
          <button
            onClick={handleShare}
            style={{
              padding: "0.5rem 1rem",
              background: "#0066ff",
              border: "none",
              borderRadius: "4px",
              color: "#fff",
              fontSize: "0.85rem",
              cursor: "pointer",
              display: "flex",
              alignItems: "center",
              gap: "0.5rem",
            }}
          >
            📱 Share
          </button>
        )}
      </div>

      <div
        style={{
          display: "flex",
          gap: "0.5rem",
          alignItems: "stretch",
        }}
      >
        <input
          id="invite-url"
          type="text"
          readOnly
          value={inviteUrl}
          onClick={(e) => e.currentTarget.select()}
          style={{
            flex: 1,
            padding: "0.75rem",
            background: "#0f0f0f",
            border: "1px solid #333",
            borderRadius: "4px",
            color: "#fff",
            fontSize: "0.85rem",
            fontFamily: "monospace",
          }}
        />
        <button
          onClick={handleCopyLink}
          style={{
            padding: "0.75rem 1rem",
            background: copied ? "#00aa00" : "#333",
            border: "none",
            borderRadius: "4px",
            color: "#fff",
            fontSize: "0.85rem",
            cursor: "pointer",
            minWidth: "100px",
            transition: "background 0.2s",
          }}
        >
          {copied ? "✓ Copied!" : "📋 Copy"}
        </button>
      </div>

      <p
        style={{
          fontSize: "0.75rem",
          color: "#666",
          margin: "0.75rem 0 0 0",
        }}
      >
        💡 Share this link with others or open it in another tab to test
      </p>
    </div>
  );
}
