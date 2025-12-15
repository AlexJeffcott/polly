/**
 * Full-Featured Example - Popup
 *
 * Demonstrates real-world extension patterns:
 * - User authentication
 * - Bookmark management
 * - Tab operations
 * - Settings management
 * - Reactive state with signals
 */

import { getMessageBus } from "@fairfox/polly/message-bus";
import { $sharedState } from "@fairfox/polly/state";
import { signal } from "@preact/signals";
import { render } from "preact";
import type { AllMessages, Bookmark } from "../shared/types/messages";

const bus = getMessageBus<AllMessages>("popup");

// Shared state
const bookmarks = $sharedState<Bookmark[]>("bookmarks", []);

// Local UI state
const username = signal("");
const token = signal("");
const isLoggedIn = signal(false);
const currentUser = signal("");
const newBookmarkUrl = signal("");
const newBookmarkTitle = signal("");
const currentTab = signal<{ id?: number; url?: string; title?: string } | null>(
  null,
);
const statusMessage = signal("");

// Type guards
function hasUserData(value: unknown): value is { username: string } {
  return value !== null && typeof value === "object" && "username" in value;
}

function isSuccessResponse(value: unknown): value is { success: true } {
  return value !== null && typeof value === "object" && "success" in value;
}

// Check if user is logged in on mount
(async () => {
  const result = await bus.adapters.storage.get("user");
  if (hasUserData(result.user)) {
    isLoggedIn.value = true;
    currentUser.value = result.user.username;
  }
})();

function Popup() {
  const handleLogin = async () => {
    if (!username.value || !token.value) {
      statusMessage.value = "Please enter username and token";
      return;
    }

    try {
      const result = await bus.send({
        type: "USER_LOGIN",
        username: username.value,
        token: token.value,
      });

      if (isSuccessResponse(result)) {
        isLoggedIn.value = true;
        currentUser.value = username.value;
        statusMessage.value = "Login successful!";
        username.value = "";
        token.value = "";
      }
    } catch (error) {
      statusMessage.value = `Login failed: ${error}`;
    }
  };

  const handleLogout = async () => {
    try {
      await bus.send({ type: "USER_LOGOUT" });
      isLoggedIn.value = false;
      currentUser.value = "";
      statusMessage.value = "Logged out";
    } catch (error) {
      statusMessage.value = `Logout failed: ${error}`;
    }
  };

  const handleAddBookmark = async () => {
    if (!newBookmarkUrl.value || !newBookmarkTitle.value) {
      statusMessage.value = "Please enter URL and title";
      return;
    }

    try {
      const result = await bus.send({
        type: "BOOKMARK_ADD",
        url: newBookmarkUrl.value,
        title: newBookmarkTitle.value,
      });

      if (isSuccessResponse(result)) {
        statusMessage.value = "Bookmark added!";
        newBookmarkUrl.value = "";
        newBookmarkTitle.value = "";
      }
    } catch (error) {
      statusMessage.value = `Failed to add bookmark: ${error}`;
    }
  };

  const handleRemoveBookmark = async (id: string) => {
    try {
      await bus.send({ type: "BOOKMARK_REMOVE", id });
      statusMessage.value = "Bookmark removed";
    } catch (error) {
      statusMessage.value = `Failed to remove bookmark: ${error}`;
    }
  };

  const handleGetCurrentTab = async () => {
    try {
      const result = await bus.send({ type: "TAB_GET_CURRENT" });

      if (result && "tab" in result) {
        const tab = result.tab;
        currentTab.value = {
          id: tab.id,
          url: tab.url,
          title: tab.title,
        };
        statusMessage.value = "Current tab retrieved";
      }
    } catch (error) {
      statusMessage.value = `Failed to get tab: ${error}`;
    }
  };

  const handleBookmarkCurrentTab = async () => {
    if (!currentTab.value?.url || !currentTab.value?.title) {
      statusMessage.value = "No current tab info";
      return;
    }

    try {
      await bus.send({
        type: "BOOKMARK_ADD",
        url: currentTab.value.url,
        title: currentTab.value.title,
      });
      statusMessage.value = "Current tab bookmarked!";
    } catch (error) {
      statusMessage.value = `Failed to bookmark tab: ${error}`;
    }
  };

  const handleUpdateSettings = async (updates: Record<string, unknown>) => {
    try {
      await bus.send({ type: "SETTINGS_UPDATE", ...updates });
      statusMessage.value = "Settings updated";
    } catch (error) {
      statusMessage.value = `Failed to update settings: ${error}`;
    }
  };

  return (
    <div class="popup" style={{ padding: "16px", minWidth: "300px" }}>
      <header style={{ marginBottom: "16px" }}>
        <h1 style={{ margin: "0 0 8px 0", fontSize: "20px" }}>
          Full-Featured Example
        </h1>
        {statusMessage.value && (
          <div
            style={{
              padding: "8px",
              background: "#f0f0f0",
              borderRadius: "4px",
              fontSize: "12px",
            }}
          >
            {statusMessage.value}
          </div>
        )}
      </header>

      <main>
        {/* Authentication Section */}
        <section
          style={{
            marginBottom: "16px",
            paddingBottom: "16px",
            borderBottom: "1px solid #e0e0e0",
          }}
        >
          <h2 style={{ fontSize: "16px", marginBottom: "8px" }}>
            Authentication
          </h2>
          {!isLoggedIn.value ? (
            <div>
              <input
                type="text"
                placeholder="Username"
                value={username.value}
                onInput={(e) =>
                  (username.value = (e.target as HTMLInputElement).value)
                }
                style={{ width: "100%", padding: "4px", marginBottom: "4px" }}
              />
              <input
                type="password"
                placeholder="Token"
                value={token.value}
                onInput={(e) =>
                  (token.value = (e.target as HTMLInputElement).value)
                }
                style={{ width: "100%", padding: "4px", marginBottom: "4px" }}
              />
              <button
                onClick={handleLogin}
                style={{ width: "100%", padding: "8px" }}
              >
                Login
              </button>
            </div>
          ) : (
            <div>
              <p>
                Logged in as: <strong>{currentUser.value}</strong>
              </p>
              <button
                onClick={handleLogout}
                style={{ width: "100%", padding: "8px" }}
              >
                Logout
              </button>
            </div>
          )}
        </section>

        {/* Bookmarks Section */}
        <section
          style={{
            marginBottom: "16px",
            paddingBottom: "16px",
            borderBottom: "1px solid #e0e0e0",
          }}
        >
          <h2 style={{ fontSize: "16px", marginBottom: "8px" }}>Bookmarks</h2>
          <div style={{ marginBottom: "8px" }}>
            <input
              type="text"
              placeholder="URL"
              value={newBookmarkUrl.value}
              onInput={(e) =>
                (newBookmarkUrl.value = (e.target as HTMLInputElement).value)
              }
              style={{ width: "100%", padding: "4px", marginBottom: "4px" }}
            />
            <input
              type="text"
              placeholder="Title"
              value={newBookmarkTitle.value}
              onInput={(e) =>
                (newBookmarkTitle.value = (e.target as HTMLInputElement).value)
              }
              style={{ width: "100%", padding: "4px", marginBottom: "4px" }}
            />
            <button
              onClick={handleAddBookmark}
              style={{ width: "100%", padding: "8px" }}
            >
              Add Bookmark
            </button>
          </div>
          <div style={{ maxHeight: "150px", overflowY: "auto" }}>
            {bookmarks.value.length === 0 ? (
              <p style={{ fontSize: "12px", color: "#666" }}>
                No bookmarks yet
              </p>
            ) : (
              bookmarks.value.map((bookmark) => (
                <div
                  key={bookmark.id}
                  style={{
                    padding: "8px",
                    marginBottom: "4px",
                    background: "#f9f9f9",
                    borderRadius: "4px",
                    display: "flex",
                    justifyContent: "space-between",
                    alignItems: "center",
                  }}
                >
                  <div style={{ flex: 1, minWidth: 0 }}>
                    <div
                      style={{
                        fontWeight: "bold",
                        fontSize: "12px",
                        overflow: "hidden",
                        textOverflow: "ellipsis",
                      }}
                    >
                      {bookmark.title}
                    </div>
                    <div
                      style={{
                        fontSize: "10px",
                        color: "#666",
                        overflow: "hidden",
                        textOverflow: "ellipsis",
                      }}
                    >
                      {bookmark.url}
                    </div>
                  </div>
                  <button
                    onClick={() => handleRemoveBookmark(bookmark.id)}
                    style={{
                      marginLeft: "8px",
                      padding: "4px 8px",
                      fontSize: "11px",
                    }}
                  >
                    Remove
                  </button>
                </div>
              ))
            )}
          </div>
        </section>

        {/* Tab Operations Section */}
        <section
          style={{
            marginBottom: "16px",
            paddingBottom: "16px",
            borderBottom: "1px solid #e0e0e0",
          }}
        >
          <h2 style={{ fontSize: "16px", marginBottom: "8px" }}>Current Tab</h2>
          <button
            onClick={handleGetCurrentTab}
            style={{ width: "100%", padding: "8px", marginBottom: "8px" }}
          >
            Get Current Tab Info
          </button>
          {currentTab.value && (
            <div
              style={{
                padding: "8px",
                background: "#f9f9f9",
                borderRadius: "4px",
                fontSize: "12px",
              }}
            >
              <div>
                <strong>Title:</strong> {currentTab.value.title}
              </div>
              <div style={{ overflow: "hidden", textOverflow: "ellipsis" }}>
                <strong>URL:</strong> {currentTab.value.url}
              </div>
              <button
                onClick={handleBookmarkCurrentTab}
                style={{ width: "100%", padding: "6px", marginTop: "8px" }}
              >
                Bookmark This Tab
              </button>
            </div>
          )}
        </section>

        {/* Quick Settings */}
        <section>
          <h2 style={{ fontSize: "16px", marginBottom: "8px" }}>
            Quick Settings
          </h2>
          <div style={{ fontSize: "12px" }}>
            <label style={{ display: "block", marginBottom: "4px" }}>
              <input
                type="checkbox"
                onChange={(e) =>
                  handleUpdateSettings({
                    autoSync: (e.target as HTMLInputElement).checked,
                  })
                }
              />{" "}
              Auto Sync
            </label>
            <label style={{ display: "block", marginBottom: "4px" }}>
              <input
                type="checkbox"
                onChange={(e) =>
                  handleUpdateSettings({
                    debugMode: (e.target as HTMLInputElement).checked,
                  })
                }
              />{" "}
              Debug Mode
            </label>
            <label style={{ display: "block", marginBottom: "4px" }}>
              <input
                type="checkbox"
                onChange={(e) =>
                  handleUpdateSettings({
                    notifications: (e.target as HTMLInputElement).checked,
                  })
                }
              />{" "}
              Notifications
            </label>
          </div>
        </section>
      </main>
    </div>
  );
}

const root = document.getElementById("root");
if (root) {
  render(<Popup />, root);
}
