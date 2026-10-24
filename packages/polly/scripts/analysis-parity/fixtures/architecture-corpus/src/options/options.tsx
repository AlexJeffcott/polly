// Options page: stores preferences.
// Second line comment.

export function Options({ theme }: { theme: "dark" | "light" }) {
  chrome.storage.sync.set({ theme });
  return <form>{theme}</form>;
}
