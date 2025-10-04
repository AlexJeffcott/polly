// DevTools registration script

// Register DevTools panel
chrome.devtools.panels.create(
  process.env["EXTENSION_NAME"] || "Extension",
  "assets/icon48.png",
  "devtools/panel.html",
  (panel) => {
    // Panel shown - currently no special handling needed
    panel.onShown.addListener(() => {
      // Reserved for future use
    });

    // Panel hidden - currently no special handling needed
    panel.onHidden.addListener(() => {
      // Reserved for future use
    });
  }
);
