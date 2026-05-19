// Test fixture: Electron main process
import { app, BrowserWindow, ipcMain } from "electron";

let mainWindow: BrowserWindow | null = null;

app.on("ready", () => {
  mainWindow = new BrowserWindow({
    width: 800,
    height: 600,
    webPreferences: {
      nodeIntegration: false,
      contextIsolation: true,
    },
  });

  mainWindow.loadFile("index.html");
});

ipcMain.on("message", (event, data) => {
  console.log("Received:", data);
  event.reply("response", { status: "ok" });
});
