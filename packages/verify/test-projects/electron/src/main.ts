import { app, BrowserWindow, ipcMain } from 'electron'

interface OpenFileMessage {
  type: 'open-file'
  path: string
}

interface SaveFileMessage {
  type: 'save-file'
  path: string
  content: string
}

type IPCMessage = OpenFileMessage | SaveFileMessage

function createWindow() {
  const win = new BrowserWindow({
    width: 800,
    height: 600,
    webPreferences: {
      nodeIntegration: false,
      contextIsolation: true,
    }
  })

  win.loadFile('index.html')
}

// IPC message handlers
ipcMain.on('message', (event, message: IPCMessage) => {
  if (message.type === 'open-file') {
    console.log('Opening file:', message.path)
    event.reply('file-opened', { success: true })
  } else if (message.type === 'save-file') {
    console.log('Saving file:', message.path)
    event.reply('file-saved', { success: true })
  }
})

app.whenReady().then(() => {
  createWindow()

  app.on('activate', () => {
    if (BrowserWindow.getAllWindows().length === 0) {
      createWindow()
    }
  })
})

app.on('window-all-closed', () => {
  if (process.platform !== 'darwin') {
    app.quit()
  }
})
