// Renderer process
import { ipcRenderer } from 'electron'

// Send message to main process
ipcRenderer.send('message', {
  type: 'open-file',
  path: '/path/to/file.txt'
})

// Listen for responses
ipcRenderer.on('file-opened', (event, data) => {
  console.log('File opened:', data)
})

ipcRenderer.on('file-saved', (event, data) => {
  console.log('File saved:', data)
})
