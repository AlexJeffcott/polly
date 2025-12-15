import { WebSocketServer } from 'ws'
import type { AppState } from './types/state'

const state: AppState = {
  authenticated: false,
  subscriptions: new Set(),
  messageCount: 0,
}

const wss = new WebSocketServer({ port: 8080 })

interface AuthenticateMessage {
  type: 'authenticate'
  token: string
}

interface QueryMessage {
  type: 'query'
  query: string
}

interface CommandMessage {
  type: 'command'
  action: string
}

interface SubscribeMessage {
  type: 'subscribe'
  topic: string
}

interface UnsubscribeMessage {
  type: 'unsubscribe'
  topic: string
}

type RequestMessage =
  | AuthenticateMessage
  | QueryMessage
  | CommandMessage
  | SubscribeMessage
  | UnsubscribeMessage

function isAuthenticateMessage(msg: RequestMessage): msg is AuthenticateMessage {
  return msg.type === 'authenticate'
}

function isQueryMessage(msg: RequestMessage): msg is QueryMessage {
  return msg.type === 'query'
}

function isCommandMessage(msg: RequestMessage): msg is CommandMessage {
  return msg.type === 'command'
}

function isSubscribeMessage(msg: RequestMessage): msg is SubscribeMessage {
  return msg.type === 'subscribe'
}

function isUnsubscribeMessage(msg: RequestMessage): msg is UnsubscribeMessage {
  return msg.type === 'unsubscribe'
}

wss.on('connection', (ws) => {
  ws.on('message', (data) => {
    const message: RequestMessage = JSON.parse(data.toString())

    if (isAuthenticateMessage(message)) {
      // Handle authentication
      state.authenticated = true
      state.messageCount = state.messageCount + 1
      ws.send(JSON.stringify({ type: 'authenticated', success: true }))
    } else if (isQueryMessage(message)) {
      // Handle query
      state.messageCount = state.messageCount + 1
      ws.send(JSON.stringify({ type: 'query-result', data: [] }))
    } else if (isCommandMessage(message)) {
      // Handle command
      state.messageCount = state.messageCount + 1
      ws.send(JSON.stringify({ type: 'command-result', success: true }))
    } else if (isSubscribeMessage(message)) {
      // Handle subscribe
      state.subscriptions.add(message.topic)
      state.messageCount = state.messageCount + 1
      ws.send(JSON.stringify({ type: 'subscribed', topic: message.topic }))
    } else if (isUnsubscribeMessage(message)) {
      // Handle unsubscribe
      state.subscriptions.delete(message.topic)
      state.messageCount = state.messageCount + 1
      ws.send(JSON.stringify({ type: 'unsubscribed', topic: message.topic }))
    }
  })
})
