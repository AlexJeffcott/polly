// Minimal handlers for testing - just USER_LOGIN and USER_LOGOUT
import { getMessageBus } from '@/shared/lib/message-bus'

const messageBus = getMessageBus('background')

// Example state object
const state = {
  user: {
    loggedIn: false,
    role: "guest" as "admin" | "user" | "guest",
  },
}

// USER_LOGIN handler - sets loggedIn=true, role from payload
messageBus.on("USER_LOGIN", (payload: { userId: string; role: "admin" | "user" }) => {
  state.user.loggedIn = true
  state.user.role = payload.role
})

// USER_LOGOUT handler - sets loggedIn=false, role=guest
messageBus.on("USER_LOGOUT", () => {
  state.user.loggedIn = false
  state.user.role = "guest"
})
