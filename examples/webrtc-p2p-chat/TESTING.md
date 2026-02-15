# WebRTC P2P Chat - Testing Guide

## Quick Test: Share/Invite Flow

### Prerequisites
- Dev servers running: `bun run dev`
- Browser tabs or separate browser windows

### Test Steps

#### 1. Create a Room (Browser Tab 1)
1. Navigate to `http://localhost:5173`
2. Enter your name (e.g., "Alice")
3. Click "Generate" to create a random room ID
4. Click "Join Room"
5. Wait for the chat room to load

#### 2. Copy Invite Link
1. In the sidebar, find the "Invite Others" section
2. Click the "📋 Copy" button
3. Verify the button changes to "✓ Copied!" (green background)
4. The copied link should look like: `http://localhost:5173/?room=abc123`

#### 3. Join from Invite Link (Browser Tab 2)
1. Open a new browser tab
2. Paste the copied invite link into the address bar
3. Press Enter
4. **Expected:** Room ID field is automatically filled with the room ID from the link
5. **Expected:** Your display name is pre-filled if you've used the app before
6. Enter a different name (e.g., "Bob")
7. Click "Join Room"

#### 4. Verify Connection
1. **In Tab 2 (Bob):**
   - You should see "Alice" in the peer list
   - Connection status should change: Connecting → Connected
   - Latency should appear after a moment

2. **In Tab 1 (Alice):**
   - You should see "Bob" appear in the peer list
   - Same connection status progression

#### 5. Test Messaging
1. In either tab, type a message and press Enter
2. **Expected:** Message appears in both tabs
3. **Expected:** Message shows sender name and timestamp
4. Try sending messages from both tabs

#### 6. Test Multiple Peers (Optional)
1. Copy the invite link again
2. Open a third tab (or use a different browser)
3. Paste the link and join as "Charlie"
4. **Expected:** All three peers see each other
5. **Expected:** Messages sent by any peer appear in all tabs

## Mobile/Touch Device Testing

### Test Native Share API
1. On a mobile device or browser that supports Web Share API
2. Join a room
3. Look for the "📱 Share" button in the "Invite Others" section
4. Click it to open the native share sheet
5. Share via your preferred method (Messages, Email, etc.)

### Test Received Invite
1. Receive the shared link on another device
2. Tap the link
3. **Expected:** Room ID auto-filled
4. Join and verify connection works across devices

## Edge Cases to Test

### Empty Room
1. Join a room that no one else is in
2. **Expected:** See "No peers connected yet" message
3. **Expected:** Can still send messages (stored locally)

### Disconnect/Reconnect
1. In one tab, close the browser tab
2. **Expected:** Other peers see "disconnected" status
3. Open new tab and rejoin same room
4. **Expected:** Reconnects successfully

### Invalid Room ID
1. Manually create URL with invalid characters: `http://localhost:5173/?room=<script>`
2. **Expected:** App handles gracefully, no XSS

### Long Room Session
1. Keep room open for several minutes
2. **Expected:** Connection stays stable
3. **Expected:** Latency measurements continue to update

## Verification Checklist

- [ ] Copy button changes to "✓ Copied!" when clicked
- [ ] Invite link includes room ID parameter
- [ ] Room ID auto-fills from URL parameter
- [ ] Display name pre-fills from saved state
- [ ] Multiple tabs can join same room as separate peers
- [ ] Messages sent in one tab appear in all tabs
- [ ] Peer list updates when peers join/leave
- [ ] Connection status indicators work correctly
- [ ] Native Share button appears on supported devices
- [ ] Native Share API works when available

## Known Issues

None currently. Report issues to the development team.

## Performance Notes

- WebRTC connections are peer-to-peer, so scalability is limited
- For N peers, each peer maintains N-1 connections
- Recommended max: 4-6 peers per room for good performance
