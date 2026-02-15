# Todo List Example with Formal Verification

A complete, working todo list extension that demonstrates both **traditional testing** and **formal verification** using TLA+ model checking.

## Features

- ✅ User authentication (login/logout)
- ✅ Add, toggle, and remove todos
- ✅ Clear completed todos
- ✅ 100 todo limit enforcement
- ✅ **Reactive state with `$sharedState`** - automatic sync and persistence
- ✅ Preact-based popup UI with automatic updates
- ✅ Full unit test coverage
- ✅ Formal verification with TLA+
- ✅ **Framework double-execution prevention** (see below)

## Project Structure

```
todo-list/
├── src/
│   ├── background/
│   │   ├── index.ts           # Background entry point
│   │   ├── handlers.ts        # Message handlers with verification primitives
│   │   └── state.ts           # Application state
│   ├── popup/
│   │   ├── index.tsx          # Popup UI
│   │   ├── popup.html         # Popup HTML
│   │   └── styles.css         # Styles
│   └── shared/
│       └── types.ts           # Shared TypeScript types
├── tests/
│   └── handlers.test.ts       # Unit tests
├── verification/
│   ├── verify.ts              # Verification script
│   ├── verify.config.ts       # Verification bounds
│   └── output/                # Generated TLA+ specs
└── manifest.json
```

## Reactive State Management

This example uses Polly's reactive state primitives for automatic synchronization and persistence:

```typescript
// src/background/state.ts
import { $sharedState } from "@fairfox/polly/state";

// Reactive state - automatically syncs across contexts and persists to storage
export const user = $sharedState<User>("user", {
  id: null,
  name: "Guest",
  role: "guest",
  loggedIn: false,
});

export const todos = $sharedState<Todo[]>("todos", []);
```

**Benefits:**
- ✅ **Automatic synchronization** - State changes in background script instantly appear in popup
- ✅ **Automatic persistence** - State survives browser restarts
- ✅ **Reactive UI** - Components automatically re-render when state changes
- ✅ **Type-safe** - Full TypeScript support with type inference
- ✅ **No manual querying** - No need to call `GET_STATE` after every action

### How It Works

In the **background script**, handlers update state directly:

```typescript
bus.on("TODO_ADD", (payload) => {
  const newTodo = { id: generateId(), text: payload.text, ... };
  todos.value = [...todos.value, newTodo];  // Automatically syncs!
  return { success: true, todo: newTodo };
});
```

In the **popup UI**, components access state directly:

```typescript
function App() {
  // State automatically updates - no manual fetching needed!
  return (
    <div>
      <p>Total todos: {todos.value.length}</p>
      {todos.value.map(todo => <TodoItem todo={todo} />)}
    </div>
  );
}
```

**Old way (manual sync):**
```typescript
const handleAddTodo = async () => {
  await bus.send({ type: "TODO_ADD", text });
  const newState = await bus.send({ type: "GET_STATE" });  // ❌ Manual fetch
  setState(newState);  // ❌ Manual update
};
```

**New way (automatic sync):**
```typescript
const handleAddTodo = async () => {
  await bus.send({ type: "TODO_ADD", text });
  // ✅ State automatically syncs - UI updates automatically!
};
```

## Running the Extension

### Development

```bash
bun run dev
```

This watches for changes and rebuilds automatically.

### Production Build

```bash
bun run build:prod
```

### Load in Browser

1. Open Chrome/Edge
2. Go to `chrome://extensions`
3. Enable "Developer mode"
4. Click "Load unpacked"
5. Select `dist/` directory

## Testing

### Unit Tests

Run traditional unit tests:

```bash
bun test
```

These tests verify:
- User authentication logic
- Todo CRUD operations
- State transitions
- Edge cases

**Limitations of traditional tests:**
- Only test paths you explicitly write
- Hard to test concurrent scenarios
- Can miss race conditions
- No exhaustive coverage

### Formal Verification

Run TLA+ model checker:

```bash
bun run verify
```

This:
1. Extracts all handlers from source code
2. Parses `requires()` and `ensures()` primitives
3. Generates TLA+ specification
4. (Optional) Runs TLC to verify all execution paths

**What verification catches:**
- ✅ All possible message orderings
- ✅ All concurrent execution paths
- ✅ Race conditions
- ✅ Invariant violations
- ✅ Edge cases you didn't think of

To run the TLC model checker (requires TLA+ Toolbox):

```bash
cd verification/output
tlc TodoList.tla -config TodoList.cfg
```

## Verification Primitives

The handlers use verification primitives to specify contracts:

### Example: USER_LOGIN

```typescript
bus.on('USER_LOGIN', (payload) => {
  // Preconditions - must be true before handler runs
  requires(state.user.loggedIn === false, 'User must not be logged in')
  requires(payload.userId !== null, 'User ID must be provided')

  // State changes
  state.user.loggedIn = true
  state.user.id = payload.userId
  state.user.role = payload.role

  // Postconditions - must be true after handler completes
  ensures(state.user.loggedIn === true, 'User must be logged in')
  ensures(state.user.id === payload.userId, 'User ID must match')
  ensures(state.user.role !== 'guest', 'User must have non-guest role')
})
```

TLC will verify these assertions hold in **all possible execution paths**, including:
- Different message orderings
- Concurrent operations
- Edge cases
- Race conditions

### Verified State Handlers

For any application using Polly's state primitives (Chrome extensions, multi-tab PWAs, WebSocket apps, reactive architectures), you can enable TLA+ verification with `{ verify: true }`:

```typescript
// Enable verification discovery
export const authState = $sharedState('auth', {
  loggedIn: false,
  userId: null,
}, { verify: true });

// Standalone functions are automatically discovered
export function handleLogin(userId: string): void {
  requires(!authState.value.loggedIn, 'Must not be logged in');
  authState.value = { ...authState.value, loggedIn: true, userId };
  ensures(authState.value.loggedIn, 'Must be logged in');
}
```

This pattern works universally across all Polly applications. See [docs/STATE.md](../../docs/STATE.md#verify-tla-verification) for full documentation.

## Framework Double-Execution Prevention

This example demonstrates the framework's built-in protection against double-execution bugs.

### The Bug We Prevented

**Problem:** If both `MessageBus` and `MessageRouter` register `chrome.runtime.onMessage` listeners, every handler executes **twice** for every message. This was happening in an early version of this example.

**Result:** Adding one todo created two todos, deleting one deleted two, etc.

### How The Framework Prevents This

#### 1. Correct API Usage

The background script uses `createBackground()` instead of `getMessageBus('background')`:

```typescript
// src/background/handlers.ts
import { createBackground } from '@fairfox/polly/background'

const bus = createBackground()  // ✅ Correct!
```

**Why this matters:**
- `createBackground()` creates MessageBus WITHOUT a listener
- Then creates MessageRouter WITH a listener
- Result: Only ONE listener total, no double execution

**What NOT to do:**
```typescript
// ❌ WRONG - Don't do this!
const bus = getMessageBus('background')  // Creates listener
new MessageRouter(bus)  // Creates ANOTHER listener
// Result: Double execution bug!
```

#### 2. Singleton Enforcement

The framework prevents multiple `MessageRouter` instances:

```typescript
const bus1 = createBackground()  // ✅ OK
const bus2 = createBackground()  // 🔴 ERROR: MessageRouter already exists!
```

#### 3. Listener Count Warning

If multiple `chrome.runtime.onMessage` listeners are registered, you'll see:

```
⚠️  WARNING: 2 chrome.runtime.onMessage listeners registered!
Multiple listeners will cause message handlers to execute multiple times.
```

#### 4. Development-Mode Execution Tracking

In development, if a handler executes twice for the same message:

```
🔴 DOUBLE EXECUTION DETECTED

Handler "TODO_ADD" executed 2 times for message abc-123.

Fix: Ensure only ONE listener is registered. In background scripts,
use createBackground() instead of getMessageBus().
```

### Testing Protection

Run the framework protection tests:

```bash
bun test tests/framework-protection.test.ts
```

These tests document:
- Why `createBackground()` is needed
- What happens if misconfigured
- How the framework protects you

### Learn More

See the [Background Setup Guide](../../docs/BACKGROUND_SETUP.md) for complete documentation.

---

## Handlers

| Message | Preconditions | Postconditions | Description |
|---------|---------------|----------------|-------------|
| `USER_LOGIN` | Not logged in, valid userId | Logged in, correct role | Authenticate user |
| `USER_LOGOUT` | Logged in | Logged out, guest role | Logout user |
| `TODO_ADD` | < 100 todos, valid text | Count increased by 1 | Add new todo |
| `TODO_TOGGLE` | Todo exists | Completed state toggled | Toggle todo completion |
| `TODO_REMOVE` | Todo exists | Count decreased by 1, todo removed | Remove todo |
| `TODO_CLEAR_COMPLETED` | - | Only incomplete todos remain | Clear completed |
| `GET_STATE` | - | - | Query current state |
| `GET_TODOS` | - | - | Query filtered todos |

## Comparison: Tests vs Verification

### Traditional Tests

**Pros:**
- Fast to write
- Easy to debug
- Good for specific scenarios

**Cons:**
- Only test what you write
- Hard to test concurrency
- Can miss edge cases

**Example:**
```typescript
test('can add todo', () => {
  state.todos.push({ id: '1', text: 'Test', completed: false })
  expect(state.todos.length).toBe(1)
})
```

### Formal Verification

**Pros:**
- Exhaustive coverage
- Finds concurrency bugs
- Proves correctness
- Catches edge cases

**Cons:**
- Slower (state space exploration)
- Requires bounds configuration
- Steeper learning curve

**Example:**
```typescript
bus.on('TODO_ADD', (payload) => {
  requires(state.todos.length < 100)
  state.todos.push(newTodo)
  ensures(state.todos.length > 0)
})
```

TLC explores ALL possible:
- Message orderings
- State combinations
- Concurrent operations
- Edge cases

## When to Use Each

### Use Traditional Tests For:
- Quick feedback during development
- Testing specific user scenarios
- UI interactions
- API mocking

### Use Formal Verification For:
- Critical business logic
- Concurrent operations
- State machine verification
- Finding subtle bugs before production

## Best Practice: Use Both!

1. **Write unit tests** for fast feedback
2. **Add verification primitives** to critical handlers
3. **Run verification** before releases
4. **Use TLC traces** to create regression tests

## Example Workflow

1. Implement feature with verification primitives
2. Run unit tests: `bun test`
3. Run verification: `bun run verify`
4. If TLC finds a violation, add regression test
5. Fix bug
6. Re-verify

## Learning More

- See `verification/output/TodoList.tla` for generated TLA+ spec
- Read TLA+ docs: https://lamport.azurewebsites.net/tla/tla.html
- Explore TLC traces when violations are found

## State Space

With current bounds (`verify.config.ts`):
- Users: 4 (guest + 3 users)
- Todos: Up to 100
- Messages: Up to 3 in flight
- Tabs: 3 (with symmetry reduction)

**Tab Symmetry Optimization:** The config enables `tabSymmetry: true` which represents tabs as model values (`Tab0`, `Tab1`, `Tab2`) instead of integers. TLC's symmetry reduction treats permutations of tabs as equivalent, significantly reducing the state space.

TLC explores ~millions of states in seconds!
