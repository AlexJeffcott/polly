# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [0.38.1] - 2026-04-30

### Added

#### Validation, ensures-count surfacing, and end-to-end coverage proof for #78

The 0.38.0 change wired `bounds` through `generateSubsystemTLA` and
proved structurally that the override reaches the generated `.cfg`.
A Lamport-style audit raised the right complaint: a string-in-cfg
test cannot show that TLC's exploration actually reaches the
multi-step-reachable handler whose `ensures()` postcondition the
fix was meant to cover. This release closes that gap on three
fronts.

The config validator (`tools/verify/src/config/parser.ts`) now
checks `subsystems.<name>.bounds`. It rejects `maxInFlight < 1` and
flags `maxInFlight > 20` as unrealistic. It rejects
`perMessageBounds[m] < 1`, rejects `perMessageBounds[m]` greater
than the effective `maxInFlight` (the bound is unreachable and the
message will not be explored), and warns when a `perMessageBounds`
key names a handler that is not in the subsystem's `handlers`
list. The last check turns a silent drop into a visible
configuration error: a typo in a handler name no longer hides
behind successful verification.

The `polly verify` CLI now reports the count of `EnsuresAfter_*`
step properties registered per subsystem, and a total across all
subsystems with a one-line reminder that a property only fires at
states where its handler is enabled. The count is the upper bound
on coverage, not the genuinely-fired count, and the report makes
that distinction explicit so the number cannot be read as a clean
"all postconditions verified" signal.

`scripts/verify-issue-78.ts` is the end-to-end mutation test the
audit asked for. It builds a two-handler connection state machine
in which `Disconnect` requires `phase = "connected"` and so is
two-step-reachable from any initial state. The script generates
four specs — correct/mutated × low-bounds/high-bounds — and runs
TLC against each. The interesting rows are the two middle ones:
under `bounds.maxInFlight: 1` even the mutated spec reports PASS,
because `Disconnect` is never enabled and its `EnsuresAfter_*`
property is vacuously true. Under `bounds.maxInFlight: 2` the same
mutation falls out as a temporal-property violation in roughly
three seconds. The script returns 0 only when all four cases match
their expected outcome, so the verification artefact lives next
to the feature and answers the question directly: yes, the
override changes which postconditions TLC actually evaluates, on
this fixture, today.

A separate ticket (#79) tracks the deeper soundness concern the
audit named: a handler in subsystem A whose `requires()` reads
state owned by subsystem B will silently never have its
postcondition evaluated under the compositional verification of A
alone. That is a static-analysis pass to add next to
`checkNonInterference`, and it is genuinely separate work from the
bounds primitive itself.

## [0.38.0] - 2026-04-30

### Added

#### Per-subsystem message bounds for multi-step ensures

Issue #78. The `ensures()` postconditions wired into step properties
by #74/#75 only fire if TLC reaches a state where the handler is
enabled. A handler that requires another handler to have fired first
— `handleDisconnected` only runs once `StartConnecting` has put the
connection into a connected phase, `becomeLeader` only after a chain
of three or four messages, `submitSuccess` only after a `ShowModal`
and a `StartSubmitting` — was a postcondition TLC never evaluated.
The global `maxInFlight` controls how many distinct messages may sit
in flight at once, and raising it from one to two carries the entire
message-router infrastructure along: ports, the message queue,
`deliveredTo`, `routingDepth`, payload non-determinism. On a
representative codebase, `maxInFlight: 2` against the auth subsystem
with unbounded payloads excluded produced 2.2 GB of TLC state files
in twenty minutes; the payload-free app subsystem of three handlers
produced 287 MB in fifteen.

The fix adds an optional `bounds` field to `SubsystemConfig`:

```ts
subsystems: {
  connection: {
    state: ["connectionState.phase"],
    handlers: ["StartConnecting", "Connected", "Disconnected", "BecomeLeader"],
    bounds: {
      maxInFlight: 2,
      perMessageBounds: { Connected: 1 },
    },
  },
}
```

`generateSubsystemTLA` already builds a filtered config per subsystem
before handing it to the standard generator. The new helper
`applySubsystemBounds` layers the override on top of that filtered
config: `bounds.maxInFlight` replaces the inherited global, and
`bounds.perMessageBounds` merges over the filtered per-message map
after the parent map has been narrowed to the subsystem's handlers.
Subsystems without `bounds` keep the parent's values exactly as
before.

The trade-off becomes local. A subsystem of payload-free handlers
can run at a higher `maxInFlight` and exercise its multi-step
ensures, while subsystems that carry unbounded payload domains stay
at the cheaper global setting. The mutation-test guarantee from
#74/#75 reaches the postconditions on multi-step-reachable handlers
(`handleDisconnected`, `becomeLeader`, `resolveConflict`,
`submitSuccess`) one subsystem at a time, without paying the global
exploration cost of doing so for every subsystem at once.

## [0.37.0] - 2026-04-30

### Fixed

#### Renamed-property assignments now contribute to the payload model

Issue #77. The handler walker recognised the shorthand assignment
`{ theme }` as a payload contribution but silently dropped its
renamed-property equivalent `{ currentView: view }`. The two forms
differ only in syntax, so the inconsistency split codebases stylistically:
field names that read as locations (`currentView`, `activeHubTab`) had
to match parameter names that read as intent (`view`, `tab`), or
verification would simply not see the assignment.

The action body lost the renamed assignment entirely, leaving the
modeled handler with a phantom no-op for that field. Worse, an
`ensures()` clause referring to the parameter still produced
`payload.<param>` in the generated property, even though the action
body had never added the parameter to `PayloadType`. TLC reported
`Evaluating action property EnsuresAfter_* failed` on a name it could
not resolve, and the source of the mismatch — two extractors disagreeing
about whether the parameter belonged to the payload — was invisible
from the surface of the spec.

The fix lives in `extractRegularPropertyAssignment`. The extractor
already had two branches: one for literal initializers
(`extractValue`) and one for property-access tracing
(`extractPayloadPropertyParam`, e.g. `role: payload.role`). A bare
parameter Identifier fell between them. A third branch closes the
gap: when the initializer is an Identifier whose text matches a
function parameter, the extractor records
`{ field, value: "param:<paramName>" }` — the same marker the shorthand
path already emits. Action body and ensures extractors now agree on
the payload model, and the codegen wires the parameter into
`PayloadType` and the `EXCEPT` clause as expected.

The codepath the fix joins is well covered downstream. Issue #72's
payload-domain wiring and issue #73's per-action ensures Asserts both
consume the `param:` marker; the renamed-property form now flows
through both without further changes.

## [0.36.0] - 2026-04-30

### Fixed

#### Multi-target sends no longer false-positive `EnsuresAfter_*` properties

Issue #75. The 0.35.0 step-temporal property emitted by the codegen
quantified over the whole target set:

```tla
=> \A target \in messages[m].targets :
     (target \in Contexts /\ ports[target] = "connected")
     => contextStates'[target].phase = "connected"
```

Routing only mutates one target at a time — `RouteMessage` selects via
`\E target \in msg.targets` and runs `StateTransition(target, ...)` on
that one — so any other connected target in the message's target set
keeps its pre-step state. When the predicate's expected value differs
from a sibling's pre-state (the common case, since `ensures()` typically
asserts a non-init value), the property false-positives. In a project
with `Contexts = {background, content, popup}` and a `CONNECT` handler
asserting `phase === 'connected'`, every multi-target send tripped the
property even though the handler did exactly the right thing on the
routed target.

The fix records the routed target on the message itself. `MessageRouter`
gains a `deliveredTo: ContextType \cup {NoTarget}` field on the message
record, set by `RouteMessage` / `UserRouteMessage` to the chosen target
on successful delivery. The property template binds `target` via `LET`
to that field instead of universally quantifying over the target set:

```tla
=> LET target == messages'[m].deliveredTo IN
     (target \in Contexts /\ ports[target] = "connected")
     => contextStates'[target].phase = "connected"
```

The wrong-target catch from #74 still trips, because the predicate now
reads the post-state of the actually-routed context — exactly the
target whose `contextStates` entry the EXCEPT touched.

Recording `deliveredTo` makes routing nondeterminism observable in the
state, which multiplies distinct states by a factor proportional to
`|targets|` per delivered message. Examples that exercise multi-target
sends at depth 8 may need a slightly tighter depth bound; the
full-featured example dropped from `maxDepth: 8` to `6`.

`scripts/verify-issue-75.ts` is the end-to-end artefact: it generates a
multi-context, multi-target spec where the handler writes the asserted
value, runs TLC, and confirms no false positive. It also generates a
companion wrong-target spec and confirms TLC still flags the violation.

Closes #75.

## [0.35.0] - 2026-04-29

### Changed

#### `ensures()` postconditions are step-temporal properties, not action-body conjuncts

0.33.0 wrapped each postcondition in TLC's `Assert(P, "msg")` and added
it as a conjunct in the handler's action body, on the assumption that a
failed Assert would halt TLC. Issue #74 confirmed empirically that this
still acts as a guard: when the EXCEPT primes a value that fails the
predicate, TLC's action evaluator catches the resulting `EvalException`
and treats the binding as not-a-successor — the buggy transition simply
doesn't fire, no invariant is reported as violated, and the model still
verifies green. The Assert-as-conjunct fix never actually closed the
bug class issue #73 named.

The codegen now lifts each handler's postconditions into a per-handler
step-temporal property emitted into the `PROPERTIES` section:

```tla
EnsuresAfter_HandleDisconnect ==
  [][
    \A m \in 1..Len(messages) :
      (messages[m].status = "pending"
       /\ messages'[m].status = "delivered"
       /\ messages[m].msgType = "DISCONNECT")
      => \A target \in messages[m].targets :
           (target \in Contexts /\ ports[target] = "connected")
           => contextStates'[target].phase = "disconnected"
  ]_allVars
```

The predicate fires only on `(s, s')` pairs that just delivered a
message of the matching type, and reads the post-state via
`contextStates'[target]`. TLC handles `[][P]_allVars` as a safety
property — no liveness machinery, no fairness needed — and a violation
is reported as `Action property EnsuresAfter_<HandlerName> is
violated`, with a counterexample trace.

The previous syntax-only test (`ensures-as-assert.test.ts`) was
replaced with `ensures-as-property.test.ts`, and an end-to-end
verification artefact lives at `scripts/verify-issue-74.ts`. The
artefact runs TLC against two synthesised specs — one where the
handler writes the value its `ensures()` asserts, and one where it
writes a different value — and confirms TLC catches the mutation.
This is the shape `CLAUDE.md` calls for: a one-command reproduction
that prints success or a specific failure rather than relying on
green unit tests that exercise the integration surface only on paper.

`requires()` is unchanged. Preconditions stay as enabling conjuncts
in the action body, which is the correct TLA+ idiom for "this handler
doesn't fire here." Only `ensures()` moves to the property layer.

The module-end `=====` line moved out of `addInvariants()` and into a
dedicated final emission step so temporal properties always land
inside the module rather than after its closing line.

Closes #74.

## [0.34.0] - 2026-04-29

### Added

#### Payload-property tracing for longhand object literals

The shorthand `{ field }` and direct `signal.value = paramName.X` paths
already let the verifier see a parameter being written into a modeled
state field. The longhand `{ field: paramName.X }` form did not — the
extractor returned undefined for any non-literal initializer, dropping
the assignment on the floor. Real handlers built the same way the
todo-list `USER_LOGIN` does — `{ id: payload.userId, role: payload.role }`
— surfaced no `role` write to the spec, so an `ensures()` over
`user.role` became a postcondition the verifier could not honour.

Polly now traces the longhand form the same way it traces the
shorthand. Combined with the payload-domain wiring from 0.32.0 and the
ensures-as-Assert change from 0.33.0, longhand assignments participate
fully in verification: the payload field carries the modeled state
field's domain, and the ensures over that field is a checked
postcondition rather than documentation that doubled as a guard.

### Fixed

#### EXCEPT clauses no longer emitted for unmodeled fields

Surfacing the new writes also revealed a quieter codegen issue. EXCEPT
clauses were being emitted for every assignment the extractor
recorded, modeled or not, which after the extractor improvement meant
unmodeled fields like `user.id` and `user.name` appeared in
`contextStates` with values the schema never declared. The codegen now
drops assignments whose target is not part of the (subsystem-filtered)
state config. Without the filter the auth subsystem's state space
ballooned sixfold for no checking benefit.

## [0.33.0] - 2026-04-29

### Changed

#### `ensures()` postconditions emit `Assert(...)` for caught wrong-target transitions

Before this change, an `ensures()` call became a plain conjunct on the
primed state inside the action body. When the EXCEPT wrote one value
and the postcondition expected another, TLC saw the conjunction as
false, marked the action **disabled**, and reported a green model —
even when the handler was visibly broken under mutation testing. The
postcondition was, in effect, documentation that doubled as a silent
guard.

The codegen now wraps every postcondition in TLC's `Assert(P, "msg")`.
Available transitively because `MessageRouter` already extends TLC,
the operator returns true when the predicate holds and raises a
runtime exception naming the failed message otherwise. A wrong-target
EXCEPT now causes TLC to halt with the user-supplied label, instead
of silently disabling the action — closing the bug class issue #73
named.

Surfacing this caught a latent `ensures()` in the `todo-list`
`USER_LOGIN` handler that asserted `user.role !== "guest"`. The
extractor only records literal assignments at that point, so
`role: payload.role` was invisible to the spec; TLC correctly
reported the postcondition as unprovable. The handler's `ensures` was
narrowed to the part the verifier could honour — `loggedIn === true`
— with a comment explaining the limitation. (0.34.0 then closes the
extractor gap.)

## [0.32.0] - 2026-04-29

### Added

#### Payload-domain wiring for parameterised handlers

A handler that writes a parameter into a modeled state field — the
common `setX(enum)` shape — used to leave the verifier guessing. The
parameter became a payload field typed `Value`, `BOOLEAN`, or `0..2`
by a name-pattern heuristic; the state field's declared domain was
ignored. TLC then explored a payload value that the field's `TypeOK`
refused, and either rejected the trace or, worse, never reached the
bug at all.

The fix joins the two pieces of information that already exist. The
extractor already records `param:X` markers on every handler
assignment. The verification config already declares each state
field's domain through `FieldConfig`. A new derivation pass walks the
handlers, links each marker to its target field, and emits the
field's domain — enum literal, bounded number, BOOLEAN — into
`PayloadType`. **Conflicting domains across handlers are a hard error**
rather than a silent fallback that would re-introduce the gap.

Subsystem-scoped verification continues to work without changes; each
subsystem reuses the same generator over its filtered config and
analysis. The `todo-list` example grows a `SET_THEME` handler in a
new `preferences` subsystem to exercise the path end to end.

## [0.31.0] - 2026-04-28

### Added

#### `iceCredentialResolver` hook on `createMeshClient`

WebRTC traversal between two peers behind symmetric NATs (cellular
CGNAT, some corporate firewalls) requires a TURN relay; STUN alone
is not enough. The runtime already accepts `iceServers` on the
WebRTC adapter, but the realistic deployment shape is short-lived
rotating credentials fetched from a consumer-owned backend, not a
static list hardcoded into the application bundle.

The new `iceCredentialResolver` option on `createMeshClient` is the
single integration point a consumer needs. It runs once at connect
time and the resolved servers reach the adapter through the existing
`iceServers` path; when both options are set the resolver wins on
purpose, so a stale `iceServers` value left in client code cannot
mask a broken credential flow. Common provider patterns are
documented inline (self-hosted coturn, Cloudflare Calls, Twilio NTS,
metered.ca-style services). ICE restart with refreshed credentials
is a separate concern not covered by this hook; deployments that
need it tear down and rebuild the mesh client when the credential
window closes. Closes #58.

## [0.30.0] - 2026-04-27

### Added

#### `Surface` primitive owns visual-surface concerns

Where `Layout` owns spatial concerns — grid, flex, gap, alignment —
`Surface` now owns the chrome that sits on top: padding, background,
border, radius, shadow, and the narrow positioning idioms (sticky
strips, fixed floating panes) that consumers had been reaching for
inline styles to express. Eight named variants — `plain`, `raised`,
`sunken`, `bubble`, `chip`, `callout`, `floating`, `sticky-bar` —
resolve to bundles of the underlying props, all routed through
`--polly-*` tokens via local `--s-*` custom properties so a
per-instance retint works through `style={{ "--polly-surface-raised":
"..." }}` without touching theme tokens. Polymorphic via an `as` prop;
`borderSides` modifiers use logical CSS properties so RTL is
browser-handled. The `team-task-manager` example's `InstallPrompt`
floating panel and `NetworkStatus` sync indicator both now consume
Surface as the reference compose-sites. Closes #66.

#### `Card` composite primitive

`Card.Root`, `Card.Header`, `Card.Body`, and `Card.Footer` each render
a `Surface` with sensible defaults — Root raised with medium radius,
Header and Footer with a logical-side border so the separator falls
in the right place under both LTR and RTL, Body as plain padding.
Every slot accepts the full `SurfaceProps`, so consumers retint,
override padding, or reach for a different variant without leaving
the primitive. Card is the first compound that is purely a re-skin
of Surface — no behavioural layer like Modal's focus trap or Toast's
severity tinting. Closes #70.

### Changed

#### `Modal`, `Toast`, and `ConfirmDialog` compose `Surface` internally

The visual chrome that each of these primitives previously hand-rolled
in its own CSS module — background, border, radius, shadow, the raised
or callout look — now lives in `<Surface>`. The behavioural shell
around each one is unchanged: Modal still installs the focus trap,
Escape still pops the top overlay, the backdrop still closes on
click, Toast still tints by severity (now via `--polly-border` retint
instead of direct `border-color`), and ConfirmDialog still resolves
its `Promise<boolean>` on confirm or cancel. The token vocabulary now
flows through one consistent path, so a per-instance retint works the
same way on every compound that composes Surface. Closes #67, #68,
#69.

## [0.29.3] - 2026-04-20

### Fixed

#### `$crdtState` no longer cycles preact signals on value-equal writes

`applyTopLevel` used to copy every top-level field onto the
Automerge doc unconditionally. A value-equal reassignment
(`doc.users = sameObject`) still generated real ops, fired a
`change` event through the DocHandle's state machine, and pushed
the signal binding to set `inner.value` again — which the preact
effect then wrote back through `applyTopLevel`, restarting the
chain. Browsers spaced these interactions across their event loop
and the cycle exhausted itself below preact's 100-deep counter;
bun runs xstate tight enough that every write re-entered and
tripped `Cycle detected` within a few iterations.

`applyTopLevel` now JSON-compares each incoming field against
what's already on the doc and only writes when it actually
differs. Value-equal writes are no-ops at the Automerge layer, so
`docChanged` in `#checkForChanges` comes up false, no change
event is emitted, and the signal binding stops echoing.
Regression test covers ten structurally-equal writes in a row.

Caught while shipping a CLI that boots under bun and writes to
`mesh:users` + `mesh:devices` on init; every invocation previously
crashed with `Cycle detected`.

### Added

#### `@fairfox/polly/quality` — no-require conformance check

Bans `require(...)` calls in TypeScript source. Inline CommonJS
defeats bundler static analysis, hides cross-module dependencies,
and quietly opts a module out of ESM semantics. Exports
`checkNoRequire`, `isLineRequireClean`, `NoRequireCheckOptions`,
`NoRequireCheckResult`, and `NoRequireViolation` from
`@fairfox/polly/quality`. The CLI gains a `polly quality
no-require` subcommand, and `polly quality all` runs it alongside
`no-as-casting` and the CSS family.

Allowed escapes: static ES imports, `await import(...)` dynamic
imports (they're ESM), `require.resolve(...)` (sometimes
load-bearing for runtime path resolution), and occurrences inside
strings or comments.

## [0.29.2] - 2026-04-20

### Added

#### `@fairfox/polly/guards` — type guards for walking `unknown` safely

Polly touches a lot of shapes it doesn't own — signalling frames
parsed from JSON, IndexedDB records, storage adapter returns. The
ergonomic-but-unsafe fix is a bare `as` cast; every cast hides a
shape mismatch until runtime. This release publishes the two
smallest possible helpers so every consumer can narrow `unknown`
at the point it lands in a tight predicate instead:

- `hasKeyInObject(input, key)` — narrows `input` to
  `Record<K, unknown>` when the input is a non-null object with an
  own property under the given key. Uses `Object.hasOwn` so it
  never walks the prototype chain; a `hasKeyInObject(x, "toString")`
  against any object would pass via prototype otherwise, which is
  never what a caller looking for a specific data key intends.
- `isRecord(input)` — narrows `input` to
  `Record<string, unknown>` when it's a non-null object (not an
  array). Useful as a prelude to reads off a record whose shape is
  known at the call site but typed as `unknown`.

Both guards leave the inner value as `unknown` so the caller still
narrows further. No runtime coupling to the rest of polly; published
from the new `./guards` subpath so consumers can import without
pulling in the mesh stack.

## [0.29.1] - 2026-04-20

### Added

#### `createMeshClient` forwards `onCustomFrame` to its signalling client

The 0.29.0 release wired an `onCustomFrame` hook onto
`MeshSignalingClient` so consumers could receive frames outside the
built-in vocabulary, but `createMeshClient`'s `signaling` option set
didn't forward it. An application that used `createMeshClient` (as
fairfox and the CLI bootstrap do) therefore couldn't subscribe to
custom frames without bypassing the factory and wiring the signalling
client by hand. `createMeshClient`'s `signaling.onCustomFrame` now
forwards straight through, matching the existing pattern for `onError`
and `WebSocket`. No behavioural change for consumers that don't pass
the option.

## [0.29.0] - 2026-04-20

### Added

#### Custom-frame extensibility on the signalling socket

The signalling transport now tolerates frames whose `type` falls
outside polly's built-in vocabulary. Consumers who want to layer their
own protocol on the existing connection — pairing return tokens,
presence pings, anything else that benefits from sharing the
signalling socket and its reconnect state — wire up a matched pair of
hooks. On the client, `MeshSignalingClient` gains an optional
`onCustomFrame` option and a `sendCustom(type, payload)` method; on
the server, `signalingServer` gains an optional `onCustomFrame`
handler that receives the parsed frame along with the sender's
authenticated peer id.

The built-in types — `join`, `signal`, `peers-present`, `peer-joined`,
`peer-left`, `error` — keep their existing fast path unchanged. An
unknown type with no configured hook still falls through silently on
the client and still returns a `malformed` error on the server, so
this is additive: an older consumer sees no behavioural change, a
newer consumer opts in.

Both sides treat frame bodies as opaque. Polly does not interpret or
route custom frames beyond the hook call; routing, authentication
beyond the join handshake, and back-pressure are the consumer's
responsibility.

## [0.28.0] - 2026-04-19

### Fixed

#### `styles.css` now delivers the working visual baseline

The `@fairfox/polly/ui/styles.css` entry previously shipped only the
structural and a11y rules; the component CSS modules built into
`index.css` were not part of it. A consumer who imported the two
documented entries (`styles.css` and `theme.css`) therefore got a
page in which every polly primitive rendered without its own styles
— tabs looked like native buttons, badges had no shape, the
underlying layout grid was invisible. Matching the expectation that
the default import deliver a complete working UI, `styles.css` now
concatenates the structural rules with the component rules. The
separate `components.css` alias remains for consumers who want to
supply their own structure.

### Added

#### Document baseline

A neutral document baseline lands in the polly-structure layer and
gives bare HTML a consistent starting point: `font-family`, `color`,
and `background` inherit from the polly tokens; `<body>` loses its
margin; headings, paragraphs, lists, and figures lose their
browser-default margins so they compose cleanly with `Layout`'s
`gap`. Every selector uses `:where()` and carries zero specificity,
so any consumer class overrides without a fight.

#### Heading scale

Headings `h1`..`h6` receive sizes drawn from the typography tokens
and a dedicated `--polly-line-height-heading`. Two new tokens,
`--polly-text-2xl` and `--polly-text-3xl`, extend the existing scale
upward so `h1` and `h2` have defined values rather than inheriting
the browser's approximate multipliers.

#### Measure tokens

Two semantic widths enter the theme. `--polly-measure-prose` caps
body text at sixty-eight characters, the WCAG 1.4.8 comfortable
reading line; `--polly-measure-page` caps an application shell at
1040 pixels. Consumers pass either token — or any CSS length —
through the new `maxInlineSize` prop on `Layout`; the layout clamps
its inline size and centres within the parent via
`margin-inline: auto`. `box-sizing: border-box` now applies to every
`Layout` so padding no longer breaks the clamp.

#### Text overflow utilities

Two zero-specificity attribute selectors offer opt-in truncation
without breaking the grid-only layout contract. `data-polly-truncate`
produces a single-line ellipsis and sets `min-inline-size: 0` so a
`1fr` grid track can shrink below the text's intrinsic content size.
`data-polly-clamp` produces a multi-line ellipsis; the consumer sets
`--polly-clamp` to the line count and the element takes on
`-webkit-box` display without affecting its parent. Both replace the
ad hoc pattern of JavaScript string slicing for "description" fields,
which tended to cut mid-word and fight the actual available width.

## [0.27.5] - 2026-04-18

### Fixed

#### `fileKeyringStorage` mkdirs its parent directory before the first write

First-run on a fresh machine typically points `fileKeyringStorage`
at a path whose parent hasn't been created yet — `~/.fairfox/keyring.json`
is the canonical shape. The previous implementation went straight to
`writeFile` on a `${path}.tmp-*` sibling, which failed at `open()` with
`ENOENT` when the parent was missing and aborted the pairing bootstrap.

`save` now calls `mkdir(dirname(path), { recursive: true })` before the
write-to-tmp-then-rename dance. The `load` path is unchanged — a
missing file still returns `null`.

A new unit test (`save creates the parent directory when it does not exist`)
pins this to a nested path under a fresh `tmpdir` and asserts the
keyring round-trips.

## [0.27.4] - 2026-04-18

### Added

#### `checkSharedComponents` quality check

`@fairfox/polly/quality` now exports a programmatic check that scans
a directory for raw native HTML elements that have a polly primitive
equivalent — `<button>` → `<Button>`, `<input>` → `<ActionInput>` /
`<TextInput>`, `<textarea>` → `<ActionInput variant="multi">`,
`<select>` → `<Select>`, `<form>` → `<ActionForm>`, `<dialog>` →
`<Modal>`. Consumers wire it into their own `bun check` script and
pass `exemptPackages` / `additionalRules` for legacy code or
application-specific extensions.

The check was lifted from fairfox's `scripts/check-shared-components.ts`
and generalised — it takes a `root` + optional `scanRoot`, and
returns a `{ violations, print() }` result. The printing path is
injectable so consumers can route output through their own logger.
Default rules add `<dialog>` on top of the fairfox originals now
that `<Modal>` is the published replacement; `<input type="hidden">`
gets a `skip` predicate because hidden inputs have no primitive
analogue.

`tests/unit/quality/check-shared-components.test.ts` covers every
default rule, the hidden-input skip, the exempt-package escape
hatch, a consumer-supplied `additionalRules` entry, commented-out
elements being ignored, the default skip-dirs traversal, and the
`print()` log-sink injection.

## [0.27.3] - 2026-04-18

### Added

#### `MeshSignalingClient` reconnects on unexpected close

Real deployments hand the signalling server restarts, load-balancer
rolls, and network blips. Pre-0.27.3 the client noticed the close,
flipped `joined = false`, called its `onClose` callback, and went
quiet. Every existing WebRTC data channel survived the drop (they
are peer-to-peer once open) but no new peer could reach the stranded
client, and any dropped channel stayed dropped. Users saw "stale
and disconnected until refresh."

The client now schedules a reconnect on every close that was not
triggered by an explicit `close()` call. Backoff starts at 250ms and
doubles up to a 30-second ceiling. Each reconnect reopens the
WebSocket, re-sends the `join` frame under the same `peerId`, and
lets the existing `peers-present` / `peer-joined` dispatch replay
discovery — no caller-side reset, no lost peer ids.

`close()` now sets a `stopping` flag and clears any pending reconnect
timer, so a consumer that deliberately tears the client down stays
torn down.

`tests/integration/signaling-client-reconnect.test.ts` is the guard.
The "re-joins after server restart" test stops the signalling server,
waits briefly, restarts on the same port, and asserts `onOpen` fires
a second time with `isConnected` returning true again. The
"explicit close does not reconnect" test asserts `close()` is
respected. Verified red against the pre-0.27.3 client (first test
times out at 10s) and green at HEAD.

## [0.27.2] - 2026-04-18

### Fixed

#### `Button` silently dropped `data-action-*` extras

Consumers that attached additional action payload attributes to
`<Button>` — `data-action-tid`, `data-action-item-id`,
`data-action-person`, any `data-action-*` — had those attributes
dropped during render. `Button` destructured `data-action` explicitly
and forwarded only that one; the rest were accepted as props by
TypeScript (the type now declares an index signature for
``data-action-${string}``) but never reached the underlying element.
The click bubbled up to the event delegator, the handler fired, and
`ctx.data` was empty. Every handler that guarded on `if (!ctx.data.tid)
return;` silently no-ed — the user clicked a delete button and
nothing happened.

The fix collects every `data-action-*` key from `props` and spreads
them onto both the anchor and button render branches. The type
surface gains an index signature so `<Button data-action-tid="…" />`
type-checks without a per-attribute enumeration.

`tests/browser/ui/primitives.browser.tsx` grows a Button regression
that plants a `<Button>` with three `data-action-*` extras, installs
the event delegator, clicks the button, and asserts every extra
arrived in `ctx.data`. Verified red against the 0.27.1 Button, green
against the 0.27.2 fix.

#### `mesh-node.js` stripped its `node:fs/promises` imports

The library build compiled every entrypoint under `target: "browser"`,
which replaced every `import … from "node:fs/promises"` statement in
`mesh-node.ts` with an empty destructure —
`var {readFile, rename, writeFile} = (() => ({}))` — turning every
call on the file-backed keyring storage into a runtime
`readFile is not a function`. Consumers that reached for
`@fairfox/polly/mesh/node` — CLI peers, always-on bridges, any
Node/Bun-side mesh participant — could not load or save a keyring.

`build-lib.ts` now routes `src/mesh-node.ts` through a second
`Bun.build` pass with `target: "node"`, so the `node:fs/promises`
and `node:readline/promises` imports survive the bundler. The
`target: "browser"` pass drops `mesh-node` from its entrypoint list;
the file was never appropriate for a browser target anyway.

## [0.27.1] - 2026-04-18

### Fixed

`createMeshClient` constructed the Automerge `Repo` without passing a
`peerId`, so Automerge auto-generated a random `peer-xxxxxxx`
identifier for the local side. `MeshNetworkAdapter` then signed every
outgoing envelope with that auto-id as its `senderId`, and the remote
receiver — whose `keyring.knownPeers` was keyed by the mesh peer id
the application had paired against — dropped the envelope on the
`knownPeers.get(senderId)` lookup. Mutual trust, WebRTC connection,
data-channel open — all correct; only the last step, signature
verification, silently rejected every message. No `$meshState`
document ever synced through consumers that used the factory.

The fix threads `options.signaling.peerId` into the `Repo` constructor
so the Automerge local peer id and the mesh peer id are the same
string. Existing consumers that wired the stack manually and passed
an explicit `peerId` to `new Repo(...)` were unaffected; the bug
only ever surfaced for the recommended `createMeshClient` entry point.

A new browser test, `tests/browser/mesh-client-roundtrip.browser.ts`,
constructs two clients through `createMeshClient` with paired
keyrings and verifies that a document written on one converges on
the other. This is the regression guard the existing hand-wired
`mesh-webrtc.browser.ts` could never have caught, because that test
passed its own explicit `peerId` to `new Repo()` and so silently
compensated for the gap.

## [0.27.0] - 2026-04-18

### Added

#### Reactive peer discovery on the signalling protocol

Two paired devices used to find each other only if both happened to be
joined to the signalling server at the same moment `connect()` fired on
the WebRTC adapter. Whichever device joined second reached the first
(which was still joined); the first device's offer landed on an empty
slot and the adapter did not retry. 0.27.0 adds three new server-to-
client frames that replace the one-shot startup sweep with a fully
reactive flow.

- `peers-present: [peerId…]` — sent once to a newcomer immediately
  after it joins, listing every peer already joined.
- `peer-joined: peerId` — broadcast to every incumbent when a new peer
  joins.
- `peer-left: peerId` — broadcast to every remaining incumbent when a
  joined peer's socket closes.

`MeshSignalingClient` parses the three new types into three optional
callbacks (`onPeersPresent`, `onPeerJoined`, `onPeerLeft`).
`MeshWebRTCAdapter` gains `handlePeerJoined`, `handlePeersPresent`, and
`handlePeerLeft`. The two initiator entry points apply a shared filter:
the peer must be in `knownPeerIds`, no slot may already exist, and the
local peer id must compare lexicographically greater than the remote's
— matching the existing glare-resolution rule in `handleOffer` so the
pre-offer filter eliminates the glare pathway entirely. `handlePeerLeft`
tears down any slot for the departed peer, so a subsequent rejoin
builds a clean connection instead of racing WebRTC's ICE-timeout
eviction. `createMeshClient` wires the three callbacks automatically.

The unconditional startup sweep in `MeshWebRTCAdapter.connect()` is
gone. Discovery flows exclusively through the notification frames; the
signalling server is the single source of truth for presence, which
removes the race that made the old sweep unreliable. A narrow
`peerSlotCount()` accessor exposes the adapter's slot count for tests
that assert "exactly one data channel per ordered pair".

The wire protocol is additive. Older servers that do not emit the new
frames leave the new client callbacks unused and behaviour degrades to
the pre-0.27 sweep; older clients ignore unknown `type` values and
continue to function against the new server. Consumers that build the
stack manually (rather than through `createMeshClient`) need to wire
`onPeersPresent`, `onPeerJoined`, and `onPeerLeft` on their
`MeshSignalingClient` — see the browser tests under `tests/browser/` for
the pattern.

### Fixed

The signalling server's close handler used pointer equality on the
Elysia `ws` wrapper when deciding whether a socket's eviction should
actually clear its peer id from the routing map. Elysia does not
guarantee the same `ws` reference across `message` and `close`
callbacks, so stale closes after a rejoin could silently evict the
fresh socket and strand the peer. The check now compares on the
`ws.data` bag Elysia does preserve per connection.

## [0.26.1] - 2026-04-17

### Fixed

Ship the compiled JavaScript for the `@fairfox/polly/ui/markdown`
subpath. The 0.26.0 release declared the export in `package.json` and
emitted `markdown.d.ts` through `tsc`, but `build-lib.ts` never listed
`src/polly-ui/markdown.tsx` as a Bun.build entrypoint, so the
corresponding `markdown.js` was absent from the published tarball.
Consumers that imported `renderMarkdown` — notably The Struggle and
Library in fairfox — compiled fine against the declaration file and
then failed to bundle against the runtime module. The fix adds
`src/polly-ui/markdown.tsx` to the library build's entrypoints list;
the emitted `markdown.js` now rides alongside its declaration.

## [0.26.0] - 2026-04-17

### Added

#### Nine UI primitives absorbed from `@fairfox/ui`

`@fairfox/polly/ui` gains `Badge`, `Button`, `Checkbox`, `Collapsible`,
`Dropdown`, `Select`, `Skeleton`, `Tabs`, and `Toggle` — the components
that Fairfox had built and Polly had not. Each follows the existing
conventions: `@layer polly-components` for the CSS, `data-polly-ui`
plus `data-polly-<name>` hooks on the root, token-driven colours and
spacing, and no reliance on `clsx` or other runtime styling helpers.

`Button` carries the full tier × colour × size matrix (three tiers,
five colours, three sizes, plus `circle`, `fullWidth`, `icon`, `label`,
and an anchor-or-button variant via `href`). `Dropdown` uses the
native Popover API and integrates with Polly's existing
`closeTopOverlay()` via the shared `data-overlay-id` + `overlay:close`
mechanism. `Select` composes `Dropdown` and a native checkbox per row;
state is a `Signal<Set<T>>` with Select All / Clear affordances in
multi-select mode. `Checkbox` accepts either a plain boolean or a
`Signal<boolean>` and binds its own change listener when given a
signal.

#### `Layout` gains an `inline` prop

`display: inline-grid` mode so `Button` can arrange an icon beside its
label without violating the no-flex-or-grid-outside-Layout rule
enforced by `polly quality css-layout`.

#### New subpath: `@fairfox/polly/ui/markdown`

Ships a `renderMarkdown(value): JSX.Element` helper that parses with
`marked`, sanitises with `DOMPurify`, and renders via
`dangerouslySetInnerHTML`. The helper plugs straight into
`ActionInput`'s existing `renderView` prop:

```tsx
import { ActionInput } from "@fairfox/polly/ui";
import { renderMarkdown } from "@fairfox/polly/ui/markdown";

<ActionInput value={note.body} variant="multi" action="note:update" renderView={renderMarkdown} />
```

`marked` and `dompurify` are declared as optional peer dependencies so
the core `@fairfox/polly/ui` bundle gains no runtime dependencies.
Apps that opt into the markdown subpath install them themselves.

#### Theme tokens for the lifted primitives

`theme.css` grows a small set of first-class tokens the ported
components genuinely need, added to all four theme blocks (default
`:root`, `prefers-color-scheme: dark`, and both explicit
`[data-polly-theme]` overrides):

- `--polly-text-xs` — smaller chip/badge type.
- `--polly-radius-full` — pill and circle shapes.
- `--polly-control-height-sm`, `-md`, `-lg` — form-control sizing.
- `--polly-accent-hover` — hover state for primary tier buttons.
- `--polly-success-contrast`, `--polly-warning-contrast` — text on
  saturated success and warning backgrounds.
- `--polly-status-{info,success,warning,danger}-{bg,text}` — tinted
  chip palette consumed by Badge variants.

## [0.25.2] - 2026-04-17

### Changed

- Reshaped `recipes/` from folder-per-recipe to file-per-recipe. Each
  recipe is now a single Markdown code-along that answers a goal in
  the user's voice — prose with focused snippets, not a full
  implementation you copy. The previous `recipes/actions-driven-app/`
  directory is replaced by `recipes/actions-driven-app.md`; two new
  recipes, `recipes/mesh-only-cloudflare.md` and
  `recipes/mesh-pi-peer.md`, cover deployment shapes on free Cloudflare
  and an always-on Raspberry Pi peer respectively. `recipes/README.md`
  now documents what a recipe is, what it is not, and how to propose
  one.

## [0.25.1] - 2026-04-17

### Fixed

- `@fairfox/polly/elysia` no longer forces a static import of
  `@automerge/automerge-repo`, `@automerge/automerge-repo-network-websocket`,
  `@automerge/automerge-repo-storage-nodefs`, and `ws` through its barrel.
  The `createPeerRepoServer` factory now pulls those peer-state dependencies
  dynamically inside the function body, so Elysia apps that use only the
  non-peer surface (the `polly()` plugin) evaluate the module without the
  peer packages installed. Apps that actually build a peer-relay server
  still need the packages — they're loaded when `createPeerRepoServer` runs
  — and the public type surface is unchanged.

## [0.25.0] - 2026-04-17

### Added

#### `@fairfox/polly/actions` — action-registry runtime

A new subpath ships the plumbing that Lingua and Fairfox have both
converged on independently: one document listener, one typed action
registry, components that read signals and emit markup.

```ts
import {
  installEventDelegation, createStore, createForm,
  type ActionRegistry,
} from "@fairfox/polly/actions";

const teamForm = createForm({
  name: "team",
  initialValues: { name: "", description: "" },
  onSubmit: async ({ values, stores }) => stores.data.createTeam(values),
});

const ACTION_REGISTRY: ActionRegistry<RootStore> = {
  ...teamForm.actions,
  "theme:toggle": ({ stores }) => stores.ui.toggleTheme(),
};

installEventDelegation((dispatch) => {
  ACTION_REGISTRY[dispatch.action]?.(ctxFor(dispatch));
});
```

Ships event delegation with a form-click guard and keyboard
activation for non-interactive elements; typed `ActionRegistry` and
`ActionContext`; a signal-backed overlay registry with
`pushOverlay` / `popOverlay` / `closeTopOverlay`; a `createStore`
base and `StoreProvider` / `useStores` context wiring; a `createForm`
primitive that extends the store base with per-field signals, an
aggregated values signal, open/close/submit methods, an entity
`guard` effect (autonomous close when the subject disappears), and
three auto-registered action handlers; an optional `createFormSet`
for many-form apps; a global `errorState` signal with `setError` /
`clearError` / `submitError` that routes handler failures to the
UI; and `runAction` / `createMockStores` / `createMockElement` /
`createMockSubmitEvent` testing helpers for DOM-less unit tests.

#### `@fairfox/polly/ui` — compound UI primitives

Eight primitives sit on top of the action runtime. Every element
carries `data-polly-*` hooks for stable selectors, focus rings are
visible on WCAG 2.4.11 terms, hit targets meet WCAG 2.5.8, focus is
trapped inside modals and restored on close, aria attributes are
wired automatically, `prefers-reduced-motion` zeroes every motion
token, and overlays portal through a single `<OverlayRoot />`.

```tsx
import {
  Layout, Modal, ActionForm, TextInput, ActionInput,
  ConfirmDialog, Toast, OverlayRoot,
} from "@fairfox/polly/ui";
import "@fairfox/polly/ui/styles.css";
import "@fairfox/polly/ui/theme.css";
import "@fairfox/polly/ui/components.css";
```

`<Layout>` is the one primitive that owns layouting concerns (CSS
grid via custom properties). `<Modal>` is compound (Root / Backdrop
/ Content / Header / Title / Body / Footer / Close). `<ActionForm>`
wraps `<form>` and wires `data-action="{form.name}:submit"` plus
`aria-busy`. `<TextInput>` is passive and signal-friendly — pass a
plain string for uncontrolled mode (FormData picks up the value on
submit) or a `Signal<string>` for controlled. `<ActionInput>` is
Fairfox's dual-mode view/edit with action dispatch on commit,
`saveOn` picks the trigger, `renderView` opts into rich view
rendering without adding deps. `<ConfirmDialog.Host />` exposes a
Promise-returning `confirm()`. `<Toast.Viewport />` consumes
`errorState` automatically.

Theming splits across two stylesheets. `theme.css` carries semantic
tokens consumers override (`--polly-surface`, `--polly-text`,
`--polly-accent`, space / radius / motion scales, light + dark
palettes, explicit `data-polly-theme` override, WCAG AA contrast
in both modes). `styles.css` carries the structural and a11y rules
that should not be overridden.

#### CSS conformance checks in `@fairfox/polly/quality`

Four new subcommands enforce the styling contract:

```
polly quality css          # all four
polly quality css-quality  # hardcoded values
polly quality css-layout   # Layout-component enforcement
polly quality css-vars     # undefined var references
polly quality css-unused   # dead selectors (advisory)
```

Each check exposes a library function (`checkCssQuality`,
`checkCssLayout`, `checkCssVars`, `checkCssUnused`) for programmatic
use. Rule disabling, token-prefix configuration, layout exempt
paths, and dynamic-variable lists are all configurable per check.

A `polly-ignore-all` marker in a file's first-line CSS comment opts
out of `css-quality`. A `layout-ignore` CSS comment on the line or
the preceding line opts out of `css-layout`.

#### `@fairfox/polly/test/visual` — visual regression harness

A new testing subpath pairs with the existing `@fairfox/polly/test/browser`
harness and adds pixel-diff assertions via pixelmatch.

```ts
import { matchBaseline, resolveVisualPaths } from "@fairfox/polly/test/visual";

const { baselinesDir, diffsDir } = resolveVisualPaths(projectRoot);
const result = await matchBaseline(page, "modal-dark", baselinesDir, diffsDir, {
  theme: "dark",
  motion: "reduced",
  selector: "[data-polly-modal-content]",
});
```

Emulates `prefers-color-scheme` and `prefers-reduced-motion`, masks
time-varying selectors, commits baselines under
`tests/visual/__baselines__/`, writes diff PNGs on mismatch under
`tests/visual/__diffs__/`. `POLLY_VISUAL_UPDATE=1` overwrites
baselines locally; the harness refuses that env var when `CI=true`
to prevent silently-drifted baselines from landing.

#### Browser test runner shipped as `polly test:browser`

The Puppeteer-based browser test runner that Polly uses internally
now ships in `dist/`. Consumers wire up `*.browser.{ts,tsx}` files
and run them with `polly test:browser <dir>` — no need to copy or
reimplement the orchestrator. The underlying harness
(`describe`/`test`/`expect`/`flush`/`cleanup`/`done`) already
shipped via `@fairfox/polly/test/browser`; this closes the gap by
exposing the runner too.

#### Centralised quality logger

Every `console` call in the quality tool now routes through a
mutable `logger` singleton exported from `@fairfox/polly/quality`.
Tests swap its methods at runtime and restore with `resetLogger()`.

#### Recipe

`recipes/actions-driven-app/` demonstrates the complete loop
end-to-end: stores, forms, registry, components, $persistedState,
and five unit tests.

### Documentation

- `docs/ACTIONS.md` — the action-registry pattern, three-layer
  split, form lifecycle, error surface, migration guide.
- `docs/UI.md` — compound components, theming contract, a11y
  guarantees, styling hooks, per-primitive worked examples.
- `docs/CSS.md` — the four CSS conformance checks, configuration,
  escape hatches, programmatic use.
- `docs/TESTING.md` — new sections on action-handler testing with
  `runAction`, visual regression with `matchBaseline`, and the
  quality logger mock pattern.

## [0.24.0] - 2026-04-17

### Added

#### Mesh client factory

`createMeshClient()` assembles signalling, WebRTC, encryption, and the
Automerge `Repo` from one call and configures `$meshState` against the
resulting repo. `MeshSignalingClient` and `MeshWebRTCAdapter` accept
optional `WebSocket` and `RTCPeerConnection` constructors; defaults
read from `globalThis` so browser code is unchanged. A clear error
now replaces the "undefined is not a constructor" failure when
neither a global nor an injected impl is available.

#### `@fairfox/polly/mesh/node`

A new subpath export ships the Node-specific wiring.
`fileKeyringStorage(path)` reads and writes the serialised keyring
atomically (tmp-then-rename, 0600 perms). `bootstrapCliKeyring` runs
the first-run pairing UX: generate an identity, print the public-key
fingerprint to stderr, read a pairing token from stdin, apply it,
save. **Token issuance stays browser-side**; the CLI path is
receive-only because the listed consumers (archival cron, LLM
proxies, admin tools, headless bridges) onboard from a trusted
device rather than introducing new peers. Neither `werift` nor
`@roamhq/wrtc` is bundled — both are declared as optional peer
dependencies and the consumer passes the `RTCPeerConnection` class
into the factory, keeping Polly out of the native-binary install-risk
story.

#### Blob store primitive

A small content-addressed blob store rounds out the mesh
participants' storage shape, so non-CRDT payloads (uploaded files,
images, anything binary) can ride alongside `$meshState` without
forcing every byte through Automerge.

## [0.23.0] - 2026-04-16

### Added

#### `checkNoAsCasting` exclusion flags

The `no-as-casting` conformance check now accepts `--exclude-packages`
and `--exclude-files` flags, letting monorepos adopt the check
incrementally without waiting for every legacy package to be cleaned
up first. The same options are available on the programmatic
`checkNoAsCasting` API as `excludePackages` / `excludeFiles`.

### Fixed

#### `as` line scanner stops flagging prose

The line scanner no longer flags prose that happens to contain the
word `as` — CLI help text in template literals, JSX paragraph copy,
and SQL column aliases all pass cleanly now. The string-literal
detector checks every occurrence on a line rather than just the
first, and two new heuristics (`isJsxText`, `isPlainText`) catch the
remaining patterns.

#### Test infrastructure: `Cycle detected` no longer kills parallel suites

`automerge-repo`'s xstate `DocHandle` machine throws a `Cycle
detected` error via `setTimeout` when multiple `Repo` instances
coexist across parallel test files. A preload script intercepts the
throw so the 19 tests that were previously killed by the leaked
error now run to completion. `Repo` instances in the affected test
files are shut down properly in `afterEach`.

Closes #44, closes #45.

## [0.22.0] - 2026-04-16

### Changed

#### Peer/mesh exports isolated behind subpath imports

The main bundle no longer pulls in `@automerge/*` or `tweetnacl` —
consumers who only use `$sharedState`, `$syncedState`, or `$resource`
can now bundle without stubbing those dependencies. Peer-first and
mesh primitives live at `@fairfox/polly/peer` and
`@fairfox/polly/mesh` respectively.

#### Quality conformance check moved to CLI

The quality conformance check, which relied on `node:fs` and broke in
the browser-targeted build, is now a proper CLI subcommand
(`polly quality`) built with the node target alongside the other
tools.

## [0.21.0] - 2026-04-16

### Added

#### Peer-first state primitives (RFC-041)

Polly now offers three resilience tiers for synced state, ordered by how resilient the data is to server loss. Applications pick per piece of data; all three coexist in one codebase.

**`$peerState` — server as a full peer on the data path.** Every device holds a full Automerge CRDT replica, the server included. Server-side cron, HTTP handlers, and scheduled jobs can open document handles and mutate contents. Any device loss — including the server — is recoverable from any reconnecting client's local history.

```typescript
import {
  createPeerStateClient,
  configurePeerState,
  $peerState,
  $peerText,
  $peerCounter,
  $peerList,
} from "@fairfox/polly";

const client = createPeerStateClient({ url: "wss://yourapp.com/polly/peer" });
configurePeerState(client.repo);

const settings = $peerState("settings", { theme: "dark" });
const draft = $peerText("draft", "");
const visits = $peerCounter("visits", 0);
const todos = $peerList("todos", []);

await settings.loaded;
settings.value = { theme: "light" }; // syncs to server and all peers
```

Server side:

```typescript
import { createPeerRepoServer } from "@fairfox/polly";

const server = await createPeerRepoServer({
  port: 3030,
  storagePath: "./data/polly-peer",
});

// Cron jobs mutate documents the same way clients do.
const handle = await server.repo.find(someDocumentId);
handle.change(doc => { doc.count += 1 });
```

Or hosted alongside Elysia:

```typescript
import { Elysia } from "elysia";
import { peerRepo } from "@fairfox/polly/elysia";

const app = new Elysia()
  .use(peerRepo({ port: 3030, storagePath: "./data/polly-peer" }))
  .get("/stats", ({ pollyPeerRepo }) => ({
    peers: pollyPeerRepo.peers.length,
  }))
  .listen(8080);
```

**`$meshState` — server off the data path entirely.** Peers hold full replicas and exchange operations through signed, end-to-end encrypted WebRTC data channels. The application functions with zero server uptime. A small stateless signalling server helps peers find each other; removing it does not affect running connections.

```typescript
import {
  configureMeshState,
  $meshState,
  MeshNetworkAdapter,
  MeshWebRTCAdapter,
  MeshSignalingClient,
} from "@fairfox/polly";

const signalingClient = new MeshSignalingClient({
  url: "wss://yourapp.com/polly/signaling",
  peerId: "device-A",
  onSignal: (from, payload) => webrtcAdapter.handleSignal(from, payload),
});

const webrtcAdapter = new MeshWebRTCAdapter({
  signaling: signalingClient,
  peerId: "device-A",
  knownPeerIds: ["device-B"],
});

const meshAdapter = new MeshNetworkAdapter({
  base: webrtcAdapter,
  keyring,
});

const repo = new Repo({ network: [meshAdapter] });
configureMeshState(repo);

const notes = $meshState("notes", { entries: [] });
// Operations flow peer-to-peer, signed and encrypted
```

#### Cryptographic layer

Ed25519 signing and XSalsa20-Poly1305 authenticated encryption via tweetnacl. Every `$meshState` operation is signed by the originating peer and encrypted under a per-document symmetric key before it leaves the device.

**Pairing.** First-time key exchange between devices uses a one-way pairing token: the issuer generates a token containing their signing public key, the shared document encryption key, a TTL, and a nonce. The token is base64-encoded for QR-code or copy-paste display.

```typescript
import {
  createPairingTokenWithFreshIdentity,
  encodePairingToken,
  decodePairingToken,
  applyPairingToken,
} from "@fairfox/polly";

// Issuer side
const { identity, token } = createPairingTokenWithFreshIdentity({
  issuerPeerId: "device-A",
  documentKeyId: DEFAULT_MESH_KEY_ID,
});
const qrString = encodePairingToken(token);

// Receiver side
const decoded = decodePairingToken(scannedQrString);
applyPairingToken(decoded, receiverKeyring);
```

**Revocation.** A compromised peer can be kicked out via a signed revocation record that propagates to every device. The `MeshNetworkAdapter` drops all further messages from revoked peers. An optional `revocationAuthority` set on the keyring restricts who is allowed to issue revocations.

```typescript
import { createRevocation, encodeRevocation, revokePeerLocally } from "@fairfox/polly";

// Local-only revocation
revokePeerLocally("compromised-peer", keyring);

// Transportable revocation (signed, broadcast to all peers)
const record = createRevocation({
  issuer: keypair,
  issuerPeerId: "admin",
  revokedPeerId: "compromised-peer",
  reason: "lost at conference",
});
const bytes = encodeRevocation(record, keypair);
```

**Signing on `$peerState`.** The `sign: true` option adds per-operation Ed25519 signatures to the relay transport without preventing the server from reading document contents. This gives Byzantine defence (a compromised client cannot push unsigned writes) while keeping server-side compute functional.

```typescript
const client = createPeerStateClient({
  url: "wss://yourapp.com/polly/peer",
  sign: true,
  keyring: { identity, knownPeers, documentKeys: new Map(), revokedPeers: new Set() },
});
configurePeerState(client.repo, { signEnabled: true });
```

#### Signalling server

An Elysia plugin that relays SDP/ICE messages between `$meshState` peers for WebRTC connection setup. Stateless — it holds no document data, no encryption keys, and no replicas.

```typescript
import { Elysia } from "elysia";
import { signalingServer } from "@fairfox/polly/elysia";

const app = new Elysia()
  .use(signalingServer({ path: "/polly/signaling" }))
  .listen(8080);
```

The server replaces the sender's claimed peer id with the authenticated join id on every relayed signal, preventing impersonation. Peers whose sockets have closed are evicted from the routing table on the next send attempt.

#### Browser test harness

A Puppeteer-based harness shipped as `@fairfox/polly/test/browser` for testing browser-only modules (WebRTC adapters, Preact components, anything that needs real DOM or native WebSocket). The runner bundles each `.browser.ts` file with Bun.build, serves it on an ephemeral port, and collects results via `window.__testResults`.

```typescript
import { describe, test, expect, done, flush, cleanup, waitFor } from "@fairfox/polly/test/browser";

const app = document.getElementById("app")!;

describe("my feature", () => {
  test("renders correctly", async () => {
    render(<MyComponent />, app);
    await flush();
    expect(app.querySelector("h1")).toHaveTextContent("Hello");
    expect(app.querySelector("input")).toHaveValue("default");
    expect(app.querySelector("button")).not.toBeDisabled();
    cleanup(app);
  });
});

done();
```

Run with:

```bash
bun tools/test/src/browser/run.ts tests/browser
HEADLESS=false bun tools/test/src/browser/run.ts tests/browser  # visible
```

Matchers: `toBe`, `toEqual`, `toContain`, `toBeTruthy`, `toBeFalsy`, `toBeNull`, `toBeDefined`, `toBeUndefined`, `toBeGreaterThan`, `toHaveLength`, `toExist`, `toHaveTextContent`, `toBeChecked`, `toBeDisabled`, `toHaveValue`, `toHaveAttribute`, plus `.not` variants. Helpers: `flush(ms?)`, `cleanup(container)`, `waitFor(predicate, timeout, interval)`.

The runner includes an internal Bun bundler plugin that redirects Automerge to its base64 WASM variant, solving the `.wasm` import issue under `Bun.build({ target: "browser" })`.

#### Quality tooling

**No-as-casting conformance check.** Bans all TypeScript type assertions (`as Type`) except `as const` and the explicit escape hatch `as unknown as`. Includes pattern-specific fix advice:

```
src/foo.ts:42
  const el = e.target as HTMLInputElement;
  💡 Use instanceof: if (el instanceof HTMLInputElement) { el.value ... }
```

Run with `bun scripts/check-no-as-casting.ts`. A companion codemod (`bun scripts/fix-as-casting.ts`) converts all violations to `as unknown as` for one-time migration.

The check is exported as `@fairfox/polly/quality` so consuming applications can adopt the same rule without copying files:

```typescript
import { checkNoAsCasting } from "@fairfox/polly/quality";

const result = await checkNoAsCasting({
  rootDir: process.cwd(),
  exclude: ["node_modules", "dist"],
});

if (result.violations.length > 0) {
  result.print(); // prints violations with pattern-specific fix advice
  process.exit(1);
}
```

The export includes `isLineClean` (per-line check), `suggestFix` (pattern-specific advice), and `checkNoAsCasting` (full directory scan with results). Applications wire it into CI, pre-commit hooks, or their own conformance scripts.

The browser test harness (`@fairfox/polly/test/browser`) and the quality checks (`@fairfox/polly/quality`) together give consuming applications the same quality tooling that Polly itself uses.

#### TLA+ formal specifications

Two new TLA+ specs alongside the existing `MessageRouter.tla`:

- **PeerState.tla** — models the relay protocol with N replicas, a server replica with persistent storage, op exchange, and server data loss recovery. Verifies strong eventual convergence, recovery convergence, and no-fabrication.
- **MeshState.tla** — extends PeerState with signed operations, per-peer access sets, and revocation. Verifies signature soundness, revocation convergence, and no-forged-delivery.

Run with `docker-compose exec tla tlc PeerState.tla` or `tlc MeshState.tla`.

#### Foundation modules

- **BlobRef** — content-addressed reference type for future blob-storage RFC. SHA-256 hash, type guard, async factory.
- **PrimitiveRegistry** — runtime namespace collision detection across primitive families. Throws `PrimitiveCollisionError` naming both call sites.
- **Access** — declarative read/write authorisation types with predicate factories (`anyone`, `nobody`, `onlyPeer`, `anyOfPeers`) and compositors (`and`, `or`, `not`).
- **SchemaVersion** — reserved `__schemaVersion` field on documents, migration runner with contiguity checks, op-version compatibility check for sync-time rejection.
- **MigratePrimitive** — one-way cross-family data migration with a `migrationRegistry` that prevents re-hydration of moved sources.

### Deployment guidance

#### `$peerState` relay server on Railway

The relay server is a single Elysia process that hosts an Automerge-Repo `Repo` with `WebSocketServerAdapter` and `NodeFSStorageAdapter`. Deploy it on Railway (or any platform that supports persistent volumes and WebSocket connections):

1. **Process.** One Bun process running `createPeerRepoServer({ port, storagePath })` or the `peerRepo` Elysia plugin.
2. **Storage.** Persistent volume mounted at `storagePath`. Automerge documents are stored as files by `NodeFSStorageAdapter`. Stream the volume to S3 via [Litestream](https://litestream.io/) for disaster recovery.
3. **Port.** A single WebSocket endpoint (default `/polly/peer`). TLS termination is handled by the platform.
4. **Recovery.** If the server loses its volume, deploy a fresh instance. The first client to reconnect pushes its full Automerge history; subsequent clients converge. No manual restore step needed.
5. **Cron.** Server-side code opens document handles on the `Repo` and mutates them the same way clients do. Changes propagate to connected clients through the same sync protocol.

#### `$meshState` signalling server

The signalling server is a stateless Elysia WebSocket route. It holds no data and no keys.

1. **Process.** One Bun process running the `signalingServer` Elysia plugin. Can share a process with the relay server or any other Elysia routes.
2. **Storage.** None. The server is stateless.
3. **Port.** A single WebSocket endpoint (default `/polly/signaling`). Can be deployed on Railway, Cloudflare Workers, Fly.io, a Pi, or anywhere that terminates WebSocket.
4. **Replacement.** Losing the signalling server does not affect existing peer-to-peer connections. New connections are blocked until a replacement is deployed, but data is safe on every peer's local storage.

#### `$meshState` optional cron peer

A dedicated always-on peer that participates in the mesh as an ordinary client and happens never to sleep:

1. **Process.** A separate Bun/Node process running the same Polly client code as browsers. Has its own device keypair provisioned via the pairing flow.
2. **Storage.** Local Automerge replica (IndexedDB via `IndexedDBStorageAdapter` or NodeFS).
3. **Deployment.** Railway, VPS, Pi, Tailnet, laptop — anywhere. It is not on the critical path for client-to-client sync.
4. **Keys.** Provisioned via `applyPairingToken` the same way any other device is. Only holds keys for documents it is authorised to access.

#### Client-side persistence

Browsers use `IndexedDBStorageAdapter` from `@automerge/automerge-repo-storage-indexeddb` for local Automerge document persistence. Documents survive page reloads, browser restarts, and offline periods. Storage is per-origin.

### Changed

- `PeerStateOptions` no longer has an `encrypt` field. Encryption prevents the server from parsing Automerge sync messages, which degrades the relay to a dumb byte forwarder — the same role `$meshState` already fills. Applications that want encrypted state use `$meshState`.
- `MeshKeyring` now requires a `revokedPeers: Set<string>` field.
- `MeshKeyring` accepts an optional `revocationAuthority?: Set<string>` for restricting who can issue revocations.
- `configurePeerState` accepts an optional second argument `{ signEnabled?: boolean }` for tracking signing-enabled Repos.
- All `as Type` assertions across the codebase have been replaced with `as unknown as Type` (the conformance-check escape hatch) or eliminated. New code must not use `as Type`.

### Dependencies

New optional peer dependencies (applications that use only `$sharedState` do not install them):

- `@automerge/automerge-repo` >= 2.5.0
- `@automerge/automerge-repo-network-websocket` >= 2.5.0
- `@automerge/automerge-repo-storage-indexeddb` >= 2.5.0
- `@automerge/automerge-repo-storage-nodefs` >= 2.5.0
- `tweetnacl` >= 1.0.0
- `ws` >= 8.0.0

New dev dependency: `puppeteer` (for the browser test harness).

All Automerge and crypto packages are externalised in the Polly build. The Polly bundle itself ships zero WASM or crypto bytes; applications bring them via their own bundler.

## [0.9.0] - 2025-12-30

### Added

#### Expose Tier 1 & 2 Optimization Features to Users (Issue #13)

Exposed all verification optimization features through the public TypeScript API:

1. **Updated Type Definitions** (`tools/verify/src/config.ts`)
   - Expanded `LegacyVerificationConfig` interface with all optimization fields
   - Full TypeScript autocomplete support

2. **Validation Logic** (`tools/verify/src/config/parser.ts`)
   - Validates include/exclude mutual exclusivity
   - Checks symmetry group sizes
   - Validates perMessageBounds ranges (1-20)
   - Validates temporal constraint ordering
   - Validates bounded exploration depth limits

3. **Config Generation** (`tools/verify/src/codegen/config.ts`)
   - Generated configs now include commented examples for all optimizations

Fixes #13

## [0.8.0] - 2025-12-30

### Added

#### Verification Optimization Features (Issue #12)

Added TLA+ codegen support for all verification optimizations:

- **Tier 1 (Zero Precision Loss):** Message type filtering (`include`/`exclude`), symmetry reduction, per-message bounds
- **Tier 2 (Controlled Approximations):** Temporal constraints, bounded exploration

Implements #12

## [0.6.1] - 2025-12-23

### Fixed

#### Verification: Filter Invalid TLA+ Identifiers from Message Types (Issue #11)
Fixes critical bug where the code analyzer was extracting TypeScript utility type definitions as message types, generating invalid TLA+ syntax.

**Problem:**
The `polly verify` command's code analyzer was treating TypeScript type definition syntax like `{ ok: true; value: T }` as message types. This generated invalid TLA+ identifiers containing braces, colons, and semicolons, causing TLA+ parsing to fail with lexical errors.

**Example Error:**
```
Lexical error at line 110, column 17. Encountered: ";" (59), after : ""
Fatal errors while parsing TLA+ spec in file UserApp
```

**Solution:**
- Added `isValidTLAIdentifier()` validation function to both `TypeExtractor` and `HandlerExtractor`
- Validates identifiers match TLA+ rules: `/^[a-zA-Z][a-zA-Z0-9_]*$/`
- Filters message types during analysis to only include valid TLA+ identifiers
- Added debug logging to track filtered types (use `POLLY_DEBUG=1`)

**What's Filtered:**
- ❌ `{ ok: true; value: t }` (contains braces, colons, semicolons)
- ❌ `{ ok: false; error: e }` (contains braces, colons, semicolons)
- ❌ `event-type` (contains hyphen)
- ❌ `123event` (starts with digit)
- ✅ `authenticate`, `user_login`, `API_REQUEST`, `event123` (valid)

**Impact:**
The generated `UserApp.tla` now only contains valid message types, preventing TLA+ parsing errors. Projects with TypeScript utility types can now use `polly verify` successfully.

**Testing:**
- Added comprehensive unit tests (`vendor/analysis/src/extract/__tests__/tla-validation.test.ts`)
- Tests cover valid identifiers, invalid identifiers, and edge cases
- All 3 tests passing with 18 assertions

**Debug Mode:**
Run with `POLLY_DEBUG=1` to see filtered types:
```bash
POLLY_DEBUG=1 bunx polly verify
```

Output:
```
[WARN] Filtered out 2 invalid message type(s):
[WARN]   - "{ ok: true; value: t }" (not a valid TLA+ identifier)
[WARN]   - "{ ok: false; error: e }" (not a valid TLA+ identifier)
```

Fixes #11

## [0.6.0] - 2025-12-23

### Changed
- **Major refactoring**: Eliminated all default exports across the codebase
- Fixed all linting issues for consistent code style
- Applied Biome formatter for unified formatting
- Resolved all TypeScript compilation errors (340+ → 0)

## [0.5.4] - 2025-12-16

### Fixed

#### Critical: Verify Feature Now Works (Issue #10)
Fixes the verify command which was completely broken in v0.5.3 due to missing package export.

**Bug 1: Missing ./verify export**
- Added `./verify` export to package.json pointing to lightweight public API
- Users can now import `defineVerification` from `@fairfox/polly/verify`
- Created new `public-api.ts` entry point (780 bytes, zero dependencies)
- Full verify API (adapters, analysis) remains in bundled CLI only

**Bug 2: CommonJS require() in ESM codebase**
- Replaced `require()` with ESM dynamic `import()` in verify CLI
- Added cache busting with timestamp query parameter
- Properly handles ESM default exports

**Impact:** The verify feature is now fully functional. Before this fix:
- `polly verify --setup` ✅ worked (generated config)
- `polly verify --validate` ❌ failed (couldn't load config)

After this fix, both commands work correctly.

**Technical Details:**
- Public API exports only `defineVerification` function and config types
- Heavy dependencies (ts-morph, analysis tools) only bundled in CLI
- User config files have zero runtime dependencies beyond polly itself

Fixes #10

## [0.5.3] - 2025-12-15

### Changed
- **Internal restructuring**: Consolidated monorepo into single package at repository root
- Moved tests from `packages/tests/` to `tests/`
- Moved examples from `packages/examples/` to `examples/`
- Flattened `packages/polly/` to repository root
- Integrated analysis, verify, and visualize tools as vendored code
- Updated all internal imports to use relative paths
- Unified build and development workflow

**Note:** This is an internal restructuring only - no API changes. All public exports remain the same.

## [0.5.2] - 2025-12-14

### Fixed

#### Structurizr DSL Syntax Error in Relationships
Fixes critical DSL syntax error that prevented visualization in Structurizr Lite (reported by Lingua CMS team in Issue #8).

**Problem:**
The `technology` parameter was incorrectly placed as a keyword inside the relationship block, causing Structurizr to fail with: `Unexpected tokens (expected: tags, url, properties, perspectives) at line X: technology "Function Call"`

**Before (Invalid):**
```dsl
handler -> service "Calls method()" {
  technology "Function Call"  # ❌ Invalid
  tags "Auto-detected"
}
```

**After (Valid):**
```dsl
handler -> service "Calls method()" "Function Call" {  # ✅ Correct
  tags "Auto-detected"
}
```

**Fixed Files:**
- `vendor/visualize/src/codegen/structurizr.ts` - Corrected relationship syntax for both user-provided and auto-detected relationships
- `vendor/visualize/src/__tests__/enhanced-dsl-integration.test.ts` - Updated tests to validate correct DSL syntax and prevent regression

**Impact:**
All DSL files now generate valid Structurizr syntax and can be visualized without errors. This affects both explicit relationships and auto-detected relationships from cross-file analysis.

## [0.5.1] - 2025-12-14

### Enhanced

#### Cross-File Relationship Detection
Fixes the architecture pattern mismatch reported in Issue #8 for projects with router-handler separation (like Lingua CMS).

**Problem Solved:**
v0.5.0 automatic detection only worked when handler routing and business logic were in the same function. It failed for production codebases with proper separation of concerns where handlers are in separate files.

**What's New:**
- **Cross-file AST traversal** - When detecting a handler call, Polly now resolves the import and analyzes the function body in the separate file
- **Nested property access detection** - Correctly detects patterns like `repositories.users.create()`, `db.connection.query()`
- **Function name inference** - Detects service calls from function names like `getDatabase()`, `createRepositories()`
- **Enhanced component mappings** - Added "repositories" and improved pattern matching
- **Graceful failure handling** - Silently handles missing files or parse errors without breaking analysis

**Example:**
```typescript
// server.ts (router):
if (isQueryMessage(message)) {
  response = await handleQuery(message);  // ← Polly detects handler
}

// handlers/query.ts (separate file):
export async function handleQuery(message: QueryMessage) {
  const db = getDatabase();              // ← NOW DETECTED ✅
  const repos = createRepositories(db);  // ← NOW DETECTED ✅
  return repos.users.findById(id);       // ← NOW DETECTED ✅
}

// Generated DSL (automatic):
query_handler -> db_client "Calls getDatabase()"
query_handler -> repositories "Calls createRepositories()"
query_handler -> repositories "Calls findById()"
```

**Test Coverage:**
- Added cross-file-handlers test fixture mimicking router-handler separation
- 7 new integration tests for cross-file relationship detection
- All 57 tests passing with 221 assertions

**Technical Implementation:**
- New `resolveImportedFunction()` method using ts-morph's `getModuleSpecifierSourceFile()`
- Recursive analysis preserves handler context across file boundaries
- Supports regular functions, arrow functions, and const function declarations
- Enhanced `extractFromPropertyAccess()` to handle nested property chains

**Impact:**
This enhancement makes automatic relationship detection work for real-world production codebases with proper architectural patterns. No more isolated gray boxes for projects with separated handler files!

## [0.5.0] - 2025-12-14

### Added

#### Auto-Generated, Always Up-to-Date Architecture Docs (Issue #8 Phase 2)
This release completes Phase 2 of Issue #8, implementing automatic detection features that eliminate manual configuration and ensure architecture diagrams stay in sync with code changes.

**Philosophy:** Architecture diagrams should be auto-generated from code analysis, not manually configured. When code changes, diagrams update automatically on re-run.

##### Priority 1: Automatic Relationship Detection ✅
- **Code analysis-based relationship detection** - Analyzes handler function bodies to detect component dependencies
- **Recursive function following** - Traces execution through local function calls to find actual service invocations
- **Property access detection** - Identifies patterns like `userService.listUsers()`, `authService.authenticate()`
- **Multiple relationship patterns** - Supports function calls, database queries, HTTP requests
- **Service name inference** - Maps object names to component IDs (user → user_service, auth → auth_service, db → db_client)
- **Automatic service component generation** - Creates service component definitions when relationships detected
- **Confidence scoring** - Relationships include confidence level (high/medium/low) and evidence
- **AST traversal** - Uses ts-morph to analyze TypeScript syntax trees
- **Deduplication** - Prevents duplicate relationships within a handler
- **Zero configuration** - Works automatically, no manual relationship definitions needed

**Example:**
```typescript
// Handler code:
async function handleQuery(message: QueryMessage) {
  const result = await userService.listUsers();
  return { type: 'result', data: result };
}

// Generated DSL (automatic):
user_service = component "User Service" {
  tags "Service" "Auto-detected"
}

query_handler -> user_service "Calls listUsers()" {
  technology "Function Call"
  tags "Auto-detected"
}
```

##### Priority 4: Automatic Component Grouping ✅
- **4-tier grouping strategy** for intelligent component organization:
  1. **Authentication handlers** - login, logout, auth, verify, register, signup
  2. **Subscription handlers** - subscribe, unsubscribe
  3. **Entity-based grouping** - Extracts entities from message types (user_add, todo_remove → User Management, Todo Management)
  4. **Query/Command pattern** - Groups remaining handlers by read vs write operations
- **Smart thresholds** - Only creates groups when >= 50% of components can be grouped OR >= 2 groups exist
- **Minimum group size** - Requires >= 2 components per entity group
- **Lifecycle handler exclusion** - Skips connection, message, close, error handlers
- **Fallback to flat rendering** - Returns empty array when grouping doesn't add value
- **Backward compatible** - Manual groups take precedence over automatic grouping
- **Pattern matching** - Supports both snake_case (user_add) and camelCase (addUser) naming

**Example:**
```dsl
group "User Management" {
  user_add_handler = component "User Add Handler" { ... }
  user_update_handler = component "User Update Handler" { ... }
  user_remove_handler = component "User Remove Handler" { ... }
}

group "Todo Management" {
  todo_add_handler = component "Todo Add Handler" { ... }
  todo_update_handler = component "Todo Update Handler" { ... }
}

group "Query Handlers" {
  list_users_handler = component "List Users Handler" { ... }
  get_todos_handler = component "Get Todos Handler" { ... }
}
```

##### Priority 5: Auto-Generate Dynamic Diagrams ✅
- **Automatic sequence diagram generation** from detected relationships
- **Category-based organization** - Groups handlers by authentication, entity (user, todo), query/command
- **Smart diagram count** - Single overview diagram for small projects (<= 5 handlers, <= 3 categories)
- **Category-specific diagrams** - Separate diagrams per category for larger projects (max 5)
- **Handler-to-service flows** - Shows execution path from message handler through business services
- **Descriptive titles** - "Authentication Flow", "User Management Flow", "Query Processing Flow"
- **Contextual descriptions** - Explains what each diagram shows
- **Proper scope** - Uses correct container context (extension.server)
- **Auto-layout** - Left-to-right flow visualization
- **Configuration option** - Can disable via `includeDynamicDiagrams: false`
- **Backward compatible** - User-provided diagrams generated first, then automatic diagrams

**Example (small project - single overview):**
```dsl
dynamic extension.server "Message Processing Flow" "Shows message processing flow through handlers and services" {
  query_handler -> user_service "Calls listUsers()"
  command_handler -> user_service "Calls executeUserCommand()"
  auth_handler -> auth_service "Calls authenticate()"
  autoLayout lr
}
```

**Example (larger project - category-specific):**
```dsl
dynamic extension.server "Authentication Flow" "Shows authentication message processing" {
  auth_handler -> auth_service "Calls authenticate()"
  login_handler -> auth_service "Calls login()"
  logout_handler -> auth_service "Calls logout()"
  autoLayout lr
}

dynamic extension.server "User Management Flow" "Shows user management operations" {
  user_add_handler -> user_service "Calls addUser()"
  user_update_handler -> user_service "Calls updateUser()"
  user_remove_handler -> user_service "Calls removeUser()"
  autoLayout lr
}
```

#### Test Infrastructure
- **50 integration tests** with **187 assertions** - all passing
- **8 tests for Priority 1** - Relationship detection and DSL output
- **5 tests for Priority 4** - Component grouping logic
- **5 tests for Priority 5** - Dynamic diagram generation
- **Real code analysis** (not mocked) - uses actual TypeScript parsing
- **Real test project** - complete WebSocket server with service calls
- **Validates entire pipeline** from TypeScript files → Analysis → DSL output

#### Architecture Enhancements
- Added `relationships?: ComponentRelationship[]` to `MessageHandler` type
- Created `RelationshipExtractor` class with recursive AST traversal
- Enhanced `StructurizrDSLGenerator` with automatic grouping and diagram generation
- Proper deduplication and evidence tracking for detected relationships
- Smart threshold logic to prevent over-grouping and over-diagramming

### Technical Details
- **New file:** `vendor/analysis/src/extract/relationships.ts` (~415 lines) - Core relationship detection
- **Modified:** `vendor/analysis/src/types/core.ts` - Added ComponentRelationship type
- **Modified:** `vendor/analysis/src/extract/handlers.ts` - Integrated relationship extraction
- **Modified:** `vendor/visualize/src/codegen/structurizr.ts` - Added automatic features
- **Modified:** `vendor/visualize/src/__tests__/enhanced-dsl-integration.test.ts` - Comprehensive test coverage

### Value Proposition
**Before Phase 2:** Architecture diagrams required manual configuration of relationships, groups, and flows. When code changed, diagrams became stale unless manually updated.

**After Phase 2:** Architecture diagrams are auto-generated from code analysis. Re-running `polly visualize` automatically updates diagrams to reflect current code structure. Zero configuration needed.

**Impact:** This delivers on the core promise of Issue #8 - "auto-generated, always up-to-date architecture docs that require zero manual configuration."

**COMPLETES #8 Phase 2** - All 3 automatic detection priorities delivered (100%)

## [0.4.2] - 2025-12-14

### Added

#### Priority 6: Deployment Diagrams - FINAL PIECE
This release adds the final missing piece, completing ALL 7 API infrastructure priorities from Issue #8 Phase 1.

**Note:** v0.4.1 was published without deployment diagrams. This v0.4.2 release adds Priority 6: Deployment Diagrams.

- **Deployment environments** with multi-environment support (Production, Staging, Dev)
- **Nested deployment nodes** for hierarchical infrastructure (Cloud → Region → Instance)
- **Container instance mapping** with explicit deployment targets
- **Instance scaling** - specify replica counts per container
- **Deployment properties** for operational metadata (region, auto-scaling, etc.)
- **Automatic container deployment** as fallback when not explicitly configured
- **Deployment views** auto-generated for each environment
- **5 integration tests** covering all deployment scenarios
- Test suite increased from 27 to 32 tests, assertions from 95 to 112

**COMPLETES #8 Phase 1** - All 7 API infrastructure priorities delivered (100%)

## [0.4.1] - 2025-12-14

### Note
This version was published without deployment diagrams. Use v0.4.2 for complete Phase 1 functionality.

## [0.4.0] - 2025-12-14

### Added

#### Enhanced Structurizr DSL Generation (Issue #8)
Complete implementation of ALL 7 priorities with comprehensive real integration testing:

##### Priority 2: Styling System ✅
- **Default element styles** with hexagons and semantic colors
  - Query handlers: Green (#51cf66)
  - Command handlers: Orange (#ff922b)
  - Authentication: Red (#ff6b6b)
  - Subscription: Purple (#845ef7)
- **Default relationship styles** with orthogonal routing, proper colors
- **Theme URL support** (Structurizr default theme)
- **Full customization** - override any style or disable defaults entirely
- **4 integration tests** covering all styling features

##### Priority 3: Properties & Metadata ✅
- **Source file paths** with line numbers (e.g., `src/server/handlers.ts:55`)
- **Technology stack detection** (TypeScript, WebSocket, Socket.IO, Elysia)
- **Message type classification** (Query, Command, Authentication, Subscription)
- **Pattern identification** (Query Handler, Command Handler, etc.)
- **Custom properties** for user-defined metadata
- **4 integration tests** covering all property features

##### Priority 1: Component Relationships ✅
- **Explicit relationship definition** between components
- **Technology metadata** on relationships
- **Relationship tagging** (Sync, Async, Database, etc.)
- **Optional fields** for minimal syntax
- **2 integration tests** covering relationship scenarios

##### Priority 4: Groups ✅
- **User-defined groups** for organizing related components
- **Proper DSL nesting** with indentation
- **Ungrouped components** rendered outside groups
- **Multiple groups** support
- **3 integration tests** covering all grouping scenarios

##### Priority 5: Dynamic Diagrams ✅
- **User-provided dynamic diagrams** with custom steps (sequence/flow diagrams)
- **Sequence flow specification** (from → to → description)
- **Diagram title and description**
- **Configurable scope** (container, system)
- **Multiple diagrams** support
- **Auto-layout** with left-to-right flow
- **2 integration tests** covering diagram scenarios

##### Priority 7: Perspectives ✅
- **Component-level perspectives** (Security, Performance, etc.)
- **Multiple perspectives per component**
- **Name-description pairs** for architectural reasoning
- **Optional perspectives** (only added when configured)
- **2 integration tests** covering perspective scenarios

##### Priority 6: Deployment Diagrams ✅
- **Deployment environments** with multi-environment support (Production, Staging, Dev)
- **Nested deployment nodes** for hierarchical infrastructure (Cloud → Region → Instance)
- **Container instance mapping** with explicit deployment targets
- **Instance scaling** - specify replica counts per container
- **Deployment properties** for operational metadata (region, auto-scaling, etc.)
- **Automatic container deployment** as fallback when not explicitly configured
- **Deployment views** auto-generated for each environment
- **5 integration tests** covering all deployment scenarios

#### Test Infrastructure
- **32 integration tests** with **112 assertions** - all passing
- **Real code analysis** (not mocked) - uses actual TypeScript parsing
- **Real test project** - complete WebSocket server with 6 handlers
- **Validates entire pipeline** from TypeScript files → Analysis → DSL output
- **File system validation** - writes DSL to disk and verifies
- **Manual verification support** - provides Structurizr Lite instructions

#### Type System
- **Strict TypeScript typing** throughout - no `any` types
- **Comprehensive type definitions** in `vendor/visualize/src/types/structurizr.ts`
- 14 element shapes, line styles, routing options
- `ComponentProperties`, `ComponentRelationship`, `ComponentGroup`, `DynamicDiagram`, `Perspective`, `DeploymentNode`, `ContainerInstance` interfaces
- Default color palette and styles with full customization

#### Architecture Enhancements
- Added `projectRoot` field to `ArchitectureAnalysis` type for relative path computation
- Enhanced `StructurizrDSLGenerator` with reusable component generation
- Proper DSL escaping and formatting throughout
- Clean separation of concerns (properties, perspectives, groups)

### Changed
- Component generation refactored to collect definitions before rendering
- DSL generator now supports grouping and perspectives
- All features are backward compatible - additive changes only

### Example Output
```dsl
workspace "example" {
  model {
    extension = softwareSystem "example" {
      server = container "Server" {
        group "Business Logic Handlers" {
          query_handler = component "Query Handler" "..." {
            tags "Message Handler"
            properties {
              "Source" "src/server/handlers.ts:55"
              "Technology" "TypeScript, WebSocket"
              "Message Type" "Query"
              "Pattern" "Query Handler"
            }
            perspectives {
              "Security" "Read-only, low risk"
              "Performance" "Cached for 5 minutes"
            }
          }
        }
      }
    }

    deploymentEnvironment "Production" {
      deploymentNode "AWS" "Cloud infrastructure" "Amazon Web Services" {
        properties {
          "Region" "us-east-1"
          "Auto-scaling" "Enabled"
        }
        deploymentNode "EC2 Instance" "Application server" "t3.medium" {
          containerInstance extension.server 2
        }
      }
    }
  }
  views {
    dynamic extension "Message Flow" "..." {
      user -> extension.server "Sends message"
      extension.server -> extension.server.query_handler "Routes"
      autoLayout lr
    }

    deployment extension "Production" "Production environment deployment architecture" {
      include *
      autoLayout lr
    }

    styles {
      element "Message Handler" {
        shape Hexagon
        background #1168bd
      }
      element "Query" {
        background #51cf66
      }
      relationship "Relationship" {
        routing Orthogonal
      }
      theme https://static.structurizr.com/themes/default/theme.json
    }
  }
}
```

### Technical Details
- Implementation follows strict typing requirements (no `any`)
- Tests validate real code analysis (not mocked)
- Full integration from TypeScript files → DSL output
- Backward compatible - no breaking changes

**COMPLETES #8** - All 7 priorities delivered (100%)

## [0.3.8] - 2025-12-14

### Added

#### Comprehensive Test Coverage (44 Tests)
- **DSL generation tests** - 11 tests covering component diagram generation for all project types
- **Project detection tests** - 15 tests for WebSocket servers, PWAs, and generic TypeScript projects
- **Prevents regressions** - Tests explicitly check for bugs like Issue #7 before they reach users
- **Automated validation** - Tests run as part of `prepublishOnly` script

#### Critical Test Coverage
The DSL generation test suite includes a test that explicitly checks for the Issue #7 bug:
```typescript
test("should NOT generate components when context not in componentDiagramContexts")
```

This test would have caught Issue #7 immediately, preventing it from reaching production.

#### Implementation Gaps Documented
Tests revealed non-critical limitations (documented for future enhancement):
1. Generic projects default to "websocket-app" type
2. Only `server.ts` detected as entry point (not `index.ts`, `app.ts`, `main.ts`)
3. Client context detection not implemented
4. Context mapping naming inconsistent

**Impact**: Before these tests, Issue #7 reached users. After these tests, similar bugs will be caught automatically before release.

See `TEST_COVERAGE_REPORT.md` for full details.

## [0.3.7] - 2025-12-14

### Fixed

#### Visualization: Component Diagrams for All Context Types
- **Auto-detect contexts for component diagrams** - Component diagrams now generated for all detected contexts, not just "background"
- **Fixes WebSocket server visualization** - Handler components now appear in DSL for "server" contexts
- **Fixes PWA/Worker visualization** - Works for "worker", "serviceworker", and all context types
- **Backward compatible** - Chrome extensions with "background" context work identically

**Impact**: Before this fix, component diagrams were only generated for Chrome extension "background" contexts, making the visualization feature broken for all non-extension projects (WebSocket servers, PWAs, workers) despite v0.3.0 adding manifest-optional support.

**Example**: Lingua CMS WebSocket server now generates full component diagrams:
```dsl
server = container "Server" {
  query_handler = component "Query Handler" { ... }
  command_handler = component "Command Handler" { ... }
  subscribe_handler = component "Subscribe Handler" { ... }
  unsubscribe_handler = component "Unsubscribe Handler" { ... }
}

component extension.server "Components_Server" {
  include *
  autoLayout tb
}
```

Fixes #7

## [0.3.6] - 2025-12-14

### Fixed

#### Bug Fixes Found by Test Suite
- **Correct ts-morph API usage** - Fixed `Node.isTypePredicate()` call (was incorrectly using `Node.isTypePredicateNode()`)
- **Prevent duplicate handler detection** - Skip else-if statements when processing if statements (they're already handled by the chain walker)

### Added

#### Comprehensive Test Suite
- **7 automated tests** covering all type guard detection patterns
- Tests for local type guards, imported guards, .ts extensions, path aliases, else-if chains
- Prevents regressions like the v0.3.2-v0.3.5 cycle

This version actually works correctly. v0.3.5 had the right approach (AST-based detection) but had implementation bugs that were caught and fixed by the new test suite.

## [0.3.5] - 2025-12-14

### Deprecated

Had bugs in implementation (wrong API method, duplicate detection). Use v0.3.6 instead.

### Fixed

#### Use AST-Based Type Predicate Detection (The Actual Fix)
- **Check AST structure, not resolved types** - Use `getReturnTypeNode()` and `Node.isTypePredicateNode()` instead of `getReturnType().getText()`
- **Fixes imported type guard detection** - ts-morph returns `"boolean"` for type predicates when checking resolved types across files, but AST structure preserves the actual type predicate
- **Works for all import patterns** - Path aliases, relative imports, with or without `.ts` extensions

### The Real Problem

When resolving imported functions, ts-morph's type system simplifies type predicates to their structural equivalent:
```typescript
// Function signature:
function isQuery(msg: Request): msg is Query { ... }

// What we were checking (WRONG):
def.getReturnType().getText()  // Returns "boolean" ❌

// What we now check (CORRECT):
def.getReturnTypeNode()  // Returns TypePredicateNode ✅
Node.isTypePredicateNode(returnTypeNode)  // true ✅
```

### What Changed

Both `findTypePredicateFunctions()` (local) and `resolveImportedTypeGuard()` (imported) now use AST-based detection:

```typescript
const returnTypeNode = node.getReturnTypeNode()

if (returnTypeNode && Node.isTypePredicateNode(returnTypeNode)) {
  const typeNode = returnTypeNode.getTypeNode()
  const typeName = typeNode.getText()  // "QueryMessage" ✅
  const messageType = extractMessageTypeFromTypeName(typeName)  // "query"
}
```

This works because AST nodes preserve the actual syntax structure, while resolved types represent semantic equivalence.

Fixes #6

## [0.3.4] - 2025-12-14

### Deprecated

Attempted to fix with compiler options. The actual issue was checking resolved types instead of AST structure. Use v0.3.5 instead.

## [0.3.3] - 2025-12-14

### Deprecated

This version implemented a manual fallback for import resolution. Use v0.3.5 instead.

## [0.3.2] - 2025-12-13

### Added

#### Imported Type Guard Detection
- **Cross-file resolution** - Automatically follows imports using ts-morph symbol resolution
- **Path alias support** - Works with tsconfig path aliases (@ws/, @/, etc.)
- **Named imports** - Detects type guards from `import { isQuery } from './messages'`
- **Relative imports** - Handles `./` and `../` imports correctly
- **Performance optimized** - Local lookup first, import resolution as fallback
- **Graceful error handling** - Skips resolution failures silently

### Example Enhancement
```typescript
// Type guard defined in: packages/api/src/ws/messages.ts
export function isQueryMessage(msg: RequestMessage): msg is QueryMessage {
  return msg.type === 'query'
}

// Used in: packages/api/src/server.ts
import { isQueryMessage } from '@ws/messages'

if (isQueryMessage(message)) {
  handleQuery(message)  // ✅ NOW DETECTED!
}
```

### Benefits
- No manual import parsing required - ts-morph handles complexity
- Works with all import patterns automatically
- Backward compatible - existing code works identically
- Enables full handler detection for projects like Lingua CMS

Addresses #4

## [0.3.1] - 2025-12-13

### Added

#### TypeScript Type Guard Pattern Detection
- **Type predicate detection** - Automatically detects TypeScript type guard functions (`msg is QueryMessage`)
- **If/else-if chain support** - Handles message routing with if/else-if chains using type guards
- **Message type extraction** - Extracts message types from type names (e.g., `QueryMessage` → `query`)
- **Fallback analysis** - Analyzes function body when type name doesn't match pattern (`return msg.type === 'query'`)
- **Performance optimized** - WeakMap caching prevents redundant file scanning (O(n) instead of O(n²))
- **Works alongside existing patterns** - Compatible with switch/case, handler maps, and `.on()` detection

### Example Pattern Detected
```typescript
function isQueryMessage(msg: RequestMessage): msg is QueryMessage {
  return msg.type === 'query'
}

if (isQueryMessage(message)) {
  response = await handleQuery(message)
} else if (isCommandMessage(message)) {
  response = await handleCommand(message)
}
```

### Benefits
- Detects handlers in TypeScript projects using type guard patterns
- Common in well-typed codebases for type narrowing and IDE support
- Enables full handler detection for projects like Lingua CMS

### Limitations
- Only detects type guards defined in the same file (imported type guards require enhancement)
- Future versions may add cross-file type guard resolution

Addresses #2

## [0.3.0] - 2025-12-12

### Added

#### Phase 1: Manifest-Optional Architecture Visualization
- **Make manifest.json optional** - Polly Visualize now works without manifest.json for WebSocket servers, generic TypeScript projects, PWAs, and Electron apps
- **Auto-detect project type** from manifest.json, package.json, or tsconfig.json
- **Simple context naming** - Use "server/client" instead of "websocket-server/websocket-client"
- **Improved CLI messaging** - Shows detected project type (Chrome Extension vs auto-detect)
- **Updated help text** - Lists all supported project types

#### Phase 2: Enhanced WebSocket Detection
- **Content analysis** - Analyzes server files to detect frameworks without relying solely on package.json
- **Framework-specific detection** for Bun, Node ws, Socket.io, Elysia, Express, Fastify, Hono, Koa
- **Confidence scoring system** with 15+ regex patterns to find the best server entry point
- **Distinguish server types** - Automatically labels as "WebSocket Server" vs "HTTP Server"
- **Bun built-in WebSocket support** - Works even without dependencies in package.json

#### Phase 3: Generic Message Pattern Detection
- **Extended handler detection** - Supports 5 new handler patterns beyond `.on()`:
  - `addEventListener('message', handler)` for Web Workers
  - `switch(message.type) { case 'EVENT': ... }` router patterns
  - `const handlers = { 'EVENT': fn }` handler map patterns
  - `ws.on('event', handler)` WebSocket handlers
  - `socket.on('event', handler)` Socket.io handlers

- **Extended flow detection** - Supports 5 new sender patterns beyond `.send()`:
  - `ws.send(message)` WebSocket messages
  - `socket.emit('event', data)` Socket.io events
  - `postMessage(data)` Web Worker/Window messages
  - `window.postMessage(data)` cross-window communication
  - `client.send()` broadcast patterns

### Changed
- ManifestParser constructor now accepts optional parameter for graceful handling of missing manifest
- ArchitectureAnalyzer automatically uses project detector when manifest is missing
- findProjectRoot() in visualize CLI checks for manifest.json OR package.json OR tsconfig.json

### Testing
- Added 11 unit tests for ManifestParser with optional manifest handling
- Integration tested with Chrome extension examples (backward compatible)
- Integration tested with WebSocket servers (Node ws, Bun)
- Tested comprehensive message pattern detection (10 handlers detected across all patterns)

### Migration Guide
No breaking changes! This release is 100% backward compatible:
- Chrome extensions with manifest.json work identically
- No API changes required
- Existing visualizations generate the same output

To use new features:
1. Run `polly visualize` in WebSocket/generic projects without manifest.json
2. Message patterns are detected automatically (no config needed)
3. Server framework detection works out of the box

## [0.2.1] - 2025-11-11

### Fixed
- **Verification Tool**: Fixed MessageRouter.tla not being found during Docker verification
  - CLI now searches multiple locations for MessageRouter.tla template file
  - Added support for external polly directory installations (git submodules, monorepos)
  - Bundled MessageRouter.tla specs with the published package
  - Improved error messaging when MessageRouter.tla cannot be found

## [0.2.0] - Previous release

(Previous changelog entries would go here)
