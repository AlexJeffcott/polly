# Recipes

A recipe answers a goal — *"I want to do X"* — with one opinionated,
narrated path to get there. Each recipe is a single Markdown file that
reads as a code-along: enough prose to explain the shape, small
snippets at the points where a novice would get stuck, reader work for
everything that is not the focus.

| | Examples | Recipes | Docs |
|---|---|---|---|
| Question answered | "How does this API work?" | "I want to do X — what should I build?" | "What does this primitive do?" |
| Shape | Full runnable source | Narrated guide with focused snippets | Reference per primitive |
| Voice | Descriptive | Prescriptive | Reference |
| Count per goal | Many approaches OK | One blessed path | One entry per primitive |
| Invites variation | Yes — study and adapt | No — the guide has chosen | No — documents what is |

A recipe is **not** a full implementation you copy. The working code
lives in the reader's project, on top of the patterns the recipe
sketches. What the recipe promises is that following the guide to the
end lands you on a shape that is known to work, without painting you
into a corner on the decisions Polly cannot make for you.

A recipe is **not** a tutorial. It assumes you know Polly's primitives
well enough to read `$meshState` without a glossary. If you need that,
start with the `docs/` reference.

A recipe is **not** many approaches to the same goal. When a better
path emerges, the recipe is rewritten, not supplemented.

## Current recipes

- [**actions-driven-app**](actions-driven-app.md) — *I want a Polly
  app where every state mutation flows through typed action handlers
  and components stay logic-free.* The three-layer split (event
  delegation, action registry, stores) walked through with focused
  snippets for each layer.

- [**mesh-only-cloudflare**](mesh-only-cloudflare.md) — *I want to
  deploy a Polly mesh app on a free Cloudflare tier.* A signalling
  Worker with one Durable Object for the peer map, Pages for static
  hosting, the client wired against both. Free tier comfortably
  covers a small team.

- [**mesh-pi-peer**](mesh-pi-peer.md) — *I want a Raspberry Pi to
  participate as a trusted always-on peer on my Polly mesh.* Bun,
  werift, a file-backed keyring, a file-backed Automerge-Repo
  storage adapter, and a systemd unit that runs the peer forever.

## Proposing a recipe

Open an issue describing the goal in the user's voice ("I want
to…"). If the goal is reachable in one opinionated way on top of
Polly's current primitives, it is a recipe. If the goal needs a
feature that does not exist yet, it is a feature request; the recipe
comes after the feature lands.
