# Recipes

A recipe answers a goal — *"I want to do X"* — with **one** opinionated,
end-to-end solution. Examples show APIs; recipes show "here's the one
correct way to achieve this".

| | Examples | Recipes |
|---|---|---|
| Question answered | "How does this API work?" | "I want to do X — what should I build?" |
| Voice | Descriptive | Prescriptive |
| Count per goal | Many approaches OK | One blessed approach |
| Completeness | Can be a fragment | Must be end-to-end deployable |
| Invites variation | Yes — study and adapt | No — copy and ship |

## Recipes

- [actions-driven-app](actions-driven-app/) — "I want a Polly app where
  all state mutation goes through typed action handlers." Demonstrates
  `createStore`, `createForm`, `<ActionForm>`, `<TextInput>`,
  `<ActionInput>`, `<Modal>`, `<Toast>`, and `$persistedState` end to end.

Further recipes covering specific deployment shapes (Cloudflare Pages +
Worker signalling, Raspberry Pi mesh peer) are tracked in issue #49.
