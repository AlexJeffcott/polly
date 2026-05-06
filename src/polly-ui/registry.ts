/**
 * Public registry surface for `@fairfox/polly/ui`.
 *
 * The actual data is generated from polly-ui's canonical sources by
 * `scripts/build-polly-ui-registry.ts` into `registry.generated.ts`.
 * This file pins the public re-export so the generator can refresh
 * `registry.generated.ts` without changing the import path consumers
 * use.
 *
 * Tokens and components are exposed as `readonly` arrays. Adding a
 * token to `theme.css` (or a component to `index.ts`) shows up here
 * after the next `bun run build:lib` pass; the surface is intended as
 * the source of truth for downstream conformance checks like
 * `polly-ui:css-vars` and `polly-ui:shared-components`.
 */

export {
  type PollyUiComponent,
  type PollyUiToken,
  type PollyUiTokenCategory,
  pollyUiComponents,
  pollyUiTokens,
} from "./registry.generated";
