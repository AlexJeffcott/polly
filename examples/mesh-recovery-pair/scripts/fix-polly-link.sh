#!/usr/bin/env bash
# bun's `link:../..` protocol sometimes resolves @fairfox/polly to a
# stale path in ~/.bun/install rather than the workspace root. The
# verifier needs the link to point at the workspace source tree to
# resolve `@fairfox/polly/verify` from specs/verification.config.ts;
# this script forces it into the correct shape.
set -euo pipefail

cd "$(dirname "$0")/.."

LINK_PATH="node_modules/@fairfox/polly"
EXPECTED_TARGET="../../../.."

if [[ ! -L "$LINK_PATH" ]] || [[ "$(readlink "$LINK_PATH")" != "$EXPECTED_TARGET" ]]; then
  rm -rf "$LINK_PATH"
  ln -s "$EXPECTED_TARGET" "$LINK_PATH"
fi
