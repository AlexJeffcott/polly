#!/bin/sh
# compare.sh : run TLC and the Bun checker, safety only, on examples/minimal's
# generated spec and compare generated / distinct / depth. Exit 0 when all three
# match.
#
# Needs: Docker, polly-tla:latest, and the generated spec. `polly verify` in
# examples/minimal writes it to specs/tla/generated.
set -eu
D=$(cd "$(dirname "$0")" && pwd)
SRC="$D/../../../../../examples/minimal/specs/tla/generated"
[ -f "$SRC/UserApp.tla" ] || { echo "no spec at $SRC: run polly verify in examples/minimal" >&2; exit 2; }

W=$(mktemp -d)
trap 'rm -rf "$W"' EXIT
cp "$SRC"/UserApp.tla "$SRC"/UserApp.cfg "$SRC"/MessageRouter.tla "$W"/
# Safety only: drop the PROPERTIES block (the checker has no liveness).
awk '/^\\\* Temporal properties/{skip=1; next} skip && /^PROPERTIES/{next} skip && /^  /{next} {skip=0; print}' \
  "$SRC/UserApp.cfg" > "$W/UserApp.cfg"

TLC=$("$D/tlc.sh" "$W" auto 2>&1)
BUN=$(bun "$D/check.ts" --spec "$W" 2>&1)
echo "$TLC" | grep -E "states generated,|depth of|Finished in|memory.peak"
echo "$BUN" | grep -E "states generated|wall"

t=$(echo "$TLC" | sed -nE 's/^([0-9]+) states generated, ([0-9]+) distinct.*/\1 \2/p')
td=$(echo "$TLC" | sed -nE 's/^The depth of the complete state graph search is ([0-9]+).*/\1/p')
b=$(echo "$BUN" | sed -nE 's/^([0-9]+) states generated, ([0-9]+) distinct states found, depth ([0-9]+).*/\1 \2 \3/p')

if [ -n "$t" ] && [ "$t $td" = "$b" ]; then
  echo "MATCH generated distinct depth: $b"
else
  echo "DIFFER  TLC: $t $td  Bun: $b" >&2
  exit 1
fi
