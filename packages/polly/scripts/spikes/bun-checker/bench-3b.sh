#!/bin/sh
# bench-3b.sh : TLC (-workers auto, as polly's runner) against the Bun checker
# (compiled engine) on each generated spec set, safety only. Runs alternate
# TLC, Bun, TLC, Bun, ... ROUNDS times. Prints wall time (`real`) and peak
# memory: the container's memory.peak for TLC, max RSS for Bun.
#
# Needs: Docker, polly-tla:latest, and `polly verify` run in each example.
set -eu
D=$(cd "$(dirname "$0")" && pwd)
EX="$D/../../../../../examples"
ROUNDS=${ROUNDS:-3}
SETS="full-featured minimal mesh-recovery-pair todo-list/auth todo-list/preferences todo-list/todos"

for set in $SETS; do
  case $set in
    todo-list/*) src="$EX/todo-list/specs/tla/generated/${set#todo-list/}" ;;
    *) src="$EX/$set/specs/tla/generated" ;;
  esac
  W=$(mktemp -d)
  cp "$src"/*.tla "$W"/
  rm -f "$W"/Witness_*
  cfg=$(ls "$src"/*.cfg | grep -v Witness_)
  awk '/^PROPERTIES/{skip=1; next} skip && /^[ \t]+[^ \t]/{next} {skip=0; print}' "$cfg" > "$W/$(basename "$cfg")"
  module=$(basename "$cfg" .cfg)
  i=0
  while [ $i -lt "$ROUNDS" ]; do
    t=$(cd "$W" && /usr/bin/time -p docker run --rm --memory 4g -e JAVA_TOOL_OPTIONS="-Xmx3072m -XX:+UseParallelGC" -v "$W:/work" --entrypoint sh polly-tla:latest \
      -c "polly-tla-entrypoint tlc -workers auto -cleanup -metadir /tmp/states $module.tla; echo \"peak \$(cat /sys/fs/cgroup/memory.peak)\"" 2>&1)
    tr=$(echo "$t" | sed -nE 's/^real ([0-9.]+)/\1/p')
    tm=$(echo "$t" | sed -nE 's/^peak ([0-9]+)/\1/p')
    tc=$(echo "$t" | sed -nE 's/^([0-9]+) states generated, ([0-9]+) distinct.*/\1 \2/p')
    b=$(/usr/bin/time -l bun "$D/../../../tools/verify/src/checker/cli.ts" --spec "$W" 2>&1)
    br=$(echo "$b" | sed -nE 's/^ *([0-9.]+) real.*/\1/p')
    bm=$(echo "$b" | sed -nE 's/^ *([0-9]+) +maximum resident set size/\1/p')
    bc=$(echo "$b" | sed -nE 's/^([0-9]+) states generated, ([0-9]+) distinct.*/\1 \2/p')
    printf '%s\tTLC %s s %s MB [%s]\tBun %s s %s MB [%s]\n' "$set" "$tr" "$((tm / 1048576))" "$tc" "$br" "$((bm / 1048576))" "$bc"
    i=$((i + 1))
  done
  rm -rf "$W"
done
