#!/bin/sh
# bench2.sh CONFIG_DIR... : per config 3x TLC -workers 1, 3x TLC -workers auto, 3x Bun; all safety only.
D=$(cd "$(dirname "$0")" && pwd)
for c in "$@"; do
  for w in 1 auto; do for n in 1 2 3; do
    echo "## $c TLC-w$w run $n $(uptime | sed 's/.*load averages*: //')"
    "$D/tlc.sh" "$D/$c" $w 2>&1 | grep -E "^Error|states generated,|depth of|Finished in|memory.peak|^real"
  done; done
  for n in 1 2 3; do
    echo "## $c BUN run $n $(uptime | sed 's/.*load averages*: //')"
    /usr/bin/time -l bun "$D/check.ts" --spec "$D/$c" 2>&1 | grep -E "^Error|states generated|encoding|wall|real|maximum resident"
  done
done
echo "## DONE $(date +%T)"
