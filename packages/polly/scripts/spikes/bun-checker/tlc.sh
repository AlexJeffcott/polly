#!/bin/sh
# tlc.sh DIR WORKERS [extra TLC flags...]  -- runs TLC the way polly's runner does (docker.ts ~L220),
# with sh as entrypoint only so the container cgroup's memory.peak can be printed afterwards.
D=$(cd "$1" && pwd); W=$2; shift 2
cd "$D" && /usr/bin/time -p docker run --rm --memory 4g -e JAVA_TOOL_OPTIONS="-Xmx3072m -XX:+UseParallelGC" -v "$D:/work" --entrypoint sh polly-tla:latest \
  -c "polly-tla-entrypoint tlc -workers $W -cleanup -metadir /tmp/states $* UserApp.tla; echo \"cgroup memory.peak \$(cat /sys/fs/cgroup/memory.peak)\""
