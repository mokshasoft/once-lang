#!/usr/bin/env bash
# knot-seq.sh MOD... — type-check Knot modules ONE PER PROCESS, in the order
# given (give them in dependency order), stopping at the first failure.
# Logs: /tmp/k-<MOD>.log; timings appended to /tmp/knot-times.txt.
# One module per process on purpose: one agda process rechecking a chain of
# modules accumulates memory and is OOM-killed at check.sh's cgroup cap.
# rc=143 = killed (OOM/contention), NOT a type error: rerun from that module.
cd "$(dirname "$0")/../.."   # bootstrap/
for m in "$@"; do
  if /usr/bin/time -f "$m %e s %M KB" -a -o /tmp/knot-times.txt \
       env AGDA_RTS="${AGDA_RTS:--A64m -c}" ./check.sh "DirectedHoTT/Examples/Knot/$m.agda" > "/tmp/k-$m.log" 2>&1; then
    echo "$m ok"
  else
    rc=$?; echo "$m FAILED (rc=$rc)"; grep -n "error" -A25 "/tmp/k-$m.log" | head -50; exit 1
  fi
done
