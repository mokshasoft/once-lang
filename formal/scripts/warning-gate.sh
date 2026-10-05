#!/usr/bin/env bash
# warning-gate.sh — the warnings ratchet (plan 0.109 S0), until `-W error` (S5).
#
# Agda reports warnings, it does not fail on them, and a warning has repeatedly been the
# ONLY signal of a real defect: a constructor captured as a pattern variable when a
# re-export went (`UnreachableClauses`, plan 0.92 §7), a `rewrite` that fires nothing
# because an implicit is unsolved (`RewritesNothing`), a moved name left in a `using` list
# (`ModuleDoesntExport`). This gate counts warnings per (module, warning) over the closure of
# the apex and the extracted compiler; a count may only go DOWN (then lower the baseline
# line), and a pair not in the baseline fails.
#
# Agda replays a module's stored warnings when it loads the module, so a warm check of the
# roots reports the whole closure — no cold build needed.
#
# Usage (from formal/):  scripts/warning-gate.sh [LOG]   (LOG: reuse a check log instead)
set -euo pipefail
cd "$(dirname "$0")/.."
baseline=scripts/warning-gate.baseline
log=${1:-}
if [[ -z $log ]]; then
  log=$(mktemp)
  for root in Once/Certified.agda Once/Compiler.agda; do
    scripts/agda-safe.sh agda MODULE=$root >> "$log" 2>&1
  done
fi
python3 - "$log" "$baseline" "$PWD/" <<'PY'
import sys,re,collections
log,base,pre=sys.argv[1],sys.argv[2],sys.argv[3]
t=open(log,errors='ignore').read()
locs=set(re.findall(r'^(\S+?\.agda):(\d+\.\d+-[\d.]+): warning: -W\[no\](\w+)',t,re.M))
cnt=collections.Counter((f.replace(pre,''),w) for f,_,w in locs)
allowed={}
for l in open(base):
    l=l.strip()
    if not l or l.startswith('#'): continue
    f,w,n=l.split(); allowed[(f,w)]=int(n)
bad=0
for k,n in sorted(cnt.items()):
    a=allowed.get(k,0)
    if n>a: print(f"warning-gate: {k[0]} {k[1]}: {n}, baseline allows {a}"); bad=1
    elif n<a: print(f"warning-gate: {k[0]} {k[1]} is down to {n} (baseline {a}) — lower its line")
for k,a in allowed.items():
    if k not in cnt and a>0: print(f"warning-gate: {k[0]} {k[1]} is down to 0 (baseline {a}) — delete its line")
print(f"warning-gate: {sum(cnt.values())} warnings in {len({f for f,_ in cnt})} modules")
if bad: print("warning-gate: FAIL — a new warning (plan 0.109)"); sys.exit(1)
print("warning-gate: OK")
PY
