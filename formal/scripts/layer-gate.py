#!/usr/bin/env python3
# layer-gate.py — the back end does not depend on the front end (plan 0.152 B).
#
# The back end (code generator, machines, targets, their correctness) and the Spec's
# type and semantics parts are about types and meanings; the surface language
# (expressions, declarations, the parser, the type checker, the printer) is the
# front end. A back-end module whose import closure reaches a front-end module is
# rebuilt whenever the surface language changes, and carries the surface's
# interfaces into memory wherever it is checked.
#
# Ratchet: scripts/layer-gate.baseline lists the back-end modules that reach the
# front end today; a module may only leave that list. A module not listed that
# reaches the front end fails the gate, with the path it reaches it by.
#
# Usage (from formal/):  scripts/layer-gate.py [--write-baseline]
import os, re, sys
from collections import deque

os.chdir(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))

FRONT = ['Once.Spec.Surface', 'Once.Spec.Source', 'Once.Parser', 'Once.TypeCheck',
         'Once.Surface', 'Once.Grammar', 'Once.Format']
BACK = ['Once.CCC', 'Once.Arith', 'Once.Memory', 'Once.Semantics', 'Once.IR', 'Once.IRTy',
        'Once.Target', 'Once.Allocator', 'Once.Adequacy.ArchCorrectness', 'Once.Adequacy.CPU',
        'Once.Spec.Type', 'Once.Spec.Core', 'Once.Spec.Effect', 'Once.Spec.Domain',
        'Once.Spec.Float', 'Once.Spec.Word', 'Once.Spec.Trace', 'Once.Spec.Observation',
        'Once.Spec.Numerics', 'Once.Spec.Grade', 'Once.Spec.Polynomial', 'Once.Spec.Boundary',
        'Once.Spec.Delay', 'Once.Spec.ABI']
# the surface modules whose dependents the gate reports (what a surface change rebuilds)
WATCH = ['Once.Spec.Surface.Syntax', 'Once.Spec.Surface.Generators', 'Once.Spec.Float.Decimal']

def under(m, prefixes):
    return any(m == p or m.startswith(p + '.') for p in prefixes)

IMP = re.compile(r'^\s*(?:open\s+)?import\s+(Once\.[^\s;()]+)', re.M)
deps = {}
for root, _, files in os.walk('Once'):
    for f in files:
        if f.endswith('.agda'):
            p = os.path.join(root, f)
            deps[p[:-5].replace('/', '.')] = set(IMP.findall(open(p, encoding='utf-8').read()))

def reach(m):
    """the first front-end module m's closure reaches, with the path, or None"""
    prev = {m: None}; q = deque([m])
    while q:
        x = q.popleft()
        for d in sorted(deps.get(x, ())):
            if d in prev: continue
            prev[d] = x
            if under(d, FRONT):
                path = [d]
                while prev[path[-1]] is not None: path.append(prev[path[-1]])
                return list(reversed(path))
            q.append(d)
    return None

back = sorted(m for m in deps if under(m, BACK) and not under(m, FRONT))
bad = {m: reach(m) for m in back}
bad = {m: p for m, p in bad.items() if p}

baseline_f = 'scripts/layer-gate.baseline'
if '--write-baseline' in sys.argv:
    with open(baseline_f, 'w') as f:
        f.write('# layer-gate baseline (plan 0.152 B): back-end modules whose import closure reaches the\n'
                '# front end. A module may only leave this list (scripts/layer-gate.py).\n')
        f.write(''.join(m + '\n' for m in sorted(bad)))
    print(f'layer-gate: baseline written, {len(bad)} of {len(back)} back-end modules')
    sys.exit(0)

allowed = {l.strip() for l in open(baseline_f) if l.strip() and not l.startswith('#')}
new = sorted(m for m in bad if m not in allowed)
gone = sorted(m for m in allowed if m not in bad)
for m in new:
    print(f'layer-gate: {m} reaches the front end: ' + ' → '.join(bad[m]))
for m in gone:
    print(f'layer-gate: {m} no longer reaches the front end — remove it from {baseline_f}')
rdeps = {}
for m, ds in deps.items():
    for d in ds: rdeps.setdefault(d, set()).add(m)
def dependents(m):
    seen = set(); q = deque([m])
    while q:
        for y in rdeps.get(q.popleft(), ()):
            if y not in seen: seen.add(y); q.append(y)
    return len(seen)
print(f'layer-gate: {len(bad)} of {len(back)} back-end modules reach the front end (baseline {len(allowed)})')
print('layer-gate: dependents: ' + ', '.join(f'{w} {dependents(w)}' for w in WATCH))
if new:
    print('layer-gate: FAIL — a back-end module newly reaches the front end (plan 0.152 B)')
    sys.exit(1)
print('layer-gate: OK')
