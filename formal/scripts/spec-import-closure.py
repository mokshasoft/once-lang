#!/usr/bin/env python3
# spec-import-closure.py — the FULL import closure of Once.Spec (plan 0.114 §8).
#
# spec-closure.py lists the Spec's `public` re-export closure: what the Spec
# exports. This lists everything the Spec IMPORTS, transitively. For each
# compiler-side module that is reachable, it prints the import chain back to
# Once.Spec, and it lists the edges by which public-closure modules leave the
# closure.
#
# Usage (from the repo root):  python3 formal/scripts/spec-import-closure.py
import collections, os, re, subprocess, sys

os.chdir(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
IMP = re.compile(r'^\s*(?:open\s+)?import\s+(Once[\w.\-]*)', re.M)
TARGETS = ['Once.Compile', 'Once.Parser', 'Once.IR', 'Once.Semantics.Machine',
           'Once.Arith.SigOp.Builders', 'Once.TypeCheck.Classify']

def deps(m):
    p = m.replace('.', '/') + '.agda'
    if not os.path.exists(p):
        return []
    src = re.sub(r'\{-.*?-\}', '', open(p).read(), flags=re.S)
    src = re.sub(r'--.*', '', src)
    return sorted(set(IMP.findall(src)))

closure = subprocess.run([sys.executable, 'formal/scripts/spec-closure.py'], cwd='..',
                         capture_output=True, text=True, check=True).stdout.split()
public = {f.removeprefix('formal/').removesuffix('.agda').replace('/', '.') for f in closure}

parent = {'Once.Spec': None}
queue = collections.deque(['Once.Spec'])
while queue:
    m = queue.popleft()
    for d in deps(m):
        if d not in parent:
            parent[d] = m
            queue.append(d)

print(f'full import closure: {len(parent)} modules; public closure: {len(public)}')
for t in TARGETS:
    if t in parent:
        chain, c = [], t
        while c:
            chain.append(c); c = parent[c]
        print('reaches  ' + ' <- '.join(chain))
print('edges leaving the public closure:')
for m in sorted(public):
    out = [d for d in deps(m) if d not in public]
    if out:
        print(f'  {m} -> {" ".join(out)}')
