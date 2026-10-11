#!/usr/bin/env python3
# spec-import-closure.py — the FULL import closure of Once.Spec, and its gate
# (plan 0.114).
#
# spec-closure.py lists the Spec's `public` re-export closure: what the Spec
# EXPORTS. This script follows every import: what the Spec DEPENDS ON. The
# goal (plan 0.114) is that this is `Once.Spec.*` plus the standard library,
# with no re-export of an implementation module and no `public` without a
# `using` list.
#
#   python3 formal/scripts/spec-import-closure.py          report: size, the
#       import chain to each compiler target, the edges out of the public closure
#   python3 formal/scripts/spec-import-closure.py --gate   the ratchet
#       (`make spec-gate`): fail on anything not in spec-gate.baseline, and on
#       a baseline line that no longer applies (the baseline only shrinks)
import collections, os, re, subprocess, sys

FORMAL = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..')
os.chdir(FORMAL)
BASELINE = 'scripts/spec-gate.baseline'
IMP = re.compile(r'^\s*(?:open\s+)?import\s+(Once[\w.\-]*)', re.M)
TARGETS = ['Once.Compile', 'Once.Parser', 'Once.IR', 'Once.Semantics.Machine',
           'Once.Arith.SigOp.Builders', 'Once.TypeCheck.Classify']

def is_spec(m):
    return m == 'Once.Spec' or m.startswith('Once.Spec.')

def source(m):
    p = m.replace('.', '/') + '.agda'
    if not os.path.exists(p):
        return None
    s = re.sub(r'\{-.*?-\}', '', open(p).read(), flags=re.S)
    return re.sub(r'--.*', '', s)

def deps(m):
    s = source(m)
    return sorted(set(IMP.findall(s))) if s else []

def reexports(m):
    """(target, has_using) for each `open import T … public` statement in m.
    A statement runs on over the following more-indented lines."""
    s = source(m)
    if not s:
        return []
    lines, out, i = s.split('\n'), [], 0
    while i < len(lines):
        mm = re.match(r'^(\s*)open\s+import\s+(Once[\w.\-]*)(.*)$', lines[i])
        if not mm:
            i += 1; continue
        ind, stmt, i = len(mm.group(1)), mm.group(3), i + 1
        while i < len(lines) and lines[i].strip() and \
                len(lines[i]) - len(lines[i].lstrip()) > ind:
            stmt += ' ' + lines[i]; i += 1
        if re.search(r'\bpublic\b', stmt):
            out.append((mm.group(2), bool(re.search(r'\busing\b', stmt))))
    return out

def closure():
    parent, queue = {'Once.Spec': None}, collections.deque(['Once.Spec'])
    while queue:
        m = queue.popleft()
        for d in deps(m):
            if d not in parent:
                parent[d] = m
                queue.append(d)
    return parent

def findings(parent):
    """What the goal forbids, as baseline lines."""
    out = set()
    for m in parent:
        if not is_spec(m):
            out.add(f'import {m}')
        for t, has_using in reexports(m):
            if not is_spec(t):
                out.add(f'reexport-impl {m} {t}')
            if not has_using:
                out.add(f'reexport-wholesale {m} {t}')
    return out

def report(parent):
    out = subprocess.run([sys.executable, 'formal/scripts/spec-closure.py'], cwd='..',
                         capture_output=True, text=True, check=True).stdout.split()
    public = {f.removeprefix('formal/').removesuffix('.agda').replace('/', '.') for f in out}
    print(f'full import closure: {len(parent)} modules ({sum(not is_spec(m) for m in parent)} '
          f'outside Once.Spec.*); public closure: {len(public)}')
    for t in TARGETS:
        if t in parent:
            chain, c = [], t
            while c:
                chain.append(c); c = parent[c]
            print('reaches  ' + ' <- '.join(chain))
    print('edges leaving the public closure:')
    for m in sorted(public):
        e = [d for d in deps(m) if d not in public]
        if e:
            print(f'  {m} -> {" ".join(e)}')

def gate(parent):
    base = set()
    for line in open(BASELINE):
        line = line.split('#')[0].strip()
        if line:
            base.add(' '.join(line.split()))
    now = findings(parent)
    new, stale = sorted(now - base), sorted(base - now)
    for f in new:
        print(f'spec-gate: NEW  {f}')
    for f in stale:
        print(f'spec-gate: GONE {f} — delete its line from {BASELINE}')
    kinds = collections.Counter(f.split()[0] for f in now)
    print(f'spec-gate: {len(parent)} modules in the import closure of Once.Spec; '
          + ', '.join(f'{k} {v}' for k, v in sorted(kinds.items())))
    if new or stale:
        print('spec-gate: FAIL (plan 0.114: the Spec imports only the Spec)')
        sys.exit(1)
    print('spec-gate: OK')

parent = closure()
if '--gate' in sys.argv:
    gate(parent)
elif '--write-baseline' in sys.argv:
    with open(BASELINE, 'w') as f:
        f.write('# spec-gate baseline (plan 0.114): what the Spec still imports or re-exports\n'
                '# beyond itself. Lines may only be DELETED. `import M`: M is in the full\n'
                '# import closure of Once.Spec but outside Once.Spec.*. `reexport-impl A B`:\n'
                '# A re-exports an implementation module. `reexport-wholesale A B`: A\n'
                '# re-exports B with no `using` list.\n')
        for line in sorted(findings(parent)):
            f.write(line + '\n')
else:
    report(parent)
