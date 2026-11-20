#!/usr/bin/env python3
# SPDX-License-Identifier: AGPL-3.0-or-later
# Copyright (C) 2025-2026 Jonas Claesson
"""check-cone.py — type-check a root's import cone one module per Agda process,
leaves first (plan 0.152 E).

A process that checks one module holds the interfaces of that module's imports
and one module's worth of new work. A process that checks the whole cone holds
everything it has checked so far, and on this machine that does not fit in the
memory two sessions can share. After this pass every interface below the root
is fresh, so the root's own run (the apex, the AST dump) only loads them.

A module is skipped when its interface is at least as new as its source and as
every in-tree import's interface. A module Agda found up to date without
rewriting its interface gets its interface touched, so it is skipped next time.

Usage:  check-cone.py [--dir DIR] ROOT.agda... -- AGDA-COMMAND...
  DIR            the tree the paths are relative to (default: the current directory)
  ROOT.agda      the roots; their cones are checked, the roots themselves are not
  AGDA-COMMAND   the command that checks one module; the module's path is appended
"""
import glob, os, re, subprocess, sys, time

IMP = re.compile(r'^\s*(?:open\s+)?import\s+([A-Za-z][^\s;()]*)', re.M)
COMMENT = re.compile(r'\{-.*?-\}', re.S)


def main(argv):
    if '--' not in argv:
        sys.exit(__doc__)
    i = argv.index('--')
    args, cmd = argv[:i], argv[i + 1:]
    d = '.'
    if args[:1] == ['--dir']:
        d, args = args[1], args[2:]
    if not args or not cmd:
        sys.exit(__doc__)
    os.chdir(d)

    def path(m): return m.replace('.', '/') + '.agda'

    imports = {}

    def deps(m):
        if m not in imports:
            src = COMMENT.sub('', open(path(m), encoding='utf-8').read())
            src = re.sub(r'--.*', '', src)
            imports[m] = sorted({x for x in IMP.findall(src) if os.path.isfile(path(x))})
        return imports[m]

    # leaves first: depth-first post-order from the roots
    roots = [r[:-len('.agda')].replace('/', '.') for r in args]
    order, seen = [], set()
    for r in roots:
        stack = [(r, iter(deps(r)))]
        seen.add(r)
        while stack:
            m, it = stack[-1]
            nxt = next(it, None)
            if nxt is None:
                stack.pop()
                order.append(m)
            elif nxt not in seen:
                seen.add(nxt)
                stack.append((nxt, iter(deps(nxt))))
    cone = [m for m in order if m not in roots]

    def iface(m):
        vd = glob.glob('_build/*/agda')
        return os.path.join(vd[0], m.replace('.', '/') + '.agdai') if vd else None

    def mtime(p):
        try:
            return os.stat(p).st_mtime
        except (OSError, TypeError):
            return None

    def fresh(m):
        t = mtime(iface(m))
        if t is None or t < os.stat(path(m)).st_mtime:
            return False
        return all((mtime(iface(x)) or float('inf')) <= t for x in deps(m))

    todo = [m for m in cone if not fresh(m)]
    print(f'check-cone: {len(cone)} modules below {", ".join(roots)}, '
          f'{len(cone) - len(todo)} up to date', flush=True)
    t0 = time.time()
    for k, m in enumerate(cone, 1):
        if fresh(m):
            continue
        t = time.time()
        r = subprocess.run(cmd + [path(m)], stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
        if r.returncode != 0:
            print(f'check-cone: {m} FAILED (rc={r.returncode}):')
            print('\n'.join(l for l in r.stdout.splitlines() if not l.lstrip().startswith('Checking'))[-4000:])
            sys.exit(1)
        if mtime(iface(m)) is not None:
            os.utime(iface(m))
        print(f'check-cone: [{k}/{len(cone)}] {m} {time.time() - t:.0f}s', flush=True)
    print(f'check-cone: done, {len(todo)} checked in {(time.time() - t0) / 60:.1f} min', flush=True)


if __name__ == '__main__':
    main(sys.argv[1:])
