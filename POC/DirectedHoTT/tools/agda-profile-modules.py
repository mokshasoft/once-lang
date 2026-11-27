#!/usr/bin/env python3
# SPDX-License-Identifier: AGPL-3.0-or-later
# Copyright (C) 2025-2026 Jonas Claesson
"""agda-profile-modules.py — what each POC module costs to type-check: wall time
and peak memory, ONE MODULE PER AGDA PROCESS, leaves first.

Ported from master's `formal/scripts/agda-profile.py` (branch
`0.146-linear-core-4`), which took the design from this POC's `sweep.sh`
("one module per process"). Not to be confused with `tools/agda-profile.sh`,
which profiles DEFINITIONS inside one module with the patched Agda.

When every import already has its interface, the process checking a module
loads those interfaces and type-checks ONE module's worth of new work, so its
peak measures that module (plus loading its closure, which every build pays
too), not whatever was checked before it in the same process.

Every module is REALLY checked: the POC tree is staged from a committed ref into
a work directory with an empty `_build` (`git archive`), so a cached interface
can never pass for a measurement. Your own `POC/_build` is never touched.

Usage (from anywhere in the repo):
    POC/DirectedHoTT/tools/agda-profile-modules.py [--ref REF] [--root MOD.agda]... [--work DIR]
    POC/DirectedHoTT/tools/agda-profile-modules.py --report [--top N] [--work DIR]

  --ref REF      the committed tree to measure (default HEAD)
  --root M.agda  measure only M's import cone, as a path under POC/ (repeatable;
                 default: every module the sweep builds, i.e. DirectedHoTT/ minus
                 Negative/)
  --work DIR     staging + results (default ~/.cache/once-lang5-profile-modules/<ref>)
  --report       print the worst offenders from an existing results file
  --top N        how many to list (default 25)
  --no-wait      check beside another agda process instead of waiting for it

Environment:
  PROFILE_MEM_MAX  cgroup memory cap per module (default 5500M, as check.sh)
  PROFILE_SWAP_MAX cgroup swap cap (default 2G)
  PROFILE_RTS      base RTS flags (default -A64m, as check.sh)

Results: <work>/profile.tsv, one row per module, appended as it goes (follow it
with `tail -f`). A rerun RESUMES: a module whose row is `ok` with the same key
(sha256 of its source and its in-tree imports' keys) is not checked again.

Memory: each module first runs at PROFILE_RTS under a heap limit just below the
cgroup cap; if it runs out it is retried with the compacting collector (`-c`),
then reported OOM. Modules that import an OOM or failed module are reported
`blocked`. The rung that worked is recorded: a module that needs `-c` is itself
a finding.

Contention: if another agda process is running (another session), the profiler
WAITS for it before starting each module, and logs that it waited. Two Agda
processes at once on this machine distort every number (and kill each other).
"""
import glob, hashlib, os, re, shutil, subprocess, sys, time

REPO = os.path.dirname(os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))
HOME = os.path.expanduser('~')
SUB = 'POC'                       # the subtree staged and checked
MODRE = r'^\s*(?:open\s+)?import\s+((?:DirectedHoTT|tmp)[\w.\-′ᵢⁿᵗ]*)'

FIELDS = ['module', 'status', 'rung', 'wall_s', 'maxrss_mb', 'residency_mb', 'alloc_gb',
          'gc_s', 'checked', 'closure', 'lines', 'key']


def modpath(m): return m.replace('.', '/') + '.agda'


def imports(root, m):
    p = os.path.join(root, modpath(m))
    if not os.path.exists(p): return []
    s = re.sub(r'--[^\n]*', '', open(p, encoding='utf-8').read())
    return sorted({d for d in re.findall(MODRE, s, re.M)
                   if os.path.exists(os.path.join(root, modpath(d)))})


def all_modules(root):
    """What the sweep builds: DirectedHoTT/ minus Negative/ (refuted results, never built)."""
    mods = []
    for d, _, fs in os.walk(os.path.join(root, 'DirectedHoTT')):
        if '/Negative' in d or '_build' in d: continue
        for f in fs:
            if f.endswith('.agda'):
                rel = os.path.relpath(os.path.join(d, f), root)
                mods.append(rel[:-5].replace('/', '.'))
    return sorted(mods)


def cone(root, roots):
    order, seen = [], set()
    sys.setrecursionlimit(20000)
    def visit(m):
        if m in seen: return
        seen.add(m)
        for d in imports(root, m): visit(d)
        order.append(m)
    for r in roots: visit(r)
    return order


def toposort(root, mods):
    """Leaves first; ties by name so the order is reproducible."""
    deps = {m: [d for d in imports(root, m) if d in mods] for m in mods}
    order, seen = [], set()
    sys.setrecursionlimit(20000)
    def visit(m):
        if m in seen: return
        seen.add(m)
        for d in deps[m]: visit(d)
        order.append(m)
    for m in sorted(mods): visit(m)
    return order, deps


def agda_id():
    path = shutil.which('agda') or 'agda'
    ver = subprocess.run([path, '--version'], capture_output=True, text=True).stdout.splitlines()[:1]
    return os.path.realpath(path) + ' ' + ' '.join(ver)


def other_agda(mine):
    """PIDs of agda processes that are not ours (another session's build)."""
    out = subprocess.run(['pgrep', '-x', 'agda'], capture_output=True, text=True).stdout.split()
    return [p for p in out if p not in mine]


def stage(ref, work):
    tree = os.path.join(work, 'tree')
    stamp = os.path.join(work, 'staged-ref')
    sha = subprocess.run(['git', '-C', REPO, 'rev-parse', ref], capture_output=True, text=True,
                         check=True).stdout.strip()
    if os.path.exists(stamp) and open(stamp).read().strip() == sha:
        return os.path.join(tree, SUB), sha, True
    # A new ref is extracted OVER the old tree, keeping `_build`: Agda keys interfaces by source
    # hash, so unchanged modules stay built, and their rows stay valid (same key). Old sources are
    # removed first so a deleted module cannot linger. Wipe the work directory to start cold.
    src = os.path.join(tree, SUB)
    if os.path.isdir(src):
        for d, _, fs in os.walk(src):
            if '_build' in d.split(os.sep): continue
            for f in fs:
                if f.endswith('.agda'): os.remove(os.path.join(d, f))
    os.makedirs(tree, exist_ok=True)
    a = subprocess.Popen(['git', '-C', REPO, 'archive', sha, SUB], stdout=subprocess.PIPE)
    subprocess.run(['tar', '-x', '-C', tree], stdin=a.stdout, check=True)
    a.wait()
    open(stamp, 'w').write(sha + '\n')
    return os.path.join(tree, SUB), sha, False


def mb(s): return f'{int(s) / 1048576:.0f}'


def parse_stats(path):
    r = {}
    try: txt = open(path, encoding='utf-8', errors='replace').read()
    except OSError: return r
    m = re.search(r'([\d,]+) bytes allocated in the heap', txt)
    if m: r['alloc_gb'] = f"{int(m.group(1).replace(',', '')) / 2**30:.1f}"
    m = re.search(r'([\d,]+) bytes maximum residency', txt)
    if m: r['residency_mb'] = mb(m.group(1).replace(',', ''))
    m = re.search(r'GC\s+time\s+([\d.]+)s', txt)
    if m: r['gc_s'] = f'{float(m.group(1)):.0f}'
    return r


def run_one(froot, lib, m, logdir, rung):
    mem = os.environ.get('PROFILE_MEM_MAX', '5500M')
    swap = os.environ.get('PROFILE_SWAP_MAX', '2G')
    base = os.environ.get('PROFILE_RTS', '-A64m')
    cap = int(mem[:-1]) * (1024 if mem[-1] in 'Gg' else 1) if mem[-1] in 'GgMm' else 5500
    stats = os.path.join(logdir, m + '.stats')
    timef = os.path.join(logdir, m + '.time')
    log = os.path.join(logdir, m + '.log')
    rts = f'{base} -M{cap - 600}m -s{stats}' + (' -c' if rung == 'c' else '')
    env = dict(os.environ, GHCRTS=rts)
    env.pop('AGDA_DIR', None)
    # The module itself is always checked from scratch: an interface left by a manual check in
    # the work tree would otherwise be loaded, and the row would record the load, not the check.
    for agdai in glob.glob(os.path.join(froot, '_build', '*', 'agda', modpath(m)[:-len('.agda')] + '.agdai')):
        os.remove(agdai)
    cmd = ['systemd-run', '--user', '--scope', '--quiet', '-p', f'MemoryMax={mem}',
           '-p', f'MemorySwapMax={swap}', '--',
           '/usr/bin/time', '-o', timef, '-f', '%e %M',
           'agda', f'--library-file={lib}', modpath(m)]
    with open(log, 'w') as lf:
        rc = subprocess.run(cmd, cwd=froot, env=env, stdout=lf, stderr=subprocess.STDOUT).returncode
    wall, rss = '', ''
    try:
        for line in open(timef):
            parts = line.split()
            if len(parts) == 2 and re.match(r'^[\d.]+$', parts[0]):
                wall, rss = f'{float(parts[0]):.0f}', f'{int(parts[1]) / 1024:.0f}'
    except OSError: pass
    txt = open(log, encoding='utf-8', errors='replace').read()
    oom = rc in (137, 251) or 'Heap exhausted' in txt
    checked = len(re.findall(r'^\s*Checking ', txt, re.M))
    r = dict(parse_stats(stats), wall_s=wall, maxrss_mb=rss, checked=str(checked))
    return rc, oom, r


def read_rows(path):
    rows = {}
    if not os.path.exists(path): return rows
    lines = open(path, encoding='utf-8').read().splitlines()
    if not lines: return rows
    head = lines[0].split('\t')
    for line in lines[1:]:
        v = line.split('\t')
        if len(v) == len(head): rows[v[0]] = dict(zip(head, v))
    return rows


def report(path, top):
    rows = [r for r in read_rows(path).values()]
    if not rows: sys.exit(f'agda-profile-modules: no results in {path}')
    def num(r, k):
        try: return float(r.get(k) or 0)
        except ValueError: return 0.0
    ok = [r for r in rows if r['status'] == 'ok']
    bad = [r for r in rows if r['status'] != 'ok']
    print(f'== {path}: {len(rows)} modules, {len(ok)} ok, {len(bad)} not ok')
    print(f'   total wall {sum(num(r, "wall_s") for r in ok) / 3600:.1f} h; '
          f'over 3 GB peak RSS: {sum(1 for r in ok if num(r, "maxrss_mb") > 3072)}; '
          f'needed -c: {sum(1 for r in ok if r["rung"] == "c")}')
    for title, key in (('PEAK RSS (MB)', 'maxrss_mb'), ('MAX RESIDENCY (MB)', 'residency_mb'),
                       ('WALL (s)', 'wall_s'), ('ALLOCATED (GB)', 'alloc_gb')):
        print(f'\n-- top {top} by {title}')
        print(f'   {"module":64} {"rss":>6} {"resid":>6} {"wall":>6} {"alloc":>6} {"clos":>5} {"lines":>5} rung')
        for r in sorted(ok, key=lambda r: -num(r, key))[:top]:
            print(f'   {r["module"]:64} {r["maxrss_mb"]:>6} {r["residency_mb"]:>6} {r["wall_s"]:>6} '
                  f'{r["alloc_gb"]:>6} {r["closure"]:>5} {r["lines"]:>5} {r["rung"]}')
    if bad:
        print('\n-- not ok')
        for r in sorted(bad, key=lambda r: r['module']):
            print(f'   {r["module"]:64} {r["status"]}')


def main():
    args = sys.argv[1:]
    ref, roots, work, rep, top, wait = 'HEAD', [], None, False, 25, True
    i = 0
    while i < len(args):
        a = args[i]
        if a == '--ref': ref = args[i + 1]; i += 2
        elif a == '--root': roots.append(args[i + 1]); i += 2
        elif a == '--work': work = args[i + 1]; i += 2
        elif a == '--report': rep = True; i += 1
        elif a == '--top': top = int(args[i + 1]); i += 2
        elif a == '--no-wait': wait = False; i += 1
        else: sys.exit(__doc__)
    label = re.sub(r'[^\w.-]', '_', ref)
    work = work or os.path.join(HOME, '.cache', 'once-lang5-profile-modules', label)
    results = os.path.join(work, 'profile.tsv')
    if rep:
        report(results, top); return

    os.makedirs(work, exist_ok=True)
    froot, sha, reused = stage(ref, work)
    logdir = os.path.join(work, 'logs'); os.makedirs(logdir, exist_ok=True)
    lib = os.path.join(work, 'libs.txt')
    open(lib, 'w').write(os.path.join(froot, 'POC.agda-lib') + '\n')   # self-contained: no stdlib
    if roots:
        mods = cone(froot, [r[:-5].replace('/', '.') if r.endswith('.agda') else r for r in roots])
    else:
        mods = all_modules(froot)
    order, deps = toposort(froot, set(mods))

    # Keys: a module's source and its in-tree imports' keys, salted with the agda binary/version
    # and the RTS flags (a different collector is a different measurement).
    salt = agda_id() + '\n' + os.environ.get('PROFILE_RTS', '-A64m')
    key, closure = {}, {}
    for m in order:
        h = hashlib.sha256(salt.encode())
        h.update(open(os.path.join(froot, modpath(m)), 'rb').read())
        for d in deps[m]: h.update(key[d].encode())
        key[m] = h.hexdigest()[:16]
        closure[m] = set(deps[m]).union(*(closure[d] for d in deps[m])) if deps[m] else set()

    done = read_rows(results)
    new = not os.path.exists(results)
    out = open(results, 'a', encoding='utf-8')
    if new: out.write('\t'.join(FIELDS) + '\n'); out.flush()
    print(f'== agda-profile-modules {ref} ({sha[:9]}), {len(order)} modules, staging '
          f'{"reused" if reused else "fresh"}: {froot}\n   results: {results}', flush=True)

    bad, t0, n = {}, time.monotonic(), len(order)
    for k, m in enumerate(order, 1):
        tag = f'[{k}/{n}]'
        prev = done.get(m)
        if prev and prev['status'] == 'ok' and prev['key'] == key[m]:
            print(f'{tag} cached {m}', flush=True); continue
        by = next((bad[d] for d in deps[m] if d in bad), None)
        if by:
            bad[m] = by
            row = dict(module=m, status=f'blocked:{by}', rung='', closure=str(len(closure[m])),
                       lines=str(sum(1 for _ in open(os.path.join(froot, modpath(m)), encoding='utf-8'))),
                       key=key[m])
            out.write('\t'.join(row.get(f, '') for f in FIELDS) + '\n'); out.flush()
            print(f'{tag} blocked {m} (by {by})', flush=True); continue
        waited = 0
        while wait and other_agda([]):
            if not waited: print(f'{tag} waiting: another agda is running', flush=True)
            time.sleep(30); waited += 30
        if waited: print(f'{tag} waited {waited}s', flush=True)
        status, rung = 'ok', 'default'
        rc, oom, r = run_one(froot, lib, m, logdir, 'default')
        if rc != 0 and oom:
            rung = 'c'
            rc, oom, r = run_one(froot, lib, m, logdir, 'c')
        if rc != 0:
            status = 'oom' if oom else f'fail({rc})'
            bad[m] = m
        row = dict(r, module=m, status=status, rung=rung, closure=str(len(closure[m])),
                   lines=str(sum(1 for _ in open(os.path.join(froot, modpath(m)), encoding='utf-8'))),
                   key=key[m])
        out.write('\t'.join(row.get(f, '') for f in FIELDS) + '\n'); out.flush()
        el = int(time.monotonic() - t0)
        print(f'{tag} {status:7} {m}  {row.get("wall_s", "?")}s  rss {row.get("maxrss_mb", "?")} MB'
              f'  resid {row.get("residency_mb", "?")} MB{"  (-c)" if rung == "c" else ""}'
              f'  (total {el // 3600}:{el // 60 % 60:02}:{el % 60:02})', flush=True)
    out.close()
    print(flush=True)
    report(results, 15)
    sys.exit(1 if bad else 0)


if __name__ == '__main__':
    main()
