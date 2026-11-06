#!/usr/bin/env python3
# SPDX-License-Identifier: AGPL-3.0-or-later
# Copyright (C) 2025-2026 Jonas Claesson
"""agda-profile.py — measure what each module costs to type-check: wall time and
peak memory, ONE MODULE PER AGDA PROCESS, leaves first.

Why one process per module, bottom-up (the lesson of plan-ref's `sweep.sh`):
when every import already has its interface, the process checking a module
loads those interfaces and type-checks ONE module's worth of new work. Its peak
then measures that module (plus loading its closure, which every build pays
too), not whatever happened to be checked before it in the same process. That
is what `make certified`, the backstop and `agda-keepgoing.py` cannot tell us:
they hold hundreds of modules in one process, so the numbers mix.

Every module is REALLY checked: the tree is staged from a committed ref into a
work directory with an empty `_build` (`git archive`, as run-ast-dumps.sh does),
so a cached interface can never pass for a measurement (decision log, "the
measurement trap"). Your own `formal/_build` is never touched.

Usage (from the repo root or formal/):
    formal/scripts/agda-profile.py [--ref REF] [--root MOD.agda]... [--work DIR]
    formal/scripts/agda-profile.py --report [--top N] [--work DIR]

  --ref REF      the committed tree to measure (default HEAD)
  --root M.agda  measure only M's import cone (repeatable; default: every module
                 the backstop checks, i.e. all of Once/ minus backstop.islands)
  --work DIR     staging + results (default ~/.cache/once-profile/<ref-label>)
  --report       print the worst offenders from an existing results file
  --top N        how many to list (default 25)

Environment:
  PROFILE_MEM_MAX  cgroup memory cap per module (default 5500M, as agda-safe.sh)
  PROFILE_SWAP_MAX cgroup swap cap (default 2G)

Results: <work>/profile.tsv, one row per module, appended as it goes (follow it
with `tail -f`). A rerun RESUMES: a module whose row is `ok` with the same key
(sha256 of its source and its in-tree imports' keys) is not checked again.

Memory: each module first runs at the default collector under a heap limit
just below the cgroup cap; if it runs out it is retried with the compacting
collector (`-c`), then reported OOM. Modules that import an OOM or failed module
are reported `blocked` (their interfaces cannot exist). The rung that worked is
recorded: a module that needs `-c` is itself a finding.

Contention: if another agda process is running (another session), the profiler
WAITS for it before starting each module, and logs that it waited. Two Agda
processes at once on this machine distort every number (and kill each other).
"""
import hashlib, os, re, shutil, subprocess, sys, time

REPO = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
HOME = os.path.expanduser('~')

FIELDS = ['module', 'status', 'rung', 'wall_s', 'maxrss_mb', 'residency_mb', 'alloc_gb',
          'gc_s', 'checked', 'closure', 'lines', 'key']


def modpath(m): return m.replace('.', '/') + '.agda'


def imports(root, m):
    p = os.path.join(root, modpath(m))
    if not os.path.exists(p): return []
    s = re.sub(r'--[^\n]*', '', open(p, encoding='utf-8').read())
    return sorted({d for d in re.findall(r'^\s*(?:open\s+)?import\s+(Once[\w.\-′]*)', s, re.M)
                   if os.path.exists(os.path.join(root, modpath(d)))})


def all_modules(root):
    isl = set()
    p = os.path.join(root, 'scripts', 'backstop.islands')
    if os.path.exists(p):
        for line in open(p, encoding='utf-8'):
            line = line.split('#')[0].strip()
            if line: isl.add(line)
    mods = []
    for d, _, fs in os.walk(os.path.join(root, 'Once')):
        for f in fs:
            if f.endswith('.agda'):
                rel = os.path.relpath(os.path.join(d, f), root)
                mods.append(rel[:-5].replace('/', '.'))
    return sorted(m for m in mods if m not in isl)


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


def stdlib():
    out = subprocess.run('find /nix/store -maxdepth 2 -name standard-library.agda-lib | head -1',
                         shell=True, capture_output=True, text=True).stdout.strip()
    if not out: sys.exit('agda-profile: standard-library not found in the nix store')
    return out


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
        return os.path.join(tree, 'formal'), sha, True
    # A new ref is extracted OVER the old tree, keeping `_build`: Agda keys interfaces by source
    # hash, so unchanged modules stay built, and their rows stay valid (same key). Old sources are
    # removed first so a deleted module cannot linger. Wipe the work directory to start cold.
    src = os.path.join(tree, 'formal')
    if os.path.isdir(src):
        for d, _, fs in os.walk(src):
            if '_build' in d.split(os.sep): continue
            for f in fs:
                if f.endswith('.agda'): os.remove(os.path.join(d, f))
    os.makedirs(tree, exist_ok=True)
    a = subprocess.Popen(['git', '-C', REPO, 'archive', sha, 'formal'], stdout=subprocess.PIPE)
    subprocess.run(['tar', '-x', '-C', tree], stdin=a.stdout, check=True)
    a.wait()
    open(stamp, 'w').write(sha + '\n')
    return os.path.join(tree, 'formal'), sha, False


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
    cap = int(mem[:-1]) * (1024 if mem[-1] in 'Gg' else 1) if mem[-1] in 'GgMm' else 5500
    stats = os.path.join(logdir, m + '.stats')
    timef = os.path.join(logdir, m + '.time')
    log = os.path.join(logdir, m + '.log')
    rts = f'-M{cap - 700}m -s{stats}' + (' -c' if rung == 'c' else '')
    env = dict(os.environ, GHCRTS=rts)
    env.pop('AGDA_DIR', None)
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
    if not rows: sys.exit(f'agda-profile: no results in {path}')
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
    ref, roots, work, rep, top = 'HEAD', [], None, False, 25
    i = 0
    while i < len(args):
        a = args[i]
        if a == '--ref': ref = args[i + 1]; i += 2
        elif a == '--root': roots.append(args[i + 1]); i += 2
        elif a == '--work': work = args[i + 1]; i += 2
        elif a == '--report': rep = True; i += 1
        elif a == '--top': top = int(args[i + 1]); i += 2
        else: sys.exit(__doc__)
    label = re.sub(r'[^\w.-]', '_', ref)
    work = work or os.path.join(HOME, '.cache', 'once-profile', label)
    results = os.path.join(work, 'profile.tsv')
    if rep:
        report(results, top); return

    os.makedirs(work, exist_ok=True)
    froot, sha, reused = stage(ref, work)
    logdir = os.path.join(work, 'logs'); os.makedirs(logdir, exist_ok=True)
    lib = os.path.join(work, 'libs.txt')
    open(lib, 'w').write(stdlib() + '\n' + os.path.join(froot, 'Once.agda-lib') + '\n')
    if roots:
        mods = cone(froot, [r[:-5].replace('/', '.') if r.endswith('.agda') else r for r in roots])
    else:
        mods = all_modules(froot)
    order, deps = toposort(froot, set(mods))

    # Keys: a module's source and its in-tree imports' keys, salted with the agda binary/version
    # and the stdlib path (immutable nix store paths: the path is the version).
    salt = agda_id() + '\n' + stdlib()
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
    print(f'== agda-profile {ref} ({sha[:9]}), {len(order)} modules, staging '
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
        while other_agda([]):
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
