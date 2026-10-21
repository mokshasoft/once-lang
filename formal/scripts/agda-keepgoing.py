#!/usr/bin/env python3
# SPDX-License-Identifier: AGPL-3.0-or-later
# Copyright (C) 2025-2026 Jonas Claesson
"""agda-keepgoing.py — type-check a module's whole import cone and report EVERY
independent error in one pass (`make -k` for Agda).

`agda M` stops at the first error, and after a fix re-checks everything above
the fixed module up to the next one: a wide refactor costs one full run per
error. This driver keeps ONE Agda process (`--interaction-json`, so checked
modules stay in memory), loads the cone bottom-up, records each module's error,
and skips the modules that import a failed one.

Usage (from formal/):
    scripts/agda-keepgoing.py [ROOT.agda] [--max N] [--only PREFIX]
Prints one block per failing module and a summary. Runs Agda under the same
memory cap as agda-safe.sh (systemd-run scope); if Agda dies it is restarted
and the pass continues.
"""
import json, os, re, subprocess, sys, glob

ROOT_DIR = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
os.chdir(ROOT_DIR)

def modpath(m): return m.replace('.', '/') + '.agda'

def imports(m):
    p = modpath(m)
    if not os.path.exists(p): return []
    s = open(p, encoding='utf-8').read()
    s = re.sub(r'--[^\n]*', '', s)
    return [d for d in re.findall(r'^\s*(?:open\s+)?import\s+(Once[\w.\-′]*)', s, re.M) if os.path.exists(modpath(d))]

def cone(root):
    order, seen, onstack = [], set(), set()
    def visit(m):
        if m in seen: return
        seen.add(m)
        for d in imports(m): visit(d)
        order.append(m)
    sys.setrecursionlimit(10000)
    visit(root)
    return order

def stdlib():
    out = subprocess.run('find /nix/store -maxdepth 2 -name standard-library.agda-lib | head -1',
                         shell=True, capture_output=True, text=True).stdout.strip()
    lib = os.path.join(ROOT_DIR, '_build', 'keepgoing.libs')
    os.makedirs(os.path.dirname(lib), exist_ok=True)
    open(lib, 'w').write(out + '\n' + os.path.join(ROOT_DIR, 'Once.agda-lib') + '\n')
    return lib

class Agda:
    def __init__(self, lib):
        mem = os.environ.get('AGDA_SAFE_MEM_MAX', '5500M')
        cmd = ['systemd-run', '--user', '--scope', '--quiet', '-p', f'MemoryMax={mem}', '-p', 'MemorySwapMax=2G',
               'env', '-u', 'AGDA_DIR', 'agda', f'--library-file={lib}', '--interaction-json']
        self.p = subprocess.Popen(cmd, stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                                  text=True, encoding='utf-8', bufsize=1)
    def alive(self): return self.p.poll() is None
    def load(self, f):
        a = os.path.abspath(f)
        q = json.dumps(a)
        self.p.stdin.write(f'IOTCM {q} None Indirect (Cmd_load {q} [])\n')
        self.p.stdin.write(f'IOTCM {q} None Indirect Cmd_show_version\n')
        self.p.stdin.flush()
        errs = []
        while True:
            line = self.p.stdout.readline()
            if not line: return None  # agda died
            line = line.strip()
            while line.startswith('JSON>'): line = line[5:].strip()
            if not line.startswith('{'): continue
            try: r = json.loads(line)
            except Exception: continue
            if r.get('kind') == 'DisplayInfo':
                info = r.get('info', {})
                k = info.get('kind')
                if k == 'Version': return errs
                if k == 'Error':
                    e = info.get('error', {})
                    errs.append(e.get('message') or json.dumps(e)[:2000])
                if k == 'AllGoalsWarnings' and (info.get('errors') or []):
                    for e in info['errors']: errs.append(e.get('message', str(e)) if isinstance(e, dict) else str(e))
    def close(self):
        try: self.p.stdin.close(); self.p.wait(10)
        except Exception: self.p.kill()

def main():
    args = sys.argv[1:]
    root = 'Once/Certified.agda'; maxerr = 1000; only = None
    i = 0
    while i < len(args):
        if args[i] == '--max': maxerr = int(args[i+1]); i += 2
        elif args[i] == '--only': only = args[i+1]; i += 2
        else: root = args[i]; i += 1
    rootm = root[:-5].replace('/', '.') if root.endswith('.agda') else root
    order = cone(rootm)
    lib = stdlib()
    agda = Agda(lib)
    failed, skipped, ok = {}, set(), 0
    deps = {m: imports(m) for m in order}
    for n, m in enumerate(order):
        if only and not m.startswith(only): continue
        if any(d in failed or d in skipped for d in deps[m]):
            skipped.add(m); continue
        res = agda.load(modpath(m))
        if res is None:
            failed[m] = ['(agda died — out of memory?)']
            agda = Agda(lib)
            continue
        if res:
            failed[m] = res
            print(f'=== FAIL {m}\n' + '\n'.join(r.strip() for r in res) + '\n', flush=True)
            if len(failed) >= maxerr: break
        else:
            ok += 1
    agda.close()
    print(f'=== SUMMARY: {len(order)} modules in cone, {ok} ok, {len(failed)} failed, {len(skipped)} skipped (import a failure)')
    sys.exit(1 if failed else 0)

if __name__ == '__main__':
    main()
