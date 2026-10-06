#!/usr/bin/env python3
# reexport-remove.py — plan 0.92 §9: remove `public` re-exports with a machine
# check that no name changes meaning.
#
# Agda (the fork's --name-resolution-report, schema 1) says, for every resolved
# occurrence of a name, what it resolved to and the chain of opens that brought
# it into scope. For a re-export `open import X … public` in a facade F, the
# occurrences that crossed it are exactly those whose lineage has F's hop
# followed by X's. Each importer then imports those names from X itself.
#
#   scripts/reexport-remove.py run F.agda:LINE [F.agda:LINE …]
#
# 1. importers: the modules that can see the re-exports (through public chains);
# 2. snapshot: a report over them, on a STAGING copy (never Once's _build);
# 3. remove the `public`s; 4. repair the importers; 5. verify: re-run, and every
#    module's sequence of (written, kind, resolved) must be unchanged.
# Alias-qualified uses (C.x) and renamed names are reported for a decision and
# the batch is not applied. On any failure the working tree is restored.
#
# Run from formal/. Env: STAGE (staging dir), AGDA_PATCHED (the fork's binary).

import json, os, re, subprocess, sys, shutil, glob
from collections import defaultdict

FORMAL = os.getcwd()
STAGE = os.environ.get("STAGE") or sys.exit("STAGE unset")
AGDA = os.environ.get("AGDA_PATCHED") or sys.exit("AGDA_PATCHED unset")
STDLIB = os.path.expanduser("~/_stdlib-cache/standard-library.agda-lib")
PUB = re.compile(r"(^|\s)public\s*$")

def modname(path):
    return path[:-len(".agda")].replace("/", ".")

def modpath(mod):
    return mod.replace(".", "/") + ".agda"

def all_modules():
    out = []
    for root, _, files in os.walk("Once"):
        for f in files:
            if f.endswith(".agda"):
                out.append(os.path.join(root, f))
    return out

IMPORT = re.compile(r"^\s*(open\s+)?import\s+([^\s(]+)")

def imports_of(path):
    res = []
    for i, l in enumerate(open(path, encoding="utf-8")):
        m = IMPORT.match(l)
        if m:
            res.append((i, m.group(2)))
    return res

# --- statements -----------------------------------------------------------------

def statement(lines, i):
    """The import/open statement starting at line i: (start, end_exclusive)."""
    depth = 0; j = i
    ind = len(lines[i]) - len(lines[i].lstrip())
    while True:
        depth += lines[j].count("(") - lines[j].count(")")
        j += 1
        if j >= len(lines): break
        nxt = lines[j]
        if depth > 0: continue
        s = nxt.strip()
        if s and (len(nxt) - len(nxt.lstrip())) > ind and re.match(r"(using|hiding|renaming|public|;|\))", s):
            continue
        break
    return i, j

def statement_start(lines, line_no):
    """The statement containing 0-based line `line_no` (its module name is there)."""
    i = line_no
    while i >= 0 and not IMPORT.match(lines[i]) and not re.match(r"^\s*open\s", lines[i]):
        i -= 1
    return i

# --- importers ----------------------------------------------------------------------

def importers(facades):
    mods = all_modules()
    imp = {p: [m for _, m in imports_of(p)] for p in mods}
    reexp = {}
    for p in mods:
        L = open(p, encoding="utf-8").read().splitlines()
        rs = set()
        for i, m in imports_of(p):
            s, e = statement(L, i)
            if PUB.search(" ".join(L[s:e])):
                rs.add(m)
        reexp[modname(p)] = rs
    seen = set(); todo = list(facades)
    while todo:
        f = todo.pop()
        for p, ms in imp.items():
            mp = modname(p)
            if f in ms and mp not in seen:
                seen.add(mp)
                if f in reexp.get(mp, ()):
                    todo.append(mp)
    return sorted(seen)

# --- staging and the report ---------------------------------------------------------

def sync():
    os.makedirs(STAGE, exist_ok=True)
    subprocess.run(["rsync", "-a", "--delete", "--exclude", "_build", "--exclude", ".chk",
                    "--exclude", "ReportRoot.agda", FORMAL + "/", STAGE + "/formal/"], check=True)
    with open(STAGE + "/libs", "w") as f:
        f.write(STDLIB + "\n" + STAGE + "/formal/Once.agda-lib\n")

def report(mods, out):
    sync()
    for m in mods:
        for i in glob.glob(STAGE + "/formal/_build/*/agda/" + m.replace(".", "/") + ".agdai"):
            os.remove(i)
    with open(STAGE + "/formal/ReportRoot.agda", "w") as f:
        f.write("module ReportRoot where\n" + "".join("import " + m + "\n" for m in mods))
    cmd = ["systemd-run", "--user", "--scope", "--quiet", "-p", "MemoryMax=5500M", "-p", "MemorySwapMax=2G",
           "--", "env", "LC_ALL=en_US.utf8", "GHCRTS=-M4500m", AGDA, "--library-file=" + STAGE + "/libs",
           "--transliterate", "--name-resolution-report=" + out, "ReportRoot.agda"]
    r = subprocess.run(cmd, cwd=STAGE + "/formal", capture_output=True, text=True)
    if r.returncode != 0:
        return None, r.stdout[-6000:] + r.stderr[-3000:]
    recs = defaultdict(list)
    want = set(mods)
    for l in open(out, encoding="utf-8"):
        x = json.loads(l)
        if x.get("module") in want:
            recs[x["module"]].append(x)
    return recs, None

# --- what crossed a re-export --------------------------------------------------------

def base(resolved):
    return resolved.rsplit(".", 1)[-1] if not resolved.endswith(".") else resolved

def crossing(r, facade, target):
    hops = [h["module"] for h in r.get("lineage", [])]
    for k in range(len(hops) - 1):
        if hops[k] == facade and hops[k + 1] == target:
            return "unqualified" if not r.get("qualifier") else "qualified"
    for q in r.get("qualifier", []):
        if q["resolved"] == facade and hops[:1] == [target]:
            return "qualified"
    return None

# --- edits -------------------------------------------------------------------------------

def remove_public(path, line):
    L = open(path, encoding="utf-8").read().split("\n")
    s, e = statement(L, line - 1)
    for j in range(e - 1, s - 1, -1):
        if PUB.search(L[j]):
            L[j] = PUB.sub("", L[j]).rstrip()
            if L[j].strip() == "":
                del L[j]
            break
    open(path, "w", encoding="utf-8").write("\n".join(L))
    m = IMPORT.match(L[s])
    return m.group(2)

def add_imports(path, additions):
    """additions: {(stmt_line0, target): set(names)} — insert `open import target
    using (names)` just before the statement that brought them."""
    L = open(path, encoding="utf-8").read().split("\n")
    for (line0, target), names in sorted(additions.items(), key=lambda kv: -kv[0][0]):
        s = statement_start(L, line0)
        ind = L[s][:len(L[s]) - len(L[s].lstrip())]
        L.insert(s, ind + "open import " + target + " using (" + "; ".join(sorted(names)) + ")")
    open(path, "w", encoding="utf-8").write("\n".join(L))

def drop_from_directives(path, facade, names):
    """Remove `names` from using/hiding lists of imports of `facade` in `path`."""
    L = open(path, encoding="utf-8").read().split("\n")
    changed = False
    for i, l in enumerate(L):
        m = IMPORT.match(l)
        if not (m and m.group(2) == facade): continue
        s, e = statement(L, i)
        text = "\n".join(L[s:e])
        def fix(mm):
            items = [t.strip() for t in mm.group(2).split(";") if t.strip()]
            keep = [t for t in items if t not in names]
            return mm.group(1) + "(" + "; ".join(keep) + ")"
        new = re.sub(r"(\b(?:using|hiding)\s*)\(([^()]*)\)", fix, text)
        if new != text:
            L[s:e] = new.split("\n"); changed = True
    if changed:
        open(path, "w", encoding="utf-8").write("\n".join(L))

# --- the batch -------------------------------------------------------------------------

def signature(recs):
    return {m: [(r["written"], r["kind"], r["resolved"]) for r in rs if r["kind"] != "module"]
            for m, rs in recs.items()}

def run(targets):
    spots = []
    for t in targets:
        f, ln = t.rsplit(":", 1)
        spots.append((f, int(ln)))
    facades = sorted({modname(f) for f, _ in spots})
    imps = [m for m in importers(facades) if m not in facades] + facades
    print(f"importers: {len(imps)}", flush=True)
    before, err = report(imps, STAGE + "/before.jsonl")
    if before is None:
        sys.exit("snapshot failed:\n" + err)
    backup = {}
    def touch(p):
        if p not in backup: backup[p] = open(p, encoding="utf-8").read()
    removed = []
    for f, ln in spots:
        touch(f)
        removed.append((modname(f), remove_public(f, ln)))
    adds = defaultdict(lambda: defaultdict(set)); drops = defaultdict(lambda: defaultdict(set))
    manual = []
    for m, rs in before.items():
        for r in rs:
            for fac, tgt in removed:
                if m == fac: continue
                c = crossing(r, fac, tgt)
                if not c: continue
                b = base(r["resolved"])
                if c == "qualified" or r["written"] != b:
                    manual.append((m, r["line"], r["written"], r["resolved"], c)); continue
                h0 = r["lineage"][0]
                adds[modpath(m)][(h0["line"] - 1, tgt)].add(b)
                drops[modpath(m)][fac].add(b)
    if manual:
        for f in backup: open(f, "w", encoding="utf-8").write(backup[f])
        print("NEEDS A DECISION (not applied):")
        for x in sorted(set(manual)): print("  ", x)
        sys.exit(2)
    for p in adds:
        touch(p)
        for fac, ns in drops[p].items(): drop_from_directives(p, fac, ns)
        add_imports(p, adds[p])
    after, err = report(imps, STAGE + "/after.jsonl")
    if after is None:
        for f in backup: open(f, "w", encoding="utf-8").write(backup[f])
        sys.exit("verification run failed (tree restored):\n" + err)
    sb, sa = signature(before), signature(after)
    bad = [m for m in sb if sb[m] != sa.get(m)]
    if bad:
        for f in backup: open(f, "w", encoding="utf-8").write(backup[f])
        sys.exit("names changed meaning in: " + ", ".join(bad) + " (tree restored)")
    print("OK: " + str(len(spots)) + " public(s) removed; edited: " + ", ".join(sorted(backup)))

if __name__ == "__main__":
    if len(sys.argv) >= 3 and sys.argv[1] == "run":
        run(sys.argv[2:])
    elif len(sys.argv) >= 3 and sys.argv[1] == "importers":
        print("\n".join(importers(sys.argv[2:])))
    else:
        sys.exit(__doc__ or "usage: reexport-remove.py run F.agda:LINE …")
