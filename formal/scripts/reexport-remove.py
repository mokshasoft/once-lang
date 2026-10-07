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
        if nxt.strip() and (len(nxt) - len(nxt.lstrip())) > ind:
            continue                         # layout: deeper indentation continues it
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

def tree_key():
    import hashlib
    h = hashlib.sha256()
    for p in sorted(all_modules()):
        h.update(p.encode()); h.update(open(p, "rb").read())
    return h.hexdigest()[:16]

def report(mods, out, cache=False):
    """`cache`: a snapshot of an unchanged tree over a superset of `mods` is reused."""
    if cache:
        key = tree_key()
        meta = STAGE + "/snap-" + key + ".mods"
        if os.path.exists(meta) and set(mods) <= set(open(meta).read().split()):
            recs = defaultdict(list); want = set(mods)
            for l in open(STAGE + "/snap-" + key + ".jsonl", encoding="utf-8"):
                x = json.loads(l)
                if x.get("module") in want: recs[x["module"]].append(x)
            print("  (snapshot reused)", flush=True)
            return recs, None
        recs, err = report(mods, out)
        if recs is not None:
            shutil.copy(out, STAGE + "/snap-" + key + ".jsonl")
            open(meta, "w").write("\n".join(mods))
        return recs, err
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

def norm(m):
    """`open import M args` names its application `.#M-<hash>`."""
    return re.sub(r"-\d+$", "", m[2:]) if m.startswith(".#") else m

def crossing(r, facade, target):
    lin = r.get("lineage", [])
    hops = [norm(h["module"]) for h in lin]
    for k in range(len(hops) - 1):
        if hops[k] == facade and hops[k + 1] == target:
            if any(h["op"] == "applied" or h["module"] == "_" for h in lin[:k + 1]):
                return "applied"            # an instance copy: the repair needs the arguments
            return "unqualified" if not r.get("qualifier") else "qualified"
    for q in r.get("qualifier", []):
        if q["resolved"] == facade and hops[:1] == [target]:
            return "qualified"
    return None

# --- edits -------------------------------------------------------------------------------

def classify(path, line):
    L = open(path, encoding="utf-8").read().split("\n")
    s = statement_start(L, line - 1)
    st, e = statement(L, s)
    m = IMPORT.match(L[s])
    if m:
        rest = re.sub(r"\s+", " ", " ".join(L[st:e])).split(m.group(2), 1)[1].strip()
        if not re.match(r"^(as \S+ ?)?((using|hiding|renaming|public)\b.*)?$", rest):
            raise ValueError("module arguments (S4): " + L[s].strip())
        return ("import", m.group(2))
    m = re.match(r"^\s*open\s+([^\s(]+)\s*(using|hiding|renaming|public|$)", L[s])
    if not m:
        raise ValueError("cannot classify (module arguments?): " + L[s].strip())
    return ("local", m.group(1))

def remove_public(path, line):
    L = open(path, encoding="utf-8").read().split("\n")
    s, e = statement(L, statement_start(L, line - 1))
    for j in range(e - 1, s - 1, -1):
        if PUB.search(L[j]):
            L[j] = PUB.sub("", L[j]).rstrip()
            if L[j].strip() == "":
                del L[j]
            break
    else:
        raise ValueError("no `public` in the statement at " + path + ":" + str(line))
    open(path, "w", encoding="utf-8").write("\n".join(L))
    m = IMPORT.match(L[s])
    if m:
        return ("import", m.group(2))
    m = re.match(r"^\s*open\s+([^\s(]+)\s*(using|hiding|renaming|$)", L[s])
    if not m:
        raise ValueError("cannot classify (module arguments?): " + L[s].strip())
    return ("local", m.group(1))

def add_imports(path, additions):
    """additions: {(stmt_line0, target): set(names)} — insert `open import target
    using (names)` just before the statement that brought them."""
    L = open(path, encoding="utf-8").read().split("\n")
    for (line0, target), names in sorted(additions.items(), key=lambda kv: -kv[0][0]):
        s = statement_start(L, line0)
        _, e = statement(L, s)              # AFTER it: a local open needs the facade bound
        ind = L[s][:len(L[s]) - len(L[s].lstrip())]
        mo = re.match(r"open (\S+)\.([^.\s]+)$", target)
        if mo and not target.startswith("open import"):
            fac, sub = mo.groups()
            src = "\n".join(L)
            al = re.findall(r"import\s+" + re.escape(fac) + r"\s+as\s+(\S+)", src)
            plain = re.search(r"import\s+" + re.escape(fac) + r"(?!\s+as\b)(\s|$)", src)
            if al and not plain:
                target = "open " + al[0] + "." + sub      # the facade is bound only by its alias here
        L.insert(e, ind + target + " using (" + "; ".join(sorted(names)) + ")")
    open(path, "w", encoding="utf-8").write("\n".join(L))

def drop_from_directives(path, facade, names):
    """Remove `names` from using/hiding lists of imports of `facade` in `path`."""
    L = open(path, encoding="utf-8").read().split("\n")
    changed = False
    aliases = set(re.findall(r"import\s+" + re.escape(facade) + r"\s+as\s+(\S+)", "\n".join(L)))
    for i, l in enumerate(L):
        m = IMPORT.match(l)
        mo = re.match(r"^\s*open\s+(\S+)", l)
        if not ((m and m.group(2) == facade) or (not m and mo and mo.group(1) in aliases)): continue
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

def applied_importers(facade, imps):
    """Importers that import `facade` APPLIED to arguments: its re-exports reach
    them as instance copies, so a repair would need the arguments."""
    out = []
    for m in imps:
        p = modpath(m)
        if not os.path.exists(p): continue
        L = open(p, encoding="utf-8").read().split("\n")
        for i, mod in imports_of(p):
            if mod != facade: continue
            st, e = statement(L, i)
            rest = " ".join(L[st:e]).split(facade, 1)[1].strip()
            if rest and not re.match(r"^(as\s+\S+\s*)?((using|hiding|renaming|public)\b.*)?$", rest):
                out.append(m)
    return out

def declares(path, name):
    """Does the module at `path` declare `name` (a signature, data/record, field,
    or constructor line)?"""
    if not os.path.exists(path): return False
    pat = re.compile(r"^\s*(?:data\s+|record\s+|field\s+|constructor\s+)?" + re.escape(name) + r"\s+(?::|where|\{|\()|"
                     r"^\s*(?:field|constructor)\s+" + re.escape(name) + r"\b", re.M)
    return pat.search(open(path, encoding="utf-8").read()) is not None

def declares_top(path, name):
    """`name` is declared at the module's TOP level (column 0) — a field or a
    nested module's name is not the module's own export."""
    if not os.path.exists(path): return False
    pat = re.compile(r"^(?:data\s+|record\s+)?" + re.escape(name) + r"\s+(?::|where|\{|\()", re.M)
    return pat.search(open(path, encoding="utf-8").read()) is not None

def directive_names(path, facade):
    """Names listed in using/renaming directives of imports of `facade` in `path`."""
    L = open(path, encoding="utf-8").read().split("\n")
    out = set()
    for i, m in imports_of(path):
        if m != facade: continue
        st, e = statement(L, i)
        text = " ".join(L[st:e])
        for mm in re.finditer(r"\busing\s*\(([^()]*)\)", text):
            out |= {t.strip() for t in mm.group(1).split(";") if t.strip()}
        for mm in re.finditer(r"\brenaming\s*\(([^()]*)\)", text):
            out |= {t.split(" to ")[0].strip() for t in mm.group(1).split(";") if t.strip()}
    return out

def run(targets):
    spots = []
    for t in targets:
        f, ln = t.rsplit(":", 1)
        spots.append((f, int(ln)))
    facades = sorted({modname(f) for f, _ in spots})
    # pre-existing RED islands cannot be scope checked, so they cannot be verified;
    # they are left as they are (plan 0.92 §9)
    red = set(os.environ.get("RED", "Once.Allocator.Slab Once.Spike.RelSpike Once.Optimizer.Normal").split())
    # refutation probes (`Once.Probe.*`) target postulates since removed: stale by design
    # Verify exactly what the gate checks: the modules the island backstop
    # (EverythingFiltered.agda, green by the gate) imports. Others are islands the
    # gate does not check either; red ones among them cannot be scope checked.
    backstop = None
    if os.path.exists("EverythingFiltered.agda"):
        backstop = {m for _, m in imports_of("EverythingFiltered.agda")}
    imps = [m for m in importers(facades)
            if m not in facades and m not in red and not m.startswith("Once.Probe.")
            and (backstop is None or m in backstop)] + facades
    # The snapshot checks the UNCHANGED tree, so a module failing it is red already:
    # drop it (and what imports it) and retry.
    for _ in range(10):
        print(f"importers: {len(imps)}", flush=True)
        before, err = report(imps, STAGE + "/before.jsonl", cache=True)
        if before is not None: break
        m = re.search(r"stage/formal/(Once/[^:\s]+)\.agda:\d+[.,]\d+-\S*: (?:error|warning)", err)
        if not m:
            sys.exit("snapshot failed:\n" + err)
        bad = m.group(1).replace("/", ".")
        print("  pre-existing RED (left as is): " + bad, flush=True)
        red.add(bad)
        imps = [x for x in imps if x != bad and bad not in [i for _, i in imports_of(modpath(x))]]
    else:
        sys.exit("snapshot failed repeatedly")
    backup = {}
    def touch(p):
        if p not in backup: backup[p] = open(p, encoding="utf-8").read()
    # classify every spot against the snapshot BEFORE editing
    plan = []
    skipped = []
    target_of = defaultdict(set)
    for f, ln in spots:
        try:
            kind, x = classify(f, ln)
            alias_of = x
        except ValueError as e:
            skipped.append((f, ln, str(e))); continue
        fac = modname(f)
        if kind == "local":
            src = open(f, encoding="utf-8").read()
            al = re.search(r"^\s*(?:open\s+)?import\s+(\S+)\s+as\s+" + re.escape(x) + r"\b", src, re.M)
            if al:
                kind, alias_of = "import", al.group(1)
        ap = applied_importers(fac, imps)
        if ap:
            skipped.append((f, ln, "imported applied by " + ", ".join(ap))); continue
        stmt = ("open import " + (alias_of if kind == "import" and x != alias_of else x)) if kind == "import" else ("open " + fac + "." + x)
        add = defaultdict(lambda: defaultdict(set)); drop = defaultdict(set); why = set()
        for m, rs in before.items():
            if m == fac: continue
            for r in rs:
                c = crossing(r, fac, x)
                if not c: continue
                b = base(r["resolved"])
                if c != "unqualified" or r["written"] != b:
                    why.add(c if c != "unqualified" else "renamed"); continue
                add[modpath(m)][(r["lineage"][0]["line"] - 1, stmt)].add(b)
                target_of[(fac, b)].add(stmt)
                drop[modpath(m)].add(b)
        if why:
            skipped.append((f, ln, ", ".join(sorted(why))))
        else:
            plan.append((f, ln, fac, add, drop, stmt))
    # PRE-FLIGHT 1: a name an importer lists in a directive of a facade but never
    # uses (no occurrence in its records — the report IS the reachability fact) is
    # a dead import: prune it, rather than move it.
    used = {m: {r["written"] for r in rs} | {base(r["resolved"]) for r in rs} for m, rs in before.items()}
    facs = {fac for _, _, fac, _, _, _ in plan}
    for fac in facs:
        for m in imps:
            p = modpath(m)
            if m == fac or not os.path.exists(p) or m not in used: continue
            dead = {n for n in directive_names(p, fac) if n not in used[m]}
            if dead:
                touch(p); drop_from_directives(p, fac, dead)
                print(f"  pruned dead imports {sorted(dead)} of {fac} in {p}", flush=True)
    # PRE-FLIGHT 2: directive names no record placed (listed, never used)
    by_fac = defaultdict(list)
    for f, ln, fac, add, drop, stmt in plan: by_fac[fac].append((f, stmt))
    for fac, sp in by_fac.items():
        for m in imps:
            p = modpath(m)
            if m == fac or not os.path.exists(p): continue
            for n in directive_names(p, fac):
                if (fac, n) in target_of or declares_top(modpath(fac), n): continue
                cands = {st for f, st in sp
                         if st.startswith("open import ") and declares(modpath(st.split()[2]), n)}
                if len(cands) != 1 and len(sp) == 1: cands = {sp[0][1]}
                if len(cands) == 1:
                    st = next(iter(cands))
                    L = open(p, encoding="utf-8").read().split("\n")
                    line0 = next(i for i, mm in imports_of(p) if mm == fac)
                    for f, ln, fac2, add, drop, stmt in plan:
                        if fac2 == fac and stmt == st:
                            add[p][(line0, st)].add(n); drop[p].add(n); break
    for f, ln, why in skipped:
        print(f"  skipped {f}:{ln}: {why}")
    if not plan:
        sys.exit("nothing mechanical in this batch")
    for f, ln, *_ in sorted(plan, key=lambda x: (x[0], -x[1])):   # bottom-up: removals shift lines
        touch(f); remove_public(f, ln)
    adds = defaultdict(lambda: defaultdict(set)); drops = defaultdict(lambda: defaultdict(set))
    for f, ln, fac, add, drop, _ in plan:
        for p, d in add.items():
            for k, ns in d.items(): adds[p][k] |= ns
        for p, ns in drop.items(): drops[p][fac] |= ns
    for p in adds:
        touch(p)
        for fac, ns in drops[p].items(): drop_from_directives(p, fac, ns)
        add_imports(p, adds[p])
    # A name listed in an importer's directive but never used is not in the report
    # (directive names are not looked up); Agda names it, so move it and re-run.
    stmt_of = defaultdict(set)
    for f, ln, fac, add, drop, stmt in plan:
        stmt_of[fac].add(stmt)
    for _ in range(25):
        after, err = report(imps, STAGE + "/after.jsonl")
        if after is not None: break
        m = re.search(r"stage/formal/(Once/[^:\s]+\.agda):(\d+)\.\d+-\S*: warning: -W\[no\]ModuleDoesntExport\s*"
                      r"The module\s+(\S+)\s+doesn't\s+export\s+the\s+following:\s*\n((?:\s+\S.*\n)+?)when", err)
        if not m:
            for f in backup: open(f, "w", encoding="utf-8").write(backup[f])
            sys.exit("verification run failed (tree restored):\n" + err)
        path, line, fac = m.group(1), int(m.group(2)), m.group(3)
        if fac not in stmt_of:                       # Agda names it by the importer's alias
            al = re.search(r"import\s+(\S+)\s+as\s+" + re.escape(fac) + r"\b", open(path, encoding="utf-8").read())
            if al: fac = al.group(1)
        if fac not in stmt_of:                       # a module INSIDE a facade (a record's module)
            owner = [f for f in stmt_of if fac.startswith(f + ".")]
            if owner:
                for f in backup: open(f, "w", encoding="utf-8").write(backup[f])
                print("AMBIGUOUS-FACADE " + max(owner, key=len))
                sys.exit("a name of " + fac + " inside a removed facade (tree restored)")
        names = {l.strip().split(" ")[0] for l in m.group(4).splitlines() if l.strip()}
        where = {}
        for n in names:
            ts = target_of.get((fac, n)) or (stmt_of.get(fac) if len(stmt_of.get(fac, ())) == 1 else None)
            if not ts or len(ts) != 1:
                for f in backup: open(f, "w", encoding="utf-8").write(backup[f])
                print("AMBIGUOUS-FACADE " + fac)
                sys.exit("cannot place unused directive name " + n + " of " + fac + " (tree restored)")
            where.setdefault(next(iter(ts)), set()).add(n)
        print(f"  moving unused directive names {sorted(names)} at {path}:{line}", flush=True)
        touch(path)
        drop_from_directives(path, fac, names)
        add_imports(path, {(line - 1, st): ns for st, ns in where.items()})
    else:
        for f in backup: open(f, "w", encoding="utf-8").write(backup[f])
        sys.exit("verification kept failing (tree restored)")
    sb, sa = signature(before), signature(after)
    bad = [m for m in sb if sb[m] != sa.get(m)]
    if bad:
        for f in backup: open(f, "w", encoding="utf-8").write(backup[f])
        sys.exit("names changed meaning in: " + ", ".join(bad) + " (tree restored)")
    print("OK: " + str(len(plan)) + " public(s) removed; edited: " + ", ".join(sorted(backup)))

def mechanical(path, i, L):
    """A re-export the client can repair: at the file's top level, its module
    written without arguments (`open import X … public`, `open R … public`)."""
    s = i
    while s >= 0 and not re.match(r"^\s*(open|import)\b", L[s]): s -= 1
    if s < 0 or L[s] != L[s].lstrip(): return False      # nested in a module
    m = re.match(r"^(open import|open)\s+([^\s(]+)\s*(.*)$", L[s])
    if not m: return False
    rest = m.group(3)
    # after the module name only `as Q`, a directive, or `public` may follow
    return re.match(r"^(as\s+\S+\s*)?((using|hiding|renaming)\b.*|public\s*)?$", rest) is not None

def candidates():
    rows = []
    for p in all_modules():
        L = open(p, encoding="utf-8").read().split("\n")
        lines = [i + 1 for i, l in enumerate(L) if PUB.search(l) and mechanical(p, i, L)]
        if lines:
            rows.append((len(importers([modname(p)])), p, lines))
    for n, p, lines in sorted(rows):
        print(n, " ".join(p + ":" + str(x) for x in lines))

def apex_live(ast_json, root="Once.Certified"):
    """The apex-live scope (plan 0.92, user 2026-10-07): from the fork's --write-ast
    dump, the modules holding reachable definitions, the record/local modules
    whose definitions are reachable, and the apex's static import cone."""
    d = json.load(open(ast_json, encoding="utf-8"))
    names = [e["name"] for e in d["reachable"]]
    defmods = set()
    for e in d["reachable"]:
        src = e.get("source") or ""
        if src.startswith("formal/") and src.endswith(".agda"):
            defmods.add(modname(src[len("formal/"):]))
    cone, todo = set(), [root]
    while todo:
        m = todo.pop()
        if m in cone or not os.path.exists(modpath(m)): continue
        cone.add(m)
        todo += [x for _, x in imports_of(modpath(m))]
    return names, defmods, cone

def live_line(path, line, names, defmods, cone):
    m = modname(path)
    if m not in cone: return False
    try:
        kind, x = classify(path, line)
    except ValueError:
        return True                      # parameterised: kept on the S4 list if live
    if kind == "import":
        return x in defmods
    prefix = m + "." + x + "."
    return any(n.startswith(prefix) for n in names)

if __name__ == "__main__":
    if len(sys.argv) == 3 and sys.argv[1] == "live-candidates":
        names, defmods, cone = apex_live(sys.argv[2])
        rows = []
        for p in all_modules():
            L = open(p, encoding="utf-8").read().split("\n")
            lines = [i + 1 for i, l in enumerate(L) if PUB.search(l) and mechanical(p, i, L)
                     and live_line(p, i + 1, names, defmods, cone)]
            if lines: rows.append((len(importers([modname(p)])), p, lines))
        for n, p, lines in sorted(rows):
            print(n, " ".join(p + ":" + str(x) for x in lines))
        sys.exit(0)
    if len(sys.argv) == 2 and sys.argv[1] == "candidates":
        candidates(); sys.exit(0)
    if len(sys.argv) >= 3 and sys.argv[1] == "run":
        run(sys.argv[2:])
    elif len(sys.argv) >= 3 and sys.argv[1] == "importers":
        print("\n".join(importers(sys.argv[2:])))
    else:
        sys.exit(__doc__ or "usage: reexport-remove.py run F.agda:LINE …")
