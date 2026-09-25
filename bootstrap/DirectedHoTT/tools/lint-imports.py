#!/usr/bin/env python3
"""lint-imports.py — the FIRST GATE: import/scope errors, in seconds, tree-wide.

★★ WHY THIS EXISTS, AND WHY IT IS NOT AGDA.  Agda's `--only-scope-checking`
  scope-checks only the TOP-LEVEL module and FULLY TYPE-CHECKS every import
  first — MEASURED 2026-09-25 with a control: `B` imports `A`; `A` has a
  type error only, `B` a scope error only; `--only-scope-checking B`
  reported `A`'s TYPE error and never reached `B`.  ⇒ a scope-only pass
  through Agda costs a full build of the closure, so it cannot be a cheap
  gate.  This script needs no interfaces: it reads the source.

WHAT IT CHECKS (both are the dominant error class of a kernel/Lib rename):
  1. every name in an `open import M using ( … )` / `hiding ( … )` /
     `renaming ( … to … )` list EXISTS in `M`'s exports (top-level
     declarations, constructors, record constructors/fields, and whatever
     `M` re-exports with `open import … public`).
  2. a DISTINCTIVE project name used in a module that nothing in the module
     brings into scope — e.g. `xenv₀` used with no import of it.
     "Distinctive" = defined in exactly one project module and never BOUND
     anywhere in the using module (patterns, binders, local decls), so a
     local variable that shadows a global is not reported.

WHAT IT DOES NOT CHECK: types, arities, unbound LOCAL variables (`wD` with
  no `wD` in scope), anything inside `module _ … where` parameter plumbing
  beyond names.  It is a GATE, not a proof: rc=0 here means "worth running
  the sweep", never "green".

Usage:  tools/lint-imports.py [--control]
  rc 0  no findings · rc 1  findings (listed) · rc 2  the CONTROL failed
⚠ `--control` seeds one error of each class into a scratch copy of a real
  module and demands BOTH are reported.  A linter that reports nothing is
  indistinguishable from a broken one — run the control after changing it.
"""
import os, re, sys, glob, tempfile, shutil

HERE = os.path.dirname(os.path.abspath(__file__))
# ★ LINT_ROOT: lint another checkout (e.g. a known-green commit, to measure
#   the false-positive rate — which must be ZERO there).
ROOT = os.environ.get("LINT_ROOT") or os.path.dirname(HERE)   # DirectedHoTT/
BOOT = os.path.dirname(ROOT)                                    # bootstrap/
SKIP_DIRS = ("Negative",)

def modname(path):
    rel = os.path.relpath(path, BOOT)[:-len(".agda")]
    return rel.replace(os.sep, ".")

def strip_comments(s):
    s = re.sub(r"\{-.*?-\}", lambda m: "\n" * m.group(0).count("\n"), s, flags=re.S)
    return "\n".join(re.sub(r"(^|\s)--.*$", "", l) for l in s.split("\n"))

TOK = re.compile(r"[^\s(){};.@\"]+")
KEYWORDS = {"private", "variable", "abstract", "mutual", "postulate", "where",
            "open", "import", "module", "using", "hiding", "renaming", "to",
            "public", "data", "record", "field", "constructor", "infix",
            "infixl", "infixr", "with", "rewrite", "let", "in", "λ", "∀",
            "instance", "pattern", "syntax", "Set", "Prop"}

# ★ check 2 reports only DISTINCTIVE names: a short all-ASCII name (`dp`,
#   `dt`, `I`) is far more often a local binder than a missed import, and
#   a false positive per module would teach everyone to ignore the gate.
def distinctive(t):
    # ★ a short base with a subscript/prime (`C₂`, `i₀`, `f'`) is a local
    #   binder by this codebase's convention, not a global.
    base = t.rstrip("₀₁₂₃₄₅₆₇₈₉'0123456789")
    if len(base) <= 2 and base.isascii(): return False
    return len(t) >= 4 or any(not (c.isascii() and c.isalnum()) for c in t)

def names_in_list(txt):
    return [t.strip() for t in txt.split(";") if t.strip()]

def balanced(s, i):
    "s[i] == '(' → index of its matching ')'"
    d = 0
    for j in range(i, len(s)):
        if s[j] == "(": d += 1
        elif s[j] == ")":
            d -= 1
            if d == 0: return j
    return len(s) - 1

IMPORT = re.compile(r"^(open\s+)?import\s+([\w.]+)((?:[^\n]|\n[ \t]+)*)", re.M)

def parse_imports(src):
    """[(module, opened?, using|None, hiding, renaming-pairs, public?)]"""
    out = []
    for m in IMPORT.finditer(src):
        opened, mod, rest = bool(m.group(1)), m.group(2), m.group(3)
        using = hiding = None; ren = []; public = "public" in rest.split()
        for kw in ("using", "hiding", "renaming"):
            k = rest.find(kw)
            while k >= 0:
                p = rest.find("(", k)
                if p < 0: break
                q = balanced(rest, p); body = rest[p + 1:q]
                if kw == "using": using = (using or []) + names_in_list(body)
                elif kw == "hiding": hiding = (hiding or []) + names_in_list(body)
                else:
                    for pr in names_in_list(body):
                        a, _, b = pr.partition(" to ")
                        ren.append((a.strip(), b.strip()))
                k = rest.find(kw, q)
        out.append((mod, opened, using, hiding or [], ren, public))
    return out

DECL = re.compile(r"^(?!open\b|import\b|module\b|infix|private\b|mutual\b|variable\b|abstract\b|postulate\b|record\b|data\b|syntax\b|pattern\b)([^\s:(){}]+(?:\s+[^\s:(){}]+)*)\s+:(?!:)", re.M)

def declared(src):
    """(exported, local-only) names declared in a module's text."""
    exp, loc = set(), set()
    lines = src.split("\n")
    priv_indent = None
    in_data = in_record = False
    in_modblock = None        # name of an enclosing `module X … where` (col 0)
    for l in lines:
        if not l.strip(): continue
        ind = len(l) - len(l.lstrip())
        st = l.strip()
        if ind == 0:
            priv_indent = None; in_data = in_record = False; in_modblock = None
            # ★ a nested module (its `where` may be lines later) — but NOT the
            #   file's own `module DirectedHoTT.… where` header.
            m = re.match(r"^module\s+(\S+)", st)
            if m and "." not in m.group(1):
                in_modblock = m.group(1)
                if in_modblock != "_": exp.add("module " + in_modblock)
                continue
            # ★ `mutual`/`abstract`/`instance` blocks: their indented
            #   declarations are the file's own, exported.
            if st in ("mutual", "abstract", "instance"):
                in_modblock = "_"; continue
            m = re.match(r"^(data|record)\s+([^\s:]+)", st)
            if m:
                exp.add(m.group(2)); in_data = m.group(1) == "data"; in_record = not in_data
                continue
            m = re.match(r"^([^\s:(){}]+(?:\s+[^\s:(){}]+)*)\s+:(?!:)", st)
            if m and not re.match(r"^(open|import|module|infix\w*|syntax|pattern)\b", st):
                exp.update(m.group(1).split())
            if st.startswith("private"): priv_indent = 0
            m = re.match(r"^pattern\s+(\S+)", st)
            if m: exp.add(m.group(1))
            continue
        # indented
        # ★ an `open X …` inside a module block: its names reach users of
        #   the block (`AmrecClosed` uses `AmT`'s `aZBr` through `AmTΠ`,
        #   which opens `AmT` WITHOUT `public`, and compiles — measured).
        #   Over-approximated to every `open`: a missed error costs a sweep,
        #   a false one costs trust in the gate.
        mo = re.match(r"^open\s+([^\s(]+)", st)
        if mo and in_modblock not in (None, "_"):
            MODPUB.setdefault(in_modblock, set()).add(mo.group(1).split(".")[-1])
        if priv_indent is not None:
            m = re.match(r"^([^\s:(){}]+(?:\s+[^\s:(){}]+)*)\s+:(?!:)", st)
            if m: loc.update(m.group(1).split())
            continue
        if in_data:
            m = re.match(r"^([^\s:(){}]+(?:\s+[^\s:(){}]+)*)\s+:(?!:)", st)
            if m: exp.update(m.group(1).split())
            continue
        if in_record:
            m = re.match(r"^constructor\s+(\S+)", st)
            if m: exp.add(m.group(1))
            m = re.match(r"^(?:field\s+)?([^\s:(){}]+(?:\s+[^\s:(){}]+)*)\s+:(?!:)", st)
            if m: exp.update(x for x in m.group(1).split() if x != "field")
            continue
        m = re.match(r"^([^\s:(){}=|]+(?:\s+[^\s:(){}=|]+)*)\s+:(?!:)", st)
        if m:
            # ★ inside a `module X … where` block (not a function's `where`)
            #   a declaration is PART OF THE MODULE: `module _` puts it in
            #   the file's own scope, a named one behind `open X`.
            (MODBLOCK.setdefault(in_modblock, set()) if in_modblock not in (None, "_")
             else (exp if in_modblock == "_" else loc)).update(m.group(1).split())
    return {x for x in exp if x not in KEYWORDS}, {x for x in loc if x not in KEYWORDS}

# `module X … where` block name → the names declared in it, tree-wide
MODBLOCK = {}
MODPUB = {}          # block → blocks it re-exports with `open … public`

def modblock(x, seen=None):
    seen = seen or set()
    if x in seen: return set()
    seen.add(x)
    r = set(MODBLOCK.get(x, set()))
    for y in MODPUB.get(x, ()): r |= modblock(y, seen)
    return r

def bound_names(src):
    "every token in a BINDING position anywhere (over-approximated)"
    b = set()
    for m in re.finditer(r"[({]([^(){}:=]+?)\s:(?!:)", src):       # (x y : T) {x : T}
        b.update(TOK.findall(m.group(1)))
    for m in re.finditer(r"λ\s*(\{[^}]*\}|[^→]+)→", src):            # λ x y →
        b.update(TOK.findall(m.group(1)))
    for m in re.finditer(r"∀\s*(\{[^}]*\}|[^→,]+)", src):
        b.update(TOK.findall(m.group(1)))
    for l in src.split("\n"):                                         # clause LHS
        if " = " in l and not l.lstrip().startswith(("open", "import")):
            lhs = l.split(" = ")[0]
            b.update(TOK.findall(lhs))
        m = re.match(r"^\s*(\S+)\s+=", l)
        if m: b.add(m.group(1))
    for m in re.finditer(r"\bwith\b[^\n]*\n((?:\s*\.\.\.[^\n]*\n)+)", src):
        b.update(TOK.findall(m.group(1)))
    for m in re.finditer(r"^\s*\.\.\.\s*\|([^=\n]*)", src, re.M):
        b.update(TOK.findall(m.group(1)))
    return b

def load(files):
    mods = {}
    for f in files:
        raw = open(f, encoding="utf-8").read()
        src = strip_comments(raw)
        exp, loc = declared(src)
        mods[modname(f)] = dict(path=f, src=src, exp=exp, loc=loc,
                                imps=parse_imports(src))
    return mods

def exports(mods, name, seen=None):
    seen = seen or set()
    if name in seen or name not in mods: return set()
    seen.add(name)
    m = mods[name]; e = set(m["exp"])
    for (mod, opened, using, hiding, ren, public) in m["imps"]:
        if public and mod in mods:
            sub = exports(mods, mod, seen)
            if using is not None: sub = set(using) & sub
            e |= (sub - set(hiding)) | {b for _, b in ren}
    return e

def lint(mods, only=None):
    findings = []
    owner = {}
    for n, m in mods.items():
        for x in m["exp"]: owner.setdefault(x, set()).add(n)
    EXP = {n: exports(mods, n) for n in mods}
    for n, m in mods.items():
        if only and n not in only: continue
        scope = set(m["exp"]) | set(m["loc"])
        for (mod, opened, using, hiding, ren, public) in m["imps"]:
            if mod not in mods:                      # outside the project
                if opened:
                    scope |= set(using or []) | {b for _, b in ren}
                    if using is None: scope.add("*" + mod)
                continue
            e = EXP[mod]
            for x in (using or []) + hiding + [a for a, _ in ren]:
                if x.startswith("module "):
                    scope |= modblock(x.split()[1])
                    if x not in e and x.split()[1] not in MODBLOCK:
                        findings.append((m["path"], "W", "`%s` is not exported by %s" % (x, mod)))
                    continue
                if x not in e:
                    findings.append((m["path"], "W", "`%s` is not exported by %s" % (x, mod)))
            if opened:
                scope |= (set(using) if using is not None else (e - set(hiding)))
                scope |= {b for _, b in ren}
        # ★ the import lines are not USES — their module paths would read as
        #   names (`…Knot.Desc` → `Desc`).
        body = "\n".join(l for l in m["src"].split("\n")
                         if not re.match(r"^\s*(open\s+)?import\b", l)
                         and not re.match(r"^module\s+\S+\.\S+", l)
                         and not re.match(r"^\s+(using|hiding|renaming|;)", l))
        # ★ a QUALIFIED name (`Cx.ε`, `M.x`) is resolved through its
        #   qualifier, which this linter does not model — drop it.
        body = re.sub(r"[^\s(){};.@\"]+(\.[^\s(){};.@\"]+)+", " ", body)
        # ★ a local `open X …` of a named module block: its names are in scope;
        #   an `open` of something unknown makes the scope unknowable.
        for om in re.finditer(r"^\s*open\s+([^\s(]+)", body, re.M):
            nm_ = om.group(1).split(".")[-1]
            if nm_ in MODBLOCK: scope |= modblock(nm_)
            elif nm_ not in ("import",) and om.group(1) not in mods:
                scope.add("*" + nm_)
            elif om.group(1) in mods: scope |= EXP[om.group(1)]
        if any(x.startswith("*") for x in scope):
            continue      # an `open` of something unknowable: its names are invisible here
        bound = bound_names(body)
        for t in set(TOK.findall(body)):
            if t in scope or t in bound or t in KEYWORDS or not distinctive(t): continue
            own = owner.get(t)
            if not own or len(own) != 1 or n in own: continue
            (o,) = tuple(own)
            findings.append((m["path"], "E", "`%s` is used but not imported (defined in %s)" % (t, o)))
    return findings

def tree():
    fs = []
    for f in glob.glob(os.path.join(ROOT, "**", "*.agda"), recursive=True):
        if any(("/%s/" % d) in f for d in SKIP_DIRS): continue
        fs.append(f)
    return fs

def control():
    """Seed one error of each class into a scratch copy of a real module."""
    files = tree()
    mods = load(files)
    target = "DirectedHoTT.Examples.Knot.CtxD"
    src = open(mods[target]["path"], encoding="utf-8").read()
    # class 1: a name the imported module does not export
    bad1 = src.replace("using ( ⊢-cast; ⊢wk )", "using ( ⊢-cast; ⊢wk; noSuchLemmaXYZ )", 1)
    # class 2: drop an import that the body needs
    bad2 = bad1.replace("open import DirectedHoTT.Examples.Knot.Build using ( kCast; tmCast )\n", "", 1)
    assert bad1 != src and bad2 != bad1, "control anchors moved — update control()"
    tmpd = tempfile.mkdtemp()
    try:
        p = os.path.join(tmpd, "CtxD.agda"); open(p, "w").write(bad2)
        raw = strip_comments(bad2); exp, loc = declared(raw)
        mods[target] = dict(path=p, src=raw, exp=exp, loc=loc, imps=parse_imports(raw))
        got = lint(mods, only={target})
    finally:
        shutil.rmtree(tmpd)
    msgs = [w for _, _, w in got]
    ok1 = any("noSuchLemmaXYZ" in w for w in msgs)
    ok2 = any("`kCast`" in w or "`tmCast`" in w for w in msgs)
    print("control: seeded unexported name %s · seeded missing import %s"
          % ("CAUGHT" if ok1 else "MISSED", "CAUGHT" if ok2 else "MISSED"))
    return 0 if (ok1 and ok2) else 2

if __name__ == "__main__":
    if "--control" in sys.argv: sys.exit(control())
    files = tree()
    mods = load(files)
    fs = lint(mods)
    errs = [f for f in fs if f[1] == "E"]
    warns = [f for f in fs if f[1] == "W"]
    for p, sv, w in sorted(fs, key=lambda f: (f[1], f[0])):
        print("%s: %s %s" % (os.path.relpath(p, BOOT),
                             "ERROR" if sv == "E" else "warning", w))
    # ⚠ A NAME IN `using` THAT THE TARGET DOES NOT EXPORT IS ONLY A WARNING
    #   in Agda 2.8 (`ModuleDoesntExport`) — measured: `Examples/AbsProbe`
    #   imports `nrs` from `Spec.Syntax` and compiles.  So it does not
    #   block; what blocks is the USE of an unimported name (NotInScope).
    print("== lint-imports: %d module(s) read, %d error(s), %d warning(s)%s"
          % (len(mods), len(errs), len(warns), "" if errs else " — NO ERRORS"))
    sys.exit(1 if errs else 0)
