#!/usr/bin/env python3
"""
gen-judge.py — the `⊢` ROWS of the Knot's typing judgement (D077), from a
rule table.  Emits `Examples/Knot/JudgeRowsGen.agda`.

★ ONE SCHEME PER ROW (the hand-written ⊢lam/⊢app/⊢var are its templates,
  `Examples/Knot/JudgeRowsTm.agda`):

  * the premises are a PARAMETRIC telescope `T⊢xI Ps` over the positions it
    mentions (depth `J`, context `G`, conclusion `X`, the subject's fields
    `F…`, the type pattern's fields `Q…`, the existentials `E…`), with
      - its law `T⊢xI-sub` — one congruence (`T⊢xA-cong`, explicit
        arguments) over the telescope's ATOMS (`sub0`, `wk`, `DF`, a Ford
        code), each atom's own `-sub` lemma;
      - its congruence `T⊢xI-cong` (all positions);
      - its typing `okT⊢xI` at ANY context and positions;
  * the row's telescope `T⊢x j a b` puts the EXISTENTIALS in front as
    σ-fields (the positions are weakened past them; `JudgeCase.w1…w3`) —
    its law chains the σ-codes' laws with `T⊢xI-sub` and `T⊢xI-cong`;
  * a PLAIN row (`a b = p c`) is `defRow`; a CASE row (`a b = q (Γ , p)`,
    the conclusion type a pattern with fresh variables) is a `CaseRow`
    on the type's head.

★ WHEN A CASE, WHEN A FORD (D077): the conclusion type is a CASE when it is
  a constructor pattern whose variables are fresh (they are bound by the
  case — no existential, no equation); it is ONE FORD field when it is
  determined by the subject or computed (`El c`, `Hom (El c) t t`, `B[u]`).

The DSL — expressions:
  'J' 'G' 'X'            depth, context, conclusion type
  ('f', i) ('q', i)      the subject's / the type pattern's i-th field
  ('e', i)               the i-th existential
  ('k', name, a…)        a Knot former `k<name>` (`Sig`), fields by shape
  ('sub0', s, d, t, u)   t[u/0]            ('wk', s, d, t)  weakening
  ('DF', d, I)           DescF I           ('cext', g, A)   Γ ▹ A
  depths: 'J' | 'J+1' | 'J+2'
entries (in order; a Ford `id` last):
  ('ty', d, g, A)   ('tm', d, g, t, A)   ('id', ('Ty'|'Tm', d), a, b)
existentials: ('Ty', d) | ('Tm', d) | ('Nat',)

Usage:  python3 tools/gen-judge.py [--check]
"""
import os, sys, importlib.util

HERE = os.path.dirname(os.path.abspath(__file__))
spec = importlib.util.spec_from_file_location("genknot", os.path.join(HERE, "gen-knot.py"))
gk = importlib.util.module_from_spec(spec); spec.loader.exec_module(gk)

ROOT = gk.ROOT
OUT = os.path.join(ROOT, "Examples", "Knot", "JudgeRowsGen.agda")

# ------------------------------------------------------------ the signature
SIG = {}          # 'Pi' -> (sort, fields, index-in-sort)
TMHEADS = []      # term constructor names, in order
TYHEADS = []
def load_sig():
    idx = {"RTy": 0, "RTm": 0}
    for data, name, fs in gk.parse():
        n = gk.kname(name)[1:]
        SIG[n] = (gk.SORTS[data], fs, idx[data])
        (TYHEADS if data == "RTy" else TMHEADS).append(n)
        idx[data] += 1

def shape_name(n): return "sh-k" + n
def ok_name(n): return "ok-k" + n

# ------------------------------------------------------------ the rule table
S0, S1 = 0, 1
def tm(d, g, t, A): return ("tm", d, g, t, A)
def ty(d, g, A): return ("ty", d, g, A)
def k(n, *a): return ("k", n) + a
F = lambda i: ("f", i)
Q = lambda i: ("q", i)
E = lambda i: ("e", i)
U = k("U"); BASE = k("base"); NAT = k("Nat")
def El(c): return k("El", c)

RULES = {
  # head: dict(case=type-head | None, ex=[…], ents=[…])
  "pair":   dict(case="Sg", ents=[ty("J+1", ("cext", "G", Q(0)), Q(1)), tm("J", "G", F(0), Q(0)),
                                  tm("J", "G", F(1), ("sub0", 0, "J", Q(1), F(0)))]),
  "absurd": dict(ents=[tm("J", "G", F(0), U), tm("J", "G", F(1), BASE), ("id", ("Ty", "J"), "X", El(F(0)))]),
  "ordtr":  dict(ents=[tm("J", "G", F(0), NAT), tm("J", "G", F(1), NAT), tm("J", "G", F(2), NAT),
                       tm("J", "G", F(3), k("Hom", NAT, F(0), F(1))), tm("J", "G", F(4), k("Hom", NAT, F(1), F(2))),
                       ("id", ("Ty", "J"), "X", k("Hom", NAT, F(0), F(2)))]),
  "fst":    dict(ex=[("Ty", "J+1")], ents=[tm("J", "G", F(0), k("Sg", "X", E(0)))]),
  "snd":    dict(ex=[("Ty", "J"), ("Ty", "J+1")],
                 ents=[tm("J", "G", F(0), k("Sg", E(0), E(1))), ("id", ("Ty", "J"), "X", ("sub0", 0, "J", E(1), k("fst", F(0))))]),
  "cbase":  dict(case="U", ents=[]),
  "cPi":    dict(case="U", ents=[tm("J", "G", F(0), U), tm("J+1", ("cext", "G", El(F(0))), F(1), U)]),
  "cSg":    dict(case="U", ents=[tm("J", "G", F(0), U), tm("J+1", ("cext", "G", El(F(0))), F(1), U)]),
  "cHom":   dict(case="U", ents=[tm("J", "G", F(0), U), tm("J", "G", F(1), El(F(0))), tm("J", "G", F(2), El(F(0)))]),
  "hrefl":  dict(ents=[tm("J", "G", F(0), U), tm("J", "G", F(1), El(F(0))), ("id", ("Ty", "J"), "X", k("Hom", El(F(0)), F(1), F(1)))]),
  "cId":    dict(case="U", ents=[tm("J", "G", F(0), U), tm("J", "G", F(1), El(F(0))), tm("J", "G", F(2), El(F(0)))]),
  "idrefl": dict(ents=[tm("J", "G", F(0), U), tm("J", "G", F(1), El(F(0))), ("id", ("Ty", "J"), "X", k("Id", El(F(0)), F(1), F(1)))]),
  "jsub":   dict(ex=[("Ty", "J"), ("Tm", "J"), ("Tm", "J")],
                 ents=[tm("J+1", ("cext", "G", E(0)), F(0), U), tm("J", "G", E(1), E(0)), tm("J", "G", E(2), E(0)),
                       tm("J", "G", F(1), k("Id", E(0), E(1), E(2))), tm("J", "G", F(2), El(("sub0", 1, "J", F(0), E(1)))),
                       ("id", ("Ty", "J"), "X", El(("sub0", 1, "J", F(0), E(2))))]),
  "unit":   dict(case="Unit", ents=[]),
  "nzero":  dict(case="Nat", ents=[]),
  "nsuc":   dict(case="Nat", ents=[tm("J", "G", F(0), NAT)]),
  "con":    dict(case="IMu", ents=[tm("J", "G", Q(0), U), tm("J", "G", Q(1), ("DF", "J", Q(0))), tm("J", "G", Q(2), El(Q(0))),
                                   tm("J", "G", F(0), El(k("dpay", Q(0), Q(1), k("app", Q(1), Q(2)))))]),
  "dI":     dict(case="Desc", ents=[tm("J", "G", Q(0), U)]),
  "dS":     dict(case="Desc", ents=[tm("J", "G", Q(0), U), tm("J", "G", F(0), U),
                                    tm("J", "G", F(1), k("Pi", El(F(0)), k("Desc", ("wk", 1, "J", Q(0)))))]),
  "dR":     dict(case="Desc", ents=[tm("J", "G", Q(0), U), tm("J", "G", F(0), El(Q(0))), tm("J", "G", F(1), k("Desc", Q(0)))]),
  "dpay":   dict(case="U", ents=[tm("J", "G", F(0), U), tm("J", "G", F(1), ("DF", "J", F(0))), tm("J", "G", F(2), k("Desc", F(0)))]),
  "cNat":   dict(case="U", ents=[]),
  "cIMu":   dict(case="U", ents=[tm("J", "G", F(0), U), tm("J", "G", F(1), ("DF", "J", F(0))), tm("J", "G", F(2), El(F(0)))]),
  "cFin":   dict(case="U", ents=[]),
  "cUnit":  dict(case="U", ents=[]),
}
# the opaque operations (`Knot/SubEnv`): result `K 0 (d + out)`, argument sorts and depth offsets
OPS = {
  "nrsK":    dict(out=2, args=[(0, 1)]),
  "pairSK":  dict(out=2, args=[(0, 1)]),
  "fsucSK":  dict(out=1, args=[(0, 1)]),
  "iinstK":  dict(out=0, args=[(1, 0), (1, 0), (0, 2)]),
  "MethTyK": dict(out=0, args=[(1, 0), (1, 0), (0, 2)]),
}
def MC(d, g, I, D): return ("mc", d, g, I, D)
NSUC = lambda e: ("nsuc", e)
NZERO = ("nzero",)

RULES.update({
  "natrec": dict(ex=[("Ty", "J+1")],
                 ents=[ty("J+1", ("cext", "G", NAT), E(0)), tm("J", "G", F(0), ("sub0", 0, "J", E(0), k("nzero"))),
                       tm("J+2", ("cext", ("cext", "G", NAT), E(0)), F(1), ("nrsK", "J", E(0))), tm("J", "G", F(2), NAT),
                       ("id", ("Ty", "J"), "X", ("sub0", 0, "J", E(0), F(2)))]),
  "fcase":  dict(ex=[("Nat",), ("Ty", "J+1")],
                 ents=[ty("J+1", ("cext", "G", k("Fin", NSUC(E(0)))), E(1)), tm("J", "G", F(0), k("Fin", NSUC(E(0)))),
                       tm("J", "G", F(1), ("sub0", 0, "J", E(1), k("fzero"))),
                       tm("J+1", ("cext", "G", k("Fin", E(0))), F(2), ("fsucSK", "J", E(1))),
                       ("id", ("Ty", "J"), "X", ("sub0", 0, "J", E(1), F(0)))]),
  "fcase0": dict(ex=[("Ty", "J+1")],
                 ents=[ty("J+1", ("cext", "G", k("Fin", NZERO)), E(0)), tm("J", "G", F(0), k("Fin", NZERO)),
                       ("id", ("Ty", "J"), "X", ("sub0", 0, "J", E(0), F(0)))]),
  "psplit": dict(ex=[("Ty", "J"), ("Ty", "J+1"), ("Ty", "J+1")],
                 ents=[ty("J", "G", E(0)), ty("J+1", ("cext", "G", E(0)), E(1)), ty("J+1", ("cext", "G", k("Sg", E(0), E(1))), E(2)),
                       tm("J", "G", F(1), k("Sg", E(0), E(1))),
                       tm("J+2", ("cext", ("cext", "G", E(0)), E(1)), F(0), ("pairSK", "J", E(2))),
                       ("id", ("Ty", "J"), "X", ("sub0", 0, "J", E(2), F(1)))]),
  "ielim":  dict(ex=[("Tm", "J"), ("Ty", "J+2")],
                 ents=[tm("J", "G", E(0), U), tm("J", "G", F(0), ("DF", "J", E(0))), ty("J+2", MC("J", "G", E(0), F(0)), E(1)),
                       tm("J", "G", F(2), ("MethTyK", "J", E(0), F(0), E(1))), tm("J", "G", F(1), El(E(0))),
                       tm("J", "G", F(3), k("IMu", E(0), F(0), F(1))),
                       ("id", ("Ty", "J"), "X", ("iinstK", "J", F(1), F(3), E(1)))]),
  "dih":    dict(ex=[("Tm", "J"), ("Ty", "J+2")],
                 ents=[tm("J", "G", E(0), U), tm("J", "G", F(0), ("DF", "J", E(0))), ty("J+2", MC("J", "G", E(0), F(0)), E(1)),
                       tm("J", "G", F(1), ("MethTyK", "J", E(0), F(0), E(1))), tm("J", "G", F(2), k("Desc", E(0))),
                       tm("J", "G", F(3), El(k("dpay", E(0), F(0), F(2)))),
                       ("id", ("Ty", "J"), "X", k("DIh", F(0), E(1), F(2), F(3)))]),
})

HAND = {"var": ("rVar", "okVar"), "lam": ("rLam", "okLam"), "app": ("rApp", "okApp"), "fzero": ("rFz", "okFz"), "fsuc": ("rFs", "okFs")}

# ------------------------------------------------------------ rendering
def dep(d):
    return {"J": "J", "J+1": "(nsuc J)", "J+2": "(nsuc (nsuc J))"}[d]
def dnum(d):
    return {"J": 0, "J+1": 1, "J+2": 2}[d]
def dty(d):          # the depth's typing
    return {"J": "dJ", "J+1": "(⊢isuc dJ)", "J+2": "(⊢isuc (⊢isuc dJ))"}[d]
def pname(p):
    if p in ("J", "G", "X"): return p
    return {"f": "F", "q": "Q", "e": "E"}[p[0]] + str(p[1])

def is_param(e): return e in ("J", "G", "X") or (isinstance(e, tuple) and e[0] in ("f", "q", "e"))

class Row:
    def __init__(self, name, spec):
        self.n = name
        self.case = spec.get("case")
        self.ex = spec.get("ex", [])
        self.ents = spec["ents"]
        self.sort, self.fields, self.idx = SIG[name]
        assert self.sort == 1
        self.sh = shape_name(name)
        if self.case:
            self.tsort, self.tfields, self.tidx = SIG[self.case]
            assert self.tsort == 0
        self.atoms = []           # (kind, args) in order of appearance, deduplicated by rendering
        self.params = []
        for ent in self.ents: self.collect(ent)
        order = ["J", "G", "X"] + [("f", i) for i in range(len(self.fields))] \
              + [("q", i) for i in range(len(self.tfields) if self.case else 0)] + [("e", i) for i in range(len(self.ex))]
        used = set(self.params)
        self.params = [p for p in order if p in used]
        self.pfx = "T⊢" + name

    # every parameter and atom the entries mention
    def collect(self, x):
        if is_param(x):
            if x not in self.params: self.params.append(x)
            return
        if isinstance(x, str) and x.startswith("J"):
            if "J" not in self.params: self.params.append("J")
            return
        if not isinstance(x, tuple): return
        tag = x[0]
        if tag in ("ty", "tm"):
            for y in x[1:]: self.collect(y)
        elif tag == "id":
            self.collect(x[1][1]); self.collect(x[2]); self.collect(x[3])
            self.add_atom((x[1][0], (x[1][1],)))
        elif tag == "k":
            for y in x[2:]: self.collect(y)
        elif tag == "cext":
            self.collect(x[1]); self.collect(x[2])
        elif tag in ("sub0", "wk"):
            for y in x[2:]: self.collect(y)
            self.add_atom((tag, x[1:]))
        elif tag in OPS or tag in ("mc", "DF"):
            for y in x[1:]: self.collect(y)
            self.add_atom((tag, x[1:]))
        elif tag == "nsuc":
            self.collect(x[1])
        elif tag == "nzero":
            pass
        else:
            raise ValueError(x)

    def add_atom(self, a):
        if a not in self.atoms: self.atoms.append(a)

    # an expression; `atoms` renders atoms as their parameter names
    def expr(self, x, env, atoms=False):
        if is_param(x): return env[x]
        if isinstance(x, str): return {"J": env["J"], "J+1": "(nsuc %s)" % env["J"], "J+2": "(nsuc (nsuc %s))" % env["J"]}[x]
        tag = x[0]
        if tag == "k":
            args = " ".join(self.expr(y, env, atoms) for y in x[2:])
            return "(k%s%s)" % (x[1], (" " + args) if args else "")
        if tag == "cext":
            return "(cext %s %s)" % (self.expr(x[1], env, atoms), self.expr(x[2], env, atoms))
        if tag == "nsuc":
            return "(nsuc %s)" % self.expr(x[1], env, atoms)
        if tag == "nzero":
            return "nzero"
        if tag in ("sub0", "wk", "DF", "mc") or tag in OPS:
            key = (tag, x[1:])
            if atoms: return "A%d" % self.atoms.index(key)
            return self.atom_expr(key, env)
        raise ValueError(x)

    def atom_expr(self, a, env, sub=None):
        kind, args = a
        r = lambda y: self.expr(y, env) if sub is None else "(subTm %s %s)" % (sub, self.expr(y, env))
        if kind == "sub0": return "(sub0 %d %s %s %s)" % (args[0], r(args[1]), r(args[2]), r(args[3]))
        if kind == "wk":   return "(wk %d %s %s)" % (args[0], r(args[1]), r(args[2]))
        if kind == "DF":   return "(DF %s %s)" % (r(args[0]), r(args[1]))
        if kind == "Ty":   return "(⌜Ty⌝ %s)" % r(args[0])
        if kind == "Tm":   return "(⌜Tm⌝ %s)" % r(args[0])
        if kind in OPS or kind == "mc": return "(%s %s)" % (kind, " ".join(r(y) for y in args))
        raise ValueError(a)

    def atom_sub(self, a, env, sigma):
        kind, args = a
        r = lambda y: self.expr(y, env)
        if kind == "sub0": return "(sub0-sub %s %d %s %s %s)" % (sigma, args[0], r(args[1]), r(args[2]), r(args[3]))
        if kind == "wk":   return "(wk-sub %s %d %s %s)" % (sigma, args[0], r(args[1]), r(args[2]))
        if kind == "DF":   return "(DF-sub %s %s %s)" % (sigma, r(args[0]), r(args[1]))
        if kind == "Ty":   return "(⌜Ty⌝-sub %s %s)" % (sigma, r(args[0]))
        if kind == "Tm":   return "(⌜Tm⌝-sub %s %s)" % (sigma, r(args[0]))
        if kind in OPS or kind == "mc": return "(%s-sub %s %s)" % (kind, sigma, " ".join(r(y) for y in args))
        raise ValueError(a)

    # the telescope's Desc, atoms abstracted
    def tel(self, env, atoms):
        out = "tι"
        for ent in reversed(self.ents):
            if ent[0] == "ty":
                _, d, g, A = ent
                out = "tρ (tyIx %s %s %s) (%s)" % (self.expr(d, env, atoms), self.expr(g, env, atoms), self.expr(A, env, atoms), out)
            elif ent[0] == "tm":
                _, d, g, t, A = ent
                out = "tρ (tmIx %s %s %s %s) (%s)" % (self.expr(d, env, atoms), self.expr(g, env, atoms),
                                                      self.expr(t, env, atoms), self.expr(A, env, atoms), out)
            elif ent[0] == "id":
                _, code, a, b = ent
                assert out == "tι", "a Ford field is last"
                key = (code[0], (code[1],))
                c = ("A%d" % self.atoms.index(key)) if atoms else self.atom_expr(key, env)
                out = "tσ (⌜Id⌝ %s %s %s) tι" % (c, self.expr(a, env, atoms), self.expr(b, env, atoms))
        return out

    # ---- the typing synthesizer: an expression at a sort and depth
    def typ(self, x, s, d, denv):
        if is_param(x):
            return denv[x]
        tag = x[0]
        if tag == "k":
            srt, fs, _ = SIG[x[1]]
            assert srt == s, (x, s)
            ds = []
            for f, y in zip(fs, x[2:]):
                if f[0] == "nat":
                    ds.append(self.nattyp(y, denv)); continue
                assert f[0] == "rec", (x, f)
                ds.append(self.typ(y, f[1], plus(d, f[2]), denv))
            return "(⊢k%s %s%s)" % (x[1], dty(d), "".join(" " + q for q in ds))
        if tag == "sub0":
            _, s0, d0, t, u = x
            assert s0 == s and d0 == d
            return "(⊢sub0 %s %s %s %s)" % (gk.lt(s0), dty(d0), self.typ(t, s0, plus(d0, 1), denv), self.typ(u, 1, d0, denv))
        if tag == "wk":
            _, s0, d0, t = x
            assert s0 == s and plus(d0, 1) == d
            return "(⊢wkS %s %s %s)" % (gk.lt(s0), dty(d0), self.typ(t, s0, d0, denv))
        if tag == "DF":
            _, d0, I = x
            assert s == 0 and d0 == d
            return "(⊢DF %s %s)" % (dty(d0), self.typ(I, 1, d0, denv))
        if tag in OPS:
            sig = OPS[tag]
            d0 = x[1]
            assert s == 0 and plus(d0, sig["out"]) == d, (x, s, d)
            ds = [self.typ(y, srt, plus(d0, k), denv) for y, (srt, k) in zip(x[2:], sig["args"])]
            return "(⊢%s %s%s)" % (tag, dty(d0), "".join(" " + q for q in ds))
        raise ValueError(x)

    def nattyp(self, x, denv):
        if is_param(x): return denv[x]
        if x[0] == "nsuc": return "(⊢isuc %s)" % self.nattyp(x[1], denv)
        if x[0] == "nzero": return "(toI ⊢nzero)"
        raise ValueError(x)

    def ctxtyp(self, g, d, denv):
        if g == "G": return denv["G"]
        if g[0] == "mc":
            _, d0, g0, I, D = g
            assert plus(d0, 2) == d
            return "(⊢mc %s %s %s %s)" % (dty(d0), self.ctxtyp(g0, d0, denv), self.typ(I, 1, d0, denv), self.typ(D, 1, d0, denv))
        assert g[0] == "cext"
        dm = minus1(d)
        return "(⊢cext %s %s %s)" % (dty(dm), self.ctxtyp(g[1], dm, denv), self.typ(g[2], 0, dm, denv))

def plus(d, n):
    v = dnum(d) + n
    return ["J", "J+1", "J+2"][v]
def minus1(d):
    return ["J", "J+1", "J+2"][dnum(d) - 1]

# ------------------------------------------------------------ one row
def pty(row, p):
    """a position's type, for the generic typing"""
    if p == "J": return "El ⌜Nat⌝"
    if p == "G": return "KCtx J"
    if p == "X": return "K 0 J"
    if p[0] in ("f", "q"):
        fs = row.fields if p[0] == "f" else row.tfields
        f = fs[p[1]]
        assert f[0] == "rec", (row.n, p, f)
        return "K %d %s" % (f[1], dep(["J", "J+1", "J+2"][f[2]]))
    if p[0] == "e":
        c = row.ex[p[1]]
        if c[0] == "Ty": return "K 0 %s" % dep(c[1])
        if c[0] == "Tm": return "K 1 %s" % dep(c[1])
        return "El ⌜Nat⌝"
    raise ValueError(p)

def gen_row(row):
    L = []
    P = row.params
    pn = [pname(p) for p in P]
    env = {p: pname(p) for p in P}
    na = len(row.atoms)
    an = ["A%d" % i for i in range(na)]
    I, A = row.pfx + "I", row.pfx + "A"
    L.append("-- ⊢%s" % row.n)
    # the parametric telescope, atoms abstracted, and with its atoms
    L.append("%s : %sTel Δ" % (A, "RTm Δ → " * (len(P) + na)))
    L.append("%s %s = %s" % (A, " ".join(pn + an), row.tel(env, True)) if P or na else "%s = %s" % (A, row.tel(env, True)))
    L.append("")
    L.append("%s : %sTel Δ" % (I, "RTm Δ → " * len(P)))
    atomvals = " ".join(row.atom_expr(a, env) for a in row.atoms)
    L.append("%s%s = %s%s" % (I, "".join(" " + q for q in pn), A, "".join(" " + q for q in pn) + ((" " + atomvals) if na else "")))
    L.append("")
    # the atom congruence
    L.append("%s-cong : {Δ : Cx} → %s%s⌜ %s ⌝ᵗ ≡ ⌜ %s ⌝ᵗ" % (A,
        "".join("(%s : RTm Δ) → " % q for q in pn) + "".join("(%s %s' : RTm Δ) → " % (a, a) for a in an),
        "".join("%s ≡ %s' → " % (a, a) for a in an),
        " ".join([A + " {Δ}"] + pn + an), " ".join([A] + pn + [a + "'" for a in an])))
    L.append("%s-cong %s%s = refl" % (A, " ".join(pn + [x for a in an for x in (a, a + "'")]), "".join(" refl" for _ in an)))
    L.append("")
    # the law
    L.append("%s-sub : (σ : Sub Δ Θ)%s → subTm σ ⌜ %s ⌝ᵗ ≡ ⌜ %s ⌝ᵗ" % (I,
        "".join(" (%s : RTm Δ)" % q for q in pn) if pn else "", " ".join([I] + pn),
        " ".join([I] + ["(subTm σ %s)" % q for q in pn])))
    if na:
        senv = {p: "(subTm σ %s)" % pname(p) for p in P}
        L.append("%s-sub σ%s = %s-cong %s %s %s" % (I, "".join(" " + q for q in pn), A,
            " ".join("(subTm σ %s)" % q for q in pn),
            " ".join("(subTm σ %s) %s" % (row.atom_expr(a, env), row.atom_expr(a, senv)) for a in row.atoms),
            " ".join(row.atom_sub(a, env, "σ") for a in row.atoms)))
    else:
        L.append("%s-sub σ%s = refl" % (I, "".join(" " + q for q in pn)))
    L.append("")
    # the congruence
    L.append("%s-cong : {Δ : Cx} → %s⌜ %s ⌝ᵗ ≡ ⌜ %s ⌝ᵗ" % (I,
        "".join("(%s %s' : RTm Δ) → " % (q, q) for q in pn) + "".join("%s ≡ %s' → " % (q, q) for q in pn),
        " ".join([I + " {Δ}"] + pn), " ".join([I] + [q + "'" for q in pn])))
    L.append("%s-cong %s%s = refl" % (I, " ".join(x for q in pn for x in (q, q + "'")), "".join(" refl" for _ in pn)))
    L.append("")
    # the generic typing
    denv = {p: "d" + pname(p) for p in P}
    denv_ctx = dict(denv)
    L.append("ok%s : {Ξ : Ctx}%s → %sTelOK Ξ JT (%s)" % (I,
        (" {%s : RTm ⌊ Ξ ⌋}" % " ".join(pn)) if pn else "",
        "".join("Ξ ⊢ %s ∷ %s → " % (pname(p), pty(row, p)) for p in P),
        " ".join([I] + pn)))
    body = "ok-ι"
    for ent in reversed(row.ents):
        if ent[0] == "ty":
            _, d, g, Aa = ent
            body = "ok-ρ (⊢tyIx %s %s %s) (%s)" % (dty(d), row.ctxtyp(g, d, denv), row.typ(Aa, 0, d, denv), body)
        elif ent[0] == "tm":
            _, d, g, t, Aa = ent
            body = "ok-ρ (⊢tmIx %s %s %s %s) (%s)" % (dty(d), row.ctxtyp(g, d, denv), row.typ(t, 1, d, denv), row.typ(Aa, 0, d, denv), body)
        elif ent[0] == "id":
            _, code, a, b = ent
            srt = 0 if code[0] == "Ty" else 1
            to = "toTy" if srt == 0 else "toTm"
            body = "ok-σ (⊢⌜Id⌝ (⊢⌜%s⌝ %s) (%s %s) (%s %s)) ok-ι" % (code[0], dty(code[1]),
                to, row.typ(a, srt, code[1], denv), to, row.typ(b, srt, code[1], denv))
    L.append("ok%s%s = %s" % (I, "".join(" d" + q for q in pn), body.replace("dJ", "dJ")))
    L.append("")
    return L


# ------------------------------------------------------------ stage 2: the row
def var(m):
    t = "vz"
    for _ in range(m): t = "(vs %s)" % t
    return t

def wN(i, x):
    return x if i == 0 else "(w%d %s)" % (i, x)

def extS(i, sig="σ"):
    t = sig
    for _ in range(i): t = "(extS %s)" % t
    return t

def fieldexpr(P, i):
    t = P
    for _ in range(i): t = "(snd %s)" % t
    return "(fst %s)" % t

def shape_expr(fs):
    return "(" + gk.shape(fs) + ")"

def gen_assembly(row):
    L = []
    P = row.params
    n = len(row.ex)
    N, I = row.pfx, row.pfx + "I"
    case = row.case is not None
    a, b = ("q", "c") if case else ("p", "c")
    payload = "(snd c)" if case else "p"
    # the positions' values at the outer context
    def src(p):
        if p == "J": return "j"
        if p == "G": return "(fst c)"
        if p == "X": return "(snd c)"
        if p[0] == "f": return fieldexpr(payload, p[1])
        if p[0] == "q": return fieldexpr("q", p[1])
        raise ValueError(p)
    def arg(p, lvl, sub=None):
        if p[0] == "e" if isinstance(p, tuple) else False:
            return "(var %s)" % var(lvl - 1 - p[1])
        v = src(p)
        if sub: v = v.replace("(fst c)", "(fst (subTm σ c))").replace("(snd c)", "(snd (subTm σ c))")
        if sub and v == "j": v = "(subTm σ j)"
        if sub and p[0] in ("f", "q") if isinstance(p, tuple) else False:
            base = "(subTm σ %s)" % ("c" if case and p[0] == "f" else ("q" if p[0] == "q" else "p"))
            v = fieldexpr("(snd %s)" % base if (case and p[0] == "f") else base, p[1])
        return wN(lvl, v)
    def code(i, sub=False):
        c = row.ex[i]
        jj = wN(i, "(subTm σ j)" if sub else "j")
        if c[0] == "Nat": return "⌜Nat⌝"
        d = {"J": jj, "J+1": "(nsuc %s)" % jj, "J+2": "(nsuc (nsuc %s))" % jj}[c[1]]
        return "(⌜%s⌝ %s)" % (c[0], d)
    def tel_from(i, sub=False):
        body = "(%s %s)" % (I, " ".join(arg(p, n, sub) for p in P)) if P else I
        for m in reversed(range(i, n)):
            body = "(tσ %s %s)" % (code(m, sub), body)
        return body
    L.append("%s : RTm Δ → RTm Δ → RTm Δ → Tel Δ" % N)
    L.append("%s j %s %s = %s" % (N, a, b, tel_from(0)))
    L.append("")
    # the law
    L.append("%s-law : TelLaw %s" % (N, N))
    argsσ = " ".join("(subTm %s %s)" % (extS(n), arg(p, n)) for p in P)
    args2 = " ".join(arg(p, n, True) for p in P)
    def argproof(p):
        if isinstance(p, tuple) and p[0] == "e": return "refl"
        if n == 0: return "refl"
        v = src(p)
        return "(w%d-sub σ %s)" % (n, v)
    if n == 0:
        L.append("%s-law σ j %s %s = %s-sub σ %s" % (N, a, b, I, " ".join(arg(p, 0) for p in P)) if P else
                 "%s-law σ j %s %s = %s-sub σ" % (N, a, b, I))
    else:
        body_l = "(subTm %s ⌜ %s ⌝ᵗ)" % (extS(n), "%s %s" % (I, " ".join(arg(p, n) for p in P)) if P else I)
        body_r = "⌜ %s ⌝ᵗ" % ("%s %s" % (I, args2) if P else I)
        bproof = "(trans (%s-sub %s %s) (%s-cong %s))" % (I, extS(n), " ".join(arg(p, n) for p in P),
                  I, " ".join("(subTm %s %s) %s" % (extS(n), arg(p, n), arg(p, n, True)) for p in P) + " " +
                  " ".join(argproof(p) for p in P)) if P else "(%s-sub %s)" % (I, extS(n))
        cs = []
        for i in range(n):
            c = row.ex[i]
            lhs = "(subTm %s %s)" % (extS(i), code(i))
            rhs = code(i, True)
            if c[0] == "Nat": pr = "refl"
            elif i == 0: pr = "(⌜%s⌝-sub σ %s)" % (c[0], code(0)[len("(⌜Ty⌝ "):-1])
            else:
                d0 = code(i)[len("(⌜Ty⌝ "):-1]
                lam = {"J": "z", "J+1": "(nsuc z)", "J+2": "(nsuc (nsuc z))"}[c[1]]
                pr = "(trans (⌜%s⌝-sub %s %s) (cong (λ z → ⌜%s⌝ %s) {x = subTm %s (w%d j)} {y = w%d (subTm σ j)} (w%d-sub σ j)))" % (
                      c[0], extS(i), d0, c[0], lam, extS(i), i, i, i)
            cs.append((lhs, rhs, pr))
        L.append("%s-law σ j %s %s =" % (N, a, b))
        L.append("  dσ%s-cong %s %s %s %s" % ("¹²³"[n - 1], " ".join("%s %s" % (l, r) for l, r, _ in cs), body_l, body_r,
                                             " ".join(pr for _, _, pr in cs) + " " + bproof))
    L.append("")
    return L

# ------------------------------------------------------------ stage 3: the row, typed
def gen_rowtyped(row):
    L = []
    P = row.params
    n = len(row.ex)
    N, I = row.pfx, row.pfx + "I"
    nm = row.n
    case = row.case is not None
    a = "q" if case else "p"
    S = "(pair (tag 1) j)"
    # contexts along the σ-prefix
    def code_at(i):
        c = row.ex[i]
        jj = wN(i, "j")
        if c[0] == "Nat": return "⌜Nat⌝"
        d = {"J": jj, "J+1": "(nsuc %s)" % jj, "J+2": "(nsuc (nsuc %s))" % jj}[c[1]]
        return "(⌜%s⌝ %s)" % (c[0], d)
    ctx = ["Ξ"]
    for i in range(n): ctx.append("(%s ▹ El %s)" % (ctx[-1], code_at(i)))
    payload = "(snd c)" if case else "p"
    def src(p):
        if p == "J": return "j"
        if p == "G": return "(fst c)"
        if p == "X": return "(snd c)"
        if p[0] == "f": return fieldexpr(payload, p[1])
        if p[0] == "q": return fieldexpr("q", p[1])
    # a position's typing at the outer context
    dP = "(⊢pI %s dc)" % row.sh if case else "dp"
    def fieldtyp(fs, base, S, i):
        d = base
        for m in range(i):
            f = fs[m]
            assert f[0] == "rec"
            d = "(⊢recSnd {s = %d} {k = %d} {sh = %s} %s)" % (f[1], f[2], shape_expr(fs[m + 1:]), d)
        f = fs[i]
        assert f[0] == "rec", (row.n, fs, i)
        return "(⊢atDepth {a = tag %d} {j = j} {s = %d} {k = %d} (⊢recFst {s = %d} {k = %d} {sh = %s} %s))" % (
            S, f[1], f[2], f[1], f[2], shape_expr(fs[i + 1:]), d)
    def styp(p):
        if p == "J": return "dj"
        if p == "G": return "(⊢gI %s dc)" % row.sh if case else "(⊢ctxOf dc)"
        if p == "X": return "(⊢tyOf dc)"
        if p[0] == "f": return fieldtyp(row.fields, dP, 1, p[1])
        if p[0] == "q": return fieldtyp(row.tfields, "dq", 0, p[1])
    def kind(p):
        if p == "J": return ("nat",)
        if p == "G": return ("ctx",)
        if p == "X": return ("K", 0, "j")
        fs = row.fields if p[0] == "f" else row.tfields
        f = fs[p[1]]
        return ("K", f[1], {0: "j", 1: "(nsuc j)", 2: "(nsuc (nsuc j))"}[f[2]])
    def weaken(kd, term, typ, frm, to):
        for i in range(frm, to):
            B = "El %s" % code_at(i)
            if kd[0] == "nat":
                typ = "(⊢wk {%s} {%s} {%s} {El ⌜Nat⌝} %s)" % (ctx[i], B, wN(i, term), typ)
            elif kd[0] == "ctx":
                typ = "(⊢wkCtx {%s} {%s} {%s} {%s} %s)" % (ctx[i], B, wN(i, "j"), wN(i, term), typ)
            else:
                typ = "(⊢wkSK {Γ = %s} {B = %s} {sg = KSig} {s = %d} {d = %s} {t = %s} %s)" % (
                    ctx[i], B, kd[1], wN(i, kd[2]), wN(i, term), typ)
        return typ
    def ptyp(p):
        if isinstance(p, tuple) and p[0] == "e":
            m = p[1]; c = row.ex[m]
            jj = wN(m, "j")
            if c[0] == "Nat":
                base, kd, term = "(⊢var here)", ("nat",), None
                return weaken(("nat",), "(var vz)", "(⊢var {%s} here)" % ctx[m + 1], m + 1, n) if False else \
                       weaken_var(m, ("nat",), "(⊢var here)")
            d = {"J": jj, "J+1": "(nsuc %s)" % jj, "J+2": "(nsuc (nsuc %s))" % jj}[c[1]]
            here = "(here%s {%s} {%s})" % (c[0], ctx[m], d)
            srt = 0 if c[0] == "Ty" else 1
            return weaken_var(m, ("K", srt, d), here)
        return weaken(kind(p), src(p), styp(p), 0, n)
    def weaken_var(m, kd, typ):
        # the m-th existential, `var vz` at level m+1, weakened to level n
        term = "(var vz)"
        for i in range(m + 1, n):
            B = "El %s" % code_at(i)
            if kd[0] == "nat":
                typ = "(⊢wk {%s} {%s} {%s} {El ⌜Nat⌝} %s)" % (ctx[i], B, term, typ)
            else:
                typ = "(⊢wkSK {Γ = %s} {B = %s} {sg = KSig} {s = %d} {d = %s} {t = %s} %s)" % (
                    ctx[i], B, kd[1], wN(i - m - 1, "(renTm vs %s)" % kd[2]) if True else "", term, typ)
            term = "(renTm vs %s)" % term
        return typ
    def argn(p):
        if isinstance(p, tuple) and p[0] == "e": return "(var %s)" % var(n - 1 - p[1])
        return wN(n, src(p))
    inner = "okT⊢%sI {%s}%s%s" % (nm, ctx[n], "".join(" {%s}" % argn(p) for p in P), "".join(" " + ptyp(p) for p in P))
    if case:
        sig = "Ξ ⊢ q ∷ PayV %s (pair (tag 0) j) (SI 2) (SD KSig) → Ξ ⊢ c ∷ El (CIat %s (pair (tag 0) j))" % (
            shape_name(row.case), row.sh)
        srcs = "dj dq dc"
    else:
        sig = "Ξ ⊢ p ∷ PayV %s %s (SI 2) (SD KSig) → Ξ ⊢ c ∷ El (CTat %s)" % (row.sh, S, S)
        srcs = "dj dp dc"
    L.append("ok%s : {Ξ : Ctx} {j %s c : RTm ⌊ Ξ ⌋} → Ξ ⊢ j ∷ El ⌜Nat⌝ → %s → TelOK Ξ JT (%s j %s c)" % (N, a, sig, N, a))
    # the telescopes after i σ-fields
    def T_at(i):
        body = "(%s %s)" % (I, " ".join(argn(p) for p in P)) if P else I
        for m in reversed(range(i, n)):
            body = "(tσ %s %s)" % (code_at(m), body)
        return body
    expr = "(%s)" % inner
    for i in reversed(range(n)):
        dj_i = weaken(("nat",), "j", "dj", 0, i)
        c = row.ex[i]
        if c[0] == "Nat": dC = "⊢⌜Nat⌝"
        else:
            dd = {"J": dj_i, "J+1": "(⊢isuc %s)" % dj_i, "J+2": "(⊢isuc (⊢isuc %s))" % dj_i}[c[1]]
            dC = "(⊢⌜%s⌝ %s)" % (c[0], dd)
        expr = "(ok-σ %s (subst (λ Y → TelOK %s Y %s) (sym (JT-ren vs)) %s))" % (dC, ctx[i + 1], T_at(i + 1), expr)
    L.append("ok%s {Ξ} {j} {%s} {c} %s = %s" % (N, a, srcs, expr))
    L.append("")
    if case:
        h = SIG[row.case][2]
        L.append("r%sI : Row" % N)
        L.append("r%sI = defRow₀ %s %s-law" % (N, N, N))
        L.append("module P%s = CaseRow %s %s %d r%sI" % (N, row.sh, ok_name(nm), h, N))
        L.append("okC%sI : P%s.RowOK 0 %s r%sI" % (N[1:], N, shape_name(row.case), N))
        L.append("okC%sI {Ξ} {j} {q} {c} dj dq dc = ⊢tel {Ξ} {JT} {%s j q c} ⊢JT (ok%s dj dq dc)" % (N[1:], N, N))
        L.append("r⊢%s : Row" % nm)
        L.append("r⊢%s = P%s.rX" % (nm, N))
        L.append("ok⊢%s : RowOK 1 %s r⊢%s" % (nm, row.sh, nm))
        L.append("ok⊢%s = P%s.okX okC%sI" % (nm, N, N[1:]))
    else:
        L.append("r⊢%s : Row" % nm)
        L.append("r⊢%s = defRow %s %s-law" % (nm, N, N))
        L.append("ok⊢%s : RowOK 1 %s r⊢%s" % (nm, row.sh, nm))
        L.append("ok⊢%s {Ξ} {j} {p} {c} dj dp dc = ⊢rows {Ξ} {JT} {1} {⌜ %s j p c ⌝ᵗ ∷ []} ⊢JT (⊢tel {Ξ} {JT} {%s j p c} ⊢JT (ok%s dj dp dc) ∷ᵈ []ᵈ)" % (nm, N, N, N))
    L.append("")
    return L

def gen_table():
    L = ["------------------------------------------------------------------------",
         "-- ★ THE `⊢` ROW TABLE, by term head (all 38; `rNone` = not yet a row)",
         "------------------------------------------------------------------------", "",
         "rowTmGen : ℕ → Row"]
    for i, h in enumerate(TMHEADS):
        if h in HAND: r = HAND[h][0]
        elif h in RULES: r = "r⊢" + h
        else: r = "rNone"
        L.append("rowTmGen %s = %s   -- %s" % (gk.nat(i), r, h))
    L.append("rowTmGen _ = rNone")
    L.append("")
    L.append("okTmGen : {k : ℕ} {sh : Shape} → NthSh TmShs k sh → RowOK 1 sh (rowTmGen k)")
    for i, h in enumerate(TMHEADS):
        nth = "nthʰ-z"
        for _ in range(i): nth = "(nthʰ-s %s)" % nth
        if h in HAND: o = HAND[h][1]
        elif h in RULES: o = "ok⊢" + h
        else: o = "okNone {1} {%s}" % shape_name(h)
        L.append("okTmGen %s = %s" % (nth, o))
    return L

# ------------------------------------------------------------ the side-condition families
# A predicate on codes (sort 1), fibred by the code's head; a row is a list of
# recursive premises `(field, depth-offset)` into the same predicate.
PREDS = {
  "NNC":  dict(doc="NoNatC c — no ⌜Nat⌝ along the Π-codomain / Hom-ambient spine (Spec/Variance)",
               rows={"cbase": [], "cUnit": [], "cFin": [], "cSg": [], "cId": [],
                     "cPi": [(1, 1)], "cHom": [(0, 0)]}),
  "StkA": dict(doc="stkA? c ≡ true — a stable ambient (Spec/Variance)",
               rows={"cbase": [], "cSg": [], "cId": [], "cUnit": [], "cFin": [], "cNat": [], "cIMu": [],
                     "cHom": [(0, 0)]}),
}

def gen_preds():
    L = [PHDR]
    for P, spec in PREDS.items():
        L.append("------------------------------------------------------------------------")
        L.append("-- ★ %s" % spec["doc"])
        L.append("------------------------------------------------------------------------")
        L.append("")
        L.append("module %sₘ = SynFam KOK (λ {Δ} → ⌜Unit⌝ {Δ ∙}) (λ σ → refl) ⊢⌜Unit⌝" % P)
        L.append("")
        # the index of a recursive premise at depth `j + k`
        L.append("ix%s : RTm Δ → RTm Δ → RTm Δ" % P)
        L.append("ix%s d c = %sₘ.ixJ (pair (tag 1) d) c unit" % (P, P))
        L.append("")
        L.append("⊢ix%s : {Ξ : Ctx} {d c : RTm ⌊ Ξ ⌋} → Ξ ⊢ d ∷ El ⌜Nat⌝ → Ξ ⊢ c ∷ K 1 d → Ξ ⊢ ix%s d c ∷ El %sₘ.J" % (P, P, P))
        L.append("⊢ix%s dd dc = %sₘ.⊢ixJ (⊢ix (lt-s lt-z) dd) dc (⊢conv ⊢unit (csymᵀ (credᵀ El-⌜Unit⌝)))" % (P, P))
        L.append("")
        for h, prems in spec["rows"].items():
            sh = shape_name(h)
            fs = SIG[h][1]
            nm = "%s⊢%s" % (P, h)
            def fld(i):
                t = "p"
                for _ in range(i): t = "(snd %s)" % t
                return "(fst %s)" % t
            def dep(k):
                t = "j"
                for _ in range(k): t = "(nsuc %s)" % t
                return t
            tel = "tι"
            for (f, k) in reversed(prems):
                tel = "tρ (ix%s %s %s) (%s)" % (P, dep(k), fld(f), tel)
            L.append("T%s : RTm Δ → RTm Δ → RTm Δ → Tel Δ" % nm)
            L.append("T%s j p c = %s" % (nm, tel))
            L.append("")
            L.append("r%s : Row" % nm)
            L.append("r%s = defRow T%s (λ σ j p c → refl)" % (nm, nm))
            L.append("")
            L.append("ok%s : %sₘ.RowOK 1 %s r%s" % (nm, P, sh, nm))
            body = "ok-ι"
            for (f, k) in reversed(prems):
                ftyp = "(g0 {j = j} {p = p} %d %d %s %s)" % (fs[f][1], fs[f][2], "[]ʰ", "dp") if f == 0 and len(fs) == 1 else None
                # the field's typing, through the payload's view
                d = "dp"
                for m in range(f):
                    d = "(⊢recSnd {s = %d} {k = %d} {sh = %s} %s)" % (fs[m][1], fs[m][2], shape_expr(fs[m + 1:]), d)
                ftyp = "(⊢atDepth {a = tag 1} {j = j} {s = %d} {k = %d} (⊢recFst {s = %d} {k = %d} {sh = %s} %s))" % (
                    fs[f][1], fs[f][2], fs[f][1], fs[f][2], shape_expr(fs[f + 1:]), d)
                ddep = "dj"
                for _ in range(k): ddep = "(⊢isuc %s)" % ddep
                body = "ok-ρ (⊢ix%s %s %s) (%s)" % (P, ddep, ftyp, body)
            L.append("ok%s {Ξ} {j} {p} {c} dj dp dc = ⊢rows {Ξ} {%sₘ.J} {1} {⌜ T%s j p c ⌝ᵗ ∷ []} %sₘ.⊢J (⊢tel {Ξ} {%sₘ.J} {T%s j p c} %sₘ.⊢J (%s) ∷ᵈ []ᵈ)" % (
                nm, P, nm, P, P, nm, P, body))
            L.append("")
        # the table
        L.append("%sNone : Row" % P)
        L.append("%sNone = record { R = λ j p c → rows [] ; R-sub = λ σ j p c → refl }" % P)
        L.append("")
        L.append("row%s : ℕ → ℕ → Row" % P)
        for i, h in enumerate(TMHEADS):
            if h in spec["rows"]:
                L.append("row%s (suc zero) %s = r%s⊢%s" % (P, gk.nat(i), P, h))
        L.append("row%s _ _ = %sNone" % (P, P))
        L.append("")
        L.append("ok%sNone : {s : ℕ} {sh : Shape} → %sₘ.RowOK s sh %sNone" % (P, P, P))
        L.append("ok%sNone dj dp dc = ⊢rows {I = %sₘ.J} {Cs = []} %sₘ.⊢J []ᵈ" % (P, P, P))
        L.append("")
        L.append("rowOK%s : {s c k : ℕ} {shs : Shapes c} {sh : Shape} → NthG KSig s shs → NthSh shs k sh → %sₘ.RowOK s sh (row%s s k)" % (P, P, P))
        L.append("rowOK%s {sh = sh} nthᵍ-z nh = ok%sNone {0} {sh}" % (P, P))
        for i, h in enumerate(TMHEADS):
            nth = "nthʰ-z"
            for _ in range(i): nth = "(nthʰ-s %s)" % nth
            o = ("ok%s⊢%s" % (P, h)) if h in spec["rows"] else ("ok%sNone {1} {%s}" % (P, shape_name(h)))
            L.append("rowOK%s (nthᵍ-s nthᵍ-z) %s = %s" % (P, nth, o))
        L.append("")
        L.append("module %sF = %sₘ.Family row%s rowOK%s" % (P, P, P, P))
        L.append("")
        L.append("-- the predicate at a code `c : K 1 d`")
        L.append("K%s : RTm Δ → RTm Δ → RTy Δ" % P)
        L.append("K%s d c = %sF.KF (ix%s d c)" % (P, P, P))
        L.append("")
    return L

PHDR = """------------------------------------------------------------------------
-- ⚠⚠ GENERATED by tools/gen-judge.py — DO NOT EDIT BY HAND. ⚠⚠
--
-- The side conditions of the kernel's rules as LOWER-STRATUM families
-- (D077): predicates on codes, fibred by the code's head (`Lib/SynFam`,
-- trivial convoy).  A premise `NoNatC c` is a σ-field of its code.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Knot.Preds where

open import normalizer.Syntax.Types using ( _≡_; refl )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax hiding ( Fin )
open import DirectedHoTT.Spec.Typing hiding ( _×_; _,,_ )
open import DirectedHoTT.Lib.Sugar using ( Cons; []; _∷_; tag; lt-z; lt-s; []ᵈ; _∷ᵈ_ )
open import DirectedHoTT.Lib.SynView using ( PayV; ⊢recFst; ⊢recSnd; ⊢atDepth )
open import DirectedHoTT.Lib.FinFam using ( ⊢isuc )
open import DirectedHoTT.Lib.Tel
open import DirectedHoTT.Lib.Syn
open import DirectedHoTT.Lib.SynFib using ( Row )
open import DirectedHoTT.Lib.SynFam using ( module SynFam )
open import DirectedHoTT.Examples.Knot.Sig
open import DirectedHoTT.Examples.Knot.Lookup using ( rows; ⊢rows )
open import DirectedHoTT.Examples.Knot.JudgeIx using ( defRow )

private
  variable
    Δ Θ : Cx
"""

def main():
    load_sig()
    L = [HDR]
    for name, spec in RULES.items():
        row = Row(name, spec)
        L += gen_row(row)
        L += gen_assembly(row)
        L += gen_rowtyped(row)
    L += gen_table()
    txt = "\n".join(L) + "\n"
    ptxt = "\n".join(gen_preds()) + "\n"
    POUT = os.path.join(ROOT, "Examples", "Knot", "Preds.agda")
    if "--check" in sys.argv:
        old = open(OUT, encoding="utf-8").read() if os.path.exists(OUT) else ""
        pold = open(POUT, encoding="utf-8").read() if os.path.exists(POUT) else ""
        if old != txt or pold != ptxt:
            print("STALE: %s / %s" % (OUT, POUT)); sys.exit(1)
        print("ok"); return
    open(OUT, "w", encoding="utf-8").write(txt)
    open(POUT, "w", encoding="utf-8").write(ptxt)
    print("wrote %s, %s" % (OUT, POUT))

HDR = """------------------------------------------------------------------------
-- ⚠⚠ GENERATED by tools/gen-judge.py — DO NOT EDIT BY HAND. ⚠⚠
--
-- The Knot's `⊢` rows (D077), one scheme per row; see the generator's
-- header.  The hand-written ⊢lam/⊢app/⊢var (`JudgeRowsTm`) are its templates.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Knot.JudgeRowsGen where

open import normalizer.Syntax.Types using ( _≡_; refl; sym; trans; cong; cong₂; subst )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax hiding ( Fin )
open import DirectedHoTT.Spec.Typing hiding ( _×_; _,,_ )
open import DirectedHoTT.Metatheory.TySub using ( ⊢wk )
open import DirectedHoTT.Lib.Sugar using ( Cons; []; _∷_; tag; Lt; lt-z; lt-s; []ᵈ; _∷ᵈ_ )
open import DirectedHoTT.Lib.SynView using ( PayV; ⊢recFst; ⊢recSnd; ⊢atDepth )
open import DirectedHoTT.Lib.FinFam using ( ⊢isuc; toI )
open import DirectedHoTT.Lib.Tel
open import DirectedHoTT.Lib.Syn
open import DirectedHoTT.Lib.SynFib using ( Row )
open import DirectedHoTT.Examples.Knot.Ctors
open import DirectedHoTT.Examples.Knot.Sig
open import DirectedHoTT.Examples.Knot.Ctx
open import DirectedHoTT.Examples.Knot.Lookup using ( rows; ⊢rows; toTy; hereTy )
open import DirectedHoTT.Examples.Knot.Sub using ( sub0; ⊢sub0; sub0-sub )
open import DirectedHoTT.Examples.Knot.Ren using ( wk; ⊢wkS; wk-sub )
open import DirectedHoTT.Examples.Knot.SubEnv using ( nrsK; ⊢nrsK; nrsK-sub; pairSK; ⊢pairSK; pairSK-sub; fsucSK; ⊢fsucSK; fsucSK-sub; iinstK; ⊢iinstK; iinstK-sub; MethTyK; ⊢MethTyK; MethTyK-sub )
open import DirectedHoTT.Examples.Knot.JudgeIx
open import DirectedHoTT.Examples.Knot.JudgeTmIx
open import DirectedHoTT.Examples.Knot.JudgeCase
open import DirectedHoTT.Examples.Knot.JudgeRowsTy using ( RowOK; okNone )
open import DirectedHoTT.Examples.Knot.JudgeRowsTm using ( rVar; okVar; rLam; okLam; rApp; okApp; rFz; okFz; rFs; okFs )

private
  variable
    Δ Θ : Cx
"""

if __name__ == "__main__":
    main()
