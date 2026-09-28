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

V0 = ("v0",)
RULES.update({
  # flat? cA ≡ true is a σ-field of the `Flat` family (a lower stratum)
  "ap": dict(ex=[("Tm", "J"), ("Pred", "Flat", "J", E(0)), ("Tm", "J"), ("Tm", "J")],
             ents=[tm("J", "G", E(0), U), tm("J", "G", F(0), U), tm("J+1", ("cext", "G", El(E(0))), F(1), El(("wk", 1, "J", F(0)))),
                   tm("J", "G", E(2), El(E(0))), tm("J", "G", E(3), El(E(0))), tm("J", "G", F(2), k("Hom", El(E(0)), E(2), E(3))),
                   ("id", ("Ty", "J"), "X", k("Hom", El(F(0)), ("sub0", 1, "J", F(1), E(2)), ("sub0", 1, "J", F(1), E(3))))]),
  # two rules on one head; the motive is a pattern UNDER A BINDER, so it Fords
  # (a case's convoy cannot be re-based from `j+1` to `j`); `occTm vz c ≡ false`
  # is `c = wk c₀` (strengthening), and NoNatC is renaming-invariant
  "tr": dict(alts=[
      dict(ex=[("Tm", "J"), ("Tm", "J"), ("IdC", ("Tm", "J+1"), F(0), V0)],
           ents=[tm("J", "G", E(0), U), tm("J", "G", E(1), U), tm("J", "G", F(1), k("Hom", U, E(0), E(1))),
                 tm("J", "G", F(2), El(E(0))), ("id", ("Ty", "J"), "X", El(E(1)))]),
      dict(ex=[("Ty", "J"), ("Tm", "J"), ("Tm", "J"), ("Pred", "NNC", "J", E(1)),
               ("IdC", ("Tm", "J+1"), F(0), k("cHom", ("wk", 1, "J", E(1)), ("wk", 1, "J", E(2)), V0)), ("Tm", "J"), ("Tm", "J")],
           ents=[tm("J+1", ("cext", "G", E(0)), ("wk", 1, "J", E(1)), U),
                 tm("J+1", ("cext", "G", E(0)), ("wk", 1, "J", E(2)), El(("wk", 1, "J", E(1)))),
                 tm("J+1", ("cext", "G", E(0)), V0, El(("wk", 1, "J", E(1)))),
                 tm("J", "G", E(5), E(0)), tm("J", "G", E(6), E(0)), tm("J", "G", F(1), k("Hom", E(0), E(5), E(6))),
                 tm("J", "G", F(2), El(k("cHom", E(1), E(2), E(5)))),
                 ("id", ("Ty", "J"), "X", El(k("cHom", E(1), E(2), E(6))))])]),
})

TESTRULES = {
  "trNoEq": dict(ex=[("Ty", "J"), ("Tm", "J"), ("Tm", "J"), ("Pred", "NNC", "J", E(1)), ("Tm", "J"), ("Tm", "J")],
           ents=[tm("J+1", ("cext", "G", E(0)), ("wk", 1, "J", E(1)), U),
                 tm("J", "G", E(4), E(0)), tm("J", "G", E(5), E(0)), tm("J", "G", F(1), k("Hom", E(0), E(4), E(5))),
                 ("id", ("Ty", "J"), "X", El(k("cHom", E(1), E(2), E(5))))]),
}

HAND = {"var": ("rVar", "okVar"), "lam": ("rLam", "okLam"), "app": ("rApp", "okApp"), "fzero": ("rFz", "okFz"), "fsuc": ("rFs", "okFs")}

# ------------------------------------------------------------ rendering
DEPTHS = ["J", "J+1", "J+2", "J+3", "J+4"]
def dnum(d): return DEPTHS.index(d)
def plus(d, n): return DEPTHS[dnum(d) + n]
def minus1(d): return DEPTHS[dnum(d) - 1]
def nsucs(k, x):
    for _ in range(k): x = "(nsuc %s)" % x
    return x
def dep(d, J="J"): return nsucs(dnum(d), J)
def dty(d, dJ="dJ"):
    t = dJ
    for _ in range(dnum(d)): t = "(⊢isuc %s)" % t
    return t
def pname(p):
    if p in ("J", "G", "X"): return p
    return {"f": "F", "q": "Q", "e": "E"}[p[0]] + str(p[1])
def is_param(e): return e in ("J", "G", "X") or (isinstance(e, tuple) and e[0] in ("f", "q", "e"))
def var(m):
    t = "vz"
    for _ in range(m): t = "(vs %s)" % t
    return t
def wN(i, x): return x if i == 0 else "(w%d %s)" % (i, x)
def extS(i, sig="σ"):
    t = sig
    for _ in range(i): t = "(extS %s)" % t
    return t
def fieldexpr(P, i):
    t = P
    for _ in range(i): t = "(snd %s)" % t
    return "(fst %s)" % t
def shape_expr(fs): return "(" + gk.shape(fs) + ")"

# ------------------------------------------------------------ a parametric object
class PObj:
    """A telescope (`kind = 'tel'`, a list of entries) or a code (`kind = 'code'`),
    parametric in the positions it mentions; its atoms abstracted for the law."""
    def __init__(self, rc, name, kind, body):
        self.rc, self.name, self.kind, self.body = rc, name, kind, body
        self.atoms, used = [], []
        self.used = used
        if kind == "tel":
            for ent in body: self.collect(ent)
        else:
            self.collect_code(body)
        order = ["J", "G", "X"] + [("f", i) for i in range(len(rc.fields))] \
              + [("q", i) for i in range(len(rc.tfields))] + [("e", i) for i in range(len(rc.ex))]
        self.params = [p for p in order if p in used]

    def use(self, p):
        if p not in self.used: self.used.append(p)

    def collect_code(self, c):
        t = c[0]
        if t in ("Ty", "Tm"):
            self.collect(c[1]); self.add_atom((t, (c[1],)))
        elif t == "Nat":
            pass
        elif t == "Pred":
            self.collect(c[2]); self.collect(c[3]); self.add_atom(("Pred:" + c[1], (c[2], c[3])))
        elif t == "IdC":
            self.collect_code(c[1]); self.collect(c[2]); self.collect(c[3])
        else:
            raise ValueError(c)

    def collect(self, x):
        if is_param(x):
            self.use(x); return
        if isinstance(x, str) and x.startswith("J"):
            self.use("J"); return
        tag = x[0]
        if tag in ("ty", "tm"):
            for y in x[1:]: self.collect(y)
        elif tag == "id":
            self.collect(x[1][1]); self.collect(x[2]); self.collect(x[3]); self.add_atom((x[1][0], (x[1][1],)))
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
        elif tag in ("nzero", "v0"):
            pass
        else:
            raise ValueError(x)

    def add_atom(self, a):
        if a not in self.atoms: self.atoms.append(a)

    def expr(self, x, env, atoms=False):
        if is_param(x): return env[x]
        if isinstance(x, str): return dep(x, env["J"])
        tag = x[0]
        if tag == "k":
            args = " ".join(self.expr(y, env, atoms) for y in x[2:])
            return "(k%s%s)" % (x[1], (" " + args) if args else "")
        if tag == "cext": return "(cext %s %s)" % (self.expr(x[1], env, atoms), self.expr(x[2], env, atoms))
        if tag == "nsuc": return "(nsuc %s)" % self.expr(x[1], env, atoms)
        if tag == "nzero": return "nzero"
        if tag == "v0": return "(kvar ffz)"
        if tag in ("sub0", "wk", "DF", "mc") or tag in OPS:
            key = (tag, x[1:])
            if atoms: return "A%d" % self.atoms.index(key)
            return self.atom_expr(key, env)
        raise ValueError(x)

    def atom_expr(self, a, env):
        kind, args = a
        r = lambda y: self.expr(y, env)
        if kind == "sub0": return "(sub0 %d %s %s %s)" % (args[0], r(args[1]), r(args[2]), r(args[3]))
        if kind == "wk":   return "(wk %d %s %s)" % (args[0], r(args[1]), r(args[2]))
        if kind == "DF":   return "(DF %s %s)" % (r(args[0]), r(args[1]))
        if kind in ("Ty", "Tm"): return "(⌜%s⌝ %s)" % (kind, r(args[0]))
        if kind.startswith("Pred:"): return "(⌜%s⌝ %s %s)" % (kind[5:], r(args[0]), r(args[1]))
        if kind in OPS or kind == "mc": return "(%s %s)" % (kind, " ".join(r(y) for y in args))
        raise ValueError(a)

    def atom_sub(self, a, env, sigma):
        kind, args = a
        r = lambda y: self.expr(y, env)
        if kind == "sub0": return "(sub0-sub %s %d %s %s %s)" % (sigma, args[0], r(args[1]), r(args[2]), r(args[3]))
        if kind == "wk":   return "(wk-sub %s %d %s %s)" % (sigma, args[0], r(args[1]), r(args[2]))
        if kind == "DF":   return "(DF-sub %s %s %s)" % (sigma, r(args[0]), r(args[1]))
        if kind in ("Ty", "Tm"): return "(⌜%s⌝-sub %s %s)" % (kind, sigma, r(args[0]))
        if kind.startswith("Pred:"): return "(⌜%s⌝-sub %s %s %s)" % (kind[5:], sigma, r(args[0]), r(args[1]))
        if kind in OPS or kind == "mc": return "(%s-sub %s %s)" % (kind, sigma, " ".join(r(y) for y in args))
        raise ValueError(a)

    def code_render(self, c, env, atoms):
        t = c[0]
        if t in ("Ty", "Tm"):
            key = (t, (c[1],))
            return ("A%d" % self.atoms.index(key)) if atoms else self.atom_expr(key, env)
        if t == "Nat": return "⌜Nat⌝"
        if t == "Pred":
            key = ("Pred:" + c[1], (c[2], c[3]))
            return ("A%d" % self.atoms.index(key)) if atoms else self.atom_expr(key, env)
        if t == "IdC":
            return "(⌜Id⌝ %s %s %s)" % (self.code_render(c[1], env, atoms), self.expr(c[2], env, atoms), self.expr(c[3], env, atoms))
        raise ValueError(c)

    def render(self, env, atoms):
        if self.kind == "code": return self.code_render(self.body, env, atoms)
        out = "tι"
        for ent in reversed(self.body):
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

    # ---- typing
    def typ(self, x, s, d, denv):
        if is_param(x): return denv[x]
        tag = x[0]
        if tag == "v0":
            assert s == 1 and dnum(d) >= 1
            return "(⊢kvar %s (⊢ffz %s))" % (dty(d, denv["J"]), dty(minus1(d), denv["J"]))
        if tag == "k":
            srt, fs, _ = SIG[x[1]]
            assert srt == s, (x, s)
            ds = []
            for f, y in zip(fs, x[2:]):
                if f[0] == "nat":
                    ds.append(self.nattyp(y, denv)); continue
                assert f[0] == "rec", (x, f)
                ds.append(self.typ(y, f[1], plus(d, f[2]), denv))
            return "(⊢k%s %s%s)" % (x[1], dty(d, denv["J"]), "".join(" " + q for q in ds))
        if tag == "sub0":
            _, s0, d0, t, u = x
            assert s0 == s and d0 == d, (x, s, d)
            return "(⊢sub0 %s %s %s %s)" % (gk.lt(s0), dty(d0, denv["J"]), self.typ(t, s0, plus(d0, 1), denv), self.typ(u, 1, d0, denv))
        if tag == "wk":
            _, s0, d0, t = x
            assert s0 == s and plus(d0, 1) == d, (x, s, d)
            return "(⊢wkS %s %s %s)" % (gk.lt(s0), dty(d0, denv["J"]), self.typ(t, s0, d0, denv))
        if tag == "DF":
            _, d0, I = x
            assert s == 0 and d0 == d
            return "(⊢DF %s %s)" % (dty(d0, denv["J"]), self.typ(I, 1, d0, denv))
        if tag in OPS:
            sg = OPS[tag]
            d0 = x[1]
            assert s == 0 and plus(d0, sg["out"]) == d, (x, s, d)
            ds = [self.typ(y, srt, plus(d0, kk), denv) for y, (srt, kk) in zip(x[2:], sg["args"])]
            return "(⊢%s %s%s)" % (tag, dty(d0, denv["J"]), "".join(" " + q for q in ds))
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
            return "(⊢mc %s %s %s %s)" % (dty(d0, denv["J"]), self.ctxtyp(g0, d0, denv), self.typ(I, 1, d0, denv), self.typ(D, 1, d0, denv))
        assert g[0] == "cext"
        dm = minus1(d)
        return "(⊢cext %s %s %s)" % (dty(dm, denv["J"]), self.ctxtyp(g[1], dm, denv), self.typ(g[2], 0, dm, denv))

    def codetyp(self, c, denv):
        t = c[0]
        if t in ("Ty", "Tm"): return "(⊢⌜%s⌝ %s)" % (t, dty(c[1], denv["J"]))
        if t == "Nat": return "⊢⌜Nat⌝"
        if t == "Pred": return "(⊢⌜%s⌝ %s %s)" % (c[1], dty(c[2], denv["J"]), self.typ(c[3], 1, c[2], denv))
        if t == "IdC":
            k0, d0 = c[1]
            srt = 0 if k0 == "Ty" else 1
            to = "toTy" if srt == 0 else "toTm"
            return "(⊢⌜Id⌝ %s (%s %s) (%s %s))" % (self.codetyp(c[1], denv), to, self.typ(c[2], srt, d0, denv), to, self.typ(c[3], srt, d0, denv))
        raise ValueError(c)

    def typing(self, denv):
        if self.kind == "code": return self.codetyp(self.body, denv)
        body = "ok-ι"
        for ent in reversed(self.body):
            if ent[0] == "ty":
                _, d, g, Aa = ent
                body = "ok-ρ (⊢tyIx %s %s %s) (%s)" % (dty(d, denv["J"]), self.ctxtyp(g, d, denv), self.typ(Aa, 0, d, denv), body)
            elif ent[0] == "tm":
                _, d, g, t, Aa = ent
                body = "ok-ρ (⊢tmIx %s %s %s %s) (%s)" % (dty(d, denv["J"]), self.ctxtyp(g, d, denv), self.typ(t, 1, d, denv),
                                                           self.typ(Aa, 0, d, denv), body)
            elif ent[0] == "id":
                _, code, a, b = ent
                srt = 0 if code[0] == "Ty" else 1
                to = "toTy" if srt == 0 else "toTm"
                body = "ok-σ (⊢⌜Id⌝ (⊢⌜%s⌝ %s) (%s %s) (%s %s)) ok-ι" % (code[0], dty(code[1], denv["J"]),
                    to, self.typ(a, srt, code[1], denv), to, self.typ(b, srt, code[1], denv))
        return body

def pty(rc, p):
    """a position's type, for the generic typing"""
    if p == "J": return "El ⌜Nat⌝"
    if p == "G": return "KCtx J"
    if p == "X": return "K 0 J"
    if p[0] in ("f", "q"):
        fs = rc.fields if p[0] == "f" else rc.tfields
        f = fs[p[1]]
        assert f[0] == "rec", (rc.n, p, f)
        return "K %d %s" % (f[1], dep(DEPTHS[f[2]]))
    if p[0] == "e":
        c = rc.ex[p[1]]
        if c[0] == "Ty": return "K 0 %s" % dep(c[1])
        if c[0] == "Tm": return "K 1 %s" % dep(c[1])
        if c[0] == "Nat": return "El ⌜Nat⌝"
        raise ValueError("a witness is not a position: %r" % (c,))
    raise ValueError(p)

def gen_pobj(po):
    L = []
    rc = po.rc
    P = po.params
    pn = [pname(p) for p in P]
    env = {p: pname(p) for p in P}
    env.setdefault("J", "J")
    na = len(po.atoms)
    an = ["A%d" % i for i in range(na)]
    I, A = po.name + "I", po.name + "A"
    tel = po.kind == "tel"
    Ret = "Tel Δ" if tel else "RTm Δ"
    q = (lambda x: "⌜ %s ⌝ᵗ" % x) if tel else (lambda x: "(%s)" % x)
    L.append("%s : %s%s" % (A, "RTm Δ → " * (len(P) + na), Ret))
    L.append("%s = %s" % (" ".join([A] + pn + an), po.render(env, True)))
    L.append("")
    L.append("%s : %s%s" % (I, "RTm Δ → " * len(P), Ret))
    L.append("%s = %s" % (" ".join([I] + pn), " ".join([A] + pn + [po.atom_expr(a, env) for a in po.atoms])))
    L.append("")
    L.append("%s-cong : {Δ : Cx} → %s%s%s ≡ %s" % (A,
        "".join("(%s : RTm Δ) → " % x for x in pn) + "".join("(%s %s' : RTm Δ) → " % (a, a) for a in an),
        "".join("%s ≡ %s' → " % (a, a) for a in an),
        q(" ".join([A + " {Δ}"] + pn + an)), q(" ".join([A] + pn + [a + "'" for a in an]))))
    L.append("%s-cong %s%s = refl" % (A, " ".join(pn + [x for a in an for x in (a, a + "'")]), "".join(" refl" for _ in an)))
    L.append("")
    L.append("%s-sub : (σ : Sub Δ Θ)%s → subTm σ %s ≡ %s" % (I,
        "".join(" (%s : RTm Δ)" % x for x in pn), q(" ".join([I] + pn)), q(" ".join([I] + ["(subTm σ %s)" % x for x in pn]))))
    if na:
        senv = {p: "(subTm σ %s)" % pname(p) for p in P}
        senv.setdefault("J", "J")
        L.append("%s-sub σ%s = %s-cong %s %s %s" % (I, "".join(" " + x for x in pn), A,
            " ".join("(subTm σ %s)" % x for x in pn),
            " ".join("(subTm σ %s) %s" % (po.atom_expr(a, env), po.atom_expr(a, senv)) for a in po.atoms),
            " ".join(po.atom_sub(a, env, "σ") for a in po.atoms)))
    else:
        L.append("%s-sub σ%s = refl" % (I, "".join(" " + x for x in pn)))
    L.append("")
    L.append("%s-cong : {Δ : Cx} → %s%s ≡ %s" % (I,
        "".join("(%s %s' : RTm Δ) → " % (x, x) for x in pn) + "".join("%s ≡ %s' → " % (x, x) for x in pn),
        q(" ".join([I + " {Δ}"] + pn)), q(" ".join([I] + [x + "'" for x in pn]))))
    L.append("%s-cong %s%s = refl" % (I, " ".join(x for y in pn for x in (y, y + "'")), "".join(" refl" for _ in pn)))
    L.append("")
    denv = {p: "d" + pname(p) for p in P}
    denv.setdefault("J", "dJ")
    concl = ("TelOK Ξ JT (%s)" if tel else "Ξ ⊢ %s ∷ U") % " ".join([I] + pn)
    L.append("ok%s : {Ξ : Ctx}%s → %s%s" % (I, (" {%s : RTm ⌊ Ξ ⌋}" % " ".join(pn)) if pn else "",
        "".join("Ξ ⊢ %s ∷ %s → " % (pname(p), pty(rc, p)) for p in P), concl))
    L.append("%s = %s" % (" ".join(["ok" + I] + ["d" + x for x in pn]), po.typing(denv)))
    L.append("")
    return L

# ------------------------------------------------------------ a row: its alternatives
class RowCtx:
    def __init__(self, name, case, ex):
        self.n = name
        self.case = case
        self.ex = ex
        self.sort, self.fields, self.idx = SIG[name]
        self.tfields = SIG[case][1] if case else []

class Alt:
    """one rule: its existentials (σ-prefix codes) and its premises"""
    def __init__(self, name, tag, case, spec):
        self.rc = RowCtx(name, case, spec.get("ex", []))
        self.n = name
        self.case = case
        self.pfx = "T⊢" + name + tag
        self.codes = [PObj(self.rc, "C⊢%s%s_%d" % (name, tag, i), "code", c) for i, c in enumerate(self.rc.ex)]
        for i, co in enumerate(self.codes):
            for p in co.params:
                assert not (isinstance(p, tuple) and p[0] == "e" and p[1] >= i), (name, i, p)
        self.body = PObj(self.rc, self.pfx, "tel", spec["ents"])

def gen_alt(al):
    L = []
    for co in al.codes: L += gen_pobj(co)
    L += gen_pobj(al.body)
    rc = al.rc
    n = len(rc.ex)
    N, I = al.pfx, al.pfx + "I"
    case = al.case is not None
    a = "q" if case else "p"
    payload = "(snd c)" if case else "p"
    def src(p, sub=False):
        cc = "(subTm σ c)" if sub else "c"
        if p == "J": return "(subTm σ j)" if sub else "j"
        if p == "G": return "(fst %s)" % cc
        if p == "X": return "(snd %s)" % cc
        if p[0] == "f": return fieldexpr("(snd %s)" % cc if case else ("(subTm σ p)" if sub else "p"), p[1])
        if p[0] == "q": return fieldexpr("(subTm σ q)" if sub else "q", p[1])
        raise ValueError(p)
    def arg(p, lvl, sub=False):
        if isinstance(p, tuple) and p[0] == "e": return "(var %s)" % var(lvl - 1 - p[1])
        return wN(lvl, src(p, sub))
    def inst(po, lvl, sub=False):
        return "(%s)" % " ".join([po.name + "I"] + [arg(p, lvl, sub) for p in po.params]) if po.params else po.name + "I"
    def tel_from(i, sub=False):
        body = inst(al.body, n, sub)
        for m in reversed(range(i, n)):
            body = "(tσ %s %s)" % (inst(al.codes[m], m, sub), body)
        return body
    L.append("%s : RTm Δ → RTm Δ → RTm Δ → Tel Δ" % N)
    L.append("%s j %s c = %s" % (N, a, tel_from(0)))
    L.append("")
    # the law
    def piece(po, lvl, isTel):
        lhs = ("(subTm %s ⌜ %s ⌝ᵗ)" if isTel else "(subTm %s %s)") % (extS(lvl), inst(po, lvl))
        rhs = ("⌜ %s ⌝ᵗ" if isTel else "%s") % inst(po, lvl, True)
        if not po.params:
            return lhs, rhs, "(%s-sub %s)" % (po.name + "I", extS(lvl))
        pr = []
        for p in po.params:
            if isinstance(p, tuple) and p[0] == "e": pr.append("refl")
            elif lvl == 0: pr.append("refl")
            else: pr.append("(w%d-sub σ %s)" % (lvl, src(p)))
        proof = "(trans (%s-sub %s %s) (%s-cong %s %s))" % (po.name + "I", extS(lvl), " ".join(arg(p, lvl) for p in po.params),
                  po.name + "I", " ".join("(subTm %s %s) %s" % (extS(lvl), arg(p, lvl), arg(p, lvl, True)) for p in po.params),
                  " ".join(pr))
        return lhs, rhs, proof
    L.append("%s-law : TelLaw %s" % (N, N))
    if n == 0:
        _, _, pr = piece(al.body, 0, True)
        L.append("%s-law σ j %s c = %s" % (N, a, pr))
    else:
        ps = [piece(al.codes[i], i, False) for i in range(n)] + [piece(al.body, n, True)]
        L.append("%s-law σ j %s c =" % (N, a))
        L.append("  dσ-cong%d %s %s" % (n, " ".join("%s %s" % (l, r) for l, r, _ in ps), " ".join(p for _, _, p in ps)))
    L.append("")
    # the typing, at the row's sources
    ctx = ["Ξ"]
    for i in range(n): ctx.append("(%s ▹ El %s)" % (ctx[-1], inst(al.codes[i], i)))
    S = "(pair (tag 1) j)"
    dP = "(⊢pI %s dc)" % shape_name(al.n) if case else "dp"
    def fieldtyp(fs, base, S_, i):
        d = base
        for m in range(i):
            f = fs[m]
            d = "(⊢recSnd {s = %d} {k = %d} {sh = %s} %s)" % (f[1], f[2], shape_expr(fs[m + 1:]), d)
        f = fs[i]
        assert f[0] == "rec", (al.n, fs, i)
        return "(⊢atDepth {a = tag %d} {j = j} {s = %d} {k = %d} (⊢recFst {s = %d} {k = %d} {sh = %s} %s))" % (
            S_, f[1], f[2], f[1], f[2], shape_expr(fs[i + 1:]), d)
    def styp(p):
        if p == "J": return "dj"
        if p == "G": return "(⊢gI %s dc)" % shape_name(al.n) if case else "(⊢ctxOf dc)"
        if p == "X": return "(⊢tyOf dc)"
        if p[0] == "f": return fieldtyp(rc.fields, dP, 1, p[1])
        if p[0] == "q": return fieldtyp(rc.tfields, "dq", 0, p[1])
    def kind(p):
        if p == "J": return ("nat",)
        if p == "G": return ("ctx",)
        if p == "X": return ("K", 0, "j")
        fs = rc.fields if p[0] == "f" else rc.tfields
        f = fs[p[1]]
        return ("K", f[1], nsucs(f[2], "j"))
    def weaken(kd, term, typ, frm, to, termlvl=None):
        # goal-directed: the contexts are inferred; only the TERMS are pinned
        for i in range(frm, to):
            t_i = wN(i, term) if termlvl is None else termlvl(i)
            if kd[0] == "nat":
                typ = "(wkN {t = %s} %s)" % (t_i, typ)
            elif kd[0] == "ctx":
                typ = "(wkG {d = %s} {g = %s} %s)" % (wN(i, "j"), t_i, typ)
            else:
                dd = wN(i, kd[2]) if termlvl is None else kd[3](i)
                typ = "(wkK {s = %d} {d = %s} {t = %s} %s)" % (kd[1], dd, t_i, typ)
        return typ
    def ptyp(p, lvl):
        if isinstance(p, tuple) and p[0] == "e":
            m = p[1]; c = rc.ex[m]
            vt = lambda i: "(var %s)" % var(i - m - 1)
            if c[0] == "Nat":
                return weaken(("nat",), None, "(⊢var here)", m + 1, lvl, termlvl=vt)
            dd0 = dep(c[1], wN(m, "j"))
            here = "(here%s {m = %s})" % (c[0], dd0)
            srt = 0 if c[0] == "Ty" else 1
            dl = lambda i: wN(i - m - 1, "(renTm vs %s)" % dd0) if i > m + 1 else "(renTm vs %s)" % dd0
            return weaken(("K", srt, None, dl), None, here, m + 1, lvl, termlvl=vt)
        return weaken(kind(p), src(p), styp(p), 0, lvl)
    def okinst(po, lvl):
        return "(ok%s {_}%s%s)" % (po.name + "I", "".join(" {%s}" % arg(p, lvl) for p in po.params),
                                   "".join(" " + ptyp(p, lvl) for p in po.params))
    if case:
        sig = "Ξ ⊢ q ∷ PayV %s (pair (tag 0) j) (SI 2) (SD KSig) → Ξ ⊢ c ∷ El (CIat %s (pair (tag 0) j))" % (
            shape_name(al.case), shape_name(al.n))
        srcs = "dj dq dc"
    else:
        sig = "Ξ ⊢ p ∷ PayV %s %s (SI 2) (SD KSig) → Ξ ⊢ c ∷ El (CTat %s)" % (shape_name(al.n), S, S)
        srcs = "dj dp dc"
    L.append("ok%s : {Ξ : Ctx} {j %s c : RTm ⌊ Ξ ⌋} → Ξ ⊢ j ∷ El ⌜Nat⌝ → %s → TelOK Ξ JT (%s j %s c)" % (N, a, sig, N, a))
    def T_at(i):
        body = inst(al.body, n)
        for m in reversed(range(i, n)):
            body = "(tσ %s %s)" % (inst(al.codes[m], m), body)
        return body
    expr = okinst(al.body, n)
    for i in reversed(range(n)):
        expr = "(okσJ %s %s)" % (okinst(al.codes[i], i), expr)
    L.append("ok%s {Ξ} {j} {%s} {c} %s = %s" % (N, a, srcs, expr))
    L.append("")
    return L

def gen_head(name, spec):
    L = ["-- ⊢%s" % name]
    case = spec.get("case")
    alts = spec.get("alts", [spec])
    tags = [""] if len(alts) == 1 else ["ᵃ", "ᵇ", "ᶜ", "ᵈ"][:len(alts)]
    As = [Alt(name, t, case, a) for t, a in zip(tags, alts)]
    for al in As: L += gen_alt(al)
    sh = shape_name(name)
    if case:
        assert len(As) == 1
        N = As[0].pfx
        h = SIG[case][2]
        L.append("r%sI : Row" % N)
        L.append("r%sI = defRow₀ %s %s-law" % (N, N, N))
        L.append("module P%s = CaseRow %s %s %d r%sI" % (N, sh, ok_name(name), h, N))
        L.append("okC%sI : P%s.RowOK 0 %s r%sI" % (N[1:], N, shape_name(case), N))
        L.append("okC%sI {Ξ} {j} {q} {c} dj dq dc = ⊢tel {Ξ} {JT} {%s j q c} ⊢JT (ok%s dj dq dc)" % (N[1:], N, N))
        L.append("r⊢%s : Row" % name)
        L.append("r⊢%s = P%s.rX" % (name, N))
        L.append("ok⊢%s : RowOK 1 %s r⊢%s" % (name, sh, name))
        L.append("ok⊢%s = P%s.okX okC%sI" % (name, N, N[1:]))
    else:
        Ns = [al.pfx for al in As]
        cs = " ∷ ".join("⌜ %s j p c ⌝ᵗ" % N for N in Ns) + " ∷ []"
        L.append("r⊢%s : Row" % name)
        if len(Ns) == 1:
            L.append("r⊢%s = defRow %s %s-law" % (name, Ns[0], Ns[0]))
        else:
            assert len(Ns) == 2
            L.append("r⊢%s = record { R = λ j p c → rows (%s)" % (name, cs))
            L.append("  ; R-sub = λ σ j p c → trans (rows-sub' σ (%s)) (cong₂ (λ X Y → rows (X ∷ Y ∷ [])) (%s-law σ j p c) (%s-law σ j p c)) }"
                     % (cs, Ns[0], Ns[1]))
        L.append("ok⊢%s : RowOK 1 %s r⊢%s" % (name, sh, name))
        L.append("ok⊢%s {Ξ} {j} {p} {c} dj dp dc = ⊢rows {Ξ} {JT} {%d} {%s} ⊢JT (%s []ᵈ)" % (
            name, len(Ns), cs, "".join("⊢tel {Ξ} {JT} {%s j p c} ⊢JT (ok%s dj dp dc) ∷ᵈ " % (N, N) for N in Ns)))
    L.append("")
    return L

def gen_helpers(maxn):
    """the weakenings past 3 binders, and the σ-prefix congruences (explicit arguments)"""
    L = []
    for kk in range(4, maxn + 1):
        L.append("w%d : RTm Δ → RTm _" % kk)
        L.append("w%d x = renTm vs (w%d x)" % (kk, kk - 1))
        L.append("w%d-sub : (σ : Sub Δ Θ) (x : RTm Δ) → subTm %s (w%d x) ≡ w%d (subTm σ x)" % (kk, extS(kk), kk, kk))
        L.append("w%d-sub σ x = trans (wkS %s (w%d x)) (cong w1 (w%d-sub σ x))" % (kk, extS(kk - 1), kk - 1, kk - 1))
        L.append("")
    for kk in range(1, maxn + 1):
        ctxs = ["Δ"]
        for _ in range(kk): ctxs.append("(%s ∙)" % ctxs[-1])
        names = ["X%d" % i for i in range(kk)]
        args = "".join("(%s %s' : RTm %s) " % (x, x, ctxs[i]) for i, x in enumerate(names)) + "(Z Z' : RTm %s)" % ctxs[kk]
        def nest(prime):
            t = "Z" + prime
            for x in reversed(names): t = "dσ %s%s (lam (%s))" % (x, prime, t)
            return t
        L.append("dσ-cong%d : %s → %s%s ≡ %s" % (kk, args, "".join("%s ≡ %s' → " % (x, x) for x in names + ["Z"]), nest(""), nest("'")))
        L.append("dσ-cong%d %s Z Z' %s = refl" % (kk, " ".join("%s %s'" % (x, x) for x in names), " ".join("refl" for _ in names + ["Z"])))
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
  "StkC": dict(doc="stkC? c ≡ true — J-able: stkA? minus the literal ⌜Nat⌝; at ⌜Hom⌝ it is stkA? of the ambient",
               rows={"cbase": [], "cSg": [], "cId": [], "cUnit": [], "cFin": [], "cIMu": [],
                     "cHom": [("σ", "StkA", 0)]}),
  "Flat": dict(doc="flat? c ≡ true — ⌜base⌝, or ⌜Hom⌝ at a J-able ambient (Spec/Variance)",
               rows={"cbase": [], "cHom": [("σ", "StkC", 0)]}),
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
            for pr in reversed(prems):
                if pr[0] == "σ":
                    assert tel == "tι", "a σ-premise is last"
                    tel = "tσ (⌜%s⌝ j %s) tι" % (pr[1], fld(pr[2]))
                else:
                    f, kk = pr
                    tel = "tρ (ix%s %s %s) (%s)" % (P, dep(kk), fld(f), tel)
            L.append("T%s : RTm Δ → RTm Δ → RTm Δ → Tel Δ" % nm)
            L.append("T%s j p c = %s" % (nm, tel))
            L.append("")
            L.append("r%s : Row" % nm)
            sp = [pr for pr in prems if pr[0] == "σ"]
            if sp:
                L.append("r%s = defRow T%s (λ σ j p c → cong (λ Z → dσ Z (lam dι)) (⌜%s⌝-sub σ j %s))" % (nm, nm, sp[0][1], fld(sp[0][2])))
            else:
                L.append("r%s = defRow T%s (λ σ j p c → refl)" % (nm, nm))
            L.append("")
            L.append("ok%s : %sₘ.RowOK 1 %s r%s" % (nm, P, sh, nm))
            body = "ok-ι"
            def ftyping(f):
                d = "dp"
                for m in range(f):
                    d = "(⊢recSnd {s = %d} {k = %d} {sh = %s} %s)" % (fs[m][1], fs[m][2], shape_expr(fs[m + 1:]), d)
                return "(⊢atDepth {a = tag 1} {j = j} {s = %d} {k = %d} (⊢recFst {s = %d} {k = %d} {sh = %s} %s))" % (
                    fs[f][1], fs[f][2], fs[f][1], fs[f][2], shape_expr(fs[f + 1:]), d)
            for pr in reversed(prems):
                if pr[0] == "σ":
                    body = "ok-σ (⊢⌜%s⌝ dj %s) ok-ι" % (pr[1], ftyping(pr[2]))
                    continue
                (f, k) = pr
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
        L.append("-- ★ …and as a CODE (a premise of a higher stratum is a σ-field of it), OPAQUE")
        L.append("opaque")
        L.append("  ⌜%s⌝ : RTm Δ → RTm Δ → RTm Δ" % P)
        L.append("  ⌜%s⌝ d c = ⌜IMu⌝ %sₘ.J %sF.DF (ix%s d c)" % (P, P, P, P))
        L.append("")
        L.append("  ⊢⌜%s⌝ : {Ξ : Ctx} {d c : RTm ⌊ Ξ ⌋} → Ξ ⊢ d ∷ El ⌜Nat⌝ → Ξ ⊢ c ∷ K 1 d → Ξ ⊢ ⌜%s⌝ d c ∷ U" % (P, P))
        L.append("  ⊢⌜%s⌝ dd dc = ⊢⌜IMu⌝ %sₘ.⊢J %sF.⊢DF (⊢ix%s dd dc)" % (P, P, P, P))
        L.append("")
        L.append("  ⌜%s⌝-sub : (σ : Sub Δ Θ) (d c : RTm Δ) → subTm σ (⌜%s⌝ d c) ≡ ⌜%s⌝ (subTm σ d) (subTm σ c)" % (P, P, P))
        L.append("  ⌜%s⌝-sub σ d c = cong₂ (λ I D → ⌜IMu⌝ I D (ix%s (subTm σ d) (subTm σ c))) (%sₘ.J-sub σ) (%sF.DF-sub σ)" % (P, P, P, P))
        L.append("")
        L.append("  El-⌜%s⌝ : {d c : RTm Δ} → El (⌜%s⌝ d c) ≅ᵀ K%s d c" % (P, P, P))
        L.append("  El-⌜%s⌝ = credᵀ El-⌜IMu⌝" % P)
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

open import normalizer.Syntax.Types using ( _≡_; refl; cong; cong₂ )
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
    if "--only" in sys.argv:
        names = sys.argv[sys.argv.index("--only") + 1].split(",")
        L = [HDR.replace("module DirectedHoTT.Examples.Knot.JudgeRowsGen where", "module DirectedHoTT.tmp.JudgeRowsOne where")]
        maxn = 7
        L += gen_helpers(max(maxn, 3))
        for nm in names:
            if nm in TESTRULES:
                al = Alt("tr", "", None, TESTRULES[nm])
                L += gen_alt(al)
            elif "#" in nm:
                base, ix = nm.split("#")
                al = Alt(base, "", RULES[base].get("case"), RULES[base]["alts"][int(ix)])
                out = gen_alt(al)
                if "--notyping" in sys.argv:
                    cut = [i for i, l in enumerate(out) if l.startswith("ok" + al.pfx + " ")]
                    out = out[:cut[0]] if cut else out
                L += out
            else:
                L += gen_head(nm, RULES[nm])
        open(os.path.join(ROOT, "tmp", "JudgeRowsOne.agda"), "w", encoding="utf-8").write("\n".join(L) + "\n")
        print("wrote tmp/JudgeRowsOne.agda"); return
    L = [HDR]
    maxn = max(len(a.get("ex", [])) for sp in RULES.values() for a in sp.get("alts", [sp]))
    L += gen_helpers(max(maxn, 3))
    for name, spec in RULES.items():
        L += gen_head(name, spec)
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
open import DirectedHoTT.Lib.FinFam using ( ⊢isuc; toI; ffz; ⊢ffz )
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
open import DirectedHoTT.Examples.Knot.Preds using ( ⌜Flat⌝; ⊢⌜Flat⌝; ⌜Flat⌝-sub; ⌜NNC⌝; ⊢⌜NNC⌝; ⌜NNC⌝-sub )
open import DirectedHoTT.Metatheory.SubjectReductionBase using () renaming ( wk-sub to wkS )
open import DirectedHoTT.Examples.Knot.JudgeRowsTm using ( rVar; okVar; rLam; okLam; rApp; okApp; rFz; okFz; rFs; okFs )

private
  variable
    Δ Θ : Cx
"""

if __name__ == "__main__":
    main()
