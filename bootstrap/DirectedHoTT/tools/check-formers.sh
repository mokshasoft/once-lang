#!/usr/bin/env bash
# ============================================================================
# check-formers.sh — THE FORMER-COVERAGE TRIPWIRES.
#
# WHY THIS EXISTS.  Agda's coverage checker checks FUNCTIONS, not DATATYPES.
# A term former missing from a datatype is a well-formed definition, so the
# module compiles GREEN and the omission only surfaces wherever something is
# finally OBLIGED to produce the missing constructor — which can be several
# modules and many minutes downstream.  That happened with `ordtr`
# (2026-08-05 → 06): absent from the whole SN layer, LR green, would only have
# blocked in `fund`.
#
# ⚠ SCOPE, STATED HONESTLY.  A missing constructor makes goals UNPROVABLE, not
# FALSE — it is a completeness gap, not a soundness gap.  These checks buy
# EARLY DETECTION, not soundness.  They also do not check that the rows are
# RIGHT, only that the decision was made somewhere.
#
# THREE CHECKS, and note they use DIFFERENT invariants — "every former appears"
# is correct for the SN layer and WRONG for e.g. `Canon`, which lists only
# INTRODUCTION forms and must not mention `var`/`app`/`fst`.
#
#   1. FAIL — every `RTm` former is homed in ≥1 of SNe / SN / SNRed / Ne.
#   2. FAIL — every `RTy` former has a level-1 logical-relation clause (and a
#      level-0 one, bar the documented `U` exception: level 0 covers only
#      decodings of codes, and there is no code for `U`).
#   3. REPORT — which formers rely on a CATCH-ALL in a stuckness classifier.
#      Not a failure: a catch-all is often the right answer (`ordtr` takes the
#      default in all four).  But a catch-all is SILENT, so a new former's
#      defaults should be reviewed rather than inherited by accident.
#
# NOT CHECKED, deliberately — these are protected by a producer's own coverage:
#   `Canon`/`Prog`  — `prog` must return a canonical form or a step for every
#                     former, so its coverage forces the decision.
#   `⊩₀`/`⊩₁` rows  — `fund-ty` must build an interpretation for every `⊢ty`.
#   `NatMem`        — not per-former; its completeness is a theorem in `fund`.
#
# Usage:  ./DirectedHoTT/tools/check-formers.sh   (from anywhere)
#
# ⚠⚠ PORTED INTO DirectedHoTT 2026-08-22, AND THE PORT WAS OVERDUE.
#   The migration took sweep.sh and gained check-trust.sh but LEFT THIS
#   BEHIND — so for the whole of that period the tree had no guard on
#   the one thing Agda cannot see. It was noticed only when adding
#   IMu/icon/ielim produced a GREEN `Spec/Typing` containing ZERO rules
#   for them. Exactly the hazard this file was written for.
# Exit:   0 = all FAIL-checks pass;  1 = at least one orphan.
# ============================================================================
set -uo pipefail
cd "$(dirname "$0")"
exec python3 - "$@" <<'PYEOF'
import re, sys, os

ROOT = os.path.normpath(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
PI  = os.path.join(ROOT, 'Spec', 'Syntax.agda')
LR  = os.path.join(ROOT, 'Metatheory', 'LogicalRelation.agda')
VAR = os.path.join(ROOT, 'Spec', 'Variance.agda')
for f in (PI, LR, VAR):
    if not os.path.isfile(f):
        print(f"!! cannot read {f}", file=sys.stderr); sys.exit(2)

def read(f):
    return open(f, encoding='utf-8').read()

def block(src, header):
    """Body of a `data X where` block: up to the next column-0 line."""
    m = re.search(r'^' + re.escape(header) + r'\s*$', src, re.M)
    if not m:
        return None
    out = []
    for line in src[m.end():].split('\n'):
        if line and not line[0].isspace():
            break
        out.append(re.sub(r'--.*$', '', line))   # strip comments
    return '\n'.join(out)

def ctors(body):
    """Constructor names: `name : ...` or `name₁ name₂ : ...` at indent."""
    names = []
    for line in body.split('\n'):
        m = re.match(r'\s+([^\s:][^:]*?)\s*:(?!=)', line)
        if m and '→' not in m.group(1):
            names += m.group(1).split()
    return names

pi, lr, var = read(PI), read(LR), read(VAR)
rtm = ctors(block(pi, 'data RTm where'))
rty = ctors(block(pi, 'data RTy where'))
if not rtm or not rty:
    print("!! parsed zero RTm/RTy constructors", file=sys.stderr); sys.exit(2)

def tok(name, hay):
    """Whole-token occurrence — `ordtr` must not match `ordtrX`."""
    return re.search(r'(?<![\w\'⌜⌝?₀-₉ᵃ-ᶻ])' + re.escape(name)
                     + r'(?![\w\'⌜⌝?₀-₉ᵃ-ᶻ])', hay) is not None

fail = 0

# ── 1. the SN layer ────────────────────────────────────────────────────────
SN = {d: (block(lr, f'data {d} {{Γ}} where') or '') for d in
      ('SNe', 'SN', 'SNRed')}
SN['Ne'] = block(lr, 'data Ne {Γ} : RTm Γ → Set where') or ''
print("== 1. RTm formers vs the SN layer (SNe/SN/SNRed/Ne) ==")
orph = 0
for c in rtm:
    homes = [d for d, b in SN.items() if tok(c, b)]
    if homes:
        print(f"  ok      {c:<8} — {' '.join(homes)}")
    else:
        print(f"  ORPHAN  {c:<8} — in NO SN-layer datatype"); orph += 1
print(f"== {len(rtm)} formers, {orph} orphaned ==")
fail += orph

# ── 2. the logical relation, one clause per RTy former ─────────────────────
# RTy former -> the clause that interprets it (`El` decodes to a NEUTRAL).
LRMAP = {'base':'base','U':'U','Π':'Π','Σ\'':'Σ','El':'ne',
         'Hom':'Hom','Unit':'Unit','Nat':'Nat','Id':'Id','Mu':'Mu',
         # ⚠ the ENTRY is a declaration of what must exist; the code below
         #   then VERIFIES `⊩₁IMu`/`⊩₀IMu` are really in the datatype
         #   blocks.  Adding a row does not silence the check — omitting
         #   one is what makes it say "UNMAPPED".
         'IMu':'IMu'}
L1 = block(lr, 'data ⊩₁_ {Γ} where') or ''
L0 = block(lr, 'data ⊩₀_ {Γ} where') or ''
print("\n== 2. RTy formers vs the logical relation (⊩₁ / ⊩₀) ==")
miss = 0
for t in rty:
    suf = LRMAP.get(t)
    if suf is None:
        print(f"  UNMAPPED {t:<6} — new RTy former: add it to LRMAP"); miss += 1; continue
    has1, has0 = tok('⊩₁' + suf, L1), tok('⊩₀' + suf, L0)
    if not has1:
        print(f"  MISSING {t:<7} — no ⊩₁{suf} clause"); miss += 1
    elif not has0 and t != 'U':
        print(f"  MISSING {t:<7} — has ⊩₁{suf} but no ⊩₀{suf}"); miss += 1
    else:
        note = "  (⊩₁ only — no code for U, by design)" if t == 'U' else ""
        print(f"  ok      {t:<7} — ⊩₁{suf}{'' if t=='U' else ' / ⊩₀'+suf}{note}")
print(f"== {len(rty)} type formers, {miss} missing ==")
fail += miss

# ── 3. catch-all reliance (report only) ────────────────────────────────────
CATCHALL = [('spine?', lr), ('stablecd?', lr), ('stableA?', lr),
            ('trlam?', lr), ('homheaded?', lr), ('pw?', var), ('stkC?', var)]
print("\n== 3. formers taking a classifier's CATCH-ALL (review, not a failure) ==")
for name, src in CATCHALL:
    rows = re.findall(r'^' + re.escape(name) + r'\s+(.+?)=', src, re.M)
    explicit = {c for c in rtm if any(tok(c, r) for r in rows)}
    silent = [c for c in rtm if c not in explicit]
    if silent:
        print(f"  {name:<11} default for: {' '.join(silent)}")
print("  ⚠ a catch-all is often correct — but it is SILENT.  When adding a")
print("    former, CONFIRM each default above rather than inherit it.")

# ── 4. VACUOUS DISCHARGE — metatheorems that are TRUE but say NOTHING ──────
#
# ⚠ THE CLASS OF BUG THIS EXISTS FOR.  A rule can be added to `_⟶_` whose
#   subject-reduction row is discharged by `⊥-elim`/`()` because no typing
#   rule names its former yet.  That is SOUND and it is `--safe`-clean —
#   and it is INDISTINGUISHABLE FROM A PROOF in a green build.  The
#   `subTI` incident (`consistency` vacuous until fixed) is the same shape.
#
#   ⇒ vacuity is a fine INTERMEDIATE state.  It must never be a SILENT one.
print("\n== 4. VACUOUSLY discharged metatheorem rows (outstanding debt) ==")
subj = read(os.path.join(ROOT,'Metatheory','SubjectReduction.agda')); canon = read(os.path.join(ROOT,'Metatheory','Canonicity.agda'))
vac = 0
for fname, src, label in (('sr', subj, 'subject reduction'),
                          ('prog', canon, 'progress'),
                          ('usplit', canon, 'code canonicity')):
    # ⚠ leading whitespace ALLOWED: `prog`/`usplit` live inside a `mutual`
    #   block, so an `^`-anchored regex silently MISSED them — this check
    #   reported "none" while two vacuous rows were still present.
    rows = re.findall(r'^\s*' + fname + r'\s+.*$', src, re.M)
    bad = [r for r in rows if '⊥-elim' in r]
    if bad:
        vac += len(bad)
        print(f"  {fname:<7} ({label}): {len(bad)} of {len(rows)} rows are ⊥-elim")
        for r in bad:
            # show WHAT is being eliminated — that is what says whether the
            # row is legitimate or debt.  `noVar` is a STRUCTURAL
            # impossibility (no variables in ◇); a `gen-…` inversion that
            # returns ⊥ is a PLACEHOLDER for a missing typing rule.
            m = re.search(r'⊥-elim \(([\w-]+)', r)
            why = m.group(1) if m else '?'
            # ⚠ HEURISTIC, and it cannot be more than that: a name ending
            #   `-clash` or `noVar` refutes the premise STRUCTURALLY; a
            #   `gen-…` returning ⊥ is a PLACEHOLDER for a missing rule.
            #   Anything else is flagged for a HUMAN to classify.
            kind = ('structural' if why == 'noVar' or why.endswith('-clash')
                    else '⚠ PLACEHOLDER' if why.startswith('gen-')
                    else '? REVIEW')
            subj = re.search(r'\{[tc] = ([^}]*)\}', r)
            print(f"      {kind:<11} ⊥-elim ({why})"
                  f"{'  at ' + subj.group(1) if subj else ''}")
if vac == 0:
    print("  none — every row carries content")
else:
    print(f"  ⇒ {vac} row(s) discharged by ⊥.  `structural` is fine — the premise")
    print("    is genuinely uninhabitable.  ⚠ PLACEHOLDER stands in for a MISSING")
    print("    TYPING RULE and proves nothing about its former; it becomes a real")
    print("    obligation the moment that rule lands.  `? REVIEW` = classify by hand.")

# ── 5. PROMISSORY NOTES — comments that defer an obligation ────────────────
#
# A design choice in one layer whose obligation is discharged in another
# layer that does not exist yet.  The ι-rule's "junk tags reduce to junk;
# `⊢con` is what rules them out" was one, and it was FALSE as written —
# `lookupD`'s totality makes subject reduction false without a `k ∈D D`
# premise.  Nothing checked the note; a gate found it by accident.
import glob as _g
print("\n== 5. PROMISSORY NOTES (a comment is not a mechanism) ==")
_scanned = _g.glob(os.path.join(ROOT,"**","*.agda"), recursive=True)
if not _scanned:
    print("  ✗ FAIL — scanned 0 files; the glob is stale (see check 5/6 root)")
    FAIL = True
else:
    print(f"  (scanning {len(_scanned)} module(s) under {ROOT})")
import glob as _g
pat = re.compile(r'--.*\b(is what rules|will rule|ruled out by|handled by|'
                 r'deferred to|becomes real when|DELETE WHEN|TEMPORARY)\b',
                 re.I)
notes = 0
for f in sorted(_g.glob(os.path.join(ROOT,'**','*.agda'), recursive=True)):
    for i, line in enumerate(open(f), 1):
        if pat.search(line):
            notes += 1
            print(f"  {os.path.relpath(f,ROOT):<40}:{i}  {line.strip()[:66]}")
print(f"  ⇒ {notes} note(s).  Each asserts an invariant NOTHING CHECKS.")
print("    ⚠ RULE: totalising a partial function RELOCATES its obligation,")
print("      it does not remove it.  A new `_⟶_` rule should ship with the")
print("      STATEMENT of its subject-reduction obligation, even if the")
print("      proof is deferred — writing the statement is what exposes the")
print("      missing premise (that is how gate 5 found `k ∈D D`).")

# ── 6. CONDITIONAL lemmas with NO CONSUMER — the VACUITY blind spot ───────
#
# Check 4 catches vacuity in METATHEOREM ROWS (a case discharged by ⊥-elim).
# It does NOT catch a lemma whose HYPOTHESIS is unsatisfiable — that one is
# `--safe`, hole-free, green, and proves nothing.
#
# Measured 2026-08-14: `gcd-gt-gen`/`gcd-le-gen` were stated at VARIABLES
# with the comparison as a premise —
#     monusTm (nsuc a) (nsuc b) ⟶* nsuc d → …
# — but `monusTm` recurses on its SECOND argument, so at a variable `b` that
# natrec is STUCK and the premise is uninhabitable exactly where the lemma
# lives.  Both typechecked. Both proved nothing.
#
# Deciding satisfiability is out of reach, so this checks the SIGNAL that
# actually found it: a lemma that takes a REDUCTION as a hypothesis and
# which NOTHING CONSUMES.  A conditional lemma exists to be applied; if no
# call site ever discharges its premise, that premise is unexamined.
print("\n== 6. CONDITIONAL lemmas with NO CONSUMER (vacuity risk) ==")
srcs = {f: open(f).read() for f in sorted(_g.glob(os.path.join(ROOT,'**','*.agda'), recursive=True))}
decl = re.compile(r'^([^\s:()\[\]{}]+)\s*:\s*(.*)$')
risky = 0
for f, txt in srcs.items():
    lines = txt.split("\n")
    for i, line in enumerate(lines):
        m = decl.match(line)
        if not m: continue
        name, rest = m.group(1), m.group(2)
        if name.startswith('--'): continue
        # gather the full type: continuation lines are indented
        j, ty = i + 1, rest
        while j < len(lines) and (lines[j].startswith(' ') or lines[j].startswith('\t')):
            ty += " " + lines[j].strip(); j += 1
        # a REDUCTION appearing as a PREMISE: `⟶` with a later `→`
        k = max(ty.find('⟶*'), ty.find('⟶'))
        if k < 0 or '→' not in ty[k:]: continue
        # consumers: any mention outside its own declaration and clauses
        uses = sum(len(re.findall(r'(?<![A-Za-z0-9-])' + re.escape(name) + r'(?![A-Za-z0-9-])', t))
                   for t in srcs.values())
        own  = len(re.findall(r'^' + re.escape(name) + r'(?![A-Za-z0-9-])', txt, re.M))
        if uses - own <= 0:
            risky += 1
            print(f"  {f:<34}:{i+1:<5} {name}")
print(f"  ⇒ {risky} conditional lemma(s) with no consumer.")
print("    ⚠ Not a failure — a REVIEW list.  For each, ask: can the premise")
print("      be discharged AT THE ARGUMENTS THE LEMMA IS STATED FOR?  If")
print("      only concrete arguments can discharge it, the lemma belongs at")
print("      arbitrary TERMS, not at variables.")

if fail:
    print(f"\n!! FAIL: {fail} orphaned/missing.  Agda will NOT catch this —"
          " datatypes need no coverage.", file=sys.stderr)
    sys.exit(1)
PYEOF
