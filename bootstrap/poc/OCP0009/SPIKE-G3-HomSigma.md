# SPIKE G3 (paper half) — `Hom` at `Σ'` ambients: the design space
## 2026-08-04 · the critical-pair spike's analysis phase, per ARCHITECTURE §G3

**Status: design settled to three findings and one fork; the mechanized
half (critical pairs of the chosen rule set) is the next session.**

---

## Finding 1 — THE MOTIVE OBSTRUCTION: the naive Σ-rule is INEXPRESSIBLE

The wished-for type-level rule

    Hom (Σ' A B) p q ⟶ Σ' (Hom A (fst p) (fst q))
                          (Hom B[fst q]… (tr ⟨B-as-motive⟩ (var vz) (snd p)…) (snd q)…)

needs `tr` at the motive family `x ↦ B[x]` — an ARBITRARY type family.
But W2's eliminator does not have general transport: `⊢tr`'s motive is
hard-wired to `⌜Hom⌝ c a (var vz)` and `⊢trU`'s to `var vz` — `gen-tr`'s
`TrGen = tgC | tgU` dichotomy is the PROOF (it is the total inversion).
W2's `tr` is directed path algebra (transporting homs along homs +
directed univalence), not J-for-arbitrary-families.  Consequences:

  * At the TYPE level the rule is doubly dead: general `B` has no code,
    and even code-shaped `B = El c₂` leaves the `tr` untypeable.
  * Any Σ-unfolding that mentions a transport of the second component
    FIRST requires generalizing `⊢tr` to arbitrary code-family motives
    `(Γ ▹ A) ⊢ d ∷ U` — a kernel-eliminator change, not a rule addition.

## Finding 2 — THE J-COLLAPSED TERM RULE: `hrefl` at `⌜Σ⌝` needs NO `tr`

For the TERM-level canonicity rule the transport evaporates: an hrefl's
endpoints coincide, so the second component's transported source sits on
a REFLEXIVITY path and J-collapses *before the rule is even stated*:

    hrefl-Σ :  hrefl (⌜Σ⌝ c₁ c₂) s ⟶
               pair (hrefl c₁ (fst s)) (hrefl (subTm (single (fst s)) c₂) (snd s))

No `tr` in the RHS.  The rule is expressible in TODAY'S kernel.  Its
typing story still routes through the Σ'-of-Homs TYPE (the pair needs a
`Σ'`-type for the Hom it inhabits), i.e. it cannot land alone — it needs
the type-level unfolding for `El (⌜Hom⌝ (⌜Σ⌝ c₁ c₂) a b)`-shaped types,
where by Finding 1 the second component's SOURCE endpoint must be the
transported term.  For the hrefl instance that source J-reduces inside
the type by ordinary conversion; for the GENERAL type the `tr` remains,
returning us to Finding 1.  So:

  * `hrefl-Σ` is the cheap half.  The Σ'-of-Homs TYPE is the expensive
    half, and it is exactly as blocked as the general rule.

## Finding 3 — THE CASCADE IS A CRITICAL PAIR, NOT A FLAG FLIP

Flipping `stkC? ⌜Σ⌝` (adding `hrefl-Σ`) breaks `tr-J-Σ`'s determinism:

    tr (⌜Hom⌝ cM aM (var vz)) (hrefl (⌜Σ⌝ c₁ c₂) s) e
      ── tr-J-Σ ──▶ e
      ── ξ-trᵖ (hrefl-Σ) ──▶ tr … (pair α β) e     ← STUCK today

Joining demands a `tr`-at-`pair`-paths rule (transporting a hom along a
Σ-path, componentwise on the ⌜Hom⌝-motive's spine) — ANOTHER new rule
with its own pairs — or dropping `tr-J-Σ` while making the pair-path rule
total enough for canonicity (G2's `jfire` loses its `⌜Σ⌝` row; `trS`'s
canonical-path analysis gains a `can-pair` case that must STEP).
The W2b classifiers absorb the flip mechanically (`stkC?`'s row, `CSR`'s
spine, `payHomT`) but the REDUCTION theory does not: the pair is the real
spike content for the mechanized half.

## The fork (decide at the start of the mechanized spike)

**(a) The restricted landing — no eliminator change.**  Add `hrefl-Σ` +
the Σ'-of-Homs type rule RESTRICTED to hrefl-reachable instances… this
collapses on inspection: type rules cannot see path values.  Concretely
(a) means: `hrefl-Σ` + `tr`-at-`pair` (drop `tr-J-Σ`), and the Σ-HOM TYPE
stays stuck (Σ-paths are consumed by `tr`, never introduced except as
hrefl-unfoldings).  Directed-path algebra gets pairs; the path SPACE at
Σ stays silent.  Small, honest, closes the `tr-J-Σ` wart.

**(b) The general landing — generalize the eliminator.**  `⊢tr` at any
vz-free code family `d`; J restricted to `stkC?` path-codes as today;
`tr-taut` stays; NEW `tr-dead` (vz-dead motive: transport is identity);
the `⌜Hom⌝`-spine motives keep `tr-pw`.  The genuinely-dependent-motive-
over-pw-path case has NO rule — and cannot: directed transport of an
arbitrary family along a function-path does not compute.  Canonicity
then FAILS at closed `tr d (lam f) e` with `d` live and non-spine —
typed instances exist (Σ over Π with dependent second component).  (b)
is therefore NOT a landing; it is a research program (the dHoTT
transport-at-Π problem).  Record and defer.

**Recommendation: (a).**  It is the G1-shaped move: finite rule set,
mechanizable pairs, canonicity preserved (G2's induction extends — the
`can-pair` path case steps by the new rule).  The Σ path SPACE joins the
W2 deferral list with a precise obstruction record (Finding 1 + the (b)
analysis) instead of a vague "needs transport".

## The mechanized half's checklist (next session)

1. `tr`-at-`pair` rule statement: `tr (⌜Hom⌝ cM aM (var vz)) (pair α β) e`
   — the ⌜Hom⌝-spine motive determines the shape; spike its SR + the
   `tr-J-Σ`-replacement join (`tr … (hrefl (⌜Σ⌝ c₁ c₂) s) e ⟶* e` both ways).
2. `hrefl-Σ` vs `CSR`/`payHomT`: the code-spine machinery meets a rule
   that consumes the WHOLE hrefl — check `csr-det`/`snr-hreflᶜ` rows.
3. `stkC?` flip fallout sweep: `jfire`, `trS`/`trCS` (G2), `sem-⌜Σ⌝`'s
   payload (`⊤` today — stays `⊤`? the decode is still non-Π), Subj's
   `StkAmb`/`homred-inv` (`sh-Σ` row), Conf triangle rows.
4. G2 extension: `pathCanon` gains pair-shaped paths at Σ-decodes;
   `consistency` untouched (base is not Σ).
