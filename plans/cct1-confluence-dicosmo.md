# CCT1 βη-Confluence: Pivot to Di Cosmo Factorisation

## STATUS (2026-06-08): GOAL DISPROVEN — DO NOT RE-ATTEMPT

Full βη confluence at CCT1 is **false**, proved (zero postulates) in
`formal/Theory/Syntax/StrongCCL/CCT1/NonConfluenceWitness.agda` (`¬confluent`).
The term `curry (apply ∘ ⟨ fst ∘ fst , snd ⟩) ∘ snd` reduces to two distinct
βη-NFs (via curry-η; and via curry-compose+assoc) that cannot be joined because
`assoc` is one-directional and `curry-η` needs the rigid shape `f ∘ fst`. This is
the typed-combinator instance of the Klop/Curien-Hardin phenomenon. Everything
below this section is the superseded pursuit, kept as a research log.

**Resolution (see `bootstrap/theory/normalizer-vs-compiler-path.md`):** confluent
β-fragment *core* (Curien1985) for conversion + `≈βη`-preserving passes for the
optimizer; for the bootstrap, an evaluator/NbE normalizer where determinism +
totality replace confluence. η is handled by *expansion*, never contraction.

**Removed (orphaned, all rested on the disproven goal; recover via
`git show <pre-cleanup-commit>:<path>`):** `CCT1/{ConfluenceFull, ConfluenceFullViaHR,
ConfluenceFullViaDiCosmoHardin, LocalConfluence, HardinSplit, HardinWN,
ParallelReductionSplit, Diamond1, Diamond2, Commute12, NFClosedAnalysis,
RuleSplit}` and `Derived/DiCosmoFactor`. `LocalConfluence` housed the false
`local-confluent-rest` postulate from which the old `cct1-confluence` was derived.

**Kept (reusable):** `CCT1/Tait` (strong normalization), `CCT1/Diamond` +
`CCT1/DecidableEquality` + `CCT1/ParallelReduction` (β-fragment parallel-reduction
work), and the confluent `Curien1985` core.

---

## Status (historical)

Strategic pivot from Newman+Tait and Hindley-Rosen+Takahashi to **Di Cosmo's
Lemma 2.7** (factorisation of confluence into a SN inner system + outer
confluence on inner-normal-forms).

## Why we pivoted

We attempted two confluence approaches at CCT1 and hit obstacles in both:

**Newman + Tait (existing `Theory.Syntax.StrongCCL.CCT1.ConfluenceFull`).**
SN proven via Tait reducibility candidates. Local confluence partially
proven; the open postulate `local-confluent-rest` is structurally blocked
by the Curien curry-η critical pair at `(curry h) ∘ id` (curry-compose vs
id-right give non-elementary-joinable reducts).

**Hindley-Rosen + Takahashi parallel reduction (`ConfluenceFullViaHR`).**
Split parallel reduction into ⟹₁ (everything except eta-pair-gen) and ⟹₂
(eta-pair-gen + congruences). Goal: isolate the eta-pair-gen non-linearity
into Diamond ⟹₂ alone. Result: ⟹₁ itself fails the Triangle property
because the same `(curry h) ∘ id` critical pair admits curry-compose and
id-right firings whose single-step reducts don't join. The Hindley-Rosen
split addressed eta-pair-gen but exposed the curry-compose/id-right
critical pair in ⟹₁.

**Literature confirms.** Hardin 1989 (TCS 65) explicitly states that
classical confluence techniques (Newman parallelisation, Takahashi parallel
reduction) do NOT work on this exact rule set. She invents the
"Interpretation Method" specifically to dodge these obstacles. Di Cosmo
1996 (JFP) generalises Hardin's trick into a clean four-condition lemma.

There is **no published Agda/Coq/Lean mechanisation** of CCC-βη confluence;
our port would be a contribution.

## CCT1 rule inventory

12 rules total, indexed by family. Where defined: `BaseRules/CCTB` and
`BaseRules/CCT1`.

### β-rules (6)

| Rule       | LHS                            | RHS                  | Origin |
|------------|--------------------------------|----------------------|--------|
| fst-pair   | `fst ∘ ⟨ f , g ⟩`              | `f`                  | CCTB   |
| snd-pair   | `snd ∘ ⟨ f , g ⟩`              | `g`                  | CCTB   |
| eta-pair   | `⟨ fst , snd ⟩`                | `id`                 | CCTB   |
| id-left    | `id ∘ f`                       | `f`                  | CCTB   |
| id-right   | `f ∘ id`                       | `f`                  | CCTB   |
| curry-β    | `apply ∘ ⟨ curry f , g ⟩`      | `f ∘ ⟨ id , g ⟩`     | CCT1   |

### η-rules (3)

| Rule         | LHS                                       | RHS                                      | Origin |
|--------------|-------------------------------------------|------------------------------------------|--------|
| curry-η      | `curry (apply ∘ ⟨ f ∘ fst , snd ⟩)`       | `f`                                      | CCT1   |
| curry-apply  | `curry apply`                             | `id`                                     | CCT1   |
| curry-compose| `curry f ∘ g`                             | `curry (f ∘ ⟨ g ∘ fst , snd ⟩)`          | CCT1   |

### s-rules (4)

| Rule         | LHS                              | RHS                          | Origin |
|--------------|----------------------------------|------------------------------|--------|
| assoc        | `(f ∘ g) ∘ h`                    | `f ∘ (g ∘ h)`                | CCTB   |
| pair-dist    | `⟨ f , g ⟩ ∘ h`                  | `⟨ f ∘ h , g ∘ h ⟩`          | CCTB   |
| eta-pair-gen | `⟨ fst ∘ h , snd ∘ h ⟩`          | `h`                          | CCTB   |
| term-unique  | `terminal ∘ f`                   | `terminal`                   | CCTB   |

## Critical-pair census

The pairs we expect to hit. Joinable (J) means joinable in finitely many
steps; "non-elementary" means more than one step needed.

| # | Locus                              | Rule A         | Rule B          | Joinability                                                                                       |
|---|------------------------------------|----------------|-----------------|---------------------------------------------------------------------------------------------------|
| 1 | `(curry h) ∘ id`                   | curry-compose  | id-right        | J non-elementary (3+ steps): id-right gives `curry h`; curry-compose gives `curry (h ∘ ⟨ id ∘ fst , snd ⟩)` which reduces to `curry h` via id-left + eta-pair + id-right. THE problematic pair. |
| 2 | `((h ∘ k) ∘ id)`                   | assoc          | id-right        | J non-elementary (2 steps): id-right gives `h ∘ k`; assoc gives `h ∘ (k ∘ id)` which reduces via id-right. |
| 3 | `(⟨ h , k ⟩ ∘ id)`                 | pair-dist      | id-right        | J non-elementary (3 steps): id-right gives `⟨ h , k ⟩`; pair-dist gives `⟨ h ∘ id , k ∘ id ⟩` which reduces via two id-rights. |
| 4 | `(terminal ∘ id)`                  | term-unique    | id-right        | J elementary: both reduce to `terminal`. |
| 5 | `⟨ fst ∘ h , snd ∘ h ⟩`            | eta-pair-gen   | sub-redex of h  | NON-LINEAR pattern; if subreduction differs on the two h-copies, redex breaks. Joinable via Decidable Term equality. |
| 6 | `curry (apply ∘ ⟨ id ∘ fst , snd ⟩)` | curry-η      | id-left + …     | J non-elementary: curry-η gives `id`; id-left+eta-pair+id-right path also reaches `id` via curry-apply. Documented in `BaseRules/CCT1` comments. |

Pairs 1–3 share a common shape: a structural rule (curry-compose, assoc,
pair-dist) and id-right both fire at root of `_ ∘ id`. id-right "wins"
locally but blocks the structural rule's single-step joinability. THIS
IS THE CHARACTERISTIC HARDIN/CURIEN OBSTACLE.

## R₁ / R₂ split — proposal

Following Hardin's pattern, R₁ is the SN sub-system that performs
"normalising" reductions, and R₂ is the "creative" rule that interacts
with R₁'s normal forms.

### Option A (Hardin-style: restricted id-right in R₁)

R₁ rules (sub-relation of ⟶βη):

* All s-rules: `assoc`, `pair-dist`, `eta-pair-gen`, `term-unique`
* β-rules: `fst-pair`, `snd-pair`, `eta-pair`, `id-left`, `curry-β`
* **Restricted** `id-right`: only when LHS is atomic (`id`, `fst`, `snd`,
  `apply`, `terminal`). NOT when LHS is `curry`, `∘`, `⟨,⟩`.

R₂ rules:

* η-rules: `curry-η`, `curry-apply`, `curry-compose`
* **Residual** `id-right`: only when LHS is `curry`, `∘`, `⟨,⟩`.

Rationale:

1. R₁ avoids the bad critical pairs because the id-right cases that
   conflict with curry-compose (#1), assoc (#2), pair-dist (#3) are NOT
   in R₁ — they live in R₂.
2. R₁-normal forms have no `f ∘ id` for f atomic, so the residual id-right
   in R₂ can fire freely.
3. R₁ should be SN: each rule strictly decreases a syntactic measure
   (term size + id-count), with eta-pair-gen the only non-trivial case,
   handled by the Hardin-Laville termination argument.
4. R₁-nf closure under R₂ requires checking each R₂ rule preserves R₁-nf
   status. curry-η, curry-apply preserve trivially. curry-compose may
   introduce new R₁ redexes (e.g., `fst ∘ ⟨ g ∘ fst , snd ⟩` if the inner
   f is fst). Need careful local analysis.

Concern with Option A: R₁-nf closure under curry-compose is NOT automatic.
We may need to either (a) restrict R₂'s curry-compose firing (requires
identifying problematic shapes), or (b) iterate R₁-normalisation after
each R₂ step, which corresponds to a multi-step formulation of the
factorisation.

### Option B (Di Cosmo-style: η-rules in R₂ alone)

R₁ rules:

* All β-rules (full), all s-rules.

R₂ rules:

* All η-rules: `curry-η`, `curry-apply`, `curry-compose`.

Rationale:

1. R₁ matches Curien1985's β-fragment. Confluence of R₁ at CCT1 is
   essentially Takahashi's parallel-reduction argument applied to the
   β-fragment with structural rules — already partially mechanised in
   `Theory.Syntax.Curien1985.CCT1.Diamond`.
2. R₂'s only critical pair issue is curry-compose vs curry-η at certain
   nested shapes; on R₁-nf these are tractable.
3. SN of R₁: known result; a syntactic measure works.
4. R₁-nf closure under R₂: curry-η, curry-apply, curry-compose must each
   preserve R₁-nf status. curry-compose can introduce β-redexes (the
   same problem as Option A).

### Recommendation

**Option B looks cleaner** because:

* R₁ corresponds to a fragment we already understand (β + structural).
* R₂ has only 3 rules, simplifying confluence on R₁-nf.
* The Curien1985 β-fragment work is partially reusable.

The R₁-nf closure under curry-compose is the hardest sub-obligation;
likely requires showing curry-compose either preserves R₁-nf or, when it
introduces a new R₁ redex, the subsequent R₁ reduction commutes with
later R₂ steps (Di Cosmo's commutation condition handles this).

## Plan

1. **`Theory/Derived/DiCosmoFactor.agda`** — abstract Lemma 2.7, parametric
   over R₁/R₂. Zero postulates. Analog of `HindleyRosen.agda`. ~80 lines.
2. **R₁ definition** as sub-relation of `_⟶βη_` at CCT1 + bridges. ~100 lines.
3. **R₂ definition** + bridges. ~50 lines.
4. **R₁ SN** — port of Curien1985 β-confluence SN argument + structural
   rule integration. Existing partially-mechanised work.
5. **R₁-nf closed under R₂** — case analysis on each R₂ rule. ~150 lines.
6. **R₂ confluent on R₁-nf** — local confluence on R₁-nfs (the bad CPs
   don't arise) + SN of R₂ on R₁-nfs + Newman. ~200 lines.
7. **R₂* commutes with R₁*-to-nf** — diagram-by-diagram. ~150 lines.
8. **Top-level theorem** in `ConfluenceFullViaDiCosmo.agda` — apply abstract
   lemma. ~50 lines.

Estimated 4-6 sessions. Each step constructive, no postulates targeted.

## What survives from Hindley-Rosen attempt

* `ParallelReduction.agda` — full ⟹ definition reusable.
* `Diamond.agda` `_*` — reusable for proving R₁ confluence (R₁ has the
  better structural properties for Takahashi).
* `DecidableEquality.agda` — stays useful for any non-linear pattern.
* `HindleyRosen.agda` (abstract) — stays as a reusable derived theorem.
* `ParallelReductionSplit.agda`, `Diamond1.agda`, `Diamond2.agda`,
  `Commute12.agda`, `ConfluenceFullViaHR.agda` — keep but mark
  superseded; they document the failed approach with precise obstacle
  identification, which is informative for downstream readers.

## References

* Hardin 1989 "Confluence Results for the Pure Strong Categorical Logic CCL", TCS 65.
* Di Cosmo 1996 "A confluent reduction for the λ-calculus with surjective pairing and terminal object", JFP. Lemma 2.7 is the target abstract lemma.
* Klop & de Vrijer 1989 "Unique Normal Forms for Lambda Calculus with Surjective Pairing", IC 80.
