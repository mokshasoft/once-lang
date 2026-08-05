# SPIKE — THE WF-AXIS: sized induction as ordered inductives
## 2026-08-04 · paper half; the design, its two risky points, and the fork

**Goal:** kill the fuel/`Acc`/guard boilerplate.  Realization (b), the
Hom-instance: ℕ as the kernel's first ORDERED inductive — the order IS
the directed structure, and ≤-facts COMPUTE.

## 1. The formers

* `⊤` with intro `tt` — the smallest former possible, inert (needed as
  the "true" end of the computing order).  Canonicity: closed normal
  `⊤`-inhabitants are `tt`.
* `Nat` with `zero`/`suc` and the ORDINARY eliminator

      indℕ : P[zero] → ((n : Nat) → P[n] → P[suc n]) → (n : Nat) → P[n]
      indℕ z s zero    ⟶ z
      indℕ z s (suc n) ⟶ s n (indℕ z s n)

  — a TERMINATING rewrite (fires on canonical heads only, the J-rule
  pattern).  ★ NO primitive wfrec: strong induction is DERIVED from
  `indℕ` by below-tuples (Σ is in the kernel), so the kernel never
  carries an unguarded fixpoint.  The surface layer later compiles
  "recursive call at a Hom-smaller argument" to the derived
  combinator — that is where the fuel/Acc pain dies for USERS.

## 2. ★ THE COMPUTING ORDER — the axis's heart

      Hom Nat zero n           ⟶ ⊤
      Hom Nat (suc m) zero     ⟶ base          -- base is finally ⊥!
      Hom Nat (suc m) (suc n)  ⟶ Hom Nat m n

  Endpoint-shape-keyed, mutually disjoint, mirroring `Hom-U`/`Hom-Π`.
  Consequences, all definitional: `Hom Nat 2 5 ⟶* ⊤ ∋ tt` — an
  ≤-obligation is `tt` after computation, NO proof term carried;
  `hrefl` is ≤-refl; `tr` at the composition motive is ≤-trans;
  `Hom Nat (suc m) zero` is EMPTY through `base` (consistency reuses
  the existing emptiness — poetic and free).  Neutral-endpoint Homs
  stay stuck (the stuck-Hom clause absorbs them).

## 3. ★ RISKY POINT 1 — the classifier story for `⌜Nat⌝`, and THE FORK

`El ⌜Nat⌝ ⟶ Nat` would make Hom-at-decode COMPUTE at canonical
endpoints, so `⌜Nat⌝` is neither `pw?` (not Π) nor `stkC?` (a stable
code's Hom must stay stuck) — a THIRD kind: endpoint-computing.
Without care, `tr` at `⌜Nat⌝`-coded hrefl paths is typed-but-stuck ⇒
canonicity breaks.  Two scopings:

  **(N-out)** `Nat` as a TYPE former only, NO `⌜Nat⌝ ∈ U`.  Then no
  code decodes to `Nat` ⇒ no `⌜Hom⌝`-motive has a Nat-ambient ⇒ `tr`
  and `ap` never type at ℕ-paths ⇒ ZERO new eliminator rules; the
  whole §2 payoff lands with the smallest possible cascade.  Cost:
  `cong`-at-ℕ (`ap` needs coded sources) and ℕ-indexed codes in `U`
  are deferred — the same honest-boundary style as flat?/G3.

  **(N-in)** `⌜Nat⌝ ∈ U` with a new `nat?` classifier and the
  completion rules: `tr-J-Nat` (J at `⌜Nat⌝`-coded hrefls — sound,
  hrefl is genuinely reflexive) AND ★ RISKY POINT 2: the tt-path
  rules.  A closed path of a STRICT `Hom Nat t u` normalizes to `tt`
  (its type computes to ⊤), and `⊢conv` lets `tt` be a `tr`-path ⇒
  a rule `tr (⌜Hom⌝-motive) tt e ⟶ tt` keyed on `nat?` of the
  motive's spine.  Soundness argument (to mechanize): the result type
  at a strict path is itself strict (a ≤ t < u), hence ⊤-convertible,
  hence `tt`-typed.  Similarly `ap`'s completion at ℕ-sources.

  **Recommendation: land (N-out) first** — it delivers the pain-killer
  (computing order + derived strong induction) with the ap-landing-
  sized cascade, and (N-in) upgrades later exactly like `tr-J-Id` did
  (we have now twice demonstrated that stable-shape completions
  retrofit cleanly).

## 4. The LR clause — the THIRD payload

`⊩Nat ∋ t = SN t × (t ⟶snr* numeral)` — the reaches-canonical
payload, the same flavor as `IdPay` (and the U-payload): `indℕ`'s fund
case runs meta-induction on the reached numeral; exp/whred transports
prefix/peel head steps by `snr-det` exactly like `idpay-peel`.  `⊤`'s
clause: SN-only + reaches-`tt` (or SN-only if the canonicity route
suffices — decide while mechanizing).  Canon: numeral canonicity,
closed `indℕ`s always step, `base` stays empty ⇒ CONSISTENCY.

## 5. What stays untouched

`Id`/`jsub` act on ℕ for FREE (unrestricted eliminator — rewriting
about numbers works the day ℕ lands).  The W2b classifiers gain
catch-all/false rows only under (N-out).  Sized-family COERCION
(`tr` at `Pos` ℕ-families) needs (N-in) + `PosC` growth — deferred
with it.

## 6. The demo (the acceptance file, write FIRST)

`NbEPDirDBExamplesNat.agda`: numerals; `⊢plus` via `indℕ`;
`le-computes : Hom Nat 2 5 ⟶* ⊤` and its inhabitant `tt` — the
"no-Acc" moment; derived strong induction (`below`-tuple) typed and
fired on a numeral; `Id`-rewriting at ℕ (`jsub` on a numeral
equation); consistency corollary: `¬ (◇ ⊢ p ∷ Hom Nat 1 0)` via the
base-collapse.

## 7. THE STAGING (refined with the user, 2026-08-04)

  **Stage A — the datatype core** — ✅ **LANDED 2026-08-05, ONE
  SESSION** (the spike priced 2).  `Unit`/`unit` +
  `Nat`/`nzero`/`nsuc`/`natrec` through the whole tower: Pi → Var →
  Type → SR → Conf → Inj → Subj → LR → Fund → Canon → the acceptance
  file `NbEPDirDBExamplesNat.agda` (`⊢plus` by `natrec`,
  `plus-computes : 2+1 ⟶* 3`).  All 24 modules `--safe`, zero
  postulates, zero holes, zero TERMINATING pragmas.

  What the landing actually cost, and what it bought:

  * `natrec` is TYPE-motived (motive in the derivation only, the
    `⊢lam` pattern) — code motives need `⌜Nat⌝ ∈ U`, which is stage C.
    The step branch binds TWO variables (the number, then the IH).
  * The one genuinely new syntactic lemma is **`natrec-step-ty`**:
    instantiating the step motive at the number and then at the IH
    collapses to the motive at the SUCCESSOR.  That single equation is
    what makes `natrec-suc` type-preserving; `sub-comm-ext` /
    `ren-comm-ext` are its substitution/renaming twins.
  * The LR gains **`natstk?`** (the scrutinee never becomes a numeral)
    as a peer of `idstk?`/`apstk?` in the mutual stuckness block, and
    **`NatMem`** — the third payload flavor, shaped exactly like `SN`
    (neutral / constructor / head-expansion), so every transport is the
    SN transport.
  * `fund`'s `⊢natrec` recurses on `NatMem` and **nothing else**.  No
    fuel, no `Acc`, no measure, no size — the induction is on the
    semantic number itself.  That IS the WF axis's thesis, mechanized.
  * `natrecS` in Canon: a closed well-typed `natrec` always steps, so
    canonicity and consistency survive unchanged.

  ★ DESIGN CONSEQUENCE ALREADY VISIBLE FOR STAGE B: stage A registered
  `sh-Unit`/`sh-Nat : StkHd` — i.e. `Hom Nat a b` is currently a STUCK
  hom.  Stage B's rules make it compute, so `sh-Nat` must GO and
  `homSem₁ (⊩₁Nat …)` must be re-derived.  That is the first move of
  stage B, not a surprise to discover mid-walk.

  **Stage B — the computing order** (IN PROGRESS, 2026-08-05).
  SYNTACTIC HALF ✅ DONE AND GREEN: the three rules are in `Type`, and
  `SR`, `Conf`, `Inj`, `Subj` all absorb them.

  What the syntactic half actually cost:

  * `Inj`: `Hom` at `Nat` is the ONLY `_⁺ᵀ` clause that develops by the
    ENDPOINTS rather than the ambient.  `pHom-Nat-z/-sz/-ss` join the
    type-level parallel relation and the endpoint case tree is
    generated (left `pnzero` is decisive; a `pnsuc` left endpoint then
    splits the right one).
  * `Subj`: the ambient-generic Hom-inversion lemmas (`Hom-to-Hom`,
    `hom-to-Π`, `homred-inv`) are no longer true at a `Nat` ambient —
    `Hom-Nat-ss` keeps the type a `Hom` while CHANGING both endpoints,
    which is exactly what those lemmas denied.  Fixed with a `NoNat`
    guard.  The four `tr` sites have an existentially-bound ambient, so
    the guard is RECOVERED there by two transport lemmas: `homAmb→`
    (the ambient only reduces) and `homAmb←` (a `Nat` ambient stays
    `Nat`, so a non-`Nat` target forces a non-`Nat` source).
  * `hom-shape` gained `hsUnit`/`hsBase` arms at NO cost to its
    consumers — every consumer is a refutation at a specific shape
    (`U`, `Σ'`, `Id`, …) that `Unit`/`base` do not match.
  * ★ The staging paid off exactly as designed: because `Nat` has NO
    CODE until stage C, `El c` can never reduce to `Nat`, so the entire
    `El`-ambient theory of stages 1–A is untouched.

  SEMANTIC HALF ✅ DONE AND GREEN (same session).  What it took:

  1. `sh-Nat : StkHd Nat` DELETED; `⊩₀Hom`/`⊩₁Hom`'s witness moved from
     `StkHd H` to `StkHd (Hom H a b)`, and the new arm is
     `sh-NatH : homnat? a b ≡ true → StkHd (Hom Nat a b)`.
  2. `homnat?` is THREE LINES, because stage A's `natstk?` already says
     the hard part: a `nzero` left endpoint always fires, a `nsuc` left
     endpoint defers to the right one, any other decides alone.
  3. **`homNatSem`** is the theorem: a DOUBLE meta-induction on both
     endpoints' `NatMem`.  Zero on the left → `⊩₁Unit`; successor over
     zero → `⊩₁base`; successor over successor → peel and recurse; a
     stuck endpoint → the endpoint-keyed stuck order-hom.  Exact mirror
     of stage A's `fund` worker, which is why `NatMem` mirrors `SN`.
  4. `hom-shape` gained `hsUnit`/`hsBase` at no cost to its refutation
     consumers; `hom-shapeN` (guarded) keeps the sharp two-shape
     conclusion where the ambient is pinned (`fund`'s `⊢trU`).
  5. `Hombase-clash` and `HomUnit-clash` became AMBIENT-SENSITIVE — and
     correctly so: `Hom Nat 2 1` really does reduce to `base`.  Both
     are refined with the `NoNat` guard.

  ★ THE ONE REAL SCARE, and why it was already handled.  A closed
  normal path at a `Nat` ambient can now be `unit`, and NO `tr` rule
  fires on a `unit` path — so `trProgress`/`pathCanon` look broken.
  They are not: `⊢tr`'s premise `(Γ ▹ A) ⊢ var vz ∷ El c` types the
  SAME variable at both `A` and `El c`, and `El c ≅ᵀ Nat` is
  impossible (no ⌜Nat⌝ code until stage C).  So the ambient of a
  well-typed `tr` is PROVABLY never `Nat` (`tr-amb-nonat`), and
  transport along an order path simply cannot be FORMED yet.  Stage B
  needed no new restriction on `⊢tr`.  ★ This is precisely the
  "tt-path rules" item the spike scheduled for stage C: when ⌜Nat⌝
  joins `U`, `tr` at an order path becomes formable and WILL need a
  rule (transport along `≤` = the coercion / ≤-transitivity story).
  Stage C must land that rule together with ⌜Nat⌝, not after it.

  **Stage C — N-in** (IN PROGRESS, 2026-08-05).  SYNTACTIC FRONT HALF
  ✅ GREEN: `⌜Nat⌝`/`⌜Unit⌝` codes, `El-⌜Nat⌝`/`El-⌜Unit⌝` decodes,
  `⊢⌜Nat⌝`/`⊢⌜Unit⌝`, and `tr-J-Nat`/`tr-J-Unit`, through Pi, Var,
  Type, SR, Conf and Inj.

  ★★ RISKY POINT 1 IS **REAL**, and the spike was right.  An earlier
  note in this file called it "settled cheaply" on the grounds that
  `stkC? ⌜Nat⌝ = true` typechecks.  **That claim was premature and is
  RETRACTED.**  Typechecking the classifier is not the same as the J
  rule it licenses being sound, and it is not.

  **`tr-J-Nat` BREAKS SUBJECT REDUCTION.**  Counterexample, in a
  context `Γ` holding `k j : Nat` and `x : base`:

  * `Hom-Nat-z` reads `Hom Nat nzero n ⟶ Unit` for **any** `n` — the
    right endpoint is discarded.  So `Hom Nat nzero nzero` and
    `Hom Nat nzero (nsuc j)` share the reduct `Unit` and are therefore
    CONVERTIBLE.
  * Hence `hrefl ⌜Nat⌝ nzero`, whose own type is
    `Hom (El ⌜Nat⌝) nzero nzero`, is typeable by `⊢conv` at
    `Hom Nat nzero (nsuc j)`.  **A reflexivity no longer pins its
    endpoints**, because the order type it lives in is collapsing.
  * Feed that as `⊢tr`'s path with `t = nzero`, `u = nsuc j`, motive
    code `c = ⌜Nat⌝` (forced: the premise `(Γ ▹ A) ⊢ var vz ∷ El c`
    with `A = Nat` gives `El c ⟶ᵀ* Nat`, so `c ⟶* ⌜Nat⌝`), and
    `a = nsuc k`.  Then `e`'s type is `Hom Nat (nsuc k) nzero ⟶ base`,
    inhabited by `x`; the conclusion's type is
    `Hom Nat (nsuc k) (nsuc j) ⟶ Hom Nat k j`, which is STUCK.
  * `tr-J-Nat` reduces the term to `e`.  Subject reduction would need
    `base ≅ᵀ Hom Nat k j`.  Both are normal and distinct. ✗

  **DECISION (2026-08-05, made with the counterexample in hand):**

  1. **DELETE `tr-J-Nat`**, and set **`stkC? ⌜Nat⌝ = false`**.  `stkC?`
     IS the J-ability key (it is what `tr-J-Hom` and `ap-J` test), so
     the classifier must not claim what the rule cannot deliver.
  2. `⌜Unit⌝` is **NOT** affected — keep `stkC? ⌜Unit⌝ = true` and
     `tr-J-Unit`.  `Hom Unit t u` has no computation rule, so a
     `hrefl ⌜Unit⌝ s` pins its endpoints normally.  **Only `Nat` is
     poisoned, and precisely because only `Nat` has the collapsing
     Hom.**  This is the sharp statement of the risky point: it is not
     "datatype codes are exotic", it is "ORDERED types cannot be
     J-able, because their path space is proof-irrelevant".
  3. So `⌜Nat⌝` is neither `pw?` nor `stkC?` — **the third code kind
     the spike predicted.**  G2's `codeCanon` (closed normal U-codes
     split `pw? ∨ stkC?`) must become a THREE-way split.  Budget for
     that: it is a real theorem change in `NbEPDirDBCanon`, not a row.
  4. Consequently the **tt-path rule is not optional and not a
     nice-to-have** — it is what RESTORES `trProgress`.  With J
     disabled at `⌜Nat⌝`, a closed `tr` at a `hrefl ⌜Nat⌝ s` path has
     no rule to fire, so `trProgress` is false until order-transport
     exists.  Design it as ≤-coercion: transport along `Hom Nat m n`
     carries a proof at `m` to one at `n`, and its computation must
     follow the SAME endpoint case tree as the order rules.

  ⚠ The front-half commits (`stage C (WIP)`) currently contain
  `tr-J-Nat` and `stkC? ⌜Nat⌝ = true`.  **Undo those two before
  building further**; the rest of the front half (codes, decodes,
  `⊢⌜Nat⌝`, `tr-J-Unit`, and all the Conf/Inj plumbing) stands.

  ★ METHOD NOTE, for this file's own §"lessons": the retracted claim
  was made because a module typechecked, not because the property was
  argued.  `FINDINGS`/`HANDOFF` already carry "match a claim's strength
  to the decision it licenses — this repo has been burned once by a
  claim outrunning its evidence (`subTI`, actually false while
  asserted)".  Same failure mode, caught one session later this time.

  ★ THE REAL WORK LEFT is the one stage B predicted, and it has taken
  a precise shape.  `El c` can now reduce to `Nat`, so stage B's
  `NoNat` guard in `Subj` is DEAD: `nonat-red nn-El El-⌜Nat⌝` is an
  unfillable hole (`NoNat` is no longer preserved by `⟶ᵀ`), and
  `stamb-red` wants `StkAmb Nat`/`StkAmb Unit` arms for the same
  reason.  The fix is a CONVERGENCE, not a new idea: stage B
  introduced two guards for the same phenomenon — `NoNat` (ambient) in
  `Subj` and `homnat?`/`sh-NatH` (endpoints) in `LR` — and stage C
  forces them to merge.  `Subj`'s Hom-inversion lemmas must be re-keyed
  off the ENDPOINTS (`homnat?`), exactly as `⊩₁Hom`'s witness already
  is.  Once that lands, `tr-amb-nonat` in `Canon` (which proved the
  `tr` ambient is never `Nat`) becomes FALSE and must be replaced by
  the tt-path rule:

  ★ RISKY POINT 2, now unavoidable and correctly scheduled here: with
  a `Nat` code, `tr` at an ORDER path IS formable, and no rule fires on
  a `unit` path.  The tt-path rule must land in this stage.  Note the
  shape it wants: transport along `Hom Nat m n` is exactly `≤`-
  coercion, so the rule is the ≤-transitivity/coercion story the
  staging always said stage C owned.

  Also still ahead: `⊩₀Unit`/`⊩₀Nat` (level 0 gains the datatype
  interps — `El (⌜Hom⌝ ⌜Nat⌝ a b)` now decodes to `Unit`, so the SMALL
  types include them for the first time), the level-0 clash matrix
  rows, `Fund`, `Canon`, and the stage C acceptance file.

  Remaining module status at the checkpoint: Pi/Var/Type/SR/Conf/Inj
  GREEN; Subj 8 coverage holes (one of them the `NoNat` collapse
  above); LR 8; Fund/Canon unmeasured behind them.

  **Stage C — N-in** (original scoping): `⌜Nat⌝ ∈ U`, `tr-J-Nat`,
  the tt-path rules (§3 risky point 2), `cong`-at-ℕ, sized-family
  coercion via `PosC` growth, and `tr`-as-≤-transitivity (NOTE: the
  composition motive needs the coded ambient, so the general
  open-endpoint ≤-trans is C-territory; at canonical numbers it is
  trivial — both sides compute to `Unit`).

## 8. Mechanized-half order (the ap-landing template)

⊤/Nat/indℕ + the three Hom-Nat rules through Pi → Var → Type → SR →
Conf (endpoint-keyed Takahashi rows mirror Hom-Π's) → Inj (Nat/⊤
reducts + the Hom-Nat arms in hom-shape/HomStk) → Subj (gen-lemmas +
sr; the Hom-Nat rules' sr rides endpoint inversion) → LR (the numeral
payload) → Fund (indℕ by numeral meta-induction) → Canon → the
acceptance file greens.  Estimate: 2 sessions, LR/Fund second.
