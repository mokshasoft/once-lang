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

  **Stage B — the computing order** (NEXT): the three `Hom Nat` rules
  on top (the §2 payoff).  Type-level rules riding the Hom-Π pattern
  (Type/SR/Conf-type-level/Inj/Subj + StkHd/stuck-Hom rows in the LR).
  Delta over A, now that A is banked: drop `sh-Nat`, re-derive
  `homSem₁` at `⊩₁Nat` (the interp must FOLLOW the endpoints), add the
  endpoint-keyed type-level Takahashi rows, and extend `hom-shape` /
  `Hom-to-Hom` / `HomStk` with the three Nat arms.

  **Stage C — N-in** (separate spike later): `⌜Nat⌝ ∈ U`, `tr-J-Nat`,
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
