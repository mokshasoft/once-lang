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

## 7. Mechanized-half order (the ap-landing template)

⊤/Nat/indℕ + the three Hom-Nat rules through Pi → Var → Type → SR →
Conf (endpoint-keyed Takahashi rows mirror Hom-Π's) → Inj (Nat/⊤
reducts + the Hom-Nat arms in hom-shape/HomStk) → Subj (gen-lemmas +
sr; the Hom-Nat rules' sr rides endpoint inversion) → LR (the numeral
payload) → Fund (indℕ by numeral meta-induction) → Canon → the
acceptance file greens.  Estimate: 2 sessions, LR/Fund second.
