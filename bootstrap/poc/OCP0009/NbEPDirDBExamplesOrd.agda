------------------------------------------------------------------------
-- OCP-0009 — EXAMPLES, WF-AXIS STAGE B: THE COMPUTING ORDER.  THE
-- ACCEPTANCE TEST (SPIKE-WF §7), written FIRST; the kernel is landed
-- under it until it greens.
--
-- The claim stage B has to earn: on ℕ the DIRECTED structure IS the
-- order.  `Hom Nat m n` does not merely *represent* `m ≤ n` — it
-- COMPUTES to `Unit` when the inequality holds and to the empty type
-- when it does not, so at canonical numbers an order proof is
-- `unit` and a false inequality is uninhabited BY CONSISTENCY.
--
--   ★ `le-computes`  — `Hom Nat 1 2 ⟶ᵀ* Unit`   (the order reduces)
--   ★ `lt-empty`     — `Hom Nat 2 1 ⟶ᵀ* base`   (…and so does its
--                       negation, onto the type with no closed terms)
--   ★ `⊢le`          — the ORDER PROOF is literally `unit`
--   ★ `no-le`        — `2 ≤ 1` has NO closed proof, and the argument
--                       is `consistency`, not a new induction
--   ★ `le-refl-2`    — reflexivity computes too
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPDirDBExamplesOrd where

open import normalizer.Syntax.Types using ( _≡_; refl; ⊥ )
open import poc.OCP0009.NbEPDirDBPi
  using ( Cx; ε; _∙; RTy; base; U; El; Hom; Unit; Nat
        ; RTm; unit; nzero; nsuc; absurd; ordtr )
open import poc.OCP0009.NbEPDirDBType
  using ( _⟶ᵀ_
        ; Hom-Nat-z; Hom-Nat-sz; Hom-Nat-ss
        ; _≅ᵀ_; credᵀ; csymᵀ; ctrnᵀ
        ; Ctx; ◇; ⌊_⌋
        ; _⟶_; _⟶*_; done; step
        ; ordtr-z; ordtr-sss
        ; _⊢_∷_; ⊢unit; ⊢conv; ⊢nsuc; ⊢absurd; ⊢ordtr )
open import poc.OCP0009.NbEPDirDBInj using ( red→≅ᵀ; _⟶ᵀ*_; doneᵀ; stepᵀ )
open import poc.OCP0009.NbEPDirDBCanon using ( consistency )

n1 n2 : {Γ : Cx} → RTm Γ
n1 = nsuc nzero
n2 = nsuc (nsuc nzero)

------------------------------------------------------------------------
-- ★ 1 ≤ 2 COMPUTES.  Two successor-peels, then the zero rule.
------------------------------------------------------------------------

le-computes : {Γ : Cx} → Hom (Nat {Γ}) n1 n2 ⟶ᵀ* Unit
le-computes =
  stepᵀ (Hom-Nat-ss _ _)
    (stepᵀ (Hom-Nat-z _) doneᵀ)

-- …so the ORDER PROOF is `unit`: no `≤`-constructor, no induction.
⊢le : ◇ ⊢ unit ∷ Hom Nat n1 n2
⊢le = ⊢conv ⊢unit (csymᵀ (red→≅ᵀ le-computes))

-- reflexivity computes as well — `2 ≤ 2` peels twice and lands on Unit.
le-refl-2 : {Γ : Cx} → Hom (Nat {Γ}) n2 n2 ⟶ᵀ* Unit
le-refl-2 =
  stepᵀ (Hom-Nat-ss _ _)
    (stepᵀ (Hom-Nat-ss _ _)
      (stepᵀ (Hom-Nat-z _) doneᵀ))

⊢le-refl-2 : ◇ ⊢ unit ∷ Hom Nat n2 n2
⊢le-refl-2 = ⊢conv ⊢unit (csymᵀ (red→≅ᵀ le-refl-2))

------------------------------------------------------------------------
-- ★ 2 ≤ 1 COMPUTES TO THE EMPTY TYPE — and that is the whole proof
--   that it is unprovable.  `base` has no closed inhabitants
--   (`consistency`, NbEPDirDBCanon), so the refutation is a
--   conversion followed by the kernel's own consistency theorem.  No
--   new induction, no fuel, no `Acc`.
------------------------------------------------------------------------

lt-empty : {Γ : Cx} → Hom (Nat {Γ}) n2 n1 ⟶ᵀ* base
lt-empty =
  stepᵀ (Hom-Nat-ss _ _)
    (stepᵀ (Hom-Nat-sz _) doneᵀ)

no-le : {t : RTm ⌊ ◇ ⌋} → ◇ ⊢ t ∷ Hom Nat n2 n1 → ⊥
no-le d = consistency (⊢conv d (red→≅ᵀ lt-empty))

------------------------------------------------------------------------
-- ★★★ WF-AXIS STAGE E: ORDER TRANSPORT.  Everything below was
--     UNREACHABLE before `ordtr` — `tr` cannot serve, because it is
--     endpoint-BLIND (its endpoints live only in the derivation) and at
--     a `Nat` ambient the answer depends on them.
------------------------------------------------------------------------

n3 : {Γ : Cx} → RTm Γ
n3 = nsuc (nsuc (nsuc nzero))

-- ★ 1 ≤ 2 and 2 ≤ 3 compose, and the composite COMPUTES to `unit`:
--   peel all three bounds once (`ordtr-sss`), then the lower bound is
--   `nzero` and the order discharges (`ordtr-z`).  Two steps, no
--   induction — this is ≤-transitivity as a REDUCTION.
trans-computes : {Γ : Cx} → ordtr {Γ} n1 n2 n3 unit unit ⟶* unit
trans-computes =
  step (ordtr-sss _ _ _ _ _)
    (step (ordtr-z _ _ _ _) done)

-- ★★ …and transitivity types at OPEN naturals, which is the whole
--    reason the former exists.  No numerals, no case split, no `Acc`.
⊢trans : {Γ : Ctx} {a t u p q : RTm ⌊ Γ ⌋} →
         Γ ⊢ a ∷ Nat → Γ ⊢ t ∷ Nat → Γ ⊢ u ∷ Nat →
         Γ ⊢ p ∷ Hom Nat a t → Γ ⊢ q ∷ Hom Nat t u →
         Γ ⊢ ordtr a t u p q ∷ Hom Nat a u
⊢trans = ⊢ordtr

------------------------------------------------------------------------
-- ★★★ THE CROWN JEWEL'S TWO HALVES — STRONG INDUCTION WITHOUT `Acc`.
--
--     aux : (n : Nat) → (m : Nat) → m ≤ n → P m       -- by natrec on n
--
--   Recall the encoding: `k < m` IS `Hom Nat (nsuc k) m`, because
--   `nsuc k ≤ m` and `k < m` are the same statement.
------------------------------------------------------------------------

-- ★ THE BASE CASE (n = 0).  Needs only stage D, and already worked
--   before `ordtr`: `Hom Nat (nsuc k) nzero` COMPUTES to `base`, so the
--   impossible branch is discharged by ex falso.  There is no
--   "impossible" tactic and no absurd-pattern machinery — the empty
--   type is what the order REDUCES TO.
⊢strong-base : {Γ : Ctx} {C k p : RTm ⌊ Γ ⌋} →
               Γ ⊢ C ∷ U → Γ ⊢ p ∷ Hom Nat (nsuc k) nzero →
               Γ ⊢ absurd C p ∷ El C
⊢strong-base {k = k} dC dp =
  ⊢absurd dC (⊢conv dp (red→≅ᵀ (stepᵀ (Hom-Nat-sz k) doneᵀ)))

-- ★★ THE STEP CASE (n = suc n').  THIS is what `ordtr` was the gate
--    for: from `k < m` and `m ≤ suc n` conclude `k ≤ n`.
--
--    Compose to get `nsuc k ≤ nsuc n`, then let the ORDER COMPUTE:
--    `Hom Nat (nsuc k) (nsuc n) ⟶ᵀ Hom Nat k n` by `Hom-Nat-ss`.  The
--    successor-peel that would be a lemma anywhere else is a single
--    reduction step here, and the whole step case is five lines.
⊢strong-step : {Γ : Ctx} {k m n p q : RTm ⌊ Γ ⌋} →
               Γ ⊢ k ∷ Nat → Γ ⊢ m ∷ Nat → Γ ⊢ n ∷ Nat →
               Γ ⊢ p ∷ Hom Nat (nsuc k) m →       -- k < m
               Γ ⊢ q ∷ Hom Nat m (nsuc n) →       -- m ≤ suc n
               Γ ⊢ ordtr (nsuc k) m (nsuc n) p q ∷ Hom Nat k n   -- k ≤ n
⊢strong-step {k = k} {n = n} dk dm dn dp dq =
  ⊢conv (⊢ordtr (⊢nsuc dk) dm (⊢nsuc dn) dp dq)
        (red→≅ᵀ (stepᵀ (Hom-Nat-ss k n) doneᵀ))

-- ★ and the descent is REAL: `k < m` and `m ≤ suc n` really do give a
--   proof at the SMALLER bound `n`, so `natrec`'s structural recursion
--   on `n` carries the whole strong induction.  No fuel, no `Acc`, no
--   `TERMINATING` — the measure never appears because the ORDER is the
--   thing that reduces.
