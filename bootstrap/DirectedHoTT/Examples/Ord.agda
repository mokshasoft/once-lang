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
module DirectedHoTT.Examples.Ord where
open import normalizer.Syntax.Types using ( _≡_; refl; ⊥ )
open import DirectedHoTT.Spec.Syntax
  using ( Cx; ε; _∙; RTy; base; U; El; Hom; Unit; Nat
        ; RTm; unit; nzero; nsuc; absurd; ordtr )
open import DirectedHoTT.Spec.Typing
  using ( _⟶ᵀ_
        ; Hom-Nat-z; Hom-Nat-sz; Hom-Nat-ss
        ; _≅ᵀ_; credᵀ; csymᵀ; ctrnᵀ
        ; Ctx; ◇; ⌊_⌋
        ; _⟶_; _⟶*_; done; step
        ; ordtr-z; ordtr-sss
        ; _⊢_∷_; ⊢unit; ⊢conv; ⊢nsuc; ⊢nzero; ⊢absurd; ⊢ordtr )
open import DirectedHoTT.Metatheory.RedCong using ( red→≅ᵀ; _⟶ᵀ*_; doneᵀ; stepᵀ )
open import DirectedHoTT.Metatheory.Canonicity using ( consistency )

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

------------------------------------------------------------------------
-- ★ THE PRIMITIVES NOW LIVE IN `…LibOrd` — `⊢trans`, `⊢strong-base`,
--   `⊢strong-step`, `⊢strong-base'`, `⊢strong-descend`.  Seven `Lib*`
--   modules build on them, so a library was importing an example.
--
-- ⚠ NOT re-exported.  Clients import the primitives from the library
--   directly — a re-export would hide the real dependency and force every
--   client to inherit this module's whole closure.
------------------------------------------------------------------------

open import DirectedHoTT.Lib.Ord
  using ( ⊢trans; ⊢strong-base; ⊢strong-step; ⊢strong-base'; ⊢strong-descend )
