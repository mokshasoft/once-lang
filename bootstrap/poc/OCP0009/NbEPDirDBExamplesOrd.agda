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
  using ( Cx; ε; _∙; RTy; base; Hom; Unit; Nat
        ; RTm; unit; nzero; nsuc )
open import poc.OCP0009.NbEPDirDBType
  using ( _⟶ᵀ_; _⟶ᵀ*_; doneᵀ; stepᵀ
        ; Hom-Nat-z; Hom-Nat-sz; Hom-Nat-ss
        ; _≅ᵀ_; credᵀ; csymᵀ; ctrnᵀ
        ; Ctx; ◇; ⌊_⌋
        ; _⊢_∷_; ⊢unit; ⊢conv )
open import poc.OCP0009.NbEPDirDBInj using ( red→≅ᵀ )
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
