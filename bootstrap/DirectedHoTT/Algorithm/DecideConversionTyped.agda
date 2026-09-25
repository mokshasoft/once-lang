------------------------------------------------------------------------
-- OCP-0009 · dHoTT — ★ CONVERSION OF WELL-TYPED TERMS IS DECIDABLE.
--                      No parameters left.
--
-- `dec-conv-typed` (Metatheory/Fundamental) decided `_≅_` for well-typed
-- terms given ONE input — decidable syntactic equality of raw terms.
-- `Algorithm/DecEq` supplies it, so this module is the closed theorem.
--
-- ⚠ SCOPE: TERM conversion `_≅_`.  TYPE conversion `_≅ᵀ_`, which `⊢conv`
--   uses and a type checker must decide, is NOT covered — types have only
--   weak-head forms (`fund-ty`).  That is the next piece of the checker.
--
-- `--safe`, ZERO axioms.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Algorithm.DecideConversionTyped where
open import normalizer.Syntax.Types using ( _≡_; refl )
open import Agda.Builtin.Bool using ( Bool; true; false )
open import DirectedHoTT.Spec.Syntax
open import DirectedHoTT.Spec.Typing
  using ( Ctx; ◇; _▹_; ⌊_⌋; _⊢_∷_; _≅_; ⊢ctx_; c-◇; c-▹
        ; ⊢var; ⊢lam; ⊢app; here; there; ty-base; ⊢appex )
open import DirectedHoTT.Algorithm.DecEq using ( Dec; yes; no; _≟Tm_ )
open import DirectedHoTT.Metatheory.Fundamental using ( dec-conv-typed )

private
  variable
    Γ : Ctx

decide-≅ : {t u : RTm ⌊ Γ ⌋} {A B : RTy ⌊ Γ ⌋} →
           ⊢ctx Γ → Γ ⊢ t ∷ A → Γ ⊢ u ∷ B → Dec (t ≅ u)
decide-≅ = dec-conv-typed _≟Tm_

------------------------------------------------------------------------
-- NON-VACUITY — it RUNS, and answers both ways.
------------------------------------------------------------------------

private
  isYes : {P : Set} → Dec P → Bool
  isYes (yes _) = true
  isYes (no  _) = false

  Γ₁ : Ctx
  Γ₁ = ◇ ▹ base

  Γ₂ : Ctx
  Γ₂ = (◇ ▹ base) ▹ base

  wΓ₁ : ⊢ctx Γ₁
  wΓ₁ = c-▹ c-◇ ty-base

  wΓ₂ : ⊢ctx Γ₂
  wΓ₂ = c-▹ wΓ₁ ty-base

  -- (λx.x) y ≅ y — a β-redex against its reduct: YES.
  redex-yes : isYes (decide-≅ wΓ₁ ⊢appex (⊢var here)) ≡ true
  redex-yes = refl

  -- x ≅ y for two distinct variables: NO.
  vars-no : isYes (decide-≅ wΓ₂ (⊢var here) (⊢var (there here))) ≡ false
  vars-no = refl
