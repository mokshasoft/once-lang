------------------------------------------------------------------------
-- OCP-0009 · OTT step 3 — observational equality for INDUCTIVE types (μ)
--
-- `NbEPOTT` gave observational equality on the `{Void,Unit,×,+,⇒}` fragment,
-- with `μ` a placeholder. This module extends it to `μ` using the `Fix` value
-- model (`normalizer.Testing.Evaluator`, where `⟦ μ F ⟧T = Fix F`):
--
--   eq (μ F) (fix x) (fix y) = eqF F F x y
--
-- where `eqF` is observational equality on a functor unfolding `⟦ G ⟧FS (Fix F)`
-- — reflexive, and at an `Id`/`Kc` position it recurses back into `eq` on the
-- sub-`Fix`. So equality of inductive data is decided by its OBSERVATIONS
-- (constructor + fields, recursively), exactly the OTT discipline, now total
-- over the whole type language.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPOTTMu where

open import normalizer.Syntax.Types
open import normalizer.Testing.Evaluator using ( ⟦_⟧T; ⟦_⟧FS; Fix; fix )

------------------------------------------------------------------------
-- Observational equality, now with the `μ` case (mutual with the functor
-- version `eqF`). Recursion descends into sub-`Fix`es — structural.
------------------------------------------------------------------------

mutual
  eq : (A : Ty) → ⟦ A ⟧T → ⟦ A ⟧T → Set
  eq Void ()
  eq Unit _ _ = ⊤
  eq (A * B) (a , b) (a' , b') = eq A a a' × eq B b b'
  eq (A + B) (inj₁ a) (inj₁ a') = eq A a a'
  eq (A + B) (inj₁ _) (inj₂ _)  = ⊥
  eq (A + B) (inj₂ _) (inj₁ _)  = ⊥
  eq (A + B) (inj₂ b) (inj₂ b') = eq B b b'
  eq (A ⇒ B) f g = ∀ x → eq B (f x) (g x)
  eq (μ F) (fix x) (fix y) = eqF F F x y

  eqF : (F G : Func) → ⟦ G ⟧FS (Fix F) → ⟦ G ⟧FS (Fix F) → Set
  eqF F Id     x         y         = eq (μ F) x y        -- sub-Fix: recurse
  eqF F One    _         _         = ⊤
  eqF F (Kc H) x         y         = eq (μ H) x y        -- nested code = Fix H
  eqF F (G ⊕ H) (inj₁ x) (inj₁ y)  = eqF F G x y
  eqF F (G ⊕ H) (inj₁ _) (inj₂ _)  = ⊥
  eqF F (G ⊕ H) (inj₂ _) (inj₁ _)  = ⊥
  eqF F (G ⊕ H) (inj₂ x) (inj₂ y)  = eqF F H x y
  eqF F (G ⊗ H) (x₁ , x₂) (y₁ , y₂) = eqF F G x₁ y₁ × eqF F H x₂ y₂

------------------------------------------------------------------------
-- Reflexivity — observational equality holds on every inductive value.
------------------------------------------------------------------------

mutual
  eq-refl : (A : Ty) (a : ⟦ A ⟧T) → eq A a a
  eq-refl Void ()
  eq-refl Unit _ = tt
  eq-refl (A * B) (a , b) = eq-refl A a , eq-refl B b
  eq-refl (A + B) (inj₁ a) = eq-refl A a
  eq-refl (A + B) (inj₂ b) = eq-refl B b
  eq-refl (A ⇒ B) f = λ x → eq-refl B (f x)
  eq-refl (μ F) (fix x) = eqF-refl F F x

  eqF-refl : (F G : Func) (x : ⟦ G ⟧FS (Fix F)) → eqF F G x x
  eqF-refl F Id     x         = eq-refl (μ F) x
  eqF-refl F One    _         = tt
  eqF-refl F (Kc H) x         = eq-refl (μ H) x
  eqF-refl F (G ⊕ H) (inj₁ x) = eqF-refl F G x
  eqF-refl F (G ⊕ H) (inj₂ y) = eqF-refl F H y
  eqF-refl F (G ⊗ H) (x₁ , x₂) = eqF-refl F G x₁ , eqF-refl F H x₂

------------------------------------------------------------------------
-- Example — the natural numbers, observationally.
------------------------------------------------------------------------

NatF : Func
NatF = One ⊕ Id

Nat : Ty
Nat = μ NatF

zeroᵥ : ⟦ Nat ⟧T
zeroᵥ = fix (inj₁ tt)

sucᵥ : ⟦ Nat ⟧T → ⟦ Nat ⟧T
sucᵥ n = fix (inj₂ n)

twoᵥ : ⟦ Nat ⟧T
twoᵥ = sucᵥ (sucᵥ zeroᵥ)

-- `2` is observationally equal to itself — decided by descending the structure.
_ : eq Nat twoᵥ twoᵥ
_ = eq-refl Nat twoᵥ

-- `eq Nat (suc _) zero` computes to `⊥` (constructor mismatch) — observational
-- equality distinguishes distinct constructors.
distinct : eq Nat (sucᵥ zeroᵥ) zeroᵥ → ⊥
distinct p = p
