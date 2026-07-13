------------------------------------------------------------------------
-- OCP-0009 · Consistency ladder, rung 1 — the graded QTT calculus
--
-- Consistency of the intrinsically-typed graded calculus `Γ ⊢[ ρ ] A`
-- (`NbEPQTTJ`): THERE IS NO CLOSED DERIVATION OF THE BASE TYPE,
--
--   ∀ ρ → ¬ (∅ ⊢[ ρ ] ι)
--
-- i.e. the free calculus proves nothing about an abstract base type. This is
-- the right consistency statement for a calculus whose `Tyq` has no empty
-- type: interpret `ι` as `Void` and a closed derivation becomes a closed IR
-- point of the initial object — refuted by rung 0's model.
--
-- Method (the ladder pattern, one level up): a SECOND elaboration `⟪_⟫`
-- mirroring `NbEPQTTJ.⟦_⟧` but sending `ι ↦ Void` instead of `ι ↦ Bool`
-- (the elaboration target is a parameter of the consistency argument, not of
-- the calculus), composed with the `--safe` Set-model `eval`. The whole
-- module is `--safe`; nothing in `NbEPQTTJ` is touched.
--
-- Gödel placement: still BELOW the threshold — the graded calculus is simply
-- typed (no propositions, no arithmetic-with-induction), so its consistency
-- is absolutely provable in the meta. The grading (`Mult` usage accounting)
-- adds a resource discipline, not logical strength.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPCon1 where

open import normalizer.Syntax.Types
  using ( Ty; Unit; Void; _*_; _⇒_; ⊥; ¬_; tt )
open import normalizer.Syntax.CCC
  using ( Term; _∘_; fst; snd; ⟨_,_⟩; curry; apply )
open import normalizer.Testing.Evaluator
  using ( ⟦_⟧T; eval )
open import poc.OCP0009.NbEPQTTJ
  using ( Tyq; ι; _×q_; _⇒[_]_
        ; Con; ∅; _,_; Use; _∋_; vz; vs
        ; _⊢[_]_; var; lam; app; pair )

------------------------------------------------------------------------
-- The refuting elaboration: `ι ↦ Void`. (Same point-free reading as
-- `NbEPQTTJ.⟦_⟧`; only the base-type target differs.)
------------------------------------------------------------------------

⟪_⟫ᵗ : Tyq → Ty
⟪ ι ⟫ᵗ          = Void
⟪ A ×q B ⟫ᵗ     = ⟪ A ⟫ᵗ * ⟪ B ⟫ᵗ
⟪ A ⇒[ _ ] B ⟫ᵗ = ⟪ A ⟫ᵗ ⇒ ⟪ B ⟫ᵗ

⟪_⟫ᶜ : Con → Ty
⟪ ∅ ⟫ᶜ     = Unit
⟪ Γ , A ⟫ᶜ = ⟪ Γ ⟫ᶜ * ⟪ A ⟫ᵗ

⟪var_⟫ : ∀ {Γ A} → Γ ∋ A → Term ⟪ Γ ⟫ᶜ ⟪ A ⟫ᵗ
⟪var vz ⟫   = snd
⟪var vs x ⟫ = ⟪var x ⟫ ∘ fst

⟪_⟫ : ∀ {Γ ρ A} → Γ ⊢[ ρ ] A → Term ⟪ Γ ⟫ᶜ ⟪ A ⟫ᵗ
⟪ var x ⟫    = ⟪var x ⟫
⟪ lam t ⟫    = curry ⟪ t ⟫
⟪ app f a ⟫  = apply ∘ ⟨ ⟪ f ⟫ , ⟪ a ⟫ ⟩
⟪ pair a b ⟫ = ⟨ ⟪ a ⟫ , ⟪ b ⟫ ⟩

------------------------------------------------------------------------
-- Consistency: no closed derivation of the base type, at ANY usage vector.
------------------------------------------------------------------------

qtt-consistent : ∀ {ρ : Use ∅} → ¬ (∅ ⊢[ ρ ] ι)
qtt-consistent t = eval ⟪ t ⟫ tt
