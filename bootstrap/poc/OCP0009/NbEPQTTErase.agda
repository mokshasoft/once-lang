------------------------------------------------------------------------
-- OCP-0009 · QTT erasure SOUNDNESS (the `nf`-tied theorem)
--
-- Split out of `NbEPQTT` because it references `nf` (the NbE normalizer),
-- keeping the QTT semiring + graded-context algebra (`NbEPQTT`) and the graded
-- typing judgment (`NbEPQTTJ`) free of any dependency on the evaluator. (All
-- three are `--safe`; `NbEP` itself is too, now that its `TERMINATING` pragma
-- proved unnecessary.)
--
-- The result: an erased (`𝟘`) index cannot influence the runtime result. For the
-- single erased slot `Γ = R ▷[𝟘] I` (where `erase Γ = fst`), a runtime
-- computation `g : Tm R B` fed the SAME kept input `r` but DIFFERENT erased
-- indices `i₁ ≠ i₂` produces the SAME normal form — `nf` never observes the
-- index (`erase` drops it by `β-fst`; evaluation factors through the runtime
-- environment). The general multi-slot statement is the same idea.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPQTTErase where

open import normalizer.Syntax.Types using ( _≡_; refl; Unit )
open import poc.OCP0009.NbEPTm using ( Tm; idT; _⊙_; fstT; sndT; pair )
open import poc.OCP0009.NbEP  using ( nf )
open import poc.OCP0009.NbEPQTT using ( Nat; Bool )

erase-irrelevant :
  ∀ {R I B} (g : Tm R B) (r : Tm Unit R) (i₁ i₂ : Tm Unit I)
  → nf ((g ⊙ fstT) ⊙ pair r i₁) ≡ nf ((g ⊙ fstT) ⊙ pair r i₂)
erase-irrelevant g r i₁ i₂ = refl

-- Concrete witness: over `Γ-ex`, the runtime read `snd` (the Bool) is the same
-- whether the erased `Nat` index is `zero`-coded or `suc`-coded.
_ : ∀ {B} (g : Tm Bool B) (b : Tm Unit Bool) (i₁ i₂ : Tm Unit Nat)
  → nf ((g ⊙ sndT) ⊙ pair (pair idT i₁) b) ≡ nf ((g ⊙ sndT) ⊙ pair (pair idT i₂) b)
_ = λ g b i₁ i₂ → refl
