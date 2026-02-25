------------------------------------------------------------------------
-- Once.CCC.Target.X86v3.SizeBoundLemma
--
-- IR size bound lemmas for proving sub-IRs are within program bound.
-- Extracted from Dispatcher.agda for faster compilation.
------------------------------------------------------------------------

module Once.CCC.Target.X86v3.SizeBoundLemma where

open import Data.Nat using (ℕ; _<_)
open import Data.Nat.Properties using (<-trans)

open import Once.CCC.Target.X86v3.IR

------------------------------------------------------------------------
-- Size bound lemmas
--
-- Pattern: if ir-size (compound-ir) < program-bound, then
-- ir-size (sub-ir) < program-bound (via <-trans with sub-ir-smaller)
--
-- Used in: compose, pair, curry cases
------------------------------------------------------------------------

-- Compose sub-IR bounds
∘-f-bound : ∀ {A B C} (f : IR A B) (g : IR B C) (program-bound : ℕ) →
  ir-size (g ∘ f) < program-bound →
  ir-size f < program-bound
∘-f-bound f g pb ir<bound = <-trans (∘-f-smaller f g) ir<bound

∘-g-bound : ∀ {A B C} (f : IR A B) (g : IR B C) (program-bound : ℕ) →
  ir-size (g ∘ f) < program-bound →
  ir-size g < program-bound
∘-g-bound f g pb ir<bound = <-trans (∘-g-smaller f g) ir<bound

-- Pair sub-IR bounds
⟨,⟩-f-bound : ∀ {A B C} (f : IR A B) (g : IR A C) {m : AllocMode} (program-bound : ℕ) →
  ir-size (⟨ f , g ⟩ m) < program-bound →
  ir-size f < program-bound
⟨,⟩-f-bound f g {m} pb ir<bound = <-trans (⟨,⟩-f-smaller f g {m}) ir<bound

⟨,⟩-g-bound : ∀ {A B C} (f : IR A B) (g : IR A C) {m : AllocMode} (program-bound : ℕ) →
  ir-size (⟨ f , g ⟩ m) < program-bound →
  ir-size g < program-bound
⟨,⟩-g-bound f g {m} pb ir<bound = <-trans (⟨,⟩-g-smaller f g {m}) ir<bound

-- Curry body bound
curry-body-bound : ∀ {A B C} (f : IR (A * B) C) {m : AllocMode} (program-bound : ℕ) →
  ir-size (curry f m) < program-bound →
  ir-size f < program-bound
curry-body-bound f {m} pb ir<bound = <-trans (curry-smaller f {m}) ir<bound

