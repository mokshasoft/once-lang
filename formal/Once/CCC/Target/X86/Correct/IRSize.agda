------------------------------------------------------------------------
-- Once.CCC.Target.X86.Correct.IRSize
--
-- Size measure for IR terms and size decrease lemmas.
-- Used for well-founded recursion to prove termination of IR execution.
--
-- Ported from Once.CCC.Termination for unsized IR (Once.IR).
------------------------------------------------------------------------

module Once.CCC.Target.X86.Correct.IRSize where

open import Once.Type hiding (_+_)
open import Once.IR

open import Data.Nat using (ℕ; zero; suc; _<_; _+_; _≤_; s≤s; z≤n)
open import Data.Nat.Properties using (m≤m+n; m≤n+m; ≤-refl)
open import Data.String using (String)

------------------------------------------------------------------------
-- Size measure for IR terms
--
-- Assigns a natural number representing the structural depth of an IR term.
-- Composite terms have size strictly greater than their components.
------------------------------------------------------------------------

ir-size : ∀ {A B} → IR A B → ℕ
ir-size id = 1
ir-size terminal = 1
ir-size initial = 1
ir-size (g ∘ f) = suc (ir-size f + ir-size g)
ir-size ⟨ f , g ⟩ = suc (ir-size f + ir-size g)
ir-size ([ f , g ]) = suc (ir-size f + ir-size g)
ir-size (curry f) = suc (ir-size f)
ir-size apply = 1
ir-size fst = 1
ir-size snd = 1
ir-size inl = 1
ir-size inr = 1
ir-size fold = 1
ir-size unfold = 1
ir-size arr = 1
ir-size (Prim _) = 1

------------------------------------------------------------------------
-- Size decrease lemmas
--
-- Prove that for each recursive IR constructor, the recursive calls
-- are on strictly smaller terms (measured by ir-size).
------------------------------------------------------------------------

-- Compose: Both f and g are smaller than (g ∘ f)
∘-f-smaller : ∀ {A B C} (f : IR A B) (g : IR B C) →
  ir-size f < ir-size (g ∘ f)
∘-f-smaller f g = s≤s (m≤m+n (ir-size f) (ir-size g))

∘-g-smaller : ∀ {A B C} (f : IR A B) (g : IR B C) →
  ir-size g < ir-size (g ∘ f)
∘-g-smaller f g = s≤s (m≤n+m (ir-size g) (ir-size f))

-- Pair: Both f and g are smaller than ⟨ f , g ⟩
⟨,⟩-f-smaller : ∀ {A B C} (f : IR C A) (g : IR C B) →
  ir-size f < ir-size ⟨ f , g ⟩
⟨,⟩-f-smaller f g = s≤s (m≤m+n (ir-size f) (ir-size g))

⟨,⟩-g-smaller : ∀ {A B C} (f : IR C A) (g : IR C B) →
  ir-size g < ir-size ⟨ f , g ⟩
⟨,⟩-g-smaller f g = s≤s (m≤n+m (ir-size g) (ir-size f))

-- Case: Both f and g are smaller than [ f , g ]
[,]-f-smaller : ∀ {A B C} (f : IR A C) (g : IR B C) →
  ir-size f < ir-size [ f , g ]
[,]-f-smaller f g = s≤s (m≤m+n (ir-size f) (ir-size g))

[,]-g-smaller : ∀ {A B C} (f : IR A C) (g : IR B C) →
  ir-size g < ir-size [ f , g ]
[,]-g-smaller f g = s≤s (m≤n+m (ir-size g) (ir-size f))

-- Curry: f is smaller than (curry f)
curry-smaller : ∀ {A B C} (f : IR (A * B) C) →
  ir-size f < ir-size (curry f)
curry-smaller f = s≤s ≤-refl
