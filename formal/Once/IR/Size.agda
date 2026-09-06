-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.IR.Size
--
-- Size measure for IR and termination lemmas.
--
-- Used by the Dispatcher to prove recursive calls decrease in size.
------------------------------------------------------------------------

module Once.IR.Size where

open import Data.Nat using (ℕ; zero; suc; _<_; _≤_; s≤s; z≤n) renaming (_+_ to _+ℕ_)
open import Data.Nat.Properties using (m<m+n; m<n+m; n<1+n; m≤m+n; m≤n+m; m≤n⇒m≤1+n)

open import Once.IR

------------------------------------------------------------------------
-- Size Measure for Termination
------------------------------------------------------------------------

ir-size : ∀ {A B} → IR A B → ℕ
-- D062: size of the natural transform a Fuse/Hylo carries.
ir-size-nt : ∀ {G F} → NatTr G F → ℕ
ir-size id = 1
ir-size (g ∘ f) = 1 +ℕ ir-size g +ℕ ir-size f
ir-size ⟨ f , g ⟩ = 1 +ℕ ir-size f +ℕ ir-size g
ir-size fst = 1
ir-size snd = 1
ir-size (inl _) = 1
ir-size (inr _) = 1
ir-size (case f g) = 1 +ℕ ir-size f +ℕ ir-size g
ir-size terminal = 1
ir-size initial = 1
ir-size (curry f _) = 2 +ℕ ir-size f
ir-size apply = 1
-- OCP-0003: fold/unfold removed. Use In/Cata/Out/Ana instead.
-- Recursion schemes (OCP-0003) - WellFormedF proofs are ignored for size
ir-size (In _ _) = 1
ir-size (out-μ _) = 1             -- Lambek isomorphism inverse
ir-size (Cata _ alg) = 2 +ℕ ir-size alg  -- Similar to curry: contains body
ir-size (Para _ alg) = 2 +ℕ ir-size alg  -- Paramorphism body
ir-size (Out _) = 1
ir-size (in-ν _ _) = 1            -- Lambek isomorphism inverse
ir-size (Ana _ coalg) = 2 +ℕ ir-size coalg  -- Contains coalgebra body
ir-size (Hylo _ _ alg t) = 2 +ℕ ir-size alg +ℕ ir-size-nt t
-- Fuse: μ-anchored fusion (correct by construction)
ir-size (Fuse _ _ alg t) = 2 +ℕ ir-size alg +ℕ ir-size-nt t
-- Guard/Unguard removed: productivity follows from IR totality
-- Other
ir-size (free-heap _) = 1
ir-size (SigOp _) = 1
ir-size (const _ _) = 1

ir-size-nt ntId         = 1
ir-size-nt (ntK ir)     = 1 +ℕ ir-size ir
ir-size-nt (ntFst t)    = 1 +ℕ ir-size-nt t
ir-size-nt (ntSnd t)    = 1 +ℕ ir-size-nt t
ir-size-nt (ntCase t u) = 1 +ℕ ir-size-nt t +ℕ ir-size-nt u
ir-size-nt (ntInl t)    = 1 +ℕ ir-size-nt t
ir-size-nt (ntInr t)    = 1 +ℕ ir-size-nt t
ir-size-nt (ntPair t u) = 1 +ℕ ir-size-nt t +ℕ ir-size-nt u

------------------------------------------------------------------------
-- Size Bound Lemmas
------------------------------------------------------------------------

∘-f-smaller : ∀ {A B C} (f : IR A B) (g : IR B C) → ir-size f < ir-size (g ∘ f)
∘-f-smaller f g = m<n+m (ir-size f) {suc (ir-size g)} (s≤s z≤n)

∘-g-smaller : ∀ {A B C} (f : IR A B) (g : IR B C) → ir-size g < ir-size (g ∘ f)
∘-g-smaller f g = s≤s (m≤m+n (ir-size g) (ir-size f))

⟨,⟩-f-smaller : ∀ {A B C} (f : IR A B) (g : IR A C) → ir-size f < ir-size ⟨ f , g ⟩
⟨,⟩-f-smaller f g = s≤s (m≤m+n (ir-size f) (ir-size g))

⟨,⟩-g-smaller : ∀ {A B C} (f : IR A B) (g : IR A C) → ir-size g < ir-size ⟨ f , g ⟩
⟨,⟩-g-smaller f g = s≤s (m≤n+m (ir-size g) (ir-size f))

curry-smaller : ∀ {A B C} (f : IR (A * B) C) {m : AllocMode} → ir-size f < ir-size (curry f m)
curry-smaller f {m} = m≤n⇒m≤1+n (n<1+n (ir-size f))

case-f-smaller : ∀ {A B C} (f : IR A C) (g : IR B C) → ir-size f < ir-size (case f g)
case-f-smaller f g = s≤s (m≤m+n (ir-size f) (ir-size g))

case-g-smaller : ∀ {A B C} (f : IR A C) (g : IR B C) → ir-size g < ir-size (case f g)
case-g-smaller f g = s≤s (m≤n+m (ir-size g) (ir-size f))