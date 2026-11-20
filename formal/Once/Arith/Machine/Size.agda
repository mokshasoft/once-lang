-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Arith.Machine.Size — the measure the arith recogniser's recursion
-- decreases (plan 0.153 D3). `sz` counts the LEFT factor of a composition
-- twice, so D163's re-association `(f ∘ g) ∘ h ↦ f ∘ (g ∘ h)` decreases it;
-- distribution `⟨ a , b ⟩ ∘ h ↦ a ∘ h , b ∘ h` and the subterm calls do too.
-- Moved from `Once.Adequacy.LiftSound`, whose soundness proof used it first.
------------------------------------------------------------------------

module Once.Arith.Machine.Size where

open import Data.Nat using (ℕ; suc; _+_; _<_; _≤_; s≤s)
open import Data.Nat.Properties using (m≤m+n; m≤n+m)
import Data.Nat.Properties
open import Relation.Binary.PropositionalEquality using (_≡_; sym)

open import Once.IR
open import Once.IRTy using (⌊_⌋)
open import Once.SigOp.Info using (SigOpInfo)

sz : ∀ {A B} → IR A B → ℕ
sz (f ∘ g)     = suc (sz f + sz f + sz g)
sz ⟨ f , g ⟩   = suc (sz f + sz g)
{-# CATCHALL #-}
sz _           = 1

reassoc-< : ∀ {A B C D} (f : IR C D) (g : IR B C) (h : IR A B) → sz (f ∘ (g ∘ h)) < sz ((f ∘ g) ∘ h)
reassoc-< f g h = s≤s (s≤s (bound (sz f) (sz g) (sz h)))
  where
    open import Data.Nat.Properties using (+-assoc)
    bound : ∀ F G H → F + F + suc (G + G + H) ≤ F + F + G + suc (F + F + G) + H
    bound F G H = Data.Nat.Properties.≤-trans
      (Data.Nat.Properties.≤-reflexive (lhs≡ F G H))
      (Data.Nat.Properties.≤-trans (step F G H) (Data.Nat.Properties.≤-reflexive (sym (rhs≡ F G H))))
      where
        open import Data.Nat.Tactic.RingSolver
        lhs≡ : ∀ F G H → F + F + suc (G + G + H) ≡ suc (F + F + G + G + H)
        lhs≡ = solve-∀
        rhs≡ : ∀ F G H → F + F + G + suc (F + F + G) + H ≡ suc (F + F + G + G + H + F + F)
        rhs≡ = solve-∀
        step : ∀ F G H → suc (F + F + G + G + H) ≤ suc (F + F + G + G + H + F + F)
        step F G H = s≤s (Data.Nat.Properties.≤-trans (m≤m+n (F + F + G + G + H) (F + F))
                                       (Data.Nat.Properties.≤-reflexive (sym (+-assoc (F + F + G + G + H) F F))))

sz-sigop : ∀ {X Y A} (si : SigOpInfo X Y) (e : IR A ⌊ X ⌋) → sz e < sz (SigOp si ∘ e)
sz-sigop si e = s≤s (Data.Nat.Properties.≤-trans (Data.Nat.Properties.n≤1+n _) (Data.Nat.Properties.n≤1+n _))

sz-pairˡ : ∀ {A B C} (a : IR A B) (b : IR A C) → sz a < sz ⟨ a , b ⟩
sz-pairˡ a b = s≤s (m≤m+n (sz a) (sz b))

sz-pairʳ : ∀ {A B C} (a : IR A B) (b : IR A C) → sz b < sz ⟨ a , b ⟩
sz-pairʳ a b = s≤s (m≤n+m (sz b) (sz a))

sz-distˡ : ∀ {A B C W} (a : IR A B) (b : IR A C) (h : IR W A) → sz (a ∘ h) < sz (⟨ a , b ⟩ ∘ h)
sz-distˡ a b h = s≤s (s≤s (go (sz a) (sz b) (sz h)))
  where
    open import Data.Nat.Tactic.RingSolver
    e : ∀ X Y H → X + X + H + suc (Y + Y) ≡ X + Y + suc (X + Y) + H
    e = solve-∀
    go : ∀ X Y H → X + X + H ≤ X + Y + suc (X + Y) + H
    go X Y H = Data.Nat.Properties.≤-trans (m≤m+n (X + X + H) (suc (Y + Y)))
                 (Data.Nat.Properties.≤-reflexive (e X Y H))

sz-distʳ : ∀ {A B C W} (a : IR A B) (b : IR A C) (h : IR W A) → sz (b ∘ h) < sz (⟨ a , b ⟩ ∘ h)
sz-distʳ a b h = s≤s (s≤s (go (sz a) (sz b) (sz h)))
  where
    open import Data.Nat.Tactic.RingSolver
    e : ∀ X Y H → Y + Y + H + suc (X + X) ≡ X + Y + suc (X + Y) + H
    e = solve-∀
    go : ∀ X Y H → Y + Y + H ≤ X + Y + suc (X + Y) + H
    go X Y H = Data.Nat.Properties.≤-trans (m≤m+n (Y + Y + H) (suc (X + X)))
                 (Data.Nat.Properties.≤-reflexive (e X Y H))
