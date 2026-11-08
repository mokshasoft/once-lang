-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Arith.Backend.XInstr.SpillBound  (plan 0.123 α′ (f2))
--
-- EVERY SPILL FITS THE FRAME. A block's code spills only to scratch slots
-- below `required-scratch` of the tree it was compiled from — the size its
-- prologue reserves (`block-payload`) and the room check charges (D393). So
-- the block writes memory only inside its own frame.
--
-- `compile-go d e` spills at depth `d` and compiles its right operand one
-- deeper, so its slots lie below `d + required-scratch e`; the bound carries
-- through `emit` because a spill is the only instruction that names a slot
-- it writes. The skeleton is `ArithSimCore`'s `LoadsWF`, for slots.
------------------------------------------------------------------------

module Once.Arith.Backend.XInstr.SpillBound where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Properties using (++-assoc)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; suc; _+_; _≤_; _<_; _⊔_; s≤s; z≤n)
open import Data.Nat.Properties using (≤-trans; <-≤-trans; +-monoʳ-≤; m≤m⊔n; m≤n⊔m; +-suc; ≤-refl; m<m+n)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

open import Once.Arith.Backend.XInstr.Syntax as XI using (XInstr; XScratch; mk-scratch)
open import Once.Arith.Backend.XInstr.CodeGen using (emit; emit-program)
open import Once.Arith.Machine.AbsInstr using (AbstractInstr; spill)
open import Once.Arith.Machine.Compile
  using (compile-abs; compile-go; required-scratch; mul-op; div-op; rem-op; mul-choose; div-choose; div-instr; rem-instr; pow2?; safe-divisor?)
open import Once.Arith.Machine.IR
  using (MArithIR; alit; aflit; ainput; aadd; asub; amul; adiv; amod; aneg; ai2f; acmp)
open import Once.Arith.Type using (NInt; NFloat)

-- a spill's slot is below `k`; nothing else is constrained
SpillOK : ℕ → XInstr → Set
SpillOK k (XI.Xmov-r-m sc _) = XScratch.slot sc < k
{-# CATCHALL #-}
SpillOK k _                  = ⊤

SpillsWF : ℕ → List XInstr → Set
SpillsWF k []       = ⊤
SpillsWF k (i ∷ is) = SpillOK k i × SpillsWF k is

private
  emit-program-++ : ∀ (xs ys : List AbstractInstr) → emit-program (xs ++ ys) ≡ emit-program xs ++ emit-program ys
  emit-program-++ []       ys = refl
  emit-program-++ (i ∷ is) ys =
    trans (cong (emit i ++_) (emit-program-++ is ys)) (sym (++-assoc (emit i) (emit-program is) (emit-program ys)))

  sw-++ : ∀ {k} (xs ys : List XInstr) → SpillsWF k xs → SpillsWF k ys → SpillsWF k (xs ++ ys)
  sw-++ []       ys _        wy = wy
  sw-++ (x ∷ xs) ys (ox , w) wy = ox , sw-++ xs ys w wy

  sw-cat : ∀ {k} (xs ys : List AbstractInstr)
         → SpillsWF k (emit-program xs) → SpillsWF k (emit-program ys) → SpillsWF k (emit-program (xs ++ ys))
  sw-cat {k} xs ys wx wy = subst (SpillsWF k) (sym (emit-program-++ xs ys)) (sw-++ (emit-program xs) (emit-program ys) wx wy)

  sw-mul-choose : ∀ {k} (mj : Maybe ℕ) → SpillsWF k (emit (mul-choose mj))
  sw-mul-choose (just j) = _
  sw-mul-choose nothing  = _

  sw-div-instr : ∀ {k} (t : Bool) → SpillsWF k (emit (div-instr t))
  sw-div-instr true  = _
  sw-div-instr false = _

  sw-rem-instr : ∀ {k} (t : Bool) → SpillsWF k (emit (rem-instr t))
  sw-rem-instr true  = _
  sw-rem-instr false = _

  sw-div-choose : ∀ {k} (mj : Maybe ℕ) (t : Bool) → SpillsWF k (emit (div-choose mj t))
  sw-div-choose (just j) t = _
  sw-div-choose nothing  t = sw-div-instr t

  -- a binary node: the left operand at `d`, the spill AT `d`, the right one deeper
  sw-bin : ∀ {k sh n m} (d : ℕ) (a : MArithIR sh n) (b : MArithIR sh m) (tl : List AbstractInstr)
         → SpillsWF k (emit-program (compile-go d a))
         → d < k
         → SpillsWF k (emit-program (compile-go (suc d) b))
         → SpillsWF k (emit-program tl)
         → SpillsWF k (emit-program (compile-go d a ++ (spill 0 d ∷ []) ++ compile-go (suc d) b ++ tl))
  sw-bin d a b tl wa dk wb wtl =
    sw-cat (compile-go d a) ((spill 0 d ∷ []) ++ compile-go (suc d) b ++ tl) wa
      (sw-cat (spill 0 d ∷ []) (compile-go (suc d) b ++ tl) (dk , tt)
        (sw-cat (compile-go (suc d) b) tl wb wtl))

  -- the bounds a binary node hands its parts
  l≤ : ∀ d x y → d + x ≤ d + (x ⊔ suc y)
  l≤ d x y = +-monoʳ-≤ d (m≤m⊔n x (suc y))
  r≤ : ∀ d x y → suc d + y ≤ d + (x ⊔ suc y)
  r≤ d x y = subst (_≤ d + (x ⊔ suc y)) (+-suc d y) (+-monoʳ-≤ d (m≤n⊔m x (suc y)))
  d< : ∀ d x y → d < d + (x ⊔ suc y)
  d< d x y = <-≤-trans (m<m+n d (s≤s z≤n)) (+-monoʳ-≤ d (m≤n⊔m x (suc y)))

spills-below : ∀ {sh n} (d k : ℕ) (e : MArithIR sh n) → d + required-scratch e ≤ k
             → SpillsWF k (emit-program (compile-go d e))
spills-below d k (alit z)   _ = _
spills-below d k (aflit dc) _ = _
spills-below {n = NInt}   d k (ainput p) _ = _
spills-below {n = NFloat} d k (ainput p) _ = _
spills-below {n = NInt} d k (aadd a b) le =
  sw-bin d a b _ (spills-below d k a (≤-trans (l≤ d _ _) le)) (≤-trans (d< d _ _) le) (spills-below (suc d) k b (≤-trans (r≤ d _ _) le)) _
spills-below {n = NFloat} d k (aadd a b) le =
  sw-bin d a b _ (spills-below d k a (≤-trans (l≤ d _ _) le)) (≤-trans (d< d _ _) le) (spills-below (suc d) k b (≤-trans (r≤ d _ _) le)) _
spills-below {n = NInt} d k (asub a b) le =
  sw-bin d a b _ (spills-below d k a (≤-trans (l≤ d _ _) le)) (≤-trans (d< d _ _) le) (spills-below (suc d) k b (≤-trans (r≤ d _ _) le)) _
spills-below {n = NFloat} d k (asub a b) le =
  sw-bin d a b _ (spills-below d k a (≤-trans (l≤ d _ _) le)) (≤-trans (d< d _ _) le) (spills-below (suc d) k b (≤-trans (r≤ d _ _) le)) _
spills-below {n = NInt} d k (amul a b) le =
  sw-bin d a b _ (spills-below d k a (≤-trans (l≤ d _ _) le)) (≤-trans (d< d _ _) le) (spills-below (suc d) k b (≤-trans (r≤ d _ _) le))
    (_ , sw-++ (emit (mul-op b)) [] (sw-mul-choose (pow2? b)) _)
spills-below {n = NFloat} d k (amul a b) le =
  sw-bin d a b _ (spills-below d k a (≤-trans (l≤ d _ _) le)) (≤-trans (d< d _ _) le) (spills-below (suc d) k b (≤-trans (r≤ d _ _) le)) _
spills-below {n = NInt} d k (adiv a b) le =
  sw-bin d a b _ (spills-below d k a (≤-trans (l≤ d _ _) le)) (≤-trans (d< d _ _) le) (spills-below (suc d) k b (≤-trans (r≤ d _ _) le))
    (_ , sw-++ (emit (div-op b)) [] (sw-div-choose (pow2? b) (safe-divisor? b)) _)
spills-below {n = NFloat} d k (adiv a b) le =
  sw-bin d a b _ (spills-below d k a (≤-trans (l≤ d _ _) le)) (≤-trans (d< d _ _) le) (spills-below (suc d) k b (≤-trans (r≤ d _ _) le)) _
spills-below d k (amod a b) le =
  sw-bin d a b _ (spills-below d k a (≤-trans (l≤ d _ _) le)) (≤-trans (d< d _ _) le) (spills-below (suc d) k b (≤-trans (r≤ d _ _) le))
    (_ , sw-++ (emit (rem-op b)) [] (sw-rem-instr (safe-divisor? b)) _)
spills-below d k (acmp o a b) le =
  sw-bin d a b _ (spills-below d k a (≤-trans (l≤ d _ _) le)) (≤-trans (d< d _ _) le) (spills-below (suc d) k b (≤-trans (r≤ d _ _) le)) _
spills-below {n = NInt}   d k (aneg a) le = sw-cat (compile-go d a) _ (spills-below d k a le) _
spills-below {n = NFloat} d k (aneg a) le = sw-cat (compile-go d a) _ (spills-below d k a le) _
spills-below d k (ai2f a) le = sw-cat (compile-go d a) _ (spills-below d k a le) _

-- THE BLOCK'S CODE fits the frame its own tree asks for
block-spills : ∀ {sh n} (e : MArithIR sh n) → SpillsWF (required-scratch e) (emit-program (compile-abs e))
block-spills e = sw-cat (compile-go 0 e) _ (spills-below 0 (required-scratch e) e ≤-refl) _
