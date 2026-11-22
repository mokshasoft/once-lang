-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.AllocExpandClasses — the allocators, as choices of size
-- classes for a program (D468 amended, plan 0.146 B1.6 items 3c4/3c5).
--
-- A program's SIZES are its allocations' and frees' block sizes. The POOL is one
-- free list whose blocks are the largest size (`--alloc=pool`): every block of
-- the program is allocated at it, so any block serves any request. What the
-- expansion's simulation asks of a choice (`AllocExpandEvents`): a block at
-- least its request (`fits`), one size per class over the program's sizes
-- (`uniform`), every class's head inside the record (`small`, `in-range`).
------------------------------------------------------------------------

open import Once.CCC.FrameSemantics using (FrameSemantics)

module Once.CCC.Codegen.AllocExpandClasses where

open import Data.List using (List; []; _∷_; _++_; foldr)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ; ∈-++⁺ʳ)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _+_; _<_; _≤_; _⊔_; z≤n; s≤s)
open import Data.Nat.Properties using (m≤m⊔n; m≤n⊔m; ≤-trans; m≤n⇒m⊔n≡n)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Once.CCC.Machine.SMCore
open import Once.CCC.Machine.Flat using (module FlatMachine)
open import Once.CCC.Codegen.AllocExpand
open Classes

------------------------------------------------------------------------
-- A program's sizes
------------------------------------------------------------------------

size-of : AbstractInstr → List ℕ
size-of (instr-alloc-heap k) = k ∷ []
size-of (instr-free-heap k)  = k ∷ []
{-# CATCHALL #-}
size-of _                    = []

sizes : AbstractTrace → List ℕ
sizes []      = []
sizes (i ∷ t) = size-of i ++ sizes t

Sz : AbstractTrace → ℕ → Set
Sz P k = k ∈ sizes P

module Fetch {FS : FrameSemantics} where
  open FlatMachine {FS} using (fetch)

  sz-at : ∀ P n i k → fetch P n ≡ just i → size-of i ≡ k ∷ [] → Sz P k
  sz-at []      n       i k ()
  sz-at (x ∷ P) zero    i k refl e = ∈-++⁺ˡ (subst (k ∈_) (sym e) (here refl))
  sz-at (x ∷ P) (suc n) i k f e = ∈-++⁺ʳ (size-of x) (sz-at P n i k f e)

  sz-alloc : ∀ P n k → fetch P n ≡ just (instr-alloc-heap k) → Sz P k
  sz-alloc P n k f = sz-at P n _ k f refl

  sz-free : ∀ P n k → fetch P n ≡ just (instr-free-heap k) → Sz P k
  sz-free P n k f = sz-at P n _ k f refl

------------------------------------------------------------------------
-- ★ The pool: one list, every block the largest size
------------------------------------------------------------------------

largest : List ℕ → ℕ
largest = foldr _⊔_ 0

≤-largest : ∀ {k} xs → k ∈ xs → k ≤ largest xs
≤-largest (x ∷ xs) (here refl) = m≤m⊔n x (largest xs)
≤-largest (x ∷ xs) (there m)   = ≤-trans (≤-largest xs m) (m≤n⊔m x (largest xs))

pool : AbstractTrace → Classes
pool P = record { count = 1 ; cls = λ _ → 0 ; bsz = λ k → k ⊔ largest (sizes P) }

module Pool (P : AbstractTrace) where
  C = pool P

  small : 3 + count C ≤ rec-size
  small = s≤s (s≤s (s≤s (s≤s z≤n)))

  in-range : ∀ k → cls C k < count C
  in-range _ = s≤s z≤n

  fits : ∀ k → k ≤ bsz C k
  fits k = m≤m⊔n k _

  uniform : ∀ k k′ → Sz P k → Sz P k′ → cls C k ≡ cls C k′ → bsz C k ≡ bsz C k′
  uniform k k′ s s′ _ = trans (m≤n⇒m⊔n≡n (≤-largest _ s)) (sym (m≤n⇒m⊔n≡n (≤-largest _ s′)))
