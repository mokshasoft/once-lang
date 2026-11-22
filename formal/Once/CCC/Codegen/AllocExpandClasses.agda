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

------------------------------------------------------------------------
-- ★ The slab (D468's allocator): a list per size, each its exact size — when
-- the program's sizes fit the record (at most 60, a head each, and one more
-- list for a size the program never allocates); the pool otherwise
------------------------------------------------------------------------

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Nat using (_≡ᵇ_; _≤ᵇ_)
open import Data.List using (length; deduplicate)
import Data.Nat.Properties
import Data.List.Membership.Propositional.Properties
open import Data.Empty using (⊥; ⊥-elim)

-- a size's list: where it first appears among the sizes (past them all if it does not)
idx-of : ℕ → List ℕ → ℕ
idx-of k []       = 0
idx-of k (x ∷ xs) = if k ≡ᵇ x then 0 else suc (idx-of k xs)

private
  idx-≤ : ∀ k xs → idx-of k xs ≤ length xs
  idx-≤ k []       = z≤n
  idx-≤ k (x ∷ xs) = by (k ≡ᵇ x)
    where by : ∀ b → (if b then 0 else suc (idx-of k xs)) ≤ suc (length xs)
          by true  = z≤n
          by false = s≤s (idx-≤ k xs)

  -- the index tells the size apart, among the sizes
  idx-inj : ∀ {k k′} xs → k ∈ xs → k′ ∈ xs → idx-of k xs ≡ idx-of k′ xs → k ≡ k′
  idx-inj {k} {k′} (x ∷ xs) m m′ e = by (k ≡ᵇ x) refl (k′ ≡ᵇ x) refl m m′ e
    where
      by : ∀ b → (k ≡ᵇ x) ≡ b → ∀ b′ → (k′ ≡ᵇ x) ≡ b′ → k ∈ (x ∷ xs) → k′ ∈ (x ∷ xs)
         → (if b then 0 else suc (idx-of k xs)) ≡ (if b′ then 0 else suc (idx-of k′ xs)) → k ≡ k′
      by true  eb true  eb′ _ _ _ = trans (Data.Nat.Properties.≡ᵇ⇒≡ k x (subst Data.Bool.T (sym eb) _))
                                          (sym (Data.Nat.Properties.≡ᵇ⇒≡ k′ x (subst Data.Bool.T (sym eb′) _)))
      by true  _ false _ _ _ ()
      by false _ true  _ _ _ ()
      by false eb false eb′ q q′ e′ = idx-inj xs (tl eb q) (tl eb′ q′) (Data.Nat.Properties.suc-injective e′)
        where
          tl : ∀ {z} → (z ≡ᵇ x) ≡ false → z ∈ (x ∷ xs) → z ∈ xs
          tl {z} f (here refl) = ⊥-elim (no f (Data.Nat.Properties.≡⇒≡ᵇ z z refl))
            where no : ∀ {c} → c ≡ false → Data.Bool.T c → ⊥
                  no refl ()
          tl f (there p) = p

-- the program's sizes, once each
dsizes : AbstractTrace → List ℕ
dsizes P = deduplicate Data.Nat.Properties._≟_ (sizes P)

slab-of : AbstractTrace → Bool → Classes
slab-of P true  = record { count = suc (length (dsizes P)) ; cls = λ k → idx-of k (dsizes P) ; bsz = λ k → k }
slab-of P false = pool P

slab : AbstractTrace → Classes
slab P = slab-of P (length (dsizes P) ≤ᵇ 60)

module Slab (P : AbstractTrace) where
  private
    ∈-dd : ∀ {xs z} → z ∈ xs → z ∈ deduplicate Data.Nat.Properties._≟_ xs
    ∈-dd = Data.List.Membership.Propositional.Properties.∈-deduplicate⁺ Data.Nat.Properties._≟_
    b = length (dsizes P) ≤ᵇ 60

  C = slab P

  -- what the expansion asks, of either branch
  record Asks (C′ : Classes) : Set where
    field
      small    : 3 + count C′ ≤ rec-size
      in-range : ∀ k → cls C′ k < count C′
      fits     : ∀ k → k ≤ bsz C′ k
      uniform  : ∀ k k′ → Sz P k → Sz P k′ → cls C′ k ≡ cls C′ k′ → bsz C′ k ≡ bsz C′ k′

  private
    asks : ∀ b′ → (length (dsizes P) ≤ᵇ 60) ≡ b′ → Asks (slab-of P b′)
    asks true  e = record
      { small    = s≤s (s≤s (s≤s (Data.Nat.Properties.≤-trans (s≤s (Data.Nat.Properties.≤ᵇ⇒≤ _ 60 (subst Data.Bool.T (sym e) _))) (Data.Nat.Properties.≤-reflexive refl))))
      ; in-range = λ k → s≤s (idx-≤ k (dsizes P))
      ; fits     = λ k → Data.Nat.Properties.≤-refl
      ; uniform  = λ k k′ s s′ e′ → idx-inj (dsizes P) (∈-dd s) (∈-dd s′) e′ }
    asks false _ = record { small = Pool.small P ; in-range = Pool.in-range P ; fits = Pool.fits P ; uniform = Pool.uniform P }

  A = asks b refl

  small : 3 + count C ≤ rec-size
  small = Asks.small A
  in-range : ∀ k → cls C k < count C
  in-range = Asks.in-range A
  fits : ∀ k → k ≤ bsz C k
  fits = Asks.fits A
  uniform : ∀ k k′ → Sz P k → Sz P k′ → cls C k ≡ cls C k′ → bsz C k ≡ bsz C k′
  uniform = Asks.uniform A
