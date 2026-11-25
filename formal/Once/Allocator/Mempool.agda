-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Allocator.Mempool
--
-- A mempool: blocks of ONE size, kept on a free list (D384: one fixed-size
-- free list per node size, alloc and free inline pop/push, no search).
--
-- Generic in what a block is (an abstract heap ref, an address): the pool
-- is the free list alone, and what it promises is stated against the
-- blocks in use (`live`), which the caller keeps:
--
--   * `PoolInv p live`: the free blocks are distinct, the live ones are
--     distinct, and no block is both free and live;
--   * `pop` (alloc) hands out a block that is no live one, and the
--     invariant holds with it live;
--   * `push` (free) of a live block takes it back, and the invariant holds
--     with it free — a freed block is returned for another user
--     (`push-pop`: the next pop is that block).
--
-- Plan 0.146 B1.6 item 3 (D470, the user, 2026-11-23: "a block should be
-- able to be freed and returned for another user"). The size classes and
-- the shared frontier are `Slab`'s.
------------------------------------------------------------------------

module Once.Allocator.Mempool {Block : Set} where

open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ; ∈-++⁺ʳ; ∈-++⁻)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.AllPairs using (AllPairs; []; _∷_)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym)

------------------------------------------------------------------------
-- The pool and its invariant
------------------------------------------------------------------------

record Pool : Set where
  constructor pool
  field
    free-list : List Block
open Pool public

record PoolInv (p : Pool) (live : List Block) : Set where
  field
    free-unique : Unique (free-list p)
    live-unique : Unique live
    apart       : ∀ {b} → b ∈ free-list p → b ∉ live
open PoolInv public

------------------------------------------------------------------------
-- Alloc and free
------------------------------------------------------------------------

-- pop: the first free block, and the pool without it (nothing when empty)
pop : Pool → Maybe (Block × Pool)
pop (pool [])       = nothing
pop (pool (b ∷ bs)) = just (b , pool bs)

-- push: a block back on the free list
push : Block → Pool → Pool
push b p = pool (b ∷ free-list p)

-- a freed block is returned for another user: the next pop is it
push-pop : ∀ b p → pop (push b p) ≡ just (b , p)
push-pop b (pool bs) = refl

------------------------------------------------------------------------
-- Distinct lists (small lemmas over `Unique`)
------------------------------------------------------------------------

module _ where
  -- the head of a distinct list is not in its tail
  head∉ : ∀ {b : Block} {bs : List Block} → Unique (b ∷ bs) → b ∉ bs
  head∉ ((b≢ ∷ _) ∷ _) (here refl) = b≢ refl
  head∉ ((_ ∷ ne) ∷ u) (there m) = head∉ (ne ∷ tail-pairs u) m
    where
      tail-pairs : ∀ {x : Block} {xs : List Block} → Unique (x ∷ xs) → Unique xs
      tail-pairs (_ ∷ u′) = u′

  tail-u : ∀ {b : Block} {bs : List Block} → Unique (b ∷ bs) → Unique bs
  tail-u (_ ∷ u) = u

  -- a block not in a list is apart from each of its elements
  ∉→All : ∀ {b : Block} (xs : List Block) → b ∉ xs → All (b ≢_) xs
  ∉→All []       _  = []
  ∉→All (x ∷ xs) nm = (λ e → nm (here e)) ∷ ∉→All xs (λ m → nm (there m))

  All→∉ : ∀ {b : Block} {xs : List Block} → All (b ≢_) xs → b ∉ xs
  All→∉ (ne ∷ _)  (here e) = ne e
  All→∉ (_ ∷ as) (there m) = All→∉ as m

  -- consing a block not in a distinct list keeps it distinct
  cons-u : ∀ {b : Block} {xs : List Block} → b ∉ xs → Unique xs → Unique (b ∷ xs)
  cons-u {xs = xs} nm u = ∉→All xs nm ∷ u

  -- a distinct list with one block taken out: still distinct, and the block is in neither part
  wider : ∀ (l₁ : List Block) {b : Block} {l₂ : List Block} {z : Block} → z ∈ l₁ ++ l₂ → z ∈ l₁ ++ b ∷ l₂
  wider l₁ m = [ ∈-++⁺ˡ , (λ m₂ → ∈-++⁺ʳ l₁ (there m₂)) ]′ (∈-++⁻ l₁ m)

  drop-all : ∀ (l₁ : List Block) {b : Block} {l₂ : List Block} {y : Block} → All (y ≢_) (l₁ ++ b ∷ l₂) → All (y ≢_) (l₁ ++ l₂)
  drop-all l₁ {b} {l₂} a = ∉→All (l₁ ++ l₂) (λ m → All→∉ a (wider l₁ {b} m))

  split-u : ∀ (l₁ : List Block) {b : Block} {l₂ : List Block} → Unique (l₁ ++ b ∷ l₂) → Unique (l₁ ++ l₂) × b ∉ (l₁ ++ l₂)
  split-u []       u = tail-u u , head∉ u
  split-u (x ∷ l₁) {b} {l₂} (ax ∷ u) =
    (drop-all l₁ ax ∷ proj₁ (split-u l₁ u)) , nm
    where
      nm : b ∉ x ∷ (l₁ ++ l₂)
      nm (here e)  = All→∉ ax (∈-++⁺ʳ l₁ (here (sym e)))
      nm (there m) = proj₂ (split-u l₁ u) m

  -- a block in a part is in the whole
  in-split : ∀ (l₁ : List Block) {b : Block} {l₂ : List Block} {z : Block} → z ∈ l₁ ++ l₂ → z ∈ l₁ ++ b ∷ l₂
  in-split = wider

------------------------------------------------------------------------
-- ★ The theorems
------------------------------------------------------------------------

-- alloc: the popped block is no live one…
pop-fresh : ∀ {p live b p′} → PoolInv p live → pop p ≡ just (b , p′) → b ∉ live
pop-fresh {pool (b ∷ bs)} I refl = apart I (here refl)

-- …and the pool's invariant holds with it live
pop-inv : ∀ {p live b p′} → PoolInv p live → pop p ≡ just (b , p′) → PoolInv p′ (b ∷ live)
pop-inv {pool (b ∷ bs)} {live} I refl = record
  { free-unique = tail-u (free-unique I)
  ; live-unique = cons-u (apart I (here refl)) (live-unique I)
  ; apart       = ap
  }
  where
    ap : ∀ {x} → x ∈ bs → x ∉ b ∷ live
    ap m (here e) = head∉ (free-unique I) (subst-∈ e m)
      where subst-∈ : ∀ {x y} → x ≡ y → x ∈ bs → y ∈ bs
            subst-∈ refl m′ = m′
    ap m (there n) = apart I (there m) n

-- free: a live block pushed back — the invariant holds with it free
push-inv : ∀ {p} (l₁ : List Block) {b l₂} → PoolInv p (l₁ ++ b ∷ l₂) → PoolInv (push b p) (l₁ ++ l₂)
push-inv {p} l₁ {b} {l₂} I = record
  { free-unique = cons-u (λ m → apart I m (∈-++⁺ʳ l₁ (here refl))) (free-unique I)
  ; live-unique = proj₁ (split-u l₁ (live-unique I))
  ; apart       = ap
  }
  where
    ap : ∀ {x} → x ∈ b ∷ free-list p → x ∉ l₁ ++ l₂
    ap (here refl) n = proj₂ (split-u l₁ (live-unique I)) n
    ap (there m)   n = apart I m (in-split l₁ {b} n)

-- the empty pool, nothing live
empty-inv : PoolInv (pool []) []
empty-inv = record { free-unique = [] ; live-unique = [] ; apart = λ () }
