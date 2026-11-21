-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Allocator.Slab
--
-- A slab: one `Mempool` per size class (D384: the classes are the program's
-- node sizes, exact — no rounding up), and the shared frontier when a
-- class's list is empty (D428 part 2: one region, the cells growing up).
--
-- Generic in what a block is and in the classes (any type with decidable
-- equality: the sizes themselves). What it promises is stated against the
-- blocks in use, per class, which the caller keeps:
--
--   * `SlabInv ps lv`: each class's pool keeps `PoolInv` against its live
--     blocks, and no block is known (free or live) to two classes;
--   * `alloc k` hands out a block of class `k` that is no live block of any
--     class — a popped one, or a fresh one from the frontier (`Fresh`: known
--     to no class; the caller's, from the frontier) — and the invariant holds
--     with it live (`alloc-ok`);
--   * `free k` of a live block of class `k` keeps the invariant with it free
--     (`free-ok`), so the next alloc of class `k` may hand it to another user.
--
-- Plan 0.146 B1.6 item 3 (D468, the user, 2026-11-22/23).
------------------------------------------------------------------------

open import Relation.Binary.Definitions using (DecidableEquality)

module Once.Allocator.Slab {Block : Set} {K : Set} (_≟K_ : DecidableEquality K) where

open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ; ∈-++⁺ʳ; ∈-++⁻)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; subst₂)

open import Once.Allocator.Mempool {Block}
  using (Pool; pool; free-list; PoolInv; module PoolInv; pop; push; pop-fresh; pop-inv; push-inv; cons-u; empty-inv)
open PoolInv using (free-unique; live-unique; apart)

------------------------------------------------------------------------
-- The slab and its invariant
------------------------------------------------------------------------

Pools : Set
Pools = K → Pool

Live : Set
Live = K → List Block

-- the blocks class `k` knows: its free list and its live blocks
Known : Pools → Live → K → Block → Set
Known ps lv k b = b ∈ free-list (ps k) ++ lv k

record SlabInv (ps : Pools) (lv : Live) : Set where
  field
    per-class : ∀ k → PoolInv (ps k) (lv k)
    one-class : ∀ {k k′ b} → Known ps lv k b → Known ps lv k′ b → k ≡ k′
open SlabInv public

-- a block no class knows: what the frontier hands out
Fresh : Pools → Live → Block → Set
Fresh ps lv b = ∀ k → ¬ Known ps lv k b

------------------------------------------------------------------------
-- Updating one class
------------------------------------------------------------------------

upd-dec : ∀ {A : Set} {k′ k : K} → Dec (k′ ≡ k) → A → A → A
upd-dec (yes _) a _ = a
upd-dec (no _)  _ b = b

at : ∀ {A : Set} → K → A → (K → A) → K → A
at k a f k′ = upd-dec (k′ ≟K k) a (f k′)

-- after updating class `k`, class `k′` is `k` (the new value) or as it was
data AtView {A : Set} (k : K) (a : A) (f : K → A) (k′ : K) : Set where
  is-k    : k′ ≡ k → at k a f k′ ≡ a → AtView k a f k′
  other-k : ¬ k′ ≡ k → at k a f k′ ≡ f k′ → AtView k a f k′

at-view : ∀ {A : Set} (k : K) (a : A) (f : K → A) (k′ : K) → AtView k a f k′
at-view k a f k′ = by (k′ ≟K k)
  where
    by : (d : Dec (k′ ≡ k)) → AtView k a f k′
    by (yes e) = is-k e (eq d′) where
      d′ = k′ ≟K k
      eq : (d : Dec (k′ ≡ k)) → upd-dec d a (f k′) ≡ a
      eq (yes _) = refl
      eq (no ne) = ⊥-elim (ne e)
    by (no ne) = other-k ne (eq (k′ ≟K k)) where
      eq : (d : Dec (k′ ≡ k)) → upd-dec d a (f k′) ≡ f k′
      eq (yes e) = ⊥-elim (ne e)
      eq (no _)  = refl

------------------------------------------------------------------------
-- Membership over the two lists a class knows
------------------------------------------------------------------------

private
  -- b′ moved from the free list's head to the live list's head: the same blocks
  moved : ∀ {b′ x : Block} (fs ls : List Block) → x ∈ fs ++ b′ ∷ ls → x ∈ (b′ ∷ fs) ++ ls
  moved {b′} fs ls m = [ (λ m₁ → there (∈-++⁺ˡ m₁)) , back ]′ (∈-++⁻ fs m)
    where
      back : ∀ {x} → x ∈ b′ ∷ ls → x ∈ (b′ ∷ fs) ++ ls
      back (here e)  = here e
      back (there n) = there (∈-++⁺ʳ fs n)

  -- a block pushed from the live list to the free list: the same blocks
  pushed : ∀ {b x : Block} (fs : List Block) (l₁ l₂ : List Block) → x ∈ (b ∷ fs) ++ (l₁ ++ l₂) → x ∈ fs ++ (l₁ ++ b ∷ l₂)
  pushed fs l₁ l₂ (here e)  = ∈-++⁺ʳ fs (∈-++⁺ʳ l₁ (here e))
  pushed {b} fs l₁ l₂ (there m) = [ ∈-++⁺ˡ , (λ n → ∈-++⁺ʳ fs (wid n)) ]′ (∈-++⁻ fs m)
    where
      wid : ∀ {x} → x ∈ l₁ ++ l₂ → x ∈ l₁ ++ b ∷ l₂
      wid n = [ ∈-++⁺ˡ , (λ n₂ → ∈-++⁺ʳ l₁ (there n₂)) ]′ (∈-++⁻ l₁ n)

  -- one more live block: it, or a block known before
  consed : ∀ {b x : Block} (fs ls : List Block) → x ∈ fs ++ b ∷ ls → (x ≡ b) ⊎ (x ∈ fs ++ ls)
  consed fs ls m = [ (λ m₁ → inj₂ (∈-++⁺ˡ m₁)) , back ]′ (∈-++⁻ fs m)
    where
      back : ∀ {x b} → x ∈ b ∷ ls → (x ≡ b) ⊎ (x ∈ fs ++ ls)
      back (here e)  = inj₁ e
      back (there n) = inj₂ (∈-++⁺ʳ fs n)

  ∈-subst : ∀ {x : Block} {l l′} → l ≡ l′ → x ∈ l → x ∈ l′
  ∈-subst refl m = m

------------------------------------------------------------------------
-- ★ Alloc: a popped block, or a fresh one from the frontier
------------------------------------------------------------------------

-- by what the class's pool gave
alloc-from : K → Block → Pools → Maybe (Block × Pool) → Block × Pools
alloc-from k b ps (just (b′ , p′)) = b′ , at k p′ ps
alloc-from k b ps nothing          = b , ps

-- alloc of class `k`, `b` the frontier's block should the list be empty
alloc : K → Block → Pools → Block × Pools
alloc k b ps = alloc-from k b ps (pop (ps k))

-- the live blocks after an alloc: the block handed out live in its class
live-after : K → Block → Live → Live
live-after k b′ lv = at k (b′ ∷ lv k) lv

record AllocOK (ps : Pools) (lv : Live) (k : K) (b′ : Block) (ps′ : Pools) : Set where
  field
    a-inv   : SlabInv ps′ (live-after k b′ lv)
    a-apart : ∀ k′ → b′ ∉ lv k′
open AllocOK public

private
  popped : ∀ (p : Pool) {b′ p′} → pop p ≡ just (b′ , p′) → free-list p ≡ b′ ∷ free-list p′
  popped (pool (x ∷ xs)) refl = refl

  empty : ∀ (p : Pool) → pop p ≡ nothing → free-list p ≡ []
  empty (pool []) refl = refl

  -- a popped block, live: what each class knows after, it knew before
  alloc-pop : ∀ {ps lv} (k : K) {b′ p′} → SlabInv ps lv → pop (ps k) ≡ just (b′ , p′)
            → AllocOK ps lv k b′ (at k p′ ps)
  alloc-pop {ps} {lv} k {b′} {p′} I e = record { a-inv = inv′ ; a-apart = apart′ }
    where
      fl = popped (ps k) e
      known-k : b′ ∈ free-list (ps k) ++ lv k
      known-k = ∈-subst (cong-++ (sym fl)) (here refl)
        where cong-++ : ∀ {l l′ : List Block} → l ≡ l′ → l ++ lv k ≡ l′ ++ lv k
              cong-++ refl = refl
      before : ∀ {k″ x} → Known (at k p′ ps) (live-after k b′ lv) k″ x → Known ps lv k″ x
      before {k″} {x} m = by (at-view k p′ ps k″) (at-view k (b′ ∷ lv k) lv k″)
        where
          by : AtView k p′ ps k″ → AtView k (b′ ∷ lv k) lv k″ → Known ps lv k″ x
          by (is-k e _) (other-k ne _) = ⊥-elim (ne e)
          by (other-k ne _) (is-k e _) = ⊥-elim (ne e)
          by (other-k _ e₁) (other-k _ e₂) = subst₂ (λ p l → x ∈ free-list p ++ l) e₁ e₂ m
          by (is-k refl e₁) (is-k _ e₂) =
            ∈-subst (cong-++ (sym fl)) (moved (free-list p′) (lv k) (subst₂ (λ p l → x ∈ free-list p ++ l) e₁ e₂ m))
            where cong-++ : ∀ {l l′ : List Block} → l ≡ l′ → l ++ lv k ≡ l′ ++ lv k
                  cong-++ refl = refl
      inv′ : SlabInv (at k p′ ps) (live-after k b′ lv)
      inv′ = record { per-class = cls ; one-class = λ m₁ m₂ → one-class I (before m₁) (before m₂) }
        where
          cls : ∀ k″ → PoolInv (at k p′ ps k″) (live-after k b′ lv k″)
          cls k″ = by (at-view k p′ ps k″) (at-view k (b′ ∷ lv k) lv k″)
            where
              by : AtView k p′ ps k″ → AtView k (b′ ∷ lv k) lv k″ → PoolInv (at k p′ ps k″) (live-after k b′ lv k″)
              by (is-k e _) (other-k ne _) = ⊥-elim (ne e)
              by (other-k ne _) (is-k e _) = ⊥-elim (ne e)
              by (other-k _ e₁) (other-k _ e₂) = subst₂ PoolInv (sym e₁) (sym e₂) (per-class I k″)
              by (is-k refl e₁) (is-k _ e₂) = subst₂ PoolInv (sym e₁) (sym e₂) (pop-inv (per-class I k) e)
      apart′ : ∀ k′ → b′ ∉ lv k′
      apart′ k′ n = by (k′ ≟K k)
        where
          by : Dec (k′ ≡ k) → ⊥
          by (yes refl) = pop-fresh (per-class I k) e n
          by (no ne)    = ne (one-class I (∈-++⁺ʳ (free-list (ps k′)) n) known-k)

  -- a fresh block, live: it is known to class `k` alone
  alloc-fresh : ∀ {ps lv} (k : K) (b : Block) → SlabInv ps lv → Fresh ps lv b → pop (ps k) ≡ nothing
              → AllocOK ps lv k b ps
  alloc-fresh {ps} {lv} k b I fr e = record { a-inv = inv′ ; a-apart = λ k′ n → fr k′ (∈-++⁺ʳ (free-list (ps k′)) n) }
    where
      before : ∀ {k″ x} → Known ps (live-after k b lv) k″ x → (x ≡ b × k″ ≡ k) ⊎ Known ps lv k″ x
      before {k″} {x} m = by (at-view k (b ∷ lv k) lv k″)
        where
          by : AtView k (b ∷ lv k) lv k″ → (x ≡ b × k″ ≡ k) ⊎ Known ps lv k″ x
          by (is-k refl e₂) = [ (λ xb → inj₁ (xb , refl)) , inj₂ ]′ (consed (free-list (ps k)) (lv k) (subst (λ l → x ∈ free-list (ps k) ++ l) e₂ m))
          by (other-k _ e₂) = inj₂ (subst (λ l → x ∈ free-list (ps k″) ++ l) e₂ m)
      one : ∀ {k₁ k₂ x} → Known ps (live-after k b lv) k₁ x → Known ps (live-after k b lv) k₂ x → k₁ ≡ k₂
      one {x = x} m₁ m₂ = by (before m₁) (before m₂)
        where
          by : ∀ {k₁ k₂} → (x ≡ b × k₁ ≡ k) ⊎ Known ps lv k₁ x → (x ≡ b × k₂ ≡ k) ⊎ Known ps lv k₂ x → k₁ ≡ k₂
          by (inj₁ (_ , e₁)) (inj₁ (_ , e₂)) = trans e₁ (sym e₂)
          by {k₂ = k₂} (inj₁ (refl , _)) (inj₂ n) = ⊥-elim (fr k₂ n)
          by {k₁ = k₁} (inj₂ n) (inj₁ (refl , _)) = ⊥-elim (fr k₁ n)
          by (inj₂ n₁) (inj₂ n₂) = one-class I n₁ n₂
      inv′ : SlabInv ps (live-after k b lv)
      inv′ = record { per-class = cls ; one-class = one }
        where
          cls : ∀ k″ → PoolInv (ps k″) (live-after k b lv k″)
          cls k″ = by (at-view k (b ∷ lv k) lv k″)
            where
              by : AtView k (b ∷ lv k) lv k″ → PoolInv (ps k″) (live-after k b lv k″)
              by (is-k refl e₂) = subst (PoolInv (ps k)) (sym e₂) (record
                { free-unique = free-unique (per-class I k)
                ; live-unique = cons-u (λ n → fr k (∈-++⁺ʳ (free-list (ps k)) n)) (live-unique (per-class I k))
                ; apart = λ m → ⊥-elim (none (∈-subst (empty (ps k) e) m)) })
                where none : ∀ {x : Block} → x ∈ [] → ⊥
                      none ()
              by (other-k _ e₂) = subst (PoolInv (ps k″)) (sym e₂) (per-class I k″)

-- ★ alloc keeps the invariant, the block handed out live and no live block before
alloc-ok : ∀ {ps lv} (k : K) (b : Block) → SlabInv ps lv → Fresh ps lv b
         → AllocOK ps lv k (proj₁ (alloc k b ps)) (proj₂ (alloc k b ps))
alloc-ok {ps} {lv} k b I fr = by (pop (ps k)) refl
  where
    by : ∀ m → pop (ps k) ≡ m → AllocOK ps lv k (proj₁ (alloc-from k b ps m)) (proj₂ (alloc-from k b ps m))
    by (just (b′ , p′)) e = alloc-pop k I e
    by nothing          e = alloc-fresh k b I fr e

------------------------------------------------------------------------
-- ★ Free: a live block of its class back on that class's list
------------------------------------------------------------------------

free : K → Block → Pools → Pools
free k b ps = at k (push b (ps k)) ps

free-ok : ∀ {ps lv} (k : K) (l₁ : List Block) {b l₂} → SlabInv ps lv → lv k ≡ l₁ ++ b ∷ l₂
        → SlabInv (free k b ps) (at k (l₁ ++ l₂) lv)
free-ok {ps} {lv} k l₁ {b} {l₂} I el = record { per-class = cls ; one-class = λ m₁ m₂ → one-class I (before m₁) (before m₂) }
  where
    before : ∀ {k″ x} → Known (free k b ps) (at k (l₁ ++ l₂) lv) k″ x → Known ps lv k″ x
    before {k″} {x} m = by (at-view k (push b (ps k)) ps k″) (at-view k (l₁ ++ l₂) lv k″)
      where
        by : AtView k (push b (ps k)) ps k″ → AtView k (l₁ ++ l₂) lv k″ → Known ps lv k″ x
        by (is-k e _) (other-k ne _) = ⊥-elim (ne e)
        by (other-k ne _) (is-k e _) = ⊥-elim (ne e)
        by (other-k _ e₁) (other-k _ e₂) = subst₂ (λ p l → x ∈ free-list p ++ l) e₁ e₂ m
        by (is-k refl e₁) (is-k _ e₂) =
          subst (λ l → x ∈ free-list (ps k) ++ l) (sym el)
            (pushed (free-list (ps k)) l₁ l₂ (subst₂ (λ p l → x ∈ free-list p ++ l) e₁ e₂ m))
    cls : ∀ k″ → PoolInv (free k b ps k″) (at k (l₁ ++ l₂) lv k″)
    cls k″ = by (at-view k (push b (ps k)) ps k″) (at-view k (l₁ ++ l₂) lv k″)
      where
        by : AtView k (push b (ps k)) ps k″ → AtView k (l₁ ++ l₂) lv k″ → PoolInv (free k b ps k″) (at k (l₁ ++ l₂) lv k″)
        by (is-k e _) (other-k ne _) = ⊥-elim (ne e)
        by (other-k ne _) (is-k e _) = ⊥-elim (ne e)
        by (other-k _ e₁) (other-k _ e₂) = subst₂ PoolInv (sym e₁) (sym e₂) (per-class I k″)
        by (is-k refl e₁) (is-k _ e₂) = subst₂ PoolInv (sym e₁) (sym e₂) (push-inv l₁ (subst (PoolInv (ps k)) el (per-class I k)))

------------------------------------------------------------------------
-- The empty slab
------------------------------------------------------------------------

empty-slab : SlabInv (λ _ → pool []) (λ _ → [])
empty-slab = record { per-class = λ _ → empty-inv ; one-class = λ () }
