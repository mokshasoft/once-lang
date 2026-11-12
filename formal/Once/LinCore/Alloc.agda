-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.LinCore.Alloc — plan 0.146 A17 (D411): ONE SIZE CLASS'S POOL.
--
-- A pool of size `k` (free lists per size, D403) numbers its blocks from 0;
-- the pool holds blocks `0 … top-1`, and where each lies in the one region
-- is `Once.LinCore.Region`'s (`addr k j`: the region gives a growing pool the next
-- `k` words at its top). The pool follows the run's events of its size: a
-- cell born takes the lowest free block below the top, or the top grows by
-- one; a cell freed frees its block; a temporary (a frame) likewise, newest
-- first.
--
-- Every block has one OWNER (`who`: free, a cell by its serial, a
-- temporary by its name); a cell's block is `own s`. So:
--
--   * ADDRESSES ARE REUSED (the lowest free block first), the run's ids are
--     not, and the map from ids to blocks is INJECTIVE ON LIVE BLOCKS — by
--     construction: `who` is a function (`live-injective`);
--   * ★ the pool grows only when it is FULL — every block below the top
--     holds a live cell or a live temporary of its own
--     (`grows-only-when-full`), and after growing it is full again
--     (`grow-full`). `Once.LinCore.Region` makes this the space claim.
--
-- Free lists per size cannot serve one size from another's freed blocks,
-- so "a run runs out only when its live data does not fit" is false for
-- them; no allocator that never moves a block can promise it (Robson 1974),
-- and moving blocks is a collector (GOAL.md excludes it). The claim is per
-- size's peak (D411 part 2, decided: `Once.LinCore.Region`).
------------------------------------------------------------------------

{-# OPTIONS --safe --guardedness #-}

open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (sym; trans; cong; subst; _≢_)
open import Agda.Builtin.Sigma using (Σ; _,_; fst; snd)
open import Data.Product using (_×_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _≤_; _<_; z≤n; s≤s; _≟_)
open import Data.Nat.Properties using (≤-refl; ≤-trans; n≤1+n; <-irrefl; ≤-pred; m≤n⇒m<n∨m≡n)
open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Relation.Nullary using (Dec; yes; no; ¬_)

module Once.LinCore.Alloc where

------------------------------------------------------------------------
-- 1. THE STATE of one size class.
------------------------------------------------------------------------

data Who : Set where
  freeW : Who
  cellW : ℕ → Who      -- a cell, by its serial
  tempW : ℕ → Who      -- a temporary, by its name

cellW-inj : ∀ {a b} → cellW a ≡ cellW b → a ≡ b
cellW-inj refl = refl

_≟w_ : (a b : Who) → Dec (a ≡ b)
freeW   ≟w freeW   = yes refl
freeW   ≟w cellW _ = no λ ()
freeW   ≟w tempW _ = no λ ()
cellW _ ≟w freeW   = no λ ()
cellW a ≟w cellW b with a ≟ b
... | yes refl = yes refl
... | no ne    = no λ e → ne (cellW-inj e)
cellW _ ≟w tempW _ = no λ ()
tempW _ ≟w freeW   = no λ ()
tempW _ ≟w cellW _ = no λ ()
tempW a ≟w tempW b with a ≟ b
... | yes refl = yes refl
... | no ne    = no λ { refl → ne refl }

record Pool : Set where
  constructor pool
  field
    top   : ℕ                -- the region holds blocks 0 … top-1
    who   : ℕ → Who          -- each block's owner
    own   : ℕ → ℕ            -- each cell's block, by serial (meaningful while live)
    temps : List (ℕ × ℕ)     -- live temporaries: (name, block), newest first
    tc    : ℕ                -- the next temporary's name
open Pool public

empty : Pool
empty = pool 0 (λ _ → freeW) (λ _ → 0) [] 0

-- a cell is live when its block says so
Live : Pool → ℕ → Set
Live p s = who p (own p s) ≡ cellW s

-- a point update
upd : ∀ {X : Set} → (ℕ → X) → ℕ → X → ℕ → X
upd f j x j′ with j ≟ j′
... | yes _ = x
... | no _  = f j′

upd-same : ∀ {X : Set} (f : ℕ → X) j x → upd f j x j ≡ x
upd-same f j x with j ≟ j
... | yes _ = refl
... | no ne = ⊥-elim (ne refl)

upd-other : ∀ {X : Set} (f : ℕ → X) {j j′} x → j ≢ j′ → upd f j x j′ ≡ f j′
upd-other f {j} {j′} x ne with j ≟ j′
... | yes e = ⊥-elim (ne e)
... | no _  = refl

------------------------------------------------------------------------
-- 2. TAKING A BLOCK: the lowest free one below the top, else the top.
------------------------------------------------------------------------

firstFree : (ℕ → Who) → ℕ → Maybe ℕ
firstFree w zero    = nothing
firstFree w (suc n) with firstFree w n
... | just j  = just j
... | nothing with w n ≟w freeW
...   | yes _ = just n
...   | no _  = nothing

ff-just : ∀ w n {j} → firstFree w n ≡ just j → j < n × w j ≡ freeW
ff-just w (suc n) e with firstFree w n in eq
... | just j′ with e
...   | refl = (≤-trans (fst (ff-just w n eq)) (n≤1+n n) , snd (ff-just w n eq))
ff-just w (suc n) e | nothing with w n ≟w freeW
...   | yes f with e
...     | refl = (≤-refl , f)
ff-just w (suc n) () | nothing | no _

ff-nothing : ∀ w n → firstFree w n ≡ nothing → ∀ j → j < n → w j ≢ freeW
ff-nothing w (suc n) e j lt with firstFree w n in eq
ff-nothing w (suc n) () j lt | just _
... | nothing with w n ≟w freeW
ff-nothing w (suc n) () j lt | nothing | yes _
...   | no nf with m≤n⇒m<n∨m≡n (≤-pred lt)
...     | inj₁ lt′ = ff-nothing w n eq j lt′
...     | inj₂ refl = nf

-- the block taken, and the new top
take : Pool → ℕ × ℕ
take p with firstFree (who p) (top p)
... | just j  = (j , top p)
... | nothing = (top p , suc (top p))

------------------------------------------------------------------------
-- 3. THE STEPS: a cell born or freed, a temporary born or freed. A step the
-- allocator cannot make (a live cell born again, a dead one freed, no
-- temporary to free) is `nothing`: a legal run never asks for one.
------------------------------------------------------------------------

born : ℕ → Pool → Maybe Pool
born s p with who p (own p s) ≟w cellW s
... | yes _ = nothing
... | no _  = just (pool (snd (take p)) (upd (who p) (fst (take p)) (cellW s))
                         (upd (own p) s (fst (take p))) (temps p) (tc p))

died : ℕ → Pool → Maybe Pool
died s p with who p (own p s) ≟w cellW s
... | yes _ = just (pool (top p) (upd (who p) (own p s) freeW) (own p) (temps p) (tc p))
... | no _  = nothing

tborn : Pool → Pool
tborn p = pool (snd (take p)) (upd (who p) (fst (take p)) (tempW (tc p))) (own p)
               ((tc p , fst (take p)) ∷ temps p) (suc (tc p))

tdied : Pool → Maybe Pool
tdied p with temps p
... | []            = nothing
... | (m , j) ∷ ts  = just (pool (top p) (upd (who p) j freeW) (own p) ts (tc p))

------------------------------------------------------------------------
-- 4. THE INVARIANT: above the top all is free; a cell's block is where its
-- owner says; a temporary's block is on the stack, and the stack's blocks
-- are its temporaries'.
------------------------------------------------------------------------

-- the temporaries' names, newest first, all below `n`: so no two are one
Desc : List (ℕ × ℕ) → ℕ → Set
Desc []            n = ⊤
Desc ((m , j) ∷ ts) n = m < n × Desc ts m

desc-below : ∀ {ts m j n} → (m , j) ∈ ts → Desc ts n → m < n
desc-below (here refl) (lt , _) = lt
desc-below {(m′ , _) ∷ ts} (there mem) (lt , d) = ≤-trans (desc-below mem d) (≤-trans (n≤1+n _) lt)

desc-weaken : ∀ {ts m n} → m ≤ n → Desc ts m → Desc ts n
desc-weaken {[]} le d = tt
desc-weaken {(m′ , _) ∷ ts} le (lt , d) = (≤-trans lt le , d)

record Inv (p : Pool) : Set where
  field
    above : ∀ j → top p ≤ j → who p j ≡ freeW
    cells : ∀ j s → who p j ≡ cellW s → own p s ≡ j
    tmps  : ∀ j m → who p j ≡ tempW m → (m , j) ∈ temps p
    stack : ∀ m j → (m , j) ∈ temps p → who p j ≡ tempW m
    desc  : Desc (temps p) (tc p)
open Inv public

inv-empty : Inv empty
inv-empty = record { above = λ _ _ → refl ; cells = λ _ _ () ; tmps = λ _ _ () ; stack = λ _ _ () ; desc = tt }

-- the block taken was free, and below the new top
take-free : ∀ p → Inv p → who p (fst (take p)) ≡ freeW × fst (take p) < snd (take p)
take-free p iv with firstFree (who p) (top p) in eq
... | just j  = (snd (ff-just (who p) (top p) eq) , fst (ff-just (who p) (top p) eq))
... | nothing = (above iv (top p) ≤-refl , ≤-refl)

take-top : ∀ p → top p ≤ snd (take p)
take-top p with firstFree (who p) (top p)
... | just _  = ≤-refl
... | nothing = n≤1+n _

private
  -- a free block is no cell's and no temporary's
  free-cell : ∀ {p j s} → who p j ≡ freeW → who p j ≡ cellW s → ⊥
  free-cell f c with trans (sym f) c
  ... | ()
  free-temp : ∀ {p j m} → who p j ≡ freeW → who p j ≡ tempW m → ⊥
  free-temp f t with trans (sym f) t
  ... | ()

born-inv : ∀ s p {p′} → Inv p → born s p ≡ just p′ → Inv p′
born-inv s p iv e with who p (own p s) ≟w cellW s
born-inv s p iv () | yes _
born-inv s p iv refl | no notlive = record { above = ab ; cells = ce ; tmps = tm ; stack = st ; desc = desc iv }
  where
    j  = fst (take p)
    tf = take-free p iv
    ab : ∀ j′ → snd (take p) ≤ j′ → upd (who p) j (cellW s) j′ ≡ freeW
    ab j′ le with j ≟ j′
    ... | yes refl = ⊥-elim (<-irrefl refl (≤-trans (snd tf) le))
    ... | no _     = above iv j′ (≤-trans (take-top p) le)
    ce : ∀ j′ s′ → upd (who p) j (cellW s) j′ ≡ cellW s′ → upd (own p) s j s′ ≡ j′
    ce j′ s′ c with j ≟ j′
    ce j′ s′ refl | yes refl = upd-same (own p) s j
    ... | no ne with s ≟ s′
    ...   | yes refl = ⊥-elim (notlive (subst (λ z → who p z ≡ cellW s) (sym (cells iv j′ s c)) c))
    ...   | no ns    = cells iv j′ s′ c
    tm : ∀ j′ m → upd (who p) j (cellW s) j′ ≡ tempW m → (m , j′) ∈ temps p
    tm j′ m t with j ≟ j′
    tm j′ m () | yes refl
    ... | no _ = tmps iv j′ m t
    st : ∀ m j′ → (m , j′) ∈ temps p → upd (who p) j (cellW s) j′ ≡ tempW m
    st m j′ mem with j ≟ j′
    ... | yes refl = ⊥-elim (free-temp {p} (fst tf) (stack iv m j mem))
    ... | no _     = stack iv m j′ mem

died-inv : ∀ s p {p′} → Inv p → died s p ≡ just p′ → Inv p′
died-inv s p iv e with who p (own p s) ≟w cellW s
died-inv s p iv () | no _
died-inv s p iv refl | yes live = record { above = ab ; cells = ce ; tmps = tm ; stack = st ; desc = desc iv }
  where
    j = own p s
    ab : ∀ j′ → top p ≤ j′ → upd (who p) j freeW j′ ≡ freeW
    ab j′ le with j ≟ j′
    ... | yes _ = refl
    ... | no _  = above iv j′ le
    ce : ∀ j′ s′ → upd (who p) j freeW j′ ≡ cellW s′ → own p s′ ≡ j′
    ce j′ s′ c with j ≟ j′
    ce j′ s′ () | yes _
    ... | no _ = cells iv j′ s′ c
    tm : ∀ j′ m → upd (who p) j freeW j′ ≡ tempW m → (m , j′) ∈ temps p
    tm j′ m t with j ≟ j′
    tm j′ m () | yes _
    ... | no _ = tmps iv j′ m t
    st : ∀ m j′ → (m , j′) ∈ temps p → upd (who p) j freeW j′ ≡ tempW m
    st m j′ mem with j ≟ j′
    ... | yes refl with trans (sym live) (stack iv m j mem)
    ...   | ()
    st m j′ mem | no _ = stack iv m j′ mem

tborn-inv : ∀ p → Inv p → Inv (tborn p)
tborn-inv p iv = record { above = ab ; cells = ce ; tmps = tm ; stack = st ; desc = (≤-refl , desc iv) }
  where
    j  = fst (take p)
    tf = take-free p iv
    ab : ∀ j′ → snd (take p) ≤ j′ → upd (who p) j (tempW (tc p)) j′ ≡ freeW
    ab j′ le with j ≟ j′
    ... | yes refl = ⊥-elim (<-irrefl refl (≤-trans (snd tf) le))
    ... | no _     = above iv j′ (≤-trans (take-top p) le)
    ce : ∀ j′ s′ → upd (who p) j (tempW (tc p)) j′ ≡ cellW s′ → own p s′ ≡ j′
    ce j′ s′ c with j ≟ j′
    ce j′ s′ () | yes _
    ... | no _ = cells iv j′ s′ c
    tm : ∀ j′ m → upd (who p) j (tempW (tc p)) j′ ≡ tempW m → (m , j′) ∈ ((tc p , j) ∷ temps p)
    tm j′ m t with j ≟ j′
    tm j′ m refl | yes refl = here refl
    ... | no _ = there (tmps iv j′ m t)
    st : ∀ m j′ → (m , j′) ∈ ((tc p , j) ∷ temps p) → upd (who p) j (tempW (tc p)) j′ ≡ tempW m
    st m j′ (here refl) = upd-same (who p) j (tempW (tc p))
    st m j′ (there mem) with j ≟ j′
    ... | yes refl = ⊥-elim (free-temp {p} (fst tf) (stack iv m j mem))
    ... | no _     = stack iv m j′ mem

private
  tempW-inj : ∀ {a b} → tempW a ≡ tempW b → a ≡ b
  tempW-inj refl = refl

tdied-inv : ∀ p {p′} → Inv p → tdied p ≡ just p′ → Inv p′
tdied-inv p iv e with temps p in eq
tdied-inv p iv () | []
tdied-inv p iv refl | (m , j) ∷ ts = record { above = ab ; cells = ce ; tmps = tm ; stack = st ; desc = de }
  where
    tps : ∀ {x} → x ∈ temps p → x ∈ ((m , j) ∷ ts)
    tps mem = subst (_ ∈_) eq mem
    pst : ∀ {x} → x ∈ ((m , j) ∷ ts) → x ∈ temps p
    pst mem = subst (_ ∈_) (sym eq) mem
    dsc : Desc ((m , j) ∷ ts) (tc p)
    dsc = subst (λ z → Desc z (tc p)) eq (desc iv)
    ab : ∀ j′ → top p ≤ j′ → upd (who p) j freeW j′ ≡ freeW
    ab j′ le with j ≟ j′
    ... | yes _ = refl
    ... | no _  = above iv j′ le
    ce : ∀ j′ s′ → upd (who p) j freeW j′ ≡ cellW s′ → own p s′ ≡ j′
    ce j′ s′ c with j ≟ j′
    ce j′ s′ () | yes _
    ... | no _ = cells iv j′ s′ c
    tm : ∀ j′ m′ → upd (who p) j freeW j′ ≡ tempW m′ → (m′ , j′) ∈ ts
    tm j′ m′ t with j ≟ j′
    tm j′ m′ () | yes _
    ... | no ne with tps (tmps iv j′ m′ t)
    ...   | here refl = ⊥-elim (ne refl)
    ...   | there mem = mem
    st : ∀ m′ j′ → (m′ , j′) ∈ ts → upd (who p) j freeW j′ ≡ tempW m′
    st m′ j′ mem with j ≟ j′
    ... | yes refl with tempW-inj (trans (sym (stack iv m j (pst (here refl)))) (stack iv m′ j (pst (there mem))))
    ...   | refl = ⊥-elim (<-irrefl refl (desc-below mem (snd dsc)))
    st m′ j′ mem | no _ = stack iv m′ j′ (pst (there mem))
    de : Desc ts (tc p)
    de = desc-weaken (≤-trans (n≤1+n m) (fst dsc)) (snd dsc)

-- one size class's operations, from the run's events of that size
data Op : Set where
  birth death : ℕ → Op     -- a cell, by its serial
  tbirth tdeath : Op       -- a temporary (a frame), newest first

step : Op → Pool → Maybe Pool
step (birth s) p = born s p
step (death s) p = died s p
step tbirth    p = just (tborn p)
step tdeath    p = tdied p

-- the operations, in order: the allocator makes each step
data Steps : Pool → List Op → Pool → Set where
  done : ∀ {p} → Steps p [] p
  _⟫_  : ∀ {p p′ p″ o os} → step o p ≡ just p′ → Steps p′ os p″ → Steps p (o ∷ os) p″

step-inv : ∀ o p {p′} → Inv p → step o p ≡ just p′ → Inv p′
step-inv (birth s) p iv e    = born-inv s p iv e
step-inv (death s) p iv e    = died-inv s p iv e
step-inv tbirth    p iv refl = tborn-inv p iv
step-inv tdeath    p iv e    = tdied-inv p iv e

-- ★ the invariant holds all along
steps-inv : ∀ {p os p′} → Inv p → Steps p os p′ → Inv p′
steps-inv iv done         = iv
steps-inv iv (_⟫_ {p = p} {o = o} e st) = steps-inv (step-inv o p iv e) st

------------------------------------------------------------------------
-- 5. ★ THE CLAIMS.
------------------------------------------------------------------------

-- the map from live cells to blocks is injective: one block, one owner
live-injective : ∀ p {s s′} → Live p s → Live p s′ → own p s ≡ own p s′ → s ≡ s′
live-injective p {s} {s′} l l′ e = cellW-inj (trans (sym l) (subst (λ z → who p z ≡ cellW s′) (sym e) l′))

-- a live cell's block and a live temporary's are different blocks
cell-not-temp : ∀ p {s m j} → Inv p → Live p s → (m , j) ∈ temps p → own p s ≢ j
cell-not-temp p iv l mem refl with trans (sym l) (stack iv _ _ mem)
... | ()

-- ★ THE SPACE CLAIM: when the region grows, every block below the old top
-- holds a live cell or a live temporary, each its own (`who` is a function)
grows-only-when-full : ∀ p → Inv p → top p < snd (take p)
                     → ∀ j → j < top p → (Σ ℕ λ s → Live p s × own p s ≡ j) ⊎ (Σ ℕ λ m → (m , j) ∈ temps p)
grows-only-when-full p iv grows j lt with firstFree (who p) (top p) in eq
grows-only-when-full p iv grows j lt | just _ = ⊥-elim (<-irrefl refl grows)
... | nothing with who p j in wj
...   | freeW   = ⊥-elim (ff-nothing (who p) (top p) eq j lt wj)
...   | cellW s = inj₁ (s , subst (λ z → who p z ≡ cellW s) (sym (cells iv j s wj)) wj , cells iv j s wj)
...   | tempW m = inj₂ (m , tmps iv j m wj)

-- every block below the top has an owner
Full : Pool → Set
Full p = ∀ j → j < top p → who p j ≢ freeW

-- the top grows by one, at the old top, only when nothing was free
take-grow : ∀ p → top p < snd (take p)
          → fst (take p) ≡ top p × snd (take p) ≡ suc (top p) × (∀ j → j < top p → who p j ≢ freeW)
take-grow p lt with firstFree (who p) (top p) in eq
... | just _  = ⊥-elim (<-irrefl refl lt)
... | nothing = (refl , refl , ff-nothing (who p) (top p) eq)

take-same : ∀ p → snd (take p) ≡ top p ⊎ snd (take p) ≡ suc (top p)
take-same p with firstFree (who p) (top p)
... | just _  = inj₁ refl
... | nothing = inj₂ refl

upd-full : ∀ p {x} → x ≢ freeW → top p < snd (take p)
         → ∀ j → j < snd (take p) → upd (who p) (fst (take p)) x j ≢ freeW
upd-full p {x} nx lt j jl with take-grow p lt
... | (e₁ , e₂ , nf) with fst (take p) ≟ j
...   | yes _ = nx
...   | no ne with m≤n⇒m<n∨m≡n (≤-pred (subst (j <_) e₂ jl))
...     | inj₁ lt′  = nf j lt′
...     | inj₂ refl = ⊥-elim (ne e₁)

-- ★ a step that grows the region leaves it FULL: every block below the new
-- top has an owner (so as many things of this size are live at once)
grow-full : ∀ o p {p′} → step o p ≡ just p′ → top p < top p′ → Full p′
grow-full (birth s) p e lt with who p (own p s) ≟w cellW s
grow-full (birth s) p () lt | yes _
grow-full (birth s) p refl lt | no _ = upd-full p (λ ()) lt
grow-full (death s) p e lt with who p (own p s) ≟w cellW s
grow-full (death s) p refl lt | yes _ = ⊥-elim (<-irrefl refl lt)
grow-full (death s) p () lt | no _
grow-full tbirth p refl lt = upd-full p (λ ()) lt
grow-full tdeath p e lt with temps p
grow-full tdeath p () lt | []
grow-full tdeath p refl lt | _ ∷ _ = ⊥-elim (<-irrefl refl lt)

-- a step keeps the top, or grows it by one
step-top : ∀ o p {p′} → step o p ≡ just p′ → top p′ ≡ top p ⊎ top p′ ≡ suc (top p)
step-top (birth s) p e with who p (own p s) ≟w cellW s
step-top (birth s) p () | yes _
step-top (birth s) p refl | no _ = take-same p
step-top (death s) p e with who p (own p s) ≟w cellW s
step-top (death s) p refl | yes _ = inj₁ refl
step-top (death s) p () | no _
step-top tbirth p refl = take-same p
step-top tdeath p e with temps p
step-top tdeath p () | []
step-top tdeath p refl | _ ∷ _ = inj₁ refl

------------------------------------------------------------------------
-- 6. WHAT EACH STEP DOES TO WHO IS LIVE (for the link with the run).
------------------------------------------------------------------------

bornP : ℕ → Pool → Pool
bornP s p = pool (snd (take p)) (upd (who p) (fst (take p)) (cellW s)) (upd (own p) s (fst (take p))) (temps p) (tc p)

diedP : ℕ → Pool → Pool
diedP s p = pool (top p) (upd (who p) (own p s) freeW) (own p) (temps p) (tc p)

born-ok : ∀ s p → ¬ Live p s → born s p ≡ just (bornP s p)
born-ok s p nl with who p (own p s) ≟w cellW s
... | yes l = ⊥-elim (nl l)
... | no _  = refl

died-ok : ∀ s p → Live p s → died s p ≡ just (diedP s p)
died-ok s p l with who p (own p s) ≟w cellW s
... | yes _ = refl
... | no nl = ⊥-elim (nl l)

tdied-ok : ∀ p {m j ts} → temps p ≡ (m , j) ∷ ts → tdied p ≡ just (pool (top p) (upd (who p) j freeW) (own p) ts (tc p))
tdied-ok p eq with temps p
tdied-ok p refl | _ = refl

private
  cellW≢ : ∀ {s s′} → s ≢ s′ → cellW s ≢ cellW s′
  cellW≢ ne e = ne (cellW-inj e)

born-live : ∀ s p → Live (bornP s p) s
born-live s p rewrite upd-same (own p) s (fst (take p)) = upd-same (who p) (fst (take p)) (cellW s)

born-to : ∀ s p {s′} → s′ ≢ s → Live (bornP s p) s′ → Live p s′
born-to s p {s′} ne l with s ≟ s′
... | yes e = ⊥-elim (ne (sym e))
... | no _ with fst (take p) ≟ own p s′
...   | yes _ = ⊥-elim (cellW≢ (λ e → ne (sym e)) l)
...   | no _  = l

born-from : ∀ s p {s′} → Inv p → s′ ≢ s → Live p s′ → Live (bornP s p) s′
born-from s p {s′} iv ne l with s ≟ s′
... | yes e = ⊥-elim (ne (sym e))
... | no _ with fst (take p) ≟ own p s′
...   | yes e = ⊥-elim (free-cell′ (fst (take-free p iv)) (subst (λ z → who p z ≡ cellW s′) (sym e) l))
  where free-cell′ : ∀ {w} → w ≡ freeW → w ≡ cellW s′ → ⊥
        free-cell′ refl ()
...   | no _  = l

died-dead : ∀ s p → Live (diedP s p) s → ⊥
died-dead s p l with own p s ≟ own p s
... | yes _ with l
...   | ()
died-dead s p l | no ne = ne refl

died-to : ∀ s p {s′} → Live (diedP s p) s′ → Live p s′
died-to s p {s′} l with own p s ≟ own p s′
... | yes _ with l
...   | ()
died-to s p {s′} l | no _ = l

died-from : ∀ s p {s′} → Live p s → s′ ≢ s → Live p s′ → Live (diedP s p) s′
died-from s p {s′} ls ne l with own p s ≟ own p s′
... | yes e = ⊥-elim (ne (live-injective p l ls (sym e)))
... | no _  = l

tborn-to : ∀ p {s} → Live (tborn p) s → Live p s
tborn-to p {s} l with fst (take p) ≟ own p s
... | yes _ with l
...   | ()
tborn-to p {s} l | no _ = l

tborn-from : ∀ p {s} → Inv p → Live p s → Live (tborn p) s
tborn-from p {s} iv l with fst (take p) ≟ own p s
... | yes e = ⊥-elim (free-cell″ (fst (take-free p iv)) (subst (λ z → who p z ≡ cellW s) (sym e) l))
  where free-cell″ : ∀ {w} → w ≡ freeW → w ≡ cellW s → ⊥
        free-cell″ refl ()
... | no _  = l

tdied-to : ∀ p {j ts s} → Live (pool (top p) (upd (who p) j freeW) (own p) ts (tc p)) s → Live p s
tdied-to p {j} {s = s} l with j ≟ own p s
... | yes _ with l
...   | ()
tdied-to p {j} {s = s} l | no _ = l

tdied-from : ∀ p {m j ts s} → Inv p → temps p ≡ (m , j) ∷ ts → Live p s
           → Live (pool (top p) (upd (who p) j freeW) (own p) ts (tc p)) s
tdied-from p {m} {j} {s = s} iv eq l with j ≟ own p s
... | yes e with trans (sym (stack iv m j (subst ((m , j) ∈_) (sym eq) (here refl)))) (subst (λ z → who p z ≡ cellW s) (sym e) l)
...   | ()
tdied-from p iv eq l | no _ = l
