-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.LinCore.Alloc — plan 0.146 A17 (D430): ONE SIZE CLASS'S POOL.
--
-- A pool of size `k` (free lists per size, D422) numbers its blocks from 0;
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
-- size's peak (D430 part 2, decided: `Once.LinCore.Region`).
------------------------------------------------------------------------

{-# OPTIONS --guardedness #-}

open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (sym; trans; cong; cong₂; subst; _≢_)
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

private
  tempW-inj : ∀ {a b} → tempW a ≡ tempW b → a ≡ b
  tempW-inj refl = refl

  freeW≢cellW : ∀ {s} → freeW ≢ cellW s
  freeW≢cellW ()

  freeW≢tempW : ∀ {m} → freeW ≢ tempW m
  freeW≢tempW ()

  cellW≢tempW : ∀ {s m} → cellW s ≢ tempW m
  cellW≢tempW ()

  ≟c : ∀ {a b} → Dec (a ≡ b) → Dec (cellW a ≡ cellW b)
  ≟c (yes refl) = yes refl
  ≟c (no ne)    = no λ e → ne (cellW-inj e)

  ≟t : ∀ {a b} → Dec (a ≡ b) → Dec (tempW a ≡ tempW b)
  ≟t (yes refl) = yes refl
  ≟t (no ne)    = no λ e → ne (tempW-inj e)

_≟w_ : (a b : Who) → Dec (a ≡ b)
freeW   ≟w freeW   = yes refl
freeW   ≟w cellW _ = no λ ()
freeW   ≟w tempW _ = no λ ()
cellW _ ≟w freeW   = no λ ()
cellW a ≟w cellW b = ≟c (a ≟ b)
cellW _ ≟w tempW _ = no λ ()
tempW _ ≟w freeW   = no λ ()
tempW _ ≟w cellW _ = no λ ()
tempW a ≟w tempW b = ≟t (a ≟ b)

record Pool : Set where
  constructor pool
  field
    top   : ℕ                -- the region holds blocks 0 … top-1
    who   : ℕ → Who          -- each block's owner
    own   : ℕ → ℕ            -- each cell's block, by serial (meaningful while live)
    temps : List (ℕ × ℕ)     -- live temporaries: (name, block), newest first
    tc    : ℕ                -- the next temporary's name
open Pool

empty : Pool
empty = pool 0 (λ _ → freeW) (λ _ → 0) [] 0

-- a cell is live when its block says so
Live : Pool → ℕ → Set
Live p s = who p (own p s) ≡ cellW s

-- a point update
upd-pick : ∀ {P X : Set} → Dec P → X → X → X
upd-pick (yes _) x y = x
upd-pick (no _)  x y = y

upd : ∀ {X : Set} → (ℕ → X) → ℕ → X → ℕ → X
upd f j x j′ = upd-pick (j ≟ j′) x (f j′)

-- ★ the one case split on a point update: at the point, or elsewhere
upd-elim : ∀ {X : Set} (P : X → Set) (f : ℕ → X) j x j′ → (j ≡ j′ → P x) → (j ≢ j′ → P (f j′)) → P (upd f j x j′)
upd-elim P f j x j′ at else = by (j ≟ j′)
  where
    by : (d : Dec (j ≡ j′)) → P (upd-pick d x (f j′))
    by (yes e) = at e
    by (no ne) = else ne

upd-same : ∀ {X : Set} (f : ℕ → X) j x → upd f j x j ≡ x
upd-same f j x = upd-elim (_≡ x) f j x j (λ _ → refl) (λ ne → ⊥-elim (ne refl))

upd-other : ∀ {X : Set} (f : ℕ → X) {j j′} x → j ≢ j′ → upd f j x j′ ≡ f j′
upd-other f {j} {j′} x ne = upd-elim (_≡ f j′) f j x j′ (λ e → ⊥-elim (ne e)) (λ _ → refl)

------------------------------------------------------------------------
-- 2. TAKING A BLOCK: the lowest free one below the top, else the top.
------------------------------------------------------------------------

ff-here : ∀ {P : Set} → ℕ → Dec P → Maybe ℕ
ff-here n (yes _) = just n
ff-here n (no _)  = nothing

ff-step : (ℕ → Who) → ℕ → Maybe ℕ → Maybe ℕ
ff-step w n (just j) = just j
ff-step w n nothing  = ff-here n (w n ≟w freeW)

firstFree : (ℕ → Who) → ℕ → Maybe ℕ
firstFree w zero    = nothing
firstFree w (suc n) = ff-step w n (firstFree w n)

ff-just : ∀ w n {j} → firstFree w n ≡ just j → j < n × w j ≡ freeW
ff-just w (suc n) {j} e = go (firstFree w n) refl e
  where
    at-n : ∀ {i} → (d : Dec (w n ≡ freeW)) → ff-here n d ≡ just i → i < suc n × w i ≡ freeW
    at-n (yes f) refl = (≤-refl , f)
    at-n (no _)  ()
    go : ∀ m → firstFree w n ≡ m → ff-step w n m ≡ just j → j < suc n × w j ≡ freeW
    go (just j′) eq refl = (≤-trans (fst (ff-just w n eq)) (n≤1+n n) , snd (ff-just w n eq))
    go nothing   eq e′   = at-n (w n ≟w freeW) e′

ff-nothing : ∀ w n → firstFree w n ≡ nothing → ∀ j → j < n → w j ≢ freeW
ff-nothing w (suc n) e j lt = go (firstFree w n) refl e
  where
    go : ∀ m → firstFree w n ≡ m → ff-step w n m ≡ nothing → w j ≢ freeW
    go (just _) eq ()
    go nothing  eq e′ = at-n (w n ≟w freeW) e′
      where
        by : j < n ⊎ j ≡ n → w n ≢ freeW → w j ≢ freeW
        by (inj₁ lt′) nf = ff-nothing w n eq j lt′
        by (inj₂ q)   nf = subst (λ z → w z ≢ freeW) (sym q) nf
        at-n : (d : Dec (w n ≡ freeW)) → ff-here n d ≡ nothing → w j ≢ freeW
        at-n (yes _) ()
        at-n (no nf) _ = by (m≤n⇒m<n∨m≡n (≤-pred lt)) nf

-- the block taken, and the new top
take-at : Pool → Maybe ℕ → ℕ × ℕ
take-at p (just j) = (j , top p)
take-at p nothing  = (top p , suc (top p))

take : Pool → ℕ × ℕ
take p = take-at p (firstFree (who p) (top p))

------------------------------------------------------------------------
-- 3. THE STEPS: a cell born or freed, a temporary born or freed. A step the
-- allocator cannot make (a live cell born again, a dead one freed, no
-- temporary to free) is `nothing`: a legal run never asks for one.
------------------------------------------------------------------------

bornP : ℕ → Pool → Pool
bornP s p = pool (snd (take p)) (upd (who p) (fst (take p)) (cellW s)) (upd (own p) s (fst (take p))) (temps p) (tc p)

diedP : ℕ → Pool → Pool
diedP s p = pool (top p) (upd (who p) (own p s) freeW) (own p) (temps p) (tc p)

born-at : ∀ s p → Dec (Live p s) → Maybe Pool
born-at s p (yes _) = nothing
born-at s p (no _)  = just (bornP s p)

born : ℕ → Pool → Maybe Pool
born s p = born-at s p (who p (own p s) ≟w cellW s)

died-at : ∀ s p → Dec (Live p s) → Maybe Pool
died-at s p (yes _) = just (diedP s p)
died-at s p (no _)  = nothing

died : ℕ → Pool → Maybe Pool
died s p = died-at s p (who p (own p s) ≟w cellW s)

tborn : Pool → Pool
tborn p = pool (snd (take p)) (upd (who p) (fst (take p)) (tempW (tc p))) (own p)
               ((tc p , fst (take p)) ∷ temps p) (suc (tc p))

tdied-at : Pool → List (ℕ × ℕ) → Maybe Pool
tdied-at p []             = nothing
tdied-at p ((m , j) ∷ ts) = just (pool (top p) (upd (who p) j freeW) (own p) ts (tc p))

tdied : Pool → Maybe Pool
tdied p = tdied-at p (temps p)

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
open Inv

inv-empty : Inv empty
inv-empty = record { above = λ _ _ → refl ; cells = λ _ _ () ; tmps = λ _ _ () ; stack = λ _ _ () ; desc = tt }

-- the block taken was free, and below the new top
take-free : ∀ p → Inv p → who p (fst (take p)) ≡ freeW × fst (take p) < snd (take p)
take-free p iv = go (firstFree (who p) (top p)) refl
  where
    go : ∀ m → firstFree (who p) (top p) ≡ m → who p (fst (take-at p m)) ≡ freeW × fst (take-at p m) < snd (take-at p m)
    go (just j) eq = (snd (ff-just (who p) (top p) eq) , fst (ff-just (who p) (top p) eq))
    go nothing  eq = (above iv (top p) ≤-refl , ≤-refl)

take-top : ∀ p → top p ≤ snd (take p)
take-top p = go (firstFree (who p) (top p))
  where
    go : ∀ m → top p ≤ snd (take-at p m)
    go (just _) = ≤-refl
    go nothing  = n≤1+n _

private
  -- a free block is no cell's and no temporary's
  free-cell : ∀ {p j s} → who p j ≡ freeW → who p j ≡ cellW s → ⊥
  free-cell f c = freeW≢cellW (trans (sym f) c)
  free-temp : ∀ {p j m} → who p j ≡ freeW → who p j ≡ tempW m → ⊥
  free-temp f t = freeW≢tempW (trans (sym f) t)

  -- a temporary below the head is not on the head's block
  drop-head : ∀ {m′ j′ m j : ℕ} {ts : List (ℕ × ℕ)} → j ≢ j′ → (m′ , j′) ∈ ((m , j) ∷ ts) → (m′ , j′) ∈ ts
  drop-head ne (here refl) = ⊥-elim (ne refl)
  drop-head ne (there mem) = mem

bornP-inv : ∀ s p → Inv p → ¬ Live p s → Inv (bornP s p)
bornP-inv s p iv notlive = record { above = ab ; cells = ce ; tmps = tm ; stack = st ; desc = desc iv }
  where
    j  = fst (take p)
    tf = take-free p iv
    ab : ∀ j′ → snd (take p) ≤ j′ → upd (who p) j (cellW s) j′ ≡ freeW
    ab j′ le = upd-elim (_≡ freeW) (who p) j (cellW s) j′
                 (λ e → ⊥-elim (<-irrefl e (≤-trans (snd tf) le)))
                 (λ _ → above iv j′ (≤-trans (take-top p) le))
    ce-own : ∀ j′ s′ → who p j′ ≡ cellW s′ → upd (own p) s j s′ ≡ j′
    ce-own j′ s′ c = upd-elim (_≡ j′) (own p) s j s′
                       (λ es → let c₀ = subst (λ z → who p j′ ≡ cellW z) (sym es) c in
                               ⊥-elim (notlive (subst (λ z → who p z ≡ cellW s) (sym (cells iv j′ s c₀)) c₀)))
                       (λ _ → cells iv j′ s′ c)
    ce : ∀ j′ s′ → upd (who p) j (cellW s) j′ ≡ cellW s′ → upd (own p) s j s′ ≡ j′
    ce j′ s′ = upd-elim (λ w → w ≡ cellW s′ → upd (own p) s j s′ ≡ j′) (who p) j (cellW s) j′
                 (λ e c → trans (subst (λ z → upd (own p) s j z ≡ j) (cellW-inj c) (upd-same (own p) s j)) e)
                 (λ _ c → ce-own j′ s′ c)
    tm : ∀ j′ m → upd (who p) j (cellW s) j′ ≡ tempW m → (m , j′) ∈ temps p
    tm j′ m = upd-elim (λ w → w ≡ tempW m → (m , j′) ∈ temps p) (who p) j (cellW s) j′
                (λ _ ()) (λ _ t → tmps iv j′ m t)
    st : ∀ m j′ → (m , j′) ∈ temps p → upd (who p) j (cellW s) j′ ≡ tempW m
    st m j′ mem = upd-elim (_≡ tempW m) (who p) j (cellW s) j′
                    (λ e → ⊥-elim (free-temp {p} (fst tf) (stack iv m j (subst (λ z → (m , z) ∈ temps p) (sym e) mem))))
                    (λ _ → stack iv m j′ mem)

born-inv : ∀ s p {p′} → Inv p → born s p ≡ just p′ → Inv p′
born-inv s p iv e = go (who p (own p s) ≟w cellW s) e
  where
    go : ∀ {p′} (d : Dec (Live p s)) → born-at s p d ≡ just p′ → Inv p′
    go (yes _) ()
    go (no nl) refl = bornP-inv s p iv nl

diedP-inv : ∀ s p → Inv p → Live p s → Inv (diedP s p)
diedP-inv s p iv live = record { above = ab ; cells = ce ; tmps = tm ; stack = st ; desc = desc iv }
  where
    j = own p s
    ab : ∀ j′ → top p ≤ j′ → upd (who p) j freeW j′ ≡ freeW
    ab j′ le = upd-elim (_≡ freeW) (who p) j freeW j′ (λ _ → refl) (λ _ → above iv j′ le)
    ce : ∀ j′ s′ → upd (who p) j freeW j′ ≡ cellW s′ → own p s′ ≡ j′
    ce j′ s′ = upd-elim (λ w → w ≡ cellW s′ → own p s′ ≡ j′) (who p) j freeW j′
                 (λ _ ()) (λ _ c → cells iv j′ s′ c)
    tm : ∀ j′ m → upd (who p) j freeW j′ ≡ tempW m → (m , j′) ∈ temps p
    tm j′ m = upd-elim (λ w → w ≡ tempW m → (m , j′) ∈ temps p) (who p) j freeW j′
                (λ _ ()) (λ _ t → tmps iv j′ m t)
    st : ∀ m j′ → (m , j′) ∈ temps p → upd (who p) j freeW j′ ≡ tempW m
    st m j′ mem = upd-elim (_≡ tempW m) (who p) j freeW j′
                    (λ e → ⊥-elim (cellW≢tempW (trans (sym live) (stack iv m j (subst (λ z → (m , z) ∈ temps p) (sym e) mem)))))
                    (λ _ → stack iv m j′ mem)

died-inv : ∀ s p {p′} → Inv p → died s p ≡ just p′ → Inv p′
died-inv s p iv e = go (who p (own p s) ≟w cellW s) e
  where
    go : ∀ {p′} (d : Dec (Live p s)) → died-at s p d ≡ just p′ → Inv p′
    go (yes l) refl = diedP-inv s p iv l
    go (no _)  ()

tborn-inv : ∀ p → Inv p → Inv (tborn p)
tborn-inv p iv = record { above = ab ; cells = ce ; tmps = tm ; stack = st ; desc = (≤-refl , desc iv) }
  where
    j  = fst (take p)
    tf = take-free p iv
    ab : ∀ j′ → snd (take p) ≤ j′ → upd (who p) j (tempW (tc p)) j′ ≡ freeW
    ab j′ le = upd-elim (_≡ freeW) (who p) j (tempW (tc p)) j′
                 (λ e → ⊥-elim (<-irrefl e (≤-trans (snd tf) le)))
                 (λ _ → above iv j′ (≤-trans (take-top p) le))
    ce : ∀ j′ s′ → upd (who p) j (tempW (tc p)) j′ ≡ cellW s′ → own p s′ ≡ j′
    ce j′ s′ = upd-elim (λ w → w ≡ cellW s′ → own p s′ ≡ j′) (who p) j (tempW (tc p)) j′
                 (λ _ ()) (λ _ c → cells iv j′ s′ c)
    tm : ∀ j′ m → upd (who p) j (tempW (tc p)) j′ ≡ tempW m → (m , j′) ∈ ((tc p , j) ∷ temps p)
    tm j′ m = upd-elim (λ w → w ≡ tempW m → (m , j′) ∈ ((tc p , j) ∷ temps p)) (who p) j (tempW (tc p)) j′
                (λ e t → here (cong₂ _,_ (sym (tempW-inj t)) (sym e)))
                (λ _ t → there (tmps iv j′ m t))
    st : ∀ m j′ → (m , j′) ∈ ((tc p , j) ∷ temps p) → upd (who p) j (tempW (tc p)) j′ ≡ tempW m
    st m j′ (here refl) = upd-same (who p) j (tempW (tc p))
    st m j′ (there mem) = upd-elim (_≡ tempW m) (who p) j (tempW (tc p)) j′
                            (λ e → ⊥-elim (free-temp {p} (fst tf) (stack iv m j (subst (λ z → (m , z) ∈ temps p) (sym e) mem))))
                            (λ _ → stack iv m j′ mem)

tdiedP-inv : ∀ p {m j ts} → Inv p → temps p ≡ (m , j) ∷ ts → Inv (pool (top p) (upd (who p) j freeW) (own p) ts (tc p))
tdiedP-inv p {m} {j} {ts} iv eq = record { above = ab ; cells = ce ; tmps = tm ; stack = st ; desc = de }
  where
    tps : ∀ {x} → x ∈ temps p → x ∈ ((m , j) ∷ ts)
    tps mem = subst (_ ∈_) eq mem
    pst : ∀ {x} → x ∈ ((m , j) ∷ ts) → x ∈ temps p
    pst mem = subst (_ ∈_) (sym eq) mem
    dsc : Desc ((m , j) ∷ ts) (tc p)
    dsc = subst (λ z → Desc z (tc p)) eq (desc iv)
    ab : ∀ j′ → top p ≤ j′ → upd (who p) j freeW j′ ≡ freeW
    ab j′ le = upd-elim (_≡ freeW) (who p) j freeW j′ (λ _ → refl) (λ _ → above iv j′ le)
    ce : ∀ j′ s′ → upd (who p) j freeW j′ ≡ cellW s′ → own p s′ ≡ j′
    ce j′ s′ = upd-elim (λ w → w ≡ cellW s′ → own p s′ ≡ j′) (who p) j freeW j′
                 (λ _ ()) (λ _ c → cells iv j′ s′ c)
    tm : ∀ j′ m′ → upd (who p) j freeW j′ ≡ tempW m′ → (m′ , j′) ∈ ts
    tm j′ m′ = upd-elim (λ w → w ≡ tempW m′ → (m′ , j′) ∈ ts) (who p) j freeW j′
                 (λ _ ()) (λ ne t → drop-head ne (tps (tmps iv j′ m′ t)))
    st : ∀ m′ j′ → (m′ , j′) ∈ ts → upd (who p) j freeW j′ ≡ tempW m′
    st m′ j′ mem = upd-elim (_≡ tempW m′) (who p) j freeW j′
                     (λ e → let mem₀ = subst (λ z → (m′ , z) ∈ ts) (sym e) mem in
                            ⊥-elim (<-irrefl (sym (tempW-inj (trans (sym (stack iv m j (pst (here refl)))) (stack iv m′ j (pst (there mem₀))))))
                                             (desc-below mem₀ (snd dsc))))
                     (λ _ → stack iv m′ j′ (pst (there mem)))
    de : Desc ts (tc p)
    de = desc-weaken (≤-trans (n≤1+n m) (fst dsc)) (snd dsc)

tdied-inv : ∀ p {p′} → Inv p → tdied p ≡ just p′ → Inv p′
tdied-inv p iv e = go (temps p) refl e
  where
    go : ∀ {p′} ts₀ → temps p ≡ ts₀ → tdied-at p ts₀ ≡ just p′ → Inv p′
    go []             eq ()
    go ((m , j) ∷ ts) eq refl = tdiedP-inv p iv eq

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
cell-not-temp p iv l mem refl = cellW≢tempW (trans (sym l) (stack iv _ _ mem))

-- ★ THE SPACE CLAIM: when the region grows, every block below the old top
-- holds a live cell or a live temporary, each its own (`who` is a function)
grows-only-when-full : ∀ p → Inv p → top p < snd (take p)
                     → ∀ j → j < top p → (Σ ℕ λ s → Live p s × own p s ≡ j) ⊎ (Σ ℕ λ m → (m , j) ∈ temps p)
grows-only-when-full p iv grows j lt = go (firstFree (who p) (top p)) refl grows
  where
    Owned : Set
    Owned = (Σ ℕ λ s → Live p s × own p s ≡ j) ⊎ (Σ ℕ λ m → (m , j) ∈ temps p)
    by : firstFree (who p) (top p) ≡ nothing → ∀ w → who p j ≡ w → Owned
    by eq freeW     wj = ⊥-elim (ff-nothing (who p) (top p) eq j lt wj)
    by eq (cellW s) wj = inj₁ (s , subst (λ z → who p z ≡ cellW s) (sym (cells iv j s wj)) wj , cells iv j s wj)
    by eq (tempW m) wj = inj₂ (m , tmps iv j m wj)
    go : ∀ mj → firstFree (who p) (top p) ≡ mj → top p < snd (take-at p mj) → Owned
    go (just _) eq g = ⊥-elim (<-irrefl refl g)
    go nothing  eq g = by eq (who p j) refl

-- every block below the top has an owner
Full : Pool → Set
Full p = ∀ j → j < top p → who p j ≢ freeW

-- the top grows by one, at the old top, only when nothing was free
take-grow : ∀ p → top p < snd (take p)
          → fst (take p) ≡ top p × snd (take p) ≡ suc (top p) × (∀ j → j < top p → who p j ≢ freeW)
take-grow p lt = go (firstFree (who p) (top p)) refl lt
  where
    go : ∀ mj → firstFree (who p) (top p) ≡ mj → top p < snd (take-at p mj)
       → fst (take-at p mj) ≡ top p × snd (take-at p mj) ≡ suc (top p) × (∀ j → j < top p → who p j ≢ freeW)
    go (just _) eq g = ⊥-elim (<-irrefl refl g)
    go nothing  eq g = (refl , refl , ff-nothing (who p) (top p) eq)

take-same : ∀ p → snd (take p) ≡ top p ⊎ snd (take p) ≡ suc (top p)
take-same p = go (firstFree (who p) (top p))
  where
    go : ∀ mj → snd (take-at p mj) ≡ top p ⊎ snd (take-at p mj) ≡ suc (top p)
    go (just _) = inj₁ refl
    go nothing  = inj₂ refl

upd-full : ∀ p {x} → x ≢ freeW → top p < snd (take p)
         → ∀ j → j < snd (take p) → upd (who p) (fst (take p)) x j ≢ freeW
upd-full p {x} nx lt j jl =
  upd-elim (_≢ freeW) (who p) (fst (take p)) x j (λ _ → nx)
    (λ ne → by ne (m≤n⇒m<n∨m≡n (≤-pred (subst (j <_) (fst (snd tg)) jl))))
  where
    tg = take-grow p lt
    by : fst (take p) ≢ j → j < top p ⊎ j ≡ top p → who p j ≢ freeW
    by ne (inj₁ lt′) = snd (snd tg) j lt′
    by ne (inj₂ q)   = ⊥-elim (ne (trans (fst tg) (sym q)))

-- ★ a step that grows the region leaves it FULL: every block below the new
-- top has an owner (so as many things of this size are live at once)
grow-full : ∀ o p {p′} → step o p ≡ just p′ → top p < top p′ → Full p′
grow-full (birth s) p e lt = go (who p (own p s) ≟w cellW s) e lt
  where
    go : ∀ {p′} (d : Dec (Live p s)) → born-at s p d ≡ just p′ → top p < top p′ → Full p′
    go (yes _) () lt
    go (no _)  refl lt = upd-full p (λ ()) lt
grow-full (death s) p e lt = go (who p (own p s) ≟w cellW s) e lt
  where
    go : ∀ {p′} (d : Dec (Live p s)) → died-at s p d ≡ just p′ → top p < top p′ → Full p′
    go (yes _) refl lt = ⊥-elim (<-irrefl refl lt)
    go (no _)  () lt
grow-full tbirth p refl lt = upd-full p (λ ()) lt
grow-full tdeath p e lt = go (temps p) e lt
  where
    go : ∀ {p′} ts₀ → tdied-at p ts₀ ≡ just p′ → top p < top p′ → Full p′
    go []            () lt
    go ((_ , _) ∷ _) refl lt = ⊥-elim (<-irrefl refl lt)

-- a step keeps the top, or grows it by one
step-top : ∀ o p {p′} → step o p ≡ just p′ → top p′ ≡ top p ⊎ top p′ ≡ suc (top p)
step-top (birth s) p e = go (who p (own p s) ≟w cellW s) e
  where
    go : ∀ {p′} (d : Dec (Live p s)) → born-at s p d ≡ just p′ → top p′ ≡ top p ⊎ top p′ ≡ suc (top p)
    go (yes _) ()
    go (no _)  refl = take-same p
step-top (death s) p e = go (who p (own p s) ≟w cellW s) e
  where
    go : ∀ {p′} (d : Dec (Live p s)) → died-at s p d ≡ just p′ → top p′ ≡ top p ⊎ top p′ ≡ suc (top p)
    go (yes _) refl = inj₁ refl
    go (no _)  ()
step-top tbirth p refl = take-same p
step-top tdeath p e = go (temps p) e
  where
    go : ∀ {p′} ts₀ → tdied-at p ts₀ ≡ just p′ → top p′ ≡ top p ⊎ top p′ ≡ suc (top p)
    go []            ()
    go ((_ , _) ∷ _) refl = inj₁ refl

------------------------------------------------------------------------
-- 6. WHAT EACH STEP DOES TO WHO IS LIVE (for the link with the run).
------------------------------------------------------------------------

born-ok : ∀ s p → ¬ Live p s → born s p ≡ just (bornP s p)
born-ok s p nl = go (who p (own p s) ≟w cellW s)
  where
    go : (d : Dec (Live p s)) → born-at s p d ≡ just (bornP s p)
    go (yes l) = ⊥-elim (nl l)
    go (no _)  = refl

died-ok : ∀ s p → Live p s → died s p ≡ just (diedP s p)
died-ok s p l = go (who p (own p s) ≟w cellW s)
  where
    go : (d : Dec (Live p s)) → died-at s p d ≡ just (diedP s p)
    go (yes _)  = refl
    go (no nl)  = ⊥-elim (nl l)

tdied-ok : ∀ p {m j ts} → temps p ≡ (m , j) ∷ ts → tdied p ≡ just (pool (top p) (upd (who p) j freeW) (own p) ts (tc p))
tdied-ok p eq = cong (tdied-at p) eq

private
  cellW≢ : ∀ {s s′} → s ≢ s′ → cellW s ≢ cellW s′
  cellW≢ ne e = ne (cellW-inj e)

born-live : ∀ s p → Live (bornP s p) s
born-live s p =
  subst (λ z → upd (who p) (fst (take p)) (cellW s) z ≡ cellW s) (sym (upd-same (own p) s (fst (take p))))
        (upd-same (who p) (fst (take p)) (cellW s))

born-to : ∀ s p {s′} → s′ ≢ s → Live (bornP s p) s′ → Live p s′
born-to s p {s′} ne l =
  upd-elim (λ w → w ≡ cellW s′ → who p (own p s′) ≡ cellW s′) (who p) (fst (take p)) (cellW s) (own p s′)
    (λ _ c → ⊥-elim (cellW≢ (λ e → ne (sym e)) c)) (λ _ c → c)
    (subst (λ z → upd (who p) (fst (take p)) (cellW s) z ≡ cellW s′) (upd-other (own p) {s} {s′} (fst (take p)) (λ e → ne (sym e))) l)

born-from : ∀ s p {s′} → Inv p → s′ ≢ s → Live p s′ → Live (bornP s p) s′
born-from s p {s′} iv ne l =
  subst (λ z → upd (who p) (fst (take p)) (cellW s) z ≡ cellW s′) (sym (upd-other (own p) {s} {s′} (fst (take p)) (λ e → ne (sym e))))
    (upd-elim (_≡ cellW s′) (who p) (fst (take p)) (cellW s) (own p s′)
       (λ e → ⊥-elim (free-cell {p} (fst (take-free p iv)) (subst (λ z → who p z ≡ cellW s′) (sym e) l)))
       (λ _ → l))

died-dead : ∀ s p → Live (diedP s p) s → ⊥
died-dead s p l = freeW≢cellW (trans (sym (upd-same (who p) (own p s) freeW)) l)

died-to : ∀ s p {s′} → Live (diedP s p) s′ → Live p s′
died-to s p {s′} l =
  upd-elim (λ w → w ≡ cellW s′ → who p (own p s′) ≡ cellW s′) (who p) (own p s) freeW (own p s′) (λ _ ()) (λ _ c → c) l

died-from : ∀ s p {s′} → Live p s → s′ ≢ s → Live p s′ → Live (diedP s p) s′
died-from s p {s′} ls ne l =
  upd-elim (_≡ cellW s′) (who p) (own p s) freeW (own p s′) (λ e → ⊥-elim (ne (live-injective p l ls (sym e)))) (λ _ → l)

tborn-to : ∀ p {s} → Live (tborn p) s → Live p s
tborn-to p {s} l =
  upd-elim (λ w → w ≡ cellW s → who p (own p s) ≡ cellW s) (who p) (fst (take p)) (tempW (tc p)) (own p s) (λ _ ()) (λ _ c → c) l

tborn-from : ∀ p {s} → Inv p → Live p s → Live (tborn p) s
tborn-from p {s} iv l =
  upd-elim (_≡ cellW s) (who p) (fst (take p)) (tempW (tc p)) (own p s)
    (λ e → ⊥-elim (free-cell {p} (fst (take-free p iv)) (subst (λ z → who p z ≡ cellW s) (sym e) l)))
    (λ _ → l)

tdied-to : ∀ p {j ts s} → Live (pool (top p) (upd (who p) j freeW) (own p) ts (tc p)) s → Live p s
tdied-to p {j} {s = s} l =
  upd-elim (λ w → w ≡ cellW s → who p (own p s) ≡ cellW s) (who p) j freeW (own p s) (λ _ ()) (λ _ c → c) l

tdied-from : ∀ p {m j ts s} → Inv p → temps p ≡ (m , j) ∷ ts → Live p s
           → Live (pool (top p) (upd (who p) j freeW) (own p) ts (tc p)) s
tdied-from p {m} {j} {s = s} iv eq l =
  upd-elim (_≡ cellW s) (who p) j freeW (own p s)
    (λ e → ⊥-elim (cellW≢tempW (trans (sym (subst (λ z → who p z ≡ cellW s) (sym e) l))
                                      (stack iv m j (subst ((m , j) ∈_) (sym eq) (here refl))))))
    (λ _ → l)
