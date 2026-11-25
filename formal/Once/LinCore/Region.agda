-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.LinCore.Region — plan 0.146 A17 (D430 part 2, decided): ONE REGION,
-- SHARED BY EVERY SIZE.
--
-- The Host supplies one region; the compiler does not split it between
-- sizes (it cannot know how, so a split would be arbitrary). The region is
-- used from the bottom up (`wtop` words in use). Each size has its own pool
-- (`Once.LinCore.Alloc`: a free list, lowest free block first); a pool that must
-- grow takes the next `k` words at the top of the region (`place`). Block `j`
-- of size `k` is the words `[addr k j, addr k j + k)`. Nothing is stored at
-- run time that the compiler knows: a block's size is its type's (D423).
--
--   * ★ DISJOINT: blocks below their pools' tops never overlap, whatever
--     their sizes, and all lie below `wtop` (`RInv`, `rinv`);
--   * ★ THE SPACE CLAIM: `wtop ≤ Σ k · topₖ` over the program's sizes
--     (`space`), and each `topₖ` is a PEAK: at some moment of the run, every
--     one of size `k`'s blocks below it had an owner (a live cell or a live
--     temporary, each its own: `Alloc.Inv`), so that many things of size
--     `k` were live at once (`peak`). So a run runs out of the region only
--     when `Σ k · peakₖ` does not fit it.
--
-- No allocator that never moves a block can promise more for every program
-- (Robson 1974: some request sequence makes any of them use more than the
-- live data); moving blocks is a collector, which GOAL.md excludes.
------------------------------------------------------------------------

{-# OPTIONS --guardedness #-}

module Once.LinCore.Region where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (sym; trans; cong; subst; _≢_)
open import Agda.Builtin.Sigma using (Σ; _,_; fst; snd)
open import Data.Product using (_×_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥-elim)
open import Data.Maybe using (Maybe; just; nothing; map)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _≤_; _<_; _≟_)
open import Data.Nat.Properties
  using (≤-refl; ≤-trans; ≤-pred; <-irrefl; m≤n⇒m<n∨m≡n; m≤m+n; +-mono-≤; +-assoc; +-comm; *-suc; n≤1+n; *-monoʳ-≤)
open import Data.List using (List; []; _∷_; _++_) renaming (map to lmap)
open import Data.Nat.ListAction using (sum)
open import Data.List.Properties using (++-identityʳ; ++-assoc)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Relation.Nullary using (Dec; yes; no; ¬_)
import Data.Sum
import Once.LinCore.Alloc as A
open A using (Pool; Op; upd; upd-same; upd-other)

------------------------------------------------------------------------
-- 1. THE REGION: a pool per size, one top, the blocks' addresses.
------------------------------------------------------------------------

record Region : Set where
  constructor region
  field
    pools : ℕ → Pool          -- each size's pool
    wtop  : ℕ                 -- the words in use: `[0, wtop)`
    addr  : ℕ → ℕ → ℕ         -- block `j` of size `k` starts at `addr k j`
open Region

empty : Region
empty = region (λ _ → A.empty) 0 (λ _ _ → 0)

-- how many blocks size `k` has
tops : Region → ℕ → ℕ
tops r k = A.Pool.top (pools r k)

-- size `k`'s pool is now `p′`; if it grew, its new block takes the next `k`
-- words at the top of the region
place-at : ∀ k p′ r → Dec (A.Pool.top p′ ≡ tops r k) → Region
place-at k p′ r (yes _) = region (upd (pools r) k p′) (wtop r) (addr r)
place-at k p′ r (no _)  = region (upd (pools r) k p′) (wtop r + k) (upd (addr r) k (upd (addr r k) (tops r k) (wtop r)))

place : ℕ → Pool → Region → Region
place k p′ r = place-at k p′ r (A.Pool.top p′ ≟ tops r k)

-- an operation on size `k`: its pool's step, then the region's
gstep : ℕ × Op → Region → Maybe Region
gstep (k , o) r = map (λ p′ → place k p′ r) (A.step o (pools r k))

data GSteps : Region → List (ℕ × Op) → Region → Set where
  done : ∀ {r} → GSteps r [] r
  _⟫_  : ∀ {r r′ r″ g gs} → gstep g r ≡ just r′ → GSteps r′ gs r″ → GSteps r (g ∷ gs) r″

gsteps-++ : ∀ {r r′ r″ gs gs′} → GSteps r gs r′ → GSteps r′ gs′ r″ → GSteps r (gs ++ gs′) r″
gsteps-++ done       st = st
gsteps-++ (e ⟫ st₁)  st = e ⟫ gsteps-++ st₁ st

gstep-ok : ∀ {k o r p′} → A.step o (pools r k) ≡ just p′ → gstep (k , o) r ≡ just (place k p′ r)
gstep-ok {k} {o} {r} e = cong (map (λ p′ → place k p′ r)) e

gstep-inv : ∀ {k o r r′} → gstep (k , o) r ≡ just r′ → Σ Pool λ p′ → A.step o (pools r k) ≡ just p′ × r′ ≡ place k p′ r
gstep-inv {k} {o} {r} e = go (A.step o (pools r k)) refl e
  where
    go : ∀ {r′} m → A.step o (pools r k) ≡ m → map (λ p′ → place k p′ r) m ≡ just r′
       → Σ Pool λ p′ → A.step o (pools r k) ≡ just p′ × r′ ≡ place k p′ r
    go (just p′) eq refl = (p′ , eq , refl)
    go nothing   eq ()

place-pools : ∀ k p′ r → pools (place k p′ r) ≡ upd (pools r) k p′
place-pools k p′ r = go (A.Pool.top p′ ≟ tops r k)
  where
    go : (d : Dec (A.Pool.top p′ ≡ tops r k)) → pools (place-at k p′ r d) ≡ upd (pools r) k p′
    go (yes _) = refl
    go (no _)  = refl

-- a point update, seen at a point
upd-view : ∀ {X : Set} (f : ℕ → X) k x k′ → (k ≡ k′ × upd f k x k′ ≡ x) ⊎ (k ≢ k′ × upd f k x k′ ≡ f k′)
upd-view f k x k′ = A.upd-elim (λ v → (k ≡ k′ × v ≡ x) ⊎ (k ≢ k′ × v ≡ f k′)) f k x k′ (λ e → inj₁ (e , refl)) (λ ne → inj₂ (ne , refl))

-- a step that changed the top grew it by one
grew-top : ∀ o p {p′} → A.step o p ≡ just p′ → ¬ (A.Pool.top p′ ≡ A.Pool.top p) → A.Pool.top p′ ≡ suc (A.Pool.top p)
grew-top o p e grew = by (A.step-top o p e)
  where
    by : _ ⊎ _ → _
    by (inj₁ s) = ⊥-elim (grew s)
    by (inj₂ g) = g

-- a step never shrinks a pool
tops-le : ∀ k o r {p′} → A.step o (pools r k) ≡ just p′ → ∀ k′ → tops r k′ ≤ A.Pool.top (upd (pools r) k p′ k′)
tops-le k o r {p′} e k′ =
  A.upd-elim (λ v → tops r k′ ≤ A.Pool.top v) (pools r) k p′ k′
    (λ eq → subst (λ z → tops r z ≤ A.Pool.top p′) eq (by (A.step-top o (pools r k) e)))
    (λ _ → ≤-refl)
  where
    by : A.Pool.top p′ ≡ tops r k ⊎ A.Pool.top p′ ≡ suc (tops r k) → tops r k ≤ A.Pool.top p′
    by (inj₁ s) = subst (tops r k ≤_) (sym s) ≤-refl
    by (inj₂ g) = subst (tops r k ≤_) (sym g) (n≤1+n _)

------------------------------------------------------------------------
-- 2. ★ DISJOINT: the invariant.
------------------------------------------------------------------------

record RInv (r : Region) : Set where
  field
    pinv   : ∀ k → A.Inv (pools r k)
    inside : ∀ k j → j < tops r k → addr r k j + k ≤ wtop r
    apart  : ∀ k j k′ j′ → j < tops r k → j′ < tops r k′ → (k ≡ k′ → j ≢ j′)
           → addr r k j + k ≤ addr r k′ j′ ⊎ addr r k′ j′ + k′ ≤ addr r k j
open RInv

rinv-empty : RInv empty
rinv-empty = record { pinv = λ _ → A.inv-empty ; inside = λ _ _ () ; apart = λ _ _ _ _ () }

-- rewriting the two addresses of an ordering
subst₂≤ : ∀ {x x′ y y′ c} → x ≡ x′ → y ≡ y′ → x + c ≤ y → x′ + c ≤ y′
subst₂≤ refl refl le = le

-- the pools after one step: each holds the invariant
step-pinv : ∀ k o r {p′} → RInv r → A.step o (pools r k) ≡ just p′ → ∀ k′ → A.Inv (upd (pools r) k p′ k′)
step-pinv k o r {p′} iv e k′ =
  A.upd-elim A.Inv (pools r) k p′ k′ (λ _ → A.step-inv o (pools r k) (pinv iv k) e) (λ _ → pinv iv k′)

rinv-same : ∀ k o r {p′} → RInv r → A.step o (pools r k) ≡ just p′ → A.Pool.top p′ ≡ tops r k
          → RInv (region (upd (pools r) k p′) (wtop r) (addr r))
rinv-same k o r {p′} iv e same = record { pinv = pv ; inside = ins ; apart = ap }
  where
    tp : ∀ k′ → A.Pool.top (upd (pools r) k p′ k′) ≡ tops r k′
    tp k′ = A.upd-elim (λ v → A.Pool.top v ≡ tops r k′) (pools r) k p′ k′
              (λ eq → subst (λ z → A.Pool.top p′ ≡ tops r z) eq same) (λ _ → refl)
    pv : ∀ k′ → A.Inv (upd (pools r) k p′ k′)
    pv = step-pinv k o r iv e
    ins : ∀ k′ j → j < A.Pool.top (upd (pools r) k p′ k′) → addr r k′ j + k′ ≤ wtop r
    ins k′ j lt = inside iv k′ j (subst (j <_) (tp k′) lt)
    ap : ∀ k₁ j₁ k₂ j₂ → j₁ < A.Pool.top (upd (pools r) k p′ k₁) → j₂ < A.Pool.top (upd (pools r) k p′ k₂)
       → (k₁ ≡ k₂ → j₁ ≢ j₂) → addr r k₁ j₁ + k₁ ≤ addr r k₂ j₂ ⊎ addr r k₂ j₂ + k₂ ≤ addr r k₁ j₁
    ap k₁ j₁ k₂ j₂ l₁ l₂ ne = apart iv k₁ j₁ k₂ j₂ (subst (j₁ <_) (tp k₁) l₁) (subst (j₂ <_) (tp k₂) l₂) ne

rinv-grew : ∀ k o r {p′} → RInv r → A.step o (pools r k) ≡ just p′ → ¬ (A.Pool.top p′ ≡ tops r k)
          → RInv (region (upd (pools r) k p′) (wtop r + k) (upd (addr r) k (upd (addr r k) (tops r k) (wtop r))))
rinv-grew k o r {p′} iv e grew = record { pinv = pv ; inside = ins ; apart = ap }
  where
    t₀ = tops r k
    w  = wtop r
    a′ = upd (addr r) k (upd (addr r k) t₀ w)
    up : A.Pool.top p′ ≡ suc t₀
    up = grew-top o (pools r k) e grew
    pv : ∀ k′ → A.Inv (upd (pools r) k p′ k′)
    pv = step-pinv k o r iv e
    a-new : a′ k t₀ ≡ w
    a-new = trans (cong (λ f → f t₀) (upd-same (addr r) k _)) (upd-same (addr r k) t₀ w)
    a-old : ∀ k′ j → (k ≡ k′ → j ≢ t₀) → a′ k′ j ≡ addr r k′ j
    a-old k′ j ne = A.upd-elim (λ f → f j ≡ addr r k′ j) (addr r) k (upd (addr r k) t₀ w) k′
                      (λ eq → trans (upd-other (addr r k) w (λ x → ne eq (sym x))) (cong (λ z → addr r z j) eq))
                      (λ _ → refl)
    at-k : ∀ {k′ j} → k ≡ k′ → j < t₀ ⊎ j ≡ t₀ → (k ≡ k′ × j ≡ t₀) ⊎ (j < tops r k′ × (k ≡ k′ → j ≢ t₀))
    at-k eq (inj₁ lt′) = inj₂ (subst (λ z → _ < tops r z) eq lt′ , λ _ x → <-irrefl x lt′)
    at-k eq (inj₂ q)   = inj₁ (eq , q)
    -- a block below the new tops is the new one, or an old one
    classify : ∀ k′ j → j < A.Pool.top (upd (pools r) k p′ k′)
             → (k ≡ k′ × j ≡ t₀) ⊎ (j < tops r k′ × (k ≡ k′ → j ≢ t₀))
    classify k′ j = A.upd-elim (λ v → j < A.Pool.top v → (k ≡ k′ × j ≡ t₀) ⊎ (j < tops r k′ × (k ≡ k′ → j ≢ t₀))) (pools r) k p′ k′
                      (λ eq lt → at-k eq (m≤n⇒m<n∨m≡n (≤-pred (subst (j <_) up lt))))
                      (λ ne lt → inj₂ (lt , λ x → ⊥-elim (ne x)))
    ins-c : ∀ k′ j → (k ≡ k′ × j ≡ t₀) ⊎ (j < tops r k′ × (k ≡ k′ → j ≢ t₀)) → a′ k′ j + k′ ≤ w + k
    ins-c .k .t₀ (inj₁ (refl , refl)) = subst (λ z → z + k ≤ w + k) (sym a-new) ≤-refl
    ins-c k′ j   (inj₂ (lt′ , ne))    = subst (λ z → z + k′ ≤ w + k) (sym (a-old k′ j ne)) (≤-trans (inside iv k′ j lt′) (m≤m+n w k))
    ins : ∀ k′ j → j < A.Pool.top (upd (pools r) k p′ k′) → a′ k′ j + k′ ≤ w + k
    ins k′ j lt = ins-c k′ j (classify k′ j lt)
    ap-c : ∀ k₁ j₁ k₂ j₂ → (k₁ ≡ k₂ → j₁ ≢ j₂)
         → (k ≡ k₁ × j₁ ≡ t₀) ⊎ (j₁ < tops r k₁ × (k ≡ k₁ → j₁ ≢ t₀))
         → (k ≡ k₂ × j₂ ≡ t₀) ⊎ (j₂ < tops r k₂ × (k ≡ k₂ → j₂ ≢ t₀))
         → a′ k₁ j₁ + k₁ ≤ a′ k₂ j₂ ⊎ a′ k₂ j₂ + k₂ ≤ a′ k₁ j₁
    ap-c .k .t₀ .k .t₀ ne (inj₁ (refl , refl)) (inj₁ (refl , refl)) = ⊥-elim (ne refl refl)
    ap-c .k .t₀ k₂ j₂ ne (inj₁ (refl , refl)) (inj₂ (lt₂ , n₂)) =
      inj₂ (subst₂≤ (sym (a-old k₂ j₂ n₂)) (sym a-new) (inside iv k₂ j₂ lt₂))
    ap-c k₁ j₁ .k .t₀ ne (inj₂ (lt₁ , n₁)) (inj₁ (refl , refl)) =
      inj₁ (subst₂≤ (sym (a-old k₁ j₁ n₁)) (sym a-new) (inside iv k₁ j₁ lt₁))
    ap-c k₁ j₁ k₂ j₂ ne (inj₂ (lt₁ , n₁)) (inj₂ (lt₂ , n₂)) =
      Data.Sum.map (subst₂≤ (sym (a-old k₁ j₁ n₁)) (sym (a-old k₂ j₂ n₂)))
                   (subst₂≤ (sym (a-old k₂ j₂ n₂)) (sym (a-old k₁ j₁ n₁)))
                   (apart iv k₁ j₁ k₂ j₂ lt₁ lt₂ ne)
    ap : ∀ k₁ j₁ k₂ j₂ → j₁ < A.Pool.top (upd (pools r) k p′ k₁) → j₂ < A.Pool.top (upd (pools r) k p′ k₂)
       → (k₁ ≡ k₂ → j₁ ≢ j₂) → a′ k₁ j₁ + k₁ ≤ a′ k₂ j₂ ⊎ a′ k₂ j₂ + k₂ ≤ a′ k₁ j₁
    ap k₁ j₁ k₂ j₂ l₁ l₂ ne = ap-c k₁ j₁ k₂ j₂ ne (classify k₁ j₁ l₁) (classify k₂ j₂ l₂)

rinv-place : ∀ k o r {p′} → RInv r → A.step o (pools r k) ≡ just p′ → RInv (place k p′ r)
rinv-place k o r {p′} iv e = go (A.Pool.top p′ ≟ tops r k)
  where
    go : (d : Dec (A.Pool.top p′ ≡ tops r k)) → RInv (place-at k p′ r d)
    go (yes same) = rinv-same k o r iv e same
    go (no grew)  = rinv-grew k o r iv e grew

-- ★ along every run of the region, its blocks stay apart, and below the top
rinv : ∀ {r gs r′} → RInv r → GSteps r gs r′ → RInv r′
rinv iv done = iv
rinv {r} iv (_⟫_ {g = (k , o)} e st) =
  let (p′ , ep , q) = gstep-inv {k} {o} {r} e
  in rinv (subst RInv (sym q) (rinv-place k o r iv ep)) st

------------------------------------------------------------------------
-- 3. ★ THE SPACE CLAIM: the words in use are at most `Σ k · topₖ`.
------------------------------------------------------------------------

Words : List ℕ → Region → ℕ
Words ks r = sum (lmap (λ k → k * tops r k) ks)

sum-mono : ∀ {f g : ℕ → ℕ} → (∀ k → f k ≤ g k) → ∀ ks → sum (lmap f ks) ≤ sum (lmap g ks)
sum-mono le []       = ≤-refl
sum-mono le (k ∷ ks) = +-mono-≤ (le k) (sum-mono le ks)

sum-grow : ∀ {f g : ℕ → ℕ} {k₀ ks} → k₀ ∈ ks → (∀ k → f k ≤ g k) → f k₀ + k₀ ≤ g k₀
         → sum (lmap f ks) + k₀ ≤ sum (lmap g ks)
sum-grow {f} {g} {k₀} {k ∷ ks} (here refl) le l₀ =
  subst (_≤ g k + sum (lmap g ks)) eq (+-mono-≤ l₀ (sum-mono le ks))
  where
    S = sum (lmap f ks)
    eq : f k + k + S ≡ f k + S + k
    eq = trans (+-assoc (f k) k S) (trans (cong (f k +_) (+-comm k S)) (sym (+-assoc (f k) S k)))
sum-grow {f} {g} {k₀} {k ∷ ks} (there m) le l₀ =
  subst (_≤ g k + sum (lmap g ks)) (sym (+-assoc (f k) _ k₀)) (+-mono-≤ (le k) (sum-grow m le l₀))

space-place : ∀ ks k o r {p′} → k ∈ ks → A.step o (pools r k) ≡ just p′
            → wtop r ≤ Words ks r → wtop (place k p′ r) ≤ Words ks (place k p′ r)
space-place ks k o r {p′} m e sp = go (A.Pool.top p′ ≟ tops r k)
  where
    up : ¬ (A.Pool.top p′ ≡ tops r k) → A.Pool.top (upd (pools r) k p′ k) ≡ suc (tops r k)
    up grew = trans (cong A.Pool.top (upd-same (pools r) k p′)) (grew-top o (pools r k) e grew)
    at-k : ¬ (A.Pool.top p′ ≡ tops r k) → k * tops r k + k ≤ k * A.Pool.top (upd (pools r) k p′ k)
    at-k grew = subst (k * tops r k + k ≤_) (sym (trans (cong (k *_) (up grew)) (*-suc k (tops r k))))
                      (subst (_≤ k + k * tops r k) (+-comm k (k * tops r k)) ≤-refl)
    go : (d : Dec (A.Pool.top p′ ≡ tops r k)) → wtop (place-at k p′ r d) ≤ Words ks (place-at k p′ r d)
    go (yes _)   = ≤-trans sp (sum-mono (λ k′ → *-monoʳ-≤ k′ (tops-le k o r e k′)) ks)
    go (no grew) = ≤-trans (+-mono-≤ sp ≤-refl)
                     (sum-grow m (λ k′ → *-monoʳ-≤ k′ (tops-le k o r e k′)) (at-k grew))

-- every operation is on one of the program's sizes
Sizes : List ℕ → List (ℕ × Op) → Set
Sizes ks []             = Data.Unit.⊤
  where import Data.Unit
Sizes ks ((k , _) ∷ gs) = k ∈ ks × Sizes ks gs

-- ★ along every run on the program's sizes, the words in use are at most
-- `Σ k · topₖ`
space : ∀ ks {r gs r′} → Sizes ks gs → wtop r ≤ Words ks r → GSteps r gs r′ → wtop r′ ≤ Words ks r′
space ks _ sp done = sp
space ks {r} (m , sz) sp (_⟫_ {g = (k , o)} e st) =
  let (p′ , ep , q) = gstep-inv {k} {o} {r} e
  in space ks sz (subst (λ z → wtop z ≤ Words ks z) (sym q) (space-place ks k o r m ep sp)) st

------------------------------------------------------------------------
-- 4. ★ EACH TOP IS A PEAK: at some moment of the run, size `k`'s pool was
-- as large as it is now, and FULL (every block below its top owned: as many
-- things of size `k` live at once).
------------------------------------------------------------------------

Peak : List (ℕ × Op) → ℕ → ℕ → Set
Peak gs k n = n ≡ 0 ⊎ Σ (List (ℕ × Op)) λ gs₁ → Σ (List (ℕ × Op)) λ gs₂ → Σ Region λ r₁ →
              gs ≡ gs₁ ++ gs₂ × GSteps empty gs₁ r₁ × tops r₁ k ≡ n × A.Full (pools r₁ k)

-- what one step does to size `k`'s pool: nothing to its top, or it grew and
-- is full
one-step : ∀ k {g r r′} → gstep g r ≡ just r′ → tops r′ k ≡ tops r k ⊎ A.Full (pools r′ k)
one-step k {(k₀ , o)} {r} e =
  let (p′ , ep , q) = gstep-inv {k₀} {o} {r} e
  in subst (λ z → tops z k ≡ tops r k ⊎ A.Full (pools z k)) (sym q) (at-place p′ ep)
  where
    at-place : ∀ p′ → A.step o (pools r k₀) ≡ just p′ → tops (place k₀ p′ r) k ≡ tops r k ⊎ A.Full (pools (place k₀ p′ r) k)
    at-place p′ ep =
      subst (λ ps → A.Pool.top (ps k) ≡ tops r k ⊎ A.Full (ps k)) (sym (place-pools k₀ p′ r))
        (A.upd-elim (λ v → A.Pool.top v ≡ tops r k ⊎ A.Full v) (pools r) k₀ p′ k
           (λ eq → by eq (A.step-top o (pools r k₀) ep)) (λ _ → inj₁ refl))
      where
        by : k₀ ≡ k → A.Pool.top p′ ≡ tops r k₀ ⊎ A.Pool.top p′ ≡ suc (tops r k₀) → A.Pool.top p′ ≡ tops r k ⊎ A.Full p′
        by eq (inj₁ s) = inj₁ (trans s (cong (tops r) eq))
        by eq (inj₂ g) = inj₂ (A.grow-full o (pools r k₀) ep (subst (tops r k₀ <_) (sym g) ≤-refl))

-- one more step: the peak so far still stands, or the pool grew and is the
-- new peak
peak-step : ∀ k {gs₀ r₁ g r₂} → GSteps empty gs₀ r₁ → gstep g r₁ ≡ just r₂
          → Peak gs₀ k (tops r₁ k) → Peak (gs₀ ++ g ∷ []) k (tops r₂ k)
peak-step k {gs₀} {r₁} {g} {r₂} st₀ e pk = by (one-step k {g} {r₁} {r₂} e) pk
  where
    by : tops r₂ k ≡ tops r₁ k ⊎ A.Full (pools r₂ k) → Peak gs₀ k (tops r₁ k) → Peak (gs₀ ++ g ∷ []) k (tops r₂ k)
    by (inj₂ full) _ =
      inj₂ (gs₀ ++ g ∷ [] , [] , r₂ , sym (++-identityʳ _) , gsteps-++ st₀ (e ⟫ done) , refl , full)
    by (inj₁ same) (inj₁ z) = inj₁ (trans same z)
    by (inj₁ same) (inj₂ (gs₁ , gs₂ , r₃ , eq , st₃ , t₃ , f₃)) =
      inj₂ (gs₁ , gs₂ ++ g ∷ [] , r₃ , trans (cong (_++ g ∷ []) eq) (++-assoc gs₁ gs₂ (g ∷ [])) , st₃ , trans t₃ (sym same) , f₃)

peak-go : ∀ k {gs₀ r₁ gs r} → GSteps empty gs₀ r₁ → Peak gs₀ k (tops r₁ k) → GSteps r₁ gs r
        → Peak (gs₀ ++ gs) k (tops r k)
peak-go k {gs₀} st₀ pk done = subst (λ z → Peak z k _) (sym (++-identityʳ gs₀)) pk
peak-go k {gs₀} {r₁} {g ∷ gs} st₀ pk (e ⟫ st) =
  subst (λ z → Peak z k _) (++-assoc gs₀ (g ∷ []) gs)
        (peak-go k (gsteps-++ st₀ (e ⟫ done)) (peak-step k st₀ e pk) st)

-- ★ from an empty region: every size's top is a peak of the run
peak : ∀ {gs r} → GSteps empty gs r → ∀ k → Peak gs k (tops r k)
peak st k = peak-go k done (inj₁ refl) st

------------------------------------------------------------------------
-- 5. Running the region on a list of operations (for examples).
------------------------------------------------------------------------

grun : List (ℕ × Op) → Region → Maybe Region
grun []       r = just r
grun (g ∷ gs) r = at (gstep g r)
  where
    at : Maybe Region → Maybe Region
    at (just r′) = grun gs r′
    at nothing   = nothing
