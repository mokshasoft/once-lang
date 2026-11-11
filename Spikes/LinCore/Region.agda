-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- LinCore.Region — plan 0.146 A17 (D411 part 2, decided): ONE REGION,
-- SHARED BY EVERY SIZE.
--
-- The Host supplies one region; the compiler does not split it between
-- sizes (it cannot know how, so a split would be arbitrary). The region is
-- used from the bottom up (`wtop` words in use). Each size has its own pool
-- (`LinCore.Alloc`: a free list, lowest free block first); a pool that must
-- grow takes the next `k` words at the top of the region (`place`). Block `j`
-- of size `k` is the words `[addr k j, addr k j + k)`. Nothing is stored at
-- run time that the compiler knows: a block's size is its type's (D404).
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

{-# OPTIONS --safe --guardedness #-}

module LinCore.Region where

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
open import Relation.Nullary using (yes; no)
import LinCore.Alloc as A
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
open Region public

empty : Region
empty = region (λ _ → A.empty) 0 (λ _ _ → 0)

-- how many blocks size `k` has
tops : Region → ℕ → ℕ
tops r k = A.top (pools r k)

-- size `k`'s pool is now `p′`; if it grew, its new block takes the next `k`
-- words at the top of the region
place : ℕ → Pool → Region → Region
place k p′ r with A.top p′ ≟ tops r k
... | yes _ = region (upd (pools r) k p′) (wtop r) (addr r)
... | no _  = region (upd (pools r) k p′) (wtop r + k) (upd (addr r) k (upd (addr r k) (tops r k) (wtop r)))

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
gstep-inv {k} {o} {r} e with A.step o (pools r k) in eq
gstep-inv refl | just p′ = (p′ , refl , refl)
gstep-inv ()   | nothing

place-pools : ∀ k p′ r → pools (place k p′ r) ≡ upd (pools r) k p′
place-pools k p′ r with A.top p′ ≟ tops r k
... | yes _ = refl
... | no _  = refl

-- a point update, seen at a point
upd-view : ∀ {X : Set} (f : ℕ → X) k x k′ → (k ≡ k′ × upd f k x k′ ≡ x) ⊎ (k ≢ k′ × upd f k x k′ ≡ f k′)
upd-view f k x k′ with k ≟ k′
... | yes e = inj₁ (e , refl)
... | no ne = inj₂ (ne , refl)

-- a step never shrinks a pool
tops-le : ∀ k o r {p′} → A.step o (pools r k) ≡ just p′ → ∀ k′ → tops r k′ ≤ A.top (upd (pools r) k p′ k′)
tops-le k o r e k′ with upd-view (pools r) k _ k′
... | inj₂ (_ , q) = subst (tops r k′ ≤_) (sym (cong A.top q)) ≤-refl
... | inj₁ (refl , q) with A.step-top o (pools r k) e
...   | inj₁ s = subst (tops r k ≤_) (sym (trans (cong A.top q) s)) ≤-refl
...   | inj₂ g = subst (tops r k ≤_) (sym (trans (cong A.top q) g)) (n≤1+n _)

------------------------------------------------------------------------
-- 2. ★ DISJOINT: the invariant.
------------------------------------------------------------------------

record RInv (r : Region) : Set where
  field
    pinv   : ∀ k → A.Inv (pools r k)
    inside : ∀ k j → j < tops r k → addr r k j + k ≤ wtop r
    apart  : ∀ k j k′ j′ → j < tops r k → j′ < tops r k′ → (k ≡ k′ → j ≢ j′)
           → addr r k j + k ≤ addr r k′ j′ ⊎ addr r k′ j′ + k′ ≤ addr r k j
open RInv public

rinv-empty : RInv empty
rinv-empty = record { pinv = λ _ → A.inv-empty ; inside = λ _ _ () ; apart = λ _ _ _ _ () }

-- rewriting the two addresses of an ordering
subst₂≤ : ∀ {x x′ y y′ c} → x ≡ x′ → y ≡ y′ → x + c ≤ y → x′ + c ≤ y′
subst₂≤ refl refl le = le

rinv-place : ∀ k o r {p′} → RInv r → A.step o (pools r k) ≡ just p′ → RInv (place k p′ r)
rinv-place k o r {p′} iv e with A.top p′ ≟ tops r k
... | yes same = record { pinv = pv ; inside = ins ; apart = ap }
  where
    tp : ∀ k′ → A.top (upd (pools r) k p′ k′) ≡ tops r k′
    tp k′ with upd-view (pools r) k p′ k′
    ... | inj₁ (refl , q) = trans (cong A.top q) same
    ... | inj₂ (_ , q)    = cong A.top q
    pv : ∀ k′ → A.Inv (upd (pools r) k p′ k′)
    pv k′ with upd-view (pools r) k p′ k′
    ... | inj₁ (refl , q) = subst A.Inv (sym q) (A.step-inv o (pools r k) (pinv iv k) e)
    ... | inj₂ (_ , q)    = subst A.Inv (sym q) (pinv iv k′)
    ins : ∀ k′ j → j < A.top (upd (pools r) k p′ k′) → addr r k′ j + k′ ≤ wtop r
    ins k′ j lt = inside iv k′ j (subst (j <_) (tp k′) lt)
    ap : ∀ k₁ j₁ k₂ j₂ → j₁ < A.top (upd (pools r) k p′ k₁) → j₂ < A.top (upd (pools r) k p′ k₂)
       → (k₁ ≡ k₂ → j₁ ≢ j₂) → addr r k₁ j₁ + k₁ ≤ addr r k₂ j₂ ⊎ addr r k₂ j₂ + k₂ ≤ addr r k₁ j₁
    ap k₁ j₁ k₂ j₂ l₁ l₂ ne = apart iv k₁ j₁ k₂ j₂ (subst (j₁ <_) (tp k₁) l₁) (subst (j₂ <_) (tp k₂) l₂) ne
... | no grew = record { pinv = pv ; inside = ins ; apart = ap }
  where
    t₀ = tops r k
    w  = wtop r
    a′ = upd (addr r) k (upd (addr r k) t₀ w)
    up : A.top p′ ≡ suc t₀
    up with A.step-top o (pools r k) e
    ... | inj₁ s = ⊥-elim (grew s)
    ... | inj₂ g = g
    pv : ∀ k′ → A.Inv (upd (pools r) k p′ k′)
    pv k′ with upd-view (pools r) k p′ k′
    ... | inj₁ (refl , q) = subst A.Inv (sym q) (A.step-inv o (pools r k) (pinv iv k) e)
    ... | inj₂ (_ , q)    = subst A.Inv (sym q) (pinv iv k′)
    a-new : a′ k t₀ ≡ w
    a-new = trans (cong (λ f → f t₀) (upd-same (addr r) k _)) (upd-same (addr r k) t₀ w)
    a-old : ∀ k′ j → (k ≡ k′ → j ≢ t₀) → a′ k′ j ≡ addr r k′ j
    a-old k′ j ne with upd-view (addr r) k (upd (addr r k) t₀ w) k′
    ... | inj₁ (refl , q) = trans (cong (λ f → f j) q) (upd-other (addr r k) w (λ x → ne refl (sym x)))
    ... | inj₂ (_ , q)    = cong (λ f → f j) q
    -- a block below the new tops is the new one, or an old one
    classify : ∀ k′ j → j < A.top (upd (pools r) k p′ k′)
             → (k ≡ k′ × j ≡ t₀) ⊎ (j < tops r k′ × (k ≡ k′ → j ≢ t₀))
    classify k′ j lt with upd-view (pools r) k p′ k′
    ... | inj₂ (ne , q) = inj₂ (subst (j <_) (cong A.top q) lt , λ x → ⊥-elim (ne x))
    ... | inj₁ (refl , q) with m≤n⇒m<n∨m≡n (≤-pred (subst (j <_) (trans (cong A.top q) up) lt))
    ...   | inj₁ lt′  = inj₂ (lt′ , λ _ x → <-irrefl x lt′)
    ...   | inj₂ refl = inj₁ (refl , refl)
    ins : ∀ k′ j → j < A.top (upd (pools r) k p′ k′) → a′ k′ j + k′ ≤ w + k
    ins k′ j lt with classify k′ j lt
    ... | inj₁ (refl , refl) = subst (λ z → z + k ≤ w + k) (sym a-new) ≤-refl
    ... | inj₂ (lt′ , ne)    = subst (λ z → z + k′ ≤ w + k) (sym (a-old k′ j ne)) (≤-trans (inside iv k′ j lt′) (m≤m+n w k))
    ap : ∀ k₁ j₁ k₂ j₂ → j₁ < A.top (upd (pools r) k p′ k₁) → j₂ < A.top (upd (pools r) k p′ k₂)
       → (k₁ ≡ k₂ → j₁ ≢ j₂) → a′ k₁ j₁ + k₁ ≤ a′ k₂ j₂ ⊎ a′ k₂ j₂ + k₂ ≤ a′ k₁ j₁
    ap k₁ j₁ k₂ j₂ l₁ l₂ ne with classify k₁ j₁ l₁ | classify k₂ j₂ l₂
    ... | inj₁ (refl , refl) | inj₁ (refl , refl) = ⊥-elim (ne refl refl)
    ... | inj₁ (refl , refl) | inj₂ (lt₂ , n₂) =
      inj₂ (subst₂≤ (sym (a-old k₂ j₂ n₂)) (sym a-new) (inside iv k₂ j₂ lt₂))
    ... | inj₂ (lt₁ , n₁) | inj₁ (refl , refl) =
      inj₁ (subst₂≤ (sym (a-old k₁ j₁ n₁)) (sym a-new) (inside iv k₁ j₁ lt₁))
    ... | inj₂ (lt₁ , n₁) | inj₂ (lt₂ , n₂) with apart iv k₁ j₁ k₂ j₂ lt₁ lt₂ ne
    ...   | inj₁ le = inj₁ (subst₂≤ (sym (a-old k₁ j₁ n₁)) (sym (a-old k₂ j₂ n₂)) le)
    ...   | inj₂ le = inj₂ (subst₂≤ (sym (a-old k₂ j₂ n₂)) (sym (a-old k₁ j₁ n₁)) le)

-- ★ along every run of the region, its blocks stay apart, and below the top
rinv : ∀ {r gs r′} → RInv r → GSteps r gs r′ → RInv r′
rinv iv done = iv
rinv {r} iv (_⟫_ {g = (k , o)} e st) with gstep-inv {k} {o} {r} e
... | (p′ , ep , refl) = rinv (rinv-place k o r iv ep) st

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
space-place ks k o r {p′} m e sp with A.top p′ ≟ tops r k
... | yes _ = ≤-trans sp (sum-mono (λ k′ → *-monoʳ-≤ k′ (tops-le k o r e k′)) ks)
... | no grew = ≤-trans (+-mono-≤ sp ≤-refl)
                  (sum-grow m (λ k′ → *-monoʳ-≤ k′ (tops-le k o r e k′)) at-k)
  where
    up : A.top (upd (pools r) k p′ k) ≡ suc (tops r k)
    up with A.step-top o (pools r k) e
    ... | inj₁ s = ⊥-elim (grew s)
    ... | inj₂ g = trans (cong A.top (upd-same (pools r) k p′)) g
    at-k : k * tops r k + k ≤ k * A.top (upd (pools r) k p′ k)
    at-k = subst (k * tops r k + k ≤_) (sym (trans (cong (k *_) up) (*-suc k (tops r k))))
                 (subst (_≤ k + k * tops r k) (+-comm k (k * tops r k)) ≤-refl)

-- every operation is on one of the program's sizes
Sizes : List ℕ → List (ℕ × Op) → Set
Sizes ks []             = Data.Unit.⊤
  where import Data.Unit
Sizes ks ((k , _) ∷ gs) = k ∈ ks × Sizes ks gs

-- ★ along every run on the program's sizes, the words in use are at most
-- `Σ k · topₖ`
space : ∀ ks {r gs r′} → Sizes ks gs → wtop r ≤ Words ks r → GSteps r gs r′ → wtop r′ ≤ Words ks r′
space ks _ sp done = sp
space ks {r} (m , sz) sp (_⟫_ {g = (k , o)} e st) with gstep-inv {k} {o} {r} e
... | (p′ , ep , refl) = space ks sz (space-place ks k o r m ep sp) st

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
one-step k {(k₀ , o)} {r} e with gstep-inv {k₀} {o} {r} e
... | (p′ , ep , refl) rewrite place-pools k₀ p′ r with upd-view (pools r) k₀ p′ k
...   | inj₂ (_ , q) = inj₁ (cong A.top q)
...   | inj₁ (refl , q) with A.step-top o (pools r k₀) ep
...     | inj₁ s = inj₁ (trans (cong A.top q) s)
...     | inj₂ g = inj₂ (subst A.Full (sym q) (A.grow-full o (pools r k₀) ep (subst (tops r k₀ <_) (sym g) ≤-refl)))

-- one more step: the peak so far still stands, or the pool grew and is the
-- new peak
peak-step : ∀ k {gs₀ r₁ g r₂} → GSteps empty gs₀ r₁ → gstep g r₁ ≡ just r₂
          → Peak gs₀ k (tops r₁ k) → Peak (gs₀ ++ g ∷ []) k (tops r₂ k)
peak-step k {gs₀} {r₁} {g} {r₂} st₀ e pk with one-step k {g} {r₁} {r₂} e
peak-step k {gs₀} {r₁} {g} {r₂} st₀ e pk | inj₂ full =
  inj₂ (gs₀ ++ g ∷ [] , [] , r₂ , sym (++-identityʳ _) , gsteps-++ st₀ (e ⟫ done) , refl , full)
peak-step k {gs₀} {r₁} {g} {r₂} st₀ e (inj₁ z) | inj₁ same = inj₁ (trans same z)
peak-step k {gs₀} {r₁} {g} {r₂} st₀ e (inj₂ (gs₁ , gs₂ , r₃ , eq , st₃ , t₃ , f₃)) | inj₁ same =
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
grun (g ∷ gs) r with gstep g r
... | just r′ = grun gs r′
... | nothing = nothing
