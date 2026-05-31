------------------------------------------------------------------------
-- Once.CCC.Machine.IR.MuSize
--
-- A structural size measure on μ-values, for well-founded recursion in
-- the Cata machinery (Plan 0.27, Option B — replacing {-# TERMINATING #-}).
--
-- μ-size is defined via the (total) catamorphism sem-cata, so it needs no
-- TERMINATING pragma here. The key lemma `μ-size-unfold` exposes the
-- recurrence  μ-size x = suc (Σ child sizes),  from which the decrease
-- `child < parent` follows — the well-foundedness witness the Cata
-- recursion threads.
------------------------------------------------------------------------

module Once.CCC.Machine.IR.MuSize where

open import Data.Nat using (ℕ; zero; suc; _<_; _≤_; s≤s; z≤n)
  renaming (_+_ to _+ℕ_)
open import Data.Nat.Properties using (≤-refl; ≤-trans; <-trans; n≤1+n; n<1+n;
  m≤m+n; m≤n+m; ≤-<-trans)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

open import Once.Type using (Functor; K; Id; _⊕_; _⊗_)
open import Once.Functor.Translate using (WellFormedF)
open import Once.Semantics.Core ℕ using (⟦_⟧F; ⟦μ⟧; sem-cata; sem-fmap;
  sem-Out; sem-In; sem-In-Out; sem-cata-compute)

------------------------------------------------------------------------
-- sum-Id: sum the ℕ at the Id (recursive) positions of an F-layer.
-- (Structural on the functor F.)
------------------------------------------------------------------------
sum-Id : ∀ F → ⟦ F ⟧F ℕ → ℕ
sum-Id (K t)     x         = 0
sum-Id Id        n         = n
sum-Id (F₁ ⊕ F₂) (inj₁ x)  = sum-Id F₁ x
sum-Id (F₁ ⊕ F₂) (inj₂ y)  = sum-Id F₂ y
sum-Id (F₁ ⊗ F₂) (x , y)   = sum-Id F₁ x +ℕ sum-Id F₂ y

------------------------------------------------------------------------
-- μ-size: number of constructor nodes in a μ-value (one per layer).
------------------------------------------------------------------------
μ-size : ∀ {G} → WellFormedF G → ⟦μ⟧ G → ℕ
μ-size {G} wfG = sem-cata wfG (λ layer → suc (sum-Id G layer))

-- The catamorphism recurrence: a node's size is suc of the sum of its
-- children's sizes (the children being the Id-positions of its layer).
μ-size-unfold : ∀ {G} (wfG : WellFormedF G) (x : ⟦μ⟧ G)
  → μ-size wfG x ≡ suc (sum-Id G (sem-fmap G (μ-size wfG) (sem-Out wfG x)))
μ-size-unfold {G} wfG x =
  trans (cong (μ-size wfG) (sym (sem-In-Out wfG x)))
        (sem-cata-compute wfG (λ layer → suc (sum-Id G layer)) (sem-Out wfG x))

-- The total child-size of x's layer is strictly less than μ-size x.
child-sum-< : ∀ {G} (wfG : WellFormedF G) (x : ⟦μ⟧ G)
  → sum-Id G (sem-fmap G (μ-size wfG) (sem-Out wfG x)) < μ-size wfG x
child-sum-< {G} wfG x rewrite μ-size-unfold wfG x = n<1+n _

------------------------------------------------------------------------
-- Layer child-bound threading: `sum-Id F (sem-fmap F μ-size l) < n`
-- shrinks structurally as process-layer descends the functor, and at an
-- Id position yields `μ-size (the child) < n`.
------------------------------------------------------------------------

-- Sum: descending into a branch keeps the same child-sum (definitional).
-- Prod: each component's child-sum is ≤ the total, hence < n.
prod-bound-left : ∀ {n} a b → a +ℕ b < n → a < n
prod-bound-left {n} a b a+b<n = ≤-<-trans (m≤m+n a b) a+b<n

prod-bound-right : ∀ {n} a b → a +ℕ b < n → b < n
prod-bound-right {n} a b a+b<n = ≤-<-trans (m≤n+m b a) a+b<n
