------------------------------------------------------------------------
-- Once.CCC.Machine.IR.MuSize
--
-- A structural size measure on μ-values, for well-founded recursion in
-- the Cata machinery (Plan 0.27, Option B — replacing TERMINATING).
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
open import Once.Word using (Carrier)
open import Once.Float.Decimal using (Decimal)
open import Once.Semantics.Value Carrier Carrier using (⟦_⟧F; ⟦μ⟧; sem-cata; sem-fmap;
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
--
-- `abstract`: μ-size unfolds to sem-cata = cataS, which is expensive to
-- normalise. Consumers (CataLayer's well-founded threading) only need it
-- as an OPAQUE mapped function plus the two propositional lemmas below;
-- keeping it abstract stops Agda unfolding cataS during size-bound type
-- comparisons (otherwise CataLayer's typecheck explodes — Plan 0.27).
-- sum-Id / sem-fmap stay reducible, so the structural threading
-- reductions (sum-Id (F⊕G)(inj₁ …) = sum-Id F …, etc.) still hold.
------------------------------------------------------------------------
abstract
  μ-size : ∀ {G} → WellFormedF G → ⟦μ⟧ G → ℕ
  μ-size {G} wfG = sem-cata wfG (λ layer → suc (sum-Id G layer))

  -- The catamorphism recurrence: a node's size is suc of the sum of its
  -- children's sizes (the children being the Id-positions of its layer).
  μ-size-unfold : ∀ {G} (wfG : WellFormedF G) (x : ⟦μ⟧ G)
    → μ-size wfG x ≡ suc (sum-Id G (sem-fmap G (μ-size wfG) (sem-Out wfG x)))
  μ-size-unfold {G} wfG x =
    trans (cong (μ-size wfG) (sym (sem-In-Out wfG x)))
          (sem-cata-compute wfG (λ layer → suc (sum-Id G layer)) (sem-Out wfG x))

  ------------------------------------------------------------------------
  -- child-measure: the well-founded measure CataLayer threads. It is the
  -- total μ-size at the Id (recursive) positions of an F-layer.
  --
  -- CRITICAL (Plan 0.27 perf): child-measure is OPAQUE. CataLayer's
  -- `process-layer` carries `size-bound : child-measure F wfG layer < n`
  -- as a hypothesis in the ambient context of a ~2700-line mutual block
  -- with 19 with-blocks. Each with-auxiliary re-takes that context, and
  -- each where-binding's type is elaborated in it. If the measure were
  -- the transparent `sum-Id F (sem-fmap F (μ-size wfG) layer)`, every such
  -- elaboration would normalise sem-fmap/sum-Id over large `layer` terms
  -- (the regression that took CataLayer's typecheck past 56 min). Keeping
  -- it opaque means there is nothing to unfold; the bound only ever moves
  -- via the refl-proved stepping lemmas below. (extract-proofs-from-where
  -- + agda-typecheck-oom-abstract.)
  ------------------------------------------------------------------------
  child-measure : ∀ F {G} (wfG : WellFormedF G) → ⟦ F ⟧F (⟦μ⟧ G) → ℕ
  child-measure F wfG layer = sum-Id F (sem-fmap F (μ-size wfG) layer)

  -- The total child-size of x's layer is strictly less than μ-size x.
  child-sum-< : ∀ {G} (wfG : WellFormedF G) (x : ⟦μ⟧ G)
    → child-measure G wfG (sem-Out wfG x) < μ-size wfG x
  child-sum-< {G} wfG x rewrite μ-size-unfold wfG x = n<1+n _

  ----------------------------------------------------------------------
  -- Stepping lemmas: how child-measure descends the functor. All hold by
  -- refl INSIDE this abstract block (child-measure unfolds, sem-fmap
  -- reduces structurally on the constructor); outside, child-measure is
  -- opaque so these are the only way CataLayer moves the bound. They are
  -- stated as bound-transformers (… < n → … < n) so the CataLayer call
  -- sites stay one-liners with opaque types and no subst noise.
  ----------------------------------------------------------------------

  -- Id position: the child μ-value's own μ-size is the bound.
  child-bound-Id : ∀ {G n} (wfG : WellFormedF G) (c : ⟦μ⟧ G)
    → child-measure Id wfG c < n → μ-size wfG c < n
  child-bound-Id wfG c h = h

  -- Sum: descending into a branch keeps the same child-measure.
  child-bound-inj₁ : ∀ {FL FR G n} (wfG : WellFormedF G) (l : ⟦ FL ⟧F (⟦μ⟧ G))
    → child-measure (FL ⊕ FR) wfG (inj₁ l) < n → child-measure FL wfG l < n
  child-bound-inj₁ wfG l h = h

  child-bound-inj₂ : ∀ {FL FR G n} (wfG : WellFormedF G) (r : ⟦ FR ⟧F (⟦μ⟧ G))
    → child-measure (FL ⊕ FR) wfG (inj₂ r) < n → child-measure FR wfG r < n
  child-bound-inj₂ wfG r h = h

  -- Prod: each component's child-measure is ≤ the total, hence < n.
  child-bound-prod-left : ∀ {FL FR G n} (wfG : WellFormedF G)
    (l : ⟦ FL ⟧F (⟦μ⟧ G)) (r : ⟦ FR ⟧F (⟦μ⟧ G))
    → child-measure (FL ⊗ FR) wfG (l , r) < n → child-measure FL wfG l < n
  child-bound-prod-left wfG l r h = ≤-<-trans (m≤m+n _ _) h

  child-bound-prod-right : ∀ {FL FR G n} (wfG : WellFormedF G)
    (l : ⟦ FL ⟧F (⟦μ⟧ G)) (r : ⟦ FR ⟧F (⟦μ⟧ G))
    → child-measure (FL ⊗ FR) wfG (l , r) < n → child-measure FR wfG r < n
  child-bound-prod-right wfG l r h = ≤-<-trans (m≤n+m _ _) h

------------------------------------------------------------------------
-- functor-size: structural size of a (reified) Functor, the well-founded
-- measure for CataLayer's FUNCTOR recursion (process-layer descending
-- FL/FR). Plan 0.27 perf: process-layer/process-layer-prod route their
-- recursive calls through a reified capability (make-proc-rec) built from
-- an `Acc _<_ (functor-size F)`; that takes the heavy bodies OUT of the
-- termination SCC (foetus does not track parameter applications). These
-- four lemmas are the strict decreases the capability is indexed by.
-- Structural + cheap, so NOT abstract (definitional reductions are fine).
------------------------------------------------------------------------
functor-size : Functor → ℕ
functor-size (K t)     = 1
functor-size Id        = 1
functor-size (F₁ ⊕ F₂) = suc (functor-size F₁ +ℕ functor-size F₂)
functor-size (F₁ ⊗ F₂) = suc (functor-size F₁ +ℕ functor-size F₂)

fsize-inj-left : ∀ F₁ F₂ → functor-size F₁ < functor-size (F₁ ⊕ F₂)
fsize-inj-left F₁ F₂ = s≤s (m≤m+n (functor-size F₁) (functor-size F₂))

fsize-inj-right : ∀ F₁ F₂ → functor-size F₂ < functor-size (F₁ ⊕ F₂)
fsize-inj-right F₁ F₂ = s≤s (m≤n+m (functor-size F₂) (functor-size F₁))

fsize-prod-left : ∀ F₁ F₂ → functor-size F₁ < functor-size (F₁ ⊗ F₂)
fsize-prod-left F₁ F₂ = s≤s (m≤m+n (functor-size F₁) (functor-size F₂))

fsize-prod-right : ∀ F₁ F₂ → functor-size F₂ < functor-size (F₁ ⊗ F₂)
fsize-prod-right F₁ F₂ = s≤s (m≤n+m (functor-size F₂) (functor-size F₁))
