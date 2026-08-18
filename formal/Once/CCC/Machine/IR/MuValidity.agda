------------------------------------------------------------------------
-- Once.CCC.Machine.IR.MuValidity
--
-- Validity for μ-type and ν-type values.
--
-- KEY INSIGHT: We define validity for recursive types separately from
-- ValidAtWF to avoid pattern matching issues. The μ/ν validity is then
-- connected to ValidAtWF via explicit constructors that don't require
-- unifying ⟦ F ⟧T (μ-type F) with other types during pattern matching.
--
-- APPROACH:
-- 1. Define μLayerValid/νLayerValid by induction on WellFormedF
-- 2. These predicates capture that F-layer memory layout is correct
-- 3. ValidAtWF constructors reference these predicates opaquely
-- 4. Pattern matching on ValidAtWF doesn't need to inspect layer types
------------------------------------------------------------------------

module Once.CCC.Machine.IR.MuValidity where

open import Data.Nat using (ℕ; zero; suc; _<_; _≤_)
open import Data.Bool using (false)
open import Data.Maybe using (just)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.SMCore hiding (AllocMode; Stack; Heap)
open import Once.Semantics.Machine using (⟦_⟧)
open import Once.Type using (Type; Functor; K; Id; _⊕_; _⊗_; μ-type; ν-type; ⟦_⟧T; _+_; _*_)
open import Once.Functor.Translate using (WellFormedF; wf-K; wf-Id; wf-Sum; wf-Prod; IsBaseType)
open import Once.CCC.Machine.Allocation hiding (AllocMode)

-- Import semantic operations
open import Once.Word using (Carrier)
open import Once.Float.Dyadic using (Dyadic)
open import Once.Semantics.Value Carrier Dyadic using (⟦μ⟧; ⟦ν⟧; ⟦_⟧F; sem-In; sem-Out; sem-CoIn; sem-CoOut)

-- Import SigOpSem for Validity module
open import Once.CCC.Eval using ()

------------------------------------------------------------------------
-- μLayerValid: Validity for F-layers by functor induction
--
-- This predicate captures that an F-layer has correct memory layout.
-- Defined by induction on WellFormedF to avoid the type computation
-- issues that occur with ValidAtWF.
--
-- KEY PROPERTY: Pattern matching on WellFormedF determines the layer
-- type statically, so we don't get unification failures.
------------------------------------------------------------------------

module MuValidityImpl {FS : FrameSemantics} (program-bound : ℕ) where
  open FrontierInvariant {FS}
  open MemOps {FS}
  open FrameSemantics FS

  -- Import readLoc-stack-heap-eq from Validity
  open import Once.CCC.Machine.Validity
  open ValidityDef {FS} program-bound using (readLoc-stack-heap-eq)

  -- | μLayerValid: F-layer at a location is memory-valid
  --
  -- Defined by induction on WellFormedF:
  -- - K: Base type at location, just needs BeforeFrontier
  -- - Id: Recursive position contains μ-value, needs μValid
  -- - Sum: Tag + one branch valid
  -- - Prod: Both components valid at consecutive locations
  --
  -- This is mutually recursive with μValid.
  mutual
    -- | Layer validity for F-layer containing μG values at recursive positions
    --
    -- Parameters:
    --   wfF : well-formedness of current sub-functor F
    --   wfG : well-formedness of the full μ-type being processed
    --   alloc : allocation state for frontier tracking
    --   layer : the F-layer value (with μG at recursive positions)
    --   loc : memory location of the layer
    --   s : machine state
    --
    data μLayerValid (alloc : AllocState {FS}) :
         ∀ {F G} → WellFormedF F → WellFormedF G →
         ⟦ F ⟧F (⟦μ⟧ G) → ValueLocation FS → LocState FS → Set where

      -- K-layer: constant type, no recursive positions
      -- Just needs the location to be before frontier
      μlayer-K : ∀ {G baseType} {wfG : WellFormedF G}
        {isBase : IsBaseType baseType}
        {x : ⟦ baseType ⟧} {loc : ValueLocation FS} {s : LocState FS} →
        BeforeFrontier alloc loc →
        μLayerValid alloc (wf-K isBase) wfG x loc s

      -- Id-layer: single recursive position containing μG value
      -- The recursive μG value must be valid
      μlayer-Id : ∀ {G} {wfG : WellFormedF G}
        {x : ⟦μ⟧ G} {loc : ValueLocation FS} {s : LocState FS} →
        μValid alloc wfG x loc s →
        μLayerValid alloc wf-Id wfG x loc s

      -- Sum-layer inl: left branch taken
      -- Tag at loc, payload pointer at sucLoc loc
      μlayer-inl : ∀ {F F' G} {wfF : WellFormedF F} {wfF' : WellFormedF F'}
        {wfG : WellFormedF G}
        {x : ⟦ F ⟧F (⟦μ⟧ G)}
        {sum-loc payload-loc : ValueLocation FS} {s : LocState FS} →
        readLoc s (sucLoc sum-loc) ≡ just (SV-Ptr payload-loc) →
        BeforeFrontier alloc payload-loc →
        BeforeFrontier alloc (sucLoc sum-loc) →
        μLayerValid alloc wfF wfG x payload-loc s →
        μLayerValid alloc (wf-Sum wfF wfF') wfG (inj₁ x) sum-loc s

      -- Sum-layer inr: right branch taken
      μlayer-inr : ∀ {F F' G} {wfF : WellFormedF F} {wfF' : WellFormedF F'}
        {wfG : WellFormedF G}
        {y : ⟦ F' ⟧F (⟦μ⟧ G)}
        {sum-loc payload-loc : ValueLocation FS} {s : LocState FS} →
        readLoc s (sucLoc sum-loc) ≡ just (SV-Ptr payload-loc) →
        BeforeFrontier alloc payload-loc →
        BeforeFrontier alloc (sucLoc sum-loc) →
        μLayerValid alloc wfF' wfG y payload-loc s →
        μLayerValid alloc (wf-Sum wfF wfF') wfG (inj₂ y) sum-loc s

      -- Product-layer: both components at consecutive locations
      μlayer-prod : ∀ {F F' G} {wfF : WellFormedF F} {wfF' : WellFormedF F'}
        {wfG : WellFormedF G}
        {x : ⟦ F ⟧F (⟦μ⟧ G)} {y : ⟦ F' ⟧F (⟦μ⟧ G)}
        {pair-loc fst-loc snd-loc : ValueLocation FS} {s : LocState FS} →
        readLoc s pair-loc ≡ just (SV-Ptr fst-loc) →
        readLoc s (sucLoc pair-loc) ≡ just (SV-Ptr snd-loc) →
        BeforeFrontier alloc fst-loc →
        BeforeFrontier alloc snd-loc →
        BeforeFrontier alloc (sucLoc pair-loc) →
        μLayerValid alloc wfF wfG x fst-loc s →
        μLayerValid alloc wfF' wfG y snd-loc s →
        μLayerValid alloc (wf-Prod wfF wfF') wfG (x , y) pair-loc s

    -- | μValid: A μ-value is valid if its layer is valid
    --
    -- By Lambek's lemma, μF ≅ F(μF) representationally.
    -- A μ-value x is valid at loc iff sem-Out wf x (the F-layer) is valid at loc.
    --
    -- This captures: no memory movement occurs in In/Out, so validity transfers.
    data μValid (alloc : AllocState {FS}) :
         ∀ {F} → WellFormedF F → ⟦μ⟧ F → ValueLocation FS → LocState FS → Set where
      μ-valid : ∀ {F} {wf : WellFormedF F}
        {x : ⟦μ⟧ F} {loc : ValueLocation FS} {s : LocState FS} →
        BeforeFrontier alloc loc →
        μLayerValid alloc wf wf (sem-Out wf x) loc s →
        μValid alloc wf x loc s

  ------------------------------------------------------------------------
  -- νLayerValid and νValid: Dual for coinductive types
  --
  -- Same structure as μ, but for ν-types (final coalgebras).
  -- The key difference is semantic: ν-values are productive (lazy),
  -- while μ-values are total (strict).
  ------------------------------------------------------------------------

  mutual
    data νLayerValid (alloc : AllocState {FS}) :
         ∀ {F G} → WellFormedF F → WellFormedF G →
         ⟦ F ⟧F (⟦ν⟧ G) → ValueLocation FS → LocState FS → Set where

      νlayer-K : ∀ {G baseType} {wfG : WellFormedF G}
        {isBase : IsBaseType baseType}
        {x : ⟦ baseType ⟧} {loc : ValueLocation FS} {s : LocState FS} →
        BeforeFrontier alloc loc →
        νLayerValid alloc (wf-K isBase) wfG x loc s

      νlayer-Id : ∀ {G} {wfG : WellFormedF G}
        {x : ⟦ν⟧ G} {loc : ValueLocation FS} {s : LocState FS} →
        νValid alloc wfG x loc s →
        νLayerValid alloc wf-Id wfG x loc s

      νlayer-inl : ∀ {F F' G} {wfF : WellFormedF F} {wfF' : WellFormedF F'}
        {wfG : WellFormedF G}
        {x : ⟦ F ⟧F (⟦ν⟧ G)}
        {sum-loc payload-loc : ValueLocation FS} {s : LocState FS} →
        readLoc s (sucLoc sum-loc) ≡ just (SV-Ptr payload-loc) →
        BeforeFrontier alloc payload-loc →
        BeforeFrontier alloc (sucLoc sum-loc) →
        νLayerValid alloc wfF wfG x payload-loc s →
        νLayerValid alloc (wf-Sum wfF wfF') wfG (inj₁ x) sum-loc s

      νlayer-inr : ∀ {F F' G} {wfF : WellFormedF F} {wfF' : WellFormedF F'}
        {wfG : WellFormedF G}
        {y : ⟦ F' ⟧F (⟦ν⟧ G)}
        {sum-loc payload-loc : ValueLocation FS} {s : LocState FS} →
        readLoc s (sucLoc sum-loc) ≡ just (SV-Ptr payload-loc) →
        BeforeFrontier alloc payload-loc →
        BeforeFrontier alloc (sucLoc sum-loc) →
        νLayerValid alloc wfF' wfG y payload-loc s →
        νLayerValid alloc (wf-Sum wfF wfF') wfG (inj₂ y) sum-loc s

      νlayer-prod : ∀ {F F' G} {wfF : WellFormedF F} {wfF' : WellFormedF F'}
        {wfG : WellFormedF G}
        {x : ⟦ F ⟧F (⟦ν⟧ G)} {y : ⟦ F' ⟧F (⟦ν⟧ G)}
        {pair-loc fst-loc snd-loc : ValueLocation FS} {s : LocState FS} →
        readLoc s pair-loc ≡ just (SV-Ptr fst-loc) →
        readLoc s (sucLoc pair-loc) ≡ just (SV-Ptr snd-loc) →
        BeforeFrontier alloc fst-loc →
        BeforeFrontier alloc snd-loc →
        BeforeFrontier alloc (sucLoc pair-loc) →
        νLayerValid alloc wfF wfG x fst-loc s →
        νLayerValid alloc wfF' wfG y snd-loc s →
        νLayerValid alloc (wf-Prod wfF wfF') wfG (x , y) pair-loc s

    data νValid (alloc : AllocState {FS}) :
         ∀ {F} → WellFormedF F → ⟦ν⟧ F → ValueLocation FS → LocState FS → Set where
      ν-valid : ∀ {F} {wf : WellFormedF F}
        {x : ⟦ν⟧ F} {loc : ValueLocation FS} {s : LocState FS} →
        BeforeFrontier alloc loc →
        νLayerValid alloc wf wf (sem-CoOut wf x) loc s →
        νValid alloc wf x loc s

  ------------------------------------------------------------------------
  -- Validity Preservation Lemmas
  --
  -- These lemmas prove that μValid/νValid are preserved under various
  -- operations. They are proven by mutual induction on μLayerValid/νLayerValid.
  --
  -- PATTERN: Each validity preservation proof follows the structure:
  --   1. Pattern match on μValid to get μLayerValid
  --   2. By mutual induction, show μLayerValid is preserved
  --   3. Reconstruct μValid from preserved components
  ------------------------------------------------------------------------

  mutual
    -- | μLayerValid preservation under memory equivalence
    μLayerValid-mem-only : ∀ {F G} (alloc : AllocState {FS})
      (wfF : WellFormedF F) (wfG : WellFormedF G)
      (layer : ⟦ F ⟧F (⟦μ⟧ G)) (loc : ValueLocation FS)
      (s₁ s₂ : LocState FS) →
      stackMem s₂ ≡ stackMem s₁ → heapMem s₂ ≡ heapMem s₁ →
      μLayerValid alloc wfF wfG layer loc s₁ →
      μLayerValid alloc wfF wfG layer loc s₂

    μLayerValid-mem-only alloc (wf-K _) wfG x loc s₁ s₂ sm hm (μlayer-K bf) =
      μlayer-K bf

    μLayerValid-mem-only alloc wf-Id wfG x loc s₁ s₂ sm hm (μlayer-Id μv) =
      μlayer-Id (μValid-mem-only alloc wfG x loc s₁ s₂ sm hm μv)

    μLayerValid-mem-only alloc (wf-Sum wfF wfF') wfG (inj₁ x) loc s₁ s₂ sm hm
      (μlayer-inl pp pb slb lv) =
      μlayer-inl (trans (readLoc-stack-heap-eq s₂ s₁ (sucLoc loc) sm hm) pp)
                 pb slb
                 (μLayerValid-mem-only alloc wfF wfG x _ s₁ s₂ sm hm lv)

    μLayerValid-mem-only alloc (wf-Sum wfF wfF') wfG (inj₂ y) loc s₁ s₂ sm hm
      (μlayer-inr pp pb slb lv) =
      μlayer-inr (trans (readLoc-stack-heap-eq s₂ s₁ (sucLoc loc) sm hm) pp)
                 pb slb
                 (μLayerValid-mem-only alloc wfF' wfG y _ s₁ s₂ sm hm lv)

    μLayerValid-mem-only alloc (wf-Prod wfF wfF') wfG (x , y) loc s₁ s₂ sm hm
      (μlayer-prod fp sp fb sb slb fv sv) =
      μlayer-prod (trans (readLoc-stack-heap-eq s₂ s₁ loc sm hm) fp)
                  (trans (readLoc-stack-heap-eq s₂ s₁ (sucLoc loc) sm hm) sp)
                  fb sb slb
                  (μLayerValid-mem-only alloc wfF wfG x _ s₁ s₂ sm hm fv)
                  (μLayerValid-mem-only alloc wfF' wfG y _ s₁ s₂ sm hm sv)

    -- | μValid preservation under memory equivalence
    μValid-mem-only : ∀ (alloc : AllocState {FS}) {F} (wf : WellFormedF F)
      (x : ⟦μ⟧ F) (loc : ValueLocation FS)
      (s₁ s₂ : LocState FS) →
      stackMem s₂ ≡ stackMem s₁ → heapMem s₂ ≡ heapMem s₁ →
      μValid alloc wf x loc s₁ →
      μValid alloc wf x loc s₂
    μValid-mem-only alloc wf x loc s₁ s₂ sm hm (μ-valid bf lv) =
      μ-valid bf (μLayerValid-mem-only alloc wf wf (sem-Out wf x) loc s₁ s₂ sm hm lv)

  -- | νValid preservation under memory equivalence (dual of μValid)
  mutual
    νLayerValid-mem-only : ∀ {F G} (alloc : AllocState {FS})
      (wfF : WellFormedF F) (wfG : WellFormedF G)
      (layer : ⟦ F ⟧F (⟦ν⟧ G)) (loc : ValueLocation FS)
      (s₁ s₂ : LocState FS) →
      stackMem s₂ ≡ stackMem s₁ → heapMem s₂ ≡ heapMem s₁ →
      νLayerValid alloc wfF wfG layer loc s₁ →
      νLayerValid alloc wfF wfG layer loc s₂

    νLayerValid-mem-only alloc (wf-K _) wfG x loc s₁ s₂ sm hm (νlayer-K bf) =
      νlayer-K bf

    νLayerValid-mem-only alloc wf-Id wfG x loc s₁ s₂ sm hm (νlayer-Id νv) =
      νlayer-Id (νValid-mem-only alloc wfG x loc s₁ s₂ sm hm νv)

    νLayerValid-mem-only alloc (wf-Sum wfF wfF') wfG (inj₁ x) loc s₁ s₂ sm hm
      (νlayer-inl pp pb slb lv) =
      νlayer-inl (trans (readLoc-stack-heap-eq s₂ s₁ (sucLoc loc) sm hm) pp)
                 pb slb
                 (νLayerValid-mem-only alloc wfF wfG x _ s₁ s₂ sm hm lv)

    νLayerValid-mem-only alloc (wf-Sum wfF wfF') wfG (inj₂ y) loc s₁ s₂ sm hm
      (νlayer-inr pp pb slb lv) =
      νlayer-inr (trans (readLoc-stack-heap-eq s₂ s₁ (sucLoc loc) sm hm) pp)
                 pb slb
                 (νLayerValid-mem-only alloc wfF' wfG y _ s₁ s₂ sm hm lv)

    νLayerValid-mem-only alloc (wf-Prod wfF wfF') wfG (x , y) loc s₁ s₂ sm hm
      (νlayer-prod fp sp fb sb slb fv sv) =
      νlayer-prod (trans (readLoc-stack-heap-eq s₂ s₁ loc sm hm) fp)
                  (trans (readLoc-stack-heap-eq s₂ s₁ (sucLoc loc) sm hm) sp)
                  fb sb slb
                  (νLayerValid-mem-only alloc wfF wfG x _ s₁ s₂ sm hm fv)
                  (νLayerValid-mem-only alloc wfF' wfG y _ s₁ s₂ sm hm sv)

    νValid-mem-only : ∀ (alloc : AllocState {FS}) {F} (wf : WellFormedF F)
      (x : ⟦ν⟧ F) (loc : ValueLocation FS)
      (s₁ s₂ : LocState FS) →
      stackMem s₂ ≡ stackMem s₁ → heapMem s₂ ≡ heapMem s₁ →
      νValid alloc wf x loc s₁ →
      νValid alloc wf x loc s₂
    νValid-mem-only alloc wf x loc s₁ s₂ sm hm (ν-valid bf lv) =
      ν-valid bf (νLayerValid-mem-only alloc wf wf (sem-CoOut wf x) loc s₁ s₂ sm hm lv)

  ------------------------------------------------------------------------
  -- Frontier Advance: μValid/νValid preserved when frontier advances
  --
  -- When alloc' has advanced frontier (same frame, slot/heap monotone),
  -- BeforeFrontier locations stay before frontier, so validity transfers.
  ------------------------------------------------------------------------

  mutual
    μLayerValid-frontier-advance : ∀ {F G} (alloc alloc' : AllocState {FS})
      (wfF : WellFormedF F) (wfG : WellFormedF G)
      (layer : ⟦ F ⟧F (⟦μ⟧ G)) (loc : ValueLocation FS) (s : LocState FS) →
      current-frame alloc' ≡ current-frame alloc →
      next-slot alloc ≤ next-slot alloc' →
      next-heap-ref alloc ≤ next-heap-ref alloc' →
      μLayerValid alloc wfF wfG layer loc s →
      μLayerValid alloc' wfF wfG layer loc s

    μLayerValid-frontier-advance alloc alloc' (wf-K _) wfG x loc s cf-eq sl-≤ hp-≤ (μlayer-K bf) =
      μlayer-K (frontier-monotone alloc alloc' (sym cf-eq) sl-≤ hp-≤ loc bf)

    μLayerValid-frontier-advance alloc alloc' wf-Id wfG x loc s cf-eq sl-≤ hp-≤ (μlayer-Id μv) =
      μlayer-Id (μValid-frontier-advance alloc alloc' wfG x loc s cf-eq sl-≤ hp-≤ μv)

    μLayerValid-frontier-advance alloc alloc' (wf-Sum wfF wfF') wfG (inj₁ x) loc s cf-eq sl-≤ hp-≤
      (μlayer-inl pp pb slb lv) =
      μlayer-inl pp
                 (frontier-monotone alloc alloc' (sym cf-eq) sl-≤ hp-≤ _ pb)
                 (frontier-monotone alloc alloc' (sym cf-eq) sl-≤ hp-≤ _ slb)
                 (μLayerValid-frontier-advance alloc alloc' wfF wfG x _ s cf-eq sl-≤ hp-≤ lv)

    μLayerValid-frontier-advance alloc alloc' (wf-Sum wfF wfF') wfG (inj₂ y) loc s cf-eq sl-≤ hp-≤
      (μlayer-inr pp pb slb lv) =
      μlayer-inr pp
                 (frontier-monotone alloc alloc' (sym cf-eq) sl-≤ hp-≤ _ pb)
                 (frontier-monotone alloc alloc' (sym cf-eq) sl-≤ hp-≤ _ slb)
                 (μLayerValid-frontier-advance alloc alloc' wfF' wfG y _ s cf-eq sl-≤ hp-≤ lv)

    μLayerValid-frontier-advance alloc alloc' (wf-Prod wfF wfF') wfG (x , y) loc s cf-eq sl-≤ hp-≤
      (μlayer-prod fp sp fb sb slb fv sv) =
      μlayer-prod fp sp
                  (frontier-monotone alloc alloc' (sym cf-eq) sl-≤ hp-≤ _ fb)
                  (frontier-monotone alloc alloc' (sym cf-eq) sl-≤ hp-≤ _ sb)
                  (frontier-monotone alloc alloc' (sym cf-eq) sl-≤ hp-≤ _ slb)
                  (μLayerValid-frontier-advance alloc alloc' wfF wfG x _ s cf-eq sl-≤ hp-≤ fv)
                  (μLayerValid-frontier-advance alloc alloc' wfF' wfG y _ s cf-eq sl-≤ hp-≤ sv)

    μValid-frontier-advance : ∀ (alloc alloc' : AllocState {FS}) {F} (wf : WellFormedF F)
      (x : ⟦μ⟧ F) (loc : ValueLocation FS) (s : LocState FS) →
      current-frame alloc' ≡ current-frame alloc →
      next-slot alloc ≤ next-slot alloc' →
      next-heap-ref alloc ≤ next-heap-ref alloc' →
      μValid alloc wf x loc s →
      μValid alloc' wf x loc s
    μValid-frontier-advance alloc alloc' wf x loc s cf-eq sl-≤ hp-≤ (μ-valid bf lv) =
      μ-valid (frontier-monotone alloc alloc' (sym cf-eq) sl-≤ hp-≤ loc bf)
              (μLayerValid-frontier-advance alloc alloc' wf wf (sem-Out wf x) loc s cf-eq sl-≤ hp-≤ lv)

  mutual
    νLayerValid-frontier-advance : ∀ {F G} (alloc alloc' : AllocState {FS})
      (wfF : WellFormedF F) (wfG : WellFormedF G)
      (layer : ⟦ F ⟧F (⟦ν⟧ G)) (loc : ValueLocation FS) (s : LocState FS) →
      current-frame alloc' ≡ current-frame alloc →
      next-slot alloc ≤ next-slot alloc' →
      next-heap-ref alloc ≤ next-heap-ref alloc' →
      νLayerValid alloc wfF wfG layer loc s →
      νLayerValid alloc' wfF wfG layer loc s

    νLayerValid-frontier-advance alloc alloc' (wf-K _) wfG x loc s cf-eq sl-≤ hp-≤ (νlayer-K bf) =
      νlayer-K (frontier-monotone alloc alloc' (sym cf-eq) sl-≤ hp-≤ loc bf)

    νLayerValid-frontier-advance alloc alloc' wf-Id wfG x loc s cf-eq sl-≤ hp-≤ (νlayer-Id νv) =
      νlayer-Id (νValid-frontier-advance alloc alloc' wfG x loc s cf-eq sl-≤ hp-≤ νv)

    νLayerValid-frontier-advance alloc alloc' (wf-Sum wfF wfF') wfG (inj₁ x) loc s cf-eq sl-≤ hp-≤
      (νlayer-inl pp pb slb lv) =
      νlayer-inl pp
                 (frontier-monotone alloc alloc' (sym cf-eq) sl-≤ hp-≤ _ pb)
                 (frontier-monotone alloc alloc' (sym cf-eq) sl-≤ hp-≤ _ slb)
                 (νLayerValid-frontier-advance alloc alloc' wfF wfG x _ s cf-eq sl-≤ hp-≤ lv)

    νLayerValid-frontier-advance alloc alloc' (wf-Sum wfF wfF') wfG (inj₂ y) loc s cf-eq sl-≤ hp-≤
      (νlayer-inr pp pb slb lv) =
      νlayer-inr pp
                 (frontier-monotone alloc alloc' (sym cf-eq) sl-≤ hp-≤ _ pb)
                 (frontier-monotone alloc alloc' (sym cf-eq) sl-≤ hp-≤ _ slb)
                 (νLayerValid-frontier-advance alloc alloc' wfF' wfG y _ s cf-eq sl-≤ hp-≤ lv)

    νLayerValid-frontier-advance alloc alloc' (wf-Prod wfF wfF') wfG (x , y) loc s cf-eq sl-≤ hp-≤
      (νlayer-prod fp sp fb sb slb fv sv) =
      νlayer-prod fp sp
                  (frontier-monotone alloc alloc' (sym cf-eq) sl-≤ hp-≤ _ fb)
                  (frontier-monotone alloc alloc' (sym cf-eq) sl-≤ hp-≤ _ sb)
                  (frontier-monotone alloc alloc' (sym cf-eq) sl-≤ hp-≤ _ slb)
                  (νLayerValid-frontier-advance alloc alloc' wfF wfG x _ s cf-eq sl-≤ hp-≤ fv)
                  (νLayerValid-frontier-advance alloc alloc' wfF' wfG y _ s cf-eq sl-≤ hp-≤ sv)

    νValid-frontier-advance : ∀ (alloc alloc' : AllocState {FS}) {F} (wf : WellFormedF F)
      (x : ⟦ν⟧ F) (loc : ValueLocation FS) (s : LocState FS) →
      current-frame alloc' ≡ current-frame alloc →
      next-slot alloc ≤ next-slot alloc' →
      next-heap-ref alloc ≤ next-heap-ref alloc' →
      νValid alloc wf x loc s →
      νValid alloc' wf x loc s
    νValid-frontier-advance alloc alloc' wf x loc s cf-eq sl-≤ hp-≤ (ν-valid bf lv) =
      ν-valid (frontier-monotone alloc alloc' (sym cf-eq) sl-≤ hp-≤ loc bf)
              (νLayerValid-frontier-advance alloc alloc' wf wf (sem-CoOut wf x) loc s cf-eq sl-≤ hp-≤ lv)

  ------------------------------------------------------------------------
  -- BeforeFrontier Transfer: μValid/νValid with general bf transfer
  --
  -- Transfer validity between allocation states using a general
  -- BeforeFrontier transfer function.
  ------------------------------------------------------------------------

  mutual
    μLayerValid-bf-transfer : ∀ {F G}
      (a₁ a₂ : AllocState {FS})
      (wfF : WellFormedF F) (wfG : WellFormedF G)
      (layer : ⟦ F ⟧F (⟦μ⟧ G)) (loc : ValueLocation FS) (s : LocState FS) →
      (bf-transfer : ∀ loc' → BeforeFrontier a₁ loc' → BeforeFrontier a₂ loc') →
      μLayerValid a₁ wfF wfG layer loc s →
      μLayerValid a₂ wfF wfG layer loc s

    μLayerValid-bf-transfer a₁ a₂ (wf-K _) wfG x loc s bf (μlayer-K bfr) =
      μlayer-K (bf loc bfr)

    μLayerValid-bf-transfer a₁ a₂ wf-Id wfG x loc s bf (μlayer-Id μv) =
      μlayer-Id (μValid-bf-transfer a₁ a₂ wfG x loc s bf μv)

    μLayerValid-bf-transfer a₁ a₂ (wf-Sum wfF wfF') wfG (inj₁ x) loc s bf
      (μlayer-inl pp pb slb lv) =
      μlayer-inl pp (bf _ pb) (bf _ slb)
                 (μLayerValid-bf-transfer a₁ a₂ wfF wfG x _ s bf lv)

    μLayerValid-bf-transfer a₁ a₂ (wf-Sum wfF wfF') wfG (inj₂ y) loc s bf
      (μlayer-inr pp pb slb lv) =
      μlayer-inr pp (bf _ pb) (bf _ slb)
                 (μLayerValid-bf-transfer a₁ a₂ wfF' wfG y _ s bf lv)

    μLayerValid-bf-transfer a₁ a₂ (wf-Prod wfF wfF') wfG (x , y) loc s bf
      (μlayer-prod fp sp fb sb slb fv sv) =
      μlayer-prod fp sp (bf _ fb) (bf _ sb) (bf _ slb)
                  (μLayerValid-bf-transfer a₁ a₂ wfF wfG x _ s bf fv)
                  (μLayerValid-bf-transfer a₁ a₂ wfF' wfG y _ s bf sv)

    μValid-bf-transfer : ∀ (a₁ a₂ : AllocState {FS}) {F} (wf : WellFormedF F)
      (x : ⟦μ⟧ F) (loc : ValueLocation FS) (s : LocState FS) →
      (bf-transfer : ∀ loc' → BeforeFrontier a₁ loc' → BeforeFrontier a₂ loc') →
      μValid a₁ wf x loc s →
      μValid a₂ wf x loc s
    μValid-bf-transfer a₁ a₂ wf x loc s bf (μ-valid bfr lv) =
      μ-valid (bf loc bfr) (μLayerValid-bf-transfer a₁ a₂ wf wf (sem-Out wf x) loc s bf lv)

  mutual
    νLayerValid-bf-transfer : ∀ {F G}
      (a₁ a₂ : AllocState {FS})
      (wfF : WellFormedF F) (wfG : WellFormedF G)
      (layer : ⟦ F ⟧F (⟦ν⟧ G)) (loc : ValueLocation FS) (s : LocState FS) →
      (bf-transfer : ∀ loc' → BeforeFrontier a₁ loc' → BeforeFrontier a₂ loc') →
      νLayerValid a₁ wfF wfG layer loc s →
      νLayerValid a₂ wfF wfG layer loc s

    νLayerValid-bf-transfer a₁ a₂ (wf-K _) wfG x loc s bf (νlayer-K bfr) =
      νlayer-K (bf loc bfr)

    νLayerValid-bf-transfer a₁ a₂ wf-Id wfG x loc s bf (νlayer-Id νv) =
      νlayer-Id (νValid-bf-transfer a₁ a₂ wfG x loc s bf νv)

    νLayerValid-bf-transfer a₁ a₂ (wf-Sum wfF wfF') wfG (inj₁ x) loc s bf
      (νlayer-inl pp pb slb lv) =
      νlayer-inl pp (bf _ pb) (bf _ slb)
                 (νLayerValid-bf-transfer a₁ a₂ wfF wfG x _ s bf lv)

    νLayerValid-bf-transfer a₁ a₂ (wf-Sum wfF wfF') wfG (inj₂ y) loc s bf
      (νlayer-inr pp pb slb lv) =
      νlayer-inr pp (bf _ pb) (bf _ slb)
                 (νLayerValid-bf-transfer a₁ a₂ wfF' wfG y _ s bf lv)

    νLayerValid-bf-transfer a₁ a₂ (wf-Prod wfF wfF') wfG (x , y) loc s bf
      (νlayer-prod fp sp fb sb slb fv sv) =
      νlayer-prod fp sp (bf _ fb) (bf _ sb) (bf _ slb)
                  (νLayerValid-bf-transfer a₁ a₂ wfF wfG x _ s bf fv)
                  (νLayerValid-bf-transfer a₁ a₂ wfF' wfG y _ s bf sv)

    νValid-bf-transfer : ∀ (a₁ a₂ : AllocState {FS}) {F} (wf : WellFormedF F)
      (x : ⟦ν⟧ F) (loc : ValueLocation FS) (s : LocState FS) →
      (bf-transfer : ∀ loc' → BeforeFrontier a₁ loc' → BeforeFrontier a₂ loc') →
      νValid a₁ wf x loc s →
      νValid a₂ wf x loc s
    νValid-bf-transfer a₁ a₂ wf x loc s bf (ν-valid bfr lv) =
      ν-valid (bf loc bfr) (νLayerValid-bf-transfer a₁ a₂ wf wf (sem-CoOut wf x) loc s bf lv)

  ------------------------------------------------------------------------
  -- Memory Preserved: μValid/νValid when memory at BeforeFrontier preserved
  --
  -- If memory at all BeforeFrontier locations is preserved between states,
  -- then validity transfers.
  ------------------------------------------------------------------------

  mutual
    μLayerValid-mem-preserved : ∀ {F G} (alloc : AllocState {FS})
      (wfF : WellFormedF F) (wfG : WellFormedF G)
      (layer : ⟦ F ⟧F (⟦μ⟧ G)) (loc : ValueLocation FS)
      (s₁ s₂ : LocState FS) →
      BeforeFrontier alloc loc →
      (∀ loc' → BeforeFrontier alloc loc' → readLoc s₂ loc' ≡ readLoc s₁ loc') →
      μLayerValid alloc wfF wfG layer loc s₁ →
      μLayerValid alloc wfF wfG layer loc s₂

    μLayerValid-mem-preserved alloc (wf-K _) wfG x loc s₁ s₂ loc-bf mem-eq (μlayer-K bf) =
      μlayer-K bf

    μLayerValid-mem-preserved alloc wf-Id wfG x loc s₁ s₂ loc-bf mem-eq (μlayer-Id μv) =
      μlayer-Id (μValid-mem-preserved alloc wfG x loc s₁ s₂ loc-bf mem-eq μv)

    μLayerValid-mem-preserved alloc (wf-Sum wfF wfF') wfG (inj₁ x) loc s₁ s₂ loc-bf mem-eq
      (μlayer-inl pp pb slb lv) =
      μlayer-inl (trans (mem-eq (sucLoc loc) slb) pp) pb slb
                 (μLayerValid-mem-preserved alloc wfF wfG x _ s₁ s₂ pb mem-eq lv)

    μLayerValid-mem-preserved alloc (wf-Sum wfF wfF') wfG (inj₂ y) loc s₁ s₂ loc-bf mem-eq
      (μlayer-inr pp pb slb lv) =
      μlayer-inr (trans (mem-eq (sucLoc loc) slb) pp) pb slb
                 (μLayerValid-mem-preserved alloc wfF' wfG y _ s₁ s₂ pb mem-eq lv)

    μLayerValid-mem-preserved alloc (wf-Prod wfF wfF') wfG (x , y) loc s₁ s₂ loc-bf mem-eq
      (μlayer-prod fp sp fb sb slb fv sv) =
      μlayer-prod (trans (mem-eq loc loc-bf) fp)
                  (trans (mem-eq (sucLoc loc) slb) sp)
                  fb sb slb
                  (μLayerValid-mem-preserved alloc wfF wfG x _ s₁ s₂ fb mem-eq fv)
                  (μLayerValid-mem-preserved alloc wfF' wfG y _ s₁ s₂ sb mem-eq sv)

    μValid-mem-preserved : ∀ (alloc : AllocState {FS}) {F} (wf : WellFormedF F)
      (x : ⟦μ⟧ F) (loc : ValueLocation FS)
      (s₁ s₂ : LocState FS) →
      BeforeFrontier alloc loc →
      (∀ loc' → BeforeFrontier alloc loc' → readLoc s₂ loc' ≡ readLoc s₁ loc') →
      μValid alloc wf x loc s₁ →
      μValid alloc wf x loc s₂
    μValid-mem-preserved alloc wf x loc s₁ s₂ loc-bf mem-eq (μ-valid bf lv) =
      μ-valid bf (μLayerValid-mem-preserved alloc wf wf (sem-Out wf x) loc s₁ s₂ loc-bf mem-eq lv)

  mutual
    νLayerValid-mem-preserved : ∀ {F G} (alloc : AllocState {FS})
      (wfF : WellFormedF F) (wfG : WellFormedF G)
      (layer : ⟦ F ⟧F (⟦ν⟧ G)) (loc : ValueLocation FS)
      (s₁ s₂ : LocState FS) →
      BeforeFrontier alloc loc →
      (∀ loc' → BeforeFrontier alloc loc' → readLoc s₂ loc' ≡ readLoc s₁ loc') →
      νLayerValid alloc wfF wfG layer loc s₁ →
      νLayerValid alloc wfF wfG layer loc s₂

    νLayerValid-mem-preserved alloc (wf-K _) wfG x loc s₁ s₂ loc-bf mem-eq (νlayer-K bf) =
      νlayer-K bf

    νLayerValid-mem-preserved alloc wf-Id wfG x loc s₁ s₂ loc-bf mem-eq (νlayer-Id νv) =
      νlayer-Id (νValid-mem-preserved alloc wfG x loc s₁ s₂ loc-bf mem-eq νv)

    νLayerValid-mem-preserved alloc (wf-Sum wfF wfF') wfG (inj₁ x) loc s₁ s₂ loc-bf mem-eq
      (νlayer-inl pp pb slb lv) =
      νlayer-inl (trans (mem-eq (sucLoc loc) slb) pp) pb slb
                 (νLayerValid-mem-preserved alloc wfF wfG x _ s₁ s₂ pb mem-eq lv)

    νLayerValid-mem-preserved alloc (wf-Sum wfF wfF') wfG (inj₂ y) loc s₁ s₂ loc-bf mem-eq
      (νlayer-inr pp pb slb lv) =
      νlayer-inr (trans (mem-eq (sucLoc loc) slb) pp) pb slb
                 (νLayerValid-mem-preserved alloc wfF' wfG y _ s₁ s₂ pb mem-eq lv)

    νLayerValid-mem-preserved alloc (wf-Prod wfF wfF') wfG (x , y) loc s₁ s₂ loc-bf mem-eq
      (νlayer-prod fp sp fb sb slb fv sv) =
      νlayer-prod (trans (mem-eq loc loc-bf) fp)
                  (trans (mem-eq (sucLoc loc) slb) sp)
                  fb sb slb
                  (νLayerValid-mem-preserved alloc wfF wfG x _ s₁ s₂ fb mem-eq fv)
                  (νLayerValid-mem-preserved alloc wfF' wfG y _ s₁ s₂ sb mem-eq sv)

    νValid-mem-preserved : ∀ (alloc : AllocState {FS}) {F} (wf : WellFormedF F)
      (x : ⟦ν⟧ F) (loc : ValueLocation FS)
      (s₁ s₂ : LocState FS) →
      BeforeFrontier alloc loc →
      (∀ loc' → BeforeFrontier alloc loc' → readLoc s₂ loc' ≡ readLoc s₁ loc') →
      νValid alloc wf x loc s₁ →
      νValid alloc wf x loc s₂
    νValid-mem-preserved alloc wf x loc s₁ s₂ loc-bf mem-eq (ν-valid bf lv) =
      ν-valid bf (νLayerValid-mem-preserved alloc wf wf (sem-CoOut wf x) loc s₁ s₂ loc-bf mem-eq lv)

  ------------------------------------------------------------------------
  -- Connection to ValidAtWF
  --
  -- These lemmas show how μValid/νValid relate to ValidAtWF.
  -- The key insight is that μValid captures the SAME memory layout
  -- constraints as ValidAtWF would for the corresponding types.
  ------------------------------------------------------------------------

  -- Note: The actual connection to ValidAtWF requires adding constructors
  -- to ValidAtWF in ClosureWellFormed.agda. These constructors will
  -- reference μValid/νValid, avoiding the pattern matching issues.

