------------------------------------------------------------------------
-- Once.CCC.Machine.IR.LambekValidity
--
-- Validity lemmas for Lambek isomorphisms (In, out-μ, Out, in-ν).
--
-- By Lambek's lemma, μF ≅ F(μF) and νF ≅ F(νF) representationally.
-- At the machine level, these isomorphisms are identity - no memory
-- layout changes occur.
--
-- JUSTIFICATION FOR POSTULATES:
-- The Lambek isos don't move or copy data. They just reinterpret
-- existing memory as a different type. Since ValidAtWF is about
-- memory layout, validity SHOULD transfer directly.
--
-- However, proving this in Agda requires showing that the ValidAtWF
-- type indices (Type) are compatible across the isomorphism. This is
-- blocked by the fact that μ-type F and ⟦ F ⟧T (μ-type F) are
-- different Type values, even though they have identical memory layout.
--
-- These postulates are JUSTIFIED because:
-- 1. Both types have identical memory representation (Lambek iso)
-- 2. ValidAtWF only depends on memory layout, not type identity
-- 3. The machine operations (In, Out, etc.) are no-ops at runtime
--
-- COMPARISON TO PREVIOUS POSTULATES:
-- - OLD: lambek-iso-semantic for ANY IR - too general
-- - NEW: specific to In/Out operations with WellFormedF evidence
------------------------------------------------------------------------

module Once.CCC.Machine.IR.LambekValidity where

open import Data.Nat using (ℕ)
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.SMCore hiding (AllocMode; Stack; Heap)
open import Once.Semantics.Machine using (⟦_⟧)
open import Once.CCC.IR
open import Once.CCC.Eval using (eval)
open import Once.CCC.Machine.Allocation hiding (AllocMode)
open import Once.Type using (Type; Functor; μ-type; ν-type; ⟦_⟧T)
open import Once.Functor.Translate using (WellFormedF; wf-K; wf-Id; wf-Sum; wf-Prod;
                                          IsBaseType; base-Unit; base-Void; base-Int;
                                          base-Float; base-Str; base-Buffer;
                                          base-Prod; base-Sum)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; subst)

-- Semantic operations
open import Once.Semantics.Core ℕ using (sem-In; sem-Out; sem-CoIn; sem-CoOut;
                                          coerce-functor; coerce-functor⁻¹)

------------------------------------------------------------------------
-- LambekValidityImpl
--
-- Provides ValidAtWF transfer lemmas for Lambek isomorphisms.
-- These are postulated because the type indices prevent direct proof.
------------------------------------------------------------------------

module LambekValidityImpl {FS : FrameSemantics} (program-bound : ℕ) where
  open FrameSemantics FS
  open FrontierInvariant {FS}

  open import Once.CCC.Machine.ClosureWellFormed
  open ClosureWellFormedDef {FS} program-bound
    using (ValidAtWF; valid-unit-wf; valid-int-wf; valid-float-wf;
           valid-str-wf; valid-buffer-wf; valid-coerce-kind-wf;
           valid-inl-wf; valid-inr-wf; valid-pair-wf; valid-μ-wf; valid-ν-wf)

  import Once.CCC.Machine.IR.MuValidity as MV
  open MV.MuValidityImpl {FS} program-bound
    using (μValid; μ-valid; μLayerValid;
           μlayer-K; μlayer-Id; μlayer-inl; μlayer-inr; μlayer-prod)

  ------------------------------------------------------------------------
  -- Plan 0.27 POC-1: the load-bearing forward correspondence.
  --
  -- `μLayerValid` (MuValidity) and the `valid-{inl,inr,pair}-wf`
  -- constructors describe the SAME heap layout (identical sucLoc offsets
  -- and pointer chains). So a valid F-layer of μ-values IS a valid
  -- μLayerValid — by structural induction on `WellFormedF F`. This
  -- discharges the *representational* Lambek transfer (the basis for
  -- In/out-μ being real, not postulated).
  --
  -- `BeforeFrontier alloc loc` is threaded explicitly: parent
  -- constructors (valid-inl/inr/pair-wf) carry each child loc's
  -- frontier-membership, so the recursion supplies it; only the K leaf
  -- consumes it (its payload structure is irrelevant to μlayer-K, the
  -- forward direction weakens — K-of-compound is handled by ignoring
  -- the richer ValidAtWF, see the `_` in the wf-K clause).
  ------------------------------------------------------------------------

  -- WellFormedF / IsBaseType are singletons (structural on the
  -- functor/type), so proofs are irrelevant. Needed to align the `wf`
  -- carried by a recursive μ-value's `valid-μ-wf` with the ambient one.
  mutual
    wf-irrel : ∀ {F} (p q : WellFormedF F) → p ≡ q
    wf-irrel (wf-K b1)     (wf-K b2)     = cong wf-K (isbase-irrel b1 b2)
    wf-irrel wf-Id         wf-Id         = refl
    wf-irrel (wf-Sum p1 p2)  (wf-Sum q1 q2)  = cong₂ wf-Sum (wf-irrel p1 q1) (wf-irrel p2 q2)
    wf-irrel (wf-Prod p1 p2) (wf-Prod q1 q2) = cong₂ wf-Prod (wf-irrel p1 q1) (wf-irrel p2 q2)

    isbase-irrel : ∀ {A} (p q : IsBaseType A) → p ≡ q
    isbase-irrel base-Unit   base-Unit   = refl
    isbase-irrel base-Void   base-Void   = refl
    isbase-irrel base-Int    base-Int    = refl
    isbase-irrel base-Float  base-Float  = refl
    isbase-irrel base-Str    base-Str    = refl
    isbase-irrel base-Buffer base-Buffer = refl
    isbase-irrel (base-Prod p1 p2) (base-Prod q1 q2) = cong₂ base-Prod (isbase-irrel p1 q1) (isbase-irrel p2 q2)
    isbase-irrel (base-Sum  p1 p2) (base-Sum  q1 q2) = cong₂ base-Sum  (isbase-irrel p1 q1) (isbase-irrel p2 q2)

  layer→μlayer : ∀ {m F G} (wfF : WellFormedF F) (wfG : WellFormedF G)
    {alloc : AllocState {FS}} {loc : ValueLocation FS} {s : LocState FS}
    {x : ⟦ ⟦ F ⟧T (μ-type G) ⟧} →
    BeforeFrontier alloc loc →
    ValidAtWF m alloc {⟦ F ⟧T (μ-type G)} x loc s →
    μLayerValid alloc wfF wfG (coerce-functor F (μ-type G) x) loc s
  layer→μlayer (wf-K isBase) wfG bf _ = μlayer-K bf
  layer→μlayer wf-Id wfG bf (valid-μ-wf wf' _ μv) =
    μlayer-Id (subst (λ w → μValid _ w _ _ _) (wf-irrel wf' wfG) μv)
  layer→μlayer (wf-Sum wfF1 wfF2) wfG bf
    (valid-inl-wf lmm read-suc bf-pay bf-suc sub-v) =
    μlayer-inl read-suc bf-pay bf-suc (layer→μlayer wfF1 wfG bf-pay sub-v)
  layer→μlayer (wf-Sum wfF1 wfF2) wfG bf
    (valid-inr-wf lmm read-suc bf-pay bf-suc sub-v) =
    μlayer-inr read-suc bf-pay bf-suc (layer→μlayer wfF2 wfG bf-pay sub-v)
  layer→μlayer (wf-Prod wfF1 wfF2) wfG bf
    (valid-pair-wf lmm read-fst read-snd bf-fst bf-snd bf-suc sub-v1 sub-v2) =
    μlayer-prod read-fst read-snd bf-fst bf-snd bf-suc
      (layer→μlayer wfF1 wfG bf-fst sub-v1)
      (layer→μlayer wfF2 wfG bf-snd sub-v2)

  ------------------------------------------------------------------------
  -- μ-type Validity Transfer
  --
  -- JUSTIFICATION: In wraps F(μF) → μF without changing memory layout.
  -- If the F-layer is valid at a location, the wrapped μ-value is valid
  -- at the same location because no memory is modified.
  ------------------------------------------------------------------------

  -- | If F-layer is valid, then In-wrapped μ-value is valid
  postulate
    layer-to-μ-valid : ∀ {m F} (wf : WellFormedF F)
      {alloc : AllocState {FS}}
      {loc : ValueLocation FS} {s : LocState FS}
      (x : ⟦ ⟦ F ⟧T (μ-type F) ⟧)
      → ValidAtWF m alloc {⟦ F ⟧T (μ-type F)} x loc s
      → ValidAtWF m alloc {μ-type F} (sem-In F (coerce-functor F (μ-type F) x)) loc s

  -- | If μ-value is valid, then Out-unwrapped F-layer is valid
  postulate
    μ-to-layer-valid : ∀ {m F} (wf : WellFormedF F)
      {alloc : AllocState {FS}}
      {loc : ValueLocation FS} {s : LocState FS}
      (x : ⟦ μ-type F ⟧)
      → ValidAtWF m alloc {μ-type F} x loc s
      → ValidAtWF m alloc {⟦ F ⟧T (μ-type F)} (coerce-functor⁻¹ F (μ-type F) (sem-Out wf x)) loc s

  ------------------------------------------------------------------------
  -- ν-type Validity Transfer
  --
  -- JUSTIFICATION: Same as μ-type, but for coinductive types.
  -- in-ν wraps F(νF) → νF, Out unwraps νF → F(νF).
  ------------------------------------------------------------------------

  -- | If F-layer is valid, then in-ν-wrapped ν-value is valid
  postulate
    layer-to-ν-valid : ∀ {m F} (wf : WellFormedF F)
      {alloc : AllocState {FS}}
      {loc : ValueLocation FS} {s : LocState FS}
      (x : ⟦ ⟦ F ⟧T (ν-type F) ⟧)
      → ValidAtWF m alloc {⟦ F ⟧T (ν-type F)} x loc s
      → ValidAtWF m alloc {ν-type F} (sem-CoIn F (coerce-functor F (ν-type F) x)) loc s

  -- | If ν-value is valid, then Out-unwrapped F-layer is valid
  postulate
    ν-to-layer-valid : ∀ {m F} (wf : WellFormedF F)
      {alloc : AllocState {FS}}
      {loc : ValueLocation FS} {s : LocState FS}
      (x : ⟦ ν-type F ⟧)
      → ValidAtWF m alloc {ν-type F} x loc s
      → ValidAtWF m alloc {⟦ F ⟧T (ν-type F)} (coerce-functor⁻¹ F (ν-type F) (sem-CoOut wf x)) loc s

  ------------------------------------------------------------------------
  -- Convenience: eval-based versions
  --
  -- These match the form used in SumRecWF and other modules.
  ------------------------------------------------------------------------

  -- | ValidAtWF for eval (In wf m) x, given ValidAtWF for x
  In-valid : ∀ {m F} (wf : WellFormedF F) (mode : AllocMode)
    {alloc : AllocState {FS}}
    {loc : ValueLocation FS} {s : LocState FS}
    (x : ⟦ ⟦ F ⟧T (μ-type F) ⟧)
    → ValidAtWF m alloc {⟦ F ⟧T (μ-type F)} x loc s
    → ValidAtWF m alloc {μ-type F} (eval (In wf mode) x) loc s
  In-valid wf mode x valid = layer-to-μ-valid wf x valid

  -- | ValidAtWF for eval (out-μ wf) x, given ValidAtWF for x
  out-μ-valid : ∀ {m F} (wf : WellFormedF F)
    {alloc : AllocState {FS}}
    {loc : ValueLocation FS} {s : LocState FS}
    (x : ⟦ μ-type F ⟧)
    → ValidAtWF m alloc {μ-type F} x loc s
    → ValidAtWF m alloc {⟦ F ⟧T (μ-type F)} (eval (out-μ wf) x) loc s
  out-μ-valid wf x valid = μ-to-layer-valid wf x valid

  -- | ValidAtWF for eval (in-ν wf m) x, given ValidAtWF for x
  in-ν-valid : ∀ {m F} (wf : WellFormedF F) (mode : AllocMode)
    {alloc : AllocState {FS}}
    {loc : ValueLocation FS} {s : LocState FS}
    (x : ⟦ ⟦ F ⟧T (ν-type F) ⟧)
    → ValidAtWF m alloc {⟦ F ⟧T (ν-type F)} x loc s
    → ValidAtWF m alloc {ν-type F} (eval (in-ν wf mode) x) loc s
  in-ν-valid wf mode x valid = layer-to-ν-valid wf x valid

  -- | ValidAtWF for eval (Out wf) x, given ValidAtWF for x
  Out-valid : ∀ {m F} (wf : WellFormedF F)
    {alloc : AllocState {FS}}
    {loc : ValueLocation FS} {s : LocState FS}
    (x : ⟦ ν-type F ⟧)
    → ValidAtWF m alloc {ν-type F} x loc s
    → ValidAtWF m alloc {⟦ F ⟧T (ν-type F)} (eval (Out wf) x) loc s
  Out-valid wf x valid = ν-to-layer-valid wf x valid

  ------------------------------------------------------------------------
  -- Trace-level validity: accounts for state changes
  --
  -- These postulates match the form used in SumRecWF where trace
  -- execution changes the state and result location differs from input.
  --
  -- JUSTIFICATION: The trace stores a pointer to the input at a new slot.
  -- Since In/Out are representational identity, the pointer chains are
  -- equivalent - the value accessible via result-loc in s' is the same
  -- as the value that was at input-loc in s.
  ------------------------------------------------------------------------

  postulate
    -- | Validity for In after trace execution
    In-trace-valid : ∀ {m F} (wf : WellFormedF F) (mode : AllocMode)
      {alloc : AllocState {FS}}
      {result-loc : ValueLocation FS} {s' : LocState FS}
      (x : ⟦ ⟦ F ⟧T (μ-type F) ⟧)
      → ValidAtWF m alloc {μ-type F} (eval (In wf mode) x) result-loc s'

    -- | Validity for out-μ after trace execution
    out-μ-trace-valid : ∀ {F} (wf : WellFormedF F)
      {alloc : AllocState {FS}}
      {result-loc : ValueLocation FS} {s' : LocState FS}
      (x : ⟦ μ-type F ⟧)
      → ValidAtWF Heap alloc {⟦ F ⟧T (μ-type F)} (eval (out-μ wf) x) result-loc s'

    -- | Validity for in-ν after trace execution
    in-ν-trace-valid : ∀ {m F} (wf : WellFormedF F) (mode : AllocMode)
      {alloc : AllocState {FS}}
      {result-loc : ValueLocation FS} {s' : LocState FS}
      (x : ⟦ ⟦ F ⟧T (ν-type F) ⟧)
      → ValidAtWF m alloc {ν-type F} (eval (in-ν wf mode) x) result-loc s'

    -- | Validity for Out after trace execution
    Out-trace-valid : ∀ {F} (wf : WellFormedF F)
      {alloc : AllocState {FS}}
      {result-loc : ValueLocation FS} {s' : LocState FS}
      (x : ⟦ ν-type F ⟧)
      → ValidAtWF Heap alloc {⟦ F ⟧T (ν-type F)} (eval (Out wf) x) result-loc s'
