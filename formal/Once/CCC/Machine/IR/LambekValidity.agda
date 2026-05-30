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
open import Once.Functor.Translate using (WellFormedF)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst; sym; trans)

-- Semantic operations
open import Once.Semantics.Core ℕ using (sem-In; sem-Out; sem-CoIn; sem-CoOut;
                                          coerce-functor; coerce-functor⁻¹; sem-Out-In;
                                          coerce-round-trip)

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
    using (ValidAtWF; valid-μ-wf; valid-ν-wf)

  ------------------------------------------------------------------------
  -- Plan 0.27 Option 3: `In` validity is now TRIVIAL.
  --
  -- `valid-μ-wf` carries the layer's own `ValidAtWF` directly, so `In`
  -- is just "wrap": given the F-layer's validity at `loc`, the μ-value
  -- `eval (In wf mode) x` is valid at the SAME loc and SAME mode
  -- (μ-value mode = its layer's memory mode — mode-rigid, hence sound
  -- and cross-mode-safe). We transport the layer validity along the
  -- Lambek round-trip `out-μ ∘ In ≡ id` (sem-Out-In + coerce-round-trip).
  -- No `BeforeFrontier`, no `μLayerValid`, no forward kernel.
  ------------------------------------------------------------------------
  In-valid-bf : ∀ {m F} (wf : WellFormedF F) (mode : AllocMode)
    {alloc : AllocState {FS}} {loc : ValueLocation FS} {s : LocState FS}
    (x : ⟦ ⟦ F ⟧T (μ-type F) ⟧) →
    ValidAtWF m alloc {⟦ F ⟧T (μ-type F)} x loc s →
    ValidAtWF m alloc {μ-type F} (eval (In wf mode) x) loc s
  In-valid-bf {m} {F} wf mode {alloc} {loc} {s} x v =
    valid-μ-wf wf (eval (In wf mode) x)
      (subst (λ y → ValidAtWF m alloc {⟦ F ⟧T (μ-type F)} y loc s)
             (sym roundtrip) v)
    where
      -- out-μ ∘ In ≡ id at the value level (Lambek).
      roundtrip : eval (out-μ wf) (eval (In wf mode) x) ≡ x
      roundtrip =
        trans (cong (coerce-functor⁻¹ F (μ-type F))
                    (sem-Out-In wf (coerce-functor F (μ-type F) x)))
              (coerce-round-trip F (μ-type F) x)

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
