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
-- blocked by the fact that μ-type F and ⟦ F ⟧TI (μ-type F) are
-- different Type values, even though they have identical memory layout.
--
-- These postulates are JUSTIFIED because:
-- 1. Both types have identical memory representation (Lambek iso)
-- 2. ValidAtWF only depends on memory layout, not type identity
-- 3. The machine operations (In, Out, etc.) are no-ops at runtime
--
-- COMPARISON TO PREVIOUS POSTULATES:
-- - OLD: lambek-iso-semantic for ANY IR - too general
-- - NEW: specific to In/Out operations with WellFormedFI evidence
------------------------------------------------------------------------

open import Once.CanonicalName using (CanonicalName)

module Once.CCC.Machine.IR.LambekValidity (o : CanonicalName) where

open import Data.Nat using (ℕ)
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.SMCore hiding (AllocMode; Stack; Heap)
-- Plan 0.52 M2: machine values are IRTy values (⟦_⟧ᴵ), renamed to ⟦_⟧ locally.
open import Once.Semantics.Machine using () renaming (⟦_⟧ᴵ to ⟦_⟧)
open import Once.IR
import Once.CCC.Eval as Ev
import Once.Semantics.Machine as EvV
open import Once.CCC.Machine.Allocation hiding (AllocMode)
-- Plan 0.52 M2: μ-type / ν-type / ⟦_⟧TI / WellFormedFI are the IRTy tier,
-- and come from Once.IR; Once.Type supplies only the surface `Type`.
open import Once.Type using (Type)
open import Once.IRTy using (WellFormedFI-irrelevant; ⌈_⌉; ⌈_⌉F; ⌈⟧TI-commute)
open import Once.IRTy.WF using (wf-⌈⌉)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst; sym; trans)
open import Relation.Binary.PropositionalEquality.Properties using (subst-sym-subst)

-- Semantic operations
open import Once.Word using (Carrier)
open import Once.Float.Decimal using (Decimal)
open import Once.Semantics.Value Carrier Carrier using (sem-In; sem-Out; sem-CoIn; sem-CoOut;
                                          coerce-functor; coerce-functor⁻¹; sem-Out-In;
                                          sem-CoOut-CoIn; coerce-round-trip)

------------------------------------------------------------------------
-- LambekValidityImpl
--
-- Provides ValidAtWF transfer lemmas for Lambek isomorphisms.
-- These are postulated because the type indices prevent direct proof.
------------------------------------------------------------------------

module LambekValidityImpl {FS : FrameSemantics} (program-bound : ℕ) where
  -- Plan 0.73 (D113): `eval` is target-relative at `Float` — a float literal
  -- has no format-free machine value. Inside a module already fixed to this
  -- target's `FrameSemantics`, THE evaluator is the one at its float format,
  -- so it is named once here and used unqualified below.
  eval : ∀ {A B} → IR A B → EvV.⟦ A ⟧ᴵ → EvV.⟦ B ⟧ᴵ
  eval = Ev.eval (Once.CCC.FrameSemantics.fs-numerics FS)

  open FrameSemantics FS
  open FrontierInvariant {FS}

  open import Once.CCC.Machine.ClosureWellFormed o
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
  In-valid-bf : ∀ {m F} (wf : WellFormedFI F) (mode : AllocMode)
    {alloc : AllocState {FS}} {loc : ValueLocation FS} {s : LocState FS}
    (x : ⟦ ⟦ F ⟧TI (μ-type F) ⟧) →
    ValidAtWF m alloc {⟦ F ⟧TI (μ-type F)} x loc s →
    ValidAtWF m alloc {μ-type F} (eval (In wf mode) x) loc s
  In-valid-bf {m} {F} wf mode {alloc} {loc} {s} x v =
    valid-μ-wf wf (eval (In wf mode) x)
      (subst (λ y → ValidAtWF m alloc {⟦ F ⟧TI (μ-type F)} y loc s)
             (sym roundtrip) v)
    where
      -- out-μ ∘ In ≡ id at the value level (Lambek).
      --
      -- Plan 0.52 M2: `eval` runs the SURFACE helpers at `⌈F⌉F` and transports
      -- the `⟦F⟧TI`-shaped operand along `⌈⟧TI-commute` (the μ RESULT needs no
      -- transport — `⌈ μ-type F ⌉ = μ-type ⌈F⌉F` definitionally). So the round
      -- trip is the surface one CONJUGATED by that transport, and the two
      -- transports cancel by `subst-sym-subst`. Nothing about Lambek changed.
      roundtrip : eval (out-μ wf) (eval (In wf mode) x) ≡ x
      roundtrip =
        trans (cong (λ y → subst (λ T → EvV.⟦ T ⟧) (sym eq)
                                 (EvV.coerce-functor⁻¹ ⌈ F ⌉F ⌈ μ-type F ⌉ y))
                    (EvV.sem-Out-In (wf-⌈⌉ wf)
                       (EvV.coerce-functor ⌈ F ⌉F ⌈ μ-type F ⌉ x')))
              (trans (cong (subst (λ T → EvV.⟦ T ⟧) (sym eq))
                           (EvV.coerce-round-trip ⌈ F ⌉F ⌈ μ-type F ⌉ x'))
                     (subst-sym-subst eq))
        where
          eq = ⌈⟧TI-commute F (μ-type F)
          x' = subst (λ T → EvV.⟦ T ⟧) eq x

  ------------------------------------------------------------------------
  -- Plan 0.27 Option 3: the four representational-transfer postulates
  -- (layer-to-μ-valid, μ-to-layer-valid, layer-to-ν-valid,
  -- ν-to-layer-valid) and the `In-valid` wrapper were REMOVED — they are
  -- subsumed by the real `In-valid-bf` / `out-μ-valid` / `in-ν-valid` /
  -- `Out-valid` below (valid-μ-wf/valid-ν-wf now carry the layer's own
  -- ValidAtWF, so In/out-μ/in-ν/Out are wrap/unwrap, not postulates).
  ------------------------------------------------------------------------

  -- | ValidAtWF for eval (out-μ wf) x — Plan 0.27 Option 3: REAL, not via
  -- the μ-to-layer-valid postulate. out-μ is "unwrap": invert valid-μ-wf
  -- (the only constructor for μ-type) and transport the stored layer
  -- ValidAtWF along WellFormedFI-irrelevant (stored wf ≡ out-μ's wf).
  out-μ-valid : ∀ {m F} (wf : WellFormedFI F)
    {alloc : AllocState {FS}}
    {loc : ValueLocation FS} {s : LocState FS}
    (x : ⟦ μ-type F ⟧)
    → ValidAtWF m alloc {μ-type F} x loc s
    → ValidAtWF m alloc {⟦ F ⟧TI (μ-type F)} (eval (out-μ wf) x) loc s
  out-μ-valid {m} {F} wf {alloc} {loc} {s} x (valid-μ-wf wf' .x layerV) =
    subst (λ w → ValidAtWF m alloc {⟦ F ⟧TI (μ-type F)} (eval (out-μ w) x) loc s)
          (WellFormedFI-irrelevant wf' wf)
          layerV

  -- | ValidAtWF for eval (in-ν wf m) x — Plan 0.27 Option 3: REAL (dual
  -- of In-valid-bf). in-ν is "wrap"; transport the layer validity along
  -- the ν Lambek round-trip `Out ∘ in-ν ≡ id` (sem-CoOut-CoIn + coerce).
  in-ν-valid : ∀ {m F} (wf : WellFormedFI F) (mode : AllocMode)
    {alloc : AllocState {FS}}
    {loc : ValueLocation FS} {s : LocState FS}
    (x : ⟦ ⟦ F ⟧TI (ν-type F) ⟧)
    → ValidAtWF m alloc {⟦ F ⟧TI (ν-type F)} x loc s
    → ValidAtWF m alloc {ν-type F} (eval (in-ν wf mode) x) loc s
  in-ν-valid {m} {F} wf mode {alloc} {loc} {s} x v =
    valid-ν-wf wf (eval (in-ν wf mode) x)
      (subst (λ y → ValidAtWF m alloc {⟦ F ⟧TI (ν-type F)} y loc s)
             (sym roundtrip) v)
    where
      -- The ν dual, same conjugation.
      roundtrip : eval (Out wf) (eval (in-ν wf mode) x) ≡ x
      roundtrip =
        trans (cong (λ y → subst (λ T → EvV.⟦ T ⟧) (sym eq)
                                 (EvV.coerce-functor⁻¹ ⌈ F ⌉F ⌈ ν-type F ⌉ y))
                    (EvV.sem-CoOut-CoIn (wf-⌈⌉ wf)
                       (EvV.coerce-functor ⌈ F ⌉F ⌈ ν-type F ⌉ x')))
              (trans (cong (subst (λ T → EvV.⟦ T ⟧) (sym eq))
                           (EvV.coerce-round-trip ⌈ F ⌉F ⌈ ν-type F ⌉ x'))
                     (subst-sym-subst eq))
        where
          eq = ⌈⟧TI-commute F (ν-type F)
          x' = subst (λ T → EvV.⟦ T ⟧) eq x

  -- | ValidAtWF for eval (Out wf) x — Plan 0.27 Option 3: REAL (dual of
  -- out-μ-valid). Out is "unwrap": invert valid-ν-wf, transport along
  -- WellFormedFI-irrelevant.
  Out-valid : ∀ {m F} (wf : WellFormedFI F)
    {alloc : AllocState {FS}}
    {loc : ValueLocation FS} {s : LocState FS}
    (x : ⟦ ν-type F ⟧)
    → ValidAtWF m alloc {ν-type F} x loc s
    → ValidAtWF m alloc {⟦ F ⟧TI (ν-type F)} (eval (Out wf) x) loc s
  Out-valid {m} {F} wf {alloc} {loc} {s} x (valid-ν-wf wf' .x layerV) =
    subst (λ w → ValidAtWF m alloc {⟦ F ⟧TI (ν-type F)} (eval (Out w) x) loc s)
          (WellFormedFI-irrelevant wf' wf)
          layerV

  ------------------------------------------------------------------------
  -- Plan 0.27 Option 3: the four hypothesis-free trace-level postulates
  -- (In-trace-valid, out-μ-trace-valid, in-ν-trace-valid, Out-trace-valid)
  -- were REMOVED. The heap-identity producers in SumRecWF (run-In,
  -- run-out-μ, run-in-ν, run-Out) now establish the result validity for
  -- real via the wrap/unwrap lemmas above, transported across
  -- mov-to-output by validityWF-mem-only.
  ------------------------------------------------------------------------
