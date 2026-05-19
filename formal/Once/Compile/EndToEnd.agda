-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Compile.EndToEnd
--
-- TYPE-LEVEL OBLIGATION: surface programs are compiled correctly.
--
-- This module composes the two correctness theorems that already exist
-- in the codebase:
--
--   1. Once.Surface.Correct.elaborate-correct
--        : evalSurface ρ e ≡ eval′ (elaborate e) (interpEnv ρ)
--
--   2. Once.CCC.Target.X86-64.Correct.compile-correct
--        : Represents ... (eval ir x) ...
--
-- Until this file existed, the two proofs were freestanding "verification
-- islands" — they could drift apart without any type-error, because
-- nothing required them to be referenced together (cf. Plan 0.4.2 C4,
-- and the historical note in EntryPointCCC.agda about the lost
-- EndToEnd.agda pre-5fac68bb).
--
-- This module RESTORES the type-level obligation. The remaining gap
-- between the two semantics (`Once.Semantics.IR.eval′` over ℤ vs
-- `Once.CCC.Eval.eval` over ℕ — Plan 0.4.2 C1) is now hidden EXPLICITLY
-- in a single named postulate (`eval-IR-bridges-eval-machine`) rather
-- than IMPLICITLY in the absence of any composition theorem.
--
-- When Plan 0.4.2 C1 (semantics consolidation) lands, the postulate
-- becomes provable / removable.
------------------------------------------------------------------------

module Once.Compile.EndToEnd where

open import Data.Product using (_×_; _,_; ∃; ∃-syntax; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Data.Bool using (false)
open import Data.Nat using (ℕ; _<_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

open import Once.Type using (Type; Unit)
open import Once.CCC.IR using (IR; AllocMode; Heap)
open import Once.CCC.IR.Size using (ir-size)

import Once.Semantics.IR as ISem
import Once.Semantics.Machine as MSem
import Once.CCC.Eval as MEval

open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.SMCore
  using (LocState; ValueLocation; StoredValue; SV-Ptr; halted; regs; readReg; Input1)
open import Once.CCC.Machine.Allocation
  using (AllocState; module FrontierInvariant)

open import Once.Surface.Syntax using (Ctx; ∅; Usage; zeroUsage; Expr)
open import Once.Surface.Semantics using (Env; ε; evalSurface)
open import Once.Surface.Elaborate using (elaborate-default; ⟦_⟧ᶜ)

-- Force `elaborate-correct` to live next to the rest of the pipeline:
-- any type drift in Surface/Correct.agda will break this import.
open import Once.Surface.Correct using (elaborate-correct; interpEnv)

-- Per-arch correctness theorem and its runtime contract.
open import Once.CCC.Target.X86-64.RuntimeContract using (RuntimeContract)
import Once.CCC.Target.X86-64.Correct as TargetCorrect
import Once.CCC.Machine.Dispatcher as DispatcherModule

------------------------------------------------------------------------
-- VERIFICATION ROOT
--
-- This module is the single entry point for "build + verify the
-- compiler". The imports below force every freestanding correctness
-- island (parser, typechecker, desugar/optimize/escape/fusion proofs,
-- arith primitives, top-level codegen wire-up) to type-check whenever
-- this file does. Anything not transitively imported here is, by
-- definition, NOT part of the verified compiler.
--
-- If a previously-passing module silently rots (cf. the
-- `distribute`/`elaborate-correct` drift caused by `0ad467ab`), the
-- single `make compiler-x86-64` build will catch it.
------------------------------------------------------------------------

-- Frontend islands (typechecked transitively):
import Once.Parser                  -- parsing rules
import Once.TypeCheck               -- verified type checker
import Once.Surface.Desugar.Correct -- desugar preserves semantics
import Once.Optimize.Correct        -- optimizer preserves semantics
import Once.Escape.Correct          -- escape analysis preserves semantics
import Once.Fusion.Correct          -- fusion preserves semantics

-- Backend wire-up + per-target arithmetic correctness. EntryPointCCC
-- wires codegen + correctness for ALL three targets (X86-64, X86-32,
-- RiscV64) — the compiler supports cross-compilation, so all three must
-- typecheck together.
import Once.CCC.EntryPointCCC       -- compile-correct ↔ codegen wire-up (all targets)
import Once.Arith.SigOp.Proofs      -- per-target arithmetic primitive proofs

------------------------------------------------------------------------
-- THE SEMANTIC BRIDGE (the explicit hole)
--
-- Two evaluators interpret the same IR over different `⟦_⟧` (ℤ vs ℕ).
-- See Plan 0.4.2 C1 (semantics consolidation, ~800-1500 LOC). Until
-- C1 lands, the bridge is asserted as a single named axiom:
--   * `encode-result` — encode the surface-side value (ℤ-flavour) as
--     a machine-side value (ℕ-flavour).
--   * `eval-IR-bridges-eval-machine` — the two evaluators agree mod
--     `encode-result`.
--
-- Both names appear in `make postulates` and are audit-visible. Any
-- claim about end-to-end correctness today factors through these.
------------------------------------------------------------------------

postulate
  encode-result : ∀ {A : Type} → ISem.⟦ A ⟧ → MSem.⟦ A ⟧

  eval-IR-bridges-eval-machine :
    ∀ {A} (ir : IR Unit A) →
    encode-result (ISem.eval′ ir tt) ≡ MEval.eval ir tt

------------------------------------------------------------------------
-- COMPOSED CORRECTNESS (parameterized over arch contract)
--
-- For a closed surface program `e : Expr ∅ zeroUsage A`, evaluated in
-- the empty environment, after compilation and execution from an
-- initial state representing `tt` at `input-loc`, the final state's
-- result location represents `encode-result (evalSurface ε e)`.
--
-- The body composes:
--   (a) compile-correct on `elaborate-default e` — produces a final
--       state representing `MEval.eval (elaborate-default e) tt`.
--   (b) `eval-IR-bridges-eval-machine` — bridges to
--       `encode-result (ISem.eval′ (elaborate-default e) tt)`.
--   (c) `elaborate-correct ε e` — bridges further to
--       `encode-result (evalSurface ε e)`.
--
-- All three links are TYPE-CHECKED here. Drift in any of them is a
-- type error in this module.
------------------------------------------------------------------------

module End-to-End
  {FS : FrameSemantics}
  (runtime : RuntimeContract FS)
  (sigOp-proof : DispatcherModule.SigOpContract.Provider {FS}
                   (RuntimeContract.program-bound runtime))
  where

  open TargetCorrect.Correctness {FS} runtime sigOp-proof

  -- `⟦_⟧` from the machine side is needed for `Represents`.
  open MSem using (⟦_⟧)

  surface-to-machine-correct :
    ∀ {A} (e : Expr ∅ zeroUsage A)
      (mIn : AllocMode)
      (input-loc : ValueLocation FS)
      (s : LocState FS) (alloc : AllocState {FS}) →
    let ir = elaborate-default e in
    Represents mIn alloc tt input-loc s →
    FrontierInvariant.BeforeFrontier {FS} alloc input-loc →
    ir-size ir < RuntimeContract.program-bound runtime →
    halted s ≡ false →
    readReg (regs s) Input1 ≡ SV-Ptr input-loc →
    ∃[ mOut ] ∃[ result-loc ] ∃[ s' ] ∃[ alloc' ]
      Represents mOut alloc'
        (encode-result {A} (evalSurface ε e))
        result-loc s'
  surface-to-machine-correct e mIn input-loc s alloc repr before ir<bound not-halted rdi-eq =
    let
      ir = elaborate-default e

      -- (a) Backend correctness produces Represents about `MEval.eval ir tt`.
      target-result = compile-correct ir mIn tt input-loc s alloc
                        repr before ir<bound not-halted rdi-eq
      mOut       = proj₁ target-result
      result-loc = proj₁ (proj₂ target-result)
      s'         = proj₁ (proj₂ (proj₂ target-result))
      alloc'     = proj₁ (proj₂ (proj₂ (proj₂ target-result)))
      repr-eval  = proj₂ (proj₂ (proj₂ (proj₂ target-result)))
        -- repr-eval : Represents mOut alloc' (MEval.eval ir tt) result-loc s'

      -- (b) Semantic bridge: MEval.eval ir tt ≡ encode-result (ISem.eval′ ir tt)
      bridge-eval : MEval.eval ir tt ≡ encode-result (ISem.eval′ ir tt)
      bridge-eval = sym (eval-IR-bridges-eval-machine ir)

      -- (c) Frontend correctness: evalSurface ε e ≡ ISem.eval′ ir tt.
      -- `interpEnv ε = tt` definitionally.
      ec : evalSurface ε e ≡ ISem.eval′ ir (interpEnv ε)
      ec = elaborate-correct ε e

      -- Combine (b) + (c): MEval.eval ir tt ≡ encode-result (evalSurface ε e)
      combined : MEval.eval ir tt ≡ encode-result (evalSurface ε e)
      combined = trans bridge-eval (cong encode-result (sym ec))
    in
      mOut , result-loc , s' , alloc'
    , subst (λ v → Represents mOut alloc' v result-loc s') combined repr-eval
