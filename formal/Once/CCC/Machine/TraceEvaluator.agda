-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Machine.TraceEvaluator
--
-- A `TraceEvaluator` bundles the per-step state evolution of a single
-- AbstractTrace, factoring out the four obligations Bridge A producers
-- otherwise re-prove in isolation:
--
--   * alloc-correct           (final-alloc matches exec-trace's output)
--   * trace-twf               (state-threaded TraceWF chain)
--   * mem-preserved-before    (caller-frontier locations read unchanged)
--   * not-halted-final        (halted false ⇒ halted final-state false)
--
-- See `plans/0.16-bridge-a-postulate-audit.md` (Pattern 3, Recommendation
-- 1) and memory [[project-bridge-a-audit]].
--
-- Design notes
-- ------------
-- `halted-preserved` is derivable from `trace-wf` via
-- `exec-trace-preserves-halted-WF`, so the smart constructor
-- `mk-trace-evaluator` computes it automatically. Producers only have
-- to discharge the three remaining obligations
-- (trace-wf / exec-alloc-eq / mem-preserved-before) — each of which
-- requires the per-step state trajectory the audit identifies as the
-- root cause of the scattered postulates.
--
-- The record does NOT replace `IRResultBase`. Instead, producers
-- construct a `TraceEvaluator` and project its fields into
-- `IRResultBase`'s `alloc-correct`, `trace-twf`, `mem-preserved-before`
-- and `not-halted` slots. This keeps the public interface stable while
-- consolidating the coupled proof work.
------------------------------------------------------------------------

module Once.CCC.Machine.TraceEvaluator where

open import Data.Bool using (Bool; false)
open import Data.Product using (proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.SMCore hiding (AllocMode; Stack; Heap)
open import Once.CCC.Machine.Allocation hiding (AllocMode)

import Once.CCC.Machine.SMPrimitives as SMP

module TraceEvaluatorDef {FS : FrameSemantics} where
  open FrameSemantics FS
  open FrontierInvariant {FS}
  open MemOps {FS}
  open AbstractExec {FS}
  open SMP.TracePrimitives {FS}

  ------------------------------------------------------------------------
  -- TraceEvaluator
  --
  -- Bundles the per-instruction state trajectory used by Bridge A
  -- producers. `final-state` / `final-alloc` are the producer's chosen
  -- post-trace state representation (possibly a synthetic
  -- `record alloc { next-heap-ref = ... }` rather than the raw
  -- exec-trace output); `exec-state-eq` / `exec-alloc-eq` tie them to
  -- the operational semantics.
  ------------------------------------------------------------------------

  record TraceEvaluator (trace : AbstractTrace)
                        (s : LocState FS)
                        (alloc : AllocState {FS}) : Set where
    inductive
    field
      final-state : LocState FS
      final-alloc : AllocState {FS}
      trace-wf    : TraceWF s alloc trace
      exec-state-eq : proj₁ (exec-trace trace s alloc) ≡ final-state
      exec-alloc-eq : proj₂ (exec-trace trace s alloc) ≡ final-alloc
      mem-preserved-before :
        ∀ (loc : ValueLocation FS) → BeforeFrontier alloc loc →
        readLoc final-state loc ≡ readLoc s loc
      halted-preserved :
        halted s ≡ false → halted final-state ≡ false

  open TraceEvaluator public

  ------------------------------------------------------------------------
  -- Smart constructor: derives `halted-preserved` from `trace-wf` via
  -- the universal `exec-trace-preserves-halted-WF` lemma, so producers
  -- only have to discharge the three semantic obligations.
  ------------------------------------------------------------------------

  mk-trace-evaluator :
    ∀ {trace : AbstractTrace}
      {s : LocState FS}
      {alloc : AllocState {FS}}
    (final-state : LocState FS)
    (final-alloc : AllocState {FS})
    (trace-wf    : TraceWF s alloc trace)
    (exec-state-eq : proj₁ (exec-trace trace s alloc) ≡ final-state)
    (exec-alloc-eq : proj₂ (exec-trace trace s alloc) ≡ final-alloc)
    (mem-preserved-before :
       ∀ (loc : ValueLocation FS) → BeforeFrontier alloc loc →
       readLoc final-state loc ≡ readLoc s loc) →
    TraceEvaluator trace s alloc
  mk-trace-evaluator {trace = trace} {s = s} {alloc = alloc}
                     fs fa twf state-eq alloc-eq mpb =
    record
      { final-state = fs
      ; final-alloc = fa
      ; trace-wf    = twf
      ; exec-state-eq = state-eq
      ; exec-alloc-eq = alloc-eq
      ; mem-preserved-before = mpb
      ; halted-preserved = λ h-eq →
          subst (λ s' → halted s' ≡ false) state-eq
            (exec-trace-preserves-halted-WF trace s alloc h-eq twf)
      }
