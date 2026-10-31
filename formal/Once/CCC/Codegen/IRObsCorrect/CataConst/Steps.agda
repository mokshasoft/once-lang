-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.IRObsCorrect.CataConst.Steps   (plan 0.135 S3, cata M1)
--
-- ONE STRAIGHT STEP AS A SEGMENT (`Resusp.Base.SegA`): what it leaves alone
-- below a base allocator `a₀` at frontier `n`, and what it does to the
-- frame, the stack frontier and the heap frontier. Four shapes cover the
-- cata's straight rows: a step that writes no memory, a slot store at
-- or above the frontier, an allocation, and an indirect store into a block
-- fresh at the base. Segments compose by `segA-∘`, so a run's preservation
-- is the composite of its rows' and never re-reads the run.
------------------------------------------------------------------------

open import Once.Spec.Name using (CanonicalName)

import Data.List as DL
open import Once.Denotation.Program using (IRFun)
module Once.CCC.Codegen.IRObsCorrect.CataConst.Steps (o : CanonicalName) (tbl : DL.List IRFun) where

open import Once.CCC.Codegen.IRObsCorrect.Machine o tbl
open import Once.CCC.Codegen.IRObsCorrect.Resusp.Base o tbl using (module ResuspBaseC)
open import Once.CCC.Machine.SMCore
  using (LocState; module LocState; AbstractInstr; AllocState; module AllocState; readReg; Output; Input1; store-at-slot; store-indirect; store-indirect-suc; instr-alloc-heap; mov-to-output; sv-as-loc; writeReg-same)
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.Locations using (AtDynamic)
open import Once.CCC.Machine.FrameFree using (FrameFreeI; exec-abstract-preserves-next-slot)
open import Once.CCC.Machine.SMPrimitives using (EffectPreservesNextHeapRef; instr-effect)
open import Once.Memory.HeapAddress using (HeapLocation; module HeapLocation; module HeapRef)
open HeapLocation using (heap-ref)
open HeapRef using (ref-id)

module CataStepsC {FS : FrameSemantics} where

  open Core {FS}
  open Mach {FS}
  open ResuspBaseC {FS} using (St; X; SegA; SRun)
  open LocState using (regs)
  open AllocState using (current-frame; next-slot; next-heap-ref)

  -- a step that writes no memory and allocates nothing
  seg-q : ∀ {a₀ : AllocState {FS}} {n : ℕ} (i : AbstractInstr) (t : FlatState)
        → InstrNoHeapWrite i → instr-writes-slot i ≡ nothing → FrameFreeI i
        → EffectPreservesNextHeapRef (instr-effect i)
        → SegA a₀ n t (St i t)
  seg-q i t nhw nws ff eh = record
    { mem  = λ loc _ → mem-untouched i (floc t) (falloc t) loc nhw nws
    ; cf   = exec-abstract-preserves-frame i (floc t) (falloc t)
    ; sf   = exec-abstract-preserves-saved i (floc t) (falloc t)
    ; ns   = exec-abstract-preserves-next-slot i (floc t) (falloc t) ff
    ; href = ≤-reflexive (sym (exec-abstract-preserves-heap-ref i (floc t) (falloc t) eh))
    }

  -- a slot store at or above the frontier
  seg-store : ∀ {a₀ : AllocState {FS}} {n : ℕ} (k : ℕ) (t : FlatState)
            → current-frame (falloc t) ≡ current-frame a₀ → n ≤ k
            → SegA a₀ n t (St (store-at-slot k) t)
  seg-store {a₀} {n} k t cf n≤k = record
    { mem  = λ loc bf → store-slot-preserves-before k (floc t) (record a₀ { next-slot = n }) (falloc t) loc cf n≤k bf
    ; cf   = refl ; sf = refl ; ns = refl ; href = ≤-refl }

  -- an allocation
  seg-alloc : ∀ {a₀ : AllocState {FS}} {n : ℕ} (t : FlatState) → SegA a₀ n t (St (instr-alloc-heap 2) t)
  seg-alloc t = record
    { mem  = λ loc _ → mem-untouched (instr-alloc-heap 2) (floc t) (falloc t) loc nhw-instr-alloc-heap refl
    ; cf   = refl ; sf = refl ; ns = refl ; href = n≤1+n _ }

  -- an indirect store into a block fresh at the base
  seg-sind : ∀ {a₀ : AllocState {FS}} {n : ℕ} (t : FlatState) (hl : HeapLocation)
           → sv-as-loc (readReg (regs (floc t)) Input1) ≡ just (AtDynamic hl)
           → next-heap-ref a₀ ≤ ref-id (heap-ref hl)
           → SegA a₀ n t (St store-indirect t)
  seg-sind {a₀} {n} t hl rdi fresh = record
    { mem  = λ loc bf → store-ind-preserves-before (floc t) (record a₀ { next-slot = n }) (falloc t) hl loc rdi fresh bf
    ; cf   = refl ; sf = refl ; ns = refl ; href = ≤-refl }

  seg-sind-suc : ∀ {a₀ : AllocState {FS}} {n : ℕ} (t : FlatState) (hl : HeapLocation)
               → sv-as-loc (readReg (regs (floc t)) Input1) ≡ just (AtDynamic hl)
               → next-heap-ref a₀ ≤ ref-id (heap-ref hl)
               → SegA a₀ n t (St store-indirect-suc t)
  seg-sind-suc {a₀} {n} t hl rdi fresh = record
    { mem  = λ loc bf → store-ind-suc-preserves-before (floc t) (record a₀ { next-slot = n }) (falloc t) hl loc rdi fresh bf
    ; cf   = refl ; sf = refl ; ns = refl ; href = ≤-refl }

  -- `mov-to-output` copies Input1
  out-movout : ∀ (s : LocState FS) (a : AllocState {FS})
             → readReg (regs (X mov-to-output s a)) Output ≡ readReg (regs s) Input1
  out-movout s a = writeReg-same (regs s) Output (readReg (regs s) Input1)

  -- two silent runs, one after the other (give the implicits: `SRun` is a
  -- definition, so inferring them unfolds the machine states)
  s-++ : ∀ {prog a b} {x y z : FlatState} → SRun prog a x y → SRun prog b y z → SRun prog (a + b) x z
  s-++ (r₁ , e₁ , l₁) (r₂ , e₂ , l₂) = FlatSteps-++ r₁ r₂ , trans (chain-events-++ r₁ r₂) (cong₂ _++_ e₁ e₂) , trans l₂ l₁
