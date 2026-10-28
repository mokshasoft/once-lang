-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.NoLeak — the compiler emits no code that leaks (plan 0.123
-- B.0, D6).
--
-- A claim about the compiler beside `correct`, not in `Once.Spec`: the Spec's
-- model has unlimited memory, so leaking is invisible to it. It is stated on
-- the flat machine's runs of the program image the compiler emits, the last
-- level where an allocation and a free are instructions (in the bytes a
-- pop-heap free is the frontier register moving down, like any arithmetic).
--
-- A BLOCK IS AN ALLOCATION EVENT. The abstract allocator is a counter
-- (`next-heap-ref`), so the block step k allocates is named by the counter at
-- k: the n-th allocation of the run, unique and never reused.
--
-- THE CLAIM, for every run from an entry state of every linked program image:
--   * every free hits a live block (allocated, not freed since), so a block
--     is never freed twice;
--   * every block live at some point is freed later in the run, or the run
--     stops first other than by returning: a run that returns (the Host's
--     `leave`, `left`) has nothing live; a run that halts in an operation into
--     `Void` (such as `exit`: the process ends there) is exempt, and so will
--     be one that ends `exhausted` (D347, once the machine has that end).
-- Together: every allocation is freed exactly once. A run that never ends (a
-- server) is covered by the second: each block is freed later in the run.
--
-- Ownership (D6) is how the compiler meets the claim, not part of it.
------------------------------------------------------------------------

module Once.Adequacy.NoLeak where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List)
open import Data.Maybe using (just)
open import Data.Nat using (ℕ; _<_; _≤_)
open import Data.Product using (Σ; ∃-syntax; _×_)
open import Data.Sum using (_⊎_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (¬_)

open import Once.CCC.FrameSemantics using (FrameSemantics; module FrameSemantics)
open FrameSemantics using (frame-word)
open import Once.CCC.Machine.SMCore
open AllocState using (next-heap-ref; frame-slots)
open LocState using (halted; left; regs)
open import Once.CCC.Machine.Locations using (AtDynamic)
open import Once.CCC.Machine.Flat
open import Once.Memory.HeapAddress using (HeapLocation; HeapRef; module HeapRef; hl-ref)
open HeapRef using (ref-id)
open import Once.IR using (IR)
open import Once.IRTy using (Unit)
open import Once.CCC.Codegen.ProgramImage using (program-image)
open import Once.Denotation.Program using (IRFun; irProgram)
open import Once.Compile using (entry-owner)
import Once.Adequacy.ArchCorrectness.FlatCore.RunContext as RunContext

------------------------------------------------------------------------
-- One run: the events, and the claim about them
------------------------------------------------------------------------

module Run (FS : FrameSemantics) (prog : AbstractTrace) where
  open FlatMachine {FS}

  -- The state after k steps of the run from fs₀.
  at : FlatState → ℕ → FlatState
  at fs₀ k = exec-flat k prog fs₀

  -- Step k executes i: the run has not halted at k, and fetches i there.
  Executes : FlatState → ℕ → AbstractInstr → Set
  Executes fs₀ k i = halted (floc (at fs₀ k)) ≡ false × fetch prog (fpc (at fs₀ k)) ≡ just i

  -- A value that points into block r.
  data PointsTo : StoredValue FS → ℕ → Set where
    points : ∀ (hl : HeapLocation) → PointsTo (SV-Ptr (AtDynamic hl)) (ref-id (hl-ref hl))

  -- Step k allocates block r: the counter at k names it (`alloc-impl`).
  Allocates : FlatState → ℕ → ℕ → Set
  Allocates fs₀ k r = Σ ℕ (λ n → Executes fs₀ k (instr-alloc-heap n))
                    × next-heap-ref (falloc (at fs₀ k)) ≡ r

  -- Step k frees block r: a free of the block `Input1` points into.
  Frees : FlatState → ℕ → ℕ → Set
  Frees fs₀ k r = Σ ℕ (λ n → Executes fs₀ k (instr-free-heap n))
                × PointsTo (readReg (regs (floc (at fs₀ k))) Input1) r

  -- Block r is live at k: allocated by an earlier step, freed by none since.
  Live : FlatState → ℕ → ℕ → Set
  Live fs₀ k r = ∃[ j ] (j < k × Allocates fs₀ j r × (∀ i → j < i → i < k → ¬ Frees fs₀ i r))

  -- The run has stopped at k other than by returning: halted, not `left`
  -- (an operation into `Void`; also a machine fault, which `correct` rules
  -- out).
  StoppedAt : FlatState → ℕ → Set
  StoppedAt fs₀ k = halted (floc (at fs₀ k)) ≡ true × left (floc (at fs₀ k)) ≡ false

  record LeakFree (fs₀ : FlatState) : Set where
    field
      -- every free hits a live block: no double free, no free of a stranger
      frees-live : ∀ k r → Frees fs₀ k r → Live fs₀ k r
      -- every live block is freed later, unless the run stops first other
      -- than by returning (a return with a block live is a leak)
      freed      : ∀ k r → Live fs₀ k r
                 → (∃[ j ] (k ≤ j × Frees fs₀ j r)) ⊎ (∃[ j ] (k ≤ j × StoppedAt fs₀ j))

------------------------------------------------------------------------
-- The claim: every run of every linked program image the compiler emits
------------------------------------------------------------------------

NoLeak : Set₁
NoLeak =
  ∀ (FS : FrameSemantics) (tbl : List IRFun) (ir : IR Unit Unit)
  → let module RC = RunContext entry-owner FS (frame-word FS) refl
        prog      = program-image entry-owner (irProgram tbl ir)
    in RC.LinkedImage tbl ir
  → ∀ (fs₀ : FlatMachine.FlatState {FS})
  → RC.EntryLike fs₀ → frame-slots (FlatMachine.falloc {FS} fs₀) ≡ 0
  → Run.LeakFree FS prog fs₀
