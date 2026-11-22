-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Implementation — the implementation Spec (plan 0.138 §5, plan 0.123
-- B.0.9): the claims that constrain the compiler but not the meaning, stated
-- beside `correct`. STATEMENTS ONLY: nothing here is proved or postulated,
-- and nothing but `Once.Certified` imports it (`make implementation-gate`).
-- A claim's proof lives elsewhere and becomes a field of `CertifiedBuild`.
--
-- The claims: `NoLeak` (below). Next: plan 0.138's layout claim.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- NoLeak — the compiler emits no code that leaks (plan 0.123 B.0, D6).
--
-- A claim about the compiler beside `correct`, not in `Once.Spec`: the Spec's
-- model has unlimited memory, so leaking is invisible to it. It is stated on
-- the flat machine's runs of the program image the compiler emits, the last
-- level where an allocation and a free are instructions (in the bytes a
-- pop-heap free is the frontier register moving down, like any arithmetic).
-- Plan 0.146 (D465): the image is the linear core's, of the module's sources
-- at their `main`, room-checked (`LinCore.ExprImage.imageAt`, what
-- `LinCore.Emit` writes); it was master's (`ProgramImage.program-image`).
--
-- A BLOCK IS AN ALLOCATION EVENT. The abstract allocator is a counter
-- (`next-heap-ref`), so the block step k allocates is named by the counter at
-- k: the n-th allocation of the run, unique and never reused.
--
-- THE CLAIM, for every run from an entry state of every program image the
-- compiler emits (D427 amended, D472: a safety claim, at every step):
--   * every free hits a live block (allocated, not freed since), so a block
--     is never freed twice;
--   * at every step every live block is reachable from what the state holds
--     (its registers, its live frames' slots, through heap cells): nothing
--     allocated is garbage; a server holds its state and nothing of the
--     rounds before. (A stale pointer, a register or dead slot still naming a
--     block, only adds reachability: the claim is the leak half of D427's
--     "exactly", the other half being memory safety, which the machine's
--     gates give.)
--
-- Ownership (D6) is how the compiler meets the claim, not part of it.
------------------------------------------------------------------------

module Once.Implementation where

open import Data.Bool using (true; false)
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
open import Once.Memory.HeapAddress using (HeapLocation; HeapRef; module HeapRef; hl-ref; heap-loc; mkHeapRef)
open HeapRef using (ref-id)
open import Data.List using ([])
open import Data.Product using (_,_)
open import Data.Sum using (inj₂)
open import Once.IR using (Heap)
open import Once.Spec.Type using (Type)
open import Once.Spec.Sub using (_<:_)
open import Once.CCC.FrameSemantics using (fs-numerics)
open import Once.CCC.Codegen.RoomChecks using (room-checks)
open import Once.Parser.Module.Core using (Resolved)
open import Once.CompileSrc using (CompiledSrc; srcModule; mainOf)
open import Once.Compile using (EffUU)
open import Once.Compile.Emit using (entry-owner)
import Once.LinCore.ExprBuild
import Once.LinCore.ExprImage
import Once.Adequacy.ArchCorrectness.FlatCore.RunContext as RunContext

------------------------------------------------------------------------
-- One run: the events, and the claim about them
------------------------------------------------------------------------

module Run (FS : FrameSemantics) (prog : AbstractTrace) where
  open FlatMachine {FS}
  open FlatState using (floc; fpc; falloc)

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

  -- D427 amended, D472: what the state still holds — a block a root points into
  -- (a register, the closure register, a slot inside a live frame's window), or
  -- one a held block's cell points into
  data Reach (fs : FlatState) : ℕ → Set where
    r-reg  : ∀ (x : AbstractReg) r → PointsTo (readReg (regs (floc fs)) x) r → Reach fs r
    r-clo  : ∀ r → PointsTo (FlatState.fclosure fs) r → Reach fs r
    r-slot : ∀ f k r {v} → ExecFinal.in-window {FS} (ExecFinal.live-frames {FS} (falloc fs)) f k ≡ true
           → LocState.stackMem (floc fs) f k ≡ just v → PointsTo v r → Reach fs r
    r-heap : ∀ r′ o r {v} → Reach fs r′ → LocState.heapMem (floc fs) (heap-loc (mkHeapRef r′) o) ≡ just v
           → PointsTo v r → Reach fs r

  record LeakFree (fs₀ : FlatState) : Set where
    field
      -- every free hits a live block: no double free, no free of a stranger
      frees-live : ∀ k r → Frees fs₀ k r → Live fs₀ k r
      -- D427 amended (a safety claim, at every step), D472: every live block is
      -- one the state still holds — nothing allocated is garbage
      reachable  : ∀ k r → Live fs₀ k r → Reach (at fs₀ k) r

------------------------------------------------------------------------
-- The claim: every run of every program image the compiler emits
------------------------------------------------------------------------

-- the image the compiler emits for a module whose sources compile, at their `main`
-- (`LinCore.Emit.fileOf`'s, before the arch lowers it)
EmittedImage : FrameSemantics → (srcs : List CompiledSrc) → ∀ {T : Type} → T <: EffUU → AbstractTrace
EmittedImage FS srcs pm =
  room-checks (Once.LinCore.ExprImage.imageAt (fs-numerics FS) (Once.LinCore.ExprBuild.srcOrder (fs-numerics FS) srcs []) pm)

NoLeak : Set₁
NoLeak =
  ∀ (FS : FrameSemantics) (m : Resolved) (srcs : List CompiledSrc) → srcModule Heap false m ≡ inj₂ srcs
  → ∀ {T : Type} (pm : T <: EffUU) → mainOf srcs ≡ just (T , pm)
  → let module RC = RunContext entry-owner FS (frame-word FS) refl
    in ∀ (fs₀ : FlatMachine.FlatState {FS})
  → RC.EntryLike fs₀ → frame-slots (FlatMachine.FlatState.falloc {FS} fs₀) ≡ 0
  → Run.LeakFree FS (EmittedImage FS srcs pm) fs₀
