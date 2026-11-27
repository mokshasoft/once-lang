-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Implementation — the implementation Spec (plan 0.138 §5, plan 0.123
-- B.0.9): the claims that constrain the compiler but not the meaning, stated
-- beside `correct`. STATEMENTS ONLY: nothing here is proved or postulated,
-- and nothing but `Once.Certified` imports it (`make implementation-gate`).
-- A claim's proof lives elsewhere and becomes a field of `CertifiedBuild`.
--
-- The claims: `NoLeak`, `BoundedStack` and `NoCopy` (below). Next: plan 0.138's layout claim.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- NoLeak — the compiler emits no code that leaks (plan 0.123 B.0, D6).
--
-- A claim about the compiler beside `correct`, not in `Once.Spec`: the Spec's
-- model has unlimited memory, so leaking is invisible to it. It is stated on
-- the flat machine's runs of the program image the compiler emits, the last
-- level where an allocation and a free are instructions (in the bytes a
-- pop-heap free is the frontier register moving down, like any arithmetic).
-- Plan 0.146 (D467): the image is the linear core's, of the module's sources
-- at their `main`, room-checked (`LinCore.ExprImage.imageAt`, what
-- `LinCore.Emit` writes); it was master's (`ProgramImage.program-image`).
--
-- A BLOCK IS AN ALLOCATION EVENT. The abstract allocator is a counter
-- (`next-heap-ref`), so the block step k allocates is named by the counter at
-- k: the n-th allocation of the run, unique and never reused.
--
-- THE CLAIM, for every run from an entry state of every program image the
-- compiler emits (D429 amended, D474: a safety claim, at every step):
--   * every free hits a live block (allocated, not freed since), so a block
--     is never freed twice;
--   * at every step every live block is reachable from what the state holds
--     (its registers, its live frames' slots, through heap cells): nothing
--     allocated is garbage; a server holds its state and nothing of the
--     rounds before. (A stale pointer, a register or dead slot still naming a
--     block, only adds reachability: the claim is the leak half of D429's
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
open AllocState using (next-heap-ref; frame-slots; saved-frames)
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
import Once.LinCore.Lower
import Once.LinCore.Loader
open import Once.CCC.Label using (e-fn; e-thunk)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Binary.Pointwise using (Pointwise)
open import Data.Product using (proj₂)
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

  -- D429 amended, D474: what the state still holds — a block a root points into
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
      -- D429 amended (a safety claim, at every step), D474: every live block is
      -- one the state still holds — nothing allocated is garbage
      reachable  : ∀ k r → Live fs₀ k r → Reach (at fs₀ k) r

  -- D502: the stack the state holds is its active calls' frames, each the size a
  -- static `F` gives the point it is at: the current frame `F` of the pc, every
  -- saved frame `F` of its pending return (the caller's frame, restored there)
  record FramesAt (F : ℕ → ℕ) (fs : FlatState) : Set where
    field
      current : frame-slots (falloc fs) ≡ F (fpc fs)
      saved   : Pointwise (λ fr r → proj₂ fr ≡ F r) (saved-frames (falloc fs)) (FlatState.fret fs)

  -- D501: the run enters none of the blocks `js` (by their index in the image's
  -- universe: a block's entry `e-fn (nameOf j)`, its trampoline's `e-thunk (tl j)`).
  -- A block is entered only by its entry instruction (calls target entry labels,
  -- a block ends in a return): entering none, the run is never inside one.
  record CopyFree (js : List ℕ) (fs₀ : FlatState) : Set where
    field
      no-entry : ∀ k j b → j ∈ js → ¬ Executes fs₀ k (instr-ctrl (c-entry (e-fn (Once.LinCore.Lower.nameOf (fs-numerics FS) Once.LinCore.Loader.bw j)) b))
      no-tramp : ∀ k j b → j ∈ js → ¬ Executes fs₀ k (instr-ctrl (c-entry (e-thunk (Once.LinCore.Lower.tl (fs-numerics FS) Once.LinCore.Loader.bw j)) b))

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

------------------------------------------------------------------------
-- BoundedStack — the stack never slowly grows (plan 0.157 D502, the user's).
--
-- `NoLeak` says nothing about the stack (frames are only its roots), and static
-- per-function depths (D490) do not rule out slow growth: a loop round leaving a
-- word, a return not restoring the stack exactly, a trampoline path leaving one.
-- The claim: for each program there is ONE static map `F` from program points to
-- frame sizes such that at every step of every run the stack in use is exactly
-- the active calls' frames, the current one `F` of the pc, each saved one `F` of
-- its pending return. The depth is then a function of where the run is (its pc
-- and its pending returns), never of how long it has run: a loop's rounds hold
-- the same frames; without recursion the bound is one constant (the image is
-- finite, so `F` takes finitely many values on it). A stop the Spec allows (room
-- exhausted) is still a failure for a controller; this rules out reaching it by
-- growth.
------------------------------------------------------------------------

BoundedStack : Set₁
BoundedStack =
  ∀ (FS : FrameSemantics) (m : Resolved) (srcs : List CompiledSrc) → srcModule Heap false m ≡ inj₂ srcs
  → ∀ {T : Type} (pm : T <: EffUU) → mainOf srcs ≡ just (T , pm)
  → ∃[ F ] (let module RC = RunContext entry-owner FS (frame-word FS) refl
            in ∀ (fs₀ : FlatMachine.FlatState {FS})
            → RC.EntryLike fs₀ → frame-slots (FlatMachine.FlatState.falloc {FS} fs₀) ≡ 0
            → ∀ k → halted (FlatMachine.FlatState.floc {FS} (Run.at FS (EmittedImage FS srcs pm) fs₀ k)) ≡ false
            → Run.FramesAt FS (EmittedImage FS srcs pm) F (Run.at FS (EmittedImage FS srcs pm) fs₀ k))

------------------------------------------------------------------------
-- NoCopy — a linear program runs without a copy (plan 0.157 D6, D500, D501).
--
-- Linearity is not enforced; it is GUARANTEED to pay: a program the compiler
-- gives no "not linear (a copy here)" warning (`LinCore.ExprImage.linearSites`
-- empty: what `--require-linear` refuses otherwise) never copies a value with
-- cells. A copy at a type without cells is words (D6's exemption by type), so
-- the claim is about the copy blocks at types with cells (`ExprImage.cellCopies`):
-- no run of the image, from an entry state as `NoLeak`'s, enters one.
-- (The image level is proved, `LinCore.NoCopyImage`; the flat run's, owed.)
------------------------------------------------------------------------

NoCopy : Set₁
NoCopy =
  ∀ (FS : FrameSemantics) (m : Resolved) (srcs : List CompiledSrc) → srcModule Heap false m ≡ inj₂ srcs
  → ∀ {T : Type} (pm : T <: EffUU) → mainOf srcs ≡ just (T , pm)
  → Once.LinCore.ExprImage.linearSites (fs-numerics FS) (Once.LinCore.ExprBuild.srcOrder (fs-numerics FS) srcs []) pm ≡ []
  → let module RC = RunContext entry-owner FS (frame-word FS) refl
    in ∀ (fs₀ : FlatMachine.FlatState {FS})
  → RC.EntryLike fs₀ → frame-slots (FlatMachine.FlatState.falloc {FS} fs₀) ≡ 0
  → Run.CopyFree FS (EmittedImage FS srcs pm)
      (Once.LinCore.ExprImage.cellCopies (fs-numerics FS) (Once.LinCore.ExprBuild.srcOrder (fs-numerics FS) srcs []) pm) fs₀
