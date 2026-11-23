-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.ArchCorrectness.Interface — plan 0.146 B1.7c (D463): ★ WHAT
-- AN ARCH IMPLEMENTS.
--
-- Everything above the arch is arch-neutral: the compiled program's image is
-- an abstract trace (`AbstractTrace`), and the flat machine runs it. An arch
-- is one `ArchSim`:
--
--   * its flat machine (`FS`: frames, words, the interpretation), its slot
--     size, and where `main` starts (`entry-frame`, `entry-regs`);
--   * over its code generator (`B`: `Target.Backend`, the file the compiler
--     writes), the table the machine reads of the file's blocks (`block-env`),
--     with the table fact its simulation reads (`ArithTable`) for any block
--     list the program's calls name (`table`);
--   * its machine: the code of an abstract trace (`compile`), its step on
--     that code under a block table (`δ`), and its loader's state (`init`);
--     the backend's file runs as that machine (`run-file`, `file-runs`), and
--     is what the assembler demands when its image's symbols are (`file-wf`);
--   * ★ one theorem (`sim`): an image whose shape facts hold (`Emitted`), at a
--     table it names, whose flat run is sound and shows a program's meaning at
--     every budget (the flat theorem, as `FlatTop` proves it of the linear
--     core's image), runs on the machine with that program's trace.
--
-- (The bytes below `compile` — decode, assemble, the CPU — are master's
-- `CPU.Interface.ArchSemantics`.)
------------------------------------------------------------------------

{-# OPTIONS --guardedness #-}

module Once.Adequacy.ArchCorrectness.Interface where

open import Data.Nat using (ℕ; suc; _≤_)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.String using (String)
open import Data.Bool using (false)
import Data.List.Relation.Unary.All
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Once.Spec.Name using (CanonicalName)
open import Once.Spec.Trace using (Tr; _⊑ᵗ⟨_⟩_)
open import Once.CCC.FrameSemantics using (FrameSemantics; fs-numerics; fs-ffi; module FrameSemantics)
open import Once.CCC.Machine.SMCore
open import Once.CCC.Machine.Flat using (module FlatMachine)
open import Once.CCC.Codegen.RoomChecks using (room-checks)
open import Once.CCC.Codegen.FlatStepLemmas using (module FlatStepsAPI)
open import Once.Adequacy.FlatEvents using (module FlatEventTrace)
open import Once.Adequacy.MachineTrace using (Step; module Machine)
open import Once.Denotation.ProgramTrace using (⟦_⟧IRᵗ)
open import Once.Arith.Machine.IR using (ArithBlock)
open import Once.Adequacy.BlockTable using (SigNamed)
open import Once.Target.Backend using (Backend; module Backend; file-table)
open import Once.CCC.Codegen.ImageExterns using (ImageWF)
open import Once.SigOp.Info using (SigOpInfo; External; module SigOpInfo)
open import Once.Target.Symbol using (once-symbol-path)
open import Once.Denotation.Program using (IRProgram; runIR)
open import Once.Denotation.Approx using (Ap; approx; endAp)
open import Data.Unit using (⊤)
import Once.IR.Semantics.Trace as TM
import Once.Adequacy.ArchCorrectness.FlatCore.RunContext
import Once.CCC.Machine.FlatStoreWF

-- where a run starts: outside every frame, nothing in its heap or log (the
-- state `LinCore.Start.start-fs` and master's `FlatFromObs.start-flat` are)
start-at : ∀ (FS : FrameSemantics) → FrameSemantics.Frame FS → Registers FS → FlatMachine.FlatState {FS}
start-at FS entry-frame entry-regs =
  FlatMachine.mkFlat {FS} (mkLocState entry-regs (λ _ _ → nothing) (λ _ → nothing) false [] false false)
                          (mkAllocState entry-frame [] 0 0 1 (λ _ → 0) (λ _ → false)) 0

-- a program's meaning at a budget, from the empty log
obs-at : ∀ (FS : FrameSemantics) → IRProgram → ℕ → TM.Run (Ap ⊤)
obs-at FS q k = TM.run (FrameSemantics.fs-interp FS) [] (approx k (runIR (fs-numerics FS) (fs-ffi FS) q))

-- ★ the flat theorem of an image for a program: at every budget its flat run
-- shows the program's meaning, and runs as long as it does
FlatShows : ∀ (FS : FrameSemantics) → AbstractTrace → FlatMachine.FlatState {FS} → IRProgram → Set
FlatShows FS image start q =
  ∀ k → Σ ℕ λ N → (FlatEventTrace.flat-events {FS} (suc N) image start ≡ (proj₁ (obs-at FS q k) , endAp (proj₂ (obs-at FS q k))))
                × (endAp (proj₂ (obs-at FS q k)) ≡ nothing → k ≤ FlatEventTrace.flat-ctrls {FS} (suc N) image start)

-- an external op's symbol is no block's (the file's table misses it)
ExtMiss : ∀ (FS : FrameSemantics) {P : Set} → (String → Maybe P) → AbstractTrace → Set
ExtMiss FS env prog = ∀ {A B} (si : SigOpInfo A B) k → External (SigOpInfo.sem si) → FlatMachine.fetch {FS} prog k ≡ just (instr-sigop si)
                    → env (once-symbol-path (SigOpInfo.name si)) ≡ nothing

record ArchSim (o : CanonicalName) (B : Backend) : Set₁ where
  field
    -- the flat machine, its slots, main's start
    FS          : FrameSemantics
    slot-size   : ℕ
    word-eq     : FrameSemantics.frame-word FS ≡ slot-size
    entry-frame : FrameSemantics.Frame FS
    entry-regs  : Registers FS

    -- the table the backend's file of a block list is (`Backend.file-table`), as the machine reads it
    block-env : List (String × Backend.Payload B) → String → Maybe (Backend.Payload B)

    -- what the simulation reads of the table, for any block list the calls name
    ArithTable : AbstractTrace → (String → Maybe (Backend.Payload B)) → Set
    table      : ∀ prog (bs : List ArithBlock) → Data.List.Relation.Unary.All.All (SigNamed bs) prog
               → ExtMiss FS (block-env (file-table (Backend.payload B) bs)) prog
               → ArithTable prog (block-env (file-table (Backend.payload B) bs))

    -- the machine: an abstract trace's code, its step under a table, the loader's state
    Code    : Set
    compile : AbstractTrace → Code
    S       : Set
    δ       : (String → Maybe (Backend.Payload B)) → Code → S → Step S
    init    : S

    -- ★ the file the backend writes runs as the machine on the trace's code (`run-file`: the
    -- CPU's run of the file from its entry, master's `Compile.run-file`)
    run-file  : Backend.File B → Tr ⊤
    file-runs : ∀ t (bs : List ArithBlock) (ex : List String)
              → run-file (Backend.file B t (file-table (Backend.payload B) bs) ex)
                ≡ Machine.trace (δ (block-env (file-table (Backend.payload B) bs)) (compile t)) init

    -- ★ the backend's file of a room-checked image (it starts with its check) is what the
    -- assembler demands when the image's symbols are (`ImageWF`: defined once, resolved, valid)
    -- (D483: past the check, the start: its code makes the file's entry, whatever the check's)
    file-wf : ∀ k b (t″ : AbstractTrace) (bs : List ArithBlock) (ex : List String)
            → ImageWF (instr-room k ∷ instr-ctrl (c-start b) ∷ t″) bs ex
            → Backend.AsmWF B (Backend.file B (instr-room k ∷ instr-ctrl (c-start b) ∷ t″) (file-table (Backend.payload B) bs) ex)
    -- …and so is a library's (empty) file (D465)
    empty-wf : Backend.AsmWF B (Backend.empty B)

  start : FlatMachine.FlatState {FS}
  start = start-at FS entry-frame entry-regs

  open Once.Adequacy.ArchCorrectness.FlatCore.RunContext o FS slot-size word-eq using (Emitted; EntryLike)

  field
    -- the start is a run's start (no frame owed, nothing held: `RunContext.EntryLike`),
    -- its store well formed (D468 3c4: what the allocator expansion's simulation reads)
    entry-like : EntryLike start
    entry-wf   : Once.CCC.Machine.FlatStoreWF.FlatWF FS start
    entry-cl   : Once.CCC.Machine.FlatStoreWF.sv-below FS (AllocState.next-heap-ref (FlatMachine.FlatState.falloc start)) (FlatMachine.FlatState.fclosure start)
    -- ★ THE ARCH'S THEOREM: the flat theorem of a well-shaped image (its start
    -- first, at main's budget `b`) becomes the machine's
    sim : ∀ (q : IRProgram) (b : ℕ) (tail : AbstractTrace) (env : String → Maybe (Backend.Payload B))
        → let image = instr-ctrl (c-start b) ∷ tail in
          Emitted image → ArithTable (room-checks image) env
        → FlatStepsAPI.Sound {FS} image start → FlatShows FS image start q
        → Machine.trace (δ env (compile (room-checks image))) init ⊑ᵗ⟨ _≡_ ⟩ ⟦ just q ⟧IRᵗ (fs-numerics FS) (FrameSemantics.fs-interp FS)
