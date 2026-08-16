-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface
--
-- WHAT A TARGET OWES THE EVENT ENGINE, as three records (plan 0.65 G2 item 4,
-- slice 3).
--
-- WHY RECORDS AND NOT MODULE PARAMETERS, which is what they were first. The
-- engine's dispatch is ~19 mutually recursive members, and EVERY ONE of them
-- carries the module's whole telescope. At 64 loose parameters that needs more
-- than 5.5 GiB to typecheck and the OOM cap kills the run — measured
-- 2026-08-15, and measured again after splitting the dispatch into its own
-- file, which changes nothing: peak memory is driven by the TELESCOPE, not by
-- file size. `ConcFlatSim` typechecks the same body comfortably with ~14
-- parameters, which is the corroborating number.
--
-- Bundled, the engine's telescope is ten entries and the dispatch's is one.
-- Nothing about the CONTENT changes: the engine `open`s these records, so
-- every name in its body reads exactly as it did when they were parameters.
--
-- The three are ordered by dependency, and the order is forced:
--
--   Emitter    the instruction type and how a trace lowers into it. Mentions
--              no machine state at all — this is the emitter's law surface,
--              the same one `FlatComposition` takes.
--   Machine    the state, its readouts, and how a step and a fuel-bounded run
--              behave. Needs `Emitter` for `Instr` and the fetch.
--   TraceLoop  the event layer: the arith payload, the call classifier, the
--              real extractor and env. Needs both.
------------------------------------------------------------------------

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Bool using (Bool; true; false)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List using (List; []; _∷_; _++_)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.SMCore using (AbstractTrace; AbstractInstr; instr-sigop)
open import Once.CCC.Label using (Label; _≡ᵇᴸ_)
open import Once.SigOp.Info using (SigOpInfo)
open import Once.Target.Symbol using (once-symbol-path)
open import Once.Denotation.Trace using (SigOpEvent)
import Once.Adequacy.ArchCorrectness.FlatCore.HeadView as HV

module Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface
  (FS : FrameSemantics)
  (Reg : Set)
  where

------------------------------------------------------------------------
-- THE EMITTER, and the ISA only as far as the label scans can see it.
-- `FlatComposition`'s parameter list, verbatim, plus the label scan as the
-- CORRESPONDENCE names it.
------------------------------------------------------------------------
record Emitter : Set₁ where
  field
    Instr : Set
    compile-abstract : AbstractInstr → List Instr
    compile-trace : AbstractTrace → List Instr
    ct-nil  : compile-trace [] ≡ []
    ct-cons : ∀ i is → compile-trace (i ∷ is) ≡ compile-abstract i ++ compile-trace is
    -- the machine's instruction fetch, by its three defining equations
    -- (`refl` at every arch — they all index a list)
    mfetch      : List Instr → ℕ → Maybe Instr
    mfetch-nil  : ∀ n → mfetch [] n ≡ nothing
    mfetch-zero : ∀ x xs → mfetch (x ∷ xs) zero ≡ just x
    mfetch-suc  : ∀ x xs n → mfetch (x ∷ xs) (suc n) ≡ mfetch xs n
    -- the ONE view of an instruction this development needs, and the laws that
    -- replace the constructor enumeration
    is-label?     : Instr → Bool
    mk-label      : Label → Instr
    find-label-go : Label → List Instr → ℕ → Maybe ℕ
    find-label-nil : ∀ (t : Label) (xi : ℕ) → find-label-go t [] xi ≡ nothing
    skip-law : ∀ (t : Label) (i : Instr) (rest : List Instr) (xi : ℕ)
             → is-label? i ≡ false
             → find-label-go t (i ∷ rest) xi ≡ find-label-go t rest (suc xi)
    label-hit : ∀ (ℓ t : Label) (rest : List Instr) (xi : ℕ)
              → (ℓ ≡ᵇᴸ t) ≡ true
              → find-label-go t (mk-label ℓ ∷ rest) xi ≡ just xi
    label-miss : ∀ (ℓ t : Label) (rest : List Instr) (xi : ℕ)
               → (ℓ ≡ᵇᴸ t) ≡ false
               → find-label-go t (mk-label ℓ ∷ rest) xi ≡ find-label-go t rest (suc xi)
    -- how THIS emitter lowers each abstract instruction, as far as the scans
    -- can see it. 39 clauses at the arch, none of them in the engine.
    headView : ∀ i → HV.HeadView FS Instr compile-abstract is-label? mk-label i
    -- …and the scan as `CompiledCorr.code-eq` names it, plus the fact that it
    -- IS the one `FlatComposition` reasons about. The second is `refl` at every
    -- arch, but the engine cannot see that through two abstract fields, and
    -- `load-code-addr` is exactly where the two meet.
    find-label : List Instr → Label → Maybe ℕ
    find-label-def : ∀ prog t → find-label prog t ≡ find-label-go t prog 0

------------------------------------------------------------------------
-- THE MACHINE: its state, the readouts the correspondence needs, and how a
-- step and a fuel-bounded run behave.
--
-- The six `exec` readouts are the only thing the engine needs from `exec`'s
-- DEFINITION. An abstract field does not reduce, so the equations have to be
-- handed over rather than computed — which is also what keeps the block
-- backbone `with`-free. Each is one line at an arch (`refl` after rewriting
-- the boolean).
------------------------------------------------------------------------
record Machine (E : Emitter) : Set₁ where
  open Emitter E using (Instr; mfetch)
  field
    State : Set
    rreg : State → Reg → ℕ
    memory : State → (ℕ → Maybe ℕ)
    xhalted : State → Bool
    xpc : State → ℕ
    -- WHERE AN UNSPILLED RETURN ADDRESS LIVES (plan 0.65 G2, 2026-08-16), and a
    -- MACHINE field because it is exactly an ABI fact: between a call and the
    -- callee's body marker the head pending return has not reached its stack
    -- cell, and each arch says where it is instead — memory on x86-64 (`call`
    -- pushed it), the link register on RISC-V (`jalr` wrote `ra`). Consumed by
    -- `CompiledCorr.ret-eq` as `RetAddrs`' per-arch head row.
    link-claim : State → ℕ → ℕ → Set
    mexecInstr : List Instr → State → Instr → Maybe State
    exec : ℕ → List Instr → State → Maybe State
    exec-zero      : ∀ prog s → exec 0 prog s ≡ just s
    exec-halted    : ∀ n prog s → xhalted s ≡ true → exec (suc n) prog s ≡ just s
    exec-end       : ∀ n prog s {s'} → xhalted s ≡ false
                   → mfetch prog (xpc s) ≡ nothing
                   → exec (suc n) prog s ≡ just s' → xhalted s' ≡ true
    exec-stuck     : ∀ n prog s j → xhalted s ≡ false → mfetch prog (xpc s) ≡ just j
                   → mexecInstr prog s j ≡ nothing → exec (suc n) prog s ≡ nothing
    exec-step-halt : ∀ n prog s j s₁ → xhalted s ≡ false → mfetch prog (xpc s) ≡ just j
                   → mexecInstr prog s j ≡ just s₁ → xhalted s₁ ≡ true
                   → exec (suc n) prog s ≡ just s₁
    exec-step-run  : ∀ n prog s j s₁ → xhalted s ≡ false → mfetch prog (xpc s) ≡ just j
                   → mexecInstr prog s j ≡ just s₁ → xhalted s₁ ≡ false
                   → exec (suc n) prog s ≡ exec n prog s₁

------------------------------------------------------------------------
-- THE TRACE LOOP: `RunTraceCore.RunTrace`'s telescope, the real extractor and
-- env this arch runs with, how a SigOp is lowered, and the ONE ISA
-- enumeration the backbone needs.
------------------------------------------------------------------------
record TraceLoop (E : Emitter) (M : Machine E) : Set₁ where
  open Emitter E using (Instr; compile-abstract)
  open Machine M using (State; mexecInstr; xhalted)
  field
    Payload : Set
    matchCall : Instr → Maybe String
    ret-past : State → State
    dispatchArith : Payload → State → State
    -- pinned, not quantified: the SigOp contracts are false over an arbitrary
    -- `ev`/`env` (2026-07-30)
    ev-arch : String → State → List SigOpEvent
    arith-env : List Instr → String → Maybe Payload
    -- HOW A SIGOP IS LOWERED, the same on every target: to ONE call by symbol.
    sigop-call : String → Instr
    sigop-lowering : ∀ {A B} (si : SigOpInfo A B)
                   → compile-abstract (instr-sigop si)
                     ≡ sigop-call (once-symbol-path (SigOpInfo.name si)) ∷ []
    sigop-matchCall : ∀ lbl → matchCall (sigop-call lbl) ≡ just lbl
    -- A step that leaves the machine RUNNING was not a `call-sym`:
    -- `execInstr (call-sym _)` always halts. One clause per instruction at the
    -- arch, and the only place the engine would need the instruction set.
    nonhalt-noncall : ∀ prog s j {s₁} → mexecInstr prog s j ≡ just s₁
                    → xhalted s₁ ≡ false → matchCall j ≡ nothing
