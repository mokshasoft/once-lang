-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF
--
-- THE FLAT MACHINE'S WELL-FORMEDNESS LAYER, arch-generic
-- (Plan 0.65 G1d, 2026-08-12).
--
-- Everything a REACHABLE state of an EMITTED program satisfies, driven by
-- `RunAt`: the segment discipline (`FrameWF`, `RetMatch`, `run-frame-wf`), the two
-- pointer invariants (`StackPtrWF` via `stack-ptr-step`, `PtrBoundsWF` via
-- `ptr-bounds-step`), the shape-table consistency (`run-shape-check`), and the
-- dataflow disciplines the correspondence consumes at its load/store/branch
-- sites (`slot-read-*`, `{load,store}-indirect{,-suc}-target-*`,
-- `branch-tag-scrutinee-wf`).
--
-- WHY IT IS HERE. It was 1,076 of `X86-64.ConcFlatSim`'s 2,832 lines and it
-- mentions the machine ZERO times — no `X.State`, no register, no state
-- literal, and not even the correspondence (`FlatCorr`, `BlockStep`,
-- `HeapView` do not occur). It is about the ABSTRACT machine and the EMITTER,
-- both of which the three arches share, so it was never x86-64's to own. Ten
-- of `ConcFlatSim`'s imports are machine-specific and NONE of them is needed
-- here — that is the mechanical statement of the same fact.
--
-- The measurement also corrected the plan: `ConcFlatSim` was called "the most
-- machine-dependent, last", and it is the LEAST — 115 machine-mentioning code
-- lines out of 2,833, four percent, in two clumps with this block between them.
--
-- It also DECLARES the seven arch-generic residuals (G1d step 2), which were
-- `ConcFlatSim`'s. They are assumed once here rather than once per arch — the
-- second payoff this plan predicted for extracting a core at all. The companion
-- `RunWFTypes` module that carried them as parameters through step 1 is gone
-- with them.
------------------------------------------------------------------------


open import Once.CCC.FrameSemantics using (FrameSemantics; module FrameSemantics)
open FrameSemantics using (frame-word)
open import Data.Nat using (ℕ; _<_)
open import Relation.Binary.PropositionalEquality using (_≡_)
-- …and the pieces the RESOURCE parameter's type needs. Imported UNAPPLIED, so
-- the module's own `FS`/`word-eq` can be threaded into them by Agda's
-- telescoping (`RC.RunAt o FS word-eq …`) — a parameter's type is elaborated
-- before the body, where the applied `open import … FS word-eq` has not run.
open import Once.Spec.Name using (CanonicalName)

open import Data.List using (List; []; _∷_)
open import Data.Unit using (tt)
open import Relation.Nullary using (yes; no)

module Once.Adequacy.ArchCorrectness.FlatCore.RunWF
  (o : CanonicalName)
  (FS : FrameSemantics)
  (slot-size : ℕ)
  (word-eq : frame-word FS ≡ slot-size)
  where


open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Bool using (Bool; true; false; _∨_; not)
open import Data.Nat using (zero; suc)
open import Relation.Binary.PropositionalEquality using (refl; sym; trans; cong; subst; subst₂)

open import Once.CCC.Machine.SMCore
open AllocState using (frame-slots; saved-frames; block-size; next-heap-ref; current-frame)
open LocState using (heapMem; regs; stackMem; halted)
open import Once.CCC.Machine.Locations using (AtDynamic; Slot; AtStack; ValueLocation)
open import Once.Memory.HeapAddress using (HeapLocation; module HeapRef; module HeapLocation; sucHL; offsetHL)
open HeapLocation using (heap-offset; heap-ref)
open HeapRef using (ref-id)
open MemOps {FS} using (readLoc)
open ExecFinal {FS} using (exec-load-with-value; exec-load-via-resolved; exec-load-suc-via-resolved; exec-store-via-resolved; exec-store-suc-via-resolved; exec-load-at-resolved; exec-store-at-resolved; frame-gate; heap-gate; gate-or; exec-store-in-block; in-block?; exec-addr-at-resolved; exec-addr-in-block)
open import Once.Memory.HeapAddress using (offsetHL)
open import Data.Bool using (T)
open import Data.Nat.Properties using (<ᵇ⇒<)
open AbstractExec {FS} using (exec-load-from-slot-with-value; exec-restore-input-with-value; unread?; exec-sigop-faults-of; decode-at; sigop-gate; exec-sigop-faults)
open FrameSemantics FS using (Frame)
open import Once.CCC.Machine.Flat
open FlatMachine {FS}
open FlatState using (fpc; fclosure; floc; fret; falloc; flink)
open import Once.CCC.Machine.FlatStoreWF FS
open import Data.Product using (Σ; ∃; _,_; _×_; proj₁; proj₂)
open import Once.CCC.Machine.FrameFree
open import Data.List.Relation.Unary.All using () renaming (All to AllL)
open import Once.CCC.Machine.InstrSlot
open import Once.CCC.Machine.FlatStackSlot FS
open SameFrames using (sf-slots; sf-saved; sf-ret)
open import Once.CCC.Machine.FlatPtrBounds FS
open import Once.CCC.Machine.AllocMin using (AllocMinI)
open import Once.CCC.Codegen.LabelSeg
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Once.CCC.Codegen.SlotSeg
open SegState using (cur; saved)
open SlotBelow using (below)
open import Data.List.Relation.Unary.All using () renaming (map to All-mapL)
open import Once.CCC.Codegen.CallOK using (InstrOK; Calls; calls-⊤)
open import Once.SigOp.Info using (module SigOpInfo; SigOpInfo; effect; Pure)
open SigOpInfo using (baseA)
open import Once.Arith.SigOp.Compare using (cmp-of)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.List.Relation.Unary.Any.Properties using () renaming (++⁺ˡ to Any++⁺ˡ; ++⁺ʳ to Any++⁺ʳ)
open import Once.CCC.Label using (_≡ᵇᴱ_; ≡ᵇᴱ-refl; e-fn; EntryId; LabelId; e-thunk)
open import Once.CanonicalName using (_≟ᶜ_)
open import Once.IRTy using (_≟IRTy_; Unit)
open import Once.Denotation.Program using (IRFun; irProgram; Linked; LinkedAt; LinkedAt-at; LinkedProgram; Leaves; leaves-map)
open Once.Denotation.Program.IRFun using (fbody; fcod; fdom; fname)
open import Once.Contract using (ISig)
open import Data.List.Relation.Unary.All.Properties using (++⁺)
open import Once.IR using (IR)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Once.Type using (fits-int; fits-float)

-- NON-HALTING ⇒ NON-CALL: `call-sym` is the ONLY instruction `matchCall` accepts,
-- and `execInstr (call-sym _)` always sets `halted := true`. So any step that
-- leaves the machine running (`halted s₁ ≡ false`) cannot have been a `call-sym`,
-- i.e. `matchCall j ≡ nothing`. (The one absurd case is `call-sym`, ruled out by
-- the halt clash; every other instruction is `matchCall … = nothing` definitionally.)
open import Once.Adequacy.ArchCorrectness.FlatCore.RunContext o FS slot-size word-eq
open Emitted using (em-budget; em-zero; em-start; em-image; em-alloc; em-calls; em-guard)
open RunAt using (run-em; run-reach)
open import Once.CCC.Codegen.FlatStepLemmas using (module FlatStepsAPI)
open FlatStepsAPI {FS} using ([]; _∷_)

------------------------------------------------------------------------
-- THE ARCH-GENERIC RESIDUALS (Plan 0.65 G1d step 2, 2026-08-12).
--
-- These seven were declared in `X86-64.ConcFlatSim`, and the block's own
-- comments already said why that was the wrong home: "No `X.State` in the
-- type: this is a fact about the ABSTRACT machine". Checked mechanically, not
-- taken on the comment's word — none of the seven mentions `X.State`,
-- `HeapView`, `RTx` or the correspondence in its TYPE (the flag that first
-- fired on `call-site-shape` was its own prose).
--
-- Left where they were, riscv64 and x86-32 would each have had to declare
-- their own copy of each, and the ledger would have grown threefold for facts
-- that are one fact. Here they are assumed ONCE and, when discharged,
-- discharged once for all three arches — the second payoff this plan predicted
-- for extracting a core at all.
--
-- The two that stayed behind are `arith-sigop-run` (D351) and
-- `external-sigop-contract`: both quantify over `HeapView` and the x86-64
-- arith runtime, so they are genuinely x86-64's.
emitted-call-fn-resolves : ∀ prog (fs : FlatState) (f : CanonicalName) → RunAt prog fs
                         → fetch prog (fpc fs) ≡ just (instr-ctrl (c-call-fn f))
                         → Σ ℕ (λ j → find-fn prog f ≡ just j)
emitted-call-fn-resolves prog fs f r ftq = em-calls (run-em r) (fpc fs) f ftq

-- B1.7b (D456): THE RUN'S FACTS ARE THE MACHINE'S GATES. A reached step does
-- not fault (its run is sound, `run-sound`), and the machine faults a call
-- that names no body and a return that is not owed or not at the reservation
-- in force (`Flat.do-call`, `do-ret`); so at a reached call or return the gate
-- passed. They were the image's (`Emitted.em-call-site`, `em-ret-owes`,
-- `em-ret-budget`), owed by the linear core's.
step-sound : ∀ prog (fs : FlatState) {i : AbstractInstr} → RunAt prog fs → halted (floc fs) ≡ false
           → fetch prog (fpc fs) ≡ just i → LocState.faulted (floc (flat-exec-instr i prog fs)) ≡ false
step-sound prog fs r h ftq = run-sound r ((h , ftq) ∷ [])

call-site-shape : ∀ prog (fs : FlatState) → RunAt prog fs → halted (floc fs) ≡ false
                → fetch prog (fpc fs) ≡ just instr-call-closure
                → Σ HeapLocation (λ hl → Σ LabelId (λ ℓ → Σ ℕ (λ j →
                    (fclosure fs ≡ SV-Ptr (AtDynamic hl))
                    × (heapMem (floc fs) (sucHL hl) ≡ just (SV-Code ℓ))
                    × (find-thunk prog ℓ ≡ just j))))
call-site-shape prog fs r h ftq = call-ok prog fs (step-sound prog fs r h ftq)

private
  ret-gate : ∀ prog (fs : FlatState) (b : ℕ) → RunAt prog fs → halted (floc fs) ≡ false
           → fetch prog (fpc fs) ≡ just (instr-ctrl (c-ret b))
           → Σ ℕ (λ rpc → Σ (List ℕ) (λ rest → fret fs ≡ rpc ∷ rest)) × (b ≡ frame-slots (falloc fs))
  ret-gate prog fs b r h ftq = ret-ok b fs (step-sound prog fs r h ftq)

ret-site-owes : ∀ prog (fs : FlatState) (b : ℕ) → RunAt prog fs → halted (floc fs) ≡ false
              → fetch prog (fpc fs) ≡ just (instr-ctrl (c-ret b))
              → Σ ℕ (λ rpc → Σ (List ℕ) (λ rest → fret fs ≡ rpc ∷ rest))
ret-site-owes prog fs b r h ftq = proj₁ (ret-gate prog fs b r h ftq)

ret-budget-matches : ∀ prog (fs : FlatState) (b : ℕ) → RunAt prog fs → halted (floc fs) ≡ false
                   → fetch prog (fpc fs) ≡ just (instr-ctrl (c-ret b))
                   → b ≡ frame-slots (falloc fs)
ret-budget-matches prog fs b r h ftq = proj₂ (ret-gate prog fs b r h ftq)

  -- D367: the two shape-check obligations of plan 0.62 (M2b, the emitter's
  -- shape check, and M3, run consistency) STOOD HERE as postulates, and M2b was
  -- FALSE: `c-start` drops every claim, so `terminal ∘ ⟨ id , id ⟩` fails the
  -- check under every label environment and the postulate derived ⊥. The site
  -- facts they fed are THEOREMS now — read off the program's own run, which
  -- never faults (`RunAt.run-sound`, from `ir-obs-correct`); see below.
  -- `branch-tag-label-miss` RETIRED 2026-08-01 — a theorem now (`go-miss` in
  -- `tag-branch-step`): not-taken rides the label-free
  -- `block-step-c-branch-tag-nz`, taken-plus-missing is the je-halt template
  -- on `find-label-none-corr`, and the bad-read routes fold into
  -- `branch-tag-bad` (they never depended on the label).


  -- `stack-ptr-case` / `ptr-bounds-case` RETIRED with item 6: the case steps
  -- of both invariants are absurd on `FrameFreeI` now.

  -- The load/branch DISCIPLINE residuals are GONE (Plan 0.62 wiring,
  -- 2026-08-02; D367): `load-indirect{,-suc}-target-ptr`,
  -- `store-indirect{,-suc}-target-ptr`, `slot-read-written`,
  -- `out-nz-output-word` and `branch-tag-scrutinee-wf` are THEOREMS below:
  -- each failing shape is a FAULT of the abstract machine, and the run never
  -- faults.

  -- A slot the emitted code READS is frame-live (`slot < frame-slots`): reads stay
  -- inside the frame the prologue reserved. Conditioned on the SITE (a property of
  -- emitted programs, not of arbitrary states) and covering the empty case too —
  -- which used to be what let the empty-slot reads be proved via
  -- `slot-empty-stop`. That lemma is GONE (Plan 0.54 rung D): the empty case is
  -- now UNREACHABLE instead, because `site-ok` requires a claim at every slot
  -- read and `MeetsSlot` refutes a claim at an unwritten slot. The slot MUST be the fetched instruction's own
  -- (`slot-of i ≡ just slot`): quantified over an unrelated `slot` this claims
  -- `slot < frame-slots` for every slot, which is inconsistent (take `slot ≡
  -- frame-slots`) — it would prove the whole correspondence vacuously.
  -- MEMORY EXHAUSTION (plan 0.54 rung D) — the price of "the two regions grow
  -- towards each other", and the ONLY thing the layout separation assumes. The
  -- ONE allocating instruction the emitter produces has room between the heap
  -- frontier and the stack's high-water mark; the
  -- disjointness facts that used to be postulated are derived from the carried
  -- `sep` these keep true. A real runtime failure mode (OOM / stack overflow),
  -- not a claim about addresses.
  -- Plan 0.54 rung D step 3: the heap's room is measured against the stack's
  -- HIGH-WATER MARK, not the current `%rsp` — a region the stack has already
  -- visited keeps its (dead) contents, so only the VIRGIN part of the gap is
  -- available. That is also what discharges the fresh block's freshness on the
  -- concrete side, which is why `alloc-heap-fresh-x86` is gone.
  -- (`heap-room` is a MODULE PARAMETER now — see the header. It was the one
  -- resource bound stated inside the correspondence rather than at the apex.)
  -- RETIRED 2026-07-31 (plan 0.54 rung D, item 2): `stack-room` / `frame-room` /
  -- `pop-room`, and the alloc-stack FRESH-FRAME pair `alloc-stack-fresh-{abs,x86}`
  -- together with `alloc-stack-entry`, all conditioned a frame-op site — and an
  -- EMITTED program has none (`FrameFree` / `frame-op-absurd`). The fresh-frame
  -- pair was the one place where the correspondence assumed something FALSE of a
  -- re-entered frame (both halves false, agreeing); it is gone with its site.
  -- RETIRED 2026-07-30 (plan 0.54 rung D step 3): "the fresh block is UNWRITTEN on
  -- the concrete side" was `alloc-heap-fresh-x86`, and stated over the region at or
  -- above `%r15` it was FALSE — a deep call that returns leaves written cells below
  -- the current `%rsp`, and the heap can bump into them. It is now a THEOREM about
  -- the region the stack has never reached: `FlatCorr.untouched` on
  -- `[hfront, lo)`, which `heap-room` puts the fresh cells inside.
  -- (Its abstract counterpart — nothing references or has written the not-yet-
  -- allocated block — was already PROVEN, `FlatStoreWF`.)
  -- `lea-indexed-wf` RETIRED 2026-08-01: `lea-indexed` had NO PRODUCER — the
  -- cata codegen walks heap-LINKED stacks (`push2`/`pop2`) — and the
  -- cursor-discipline residual died with its site (the instruction itself was
  -- deleted by plan 0.135).

  -- RETIRED 2026-07-31 (plan 0.54 rung D, item 2): the MATCHED PROLOGUE/EPILOGUE
  -- family — `dealloc-stack-restores`, `pop-frame-restores`, `dealloc-stack-full`,
  -- `pop-frame-empty`, `pop-frame-saved`. Each was a pairing property of emitted
  -- code at a frame-op site, and emitted code contains no frame op.
  -- `load-const-float` RETIRED 2026-08-03 (D079): a float CONSTANT is a
  -- 64-bit pattern, so codegen emits it as an ordinary immediate instead of
  -- `ud2` — both machines now load the same word and continue. (Float
  -- ARITHMETIC remains unsupported; that is a separate, unemitted path.)

  -- ARITH SIGOP interpretation contract (D061): the internal-producer obligation,
  -- discharged OFFLINE from the arith proofs (dispatch-arith-preserves + arith-block-
  -- correct). For a Pure SigOp, the arith-env maps its symbol to the block `pl`, and
  -- dispatching `pl` yields the CompiledCorr of the flat post-state. `sigop-step` proves
  -- the run-events mechanics AROUND this (pc-alignment + run-events-arith), so this
  -- states exactly the residual arith obligation — nothing about the machine loop.


--
-- `FrameFreeI` (`Once.CCC.Machine.FrameFree`) and its emitter induction live
-- below this layer
-- (`Once.CCC.Codegen.FrameFreeTrace`) — this is a fact about `ir-to-trace`, not
-- about the machine. Here it is only APPLIED, at the `Emitted` witness the run
-- context already carries.
-- Plan 0.63 step 2b: also needs HEAP MODE, because `lea-slot` joined the ⊥
-- set — it is emitted, but only by the four Stack-mode clauses. `RunAt`
-- carries `run-heap`, so every call site already has the evidence.
-- Plan 0.63 (the flip): this now yields the EMITTER FENCE (`EmittableI`), not
-- semantic frame-freeness — an emitted trace really does contain the two
-- closure markers, and they really do move the frame. The fossils are
-- unchanged, so every ⊥-route below still closes; what changed is that the
-- markers now need REAL clauses instead of `⊥-elim`.
------------------------------------------------------------------------
-- D244/D245: THE PROGRAM IMAGE's per-instruction facts. `main`'s unit, then
-- each table entry as its marker and its own unit (emitted under its own
-- name), so an `All` over the image is `main`'s, then per function the
-- marker's (it moves only the frame) and that unit's.
------------------------------------------------------------------------
frame-op-absurd : ∀ prog (fs : FlatState) (i : AbstractInstr) (em : Emitted prog)
                → fetch prog (fpc fs) ≡ just i → ImageI i
frame-op-absurd prog fs i em ftq = fetch-All {prog = prog} {k = fpc fs} (em-image em) ftq

-- Plan 0.107: THE START IS AT pc 0 AND NOWHERE ELSE. The rest of the image is
-- units (`ProgramImage.image-body`), and no unit holds a start.
start-at-zero : ∀ prog (k b : ℕ) → Emitted prog
              → fetch prog k ≡ just (instr-ctrl (c-start b)) → k ≡ 0
start-at-zero prog k b em ftq = em-start em k b ftq

-- …and pc 0 holds it.
fetch-zero : ∀ prog → (em : Emitted prog)
           → fetch prog 0 ≡ just (instr-ctrl (c-start (em-budget em)))
fetch-zero prog em = em-zero em

------------------------------------------------------------------------
-- THE FRAME STACK AND THE RETURN STACK ARE ONE STACK (Plan 0.63).
--
-- `c-thunk` pushes the caller's frame while `instr-call-closure` pushes the
-- return pc; `c-ret` pops both. So they have the same length, and each return
-- address is one past a call.
--
-- D455: the invariant is the RUN's, read off no scan of the code. Master's
-- positional segments (the reservation in force at each pc, a saved frame's
-- at its return pc) are master's proof of the slot fact, and live with its
-- image (`OldSeg`); the slot fact itself is the machine's slot gate
-- (B1.7b, D456: `slot-read-in-frame`).
--
-- A DATATYPE (not a `with`-free function on two lists) so the cons/nil cases
-- compose at the pushes and pops the markers produce.
------------------------------------------------------------------------
data RetMatch (prog : AbstractTrace) : List (Frame × ℕ) → List ℕ → Set where
  rm-[]  : RetMatch prog [] []
  rm-∷   : ∀ {f b rpc frs rs}
         -- WHERE THE RETURN ADDRESS CAME FROM (D094): one past a CALL,
         -- because the call is the only pusher. That is what says a return
         -- lands after a call site rather than anywhere — in particular never
         -- on a body entry, whose predecessor is a guard.
         → Σ ℕ (λ q → (rpc ≡ suc q) × Σ AbstractInstr (λ c → (fetch prog q ≡ just c) × CallI c))
         → RetMatch prog frs rs
         → RetMatch prog ((f , b) ∷ frs) (rpc ∷ rs)

-- THE RUN INVARIANT, per frame. `fw-stack` is what a return consumes;
-- `fw-entry` what an entry consumes. One induction.
record FrameWF (prog : AbstractTrace) (fs : FlatState) : Set where
  constructor mkFrameWF
  field
    fw-stack : RetMatch prog (saved-frames (falloc fs)) (fret fs)
    -- A BODY ENTRY IS REACHED WITH AN EMPTY RESERVATION (D094). The frame a
    -- `c-thunk` deepens is the one a CALL entered, and `enter-call` reserves
    -- nothing (D086). Every other way of arriving at a body entry is refuted:
    -- a fall-through cannot, because the emitter puts a `c-jmp` there
    -- (`emitted-thunk-guarded`); a jump cannot, because `find-label` resolves
    -- `c-label`s (`find-label-sound`, D082's disjoint provenances); and a
    -- return cannot, because its address is one past a CALL (`RetMatch`'s
    -- provenance), which is not a `c-jmp`.
    -- …AND WITH A LIVE LINK (plan 0.65 G2, 2026-08-16). Same enumeration, same
    -- refutations: the ONLY way to reach a body entry is a call, and a call
    -- sets `flink`. Carried in the SAME field rather than a second one because
    -- every case but the call is `⊥-elim`, which produces a pair as readily as
    -- an equation — the proof did not grow by a line.
    --
    -- riscv64 is what needs it. Its marker SPILLS (`sd ra, 8b(sp)`) onto the
    -- head pending return's own cell, so without a live link that store would
    -- overwrite a saved return address with whatever `ra` happens to hold. The
    -- x86-64 route never asked, because its marker writes no memory.
    -- …and a PENDING RETURN, for the same reason and by the same enumeration.
    -- riscv64's spill needs it TWICE OVER: the head row of `RetAddrs` is what
    -- says `ra` holds the return address, and its `GapNext` is what says the
    -- caller's base is one slot ABOVE the cell being written — the half
    -- `StackWindows`' `≤`-threaded floor cannot supply. Both live at the head
    -- of `RetAddrs`, which exists only when `fret` is a cons.
    fw-entry : ∀ (ℓ : EntryId) (bb : ℕ)
             → fetch prog (fpc fs) ≡ just (instr-ctrl (c-entry ℓ bb))
             → (frame-slots (falloc fs) ≡ 0) × Σ ℕ (λ r → flink fs ≡ just r)
               × Σ ℕ (λ rpc → Σ (List ℕ) (λ rest → fret fs ≡ rpc ∷ rest))
open FrameWF

------------------------------------------------------------------------
-- HOW THE PC MOVES, per instruction. Everything a frame-free step can be
-- either FALLS THROUGH (`flat-step-straight`, and `c-label`) or is one of the
-- three JUMPS. That split is what confines the label-scoping obligation:
-- a fall-through's segment fact is the fold's own recursion (`seg-at-suc`),
-- with nothing assumed about emitted code.
------------------------------------------------------------------------
-- where a jump can land: fall through, halt with the pc unmoved (the label
-- was not found), or at the label's resolved index. The last is the only case
-- that needs LABEL SCOPING, and carrying the target `m` here is what lets it
-- consume `emitted-jump-in-segment`.
-- the three post-pc shapes, read off `do-jump` / `do-branch`
dj-aux : ∀ (mj : Maybe ℕ) (fs : FlatState)
       → (fpc (do-jump mj fs) ≡ fpc fs)
         ⊎ (Σ ℕ (λ q → (mj ≡ just q) × (fpc (do-jump mj fs) ≡ q)))
dj-aux (just q) fs = inj₂ (q , refl , refl)
dj-aux nothing  fs = inj₁ refl

-- …and the branch, over a VARIABLE condition. Taking `b` as an argument is
-- what makes `do-branch b` reduce on the split — abstracting the scrutinee at
-- the use site does not work, because its normal form is spelled differently
-- from the source term (a register read vs the field accessor).
db-aux : ∀ (b : Bool) (m : LabelId) (prog : AbstractTrace) (fs : FlatState)
       → (fpc (do-branch b m prog fs) ≡ suc (fpc fs))
         ⊎ ((fpc (do-branch b m prog fs) ≡ fpc fs)
            ⊎ (Σ ℕ (λ q → (find-label prog m ≡ just q)
                        × (fpc (do-branch b m prog fs) ≡ q))))
db-aux false m prog fs = inj₁ refl
db-aux true  m prog fs = inj₂ (dj-aux (find-label prog m) fs)

-- D367: …and the tag branch's own test, whose fault stays where it stands.
dt-aux : ∀ (mb : Maybe Bool) (m : LabelId) (prog : AbstractTrace) (fs : FlatState)
       → (fpc (do-branch-test mb m prog fs) ≡ suc (fpc fs))
         ⊎ ((fpc (do-branch-test mb m prog fs) ≡ fpc fs)
            ⊎ (Σ ℕ (λ q → (find-label prog m ≡ just q)
                        × (fpc (do-branch-test mb m prog fs) ≡ q))))
dt-aux (just b) m prog fs = db-aux b m prog fs
dt-aux nothing  m prog fs = inj₂ (inj₁ refl)

-- D367: `out-nz` moves past itself whether it steps or faults.
nz-pc : ∀ (v : StoredValue FS) (fs : FlatState) → fpc (do-nz v fs) ≡ suc (fpc fs)
nz-pc (SV-Lit fits-int _)   fs = refl
nz-pc (SV-Lit fits-float _) fs = refl
nz-pc (SV-Tag _)            fs = refl
nz-pc (SV-Ptr _)            fs = refl
nz-pc (SV-Code _)           fs = refl

-- "not the unconditional jump" (D094). The ONE instruction that can sit
-- immediately before a body entry is `c-jmp` — that is the guard `ir-to-trace'`
-- emits to stop the parent falling in. So every step that FALLS THROUGH has to
-- be able to say it is not one, and this is the witness. Enumerated by
-- catch-all, so it reduces to `⊤` at every concrete constructor.
NotJmpI : AbstractInstr → Set
NotJmpI (instr-ctrl (c-jmp _)) = ⊥
{-# CATCHALL #-}
NotJmpI _                      = ⊤

data JumpPost (i : AbstractInstr) (m : LabelId) (prog : AbstractTrace) (fs : FlatState) : Set where
  -- FALLING THROUGH carries `NotJmpI`: only a BRANCH falls through, and a
  -- `c-jmp` never produces this row (`dj-aux` has no fall-through case).
  jp-suc  : fpc (flat-exec-instr i prog fs) ≡ suc (fpc fs) → NotJmpI i → JumpPost i m prog fs
  jp-halt : fpc (flat-exec-instr i prog fs) ≡ fpc fs → JumpPost i m prog fs
  jp-to   : ∀ (q : ℕ) → find-label prog m ≡ just q
          → fpc (flat-exec-instr i prog fs) ≡ q → JumpPost i m prog fs

-- Plan 0.63 (post-flip): an EMITTED instruction is one of four kinds, and the
-- markers are now among them. `pv-suc`/`pv-jump` are the frame-free ones (they
-- carry `FrameFreeI`, which is what `flat-same-frames` and the invariant
-- inductions consume); `pv-thunk`/`pv-ret` are the two that MOVE THE FRAME and
-- carry their reservation instead.
data PcView (i : AbstractInstr) : Set where
  -- (B1.7b: …or a slot instruction out of its frame faulted where it stands)
  pv-suc   : FrameFreeI i → NotJmpI i
           → (∀ prog fs → (fpc (flat-exec-instr i prog fs) ≡ suc (fpc fs)) ⊎ (flat-exec-instr i prog fs ≡ flat-fault fs))
           → PcView i
  pv-jump  : FrameFreeI i → ∀ (m : LabelId) → once-label-of i ≡ just m
           → (∀ prog fs → JumpPost i m prog fs) → PcView i
  -- D245: a callable ENTRY, a closure body's or a program function's.
  pv-thunk : ∀ (ℓ : EntryId) (bb : ℕ) → i ≡ instr-ctrl (c-entry ℓ bb) → PcView i
  pv-ret   : ∀ (bb : ℕ) → i ≡ instr-ctrl (c-ret bb) → PcView i
  -- plan 0.107: the program's START, which reserves the outermost frame.
  pv-start : ∀ (bb : ℕ) → i ≡ instr-ctrl (c-start bb) → PcView i
  -- D320: the program's LEAVE, which halts where it stands.
  pv-leave : i ≡ instr-ctrl c-leave → PcView i
  -- D092: the call is the fifth kind. It moves BOTH stacks and lands the pc on
  -- a body entry, so it is neither frame-free nor a jump.
  pv-call  : i ≡ instr-call-closure → PcView i
  -- D245: …and the direct call, the same transfer to a statically named entry.
  pv-call-fn : ∀ (f : CanonicalName) → i ≡ instr-ctrl (c-call-fn f) → PcView i

-- B1.7b (D456): a slot instruction's step moves on, or faults where it stands
slot-adv : ∀ i (fs : FlatState) → (fpc (flat-step-straight i fs) ≡ suc (fpc fs)) ⊎ (flat-step-straight i fs ≡ flat-fault fs)
slot-adv i fs = go (straightView i fs)
  where
    go : StraightPost i fs → (fpc (flat-step-straight i fs) ≡ suc (fpc fs)) ⊎ (flat-step-straight i fs ≡ flat-fault fs)
    go (sp-fault e) = inj₂ e
    go (sp-go _ e) = inj₁ (cong fpc e)

pcView : ∀ (i : AbstractInstr) → ImageI i → PcView i
pcView (instr-ctrl (c-label _))               _ = pv-suc tt tt (λ _ _ → inj₁ refl)
pcView (instr-ctrl (c-start bb))              _ = pv-start bb refl
pcView (instr-ctrl c-leave)                   _ = pv-leave refl
pcView (instr-ctrl (c-jmp m))                 _ = pv-jump tt m refl go
  where go : ∀ prog fs → JumpPost (instr-ctrl (c-jmp m)) m prog fs
        go prog fs = mk (dj-aux (find-label prog m) fs)
          where mk : (fpc (do-jump (find-label prog m) fs) ≡ fpc fs)
                     ⊎ (Σ ℕ (λ q → (find-label prog m ≡ just q)
                                 × (fpc (do-jump (find-label prog m) fs) ≡ q)))
                   → JumpPost (instr-ctrl (c-jmp m)) m prog fs
                mk (inj₁ e)            = jp-halt e
                mk (inj₂ (q , fq , e)) = jp-to q fq e
-- the branches abstract their scrutinee WITH an equation (J-style), so the
-- goal's `do-branch <cond>` reduces on the taken/not-taken split
pcView (instr-ctrl (c-branch-tag-zero m))     _ = pv-jump tt m refl go
  where
    go : ∀ prog fs → JumpPost (instr-ctrl (c-branch-tag-zero m)) m prog fs
    go prog fs = mk (dt-aux (tag-test (flat-read-tag (falloc fs) (floc fs))) m prog fs)
      where mk : _ → JumpPost (instr-ctrl (c-branch-tag-zero m)) m prog fs
            mk (inj₁ e)                     = jp-suc e tt
            mk (inj₂ (inj₁ e))              = jp-halt e
            mk (inj₂ (inj₂ (q , fq , e)))   = jp-to q fq e
pcView (instr-ctrl (c-entry ℓ bb))            _ = pv-thunk ℓ bb refl
pcView (instr-ctrl (c-call-fn f))             _ = pv-call-fn f refl
pcView (instr-ctrl (c-ret bb))                _ = pv-ret bb refl
pcView (instr-alloc-stack _)                  ()
pcView (instr-dealloc-stack _)                ()
pcView (instr-free-heap _)                    _ = pv-suc tt tt (λ _ _ → inj₁ refl)
pcView (load-at _)                            _ = pv-suc tt tt (λ _ _ → inj₁ refl)
pcView (store-at _)                           _ = pv-suc tt tt (λ _ _ → inj₁ refl)
pcView (addr-at _)                            _ = pv-suc tt tt (λ _ _ → inj₁ refl)
pcView (instr-room _)                    ()
pcView (instr-push-frame _)                   ()
pcView instr-pop-frame                        ()
pcView (lea-slot k)                         _ = pv-suc tt tt (λ _ fs → slot-adv (lea-slot k) fs)
pcView mov-to-output                          _ = pv-suc tt tt (λ _ _ → inj₁ refl)
pcView mov-to-input                           _ = pv-suc tt tt (λ _ _ → inj₁ refl)
pcView load-indirect                          ()
pcView load-indirect-suc                      ()
pcView (load-from-slot k)                   _ = pv-suc tt tt (λ _ fs → slot-adv (load-from-slot k) fs)
pcView (store-at-slot k)                    _ = pv-suc tt tt (λ _ fs → slot-adv (store-at-slot k) fs)
pcView store-indirect                         ()
pcView store-indirect-suc                     ()
pcView (restore-input k)                    _ = pv-suc tt tt (λ _ fs → slot-adv (restore-input k) fs)
pcView (instr-reclaim-to _)                   _ = pv-suc tt tt (λ _ _ → inj₁ refl)
pcView instr-call-closure                     _ = pv-call refl
pcView (worklist-init k)                    _ = pv-suc tt tt (λ _ fs → slot-adv (worklist-init k) fs)
pcView (worklist-push k)                    _ = pv-suc tt tt (λ _ fs → slot-adv (worklist-push k) fs)
pcView (worklist-pop k)                     _ = pv-suc tt tt (λ _ fs → slot-adv (worklist-pop k) fs)
pcView (worklist-check k)                   _ = pv-suc tt tt (λ _ fs → slot-adv (worklist-check k) fs)
pcView (instr-sigop _)                        _ = pv-suc tt tt (λ _ _ → inj₁ refl)
pcView (instr-load-const _ _)                 _ = pv-suc tt tt (λ _ _ → inj₁ refl)
pcView (instr-load-code-addr _)               _ = pv-suc tt tt (λ _ _ → inj₁ refl)
pcView instr-save-closure-reg                 _ = pv-suc tt tt (λ _ _ → inj₁ refl)
pcView (instr-load-tag-lit _)                 _ = pv-suc tt tt (λ _ _ → inj₁ refl)
pcView (instr-alloc-heap _)                   _ = pv-suc tt tt (λ _ _ → inj₁ refl)
pcView (instr-reg-op out-nz)                  _ = pv-suc tt tt (λ _ fs → inj₁ (nz-pc (readReg (regs (floc fs)) Output) fs))

-- THE RUN INVARIANT is the run's own: an induction on `Reachable` whose steps
-- read two facts of the code and nothing else (D455): what each instruction
-- is (`ImageI`, the emitter's fence) and the guard before each entry
-- (`GuardAt`). Taken as arguments rather than from `RunAt`, so a provider of
-- `Emitted` (master's scan, `OldSeg`) can use the invariant while building it.
run-frame-wf : ∀ prog → AllL ImageI prog → GuardAt prog
             → ∀ (fs : FlatState) → Reachable prog 0 fs → FrameWF prog fs
run-frame-wf prog img grd = go
  where
    0≢suc : ∀ {n : ℕ} → 0 ≡ suc n → ⊥
    0≢suc ()
    suc-inj : ∀ {m n : ℕ} → suc m ≡ suc n → m ≡ n
    suc-inj refl = refl
    just-injI : ∀ {a b : AbstractInstr} → just a ≡ just b → a ≡ b
    just-injI refl = refl
    -- the emitter's guard, at THIS program (D245: a `c-jmp` or a `c-ret`;
    -- D454: or a `c-leave`, which halts where it stands)
    Guard : ℕ → Set
    Guard q = (Σ LabelId (λ m → fetch prog q ≡ just (instr-ctrl (c-jmp m))))
              ⊎ (Σ ℕ (λ b → fetch prog q ≡ just (instr-ctrl (c-ret b))))
              ⊎ (fetch prog q ≡ just (instr-ctrl c-leave))
    -- a step that moves the pc on is not a `c-leave`
    n≢sn : ∀ (n : ℕ) → n ≡ suc n → ⊥
    n≢sn zero    ()
    n≢sn (suc n) e = n≢sn n (suc-inj e)
    guard : ∀ (p : ℕ) (ℓ : EntryId) (bb : ℕ)
          → fetch prog p ≡ just (instr-ctrl (c-entry ℓ bb))
          → Σ ℕ (λ q → (p ≡ suc q) × Guard q)
    guard p ℓ bb H = grd p ℓ bb H
    go : ∀ (fs' : FlatState) → Reachable prog 0 fs' → FrameWF prog fs'
    go fs' (reach-start .fs' el eqB _) =
      mkFrameWF (subst₂ (RetMatch prog)
                        (sym (proj₁ (proj₂ (proj₂ (proj₂ el)))))
                        (sym (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ el))))))
                        rm-[])
                -- AT ENTRY the pc is 0, and a body entry is never at position 0
                -- (the emitter's guard sits before it).
                (λ ℓ bb H → ⊥-elim (0≢suc (proj₁ (proj₂ (guard 0 ℓ bb
                              (subst (λ z → fetch prog z ≡ just (instr-ctrl (c-entry ℓ bb)))
                                     (proj₁ el) H))))))
    go .(flat-exec-instr i prog fs'') (reach-step i fs'' r' ftq h) =
      step (pcView i (fetch-All {prog = prog} {k = fpc fs''} img ftq))
      where
        ih  = go fs'' r'
        -- D094: NO FALL-THROUGH LANDS ON A BODY ENTRY. The emitter's guard
        -- puts a `c-jmp` immediately before one, and the instruction actually
        -- fetched here is not a `c-jmp` — whoever calls this says so.
        -- D245: …or a `c-ret` — so the instruction here must be neither.
        -- D454: …or a `c-leave`, which a step that falls through is not.
        no-fallthrough : ∀ (p : ℕ) (ℓ : EntryId) (bb : ℕ) (i' : AbstractInstr)
                       → (∀ m → i' ≡ instr-ctrl (c-jmp m) → ⊥) → (∀ b → i' ≡ instr-ctrl (c-ret b) → ⊥)
                       → (i' ≡ instr-ctrl c-leave → ⊥)
                       → fetch prog p ≡ just i'
                       → fetch prog (suc p) ≡ just (instr-ctrl (c-entry ℓ bb)) → ⊥
        no-fallthrough p ℓ bb i' nj nr nl ftq' H = clash (guard (suc p) ℓ bb H)
          where clash : Σ ℕ (λ q → (suc p ≡ suc q) × Guard q) → ⊥
                clash (q , sq , inj₁ (m , fq)) =
                  nj m (just-injI (trans (sym ftq')
                                    (subst (λ z → fetch prog z ≡ just (instr-ctrl (c-jmp m)))
                                           (sym (suc-inj sq)) fq)))
                clash (q , sq , inj₂ (inj₁ (b , fq))) =
                  nr b (just-injI (trans (sym ftq')
                                    (subst (λ z → fetch prog z ≡ just (instr-ctrl (c-ret b)))
                                           (sym (suc-inj sq)) fq)))
                clash (q , sq , inj₂ (inj₂ fq)) =
                  nl (just-injI (trans (sym ftq')
                                  (subst (λ z → fetch prog z ≡ just (instr-ctrl c-leave))
                                         (sym (suc-inj sq)) fq)))
        -- a step that moves the pc on is not a `c-leave` (which halts in place)
        adv-not-leave : ∀ {i' : AbstractInstr} → fpc (flat-exec-instr i' prog fs'') ≡ suc (fpc fs'')
                      → i' ≡ instr-ctrl c-leave → ⊥
        adv-not-leave a refl = n≢sn (fpc fs'') a
        -- a frame-free instruction is not a `c-ret` (which moves the frame)
        ff-not-ret : FrameFreeI i → ∀ b → i ≡ instr-ctrl (c-ret b) → ⊥
        ff-not-ret ff b e = subst FrameFreeI e ff
        nj-eq : ∀ {i' : AbstractInstr} → NotJmpI i' → ∀ m → i' ≡ instr-ctrl (c-jmp m) → ⊥
        nj-eq nj m e = subst NotJmpI e nj
        step : PcView i → FrameWF prog (flat-exec-instr i prog fs'')
        -- FRAME-FREE, FALLING THROUGH: frames untouched.
        step (pv-suc ff nj adv) =
          mkFrameWF
            (subst₂ (RetMatch prog) (sym (sf-saved same)) (sym (sf-ret same)) (fw-stack ih))
            (land (adv prog fs''))
          where
            same = flat-same-frames i prog fs'' ff
            -- a FALL-THROUGH cannot land on a body entry: the emitter put a
            -- guard there, and this instruction is not one. (B1.7b: a fault
            -- stays on this instruction, which is not an entry either.)
            land : (fpc (flat-exec-instr i prog fs'') ≡ suc (fpc fs'')) ⊎ (flat-exec-instr i prog fs'' ≡ flat-fault fs'')
                 → ∀ ℓ bb → fetch prog (fpc (flat-exec-instr i prog fs'')) ≡ just (instr-ctrl (c-entry ℓ bb))
                 → (frame-slots (falloc (flat-exec-instr i prog fs'')) ≡ 0) × Σ ℕ (λ r → flink (flat-exec-instr i prog fs'') ≡ just r)
                   × Σ ℕ (λ rpc → Σ (List ℕ) (λ rest → fret (flat-exec-instr i prog fs'') ≡ rpc ∷ rest))
            land (inj₁ a) ℓ bb H =
              ⊥-elim (no-fallthrough (fpc fs'') ℓ bb i (nj-eq nj) (ff-not-ret ff) (adv-not-leave a) ftq
                        (subst (λ z → fetch prog z ≡ just (instr-ctrl (c-entry ℓ bb))) a H))
            land (inj₂ e) ℓ bb H =
              ⊥-elim (subst FrameFreeI (just-injI (trans (sym ftq) (subst (λ z → fetch prog z ≡ just (instr-ctrl (c-entry ℓ bb))) (cong fpc e) H))) ff)
        -- FRAME-FREE JUMP: frames untouched.
        step (pv-jump ff m mlab jp) =
          mkFrameWF
            (subst₂ (RetMatch prog) (sym (sf-saved same)) (sym (sf-ret same)) (fw-stack ih))
            -- THE THREE WAYS A JUMP CAN LAND, and none is a body entry: a
            -- fall-through (branch not taken) is guarded as above; a HALT
            -- leaves the pc on this very instruction, which `once-label-of`
            -- says is not an entry; and a resolved target holds a `c-label`
            -- (`find-label-sound` — D082's disjoint provenances).
            (λ ℓ bb H → ⊥-elim (ego (jp prog fs'') ℓ bb H))
          where
            same = flat-same-frames i prog fs'' ff
            ego : JumpPost i m prog fs'' → ∀ ℓ bb
                → fetch prog (fpc (flat-exec-instr i prog fs''))
                    ≡ just (instr-ctrl (c-entry ℓ bb)) → ⊥
            ego (jp-suc adv nj) ℓ bb H =
              no-fallthrough (fpc fs'') ℓ bb i (nj-eq nj) (ff-not-ret ff) (adv-not-leave adv) ftq
                (subst (λ z → fetch prog z ≡ just (instr-ctrl (c-entry ℓ bb))) adv H)
            ego (jp-halt e) ℓ bb H = no-once (trans (sym mlab) (cong once-label-of i≡thunk))
              where i≡thunk : i ≡ instr-ctrl (c-entry ℓ bb)
                    i≡thunk = just-injI (trans (sym ftq)
                                (subst (λ z → fetch prog z ≡ just (instr-ctrl (c-entry ℓ bb))) e H))
                    no-once : ∀ {A : Set} → just m ≡ nothing → A
                    no-once ()
            ego (jp-to q fq e) ℓ bb H = clash (trans (sym (find-label-sound prog m q fq))
                    (subst (λ z → fetch prog z ≡ just (instr-ctrl (c-entry ℓ bb))) e H))
              where clash : ∀ {A : Set}
                          → just (instr-ctrl (c-label m)) ≡ just (instr-ctrl (c-entry ℓ bb)) → A
                    clash ()
        -- THE ENTRY: `saved-frames`/`fret` untouched; it falls through, so the
        -- same guard applies to the position after it.
        step (pv-thunk ℓ bb ieq) =
          mkFrameWF (subst₂ (RetMatch prog)
                            (sym (cong (λ z → saved-frames (falloc (flat-exec-instr z prog fs''))) ieq))
                            (sym (cong (λ z → fret (flat-exec-instr z prog fs'')) ieq))
                            (fw-stack ih))
                    (λ ℓ' bb' H → ⊥-elim (no-fallthrough (fpc fs'') ℓ' bb' i
                                    (entry-not-jmp ieq) (entry-not-ret ieq) (adv-not-leave (pc-eq ieq)) ftq
                                    (subst (λ z → fetch prog z ≡ just (instr-ctrl (c-entry ℓ' bb')))
                                           (pc-eq ieq) H)))
          where
            entry-not-ret : i ≡ instr-ctrl (c-entry ℓ bb) → ∀ b → i ≡ instr-ctrl (c-ret b) → ⊥
            entry-not-ret refl b ()
            entry-not-jmp : i ≡ instr-ctrl (c-entry ℓ bb) → ∀ m → i ≡ instr-ctrl (c-jmp m) → ⊥
            entry-not-jmp refl m ()
            pc-eq : i ≡ instr-ctrl (c-entry ℓ bb)
                  → fpc (flat-exec-instr i prog fs'') ≡ suc (fpc fs'')
            pc-eq refl = refl
        -- plan 0.107: THE START, likewise.
        step (pv-start bb ieq) =
          mkFrameWF (subst₂ (RetMatch prog)
                            (sym (cong (λ z → saved-frames (falloc (flat-exec-instr z prog fs''))) ieq))
                            (sym (cong (λ z → fret (flat-exec-instr z prog fs'')) ieq))
                            (fw-stack ih))
                    (λ ℓ' bb' H → ⊥-elim (no-fallthrough (fpc fs'') ℓ' bb' i
                                    (start-not-jmp ieq) (start-not-ret ieq) (adv-not-leave (pc-eq′ ieq)) ftq
                                    (subst (λ z → fetch prog z ≡ just (instr-ctrl (c-entry ℓ' bb')))
                                           (pc-eq′ ieq) H)))
          where
            start-not-ret : i ≡ instr-ctrl (c-start bb) → ∀ b → i ≡ instr-ctrl (c-ret b) → ⊥
            start-not-ret refl b ()
            start-not-jmp : i ≡ instr-ctrl (c-start bb) → ∀ m → i ≡ instr-ctrl (c-jmp m) → ⊥
            start-not-jmp refl m ()
            pc-eq′ : i ≡ instr-ctrl (c-start bb)
                   → fpc (flat-exec-instr i prog fs'') ≡ suc (fpc fs'')
            pc-eq′ refl = refl
        -- D320: THE LEAVE halts where it stands — frames, pc and returns as they were.
        step (pv-leave ieq) = subst (λ z → FrameWF prog (flat-exec-instr z prog fs'')) (sym ieq)
                                (mkFrameWF (fw-stack ih) (fw-entry ih))
        -- THE RETURN pops both stacks and lands one past a call.
        step (pv-ret bb ieq) = ret-step ieq
          where
            -- the pc has not moved, so the instruction is this `c-ret`
            ret-clash : i ≡ instr-ctrl (c-ret bb) → ∀ ℓ bb'
                      → fetch prog (fpc fs'') ≡ just (instr-ctrl (c-entry ℓ bb')) → ⊥
            ret-clash refl ℓ bb' H = go-c (just-injI (trans (sym ftq) H))
              where go-c : instr-ctrl (c-ret bb) ≡ instr-ctrl (c-entry ℓ bb') → ⊥
                    go-c ()
            ret-step : i ≡ instr-ctrl (c-ret bb) → FrameWF prog (flat-exec-instr i prog fs'')
            ret-step refl = rgo (retView bb fs'')
              where
                rgo : RetPost bb fs'' → FrameWF prog (do-ret bb (fret fs'') fs'')
                -- B1.7b: a return that fails FAULTS: no stack moves, the pc stays
                rgo (rp-fault e) rewrite e =
                  mkFrameWF (fw-stack ih) (λ ℓ bb′ H → ⊥-elim (ret-clash ieq ℓ bb′ H))
                -- …and a real return lands at `rpc`, one past a CALL
                -- (`RetMatch`'s provenance), which is not a guard.
                rgo (rp-ret rpc rs req be e) rewrite e =
                  land (saved-frames (falloc fs'')) refl (subst (RetMatch prog (saved-frames (falloc fs''))) req (fw-stack ih))
                  where
                    land : ∀ (frs : List (Frame × ℕ)) → saved-frames (falloc fs'') ≡ frs → RetMatch prog frs (rpc ∷ rs)
                         → FrameWF prog (record fs'' { falloc = leave-frame (falloc fs'') ; fpc = rpc ; fret = rs })
                    land ((f , b) ∷ frs) feq (rm-∷ prov rest) =
                      mkFrameWF (subst (λ x → RetMatch prog x rs) (sym (leave-frame-saved-∷ (falloc fs'') f b frs feq)) rest)
                                (λ ℓ bb′ H → ⊥-elim
                                  (no-fallthrough (proj₁ prov) ℓ bb′ (proj₁ (proj₂ (proj₂ prov)))
                                    (call-not-jmp (proj₁ (proj₂ (proj₂ prov))) (proj₂ (proj₂ (proj₂ (proj₂ prov)))))
                                    (call-not-ret (proj₁ (proj₂ (proj₂ prov))) (proj₂ (proj₂ (proj₂ (proj₂ prov)))))
                                    (λ e′ → subst CallI e′ (proj₂ (proj₂ (proj₂ (proj₂ prov)))))
                                    (proj₁ (proj₂ (proj₂ (proj₂ prov))))
                                    (subst (λ z → fetch prog z ≡ just (instr-ctrl (c-entry ℓ bb′)))
                                           (proj₁ (proj₂ prov)) H)))
        -- THE CALL (D092): it PUSHES both stacks and lands on a body entry,
        -- with a frame that reserves nothing (D086) and a live link.
        step (pv-call ieq) = call-go ieq
          where
            call-go : i ≡ instr-call-closure → FrameWF prog (flat-exec-instr i prog fs'')
            call-go refl = cgo (callView prog fs'')
              where
                call-clash : ∀ {ℓ' bb'} → instr-call-closure ≡ instr-ctrl (c-entry ℓ' bb') → ⊥
                call-clash ()
                cgo : CallPost prog fs'' → FrameWF prog (do-call prog fs'')
                -- B1.7b: a malformed call FAULTS: no stack moves
                cgo (cp-fault e) rewrite e =
                  mkFrameWF (fw-stack ih)
                            (λ ℓ bb H → ⊥-elim (call-clash (just-injI (trans (sym ftq) H))))
                cgo (cp-enter ℓ j hl ce he fteq e) rewrite e =
                  mkFrameWF (rm-∷ (fpc fs'' , refl , instr-call-closure , ftq , tt) (fw-stack ih))
                            (λ _ _ _ → refl , (suc (fpc fs'') , refl)
                                             , suc (fpc fs'') , fret fs'' , refl)
        -- D245: THE DIRECT CALL, the same transfer to a statically named entry.
        step (pv-call-fn f ieq) = callfn-go ieq
          where
            callfn-go : i ≡ instr-ctrl (c-call-fn f) → FrameWF prog (flat-exec-instr i prog fs'')
            callfn-go refl = cfgo (find-fn prog f) refl
              where
                cf-clash : ∀ {ℓ' bb'} → instr-ctrl (c-call-fn f) ≡ instr-ctrl (c-entry ℓ' bb') → ⊥
                cf-clash ()
                cfgo : ∀ (mj : Maybe ℕ) → find-fn prog f ≡ mj
                     → FrameWF prog (do-call-at (find-fn prog f) fs'')
                cfgo nothing fe rewrite fe =
                  mkFrameWF (fw-stack ih)
                            (λ ℓ bb H → ⊥-elim (cf-clash (just-injI (trans (sym ftq) H))))
                cfgo (just j) fe rewrite fe =
                  mkFrameWF (rm-∷ (fpc fs'' , refl , instr-ctrl (c-call-fn f) , ftq , tt) (fw-stack ih))
                            (λ _ _ _ → refl , (suc (fpc fs'') , refl)
                                             , suc (fpc fs'') , fret fs'' , refl)

-- …at a run context
run-frame-wf-at : ∀ prog (fs : FlatState) → RunAt prog fs → FrameWF prog fs
run-frame-wf-at prog fs (mkRunAt emt reach) = run-frame-wf prog (em-image emt) (em-guard emt) fs reach

-- …and the form the correspondence consumes (D093/D094). Was a POSTULATE for
-- one commit; it is now a projection of the run invariant, which is where it
-- always belonged — the emitter's guard is the only assumption left under it.
-- D245: the three projections at any callable ENTRY (a function's too).
entry-empty : ∀ prog (fs : FlatState) (ℓ : EntryId) (bb : ℕ) → RunAt prog fs
            → fetch prog (fpc fs) ≡ just (instr-ctrl (c-entry ℓ bb))
            → frame-slots (falloc fs) ≡ 0
entry-empty prog fs ℓ bb r ftq = proj₁ (fw-entry (run-frame-wf-at prog fs r) ℓ bb ftq)

entry-link : ∀ prog (fs : FlatState) (ℓ : EntryId) (bb : ℕ) → RunAt prog fs
           → fetch prog (fpc fs) ≡ just (instr-ctrl (c-entry ℓ bb))
           → Σ ℕ (λ r → flink fs ≡ just r)
entry-link prog fs ℓ bb r ftq = proj₁ (proj₂ (fw-entry (run-frame-wf-at prog fs r) ℓ bb ftq))

entry-ret : ∀ prog (fs : FlatState) (ℓ : EntryId) (bb : ℕ) → RunAt prog fs
          → fetch prog (fpc fs) ≡ just (instr-ctrl (c-entry ℓ bb))
          → Σ ℕ (λ rpc → Σ (List ℕ) (λ rest → fret fs ≡ rpc ∷ rest))
entry-ret prog fs ℓ bb r ftq = proj₂ (proj₂ (fw-entry (run-frame-wf-at prog fs r) ℓ bb ftq))

thunk-entry-empty : ∀ prog (fs : FlatState) (ℓ : LabelId) (bb : ℕ) → RunAt prog fs
                  → fetch prog (fpc fs) ≡ just (instr-ctrl (c-thunk ℓ bb))
                  → frame-slots (falloc fs) ≡ 0
thunk-entry-empty prog fs ℓ bb r ftq = proj₁ (fw-entry (run-frame-wf-at prog fs r) (e-thunk ℓ) bb ftq)

-- …and its twin, which riscv64's body marker needs: A BODY ENTRY IS REACHED
-- WITH A LIVE LINK. Same projection, same one assumption (the emitter's guard)
-- underneath. This is the CONVERSE of `run-link-at-thunk`, and unlike that one
-- it is a block-step's business rather than the engine's: riscv64's `sd ra`
-- writes the head return cell, so it must know the value in `ra` IS that
-- return address.
thunk-entry-link : ∀ prog (fs : FlatState) (ℓ : LabelId) (bb : ℕ) → RunAt prog fs
                 → fetch prog (fpc fs) ≡ just (instr-ctrl (c-thunk ℓ bb))
                 → Σ ℕ (λ r → flink fs ≡ just r)
thunk-entry-link prog fs ℓ bb r ftq = proj₁ (proj₂ (fw-entry (run-frame-wf-at prog fs r) (e-thunk ℓ) bb ftq))

-- …and the third projection: A BODY ENTRY HAS A PENDING RETURN. Same one
-- assumption; what riscv64's marker needs it for is `RetAddrs`' head row, which
-- carries both the value it is about to spill and the `GapNext` that makes the
-- spill miss the caller's window.
thunk-entry-ret : ∀ prog (fs : FlatState) (ℓ : LabelId) (bb : ℕ) → RunAt prog fs
                → fetch prog (fpc fs) ≡ just (instr-ctrl (c-thunk ℓ bb))
                → Σ ℕ (λ rpc → Σ (List ℕ) (λ rest → fret fs ≡ rpc ∷ rest))
thunk-entry-ret prog fs ℓ bb r ftq = proj₂ (proj₂ (fw-entry (run-frame-wf-at prog fs r) (e-thunk ℓ) bb ftq))

-- (`run-stack-slot` — "the window is the whole trace's budget" — is GONE with
-- the flip. It is FALSE inside a closure body, whose window is the body's own
-- reservation. Its consumer wants the slot inside the CURRENT frame, which is
-- the machine's slot gate, B1.7b D456: `slot-read-in-frame`.)

------------------------------------------------------------------------
-- (`run-no-ret` STOOD HERE and is now DELETED — on purpose, and it is the
-- check that D092 really landed.
--
-- It was the theorem "`fret` and `saved-frames` are empty in EVERY reachable
-- state", true only because `instr-call-closure` was the IDENTITY: nothing
-- pushed, so no closure body was ever entered and the return correspondence
-- spoke about a state that could not arise (D091). Now that the call is
-- MODELLED it pushes, the theorem is FALSE, and it stops typechecking — which
-- is exactly the signal that the machine changed. `events-running-ret` is a
-- live route again, and `ret-site-owes` — the residual that stood in for it —
-- is gone with it.)
------------------------------------------------------------------------

-- …and the pointer-bounds and store-WF invariants likewise (D074: the entry
-- registers are all tags, both memories empty).
entry-ptr-bounds : ∀ (fs : FlatState) → EntryLike fs → PtrBoundsWF fs
entry-ptr-bounds fs (_ , _ , _ , _ , _ , hemp , semp , _ , noptr , _) = record
  { pb-regs  = λ r → go r (readReg (regs (floc fs)) r) refl
  ; pb-heap  = λ hl → subst (PtrB? _) (sym (hemp hl)) tt
  ; pb-stack = λ f k → subst (PtrB? _) (sym (semp f k)) tt }
  where go : ∀ (r : AbstractReg) (v : StoredValue FS) → readReg (regs (floc fs)) r ≡ v
           → PtrB (block-size (falloc fs)) (readReg (regs (floc fs)) r)
        go r (SV-Ptr loc)  eq = ⊥-elim (noptr r loc eq)
        go r (SV-Tag t)    eq rewrite eq = tt
        go r (SV-Lit p v)  eq rewrite eq = tt
        go r (SV-Code c)   eq rewrite eq = tt

entry-flat-wf : ∀ (fs : FlatState) → EntryLike fs → FlatWF fs
entry-flat-wf fs (_ , _ , _ , _ , _ , hemp , semp , _ , noptr , _ , nolit) = record
  { wf-regs  = λ r → go r (readReg (regs (floc fs)) r) refl
  ; wf-heap  = λ hl → subst (svm-below _) (sym (hemp hl)) tt
  ; wf-stack = λ f k → subst (svm-below _) (sym (semp f k)) tt
  ; wf-fresh = λ hl _ → hemp hl }
  where go : ∀ (r : AbstractReg) (v : StoredValue FS) → readReg (regs (floc fs)) r ≡ v
           → sv-below (next-heap-ref (falloc fs)) (readReg (regs (floc fs)) r)
        go r (SV-Ptr loc)  eq = ⊥-elim (noptr r loc eq)
        go r (SV-Tag t)    eq rewrite eq = tt
        go r (SV-Lit p v)  eq = ⊥-elim (nolit r p v eq)
        go r (SV-Code c)   eq rewrite eq = tt

-- Plan 0.107: NO STEP LANDS ON THE START. A fall-through lands one past
-- something; a jump on a `c-label`, a call on an entry — and pc 0 holds the
-- start; a return one past a CALL (`RetMatch`'s provenance); and a step that
-- leaves the pc where it is was not the start (the start falls through). So
-- the correspondence, which begins AFTER the start, never meets it.
run-step-pc-pos : ∀ prog (fs : FlatState) (i : AbstractInstr) → RunAt prog fs
                → fetch prog (fpc fs) ≡ just i
                → fpc (flat-exec-instr i prog fs) ≡ 0 → ⊥
run-step-pc-pos prog fs i r ftq = step (pcView i (frame-op-absurd prog fs i (run-emitted r) ftq))
  where
    z≢s : ∀ {n : ℕ} → suc n ≡ 0 → ⊥
    z≢s ()
    jI : ∀ {a b : AbstractInstr} → just a ≡ just b → a ≡ b
    jI refl = refl
    -- whatever sits at a position that is 0 is the start
    at-zero : ∀ (k : ℕ) (i' : AbstractInstr) → fetch prog k ≡ just i' → k ≡ 0
            → i' ≡ instr-ctrl (c-start (em-budget (run-emitted r)))
    at-zero k i' fq refl = jI (trans (sym fq) (fetch-zero prog (run-emitted r)))
    -- the pc did not move: then `i` itself sat at 0, so `i` is the start
    unmoved : (∀ b → i ≡ instr-ctrl (c-start b) → ⊥)
            → fpc (flat-exec-instr i prog fs) ≡ fpc fs → fpc (flat-exec-instr i prog fs) ≡ 0 → ⊥
    unmoved ns e z = ns _ (at-zero (fpc fs) i ftq (trans (sym e) z))
    lab≢start : ∀ {m b} → instr-ctrl (c-label m) ≡ instr-ctrl (c-start b) → ⊥
    lab≢start ()
    ent≢start : ∀ {e b' b} → instr-ctrl (c-entry e b') ≡ instr-ctrl (c-start b) → ⊥
    ent≢start ()
    step : PcView i → fpc (flat-exec-instr i prog fs) ≡ 0 → ⊥
    step (pv-suc ff nj adv) z = sgo (adv prog fs)
      where
        sgo : (fpc (flat-exec-instr i prog fs) ≡ suc (fpc fs)) ⊎ (flat-exec-instr i prog fs ≡ flat-fault fs) → ⊥
        sgo (inj₁ a) = z≢s (trans (sym a) z)
        sgo (inj₂ e) = unmoved (λ b eq → subst FrameFreeI eq ff) (cong fpc e) z
    step (pv-jump ff m mlab jp) z = jgo (jp prog fs)
      where
        not-start : ∀ b → i ≡ instr-ctrl (c-start b) → ⊥
        not-start b refl = no-once mlab
          where no-once : ∀ {A : Set} → nothing ≡ just m → A
                no-once ()
        jgo : JumpPost i m prog fs → ⊥
        jgo (jp-suc adv _) = z≢s (trans (sym adv) z)
        jgo (jp-halt e)    = unmoved not-start e z
        jgo (jp-to q fq e) =
          lab≢start (at-zero q _ (find-label-sound prog m q fq) (trans (sym e) z))
    step (pv-thunk ℓ bb refl) z = z≢s z
    step (pv-start bb refl)   z = z≢s z
    step (pv-leave refl)      z = unmoved (λ b ()) refl z
    step (pv-ret bb refl) z = rgo (retView bb fs)
      where
        ret≢start : ∀ b → instr-ctrl (c-ret bb) ≡ instr-ctrl (c-start b) → ⊥
        ret≢start b ()
        rgo : RetPost bb fs → ⊥
        -- B1.7b: a failing return faults, the pc stays
        rgo (rp-fault e) = unmoved ret≢start (cong fpc e) z
        rgo (rp-ret rpc rs e be eq) =
          prov-go (subst (RetMatch prog (saved-frames (falloc fs))) e (fw-stack (run-frame-wf-at prog fs r)))
          where
            prov-go : RetMatch prog (saved-frames (falloc fs)) (rpc ∷ rs) → ⊥
            prov-go (rm-∷ (q , rq , _) _) =
              z≢s (trans (sym rq) (trans (sym (cong fpc eq)) z))
    step (pv-call refl) z = cgo (callView prog fs)
      where
        cl≢start : ∀ b → instr-call-closure ≡ instr-ctrl (c-start b) → ⊥
        cl≢start b ()
        cgo : CallPost prog fs → ⊥
        cgo (cp-fault heq)        = unmoved cl≢start (cong fpc heq) z
        cgo (cp-enter ℓ j hl ce he feq eeq) =
          ent≢start (at-zero j _ (proj₂ (find-thunk-sound prog ℓ j feq)) (trans (sym (cong fpc eeq)) z))
    step (pv-call-fn f refl) z = fgo (find-fn prog f) refl
      where
        cf≢start : ∀ b → instr-ctrl (c-call-fn f) ≡ instr-ctrl (c-start b) → ⊥
        cf≢start b ()
        fgo : ∀ (mj : Maybe ℕ) → find-fn prog f ≡ mj → ⊥
        fgo nothing  fe = unmoved cf≢start (cong (λ x → fpc (do-call-at x fs)) fe) z
        fgo (just j) fe =
          ent≢start (at-zero j _ (proj₂ (find-entry-sound prog (e-fn f) j fe))
                     (trans (sym (cong (λ x → fpc (do-call-at x fs)) fe)) z))

slot-read-in-frame : ∀ prog (fs : FlatState) (slot : Slot) (i : AbstractInstr) → RunAt prog fs
                   → halted (floc fs) ≡ false
                   → fetch prog (fpc fs) ≡ just i → slot-of i ≡ just slot
                   → slot < frame-slots (falloc fs)
-- B1.7b (D456): the machine's slot gate, passed at a reached step (it did not
-- fault: the run is sound). It was the image's (`Emitted.em-slots`, D455).
slot-read-in-frame prog fs slot i r h ftq soq = slot-gate-ok i prog fs soq (step-sound prog fs r h ftq)

------------------------------------------------------------------------
-- THE POINTER-BOUNDS INVARIANT IS A THEOREM (plan 0.54 rung D, item 5).
--
-- Every dynamic pointer a reachable state holds is in-bounds for its block —
-- in the PAIR form (`Once.CCC.Machine.FlatPtrBounds`). Same shape as
-- `run-stack-ptr`, with two extra inputs: the emitter's allocation discipline
-- (every emitted `instr-alloc-heap` is a 2-cell pair block, `AllocMin`) and
-- the store-WF invariant (carried through the SAME induction — an allocation
-- cannot shrink the block under a live pointer because no live pointer
-- references the fresh ref). This is what turned the in-bounds residual
-- family into theorems: `store-indirect{,-suc}-inbounds` outright, and the
-- in-bounds conjunct of `load-indirect{,-suc}-target-wf` (whose pointer-SHAPE
-- half stays the D073 site-discipline residual, now named `-target-ptr`).
------------------------------------------------------------------------

-- THE EMITTER HALF: a fetched instruction of an emitted program satisfies the
-- allocation discipline (`AllocMinI`).
emitted-alloc-min : ∀ prog (fs : FlatState) (i : AbstractInstr) → Emitted prog
                  → fetch prog (fpc fs) ≡ just i → AllocMinI i
emitted-alloc-min prog fs i em ftq = fetch-All {prog = prog} {k = fpc fs} (em-alloc em) ftq

-- ONE FRAME-FREE STEP PRESERVES THE INVARIANT — enumerated like
-- `stack-ptr-step` (the vacuous alloc premises need `i` concrete).
ptr-bounds-step : ∀ (i : AbstractInstr) prog (fs : FlatState) → RunAt prog fs
                → fetch prog (fpc fs) ≡ just i → ImageI i
                → FlatWF fs
                → PtrBoundsWF fs → PtrBoundsWF (flat-exec-instr i prog fs)
ptr-bounds-step (instr-alloc-stack n)   prog fs r ftq () wfS wf
ptr-bounds-step (instr-dealloc-stack n) prog fs r ftq () wfS wf
ptr-bounds-step (instr-free-heap n)     prog fs r ftq ff wfS wf = flat-ptr-bounds (instr-free-heap n) prog fs ff (λ { _ () }) wfS wf
ptr-bounds-step (load-at n)     prog fs r ftq ff wfS wf = flat-ptr-bounds (load-at n) prog fs ff (λ { _ () }) wfS wf
ptr-bounds-step (store-at n)     prog fs r ftq ff wfS wf = flat-ptr-bounds (store-at n) prog fs ff (λ { _ () }) wfS wf
ptr-bounds-step (addr-at n)     prog fs r ftq ff wfS wf = flat-ptr-bounds (addr-at n) prog fs ff (λ { _ () }) wfS wf
ptr-bounds-step (instr-room n)     prog fs r ftq ff wfS wf = flat-ptr-bounds (instr-room n) prog fs ff (λ { _ () }) wfS wf
ptr-bounds-step (instr-push-frame cap)  prog fs r ftq () wfS wf
ptr-bounds-step instr-pop-frame         prog fs r ftq () wfS wf
-- THE PRODUCER: the emitter's alloc discipline comes in through the premise.
ptr-bounds-step (instr-alloc-heap k) prog fs r ftq ff wfS wf =
  flat-ptr-bounds (instr-alloc-heap k) prog fs ff
    (λ n eq → subst AllocMinI eq
                (emitted-alloc-min prog fs (instr-alloc-heap k) (run-emitted r) ftq))
    wfS wf
ptr-bounds-step mov-to-output prog fs r ftq ff wfS wf =
  flat-ptr-bounds mov-to-output prog fs ff (λ { _ () }) wfS wf
ptr-bounds-step mov-to-input prog fs r ftq ff wfS wf =
  flat-ptr-bounds mov-to-input prog fs ff (λ { _ () }) wfS wf
ptr-bounds-step load-indirect prog fs r ftq ff wfS wf =
  flat-ptr-bounds load-indirect prog fs ff (λ { _ () }) wfS wf
ptr-bounds-step load-indirect-suc prog fs r ftq ff wfS wf =
  flat-ptr-bounds load-indirect-suc prog fs ff (λ { _ () }) wfS wf
ptr-bounds-step (load-from-slot k) prog fs r ftq ff wfS wf =
  flat-ptr-bounds (load-from-slot k) prog fs ff (λ { _ () }) wfS wf
ptr-bounds-step (store-at-slot k) prog fs r ftq ff wfS wf =
  flat-ptr-bounds (store-at-slot k) prog fs ff (λ { _ () }) wfS wf
ptr-bounds-step store-indirect prog fs r ftq ff wfS wf =
  flat-ptr-bounds store-indirect prog fs ff (λ { _ () }) wfS wf
ptr-bounds-step store-indirect-suc prog fs r ftq ff wfS wf =
  flat-ptr-bounds store-indirect-suc prog fs ff (λ { _ () }) wfS wf
ptr-bounds-step (lea-slot k) prog fs r ftq ff wfS wf =
  flat-ptr-bounds (lea-slot k) prog fs ff (λ { _ () }) wfS wf
ptr-bounds-step (restore-input k) prog fs r ftq ff wfS wf =
  flat-ptr-bounds (restore-input k) prog fs ff (λ { _ () }) wfS wf
ptr-bounds-step (instr-reclaim-to k) prog fs r ftq ff wfS wf =
  flat-ptr-bounds (instr-reclaim-to k) prog fs ff (λ { _ () }) wfS wf
ptr-bounds-step instr-call-closure prog fs r ftq ff wfS wf =
  flat-ptr-bounds instr-call-closure prog fs ff (λ { _ () }) wfS wf
ptr-bounds-step (worklist-init k) prog fs r ftq ff wfS wf =
  flat-ptr-bounds (worklist-init k) prog fs ff (λ { _ () }) wfS wf
ptr-bounds-step (worklist-push k) prog fs r ftq ff wfS wf =
  flat-ptr-bounds (worklist-push k) prog fs ff (λ { _ () }) wfS wf
ptr-bounds-step (worklist-pop k) prog fs r ftq ff wfS wf =
  flat-ptr-bounds (worklist-pop k) prog fs ff (λ { _ () }) wfS wf
ptr-bounds-step (worklist-check k) prog fs r ftq ff wfS wf =
  flat-ptr-bounds (worklist-check k) prog fs ff (λ { _ () }) wfS wf
ptr-bounds-step (instr-sigop si) prog fs r ftq ff wfS wf =
  flat-ptr-bounds (instr-sigop si) prog fs ff (λ { _ () }) wfS wf
ptr-bounds-step (instr-load-const p v) prog fs r ftq ff wfS wf =
  flat-ptr-bounds (instr-load-const p v) prog fs ff (λ { _ () }) wfS wf
ptr-bounds-step (instr-load-code-addr k) prog fs r ftq ff wfS wf =
  flat-ptr-bounds (instr-load-code-addr k) prog fs ff (λ { _ () }) wfS wf
ptr-bounds-step instr-save-closure-reg prog fs r ftq ff wfS wf =
  flat-ptr-bounds instr-save-closure-reg prog fs ff (λ { _ () }) wfS wf
ptr-bounds-step (instr-load-tag-lit k) prog fs r ftq ff wfS wf =
  flat-ptr-bounds (instr-load-tag-lit k) prog fs ff (λ { _ () }) wfS wf
ptr-bounds-step (instr-reg-op op) prog fs r ftq ff wfS wf =
  flat-ptr-bounds (instr-reg-op op) prog fs ff (λ { _ () }) wfS wf
ptr-bounds-step (instr-ctrl c) prog fs r ftq ff wfS wf =
  flat-ptr-bounds (instr-ctrl c) prog fs ff (λ { _ () }) wfS wf

-- THE RUN INDUCTION, carrying the store-WF invariant alongside (the alloc
-- step's freshness needs it at every PRE state, and `EntryLike` — all-tag
-- registers, empty memories — starts both off).
run-wf-ptr-bounds : ∀ prog (fs : FlatState) (r : RunAt prog fs)
                  → FlatWF fs × PtrBoundsWF fs
run-wf-ptr-bounds prog fs (mkRunAt em reach) = go fs reach
  where go : ∀ (fs' : FlatState) → Reachable prog 0 fs'
           → FlatWF fs' × PtrBoundsWF fs'
        go fs' (reach-start .fs' el _ _) = entry-flat-wf fs' el , entry-ptr-bounds fs' el
        go .(flat-exec-instr i prog fs'') (reach-step i fs'' r' ftq h) =
          let ih = go fs'' r' in
          flat-wf-step i prog fs'' (proj₁ ih) ,
          ptr-bounds-step i prog fs'' (mkRunAt em r') ftq
            (frame-op-absurd prog fs'' i em ftq)
            (proj₁ ih) (proj₂ ih)

run-ptr-bounds : ∀ prog (fs : FlatState) (r : RunAt prog fs) → PtrBoundsWF fs
run-ptr-bounds prog fs r = proj₂ (run-wf-ptr-bounds prog fs r)

------------------------------------------------------------------------
-- THE DATAFLOW DISCIPLINES ARE THEOREMS (D367).
--
-- Each fact below is "this site's step does not fault": the abstract machine
-- faults exactly where a target could not follow (a load or store through a
-- non-pointer, an unwritten slot, a tag branch on anything but a tag or a heap
-- pointer, `out-nz` on anything but an `Int` word — `LocState.faulted`), and
-- the program's run never faults (`RunAt.run-sound`, which the apex reads off
-- `ir-obs-correct`). So each is one step of the run, computed: the failing
-- shapes compute `faulted ≡ true`, which the run refutes.
--
-- They replace the plan 0.62 route (a typed shape checker over the emitted
-- trace, M2b, plus run consistency, M3) — two postulates, the first of them
-- false (`c-start` drops every claim, so a pair fails the check under every
-- label environment). The facts are now stated about the run that happens,
-- not about a static approximation of it.
------------------------------------------------------------------------

-- the site's step, from a reached running state, has not faulted
step-ok : ∀ prog (fs : FlatState) (i : AbstractInstr) → RunAt prog fs
        → halted (floc fs) ≡ false → fetch prog (fpc fs) ≡ just i
        → LocState.faulted (floc (flat-exec-instr i prog fs)) ≡ false
step-ok prog fs i r h ftq = run-sound r ((h , ftq) ∷ [])

private
  true≢false : true ≡ false → ⊥
  true≢false ()

  -- a register read, generalised to an equation
  at : ∀ {A : Set} (f : A → Bool) {x y : A} → x ≡ y → f x ≡ false → f y ≡ false
  at f e ok = subst (λ z → f z ≡ false) e ok

-- THE SLOT READS. `SlotRead i slot`: `i` reads `slot` of the current frame.
data SlotRead : AbstractInstr → Slot → Set where
  sr-load    : ∀ {slot} → SlotRead (load-from-slot slot) slot
  sr-restore : ∀ {slot} → SlotRead (restore-input slot) slot
  sr-pop     : ∀ {slot} → SlotRead (worklist-pop slot) slot

-- A SLOT READ NEVER FINDS AN UNWRITTEN SLOT (Plan 0.54 rung D).
--
-- This is what makes the `*-empty-*` routes UNREACHABLE: with `Window`
-- one-directional an empty-slot read would be a genuine DIVERGENCE (abstract
-- stops, concrete reads the previous frame's data). The read of an unwritten
-- slot faults (`exec-load-from-slot-with-value nothing`), and the run does not.
slot-read-written : ∀ prog (fs : FlatState) (slot : Slot) (i : AbstractInstr) → RunAt prog fs
                  → halted (floc fs) ≡ false
                  → fetch prog (fpc fs) ≡ just i → SlotRead i slot
                  → stackMem (floc fs) (current-frame (falloc fs)) slot ≡ nothing → ⊥
slot-read-written prog fs slot .(load-from-slot slot) r h ftq sr-load empty =
  true≢false (at (λ mv → LocState.faulted (proj₁ (exec-load-from-slot-with-value mv (floc fs) (falloc fs)))) empty
                 (slot-go-ok (load-from-slot slot) prog fs refl (step-ok prog fs (load-from-slot slot) r h ftq)))
slot-read-written prog fs slot .(restore-input slot) r h ftq sr-restore empty =
  true≢false (at (λ mv → LocState.faulted (proj₁ (exec-restore-input-with-value mv (floc fs) (falloc fs)))) empty
                 (slot-go-ok (restore-input slot) prog fs refl (step-ok prog fs (restore-input slot) r h ftq)))
slot-read-written prog fs slot .(worklist-pop slot) r h ftq sr-pop empty =
  true≢false (at (λ mv → LocState.faulted (proj₁ (exec-load-from-slot-with-value mv (floc fs) (falloc fs)))) empty
                 (slot-go-ok (worklist-pop slot) prog fs refl (step-ok prog fs (worklist-pop slot) r h ftq)))

-- THE LOAD/STORE TARGET DISCIPLINE: at an emitted load or store site `Input1`
-- holds a POINTER — a resolution of anything else faults. (For a store this
-- is what retired `store-indirect{,-suc}-bad`: the concrete `mov [rdi],rax`
-- through a non-pointer writes at the value's encoding and continues.)
private
  -- the four through-`Input1` sites, by their resolution
  ptr-of : ∀ (fault : Maybe (ValueLocation FS) → Bool) (v : StoredValue FS)
         → fault nothing ≡ true → fault (sv-as-loc v) ≡ false
         → Σ (ValueLocation FS) (λ loc → v ≡ SV-Ptr loc)
  ptr-of fault (SV-Ptr loc)    ft ok = loc , refl
  ptr-of fault (SV-Tag _)      ft ok = ⊥-elim (true≢false (trans (sym ft) ok))
  ptr-of fault (SV-Lit _ _)    ft ok = ⊥-elim (true≢false (trans (sym ft) ok))
  ptr-of fault (SV-Code _)     ft ok = ⊥-elim (true≢false (trans (sym ft) ok))

  in1-ptr : ∀ (fs : FlatState) (fault : Maybe (ValueLocation FS) → Bool)
          → fault nothing ≡ true → fault (sv-as-loc (readReg (regs (floc fs)) Input1)) ≡ false
          → Σ (ValueLocation FS) (λ loc → readReg (regs (floc fs)) Input1 ≡ SV-Ptr loc)
  in1-ptr fs fault ft ok = ptr-of fault (readReg (regs (floc fs)) Input1) ft ok

load-indirect-target-ptr : ∀ prog (fs : FlatState) → RunAt prog fs → halted (floc fs) ≡ false
                         → fetch prog (fpc fs) ≡ just load-indirect
                         → Σ (ValueLocation FS) (λ loc →
                             readReg (regs (floc fs)) Input1 ≡ SV-Ptr loc)
load-indirect-target-ptr prog fs r h ftq =
  in1-ptr fs (λ ml → LocState.faulted (exec-load-via-resolved Output ml (floc fs))) refl
          (step-ok prog fs load-indirect r h ftq)

load-indirect-suc-target-ptr : ∀ prog (fs : FlatState) → RunAt prog fs → halted (floc fs) ≡ false
                             → fetch prog (fpc fs) ≡ just load-indirect-suc
                             → Σ (ValueLocation FS) (λ loc →
                                 readReg (regs (floc fs)) Input1 ≡ SV-Ptr loc)
load-indirect-suc-target-ptr prog fs r h ftq =
  in1-ptr fs (λ ml → LocState.faulted (exec-load-suc-via-resolved Output ml (floc fs))) refl
          (step-ok prog fs load-indirect-suc r h ftq)

-- Plan 0.123 A.4 step 4, by D367's route: a load through `Input1` never reads
-- an unwritten HEAP cell. Reading one faults (`exec-load-with-value … nothing`),
-- and the run never faults (`step-ok`). So nothing reads a cell before it is
-- written, and the emitted code needs no discipline of its own for it (the
-- slot twin is `slot-read-written` below).
heap-load-written : ∀ prog (fs : FlatState) (hl : HeapLocation) → RunAt prog fs
                  → halted (floc fs) ≡ false → fetch prog (fpc fs) ≡ just load-indirect
                  → readReg (regs (floc fs)) Input1 ≡ SV-Ptr (AtDynamic hl)
                  → heapMem (floc fs) hl ≡ nothing → ⊥
heap-load-written prog fs hl r h ftq i-eq empty =
  true≢false (at (λ mv → LocState.faulted (exec-load-with-value Output mv (floc fs))) empty
                 (at (λ v → LocState.faulted (exec-load-via-resolved Output (sv-as-loc v) (floc fs))) i-eq
                     (step-ok prog fs load-indirect r h ftq)))

heap-load-suc-written : ∀ prog (fs : FlatState) (hl : HeapLocation) → RunAt prog fs
                      → halted (floc fs) ≡ false → fetch prog (fpc fs) ≡ just load-indirect-suc
                      → readReg (regs (floc fs)) Input1 ≡ SV-Ptr (AtDynamic hl)
                      → heapMem (floc fs) (sucHL hl) ≡ nothing → ⊥
heap-load-suc-written prog fs hl r h ftq i-eq empty =
  true≢false (at (λ mv → LocState.faulted (exec-load-with-value Output mv (floc fs))) empty
                 (at (λ v → LocState.faulted (exec-load-suc-via-resolved Output (sv-as-loc v) (floc fs))) i-eq
                     (step-ok prog fs load-indirect-suc r h ftq)))

store-indirect-target-ptr : ∀ prog (fs : FlatState) → RunAt prog fs → halted (floc fs) ≡ false
                          → fetch prog (fpc fs) ≡ just store-indirect
                          → Σ (ValueLocation FS) (λ loc →
                              readReg (regs (floc fs)) Input1 ≡ SV-Ptr loc)
store-indirect-target-ptr prog fs r h ftq =
  in1-ptr fs (λ ml → LocState.faulted (exec-store-via-resolved ml (readReg (regs (floc fs)) Output) (floc fs))) refl
          (step-ok prog fs store-indirect r h ftq)

store-indirect-suc-target-ptr : ∀ prog (fs : FlatState) → RunAt prog fs → halted (floc fs) ≡ false
                              → fetch prog (fpc fs) ≡ just store-indirect-suc
                              → Σ (ValueLocation FS) (λ loc →
                                  readReg (regs (floc fs)) Input1 ≡ SV-Ptr loc)
store-indirect-suc-target-ptr prog fs r h ftq =
  in1-ptr fs (λ ml → LocState.faulted (exec-store-suc-via-resolved ml (readReg (regs (floc fs)) Output) (floc fs))) refl
          (step-ok prog fs store-indirect-suc r h ftq)

-- plan 0.123 B.4 α: THE OFFSET FORMS' SITES, by the same route. A load at an
-- offset reads a written cell (so a mapped one, `dom-written`); a store at an
-- offset writes a cell of its block (D385: anything else faults), so a mapped
-- one (`dom-sized`).
load-at-target-ptr : ∀ prog (fs : FlatState) (k : ℕ) → RunAt prog fs → halted (floc fs) ≡ false
                   → fetch prog (fpc fs) ≡ just (load-at k)
                   → Σ (ValueLocation FS) (λ loc → readReg (regs (floc fs)) Input1 ≡ SV-Ptr loc)
load-at-target-ptr prog fs k r h ftq =
  in1-ptr fs (λ ml → LocState.faulted (exec-load-at-resolved k Output (frame-gate (falloc fs) k ml) (floc fs))) refl
          (step-ok prog fs (load-at k) r h ftq)

-- D392: A PURE SIGOP'S ARGUMENT DECODED, at a non-faulting step — the site fact
-- `arith-sigop-run` reads its input from (its block computes from the words).
private
  ∨-false-l : ∀ a b → (a ∨ b) ≡ false → a ≡ false
  ∨-false-l false b _ = refl
  ∨-false-l true  b ()

  read-of : ∀ {X : Set} (m : Maybe X) → unread? m ≡ false → ∃ (λ x → m ≡ just x)
  read-of (just x) _ = x , refl
  read-of nothing ()

sigop-decodes : ∀ prog (fs : FlatState) {A B} (si : SigOpInfo A B) → RunAt prog fs → halted (floc fs) ≡ false
              → fetch prog (fpc fs) ≡ just (instr-sigop si) → effect si ≡ Pure
              → ∃ (λ a → decode-at (baseA si) (readReg (regs (floc fs)) Input1) (floc fs) ≡ just a)
sigop-decodes prog fs si r h ftq pe =
  read-of _ (subst (λ e → exec-sigop-faults-of e si (floc fs) ≡ false) pe
              (∨-false-l _ _ (step-ok prog fs (instr-sigop si) r h ftq)))

-- D452 (d): A SIGOP'S WINDOW CHECK PASSED, at a non-faulting step — its
-- argument's and its answer's words, when on the stack, are in a live window.
private
  ∨-false-r : ∀ a b → (a ∨ b) ≡ false → b ≡ false
  ∨-false-r false b e = e
  ∨-false-r true  b ()

  not-false : ∀ g → not g ≡ false → g ≡ true
  not-false true  _ = refl
  not-false false ()

sigop-gated : ∀ prog (fs : FlatState) {A B} (si : SigOpInfo A B) → RunAt prog fs → halted (floc fs) ≡ false
            → fetch prog (fpc fs) ≡ just (instr-sigop si)
            → sigop-gate (falloc fs) si (floc fs) ≡ true
sigop-gated prog fs si r h ftq =
  not-false _ (∨-false-l _ _ (∨-false-r (exec-sigop-faults si (floc fs)) _ (step-ok prog fs (instr-sigop si) r h ftq)))

heap-load-at-written : ∀ prog (fs : FlatState) (k : ℕ) (hl : HeapLocation) → RunAt prog fs
                     → halted (floc fs) ≡ false → fetch prog (fpc fs) ≡ just (load-at k)
                     → readReg (regs (floc fs)) Input1 ≡ SV-Ptr (AtDynamic hl)
                     → heapMem (floc fs) (offsetHL hl k) ≡ nothing → ⊥
heap-load-at-written prog fs k hl r h ftq i-eq empty =
  true≢false (at (λ mv → LocState.faulted (exec-load-with-value Output mv (floc fs))) empty
                 (at (λ v → LocState.faulted (exec-load-at-resolved k Output (frame-gate (falloc fs) k (sv-as-loc v)) (floc fs))) i-eq
                     (step-ok prog fs (load-at k) r h ftq)))

store-at-target-ptr : ∀ prog (fs : FlatState) (k : ℕ) → RunAt prog fs → halted (floc fs) ≡ false
                    → fetch prog (fpc fs) ≡ just (store-at k)
                    → Σ (ValueLocation FS) (λ loc → readReg (regs (floc fs)) Input1 ≡ SV-Ptr loc)
store-at-target-ptr prog fs k r h ftq =
  in1-ptr fs (λ ml → LocState.faulted (exec-store-at-resolved (block-size (falloc fs)) k (frame-gate (falloc fs) k ml)
                                         (readReg (regs (floc fs)) Output) (floc fs))) refl
          (step-ok prog fs (store-at k) r h ftq)

store-at-in-block : ∀ prog (fs : FlatState) (k : ℕ) (hl : HeapLocation) → RunAt prog fs
                  → halted (floc fs) ≡ false → fetch prog (fpc fs) ≡ just (store-at k)
                  → readReg (regs (floc fs)) Input1 ≡ SV-Ptr (AtDynamic hl)
                  → in-block? (block-size (falloc fs)) (AtDynamic (offsetHL hl k)) ≡ true
store-at-in-block prog fs k hl r h ftq i-eq = ib _ refl
  where
    ok : LocState.faulted (exec-store-at-resolved (block-size (falloc fs)) k (just (AtDynamic hl))
                             (readReg (regs (floc fs)) Output) (floc fs)) ≡ false
    ok = at (λ v → LocState.faulted (exec-store-at-resolved (block-size (falloc fs)) k (frame-gate (falloc fs) k (sv-as-loc v))
                                       (readReg (regs (floc fs)) Output) (floc fs))) i-eq
            (step-ok prog fs (store-at k) r h ftq)
    ib : ∀ b → in-block? (block-size (falloc fs)) (AtDynamic (offsetHL hl k)) ≡ b
       → in-block? (block-size (falloc fs)) (AtDynamic (offsetHL hl k)) ≡ true
    ib true  e = e
    ib false e = ⊥-elim (true≢false
      (at (λ b → LocState.faulted (exec-store-in-block b (AtDynamic (offsetHL hl k))
                                     (readReg (regs (floc fs)) Output) (floc fs))) e ok))

-- D452: AT A NON-FAULTING OFFSET LOAD OR STORE, THE GATE PASSED ITS LOCATION
-- (a stack location is a slot of a live window); a stack slot read is written;
-- an `addr-at` never sees a stack pointer (a heap block's address only).
load-at-gate-wf : ∀ prog (fs : FlatState) (k : ℕ) (loc : ValueLocation FS) → RunAt prog fs → halted (floc fs) ≡ false
             → fetch prog (fpc fs) ≡ just (load-at k) → readReg (regs (floc fs)) Input1 ≡ SV-Ptr loc
             → frame-gate (falloc fs) k (just loc) ≡ just loc
load-at-gate-wf prog fs k loc r h ftq i-eq = go (gate-or (falloc fs) k loc)
  where
    ok = at (λ v → LocState.faulted (exec-load-at-resolved k Output (frame-gate (falloc fs) k (sv-as-loc v)) (floc fs))) i-eq
            (step-ok prog fs (load-at k) r h ftq)
    go : (frame-gate (falloc fs) k (just loc) ≡ just loc) ⊎ (frame-gate (falloc fs) k (just loc) ≡ nothing)
       → frame-gate (falloc fs) k (just loc) ≡ just loc
    go (inj₁ g) = g
    go (inj₂ g) = ⊥-elim (true≢false (at (λ m → LocState.faulted (exec-load-at-resolved k Output m (floc fs))) g ok))

store-at-gate-wf : ∀ prog (fs : FlatState) (k : ℕ) (loc : ValueLocation FS) → RunAt prog fs → halted (floc fs) ≡ false
              → fetch prog (fpc fs) ≡ just (store-at k) → readReg (regs (floc fs)) Input1 ≡ SV-Ptr loc
              → frame-gate (falloc fs) k (just loc) ≡ just loc
store-at-gate-wf prog fs k loc r h ftq i-eq = go (gate-or (falloc fs) k loc)
  where
    ok = at (λ v → LocState.faulted (exec-store-at-resolved (block-size (falloc fs)) k (frame-gate (falloc fs) k (sv-as-loc v))
                                       (readReg (regs (floc fs)) Output) (floc fs))) i-eq
            (step-ok prog fs (store-at k) r h ftq)
    go : (frame-gate (falloc fs) k (just loc) ≡ just loc) ⊎ (frame-gate (falloc fs) k (just loc) ≡ nothing)
       → frame-gate (falloc fs) k (just loc) ≡ just loc
    go (inj₁ g) = g
    go (inj₂ g) = ⊥-elim (true≢false (at (λ m → LocState.faulted (exec-store-at-resolved (block-size (falloc fs)) k m
                                                                    (readReg (regs (floc fs)) Output) (floc fs))) g ok))

stack-load-at-written-wf : ∀ prog (fs : FlatState) (k : ℕ) (f : Frame) (j : ℕ) → RunAt prog fs
                      → halted (floc fs) ≡ false → fetch prog (fpc fs) ≡ just (load-at k)
                      → readReg (regs (floc fs)) Input1 ≡ SV-Ptr (AtStack f j)
                      → frame-gate (falloc fs) k (just (AtStack f j)) ≡ just (AtStack f j)
                      → stackMem (floc fs) f (k Data.Nat.+ j) ≡ nothing → ⊥
stack-load-at-written-wf prog fs k f j r h ftq i-eq g empty =
  true≢false (at (λ mv → LocState.faulted (exec-load-with-value Output mv (floc fs))) empty
               (at (λ m → LocState.faulted (exec-load-at-resolved k Output m (floc fs))) g
                 (at (λ v → LocState.faulted (exec-load-at-resolved k Output (frame-gate (falloc fs) k (sv-as-loc v)) (floc fs))) i-eq
                     (step-ok prog fs (load-at k) r h ftq))))

addr-at-not-stack-wf : ∀ prog (fs : FlatState) (k : ℕ) (f : Frame) (j : ℕ) → RunAt prog fs
                  → halted (floc fs) ≡ false → fetch prog (fpc fs) ≡ just (addr-at k)
                  → readReg (regs (floc fs)) Input1 ≡ SV-Ptr (AtStack f j) → ⊥
addr-at-not-stack-wf prog fs k f j r h ftq i-eq =
  true≢false (at (λ v → LocState.faulted (exec-addr-at-resolved (block-size (falloc fs)) k (heap-gate (sv-as-loc v)) (floc fs))) i-eq
                 (step-ok prog fs (addr-at k) r h ftq))

-- plan 0.123 B.4 α (D385): an address at an offset is a cell of its block, or
-- the step faults — so at an emitted `addr-at` it is.
addr-at-target-ptr : ∀ prog (fs : FlatState) (k : ℕ) → RunAt prog fs → halted (floc fs) ≡ false
                   → fetch prog (fpc fs) ≡ just (addr-at k)
                   → Σ (ValueLocation FS) (λ loc → readReg (regs (floc fs)) Input1 ≡ SV-Ptr loc)
addr-at-target-ptr prog fs k r h ftq =
  in1-ptr fs (λ ml → LocState.faulted (exec-addr-at-resolved (block-size (falloc fs)) k (heap-gate ml) (floc fs))) refl
          (step-ok prog fs (addr-at k) r h ftq)

addr-at-in-block : ∀ prog (fs : FlatState) (k : ℕ) (hl : HeapLocation) → RunAt prog fs
                 → halted (floc fs) ≡ false → fetch prog (fpc fs) ≡ just (addr-at k)
                 → readReg (regs (floc fs)) Input1 ≡ SV-Ptr (AtDynamic hl)
                 → in-block? (block-size (falloc fs)) (AtDynamic (offsetHL hl k)) ≡ true
addr-at-in-block prog fs k hl r h ftq i-eq = ib _ refl
  where
    ok : LocState.faulted (exec-addr-at-resolved (block-size (falloc fs)) k (just (AtDynamic hl)) (floc fs)) ≡ false
    ok = at (λ v → LocState.faulted (exec-addr-at-resolved (block-size (falloc fs)) k (heap-gate (sv-as-loc v)) (floc fs))) i-eq
            (step-ok prog fs (addr-at k) r h ftq)
    ib : ∀ b → in-block? (block-size (falloc fs)) (AtDynamic (offsetHL hl k)) ≡ b
       → in-block? (block-size (falloc fs)) (AtDynamic (offsetHL hl k)) ≡ true
    ib true  e = e
    ib false e = ⊥-elim (true≢false
      (at (λ b → LocState.faulted (exec-addr-in-block b (AtDynamic (offsetHL hl k)) (floc fs))) e ok))

addr-at-inbounds : ∀ prog (fs : FlatState) (k : ℕ) (hl : HeapLocation) → RunAt prog fs
                 → halted (floc fs) ≡ false → fetch prog (fpc fs) ≡ just (addr-at k)
                 → readReg (regs (floc fs)) Input1 ≡ SV-Ptr (AtDynamic hl)
                 → heap-offset (offsetHL hl k) < block-size (falloc fs) (ref-id (heap-ref (offsetHL hl k)))
addr-at-inbounds prog fs k hl r h ftq i-eq =
  <ᵇ⇒< (heap-offset (offsetHL hl k)) (block-size (falloc fs) (ref-id (heap-ref (offsetHL hl k))))
       (T-of (addr-at-in-block prog fs k hl r h ftq i-eq))
  where
    T-of : ∀ {b : Bool} → b ≡ true → T b
    T-of refl = tt

store-at-inbounds : ∀ prog (fs : FlatState) (k : ℕ) (hl : HeapLocation) → RunAt prog fs
                  → halted (floc fs) ≡ false → fetch prog (fpc fs) ≡ just (store-at k)
                  → readReg (regs (floc fs)) Input1 ≡ SV-Ptr (AtDynamic hl)
                  → heap-offset (offsetHL hl k) < block-size (falloc fs) (ref-id (heap-ref (offsetHL hl k)))
store-at-inbounds prog fs k hl r h ftq i-eq =
  <ᵇ⇒< (heap-offset (offsetHL hl k)) (block-size (falloc fs) (ref-id (heap-ref (offsetHL hl k))))
       (T-of (store-at-in-block prog fs k hl r h ftq i-eq))
  where
    T-of : ∀ {b : Bool} → b ≡ true → T b
    T-of refl = tt

-- plan 0.108 / D367: AT AN EMITTED `out-nz`, OUTPUT HOLDS AN `Int` WORD — the
-- comparison's arith block just wrote it; anything else faults (`do-nz`).
out-nz-output-word : ∀ prog (fs : FlatState) → RunAt prog fs → halted (floc fs) ≡ false
                   → fetch prog (fpc fs) ≡ just (instr-reg-op out-nz)
                   → ∃ λ w → readReg (regs (floc fs)) Output ≡ SV-Lit fits-int w
out-nz-output-word prog fs r h ftq = go (readReg (regs (floc fs)) Output) refl
  where
    ok = step-ok prog fs (instr-reg-op out-nz) r h ftq
    go : ∀ (v : StoredValue FS) → readReg (regs (floc fs)) Output ≡ v
       → ∃ λ w → readReg (regs (floc fs)) Output ≡ SV-Lit fits-int w
    go (SV-Lit fits-int w)   e = w , e
    go (SV-Lit fits-float _) e = ⊥-elim (true≢false (at (λ v → LocState.faulted (floc (do-nz v fs))) e ok))
    go (SV-Tag _)            e = ⊥-elim (true≢false (at (λ v → LocState.faulted (floc (do-nz v fs))) e ok))
    go (SV-Ptr _)            e = ⊥-elim (true≢false (at (λ v → LocState.faulted (floc (do-nz v fs))) e ok))
    go (SV-Code _)           e = ⊥-elim (true≢false (at (λ v → LocState.faulted (floc (do-nz v fs))) e ok))

-- the non-pointer routes of a store site are absurd
store-nonptr-absurd : ∀ prog (fs : FlatState) {v : StoredValue FS} → RunAt prog fs
                    → halted (floc fs) ≡ false
                    → fetch prog (fpc fs) ≡ just store-indirect
                    → readReg (regs (floc fs)) Input1 ≡ v
                    → (∀ (loc : ValueLocation FS) → v ≡ SV-Ptr loc → ⊥)
                    → ⊥
store-nonptr-absurd prog fs r h ftq i-eq nptr =
  nptr (proj₁ wits) (trans (sym i-eq) (proj₂ wits))
  where wits = store-indirect-target-ptr prog fs r h ftq

store-suc-nonptr-absurd : ∀ prog (fs : FlatState) {v : StoredValue FS} → RunAt prog fs
                        → halted (floc fs) ≡ false
                        → fetch prog (fpc fs) ≡ just store-indirect-suc
                        → readReg (regs (floc fs)) Input1 ≡ v
                        → (∀ (loc : ValueLocation FS) → v ≡ SV-Ptr loc → ⊥)
                        → ⊥
store-suc-nonptr-absurd prog fs r h ftq i-eq nptr =
  nptr (proj₁ wits) (trans (sym i-eq) (proj₂ wits))
  where wits = store-indirect-suc-target-ptr prog fs r h ftq

-- THE BRANCH SCRUTINEE (D073, D367): at an emitted `c-branch-tag-zero` site
-- `Input1` points at a WRITTEN cell holding a TAG — a sum's, or a cata stack's
-- sentinel — or a HEAP POINTER — a cata stack's top element, a μ node. Before
-- D367 this claimed a tag outright, and that was FALSE: the cata walk tests its
-- todo and eval stacks by reading the top element's word, which is a μ node's
-- address (`CataBr.Stack.word-nz-μ`). Every other shape faults (`tag-test`).
data TagCell : StoredValue FS → Set where
  tc-tag : ∀ (k : ℕ) → TagCell (SV-Tag k)
  tc-ptr : ∀ (hl : HeapLocation) → TagCell (SV-Ptr (AtDynamic hl))

branch-tag-scrutinee-wf : ∀ prog (fs : FlatState) (m : LabelId) → RunAt prog fs
                        → halted (floc fs) ≡ false
                        → fetch prog (fpc fs) ≡ just (instr-ctrl (c-branch-tag-zero m))
                        → Σ (ValueLocation FS) (λ loc → Σ (StoredValue FS) (λ v →
                            (readReg (regs (floc fs)) Input1 ≡ SV-Ptr loc)
                            × (readLoc (floc fs) loc ≡ just v) × TagCell v × (frame-gate (falloc fs) 0 (just loc) ≡ just loc)))
branch-tag-scrutinee-wf prog fs m r h ftq = go-in1 (readReg (regs (floc fs)) Input1) refl
  where
    ok = step-ok prog fs (instr-ctrl (c-branch-tag-zero m)) r h ftq
    -- the fault flag of the branch, as a function of what it reads
    flt : Maybe (StoredValue FS) → Bool
    flt mv = LocState.faulted (floc (do-branch-test (tag-test mv) m prog fs))
    -- through the frame gate (D452): it passes the location, or the branch faults
    rd : StoredValue FS → Bool
    rd v = flt (flat-read-at (floc fs) (frame-gate (falloc fs) 0 (sv-as-loc v)))
    go-cell : ∀ (loc : ValueLocation FS) → readReg (regs (floc fs)) Input1 ≡ SV-Ptr loc
            → frame-gate (falloc fs) 0 (just loc) ≡ just loc
            → ∀ (mv : Maybe (StoredValue FS)) → readLoc (floc fs) loc ≡ mv
            → Σ (ValueLocation FS) (λ loc → Σ (StoredValue FS) (λ v →
                (readReg (regs (floc fs)) Input1 ≡ SV-Ptr loc)
                × (readLoc (floc fs) loc ≡ just v) × TagCell v × (frame-gate (falloc fs) 0 (just loc) ≡ just loc)))
    go-cell loc ie g (just (SV-Tag k))              re = loc , SV-Tag k , ie , re , tc-tag k , g
    go-cell loc ie g (just (SV-Ptr (AtDynamic hl))) re = loc , _ , ie , re , tc-ptr hl , g
    -- D452: a stack pointer has no tag (`tag-test` faults)
    go-cell loc ie g (just (SV-Ptr (AtStack f k)))  re =
      ⊥-elim (true≢false (at flt re (at (λ z → flt (flat-read-at (floc fs) z)) g (at rd ie ok))))
    go-cell loc ie g (just (SV-Lit _ _))            re =
      ⊥-elim (true≢false (at flt re (at (λ z → flt (flat-read-at (floc fs) z)) g (at rd ie ok))))
    go-cell loc ie g (just (SV-Code _))             re =
      ⊥-elim (true≢false (at flt re (at (λ z → flt (flat-read-at (floc fs) z)) g (at rd ie ok))))
    go-cell loc ie g nothing                        re =
      ⊥-elim (true≢false (at flt re (at (λ z → flt (flat-read-at (floc fs) z)) g (at rd ie ok))))
    go-gate : ∀ (loc : ValueLocation FS) → readReg (regs (floc fs)) Input1 ≡ SV-Ptr loc
            → (frame-gate (falloc fs) 0 (just loc) ≡ just loc) ⊎ (frame-gate (falloc fs) 0 (just loc) ≡ nothing)
            → Σ (ValueLocation FS) (λ loc → Σ (StoredValue FS) (λ v →
                (readReg (regs (floc fs)) Input1 ≡ SV-Ptr loc)
                × (readLoc (floc fs) loc ≡ just v) × TagCell v × (frame-gate (falloc fs) 0 (just loc) ≡ just loc)))
    go-gate loc ie (inj₁ g) = go-cell loc ie g (readLoc (floc fs) loc) refl
    go-gate loc ie (inj₂ g) = ⊥-elim (true≢false (at (λ z → flt (flat-read-at (floc fs) z)) g (at rd ie ok)))
    go-in1 : ∀ (v : StoredValue FS) → readReg (regs (floc fs)) Input1 ≡ v
           → Σ (ValueLocation FS) (λ loc → Σ (StoredValue FS) (λ v →
               (readReg (regs (floc fs)) Input1 ≡ SV-Ptr loc)
               × (readLoc (floc fs) loc ≡ just v) × TagCell v × (frame-gate (falloc fs) 0 (just loc) ≡ just loc)))
    go-in1 (SV-Ptr loc) ie = go-gate loc ie (gate-or (falloc fs) 0 loc)
    go-in1 (SV-Tag _)   ie = ⊥-elim (true≢false (at rd ie ok))
    go-in1 (SV-Lit _ _) ie = ⊥-elim (true≢false (at rd ie ok))
    go-in1 (SV-Code _)  ie = ⊥-elim (true≢false (at rd ie ok))

------------------------------------------------------------------------

-- THE FOUR IN-BOUNDS FACTS THE BLOCK-STEPS CONSUME, now read off the
-- invariant (the store pair was residual until 2026-08-01; the load pair
-- combines the `-target-ptr` residual's pointer shape with the theorem).
store-indirect-inbounds : ∀ prog (fs : FlatState) (hl : HeapLocation) → RunAt prog fs
                        → fetch prog (fpc fs) ≡ just store-indirect
                        → readReg (regs (floc fs)) Input1 ≡ SV-Ptr (AtDynamic hl)
                        → heap-offset hl < block-size (falloc fs) (ref-id (heap-ref hl))
store-indirect-inbounds prog fs hl r ftq eq =
  ptr-bounds-cell fs Input1 hl (run-ptr-bounds prog fs r) eq

store-indirect-suc-inbounds : ∀ prog (fs : FlatState) (hl : HeapLocation) → RunAt prog fs
                            → fetch prog (fpc fs) ≡ just store-indirect-suc
                            → readReg (regs (floc fs)) Input1 ≡ SV-Ptr (AtDynamic hl)
                            → heap-offset (sucHL hl) < block-size (falloc fs) (ref-id (heap-ref (sucHL hl)))
-- plan 0.123 B.4 α: the four fixed-offset forms are retired (out of both
-- fences), so an emitted program never fetches one — and `PtrB` no longer says
-- anything about the next cell.
store-indirect-suc-inbounds prog fs hl r ftq eq =
  ⊥-elim (frame-op-absurd prog fs store-indirect-suc (run-emitted r) ftq)

load-indirect-target-wf : ∀ prog (fs : FlatState) → RunAt prog fs → halted (floc fs) ≡ false
                        → fetch prog (fpc fs) ≡ just load-indirect
                        → Σ (ValueLocation FS) (λ loc →
                            (readReg (regs (floc fs)) Input1 ≡ SV-Ptr loc)
                            × (∀ hl → loc ≡ AtDynamic hl
                               → heap-offset hl < block-size (falloc fs) (ref-id (heap-ref hl))))
load-indirect-target-wf prog fs r h ftq with load-indirect-target-ptr prog fs r h ftq
... | loc , eq = loc , eq ,
  λ hl leq → ptr-bounds-cell fs Input1 hl (run-ptr-bounds prog fs r)
               (trans eq (cong SV-Ptr leq))

load-indirect-suc-target-wf : ∀ prog (fs : FlatState) → RunAt prog fs → halted (floc fs) ≡ false
                            → fetch prog (fpc fs) ≡ just load-indirect-suc
                            → Σ (ValueLocation FS) (λ loc →
                                (readReg (regs (floc fs)) Input1 ≡ SV-Ptr loc)
                                × (∀ hl → loc ≡ AtDynamic hl
                                   → heap-offset (sucHL hl) < block-size (falloc fs) (ref-id (heap-ref (sucHL hl)))))
load-indirect-suc-target-wf prog fs r h ftq =
  ⊥-elim (frame-op-absurd prog fs load-indirect-suc (run-emitted r) ftq)


------------------------------------------------------------------------
-- THE CALL WINDOW IS ONE STEP WIDE, AND ITS INSTRUCTION IS A BODY MARKER
-- (plan 0.65 G2, 2026-08-16).
--
-- `flink ≡ just _` says a call has happened and the callee has not spilled its
-- return address yet. The callee's FIRST instruction is its own `c-thunk`: a
-- call lands the pc on `find-thunk prog ℓ`, and `find-thunk-sound` — already a
-- theorem — says what that index fetches.
--
-- WHY IT EARNS ITS KEEP. Without it, every block-step that is NOT the body
-- marker would have to show it leaves the link alone: 41 obligations per arch,
-- and on x86-64 the claim is not even true in general, since its link lives at
-- `[rsp]` and a slot store can reach that address. With it, the engine hands
-- those fields `flink fs ≡ nothing` and each discharges its link component by
-- absurdity. One induction instead of 82 proofs.
--
-- The induction is `Reachable`, and every case is a clash rather than an
-- argument:
--
--   entry        `EntryLike` says `flink ≡ nothing`.
--   after a call `callView`: the halting route preserves the link and hands
--                the clash to the IH; the entering route IS the theorem.
--   after a body marker  `do-thunk` clears the link.
--   after anything else  `FlinkView`'s `fv-pres` threads it, so the IH applies
--                at the PRE-state and says the fetched instruction was a body
--                marker — whereupon `fv-pres` at THAT instruction says the
--                link was cleared, contradicting it being live.
------------------------------------------------------------------------
private
  nothing≢justℕ : ∀ {x : ℕ} → nothing ≡ just x → ⊥
  nothing≢justℕ ()

run-link-at-thunk : ∀ prog (fs : FlatState) → RunAt prog fs
                  → ∀ {r : ℕ} → flink fs ≡ just r
                  → Σ EntryId (λ ℓ → Σ ℕ (λ bb →
                      fetch prog (fpc fs) ≡ just (instr-ctrl (c-entry ℓ bb))))
run-link-at-thunk prog fs (mkRunAt em reach) = go fs reach
  where
    Goal : FlatState → Set
    Goal fs' = Σ EntryId (λ ℓ → Σ ℕ (λ bb →
                 fetch prog (fpc fs') ≡ just (instr-ctrl (c-entry ℓ bb))))

    go : ∀ (fs' : FlatState) → Reachable prog 0 fs'
       → ∀ {r : ℕ} → flink fs' ≡ just r → Goal fs'
    go fs' (reach-start .fs' (_ , _ , _ , _ , _ , _ , _ , _ , _ , fl , _) _ _) lk =
      ⊥-elim (nothing≢justℕ (trans (sym fl) lk))
    go .(flat-exec-instr i prog fs'') (reach-step i fs'' r' ftq h) {r} lk =
      step (flinkView i)
      where
        -- the IH, once the link is known live at the PRE-state
        ih-thunk : flink fs'' ≡ just r → Σ EntryId (λ ℓ → Σ ℕ (λ bb →
                     i ≡ instr-ctrl (c-entry ℓ bb)))
        ih-thunk pre = proj₁ ihr , proj₁ (proj₂ ihr) ,
                       just-injective (trans (sym ftq) (proj₂ (proj₂ ihr)))
          where ihr = go fs'' r' pre

        step : FlinkView i → Goal (flat-exec-instr i prog fs'')
        -- THE CALL. `callView` splits into halt and enter.
        step (fv-call ieq) = call-step (callView prog fs'')
          where
            red : flat-exec-instr i prog fs'' ≡ do-call prog fs''
            red = cong (λ z → flat-exec-instr z prog fs'') ieq
            call-step : CallPost prog fs'' → Goal (flat-exec-instr i prog fs'')
            -- a HALTING call writes no link, so the link was already live and
            -- the IH says the pc held a body marker — but `ftq` says it held
            -- the call.
            call-step (cp-fault heq) =
              ⊥-elim (thunk≢call (proj₂ (proj₂ (ih-thunk pre))))
              where
                pre : flink fs'' ≡ just r
                pre = trans (sym (cong flink (trans red heq))) lk
                thunk≢call : ∀ {ℓ bb} → i ≡ instr-ctrl (c-entry ℓ bb) → ⊥
                thunk≢call teq with trans (sym teq) ieq
                ... | ()
            -- and an ENTERING call is the theorem: its pc IS the resolved
            -- body index, and `find-thunk-sound` says what sits there.
            call-step (cp-enter ℓ j hl ce he feq eeq) =
              e-thunk ℓ , proj₁ fts ,
              subst (λ z → fetch prog z ≡ just (instr-ctrl (c-thunk ℓ (proj₁ fts))))
                    (sym (cong fpc (trans red eeq))) (proj₂ fts)
              where fts = find-thunk-sound prog ℓ j feq
        -- D245: THE DIRECT CALL, split on its static scan: a miss halts and
        -- writes no link (so the IH clashes with the call itself), a hit lands
        -- on the function's entry.
        step (fv-call-fn f ieq) = cf-step (find-fn prog f) refl
          where
            red : flat-exec-instr i prog fs'' ≡ do-call-at (find-fn prog f) fs''
            red = cong (λ z → flat-exec-instr z prog fs'') ieq
            entry≢callfn : ∀ {ℓ bb} → i ≡ instr-ctrl (c-entry ℓ bb) → ⊥
            entry≢callfn teq with trans (sym teq) ieq
            ... | ()
            cf-step : ∀ (mj : Maybe ℕ) → find-fn prog f ≡ mj → Goal (flat-exec-instr i prog fs'')
            cf-step nothing fe =
              ⊥-elim (entry≢callfn (proj₂ (proj₂ (ih-thunk pre))))
              where
                pre : flink fs'' ≡ just r
                pre = trans (sym (cong flink (trans red (cong (λ z → do-call-at z fs'') fe)))) lk
            cf-step (just j) fe =
              e-fn f , proj₁ fes ,
              subst (λ z → fetch prog z ≡ just (instr-ctrl (c-entry (e-fn f) (proj₁ fes))))
                    (sym (cong fpc (trans red (cong (λ z → do-call-at z fs'') fe)))) (proj₂ fes)
              where fes = find-entry-sound prog (e-fn f) j fe
        -- THE BODY MARKER clears the link, so it cannot be live after one.
        step (fv-thunk ℓ bb ieq) =
          ⊥-elim (nothing≢justℕ (trans (sym cleared) lk))
          where cleared : flink (flat-exec-instr i prog fs'') ≡ nothing
                cleared = cong (λ z → flink (flat-exec-instr z prog fs'')) ieq
        -- plan 0.107: …and so does the START (the same `do-thunk`).
        step (fv-start bb ieq) =
          ⊥-elim (nothing≢justℕ (trans (sym cleared) lk))
          where cleared : flink (flat-exec-instr i prog fs'') ≡ nothing
                cleared = cong (λ z → flink (flat-exec-instr z prog fs'')) ieq
        -- EVERYTHING ELSE threads the link, so the IH applies at the
        -- pre-state and says the instruction was a body marker — which this
        -- very equation then says cleared the link.
        step (fv-pres pres) =
          ⊥-elim (nothing≢justℕ (trans (sym cleared) pre))
          where
            pre : flink fs'' ≡ just r
            pre = trans (sym (pres prog fs'')) lk
            ihr = ih-thunk pre
            cleared : flink fs'' ≡ nothing
            cleared = trans (sym (pres prog fs''))
                            (cong (λ z → flink (flat-exec-instr z prog fs''))
                                  (proj₂ (proj₂ ihr)))

-- …AND THE FORM THE ENGINE ACTUALLY CONSUMES. `bs-call` and `bs-c-ret` need
-- `flink fs ≡ nothing` — both READ the head return cell, so they need
-- `ret-eq`'s memory row rather than the arch's link claim — and the engine is
-- the only layer that can supply it, because it holds the `RunAt`. The
-- contrapositive of the lemma above at a fetch that is not a body marker.
--
-- With-free by the standard aux (`de-with by parameterizing the equation`):
-- the split is on `flink fs`, which is not a pattern position.
run-link-nothing-aux : ∀ prog (fs : FlatState) → RunAt prog fs
                     → (∀ (ℓ : EntryId) (bb : ℕ)
                          → fetch prog (fpc fs) ≡ just (instr-ctrl (c-entry ℓ bb)) → ⊥)
                     → ∀ (m : Maybe ℕ) → flink fs ≡ m → flink fs ≡ nothing
run-link-nothing-aux prog fs ra nt nothing  eq = eq
run-link-nothing-aux prog fs ra nt (just r) eq =
  ⊥-elim (nt (proj₁ res) (proj₁ (proj₂ res)) (proj₂ (proj₂ res)))
  where res = run-link-at-thunk prog fs ra eq

run-link-nothing : ∀ prog (fs : FlatState) → RunAt prog fs
                 → (∀ (ℓ : EntryId) (bb : ℕ)
                      → fetch prog (fpc fs) ≡ just (instr-ctrl (c-entry ℓ bb)) → ⊥)
                 → flink fs ≡ nothing
run-link-nothing prog fs ra nt = run-link-nothing-aux prog fs ra nt (flink fs) refl

