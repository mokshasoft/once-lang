-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.ArchCorrectness.FlatFromObs  (Plan 0.53-step2 / Phase B L1;
-- Plan 0.54 rung A step-7 rewire 2026-07-20)
--
-- Shared, arch-parametric construction of the per-arch `ArchCorrect` record.
--
-- D320: what it provides is how the PROGRAM'S FLAT RUN ENDS (`flat-ends`): the
-- start, `main`'s run (the entry witness `ir-obs-correct` supplies), and the
-- program's leave — the meaning's calls and how its run ended. The concrete
-- correspondence (`events-agree-start`) runs to exactly that point, and the
-- binary's trace follows (`ArchCorrectness.<arch>.conc-tr`).
--
-- Residual introduced (narrow + named, replacing the opaque whole-statement
-- postulate): the ENTRY STATE and its preconditions — `ArchCorrectness.agda`
-- already flags these as "provable (no new mathematics)". `ValidAtWF` at `Unit`
-- is literally `valid-unit-wf`; the rest is loader/initial-frame plumbing.
------------------------------------------------------------------------

open import Data.Nat using (suc)
open import Once.Adequacy.CPU.Interface using (ArchSemantics)
open import Once.Target.Arch using (Arch)
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.Target.Arch using (arch-numerics)
open import Relation.Binary.PropositionalEquality using (_≡_)

-- Plan 0.63 (D089): parameterised by the DEFINITION'S identity, which keys its
-- labels. `o` is constant for a whole definition, so it belongs on the module
-- rather than on every lemma — which is what keeps the statements below
-- UNCHANGED: the emitter is imported APPLIED, so each call site reads as before.
open import Once.Spec.Name using (CanonicalName)

open import Data.List using (List)
open import Once.Denotation.Program using (IRFun; irProgram; Linked; LinkedProgram)
open Once.Denotation.Program.IRFun using (fbody; fname)
open import Once.Internal.Contract using (ISig)
import Once.Internal.Trace as TM
import Once.CCC.FrameSemantics
module Once.Adequacy.ArchCorrectness.FlatFromObs (o : CanonicalName) (tbl : List IRFun)
  (arch          : Arch)
  (FS            : FrameSemantics)
  -- Plan 0.54 rung D: the loader's initial FRAME is supplied BY THE ARCH, not
  -- postulated here. It used to be `postulate entry-frame : Frame FS` — opaque,
  -- so nothing about it could ever be proven, which is exactly why the apex
  -- needed a SECOND postulate (`entry-frame-base`) to say where its base was.
  -- As a parameter the arch can hand over a CONSTRUCTED frame and that second
  -- postulate becomes `refl` (x86-64 does; see `…ArchCorrectness.X86-64`).
  -- THE TWO CHANNELS FOR THE FORMAT MUST AGREE (plan 0.73, D113/D114).
  --
  -- The machine reads it from `FrameSemantics.float-format FS`; the apex reads
  -- it from `arch-float-format arch`. Both are stated independently — one is a
  -- field of the frame semantics, the other a fact about the target enum — and
  -- nothing makes them the same until it is SAID. Here is where it is said,
  -- and where a disagreement becomes a type error instead of a wrong binary:
  -- `arch-numerics`' own comment promises exactly this check.
  --
  -- D115: it now covers BOTH numeric facts at once — the float format AND the
  -- int width — because `TargetNum` carries them together, so neither can
  -- drift from the machine's view on its own.
  --
  -- A PARAMETER, not a postulate: every instantiation discharges it by `refl`,
  -- so it costs nothing and cannot be forgotten.
  (fmt-agree     : Once.CCC.FrameSemantics.fs-numerics FS ≡ arch-numerics arch)
  (entry-frame   : FrameSemantics.Frame FS)
  (as            : ArchSemantics)
  where

open import Data.Bool using (false)
open import Data.List using (List; []; take)
open import Data.Maybe using (just; nothing)
import Data.Maybe
open import Data.Product using (proj₁)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

open import Once.IR using (IR; Stack)
open import Once.IRTy using (Unit)
open import Once.Denotation.Behavior using (Behavior)
open Once.Denotation.Behavior.Behavior using (at)
open import Once.Internal.Event using (SigOpEvent)
open import Once.CCC.Codegen.ProgramImage using (program-image; fns-image; fn-next)
import Once.CCC.Codegen.CataIRSlotStable as CIS
open import Data.List.Relation.Unary.All using ([]; _∷_)
open import Data.List.Relation.Unary.All.Properties using (++⁺)
open import Data.Product using (_×_; _,_)
open import Once.CCC.Label using (LabelId)
open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality using (subst)
open import Once.CCC.Codegen.IRObsCorrectFlat o tbl using (module IRObsCorrectFlatness)
open import Once.CCC.Codegen.IRToTrace o using (ir-to-trace; ir-stack-budget; ir-next-label)
open import Once.CCC.Codegen.BlockLayout using (module Layout)
open import Once.CCC.Codegen.LabelsUnique o using (module Unique)
open Layout {FS} using (NoThunks; missBefore-from; blocks-at)
open import Data.List using (_++_; _∷_)
open import Once.CCC.Machine.SMCore using (instr-ctrl; c-ret; c-start; c-label; c-jmp; blocks-layout; block-layout; AbstractTrace; e-thunk; AllocState; mkAllocState; module AllocState; c-leave)
open AllocState using (next-slot)
open import Data.List.Properties using (++-assoc)
open import Data.List.Properties using (++-identityʳ)
open import Once.Internal.Out using (_▹_)
open import Once.Denotation.TraceTr using (endOf)
open import Data.List using (length)
open import Data.Unit using (⊤; tt)
open import Data.Bool using (true; false)
open import Relation.Binary.PropositionalEquality using (cong₂)
open import Once.Internal.Res using (Res; returns; stopped; is-stopped)
open import Once.Denotation.Approx using (Ap; done; cut; budgetLeft; endAp)
open import Data.Nat.Properties using (≤-trans; ≤-reflexive; m≤m+n; n≤1+n)
open import Once.Spec.Trace using (End; returned) renaming (halted to halted-end)
-- D158: the entry instance supplies the PLACEMENT — the whole program is the
-- fragment, at offset 0.
open import Data.Nat.Properties using (+-identityʳ; +-comm)
open import Once.CCC.Machine.SMCore
  using (LocState; mkLocState; Registers; mkRegs; SV-Tag; module LocState)
open LocState using (halted)
open import Once.CCC.Machine.Locations using (ValueLocation; AtDynamic)
open import Once.Memory.HeapAddress using (heap-loc; mkHeapRef)
open import Data.Nat using (z≤n; s≤s; _≤_; _+_)
open import Once.CCC.Machine.Allocation
  using (module FrontierInvariant)
open import Once.CCC.Machine.Flat using (module FlatMachine)
open import Once.Adequacy.FlatEvents using (module FlatEventTrace)
import Once.Compile as C
import Once.Parser.Module.Core as P
-- D100: the assembler's own precondition — the emitted local labels are
-- pairwise distinct. Consumed by `AsmTraceCorrect` below.

open IRObsCorrectFlatness {FS} using (IRObsCorrectF; BlockRuns; MachineRefinesObsF; ValueRealized; in-unit; SpanAt; LabelsAt; emitted; BlocksAt; blocks; eventsAt; resultAt; evalᴰ; ⟪_⟫_; chain-ctrls)
open FlatMachine {FS} using (mkFlat; fetch; fetch-++-left; fetch-++-right; fpc; find-label; ft-go-prefix; FlatState; flat-exec-instr; floc; falloc)
open import Once.CCC.Codegen.FlatStepLemmas using (module FlatStepsAPI)
open FlatStepsAPI {FS} using (fl-go-prefix; fl-go-shift)
open import Once.CCC.Codegen.CataNextSlot using (module CataNextSlot)
open CataNextSlot {FS} using (AllSlotStable)
open FlatEventTrace {FS} using (flat-events; chain-events; flat-events-steps; flat-ctrls; flat-ctrls-steps)
open FrontierInvariant {FS} using (BeforeFrontier; heap-before)

-- (plan 0.107: `asm-sem` — the text's meaning — is gone; the file's run is
-- `ArchSemantics.run-trace`, and the text is its print.)

------------------------------------------------------------------------
-- The ENTRY STATE residual (narrow, named; replaces the opaque postulates).
-- The loader hands `main` a fresh frame: nothing allocated (`next-slot ≡ 0`),
-- not halted. `main`'s (erased) Unit argument has no residence (D074) —
-- every register starts as the tag filler `SV-Tag 0`.
------------------------------------------------------------------------

-- The loader's initial FRAME is the genuine external trust point (FrameSemantics
-- documents program entry as exactly that: "we trust the OS/runtime set up
-- sufficient space before calling our code"). `Frame` is abstract, so it cannot
-- be constructed here. Everything ELSE about the entry state is now CONSTRUCTED,
-- and its preconditions are PROVED (was: 8 postulates, now 2).
-- D213 / plan 0.91 S1: `entry-size : ∀ ir → ir-size ir < program-bound` STOOD
-- HERE and was FALSE — `program-bound` is universally quantified inside this
-- module while `ir-size` is unbounded, so `big n = id ∘ id ∘ …` at
-- `n := program-bound` refutes it. It is GONE, not narrowed: the premise it
-- discharged has been deleted from `IRObsCorrectF` itself, because
-- `ir-obs-correct` recurses STRUCTURALLY on the IR and never read the bound as
-- a fact — every use only weakened it to a sub-term to feed a sub-IH
-- (`comp-size-f`/`comp-size-g`, `szf`/`szg`). D170 had already removed the one
-- place that consumed it (`body<bound` in `valid-closure-wf`). The whole
-- `program-bound` telescope is removed with it.

-- A fresh frame: nothing on the stack (`next-slot ≡ 0`), one heap ref reserved
-- for the (erased) `Unit` argument cell so it is `BeforeFrontier`.
-- Plan 0.63: the entry allocator is now indexed by the frame the prologue
-- reserved, because the reserved slot count lives WITH the frame
-- (`frame-slots`) instead of in the register file.
entry-alloc : ℕ → AllocState {FS}
-- the entry allocator: one ref reserved for the erased Unit cell, and NO block
-- has a size yet (the entry heap is empty, so `block-size ≡ λ _ → 0` — which makes
-- the correspondence's in-bounds coverage vacuously true at entry)
entry-alloc slots = mkAllocState entry-frame [] slots 0 1 (λ _ → 0)

entry-loc : ValueLocation FS
entry-loc = AtDynamic (heap-loc (mkHeapRef 0) 0)

-- D074: EVERY filler is a TAG. `main`'s (erased) Unit argument has no
-- residence (`in-unit`), so nothing requires Input1 to be a pointer — and a
-- pointer filler into the sizeless block 0 is exactly what made the heap
-- in-bounds invariant FALSE at entry. `SV-Tag 0` encodes to 0 just as the
-- pointer filler did (`enc-sv (SV-Tag 0) = 0`), so `entry-corr` is unchanged;
-- with no pointer anywhere in the entry state the in-bounds invariant holds
-- vacuously at the start of the run. (Plan 0.54 D item 4 made `Scratch` and
-- `Count` tags for `FlatRegTagWF`'s entry case; this finishes the move.)
entry-regs : Registers FS
entry-regs = mkRegs (SV-Tag 0) (SV-Tag 0) (SV-Tag 0) (SV-Tag 0)

-- THE ENTRY STATE IS INDEXED BY THE FRAME THE PROLOGUE RESERVED (2026-07-30).
--
-- `frame-slots` — the runtime slot counter the correspondence uses to bound the live
-- stack window — is moved ONLY by `instr-alloc-stack` / `-dealloc-stack` /
-- `-push-frame`, and `ir-to-trace` emits NONE of them: the frame reservation is the
-- `subq $budget*8, %rsp` bracket the per-arch emitter wraps around the trace. So
-- with `frame-slots ≡ 0` at entry it is 0 for the WHOLE run, the correspondence's
-- `stack-eq` says nothing about any slot, and "the slot this instruction reads is
-- in frame" (`slot-read-in-frame`) is FALSE for every emitted program that touches
-- a slot — an assumption that cannot be discharged, only refuted.
--
-- Entering with the reservation already made is both faithful (the machine really
-- starts inside its frame) and what makes that residual DISCHARGEABLE: it becomes
-- `slot < ir-stack-budget ir`, which is the emitter's own static invariant.
entry-s : LocState FS
-- plan 0.105: a program starts with nothing in its log.
entry-s = mkLocState entry-regs (λ _ _ → nothing) (λ _ → nothing) false [] false

-- All four preconditions now hold BY CONSTRUCTION.
-- D155: the premise is `next-slot alloc ≤ n`, not an equation — the entry
-- instance is `n ≡ 0`, so this is `0 ≤ 0` and still holds by construction.
entry-ns : ∀ (slots : ℕ) → next-slot (entry-alloc slots) ≤ 0
entry-ns _ = z≤n

entry-bf : ∀ (slots : ℕ) → BeforeFrontier (entry-alloc slots) entry-loc
entry-bf _ = heap-before (s≤s z≤n)

entry-nh : halted entry-s ≡ false
entry-nh = refl

-- D180: …AT AN OBSERVATION DEPTH. The obligation is depth-indexed (one run per
-- depth, D058's shape), so the entry witness is too.
------------------------------------------------------------------------
-- D188: THE BLOCK TABLE, assumed here — the apex's one new axiom, and the
-- whole of what `obs-correct-apply` could not prove.
--
-- It says: a closure that is VALIDLY RESIDENT in a reachable state names a
-- label whose block implements its body, and running that block from the
-- post-call state returns with the body's value and the body's events.
--
-- Two halves, and only the second is a real assumption:
--
--   * "every block of `ir-to-unit ir` IS `emitted 0 l body` for the body its
--     label was minted for" is TRUE BY CONSTRUCTION of the emitter — the
--     `curry` clause puts `(ℓ o this-label , _ , body-trace)` in `all-bodies`
--     — and is provable by induction over `ir-to-trace'`;
--   * that the closure a RUNTIME state holds was built by one of those
--     `curry`s is a REACHABILITY invariant. It is true (the entry heap is
--     empty, so every resident closure was built by an earlier `curry` in the
--     same run), and proving it needs an induction over runs that nothing
--     here has. That is the honest content of this axiom.
--
-- Class **deferred proof**. It replaces `obs-correct-apply`, which was an
-- axiom for the WHOLE clause: the seventeen-instruction setup, its memory
-- preservation, the call's label resolution and all three input residences
-- are now PROVED (D183/D185/D188), and only the callee's own run is assumed.
------------------------------------------------------------------------
-- D199 widens this to BOTH block kinds. The ν's coalgebra block is reached
-- exactly as a closure body is — through a code cell of a resident two-cell
-- object — and carries exactly the same two halves: its content is true by
-- construction of the emitter (`Ana`'s clause puts the block in `all-bodies`,
-- and since D199 that block is the coalgebra FOLLOWED BY the re-suspension of
-- every recursive position, which is what makes it compute `evalᴰ (Out wf)`
-- rather than the coalgebra alone), and that a resident suspension was built
-- by an earlier `Ana` in the same run is the same reachability invariant.
--
-- Widening it is not a new assumption so much as an honest one: while the
-- premise mentioned only closures, `obs-correct-Out` was a postulate covering
-- the ν side, and that postulate was FALSE (D199).
-- plan 0.91 parallel track (2026-09-17) — `block-runs` IS NO LONGER CLAIMED.
--
-- It stood here as
--
--     postulate block-runs : (ir : IR Unit Unit) → BlockRuns (ir-to-trace ir)
--
-- and it is FALSE (D213, machine-checked: `Once/Probe/ApexInconsistent.boom : ⊥`).
-- Everything above it was therefore derived from an inconsistent assumption —
-- the apex theorem was not weak, it was VACUOUS.
--
-- Three things had to be separated to see what to do, and D217 is what forced
-- the separation:
--
--   * `BlockRuns prog` AS A PREMISE of `IRObsCorrectF` is LEGITIMATE, and D188
--     was right to put it there. It is what excludes a fabricated closure —
--     and `IRObsCorrectF apply` is itself false without it, since a state whose
--     closure names an undefined label HALTS the machine on the call while the
--     denotation says `f a`.
--   * The apex DISCHARGE — the claim that the premise always holds — is the
--     false statement.
--   * What the discharge needs is BEHAVIOURAL (that entering the block runs the
--     body), and D217 showed no fact about a state can supply it: one cell, two
--     denotations. That is what plan 0.93 rebuilds, as a relation recursive on
--     the TYPE rather than a `data` indexed by it.
--
-- Until 0.93 lands, the honest thing is to ASSUME it visibly rather than claim
-- it falsely. It is now a HYPOTHESIS of this module, threaded to
-- `Once.Certified`, so the top-level theorem reads
--
--     "IF the emitter's block table is coherent, THEN the compiled code is
--      correct"
--
-- which is WEAKER than what stood here, and TRUE, where what stood here was
-- stronger and vacuous. Discharging it is plan 0.93's whole purpose; the
-- hypothesis is what makes the debt visible in the statement instead of hidden
-- in a postulate block.

-- …and `entry-blocks` is now a DEFINITION: the proved composition, transported
-- across `link`'s own associativity
-- (`entry ++ c-ret ∷ layout` vs `(entry ++ c-ret ∷ []) ++ layout`).
-- The image is the START, then `main`'s unit linked with the program's leave
-- (D320), then the table. `main`'s code sits at pc 1, and its blocks follow
-- the leave; `top-noThunks` is the label-distinctness fact for exactly that
-- prefix.
top-pre : (ir : IR Unit Unit) → AbstractTrace
top-pre ir = instr-ctrl (c-start (ir-stack-budget ir)) ∷ emitted 0 0 ir
             ++ instr-ctrl c-leave ∷ []

main-blocks : (ir : IR Unit Unit)
            → BlocksAt (top-pre ir ++ blocks-layout (blocks 0 0 ir)) (blocks 0 0 ir)
main-blocks ir =
  blocks-at (top-pre ir) (blocks 0 0 ir)
            (missBefore-from (top-pre ir) (blocks 0 0 ir)
                             (Unique.top-noThunks {FS} ir (ir-stack-budget ir)))

------------------------------------------------------------------------
-- D244/D245: THE PROGRAM IMAGE. `main`'s unit is its PREFIX and the table's
-- function entries follow (`ProgramImage`), so every fact about `main`'s own
-- code carries over by the prefix laws: a fetch, a jump-label scan and an
-- entry scan that resolve inside the prefix resolve identically in the image.
------------------------------------------------------------------------

image : IR Unit Unit → AbstractTrace
image ir = program-image o (irProgram tbl ir)

-- The image's block table: the premise the apex carries (D188), now naming the
-- table's functions as well as the closure bodies and coalgebras.
BlockRunsT : Set
BlockRunsT = (ir : IR Unit Unit) → BlockRuns (image ir)

span-prefix : ∀ (t₁ t₂ : AbstractTrace) (j : ℕ) (t : AbstractTrace)
            → SpanAt t₁ j t → SpanAt (t₁ ++ t₂) j t
span-prefix t₁ t₂ j t sp k i eq = fetch-++-left t₁ t₂ (k + j) i (sp k i eq)

blocks-prefix : ∀ (t₁ t₂ : AbstractTrace) (bs : List (LabelId × ℕ × AbstractTrace))
              → BlocksAt t₁ bs → BlocksAt (t₁ ++ t₂) bs
blocks-prefix t₁ t₂ []                    []                        = []
blocks-prefix t₁ t₂ ((lbl , b , t) ∷ bs) ((j , feq , sp) ∷ rest) =
  (j , ft-go-prefix t₁ t₂ (e-thunk lbl) 0 j feq , span-prefix t₁ t₂ j (block-layout (lbl , b , t)) sp)
  ∷ blocks-prefix t₁ t₂ bs rest

-- …so `main`'s code is found ONE PAST the start.
private
  rest : IR Unit Unit → AbstractTrace
  rest ir = instr-ctrl c-leave ∷ blocks-layout (blocks 0 0 ir)

  -- the image, re-associated so the blocks are a suffix of `top-pre`
  image-assoc : (ir : IR Unit Unit)
              → image ir ≡ (top-pre ir ++ blocks-layout (blocks 0 0 ir)) ++ fns-image (suc (ir-next-label 0 ir)) tbl
  image-assoc ir =
    cong (instr-ctrl (c-start (ir-stack-budget ir)) ∷_)
      (trans (cong (_++ fns-image (suc (ir-next-label 0 ir)) tbl)
                   (sym (++-assoc (emitted 0 0 ir)
                                  (instr-ctrl c-leave ∷ [])
                                  (blocks-layout (blocks 0 0 ir)))))
             refl)

entry-span : (ir : IR Unit Unit) → SpanAt (image ir) 1 (emitted 0 0 ir)
entry-span ir k i eq =
  subst (λ m → fetch (image ir) m ≡ just i) (+-comm 1 k)
        (fetch-++-left (emitted 0 0 ir ++ rest ir) (fns-image (suc (ir-next-label 0 ir)) tbl) k i
          (fetch-++-left (emitted 0 0 ir) (rest ir) k i eq))

entry-labels : (ir : IR Unit Unit) → LabelsAt (image ir) 1 (emitted 0 0 ir)
entry-labels ir m j eq =
  trans (fl-go-shift ((emitted 0 0 ir ++ rest ir) ++ fns-image (suc (ir-next-label 0 ir)) tbl) m 1 0)
        (cong (Data.Maybe.map (_+ 1))
              (fl-go-prefix (emitted 0 0 ir ++ rest ir) _ m 0 j
                            (fl-go-prefix (emitted 0 0 ir) (rest ir) m 0 j eq)))

entry-blocks : (ir : IR Unit Unit) → BlocksAt (image ir) (blocks 0 0 ir)
entry-blocks ir =
  subst (λ prog → BlocksAt prog (blocks 0 0 ir)) (sym (image-assoc ir))
        (blocks-prefix (top-pre ir ++ blocks-layout (blocks 0 0 ir))
                       (fns-image (suc (ir-next-label 0 ir)) tbl) (blocks 0 0 ir) (main-blocks ir))

-- Every function entry is slot-stable: its marker moves only the frame, and
-- its unit is the emitter's, stable under its OWN owner.
fns-slot-stable : ∀ (l : ℕ) (es : List IRFun) → AllSlotStable (fns-image l es)
fns-slot-stable l []       = []
fns-slot-stable l (e ∷ es) =
  ++⁺ (tt ∷ CIS.CataIRSlotStable.ir-to-trace-lab-slot-stable (fname e) {FS} (fbody e) l)
      (fns-slot-stable (fn-next l e) es)

image-slot-stable : (ir : IR Unit Unit) → AllSlotStable (image ir)
image-slot-stable ir =
  tt ∷ ++⁺ (CIS.CataIRSlotStable.ir-to-trace-top-slot-stable o {FS} ir)
           (fns-slot-stable (suc (ir-next-label 0 ir)) tbl)

-- Plan 0.107: THE RUN STARTS OUTSIDE EVERY FRAME (`entry-alloc 0`, pc 0) —
-- what a kernel's `exec` or a bare-metal reset hands over. The start (pc 0)
-- reserves `main`'s frame, and `main`'s unit runs from pc 1.
start-flat : FlatState
start-flat = mkFlat entry-s (entry-alloc 0) 0

main-flat : IR Unit Unit → FlatState
main-flat ir = flat-exec-instr (instr-ctrl (c-start (ir-stack-budget ir))) (image ir) start-flat

entry-witness : (ir : IR Unit Unit) → IRObsCorrectF ir
              → (brs : BlockRunsT) → (k : ℕ)
              → MachineRefinesObsF (image ir) 1 0 0 ir tt (floc (main-flat ir))
                  (falloc (main-flat ir)) (SV-Tag 0) [] k
entry-witness ir ioc brs k =
  ioc 0 0 (image ir) 1 (image-slot-stable ir)
      (brs ir) (entry-span ir) (entry-blocks ir) (entry-labels ir)
      Stack tt (floc (main-flat ir)) (falloc (main-flat ir)) (SV-Tag 0)
      refl refl
      -- D153: `main : IR Unit Unit`, so its input has no residence at all.
      (in-unit refl) k []

------------------------------------------------------------------------
-- The entry witness. D244: the machine runs the PROGRAM IMAGE, and the meaning
-- is the program's (`main` in its table's environment).
------------------------------------------------------------------------

IOC : Set
-- plan 0.105: the signatures the world `FS` runs in declares.
σFS : ISig
σFS = TM.Interp.sig (Once.CCC.FrameSemantics.FrameSemantics.fs-interp FS)

IOC = ∀ {A B} (ir : IR A B) → Linked σFS tbl ir → IRObsCorrectF ir

entry-vr : (ir : IR Unit Unit) → LinkedProgram σFS (irProgram tbl ir) → IOC → (brs : BlockRunsT) → (k : ℕ)
         → ValueRealized (image ir) 1 0 0 ir tt (floc (main-flat ir))
             (falloc (main-flat ir)) (SV-Tag 0) [] k
entry-vr ir lk ioc brs k = MachineRefinesObsF.value-realized (entry-witness ir (ioc ir (proj₁ lk)) brs k)

------------------------------------------------------------------------
-- D320: HOW THE PROGRAM'S FLAT RUN ENDS. The start, `main`'s run (the entry
-- witness's chain), and then: if `main` returned, the image's `c-leave` — the
-- run ends `returned`; if it stopped, the halted machine, which has not left
-- (`ValueRealized.stops`) — `halted`. Either way, the meaning's calls and how
-- it ended, at a fuel the witness names.
------------------------------------------------------------------------

private
  -- the image's `c-leave` sits right after `main`'s code
  leave-at : (ir : IR Unit Unit) → fetch (image ir) (length (emitted 0 0 ir) + 1) ≡ just (instr-ctrl c-leave)
  leave-at ir =
    subst (λ m → fetch (image ir) m ≡ just (instr-ctrl c-leave)) (+-comm 1 (length (emitted 0 0 ir)))
      (subst (λ prog → fetch prog (suc (length (emitted 0 0 ir))) ≡ just (instr-ctrl c-leave)) (sym (image-assoc ir))
        (fetch-++-left (top-pre ir ++ blocks-layout (blocks 0 0 ir)) (fns-image (suc (ir-next-label 0 ir)) tbl)
                       (suc (length (emitted 0 0 ir))) (instr-ctrl c-leave)
          (fetch-++-left (top-pre ir) (blocks-layout (blocks 0 0 ir)) (suc (length (emitted 0 0 ir))) (instr-ctrl c-leave)
            (trans (cong (fetch (emitted 0 0 ir ++ instr-ctrl c-leave ∷ [])) (sym (+-identityʳ (length (emitted 0 0 ir)))))
                   (fetch-++-right (emitted 0 0 ir) (instr-ctrl c-leave ∷ []) 0)))))

-- plan 0.119 D5: …at a ROUND BUDGET. `main`'s budgeted run returned (the
-- image's `c-leave`: `returned`), stopped (`halted`), or was CUT — the machine
-- is still running, its fuel used up at the cut.
tail-fuel : ∀ {X : Set} → Res (Ap X) → ℕ
tail-fuel (returns (done _ _)) = 2
tail-fuel stopped              = 2
tail-fuel (returns cut)        = 0

flat-ends : (ioc : IOC) (brs : BlockRunsT) (ir : IR Unit Unit) (lk : LinkedProgram σFS (irProgram tbl ir)) (k : ℕ)
          → flat-events (suc (ValueRealized.steps (entry-vr ir lk ioc brs k)
                              + tail-fuel (resultAt (floc (main-flat ir)) (⟪ evalᴰ ir tt ⟫ k))))
                        (image ir) start-flat
            ≡ (eventsAt (floc (main-flat ir)) (⟪ evalᴰ ir tt ⟫ k) , endAp (resultAt (floc (main-flat ir)) (⟪ evalᴰ ir tt ⟫ k)))
flat-ends ioc brs ir lk k =
  trans (flat-events-steps (ValueRealized.run vr) (tail-fuel (resultAt s0 T)))
        (trans (cong₂ _▹_ (MachineRefinesObsF.traces-agree (entry-witness ir (ioc ir (proj₁ lk)) brs k))
                          (tail (resultAt s0 T) refl))
               (cong (_, endAp (resultAt s0 T)) (++-identityʳ (eventsAt s0 T))))
  where
    vr = entry-vr ir lk ioc brs k
    s0 = floc (main-flat ir)
    T  = ⟪ evalᴰ ir tt ⟫ k
    st = ValueRealized.settle vr
    tail : ∀ (ρ : Res _) → resultAt s0 T ≡ ρ → flat-events (tail-fuel ρ) (image ir) st ≡ ([] , endAp ρ)
    tail (returns (done v r)) eq = fin (ValueRealized.live vr (cong is-stopped eq)) (ValueRealized.at-end vr eq)
      where fin : halted (floc st) ≡ false → fpc st ≡ length (emitted 0 0 ir) + 1
                → flat-events 2 (image ir) st ≡ ([] , just (returned tt))
            fin h p rewrite h | p | leave-at ir = refl
    tail stopped eq = fin (ValueRealized.stops vr (cong is-stopped eq))
      where fin : halted (floc st) ≡ true × LocState.left (floc st) ≡ LocState.left s0
                → flat-events 2 (image ir) st ≡ ([] , just halted-end)
            fin (h , l) rewrite h | l = refl
    tail (returns cut) eq = refl

-- A cut run has taken a control step for every silent step it passed.
flat-progress : (ioc : IOC) (brs : BlockRunsT) (ir : IR Unit Unit) (lk : LinkedProgram σFS (irProgram tbl ir)) (k : ℕ)
              → resultAt (floc (main-flat ir)) (⟪ evalᴰ ir tt ⟫ k) ≡ returns cut
              → k ≤ chain-ctrls (ValueRealized.run (entry-vr ir lk ioc brs k))
flat-progress ioc brs ir lk k eq =
  subst (λ ρ → k ≤ budgetLeft k ρ + chain-ctrls (ValueRealized.run (entry-vr ir lk ioc brs k))) eq
        (ValueRealized.progress (entry-vr ir lk ioc brs k))

-- The flat fuel the budget-`k` observation is read at, and — when the budget
-- cut the run — the control steps that fuel covers (at least the budget).
flat-fuel : (ioc : IOC) (brs : BlockRunsT) (ir : IR Unit Unit) (lk : LinkedProgram σFS (irProgram tbl ir)) (k : ℕ) → ℕ
flat-fuel ioc brs ir lk k =
  ValueRealized.steps (entry-vr ir lk ioc brs k) + tail-fuel (resultAt (floc (main-flat ir)) (⟪ evalᴰ ir tt ⟫ k))

flat-cut : (ioc : IOC) (brs : BlockRunsT) (ir : IR Unit Unit) (lk : LinkedProgram σFS (irProgram tbl ir)) (k : ℕ)
         → endAp (resultAt (floc (main-flat ir)) (⟪ evalᴰ ir tt ⟫ k)) ≡ nothing
         → k ≤ flat-ctrls (suc (flat-fuel ioc brs ir lk k)) (image ir) start-flat
flat-cut ioc brs ir lk k e = go (resultAt (floc (main-flat ir)) (⟪ evalᴰ ir tt ⟫ k)) refl e
  where
    vr = entry-vr ir lk ioc brs k
    go : ∀ (ρ : Res _) → resultAt (floc (main-flat ir)) (⟪ evalᴰ ir tt ⟫ k) ≡ ρ → endAp ρ ≡ nothing
       → k ≤ flat-ctrls (suc (flat-fuel ioc brs ir lk k)) (image ir) start-flat
    go (returns (done _ _)) _ ()
    go stopped              _ ()
    go (returns cut) eq _ =
      ≤-trans (flat-progress ioc brs ir lk k eq)
        (≤-trans (m≤m+n _ (flat-ctrls (tail-fuel (resultAt (floc (main-flat ir)) (⟪ evalᴰ ir tt ⟫ k))) (image ir) (ValueRealized.settle vr)))
          (≤-trans (≤-reflexive (sym (flat-ctrls-steps (ValueRealized.run vr)
                                        (tail-fuel (resultAt (floc (main-flat ir)) (⟪ evalᴰ ir tt ⟫ k))))))
                   (n≤1+n _)))
