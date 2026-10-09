-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.ArchCorrectness.FlatFromObs  (Plan 0.53-step2 / Phase B L1;
-- Plan 0.54 rung A step-7 rewire 2026-07-20)
--
-- Shared, arch-parametric construction of the per-arch `ArchCorrect` record.
--
-- STEP-7 REWIRE (the first break in the decomposition from the COMPILER apex
-- `Once.Compiler.correct` = `VC.correctᵈ`): previously this module POSTULATED
-- `ir-flat-correct`, left `flat-trace` an abstract parameter, and DISCARDED the
-- `ir-obs-correct` it was handed (`flat-from-obs _ = …`) — so the whole
-- IR-observable theorem (and everything under it: the composition case, the
-- arith value work) was an island. Now:
--
--   * `flat-trace`       — DEFINED: `take n (flat-events (EF n) (ir-to-trace ir)
--                          entry)`, where the adequate fuel `EF n` is exactly the
--                          `∃[ f ]` witness `traces-agree` supplies at depth `n`
--                          (fuel counts machine STEPS, `n` counts EVENTS — which
--                          is why a naive `flat-events n` would be wrong).
--   * `ir-flat-correct`  — PROVED from `ir-obs-correct`'s `traces-agree`
--                          (`proj₂` of that same witness). NO LONGER A POSTULATE.
--   * `asm-trace-correct`— NAMED postulate (printer / loader faithfulness; the
--                          concrete-machine half = Plan 0.54 rung B).
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
open import Once.CanonicalName using (CanonicalName)

open import Data.List using (List)
open import Once.Denotation.Program using (IRFun; irProgram; Linked; LinkedProgram)
open Once.Denotation.Program.IRFun using (fbody; fname)
open import Once.Spec.Contract using (ISig)
import Once.Denotation.TraceMonad as TM
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
open import Once.Denotation.Behavior using (Behavior; behavior-by)
open Once.Denotation.Behavior.Behavior using (at)
open import Once.Denotation.Trace using (SigOpEvent)
open import Once.Adequacy.SourceTrace using (⟦_⟧IR)
open import Once.CCC.Codegen.ProgramImage using (program-image; fns-image; fn-next; top-done)
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
open import Once.CCC.Machine.SMCore using (instr-ctrl; c-ret; c-start; c-label; c-jmp; blocks-layout; block-layout; AbstractTrace; e-thunk; AllocState; mkAllocState; next-slot)
open import Data.List.Properties using (++-assoc)
open import Data.List.Properties using (++-identityʳ)
-- D158: the entry instance supplies the PLACEMENT — the whole program is the
-- fragment, at offset 0.
open import Data.Nat.Properties using (+-identityʳ; +-comm)
open import Once.CCC.Machine.SMCore
  using (LocState; mkLocState; Registers; mkRegs; SV-Tag;
         halted)
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

open IRObsCorrectFlatness {FS} using (IRObsCorrectF; BlockRuns; MachineRefinesObsF; ValueRealized; in-unit; SpanAt; LabelsAt; emitted; BlocksAt; blocks)
open FlatMachine {FS} using (mkFlat; fetch; fetch-++-left; find-label; ft-go-prefix; FlatState; flat-exec-instr; floc; falloc)
open import Once.CCC.Codegen.FlatStepLemmas using (module FlatStepsAPI)
open FlatStepsAPI {FS} using (fl-go-prefix; fl-go-shift)
open import Once.CCC.Codegen.CataNextSlot using (module CataNextSlot)
open CataNextSlot {FS} using (AllSlotStable)
open FlatEventTrace {FS} using (flat-events; chain-events; flat-events-steps)
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
entry-s = mkLocState entry-regs (λ _ _ → nothing) (λ _ → nothing) false []

-- All four preconditions now hold BY CONSTRUCTION.
-- D155: the premise is `next-slot alloc ≤ n`, not an equation — the entry
-- instance is `n ≡ 0`, so this is `0 ≤ 0` and still holds by construction.
entry-ns : ∀ (slots : ℕ) → next-slot (entry-alloc slots) ≤ 0
entry-ns _ = z≤n

entry-bf : ∀ (slots : ℕ) → BeforeFrontier (entry-alloc slots) entry-loc
entry-bf _ = heap-before (s≤s z≤n)

entry-nh : halted entry-s ≡ false
entry-nh = refl

-- `main`'s machine-refinement witness at the entry state. The `Unit` input's
-- validity is `valid-unit-wf`, and its residence is `in-unit` (D074: a unit
-- input needs none — the tag filler in `Input1` is never read).
-- D152: the ENTRY INSTANCE of the obligation is `n = l = 0`. That is the only
-- instance this consumer ever needs -- which is exactly why the obligation
-- could be (wrongly) stated at frontier 0 and still satisfy its consumer,
-- while being unusable for the induction underneath it.
-- D155: the entry closure register is the tag filler, and
-- `entry-flat s alloc (SV-Tag 0)` IS `mkFlat s alloc 0` — so every consumer
-- below (which names the entry state as `mkFlat …`) is untouched by the
-- interface gaining that component.
-- D159: `main` is no longer THE program — it is the ENTRY BLOCK of it. The
-- linked program is `emitted 0 0 ir ++ c-ret budget ∷ blocks-layout bodies`,
-- so `main`'s own code is a genuine PREFIX and the placement premise carries
-- real content at last. Under D158 this was the identity span (`k + 0 ≡ k`)
-- and said nothing; now it is `fetch-++-left`, i.e. "the entry block sits at
-- offset 0 of the linked image".
main-span : (ir : IR Unit Unit) → SpanAt (ir-to-trace ir) 0 (emitted 0 0 ir)
main-span ir k i eq =
  subst (λ m → fetch (ir-to-trace ir) m ≡ just i) (sym (+-identityʳ k))
        (fetch-++-left (emitted 0 0 ir) _ k i eq)

-- plan 0.88: …and its LABEL half, which at the entry is the easy end of
-- `LabelsAt`: the entry trace is a PREFIX of the linked image, so a scan that
-- resolves inside it never reaches the `c-ret` or the block layouts.
main-labels : (ir : IR Unit Unit) → LabelsAt (ir-to-trace ir) 0 (emitted 0 0 ir)
main-labels ir m j eq =
  subst (λ z → find-label (ir-to-trace ir) m ≡ just z) (sym (+-identityʳ j))
        (fl-go-prefix (emitted 0 0 ir) _ m 0 j eq)

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

-- plan 0.91 S2 — THE APEX'S SHARE OF THE NEW PREMISE, and S5's obligation.
--
-- `IRObsCorrectF` now asks each fragment's caller to show the program
-- implements the blocks that fragment emits. Composites split that premise
-- (`comp-blocks-f`/`-g`, `blocks-f`/`blocks-g` in `PairAssemble`) and leaves
-- ignore it, so it arrives here, at the whole program, unsplit.
--
-- UNLIKE `block-runs` THIS IS ABOUT THE PROGRAM, NOT ABOUT A STATE — which is
-- the whole point of S2. `ir-to-trace ir` is
--
--     emitted 0 0 ir ++ c-ret ∷ blocks-layout (blocks 0 0 ir)
--
-- so every block in `blocks 0 0 ir` is laid out, contiguously, at a position
-- `blocks-layout` determines: `length (emitted 0 0 ir) + 1` plus the lengths
-- of the earlier blocks. Nothing is quantified over fabricable memory, so
-- D213's refutation has no purchase here — the ⊥-probe that kills
-- `block-runs` cannot be written against this.
--
-- S5 discharges it. The induction is `SlotBudget.blocks-below`'s shape (a
-- structural walk over `IR` returning `All … (bodies-of (ir-to-trace' n l ir))`)
-- plus D168's `link`-relocation lemmas, which is the first REAL demand for
-- that machinery — the plan said to check rather than assume, and this is the
-- check coming back positive.
-- plan 0.91 S5 / plan 0.93 S4 — NO LONGER ONE OPAQUE POSTULATE.
--
-- `Once.CCC.Codegen.BlockLayout` proves the whole of this except ONE fact.
-- `blocks-at` gives `BlockAt` for every block at once — each resolves to its
-- own offset (`block-resolves`, from `ft-go-++-miss` + `≡ᵇᴵ-refl`) and spans
-- there (`blocks-placed`, induction on the block list). What it needs is
-- `MissBefore`: each block's own prefix does not already resolve its label.
--
-- That is the label-distinctness fact, and it spans TWO channels. `curry`,
-- `Ana` and `in-ν` put their bodies in the BLOCKS list, but `cata-body`
-- (IRToTrace.agda:262-267) splices a `c-thunk` INLINE into the emitted trace
-- for all four cata strategies. So a prefix genuinely contains `c-thunk`
-- markers and the obligation is that none carries THIS label — not the
-- stronger, and false, "the entry mints no thunks".
--
-- `EmittedWF.labels-unique : AllPairs _≢_ (labels-def at)` states exactly this
-- (`labels-def-i` already tags `thunk m` apart from `once m`), but nothing
-- constructs it for the real program. Doing so is the remaining induction over
-- `ir-to-trace'`, tracking the label counter — `LabelScope`'s `label-mono`
-- territory.
--
-- D168's `link-pre`/`link-post`/`link-block-split` were NOT needed. The comment
-- that stood here predicted this would be "the first REAL demand for that
-- machinery"; `blocks-placed` goes through by direct induction on the block
-- list, so the prediction was wrong and the machinery stays unexercised here.
-- Stated with `NoThunks`, not `MissBefore`: the scan is gone. What is owed is
-- purely SYNTACTIC — no instruction in a block's prefix is a `c-thunk` carrying
-- that block's label. `missBefore-from` turns it into the scan fact.
-- plan 0.88: IT IS NO LONGER A POSTULATE. `LabelsUnique.defs-uniq` constructs
-- `EmittedWF.labels-unique` for the real program — the induction over
-- `ir-to-trace'` this comment predicted — and `entry-noThunks` is its
-- consumer's form, with the `c-ret` (which mints nothing) absorbed.
entry-no-thunks : (ir : IR Unit Unit)
                → NoThunks (emitted 0 0 ir ++ instr-ctrl (c-ret (ir-stack-budget ir)) ∷ [])
                           (blocks 0 0 ir)
entry-no-thunks ir = Unique.entry-noThunks {FS} ir (ir-stack-budget ir)

-- …and `entry-blocks` is now a DEFINITION: the proved composition, transported
-- across `link`'s own associativity
-- (`entry ++ c-ret ∷ layout` vs `(entry ++ c-ret ∷ []) ++ layout`).
-- Plan 0.107: the image is the START, then `main`'s unit linked with the
-- silent stop, then the table. `main`'s code sits at pc 1, and its blocks
-- follow the stop pair; `top-noThunks` is the label-distinctness fact for
-- exactly that prefix.
top-pre : (ir : IR Unit Unit) → AbstractTrace
top-pre ir = instr-ctrl (c-start (ir-stack-budget ir)) ∷ emitted 0 0 ir
             ++ instr-ctrl (c-label (top-done o (irProgram tbl ir)))
             ∷ instr-ctrl (c-jmp (top-done o (irProgram tbl ir))) ∷ []

main-blocks : (ir : IR Unit Unit)
            → BlocksAt (top-pre ir ++ blocks-layout (blocks 0 0 ir)) (blocks 0 0 ir)
main-blocks ir =
  blocks-at (top-pre ir) (blocks 0 0 ir)
            (missBefore-from (top-pre ir) (blocks 0 0 ir)
                             (Unique.top-noThunks {FS} ir (ir-stack-budget ir) (top-done o (irProgram tbl ir))))

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
  rest ir = instr-ctrl (c-label (top-done o (irProgram tbl ir)))
            ∷ instr-ctrl (c-jmp (top-done o (irProgram tbl ir)))
            ∷ blocks-layout (blocks 0 0 ir)

  -- the image, re-associated so the blocks are a suffix of `top-pre`
  image-assoc : (ir : IR Unit Unit)
              → image ir ≡ (top-pre ir ++ blocks-layout (blocks 0 0 ir)) ++ fns-image (suc (ir-next-label 0 ir)) tbl
  image-assoc ir =
    cong (instr-ctrl (c-start (ir-stack-budget ir)) ∷_)
      (trans (cong (_++ fns-image (suc (ir-next-label 0 ir)) tbl)
                   (sym (++-assoc (emitted 0 0 ir)
                                  (instr-ctrl (c-label (top-done o (irProgram tbl ir)))
                                   ∷ instr-ctrl (c-jmp (top-done o (irProgram tbl ir))) ∷ [])
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
  tt ∷ ++⁺ (CIS.CataIRSlotStable.ir-to-trace-top-slot-stable o {FS} ir (top-done o (irProgram tbl ir)))
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
                  (falloc (main-flat ir)) (SV-Tag 0) k
entry-witness ir ioc brs k =
  ioc 0 0 (image ir) 1 (image-slot-stable ir)
      (brs ir) (entry-span ir) (entry-blocks ir) (entry-labels ir)
      Stack tt (floc (main-flat ir)) (falloc (main-flat ir)) (SV-Tag 0)
      z≤n refl
      -- D153: `main : IR Unit Unit`, so its input has no residence at all.
      (in-unit refl) k

------------------------------------------------------------------------
-- `flat-main` — DEFINED. D159: the adequate fuel is the witness's OWN STEP
-- COUNT. D244: the machine runs the PROGRAM IMAGE, and the meaning is the
-- program's (`main` in its table's environment).
------------------------------------------------------------------------

IOC : Set
-- plan 0.105: the signatures the world `FS` runs in declares.
σFS : ISig
σFS = TM.Interp.sig (Once.CCC.FrameSemantics.FrameSemantics.fs-interp FS)

IOC = ∀ {A B} (ir : IR A B) → Linked σFS tbl ir → IRObsCorrectF ir

entry-vr : (ir : IR Unit Unit) → LinkedProgram σFS (irProgram tbl ir) → IOC → (brs : BlockRunsT) → (k : ℕ)
         → ValueRealized (image ir) 1 0 0 ir tt (floc (main-flat ir))
             (falloc (main-flat ir)) (SV-Tag 0) k
entry-vr ir lk ioc brs k = MachineRefinesObsF.value-realized (entry-witness ir (ioc ir (proj₁ lk)) brs k)

flat-trace-fam : IOC → BlockRunsT → (ir : IR Unit Unit) → LinkedProgram σFS (irProgram tbl ir) → ℕ → List SigOpEvent
flat-trace-fam ioc brs ir lk n =
  take n (flat-events (suc (ValueRealized.steps (entry-vr ir lk ioc brs n) + 0))
                      (image ir) start-flat)

-- D113/D115: at THIS target's NUMERICS, which is where `IRObsCorrectFlat`'s
-- `evalᴰ` alias reads them from too, so the two sides mean one thing.
ir-flat-correct-fam : (ioc : IOC) (brs : BlockRunsT) (ir : IR Unit Unit) (lk : LinkedProgram σFS (irProgram tbl ir)) (n : ℕ)
                    → flat-trace-fam ioc brs ir lk n
                      ≡ at (⟦ just (irProgram tbl ir) ⟧IR (Once.CCC.FrameSemantics.fs-numerics FS)
                              (Once.CCC.FrameSemantics.FrameSemantics.fs-interp FS)) n
-- Plan 0.105: the witness's events are EXACTLY the program's run from the
-- empty log (`entry-s`), so the depth-`n` observable is one `take n`.
ir-flat-correct-fam ioc brs ir lk n =
  cong (take n)
    (trans (trans (flat-events-steps (ValueRealized.run (entry-vr ir lk ioc brs n)) 0)
                  (++-identityʳ (chain-events (ValueRealized.run (entry-vr ir lk ioc brs n)))))
           (MachineRefinesObsF.traces-agree (entry-witness ir (ioc ir (proj₁ lk)) brs n)))

-- …and THAT is what makes the machine's family a `Behavior`: it borrows the
-- three laws from the denotation it is proved equal to (`behavior-by`).
flat-main : IOC → BlockRunsT → (ir : IR Unit Unit) → LinkedProgram σFS (irProgram tbl ir) → Behavior
flat-main ioc brs ir lk =
  behavior-by (⟦ just (irProgram tbl ir) ⟧IR (Once.CCC.FrameSemantics.fs-numerics FS) (Once.CCC.FrameSemantics.FrameSemantics.fs-interp FS))
              (flat-trace-fam ioc brs ir lk)
              (λ n → sym (ir-flat-correct-fam ioc brs ir lk n))

ir-flat-correct-main : (ioc : IOC) (brs : BlockRunsT) (ir : IR Unit Unit) (lk : LinkedProgram σFS (irProgram tbl ir)) (n : ℕ)
                     → at (flat-main ioc brs ir lk) n
                       ≡ at (⟦ just (irProgram tbl ir) ⟧IR (arch-numerics arch) (Once.CCC.FrameSemantics.FrameSemantics.fs-interp FS)) n
ir-flat-correct-main ioc brs ir lk n =
  subst (λ F → at (flat-main ioc brs ir lk) n ≡ at (⟦ just (irProgram tbl ir) ⟧IR F (Once.CCC.FrameSemantics.FrameSemantics.fs-interp FS)) n)
        fmt-agree (ir-flat-correct-fam ioc brs ir lk n)
