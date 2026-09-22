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
--   * `asm-sem`          — DEFINED  (`exec-bytes ∘ assemble`)
--   * `assemble-correct` — PROVED   (`refl`, by the `asm-sem` definition)
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

open import Data.Nat using (ℕ; _<_)
open import Once.Adequacy.CPU.Interface using (Arch; ArchSemantics)
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.Target.Arch using (arch-numerics)
open import Relation.Binary.PropositionalEquality using (_≡_; subst)

-- Plan 0.63 (D089): parameterised by the DEFINITION'S identity, which keys its
-- labels. `o` is constant for a whole definition, so it belongs on the module
-- rather than on every lemma — which is what keeps the statements below
-- UNCHANGED: the emitter is imported APPLIED, so each call site reads as before.
open import Once.CanonicalName using (CanonicalName)

module Once.Adequacy.ArchCorrectness.FlatFromObs (o : CanonicalName)
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
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (proj₁; proj₂)
open import Data.String using (String)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

open import Once.IR using (IR; Unit; AllocMode; Stack)
open import Once.IR.Size using (ir-size)
open import Once.Denotation.Behavior using (Behavior; at; behavior-by)
open import Once.Denotation.Trace using (SigOpEvent)
open import Once.Adequacy.Compile using (ArchCorrect)
open import Once.Adequacy.SourceTrace using (moduleToIR; moduleToIR-emitted; map-rewrite; ⟦_⟧IR)
open import Once.CCC.Codegen.IRObsCorrectFlat o using (module IRObsCorrectFlatness)
open import Once.CCC.Codegen.IRToTrace o using (ir-to-trace; ir-stack-budget)
open import Once.CCC.Codegen.BlockLayout using (module Layout)
open import Once.CCC.Codegen.LabelsUnique o using (module Unique)
open Layout {FS} using (MissBefore; NoThunks; missBefore-from; blocks-at; Span)
open import Data.List using (_++_; []; _∷_)
open import Once.CCC.Machine.SMCore using (instr-ctrl; c-ret; blocks-layout)
open import Data.List.Properties using (++-assoc)
open import Data.List.Properties using (++-identityʳ; take-all)
open import Once.Denotation.TraceMonad using (projTrace; bnd)
open import Once.Denotation.DenotPrefix using (evalᴰ-good)
-- D158: the entry instance supplies the PLACEMENT — the whole program is the
-- fragment, at offset 0.
open import Once.CCC.Codegen.CataIRSlotStable o using (module CataIRSlotStable)
open import Data.Nat.Properties using (+-identityʳ)
open import Once.CCC.Machine.SMCore
  using (LocState; mkLocState; Registers; mkRegs; ValueLocation; AtDynamic; SV-Tag;
         halted)
open import Once.Memory.HeapAddress using (heap-loc; mkHeapRef)
open import Data.Nat using (z≤n; s≤s; _≤_; _+_)
open import Once.CCC.Machine.Allocation
  using (AllocState; mkAllocState; next-slot; module FrontierInvariant)
open import Once.CCC.Machine.Flat using (module FlatMachine)
open import Once.Adequacy.FlatEvents using (module FlatEventTrace)
open import Once.CCC.Machine.ClosureWellFormed o using (module ClosureWellFormedDef)
import Once.Compile as C
import Once.Parser.Module.Core as P
-- D100: the assembler's own precondition — the emitted local labels are
-- pairwise distinct. Consumed by `AsmTraceCorrect` below.
open import Once.Adequacy.LabelClash using (DistinctLabels; LabelsResolvable)
open import Once.Adequacy.SymbolClash using (SymbolsResolvable)

open IRObsCorrectFlatness {FS} using (IRObsCorrectF; CalleeRuns; BlockRuns; MachineRefinesObsF; ValueRealized; in-unit; SpanAt; LabelsAt; emitted; BlocksAt; blocks)
open FlatMachine {FS} using (mkFlat; fetch; fetch-++-left; find-label)
open import Once.CCC.Codegen.FlatStepLemmas using (module FlatStepsAPI)
open FlatStepsAPI {FS} using (fl-go-prefix)
open CataIRSlotStable {FS} using (ir-to-trace-slot-stable)
open FlatEventTrace {FS} using (flat-events; chain-events; flat-events-steps)
open FrontierInvariant {FS} using (BeforeFrontier; heap-before)
open ClosureWellFormedDef {FS} using (ValidAtWF; valid-unit-wf)

------------------------------------------------------------------------
-- The DEFINED field (+ its proof)
------------------------------------------------------------------------

asm-sem : String → Behavior
asm-sem asm = ArchSemantics.exec-bytes as (ArchSemantics.assemble as asm)

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
entry-s = mkLocState entry-regs (λ _ _ → nothing) (λ _ → nothing) false

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
entry-span : (ir : IR Unit Unit) → SpanAt (ir-to-trace ir) 0 (emitted 0 0 ir)
entry-span ir k i eq =
  subst (λ m → fetch (ir-to-trace ir) m ≡ just i) (sym (+-identityʳ k))
        (fetch-++-left (emitted 0 0 ir) _ k i eq)

-- plan 0.88: …and its LABEL half, which at the entry is the easy end of
-- `LabelsAt`: the entry trace is a PREFIX of the linked image, so a scan that
-- resolves inside it never reaches the `c-ret` or the block layouts.
entry-labels : (ir : IR Unit Unit) → LabelsAt (ir-to-trace ir) 0 (emitted 0 0 ir)
entry-labels ir m j eq =
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
entry-blocks : (ir : IR Unit Unit) → BlocksAt (ir-to-trace ir) (blocks 0 0 ir)
entry-blocks ir =
  subst (λ prog → BlocksAt prog (blocks 0 0 ir))
        (++-assoc (emitted 0 0 ir) (instr-ctrl (c-ret (ir-stack-budget ir)) ∷ [])
                  (blocks-layout (blocks 0 0 ir)))
        (blocks-at (emitted 0 0 ir ++ instr-ctrl (c-ret (ir-stack-budget ir)) ∷ [])
                   (blocks 0 0 ir)
                   (missBefore-from (emitted 0 0 ir ++ instr-ctrl (c-ret (ir-stack-budget ir)) ∷ [])
                                    (blocks 0 0 ir) (entry-no-thunks ir)))

entry-witness : (ir : IR Unit Unit) → IRObsCorrectF ir
              → (brs : (ir : IR Unit Unit) → BlockRuns (ir-to-trace ir)) → (k : ℕ)
              → MachineRefinesObsF (ir-to-trace ir) 0 0 0 ir tt entry-s
                  (entry-alloc (ir-stack-budget ir)) (SV-Tag 0) k
entry-witness ir ioc brs k =
  ioc 0 0 (ir-to-trace ir) 0 (ir-to-trace-slot-stable ir)
      (brs ir) (entry-span ir) (entry-blocks ir) (entry-labels ir)
      Stack tt entry-s (entry-alloc (ir-stack-budget ir)) (SV-Tag 0)
      (entry-ns (ir-stack-budget ir)) entry-nh
      -- D153: ONE residence premise. `main : IR Unit Unit`, so its input has
      -- no residence at all and `in-unit` discharges it outright — the
      -- `entry-loc` / `valid-unit-wf` / `entry-bf` triple that used to be
      -- threaded here was only ever satisfying a premise that should not have
      -- existed.
      (in-unit refl) k

------------------------------------------------------------------------
-- `flat-trace` — DEFINED. D159: the adequate fuel is the witness's OWN STEP
-- COUNT, not an existential per observation depth. `traces-agree` is now
-- bounded by `value-realized`'s chain (a fragment's events are the events along
-- its chain, not everything a fuel happens to reach), so the fuel that realises
-- it is exactly `steps` — and it no longer varies with `n`.
------------------------------------------------------------------------

entry-vr : (ir : IR Unit Unit) → (∀ {A B} (ir' : IR A B) → IRObsCorrectF ir')
         → (brs : (ir : IR Unit Unit) → BlockRuns (ir-to-trace ir)) → (k : ℕ)
         → ValueRealized (ir-to-trace ir) 0 0 0 ir tt entry-s
             (entry-alloc (ir-stack-budget ir)) (SV-Tag 0) k
entry-vr ir ioc brs k = MachineRefinesObsF.value-realized (entry-witness ir (ioc ir) brs k)

-- The machine's trace FAMILY. The fuel is the depth-`n` witness's own step
-- count — "for each depth there is a fuel that reaches it", D058's
-- productivity shape, now carried by the statement rather than an ∃.
flat-trace-fam : (∀ {A B} (ir : IR A B) → IRObsCorrectF ir)
               → (brs : (ir : IR Unit Unit) → BlockRuns (ir-to-trace ir))
               → Maybe (IR Unit Unit) → ℕ → List SigOpEvent
flat-trace-fam ioc brs nothing   _ = []
flat-trace-fam ioc brs (just ir) n =
  take n (flat-events (ValueRealized.steps (entry-vr ir ioc brs n) + 0)
                      (ir-to-trace ir) (mkFlat entry-s (entry-alloc (ir-stack-budget ir)) 0))

------------------------------------------------------------------------
-- The concrete↔abstract seam (Plan 0.54 rung B). At THIS module the machine
-- (`as : ArchSemantics`) is OPAQUE (injected), so `asm-trace-correct` cannot be
-- decomposed here — it would be an un-dischargeable internal postulate. Instead
-- it is a PARAMETER of `flat-from-obs`, supplied by the per-arch instance where
-- the concrete `X64.State`/`run-events` machine IS visible, so the arith slice
-- can consume `dispatch-arith-preserves` there (the rest = the explicit ISA /
-- printer / loader trust). Same move that un-postulated `ir-flat-correct`:
-- localise the obligation to where it can be discharged.
--
-- The `AsmTraceCorrect ft` type is the shape the per-arch instance must supply
-- (against the DEFINED `flat-trace-of ioc`).
------------------------------------------------------------------------

-- D100: the HONEST precondition on the toolchain. `as` refuses a file that
-- defines a label twice, so for such a program `asm-sem asm` is the trace of
-- nothing at all and this equation is FALSE — not merely unproved. Stating
-- `DistinctLabels` here (and NOT on `assemble-correct`, where the same class of
-- premise already went vacuous when `asm-sem` was defined) narrows every arch's
-- `loader-faithful` axiom to the programs the assembler actually accepts. The
-- apex supplies it, so `correct` gains no hypothesis — it gains an obligation.
AsmTraceCorrect : (Maybe (IR Unit Unit) → Behavior) → Set
AsmTraceCorrect ft =
  ∀ (m : P.Module) (asm : String) →
  C.compileFromModule C.Heap C.Build false arch m ≡ C.Built asm →
  DistinctLabels arch m →
  -- D167: …and the text LINKS — every compiler-minted SigOp it calls has its
  -- arith block emitted. `ld`'s rejection, which nothing stated before.
  -- D169: …and every jump/branch/code-address it names is defined in it.
  LabelsResolvable arch m →
  SymbolsResolvable arch m →
  -- D165: the EMITTED IR — `rewrite-ir`-lifted, which is what the text was
  -- generated from. Was `moduleToIR m`, the raw IR, which made this shape
  -- relate two different programs.
  ∀ (n : ℕ) → at (asm-sem asm) n ≡ at (ft (moduleToIR-emitted m)) n

------------------------------------------------------------------------
-- `ir-flat-correct` — PROVED from `traces-agree` (was a postulate).
------------------------------------------------------------------------

-- D113/D115: at THIS target's NUMERICS — the format and the width — which
-- is where `IRObsCorrectFlat`'s `evalᴰ` alias reads them from too, so the
-- two sides mean one thing.
ir-flat-correct-fam : (ioc : ∀ {A B} (ir : IR A B) → IRObsCorrectF ir)
                   → (brs : (ir : IR Unit Unit) → BlockRuns (ir-to-trace ir))
                   → ∀ (mir : Maybe (IR Unit Unit)) (n : ℕ)
                   → flat-trace-fam ioc brs mir n ≡ at (⟦ mir ⟧IR (Once.CCC.FrameSemantics.fs-numerics FS)) n
ir-flat-correct-fam ioc brs nothing   n = refl
-- D159: peel the chain off the fuel (`flat-events-steps`), and the leftover is
-- `flat-events 0`, i.e. `[]`. So the run's events ARE the chain's events, and
-- the chain's events are what `traces-agree` now speaks about.
ir-flat-correct-fam ioc brs (just ir) n =
  trans (cong (take n)
          (trans (flat-events-steps (ValueRealized.run (entry-vr ir ioc brs n)) 0)
                 (++-identityʳ (chain-events (ValueRealized.run (entry-vr ir ioc brs n))))))
        (trans (MachineRefinesObsF.traces-agree (entry-witness ir (ioc ir) brs n))
               -- `at` no longer caps: `bounded` says the depth-`n` prefix is
               -- already at most `n` long, so the cap was the identity.
               (take-all n _ (bnd (proj₁ (evalᴰ-good (Once.CCC.FrameSemantics.fs-numerics FS) ir tt tt)) n)))

-- …and THAT is what makes the machine's family a `Behavior`: it borrows the
-- three laws from the denotation it is proved equal to (`behavior-by`). The
-- machine side never needs a prefix-family induction of its own — the
-- correctness theorem is the transport.
flat-trace-of : (∀ {A B} (ir : IR A B) → IRObsCorrectF ir)
              → (brs : (ir : IR Unit Unit) → BlockRuns (ir-to-trace ir))
              → Maybe (IR Unit Unit) → Behavior
flat-trace-of ioc brs mir =
  behavior-by (⟦ mir ⟧IR (Once.CCC.FrameSemantics.fs-numerics FS))
              (flat-trace-fam ioc brs mir)
              (λ n → sym (ir-flat-correct-fam ioc brs mir n))

ir-flat-correct-of : (ioc : ∀ {A B} (ir : IR A B) → IRObsCorrectF ir)
                   → (brs : (ir : IR Unit Unit) → BlockRuns (ir-to-trace ir))
                   → ∀ (mir : Maybe (IR Unit Unit)) (n : ℕ)
                   → at (flat-trace-of ioc brs mir) n ≡ at (⟦ mir ⟧IR (Once.CCC.FrameSemantics.fs-numerics FS)) n
ir-flat-correct-of ioc brs mir n = ir-flat-correct-fam ioc brs mir n

------------------------------------------------------------------------
-- The constructed ArchCorrect record — now CONSUMING `ir-obs-correct`.
------------------------------------------------------------------------

-- D165 — THE ARITH PASS PRESERVES THE FLAT TRACE.
--
-- `rewrite-ir` swaps a recognised arith subtree for one `arith.block.<digest>`
-- SigOp. Both sides emit nothing (arith SigOps are pure, Plan 0.25/0.26), so
-- the EVENT lists agree; what has real content is that the block's VALUE
-- equals the subtree's, because an arith result reaches an observable SigOp's
-- argument and a wrong value is a different trace.
--
-- Postulated HERE rather than left inside `asm-trace-correct`: it is compiler
-- logic, not toolchain trust, and it is the obligation D163's regression walked
-- through. Class **deferred proof / codegen**.
postulate
  rewrite-preserves-of :
    (ioc : ∀ {A B} (ir : IR A B) → IRObsCorrectF ir)
    → (brs : (ir : IR Unit Unit) → BlockRuns (ir-to-trace ir))
    → ∀ (mir : Maybe (IR Unit Unit)) (n : ℕ)
    → at (flat-trace-of ioc brs (map-rewrite mir)) n ≡ at (flat-trace-of ioc brs mir) n

flat-from-obs :
  (ioc : ∀ {A B} (ir : IR A B) → IRObsCorrectF ir)
  → (brs : (ir : IR Unit Unit) → BlockRuns (ir-to-trace ir))
  → AsmTraceCorrect (flat-trace-of ioc brs)
  → ArchCorrect arch as
flat-from-obs ioc brs atc = record
  { asm-sem           = asm-sem
  ; flat-trace        = flat-trace-of ioc brs
  ; assemble-correct  = λ _ _ _ _ _ → refl
  ; asm-trace-correct = atc
  -- D165: a NAMED RESIDUAL — the arith pass preserves the flat trace. It was
  -- previously folded into `asm-trace-correct`'s two mismatched sides.
  ; rewrite-preserves = rewrite-preserves-of ioc brs
  -- the one place `fmt-agree` is spent
  ; ir-flat-correct   = λ mir n →
      subst (λ F → at (flat-trace-of ioc brs mir) n ≡ at (⟦ mir ⟧IR F) n)
            fmt-agree (ir-flat-correct-of ioc brs mir n)
  }
