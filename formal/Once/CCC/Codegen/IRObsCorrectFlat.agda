-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.IRObsCorrectFlat — observable correctness over the
-- FLAT machine (Plan 0.36, corrected machine side).
--
-- `MachineRefinesObsF` is the flat-machine instance of the Plan 0.36
-- encoding: a program's only observable is its SigOp trace, so
-- trace-correctness (`traces-agree`) is the headline obligation and
-- value-correctness (`ValidAtWF`) is a FIELD (`value-realized`).
--
-- It runs over `exec-flat` (pc + jump + fuel), NOT the straight-line
-- `exec-trace`, because the recursion schemes compile to LOOPS — so,
-- unlike `compile-correct-flat`, there is NO `StraightIR` precondition.
-- It is also GENERIC in `FrameSemantics` and carries NO target `X.exec`
-- obligation: the per-target machine bridge is the IR-agnostic
-- `flat-sim`, established once per target. So `cata-correct` here is one
-- statement for all targets.
--
-- `cata-correct` is the single named postulate (top-down scaffold):
--   * `traces-agree`   — discharged by μ-induction (`μS-ind`) over the
--                        events fold + per-SigOp `respects-semM`.
--   * `value-realized` — the looping flat-semantic correctness (the
--                        `rec-scheme-semantic` value half).
------------------------------------------------------------------------

-- Plan 0.63 (D089): parameterised by the DEFINITION'S identity, which keys
-- its labels. `o` is constant for a whole definition, so it belongs on the
-- module rather than on every lemma — which is exactly what keeps the
-- statements below UNCHANGED under D089: `IRToTrace` is imported APPLIED,
-- so each `ir-to-trace' n l ir` reads as it always did.
open import Once.CanonicalName using (CanonicalName)

module Once.CCC.Codegen.IRObsCorrectFlat (o : CanonicalName) where

open import Data.Nat using (ℕ; zero; suc; _<_)
open import Data.Bool using (false; true)
open import Data.List using (length; take; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; ∃; ∃-syntax; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Once.CCC.FrameSemantics using (FrameSemantics)
-- SigOpInfo is over SURFACE Type (`SigOp : SigOpInfo A B → IR ⌊A⌋ ⌊B⌋`), so the
-- surface `FitsInReg`/`fits-in-reg?` stay; the μ/functor + value-domain layer is IRTy.
open import Once.Type using (Type; FitsInReg; fits-in-reg?)
  renaming (fits-int to fits-intˢ; fits-float to fits-floatˢ; Int to Intˢ; Unit to Unitˢ)
open import Once.Float.Decimal using (Decimal; round)
open import Data.Integer using (ℤ)
open import Once.IRTy using (WellFormedFI-irrelevant)
open import Once.Semantics.Machine using () renaming (⟦_⟧ᴵ to ⟦_⟧)
open import Once.IR using (IR; IRTy; Unit; AllocMode; Stack; Cata; SigOp; SigOpInfo; out-μ; _∘_;
  μ-type; ⟦_⟧TI; WellFormedFI; FitsInRegI; fits-int; fits-float; ⌊_⌋;
  -- Plan 0.68 step 0: the enumeration needs EVERY constructor in scope, not
  -- just the ones with a clause of their own before it.
  id; ⟨_,_⟩; fst; snd; inl; inr; case; terminal; initial; curry; apply;
  In; Para; Out; in-ν; Ana; Hylo; Fuse; free-heap; const;
  NatTr; ν-type; _*_)
open import Once.IRTy using (⟦_,_⟧-baseI)
open import Once.Memory.HeapAddress using (HeapRef)
open import Once.Word using (Carrier)
open import Data.Unit using (tt)

-- Surface `FitsInReg B` ⇒ erased `FitsInRegI ⌊B⌋`: `⌊Int⌋=Int`, `⌊Float⌋=Float`
-- definitionally, so this is a match-to-refl coherence.
fits-erase : ∀ {B} → FitsInReg B → FitsInRegI ⌊ B ⌋
fits-erase fits-intˢ   = fits-int
fits-erase fits-floatˢ = fits-float
open import Once.SigOp.Info using (effect; EffectShape; Pure; Emits; Halts)
open import Relation.Binary.PropositionalEquality using (refl; sym; trans; cong; subst)
open import Once.IR.Size using (ir-size)
open import Data.Nat.Properties using (≤-<-trans; ≤-trans; m≤m+n; m≤n+m; n≤1+n)
open import Function using (case_of_)
import Once.CCC.Eval as Ev
import Once.Semantics.Machine as EvV
open import Once.CCC.Machine.SMCore
  using (LocState; ValueLocation; SV-Ptr; sv-as-loc; halted; regs; readReg; Input1; Output;
         instr-sigop; mov-to-output; instr-load-const; SV-Lit; writeReg; writeReg-same; AbstractTrace; module AbstractExec; module MemOps)
open import Once.CCC.Machine.Validity using (module ValidityDef)
open import Once.CCC.Machine.ValidAtWFHalted o using (validAtWF-set-halted)
open import Once.CCC.Machine.Allocation using (AllocState; next-slot; module FrontierInvariant)
open import Once.CCC.Machine.Flat using (module FlatMachine)
open import Once.CCC.Codegen.IRToTrace o using (ir-to-trace)
open import Once.CCC.Codegen.CataNextSlot using (module CataNextSlot)
open import Once.CCC.Codegen.CataIRSlotStable o using (module CataIRSlotStable)
open import Once.CCC.Machine.ClosureWellFormed o using (module ClosureWellFormedDef)
import Once.CCC.Machine.ReadTypedAdequate as RTA
open import Once.Denotation.Trace using (SigOpEvent)
import Once.Denotation.DenotTrace as DT
open import Once.Denotation.DenotTrace using (inject)
open import Once.Denotation.TraceMonad using (projTrace)
import Once.Denotation.TraceMonad as TM
open import Once.Adequacy.FlatEvents using (module FlatEventTrace)

module IRObsCorrectFlatness {FS : FrameSemantics} (program-bound : ℕ) where
  -- Plan 0.73 (D113): `eval` is target-relative at `Float` — a float literal
  -- has no format-free machine value. Inside a module already fixed to this
  -- target's `FrameSemantics`, THE evaluator is the one at its float format,
  -- so it is named once here and used unqualified below.
  eval : ∀ {A B} → IR A B → EvV.⟦ A ⟧ᴵ → EvV.⟦ B ⟧ᴵ
  eval = Ev.eval (Once.CCC.FrameSemantics.fs-numerics FS)

  -- …and the reference DENOTATION at the same format. That the machine and the
  -- denotation read the format from ONE place is what makes this module's
  -- obligations discharge: `float-format FS` is what `exec-abstract` encodes a
  -- float literal at, so it is what `evalᴰ` must mean by one.
  evalᴰ : ∀ {A B} → IR A B → DT.⟦ A ⟧ᴰᴵ → TM.T DT.⟦ B ⟧ᴰᴵ
  evalᴰ = DT.evalᴰ (Once.CCC.FrameSemantics.fs-numerics FS)

  open FlatMachine {FS}
  open AbstractExec {FS} using (exec-sigop-halts; exec-sigop-halts-of; exec-sigop-output-of; pure-sigop-output; pure-sigop-out-aux; pure-sigop-out-val; readTyped; readReg-typed)
  open FrontierInvariant {FS} using (BeforeFrontier)
  open ClosureWellFormedDef {FS} program-bound
    using (ValidAtWF; valid-μ-wf; valid-ν-wf; valid-primitive-wf; ResultPlace; at-loc; at-reg; unit-result; prim-sv
          -- Plan 0.68 step 1: the class-A discharges move the value witness
          -- across a REGISTER write. `ValueLocation` is `AtStack`/`AtDynamic`
          -- only — there is no register location — so `readLoc` cannot see a
          -- register write at all, and this is the combinator that says so.
          ; validityWF-mem-preserved)
  open MemOps {FS} using (readLoc)
  open ValidityDef {FS} program-bound using (readLoc-stack-heap-eq)
  open FlatEventTrace {FS} using (flat-events; event-of; flat-events-[])
  open RTA o {FS} program-bound using (Readable; r-unit; r-int; r-pair; readable?; readTyped-adequate)
  open CataNextSlot {FS} using (exec-flat-keeps-next-slot)
  open CataIRSlotStable {FS} using (ir-to-trace-slot-stable)

  -- μ↔layer iso (the strat-const crux), general in F. A μ-value's
  -- validity at `loc` IS its destructured layer's validity at the SAME
  -- `loc` — `valid-μ-wf` (Plan 0.27 Option 3) bakes this in by carrying
  -- the layer's own `ValidAtWF`. Inverting it yields the layer validity
  -- the algebra consumes. (For a `strat-const` functor, `rec-count F = 0`
  -- ⇒ `⟦F⟧T (μ-type F) ≡ ⟦F⟧T A`, so this layer IS `alg`'s input.)
  -- `WellFormedFI-irrelevant` bridges the lemma's `wf` and the proof's.
  μ-layer-iso : ∀ {m F} (wf : WellFormedFI F) (x : ⟦ μ-type F ⟧)
                {alloc : AllocState {FS}} {loc : ValueLocation FS} {s : LocState FS}
              → ValidAtWF m alloc {μ-type F} x loc s
              → ValidAtWF m alloc {⟦ F ⟧TI (μ-type F)} (eval (out-μ wf) x) loc s
  μ-layer-iso wf x (valid-μ-wf wf′ .x layer-v)
    rewrite WellFormedFI-irrelevant wf wf′ = layer-v

  -- The ν analogue, for `Out` (Plan 0.68 step 1). Same one-line inversion:
  -- `valid-ν-wf` carries the layer's own `ValidAtWF`, so destructing it yields
  -- the layer validity `Out`'s result needs.
  ν-layer-iso : ∀ {m F} (wf : WellFormedFI F) (x : ⟦ ν-type F ⟧)
                {alloc : AllocState {FS}} {loc : ValueLocation FS} {s : LocState FS}
              → ValidAtWF m alloc {ν-type F} x loc s
              → ValidAtWF m alloc {⟦ F ⟧TI (ν-type F)} (eval (Out wf) x) loc s
  ν-layer-iso wf x (valid-ν-wf wf′ .x layer-v)
    rewrite WellFormedFI-irrelevant wf wf′ = layer-v

  -- The flat run of `ir` from `s`/`alloc` at a given fuel (frontier 0).
  flat-run : ℕ → ∀ {A B} → IR A B → LocState FS → AllocState {FS} → FlatState
  flat-run fuel ir s alloc = exec-flat fuel (ir-to-trace ir) (mkFlat s alloc 0)

  -- Frame discipline (codegen-image half + machine half wired together):
  -- running any compiled IR preserves the stack-frame frontier `next-slot`.
  -- `ir-to-trace-slot-stable` (no trace touches next-slot) + `exec-flat-
  -- keeps-next-slot` (exec-flat preserves it for slot-stable traces). This
  -- is what `value-realized` needs to apply the algebra's `IRObsCorrectF`
  -- IH at every cata layer: the cata scaffold keeps `next-slot ≡ 0`, so the
  -- algebra's `next-slot alloc ≡ 0` precondition holds at each layer's run.
  flat-run-keeps-next-slot :
    ∀ (fuel : ℕ) {A B} (ir : IR A B) (s : LocState FS) (alloc : AllocState {FS})
    → next-slot (falloc (flat-run fuel ir s alloc)) ≡ next-slot alloc
  flat-run-keeps-next-slot fuel ir s alloc =
    exec-flat-keeps-next-slot (ir-to-trace ir) (ir-to-trace-slot-stable ir) fuel (mkFlat s alloc 0)

  -- The cata corollary `value-realized` consumes directly: an algebra run
  -- from a 0-frontier entry alloc still sees `next-slot ≡ 0` afterwards, so
  -- the next layer's algebra call meets its `IRObsCorrectF` precondition.
  alg-run-keeps-frontier-0 :
    ∀ (fuel : ℕ) {A B} (ir : IR A B) (s : LocState FS) (alloc : AllocState {FS})
    → next-slot alloc ≡ 0
    → next-slot (falloc (flat-run fuel ir s alloc)) ≡ 0
  alg-run-keeps-frontier-0 fuel ir s alloc eq =
    trans (flat-run-keeps-next-slot fuel ir s alloc) eq

  -- Observable refinement over the flat machine.
  --
  -- FUEL = "just enough", not a step-index. A `Cata` is a TOTAL inductive
  -- fold over a finite μ-value, so its compiled loop TERMINATES: `enough-fuel`
  -- is a (finite, input-dependent) WITNESS that the run completes
  -- (`run-halts`), provable from totality. Every cata is verified with its
  -- OWN sufficient fuel — no fixed constant, so no program is left unverified.
  -- (A fixed `n` like `defaultFuel = 10000` is only the executable's runtime
  -- guard, never the correctness fuel.) The single step-INDEXED loop in a
  -- total+productive program is the top-level event loop = an `Ana`
  -- coinductive unfold (∀ n: first-n events match); a non-terminating loop
  -- nested inside another can't be productive. So `Cata` carries a termination
  -- witness; only `Ana` carries a step-index.
  record MachineRefinesObsF {A B} (ir : IR A B) (x : ⟦ A ⟧)
                             (s : LocState FS) (alloc : AllocState {FS}) : Set where
    field
      -- NO completion fields (M3, D058: "productivity — not termination").
      -- `run-halts` ("the run halts") is exactly what excludes `Ana`; instead,
      -- the machine REFINES the denotational `evalᴰ` at each observation depth
      -- `k` PRODUCTIVELY: there EXISTS a fuel `f` that emits the first `k`
      -- effectful events, matching `evalᴰ`'s depth-`k` event-prefix. The `∃ f`
      -- is the productivity witness, never the observable index (which is `k`).
      -- (Cata emits a full finite trace; Ana grows with depth — both composed
      -- correctly in `evalᴰ`, observed by the `take k` event-prefix.)
      traces-agree :
        ∀ (k : ℕ) → ∃[ f ]
          take k (flat-events f (ir-to-trace ir) (mkFlat s alloc 0))
            ≡ take k (projTrace (evalᴰ ir (inject x)) k)
      -- The value device: "the value the next effectful SigOp reads is right".
      -- Plan 0.54 rung A: a `ResultPlace` (register `at-reg` OR memory `at-loc`),
      -- NOT bare `ValidAtWF` at a memory loc — a Pure primitive result is
      -- register-resident (`Output`), so the memory-only form could not capture
      -- it. This is the `Place` split (register-allocation both-residences); the
      -- register count per arch is rung B. Final-value form (its own fuel `f`).
      value-realized :
        ∃[ f ] ∃[ mOut ] ∃[ ca ]
          ResultPlace B mOut (falloc (flat-run f ir s alloc)) ca
            (eval ir x)
            (forced (floc (flat-run f ir s alloc)))

  -- The INPUT's residence — the input-side mirror of `ResultPlace`. `Input1`
  -- either POINTS at the value in memory (`in-loc`, the spill path) or HOLDS it
  -- directly as a register literal (`in-reg`, the fast path). Forced top-down by
  -- `comp-step`: `ir-to-trace (g ∘ f) = ft ++ mov-to-input ∷ gt`, so after a
  -- primitive-returning `f` the mov leaves `Input1` holding an `SV-Lit` — a
  -- pointer-only precondition could never be met, and `g`'s IH could not be
  -- applied at all. Generalising a PRECONDITION strengthens the obligation (it
  -- must now hold in more situations); the apex statement is untouched.
  data InputAt {A : IRTy} (v : ⟦ A ⟧) (loc : ValueLocation FS) (s : LocState FS) : Set where
    in-loc : readReg (regs s) Input1 ≡ SV-Ptr loc → InputAt v loc s
    in-reg : (fit : FitsInRegI A) → readReg (regs s) Input1 ≡ prim-sv fit v
           → InputAt v loc s
    -- D074: a UNIT input has no residence at all — `Input1` may hold anything
    -- (the entry state's tag filler; after `f : IR A Unit` in a composition,
    -- `f`'s unit output is likewise unconstrained, so a residence premise
    -- would make `comp-step`'s IH inapplicable). The machine never reads a
    -- unit input: `readTyped Unit` and `readReg-typed Unit` both materialise
    -- `tt` regardless of what is there.
    in-unit : A ≡ Unit → InputAt v loc s

  -- Same preconditions as `compile-correct-flat`'s semantic side (entry
  -- frontier 0), minus `StraightIR` (loops are allowed); conclusion is
  -- the flat refinement.
  IRObsCorrectF : ∀ {A B} → IR A B → Set
  IRObsCorrectF {A} {B} ir =
    ir-size ir < program-bound →
    ∀ (mIn : AllocMode) (x : ⟦ A ⟧) (input-loc : ValueLocation FS)
      (s : LocState FS) (alloc : AllocState {FS}) →
    next-slot alloc ≡ 0 →
    ValidAtWF mIn alloc x input-loc s →
    BeforeFrontier alloc input-loc →
    halted s ≡ false →
    InputAt x input-loc s →
    MachineRefinesObsF ir x s alloc

  -- `cata-correct`: the single named obligation; the record FIELDS name the
  -- parts the discharge must provide (all sharing one `enough-fuel`):
  --   * `enough-fuel`/`run-halts` — the cata terminates (totality witness).
  --   * `traces-agree`  — loop↔fold: discharge by `μS-ind` over the events
  --                       fold + per-`instr-sigop` `respects-semM`. (Pure-cata
  --                       sub-case already dischargeable: `flat-events-[]` +
  --                       `pure-cata-emits-[]`, both `[]`.)
  --   * `value-realized`— looping flat-semantic value correctness (= the
  --                       existing `rec-scheme-semantic` trust boundary).
  -- These are the boundaries the cata collapses into; Phase 4 then deletes the
  -- old `ir-to-trace-correct-non-layer0` catchall + `rec-scheme-semantic`.
  -- `cata-correct` now RECEIVES the algebra's `IRObsCorrectF` (the IH) — this
  -- is what discharges the per-layer machine↔otrace correspondence's link (2)
  -- (`flat-events(alg) ≡ otrace(alg)`), the algebra's OWN trace correctness.
  -- `ir-obs-correct` supplies it by recursing on `alg ⊂ Cata wf alg`.
  postulate
    cata-correct : ∀ {F} (wf : WellFormedFI F) {E A} (alg : IR (E * ⟦ F ⟧TI A) A)
                 → IRObsCorrectF alg
                 → IRObsCorrectF (Cata wf alg)

  -- ════════════════════════════════════════════════════════════════════
  -- `ir-obs-correct` — the GENERIC IR-observable theorem: a TOTAL dispatch
  -- over the IR giving every shape its observable-correctness witness. This
  -- is the connection to ALL CCC IRs: the per-arch `ir-flat-correct` (in
  -- `Verified.Compile.ArchCorrect`) is discharged THROUGH it (via the
  -- entry-state + ∀-fuel adapter). Being total, the type-checker forces every
  -- IR constructor to be accounted for — a new constructor cannot slip
  -- through unproven.
  --
  --   * `Cata` routes to `cata-correct` (the loop obligation, whose intended
  --     discharge is the descend/base/ascend μ-induction. The `CataNat*`
  --     attempt at it was NatF-only and is deleted (D132).
  --     NOT WIREABLE AS IT STANDS, and the reason is worth recording: this
  --     pointer was written 2026-06-13, and four days later `5088e571`
  --     deleted `CataNatAscend`/`CataNatValue`/`CataNatTrace` as "dead …
  --     no live importers". So of the three phases the induction composes,
  --     only DESCEND survived, and it too is now deleted (D132) — it was
  --     (`CataNatDescend*`/`Chain`/`Heap*`/`Producer`/
  --     `Seam` — kept, since they prove content this module only postulates).
  --     Closing `cata-correct` means REBUILDING base and ascend, not wiring
  --     up what is here.
  --   * everything else USED to be `obs-correct-rest`, one catch-all clause
  --     routing every remaining constructor to a single postulate. Plan 0.68
  --     STEP 0 ENUMERATED it — see below for why that was not cosmetic.
  -- ════════════════════════════════════════════════════════════════════

  -- ════════════════════════════════════════════════════════════════════
  -- THE ENUMERATION (Plan 0.68 STEP 0). One named obligation per IR
  -- constructor, replacing the `obs-correct-rest` catch-all.
  --
  -- WHY. A catch-all routing every case to one postulate hides two different
  -- kinds of falsity, and this one was hiding both:
  --
  --   * LABELS. `curry`/`case` emit `c-jmp`/`c-thunk`/`c-label`, and the flat
  --     machine resolves by a FIRST-MATCH scan over the whole trace. If two
  --     definitions share a label the jump lands on the wrong one, so the
  --     machine's events diverge from `evalᴰ` — the obligation is FALSE, not
  --     merely unproved. That is D099's defect, and `cata-correct` (next door)
  --     is where it actually bites: `cata-dispatch` splices the algebra trace
  --     TWICE at one label range. `as` was the only component in the stack that
  --     noticed, seven weeks later, for an unrelated reason.
  --   * UNIMPLEMENTED CODEGEN. `Para`, `Ana`, `Hylo`, `Fuse` and `in-ν` compile
  --     to the EMPTY TRACE (`ir-to-trace' n l (Para _ _) = n , l , [] , []`).
  --     For any argument whose denotation emits an event, `traces-agree`
  --     compares `[]` against a non-empty prefix. Refutable, for a reason that
  --     has nothing to do with labels — and no proof discharges it, because
  --     what is missing is the emitter.
  --
  -- Enumerated, each is independently attackable and a false one is isolated
  -- instead of laundered through its neighbours. The count rising from one to
  -- twenty is correct: the content assumed is unchanged and now it is NAMED.
  --
  -- IHs are NOT threaded here. `comp-obs-correct` shows the target shape (take
  -- the sub-witnesses, so sub-term proofs stay load-bearing), but each needs its
  -- own `ir-size` bound lemma, and those belong with the DISCHARGE of the
  -- constructor that consumes them, not with the bookkeeping. Plan 0.68 steps
  -- 1-4 add them one at a time.
  --
  -- ORDER = `Once.IR`'s own constructor order, so a retired constructor shows
  -- up as a missing clause rather than as a silent variable catch-all.
  -- ════════════════════════════════════════════════════════════════════
  -- ════════════════════════════════════════════════════════════════════
  -- CLASS A, THE SHARED CORE (Plan 0.68 step 1).
  --
  -- Six constructors compile to the SAME one-instruction trace
  -- `mov-to-output ∷ []` (`id`, `initial`, `free-heap`, `In`, `out-μ`, `Out`),
  -- and three more differ only in which single instruction they emit. So the
  -- discharge is written ONCE over the shape and instantiated, rather than
  -- copied nine times.
  --
  -- WHAT MAKES IT EASY, stated once because every class-A/B proof rides it:
  -- `ValueLocation` is `AtStack f k` or `AtDynamic hl` — there is NO register
  -- location. So `readLoc` reads memory only, a register write is invisible to
  -- it, and every memory-side invariant (`ValidAtWF`, and `BeforeFrontier`
  -- which does not mention the state at all) survives `mov-to-output`
  -- DEFINITIONALLY. `readLoc-stack-heap-eq` is the discharge of that, and
  -- `validAtWF-set-halted` covers the `forced` at the end of the run.
  -- ════════════════════════════════════════════════════════════════════

  -- The missing half of `Flat`'s with-free step API: what the machine does when
  -- the pc runs off the end of the trace. `exec-flat-step` peels a fetched
  -- instruction; this peels the FINAL fetch, which halts. Stated over an
  -- OPAQUE `fs` with both decisions as hypotheses — the same discipline, and
  -- the reason it is needed: after one step the inner `halted (floc fs₁)` is no
  -- longer a syntactic occurrence in the goal, so a second `rewrite` cannot
  -- reach it. A semantic step API can.
  exec-flat-stop : ∀ (n : ℕ) (prog : AbstractTrace) (fs : FlatState)
    → halted (floc fs) ≡ false
    → fetch prog (fpc fs) ≡ nothing
    → exec-flat (suc n) prog fs ≡ record fs { floc = record (floc fs) { halted = true } }
  exec-flat-stop n prog fs h-eq f-eq rewrite h-eq | f-eq = refl

  -- The post-run state of a one-instruction register-only trace: memory is
  -- untouched, so `readLoc` agrees with the entry state at EVERY location.
  reg-write-readLoc : ∀ (s : LocState FS) (v : _) (b : _) (loc : ValueLocation FS)
    → readLoc (record (record s { regs = v }) { halted = b }) loc ≡ readLoc s loc
  reg-write-readLoc s v b loc =
    readLoc-stack-heap-eq (record (record s { regs = v }) { halted = b }) s loc refl refl

  -- ── `id` — DISCHARGED (Plan 0.68 step 1, the first of class A).
  --
  -- `ir-to-trace id = mov-to-output ∷ []`, so the whole run is: one register
  -- write, then a fetch off the end of the trace (which halts). Both halves of
  -- `MachineRefinesObsF` fall out:
  --   traces-agree   — `mov-to-output` emits no event and `evalᴰ id = returnT`
  --                    emits none either, so both sides are `[]`.
  --   value-realized — `Output := Input1`, so the result's residence IS the
  --                    input's residence: the three `InputAt` shapes map onto
  --                    the three `ResultPlace` shapes one-for-one.
  --
  -- The single reduction lemma `run-eq` is what keeps this readable: `exec-flat`
  -- is stuck on `halted s` until `nh` fires, so the reduction is done ONCE and
  -- every component rewrites by it, instead of each re-deriving the run.
  obs-correct-id : ∀ {A} → IRObsCorrectF (id {A})
  obs-correct-id {A} _ mIn x input-loc s alloc _ valid input-before nh rdi-eq =
    record
      { traces-agree = λ k →
          2 , trans (cong (take k) (mach-[] 2)) (cong (take k) (sym (denot-[] k)))
      ; value-realized =
          2 , mIn , falloc (flat-run 2 (id {A}) s alloc) , place rdi-eq
      }
    where
      -- The post-`mov` register file and the intermediate flat state. `run-eq`
      -- is derived from the two step lemmas rather than by `rewrite nh`: the
      -- second step's `halted` test is not a syntactic occurrence in the goal.
      regs' = writeReg (regs s) Output (readReg (regs s) Input1)
      fs₁   = flat-exec-instr mov-to-output (ir-to-trace (id {A})) (mkFlat s alloc 0)

      run-eq : flat-run 2 (id {A}) s alloc
             ≡ record fs₁ { floc = record (floc fs₁) { halted = true } }
      run-eq = trans (exec-flat-step 1 (ir-to-trace (id {A})) (mkFlat s alloc 0)
                        mov-to-output nh refl)
                     (exec-flat-stop 0 (ir-to-trace (id {A})) fs₁ nh refl)

      -- Machine side: the only fetchable instruction is `mov-to-output`, which
      -- emits nothing.
      ev-[] : ∀ pc i → fetch (ir-to-trace (id {A})) pc ≡ just i → ∀ fs → event-of i fs ≡ []
      ev-[] zero    .mov-to-output refl fs = refl
      ev-[] (suc n) i              ()   fs

      mach-[] : ∀ f → flat-events f (ir-to-trace (id {A})) (mkFlat s alloc 0) ≡ []
      mach-[] f = flat-events-[] (ir-to-trace (id {A})) ev-[] f (mkFlat s alloc 0)

      -- Denotation side: `evalᴰ id a = returnT a` emits nothing.
      denot-[] : ∀ k → projTrace (evalᴰ (id {A}) (inject x)) k ≡ []
      denot-[] k = refl

      keeps-alloc : falloc (flat-run 2 (id {A}) s alloc) ≡ alloc
      keeps-alloc rewrite run-eq = refl

      -- A register write is invisible to `readLoc` (there is no register
      -- `ValueLocation`), and so is the halt flag.
      mem-eq : ∀ loc' → readLoc (forced (floc (flat-run 2 (id {A}) s alloc))) loc' ≡ readLoc s loc'
      mem-eq loc' rewrite run-eq = reg-write-readLoc s regs' true loc'

      valid' : ValidAtWF mIn alloc x input-loc (forced (floc (flat-run 2 (id {A}) s alloc)))
      valid' = validityWF-mem-preserved x input-loc s _ input-before
                 (λ loc' _ → mem-eq loc') valid

      out-ptr : readReg (regs s) Input1 ≡ SV-Ptr input-loc
              → readReg (regs (forced (floc (flat-run 2 (id {A}) s alloc)))) Output ≡ SV-Ptr input-loc
      out-ptr eq rewrite run-eq =
        trans (writeReg-same (regs s) Output (readReg (regs s) Input1)) eq

      out-lit : ∀ (fit : FitsInRegI A) → readReg (regs s) Input1 ≡ prim-sv fit x
              → readReg (regs (forced (floc (flat-run 2 (id {A}) s alloc)))) Output ≡ prim-sv fit x
      out-lit fit eq rewrite run-eq =
        trans (writeReg-same (regs s) Output (readReg (regs s) Input1)) eq

      before' : BeforeFrontier (falloc (flat-run 2 (id {A}) s alloc)) input-loc
      before' rewrite keeps-alloc = input-before

      place : InputAt x input-loc s
            → ResultPlace A mIn (falloc (flat-run 2 (id {A}) s alloc))
                (falloc (flat-run 2 (id {A}) s alloc)) (eval (id {A}) x)
                (forced (floc (flat-run 2 (id {A}) s alloc)))
      place (in-loc eq)      = at-loc input-loc valid'' before' (out-ptr eq) valid'' before'
        where valid'' = subst (λ a → ValidAtWF mIn a x input-loc
                                       (forced (floc (flat-run 2 (id {A}) s alloc))))
                              (sym keeps-alloc) valid'
      place (in-reg fit eq)  = at-reg input-loc fit before' (out-lit fit eq) before'
      place (in-unit refl)   = unit-result

  -- ── `terminal` — DISCHARGED. The emitter emits NOTHING for it
  -- (`ir-to-trace terminal = []`), which is right: the codomain is `Unit`, the
  -- erased type, so there is no value to place and no event to emit. `fetch []`
  -- is `nothing` at every pc, so both `ev-[]` clauses are absurd, and the
  -- result place is `unit-result` — which asserts nothing about the state,
  -- exactly because a unit result has no residence (D074).
  obs-correct-terminal : ∀ {A} → IRObsCorrectF (terminal {A})
  obs-correct-terminal {A} _ mIn x input-loc s alloc _ valid input-before nh rdi-eq =
    record
      { traces-agree = λ k → 1 , cong (take k) (mach-[] 1)
      ; value-realized = 1 , mIn , falloc (flat-run 1 (terminal {A}) s alloc) , unit-result
      }
    where
      ev-[] : ∀ pc i → fetch (ir-to-trace (terminal {A})) pc ≡ just i → ∀ fs → event-of i fs ≡ []
      ev-[] zero    i () fs
      ev-[] (suc n) i () fs

      mach-[] : ∀ f → flat-events f (ir-to-trace (terminal {A})) (mkFlat s alloc 0) ≡ []
      mach-[] f = flat-events-[] (ir-to-trace (terminal {A})) ev-[] f (mkFlat s alloc 0)

  -- ── `initial` — DISCHARGED, VACUOUSLY, and that is the honest reading.
  -- `initial : IR Void A` and `⟦ Void ⟧ᴵ` is `⊥`, so there is no input to run
  -- on. The denotation agrees: `evalᴰ initial ()` is itself defined by an
  -- absurd pattern. The emitter's `mov-to-output` is never reached because the
  -- state it would run from cannot exist.
  obs-correct-initial : ∀ {A} → IRObsCorrectF (initial {A})
  obs-correct-initial _ mIn ()

  -- ── `free-heap` — DISCHARGED. `IR Unit Unit`, a semantic no-op that still
  -- compiles to `mov-to-output ∷ []` (copy through, so the register discipline
  -- holds). Unit codomain ⇒ `unit-result`; no event on either side.
  obs-correct-free-heap : ∀ (r : HeapRef) → IRObsCorrectF (free-heap r)
  obs-correct-free-heap r _ mIn x input-loc s alloc _ valid input-before nh rdi-eq =
    record
      { traces-agree = λ k → 2 , cong (take k) (mach-[] 2)
      ; value-realized = 2 , mIn , falloc (flat-run 2 (free-heap r) s alloc) , unit-result
      }
    where
      ev-[] : ∀ pc i → fetch (ir-to-trace (free-heap r)) pc ≡ just i → ∀ fs → event-of i fs ≡ []
      ev-[] zero    .mov-to-output refl fs = refl
      ev-[] (suc n) i              ()   fs

      mach-[] : ∀ f → flat-events f (ir-to-trace (free-heap r)) (mkFlat s alloc 0) ≡ []
      mach-[] f = flat-events-[] (ir-to-trace (free-heap r)) ev-[] f (mkFlat s alloc 0)

  -- ── `out-μ` / `Out` — DISCHARGED. Both are Lambek inverses compiling to the
  -- same `mov-to-output ∷ []` as `id`, and both are DOMAIN-RESTRICTED in a way
  -- that kills two of the three input residences outright:
  --   * `in-reg` carries `FitsInRegI (μ-type F)`, and `FitsInRegI` has only
  --     `fits-int`/`fits-float` — absurd;
  --   * `in-unit` claims `μ-type F ≡ Unit` — absurd by constructor disjointness.
  -- So only the pointer residence survives, and the value witness is exactly
  -- the layer iso: `valid-μ-wf`/`valid-ν-wf` CARRY the layer's own `ValidAtWF`
  -- (Plan 0.27 Option 3), so destructing one yields what `at-loc` wants.
  obs-correct-out-μ : ∀ {F} (wf : WellFormedFI F) → IRObsCorrectF (out-μ wf)
  obs-correct-out-μ {F} wf _ mIn x input-loc s alloc _ valid input-before nh rdi-eq =
    record
      { traces-agree = λ k → 2 , cong (take k) (mach-[] 2)
      ; value-realized =
          2 , mIn , falloc (flat-run 2 (out-μ wf) s alloc) , place rdi-eq
      }
    where
      regs' = writeReg (regs s) Output (readReg (regs s) Input1)
      fs₁   = flat-exec-instr mov-to-output (ir-to-trace (out-μ wf)) (mkFlat s alloc 0)

      run-eq : flat-run 2 (out-μ wf) s alloc
             ≡ record fs₁ { floc = record (floc fs₁) { halted = true } }
      run-eq = trans (exec-flat-step 1 (ir-to-trace (out-μ wf)) (mkFlat s alloc 0)
                        mov-to-output nh refl)
                     (exec-flat-stop 0 (ir-to-trace (out-μ wf)) fs₁ nh refl)

      ev-[] : ∀ pc i → fetch (ir-to-trace (out-μ wf)) pc ≡ just i → ∀ fs → event-of i fs ≡ []
      ev-[] zero    .mov-to-output refl fs = refl
      ev-[] (suc n) i              ()   fs

      mach-[] : ∀ f → flat-events f (ir-to-trace (out-μ wf)) (mkFlat s alloc 0) ≡ []
      mach-[] f = flat-events-[] (ir-to-trace (out-μ wf)) ev-[] f (mkFlat s alloc 0)

      keeps-alloc : falloc (flat-run 2 (out-μ wf) s alloc) ≡ alloc
      keeps-alloc rewrite run-eq = refl

      mem-eq : ∀ loc' → readLoc (forced (floc (flat-run 2 (out-μ wf) s alloc))) loc' ≡ readLoc s loc'
      mem-eq loc' rewrite run-eq = reg-write-readLoc s regs' true loc'

      valid' : ValidAtWF mIn alloc x input-loc (forced (floc (flat-run 2 (out-μ wf) s alloc)))
      valid' = validityWF-mem-preserved x input-loc s _ input-before
                 (λ loc' _ → mem-eq loc') valid

      valid'' : ValidAtWF mIn (falloc (flat-run 2 (out-μ wf) s alloc))
                  (eval (out-μ wf) x) input-loc
                  (forced (floc (flat-run 2 (out-μ wf) s alloc)))
      valid'' = subst (λ a → ValidAtWF mIn a (eval (out-μ wf) x) input-loc
                               (forced (floc (flat-run 2 (out-μ wf) s alloc))))
                      (sym keeps-alloc) (μ-layer-iso wf x valid')

      out-ptr : readReg (regs s) Input1 ≡ SV-Ptr input-loc
              → readReg (regs (forced (floc (flat-run 2 (out-μ wf) s alloc)))) Output
                ≡ SV-Ptr input-loc
      out-ptr eq rewrite run-eq =
        trans (writeReg-same (regs s) Output (readReg (regs s) Input1)) eq

      before' : BeforeFrontier (falloc (flat-run 2 (out-μ wf) s alloc)) input-loc
      before' rewrite keeps-alloc = input-before

      place : InputAt x input-loc s
            → ResultPlace (⟦ F ⟧TI (μ-type F)) mIn (falloc (flat-run 2 (out-μ wf) s alloc))
                (falloc (flat-run 2 (out-μ wf) s alloc)) (eval (out-μ wf) x)
                (forced (floc (flat-run 2 (out-μ wf) s alloc)))
      place (in-loc eq)   = at-loc input-loc valid'' before' (out-ptr eq) valid'' before'
      place (in-reg () _)
      place (in-unit ())

  obs-correct-Out : ∀ {F} (wf : WellFormedFI F) → IRObsCorrectF (Out wf)
  obs-correct-Out {F} wf _ mIn x input-loc s alloc _ valid input-before nh rdi-eq =
    record
      { traces-agree = λ k → 2 , cong (take k) (mach-[] 2)
      ; value-realized =
          2 , mIn , falloc (flat-run 2 (Out wf) s alloc) , place rdi-eq
      }
    where
      regs' = writeReg (regs s) Output (readReg (regs s) Input1)
      fs₁   = flat-exec-instr mov-to-output (ir-to-trace (Out wf)) (mkFlat s alloc 0)

      run-eq : flat-run 2 (Out wf) s alloc
             ≡ record fs₁ { floc = record (floc fs₁) { halted = true } }
      run-eq = trans (exec-flat-step 1 (ir-to-trace (Out wf)) (mkFlat s alloc 0)
                        mov-to-output nh refl)
                     (exec-flat-stop 0 (ir-to-trace (Out wf)) fs₁ nh refl)

      ev-[] : ∀ pc i → fetch (ir-to-trace (Out wf)) pc ≡ just i → ∀ fs → event-of i fs ≡ []
      ev-[] zero    .mov-to-output refl fs = refl
      ev-[] (suc n) i              ()   fs

      mach-[] : ∀ f → flat-events f (ir-to-trace (Out wf)) (mkFlat s alloc 0) ≡ []
      mach-[] f = flat-events-[] (ir-to-trace (Out wf)) ev-[] f (mkFlat s alloc 0)

      keeps-alloc : falloc (flat-run 2 (Out wf) s alloc) ≡ alloc
      keeps-alloc rewrite run-eq = refl

      mem-eq : ∀ loc' → readLoc (forced (floc (flat-run 2 (Out wf) s alloc))) loc' ≡ readLoc s loc'
      mem-eq loc' rewrite run-eq = reg-write-readLoc s regs' true loc'

      valid' : ValidAtWF mIn alloc x input-loc (forced (floc (flat-run 2 (Out wf) s alloc)))
      valid' = validityWF-mem-preserved x input-loc s _ input-before
                 (λ loc' _ → mem-eq loc') valid

      valid'' : ValidAtWF mIn (falloc (flat-run 2 (Out wf) s alloc))
                  (eval (Out wf) x) input-loc
                  (forced (floc (flat-run 2 (Out wf) s alloc)))
      valid'' = subst (λ a → ValidAtWF mIn a (eval (Out wf) x) input-loc
                               (forced (floc (flat-run 2 (Out wf) s alloc))))
                      (sym keeps-alloc) (ν-layer-iso wf x valid')

      out-ptr : readReg (regs s) Input1 ≡ SV-Ptr input-loc
              → readReg (regs (forced (floc (flat-run 2 (Out wf) s alloc)))) Output
                ≡ SV-Ptr input-loc
      out-ptr eq rewrite run-eq =
        trans (writeReg-same (regs s) Output (readReg (regs s) Input1)) eq

      before' : BeforeFrontier (falloc (flat-run 2 (Out wf) s alloc)) input-loc
      before' rewrite keeps-alloc = input-before

      place : InputAt x input-loc s
            → ResultPlace (⟦ F ⟧TI (ν-type F)) mIn (falloc (flat-run 2 (Out wf) s alloc))
                (falloc (flat-run 2 (Out wf) s alloc)) (eval (Out wf) x)
                (forced (floc (flat-run 2 (Out wf) s alloc)))
      place (in-loc eq)   = at-loc input-loc valid'' before' (out-ptr eq) valid'' before'
      place (in-reg () _)
      place (in-unit ())

  -- ── `const` — DISCHARGED, and it is the first REGISTER-resident result of
  -- class A. `ir-to-trace (const fit v) = instr-load-const fitˢ v ∷ []`, whose
  -- `exec-abstract` writes `SV-Lit fitˢ v` to `Output` — which is exactly
  -- `prim-sv fit v`, the literal `at-reg` claims. The domain is `Unit`, so the
  -- input residence plays no part at all (nothing is read).
  --
  -- Two clauses because `prim-sv` dispatches on the `FitsInRegI` evidence; the
  -- bodies are identical.
  obs-correct-const : ∀ {A} (fit : FitsInRegI A) (v : ⟦ ℤ , Decimal ⟧-baseI A)
                    → IRObsCorrectF (const fit v)
  obs-correct-const fits-int v _ mIn x input-loc s alloc _ valid input-before nh rdi-eq =
    record
      { traces-agree = λ k → 2 , cong (take k) (mach-[] 2)
      ; value-realized =
          2 , mIn , falloc (flat-run 2 (const fits-int v) s alloc) ,
          at-reg input-loc fits-int before' out-lit before'
      }
    where
      instr = instr-load-const fits-intˢ v
      fs₁   = flat-exec-instr instr (ir-to-trace (const fits-int v)) (mkFlat s alloc 0)

      run-eq : flat-run 2 (const fits-int v) s alloc
             ≡ record fs₁ { floc = record (floc fs₁) { halted = true } }
      run-eq = trans (exec-flat-step 1 (ir-to-trace (const fits-int v)) (mkFlat s alloc 0)
                        instr nh refl)
                     (exec-flat-stop 0 (ir-to-trace (const fits-int v)) fs₁ nh refl)

      ev-[] : ∀ pc i → fetch (ir-to-trace (const fits-int v)) pc ≡ just i → ∀ fs → event-of i fs ≡ []
      ev-[] zero    .instr refl fs = refl
      ev-[] (suc n) i      ()   fs

      mach-[] : ∀ f → flat-events f (ir-to-trace (const fits-int v)) (mkFlat s alloc 0) ≡ []
      mach-[] f = flat-events-[] (ir-to-trace (const fits-int v)) ev-[] f (mkFlat s alloc 0)

      keeps-alloc : falloc (flat-run 2 (const fits-int v) s alloc) ≡ alloc
      keeps-alloc rewrite run-eq = refl

      before' : BeforeFrontier (falloc (flat-run 2 (const fits-int v) s alloc)) input-loc
      before' rewrite keeps-alloc = input-before

      out-lit : readReg (regs (forced (floc (flat-run 2 (const fits-int v) s alloc)))) Output
              ≡ prim-sv fits-int (eval (const fits-int v) x)
      -- D115: the machine MATERIALISES the literal, exactly as the float
      -- case below does — `lit-value` is two's complement at this width.
      out-lit rewrite run-eq =
        writeReg-same (regs s) Output (SV-Lit fits-intˢ (AbstractExec.lit-value {FS} fits-intˢ v))

  obs-correct-const fits-float v _ mIn x input-loc s alloc _ valid input-before nh rdi-eq =
    record
      { traces-agree = λ k → 2 , cong (take k) (mach-[] 2)
      ; value-realized =
          2 , mIn , falloc (flat-run 2 (const fits-float v) s alloc) ,
          at-reg input-loc fits-float before' out-lit before'
      }
    where
      instr = instr-load-const fits-floatˢ v
      fs₁   = flat-exec-instr instr (ir-to-trace (const fits-float v)) (mkFlat s alloc 0)

      run-eq : flat-run 2 (const fits-float v) s alloc
             ≡ record fs₁ { floc = record (floc fs₁) { halted = true } }
      run-eq = trans (exec-flat-step 1 (ir-to-trace (const fits-float v)) (mkFlat s alloc 0)
                        instr nh refl)
                     (exec-flat-stop 0 (ir-to-trace (const fits-float v)) fs₁ nh refl)

      ev-[] : ∀ pc i → fetch (ir-to-trace (const fits-float v)) pc ≡ just i → ∀ fs → event-of i fs ≡ []
      ev-[] zero    .instr refl fs = refl
      ev-[] (suc n) i      ()   fs

      mach-[] : ∀ f → flat-events f (ir-to-trace (const fits-float v)) (mkFlat s alloc 0) ≡ []
      mach-[] f = flat-events-[] (ir-to-trace (const fits-float v)) ev-[] f (mkFlat s alloc 0)

      keeps-alloc : falloc (flat-run 2 (const fits-float v) s alloc) ≡ alloc
      keeps-alloc rewrite run-eq = refl

      before' : BeforeFrontier (falloc (flat-run 2 (const fits-float v) s alloc)) input-loc
      before' rewrite keeps-alloc = input-before

      out-lit : readReg (regs (forced (floc (flat-run 2 (const fits-float v) s alloc)))) Output
              ≡ prim-sv fits-float (eval (const fits-float v) x)
      -- Plan 0.73 (D113): the machine MATERIALISES the literal as it executes —
      -- `exec-abstract` writes `round (float-format FS) v`, not the payload.
      -- The denotation says the same because `eval` above is at the same
      -- format; that agreement is the whole point of reading it from one place.
      out-lit rewrite run-eq =
        writeReg-same (regs s) Output (SV-Lit fits-floatˢ (round (FrameSemantics.float-format FS) v))

  postulate
    obs-correct-fst       : ∀ {A B} → IRObsCorrectF (fst {A} {B})
    obs-correct-snd       : ∀ {A B} → IRObsCorrectF (snd {A} {B})
    -- `In` — the ONE class-A constructor that did NOT fall to the `id`
    -- template, and the reason is a SPEC gap, not a missing lemma. Its domain
    -- is `⟦ F ⟧TI (μ-type F)`, a stuck application: unlike `out-μ`/`Out` (whose
    -- domains are `μ-type F`/`ν-type F`, so `FitsInRegI …` and `… ≡ Unit` are
    -- both absurd), neither of `In`'s off-pointer input residences can be
    -- refuted — `⟦ K Unit ⟧TI X` really is `Unit`.
    --
    -- In that case the input has NO residence (D074), so after `mov-to-output`
    -- nothing is known about `Output`, and `ResultPlace` has no shape to offer:
    -- `at-loc`/`at-reg` both demand an `Output` equation, and `unit-result`
    -- needs the CODOMAIN to be syntactically `Unit`, which `μ-type F` is not.
    -- The `ValidAtWF` half is free (`valid-μ-wf … valid-unit-wf`); it is the
    -- RESIDENCE that has no witness.
    --
    -- So `ResultPlace` is missing the dual of `InputAt`'s `in-unit`: "an erased
    -- result, no residence claimed". Adding it is a spec change, and per this
    -- plan's own gate the discharge dictates it rather than a guess ahead of
    -- time — deferred with the case named.
    obs-correct-In        : ∀ {F} (wf : WellFormedFI F) (m : AllocMode)
                          → IRObsCorrectF (In wf m)

    -- CLASS B — allocating, no control flow. Step 1; adds the frontier thread.
    obs-correct-pair : ∀ {A B C} (f : IR A B) (g : IR A C) (m : AllocMode)
                     → IRObsCorrectF (⟨ f , g ⟩ m)
    obs-correct-inl  : ∀ {A B} (m : AllocMode) → IRObsCorrectF (inl {A} {B} m)
    obs-correct-inr  : ∀ {A B} (m : AllocMode) → IRObsCorrectF (inr {A} {B} m)

    -- CLASS D — LABEL-BEARING. Step 2/3: these are the obligations that force
    -- the label discipline. `curry` emits `c-jmp end ∷ c-thunk this bb ∷ body
    -- ++ c-ret bb ∷ c-label end ∷ []` in one literal list, so matching
    -- `⟦curry⟧` requires that the parent's jump lands on THIS clause's
    -- `c-label end` — which needs the CONVERSE of `find-label-sound`, false
    -- without label uniqueness. `EmittedWF.labels-unique`'s real consumer.
    obs-correct-curry : ∀ {A B C} (body : IR (A * B) C) (m : AllocMode)
                      → IRObsCorrectF (curry body m)
    obs-correct-case  : ∀ {A B C} (f : IR A C) (g : IR B C)
                      → IRObsCorrectF (case f g)

    -- CLASS E — resolution-consuming. `instr-call-closure` jumps to the code
    -- address a `curry` put in the closure record, so it needs the same
    -- discipline from the other side (`find-thunk`, D082's provenance).
    obs-correct-apply : ∀ {A B} → IRObsCorrectF (apply {A} {B})

    -- CLASS G — THE EMITTER IS MISSING. Each of these compiles to `[]`, so the
    -- obligation is refutable whenever the denotation emits an event. NOT a
    -- proof task: implement the codegen, restrict the IR so they cannot be
    -- built, or condition the obligation to exclude them (Plan 0.68 step 5, and
    -- it needs a decision-log entry either way). Named so the choice is forced.
    obs-correct-Para : ∀ {F} (wf : WellFormedFI F) {A} (f : IR (⟦ F ⟧TI (μ-type F * A)) A)
                     → IRObsCorrectF (Para wf f)
    obs-correct-in-ν : ∀ {F} (wf : WellFormedFI F) (m : AllocMode)
                     → IRObsCorrectF (in-ν wf m)
    obs-correct-Ana  : ∀ {F} (wf : WellFormedFI F) {A} (f : IR A (⟦ F ⟧TI A))
                     → IRObsCorrectF (Ana wf f)
    obs-correct-Hylo : ∀ {F G} (wfF : WellFormedFI F) (wfG : WellFormedFI G) {B}
                       (alg : IR (⟦ F ⟧TI B) B) (nt : NatTr G F)
                     → IRObsCorrectF (Hylo wfF wfG alg nt)
    obs-correct-Fuse : ∀ {F G} (wfF : WellFormedFI F) (wfG : WellFormedFI G) {B}
                       (alg : IR (⟦ F ⟧TI B) B) (nt : NatTr G F)
                     → IRObsCorrectF (Fuse wfF wfG alg nt)

  -- ════════════════════════════════════════════════════════════════════
  -- `obs-correct-sigop` — the `SigOp` case carved OUT of `obs-correct-rest`
  -- and discharged DIRECTLY for the tractable class:
  -- `Pure` + fits-in-reg SigOps (which is exactly `arith.block.*`). This is
  -- the FLAT-machine analogue of `Once.CCC.SigOp.PureProvider` (which does
  -- the same over the abstract `exec-trace`); here we target
  -- `MachineRefinesObsF` over `flat-run`/`flat-events`.
  --
  --   * `traces-agree`  — a `Pure` SigOp is a register computation, not a
  --     syscall: the machine emits `[]` (`flat-events-[]`, since the only
  --     fetchable instr `instr-sigop si` is `Pure` ⇒ `event-of ≡ []`) and
  --     the denotation emits `[]` (`emit-D si _ ≡ []` for `Pure`). Both
  --     sides reduce to `take k [] ≡ take k []`.
  --   * `value-realized` — the codomain fits in a register, so its validity
  --     is location-only (`valid-primitive-wf fitness before`). The single
  --     `instr-sigop` step leaves `alloc` untouched
  --     (`exec-abstract (instr-sigop …)` returns `… , alloc`), so
  --     `BeforeFrontier alloc input-loc` transports to the post-run alloc.
  --
  -- Non-`Pure` or non-fits-in-reg SigOps still route to `obs-correct-rest`,
  -- so the total IR dispatch is preserved.
  -- ════════════════════════════════════════════════════════════════════
  -- ════════════════════════════════════════════════════════════════════
  -- THE ARITH VALUE OBLIGATION (Plan 0.54 rung A) — the single named residual
  -- the whole apex chain now reduces to for a Pure register-returning SigOp:
  -- after the `instr-sigop` step, `Output` holds the REAL result.
  --
  -- TRUE by construction since A4: `exec-abstract (instr-sigop si)` writes
  -- `pure-sigop-output si s = SV-Lit fitB (semM si (readTyped A input-loc s))`
  -- (SMCore), and `readTyped-adequate` (ReadTypedAdequate) turns the `ValidAtWF`
  -- hypothesis into `readTyped A input-loc s ≡ just (subst id (coh A) x)`; with
  -- `eval (SigOp si) x = subst (sym (coh B)) (semM si (subst id (coh A) x))`
  -- (CCC.Eval:83) the two sides coincide modulo the `coh` transports (which are
  -- `refl` on the fits-in-reg base types). Discharge = the next step; stated
  -- here so the apex chain is verified end-to-end against ONE named equation.
  -- ════════════════════════════════════════════════════════════════════
  -- DISCHARGE STATUS: true by construction — `exec-abstract (instr-sigop si)`
  -- writes `pure-sigop-output si s = SV-Lit fit (semM si (readTyped A input-loc s))`
  -- (SMCore, Plan 0.54 A4) and `readTyped-adequate` turns the `ValidAtWF`
  -- hypothesis into `readTyped A input-loc s ≡ just (subst id (coh A) x)`, which
  -- with `eval (SigOp si) x = subst (sym (coh B)) (semM si (subst id (coh A) x))`
  -- (CCC.Eval:83) makes the two sides equal. Verified as far as
  --   `pure-sigop-output si s | just fits-intˢ | sv-as-loc (input1 (regs s))`
  -- (i.e. the codomain and input-pointer dispatches both reduce). The residual is
  -- REDUCTION PLUMBING, not mathematics: `effect` is a DERIVED accessor, so it
  -- unfolds and `rewrite pure-eq` cannot fire on the second fuel step's
  -- `exec-sigop-halts-of`. Fix = generalise the goal over `effect si`
  -- (`with effect si in eq`, or a shape-parameterised helper) so BOTH the output
  -- and halts dispatches resolve together. All hypotheses needed for the
  -- discharge are already in the statement.
  -- A `Pure` SigOp does not halt — a top-level helper (a `where` binding cannot
  -- be used in the clause's own `rewrite`). `exec-sigop-halts si s` IS
  -- `exec-sigop-halts-of (effect si) si s` definitionally, and
  -- `exec-sigop-halts-of Pure si s = false`; so `cong` on the derived accessor
  -- resolves the SECOND fuel step's guard, which plain `rewrite pure-eq` could
  -- not (the accessor unfolds).
  sigop-halts-false : ∀ {A B} (si : SigOpInfo A B) → effect si ≡ Pure
                    → (s : LocState FS) → exec-sigop-halts si s ≡ false
  sigop-halts-false si pure-eq s = cong (λ e → exec-sigop-halts-of e si s) pure-eq

  -- Same shape at the input-pointer dispatch: state the equation at exactly the
  -- form the goal holds (`sv-as-loc (readReg …)`), so `rewrite` matches.
  sv-loc-of : ∀ (s : LocState FS) (input-loc : ValueLocation FS)
            → readReg (regs s) Input1 ≡ SV-Ptr input-loc
            → sv-as-loc (readReg (regs s) Input1) ≡ just input-loc
  sv-loc-of s input-loc eq = cong sv-as-loc eq

  -- REGISTER-RESIDENT INPUT (`in-reg`). `Input1` holds the value, so
  -- `sv-as-loc` gives `nothing` and `pure-sigop-out-aux` takes its register
  -- branch, reading the value with `readReg-typed` (SMCore) — the same equation
  -- therefore holds. Residual = the IRTy/Type seam on the INPUT type (the
  -- `⌊A⌋ ≡ Int` inversion `readReg-typed` needs). CONSUMED by the clause below,
  -- so it is a real obligation on the apex path, not an island.
  -- REGISTER-RESIDENT INPUT (`in-reg`) — PROVED. `Input1` holds the value, so
  -- `sv-as-loc` is `nothing` and `pure-sigop-out-aux` takes its register branch,
  -- reading the value back with `readReg-typed` (SMCore).
  --
  -- The IRTy/Type seam on the INPUT type is supplied by the `Readable A`
  -- evidence the caller already carries: `r-int` gives `A ≡ Int` DIRECTLY (no
  -- separate `⌊A⌋ ≡ Int` inversion needed), and the other two readable shapes
  -- are impossible here — `FitsInRegI ⌊Unit⌋` and `FitsInRegI ⌊_ * _⌋` are empty,
  -- so those clauses are absurd. (Float is not `Readable`, so no float-input case
  -- arises.)
  pure-sigop-value-reg :
      ∀ {A B} (si : SigOpInfo A B) (fitness : FitsInReg B) (rA : Readable A)
      → effect si ≡ Pure
      → ∀ (x : ⟦ ⌊ A ⌋ ⟧) (s : LocState FS) (alloc : AllocState {FS})
          (fit : FitsInRegI ⌊ A ⌋)
      → readReg (regs s) Input1 ≡ prim-sv fit x
      → halted s ≡ false
      → readReg (regs (forced (floc (flat-run 2 (SigOp si) s alloc)))) Output
          ≡ prim-sv (fits-erase fitness) (eval (SigOp si) x)
  pure-sigop-value-reg si fits-intˢ r-int pure-eq x s alloc fits-int rdi-eq nh
    rewrite nh | sigop-halts-false si pure-eq s =
    trans (cong (λ e → exec-sigop-output-of e si s) pure-eq) step2
    where
      step2 : exec-sigop-output-of Pure si s ≡ prim-sv fits-int (eval (SigOp si) x)
      step2 rewrite cong sv-as-loc rdi-eq | cong (readReg-typed Intˢ) rdi-eq = refl
  pure-sigop-value-reg si fits-floatˢ r-int pure-eq x s alloc fits-int rdi-eq nh
    rewrite nh | sigop-halts-false si pure-eq s =
    trans (cong (λ e → exec-sigop-output-of e si s) pure-eq) step2
    where
      step2 : exec-sigop-output-of Pure si s ≡ prim-sv fits-float (eval (SigOp si) x)
      step2 rewrite cong sv-as-loc rdi-eq | cong (readReg-typed Intˢ) rdi-eq = refl
  pure-sigop-value-reg si fitness r-unit       pure-eq x s alloc () rdi-eq nh
  pure-sigop-value-reg si fitness (r-pair _ _) pure-eq x s alloc () rdi-eq nh

  -- UNIT-DOMAIN input (`in-unit`, D074) — a unit input has no residence, so
  -- the output equation must hold whatever `Input1` contains. It does: the
  -- pointer branch ignores the pointee (`readTyped Unit loc s = just tt`) and
  -- the register branch materialises the unit (`readReg-typed Unit _ =
  -- just tt`), so both dispatch arms of `pure-sigop-out-aux` reduce to
  -- `just tt` and each clause is `refl`.
  pure-sigop-out-unit : ∀ {B} (si : SigOpInfo Unitˢ B) (fitB : FitsInReg B)
                        (s : LocState FS) (ml : Maybe (ValueLocation FS))
                      → pure-sigop-out-aux si s (just fitB) ml
                        ≡ pure-sigop-out-val si fitB (just tt)
  pure-sigop-out-unit si fitB s (just l) = refl
  pure-sigop-out-unit si fitB s nothing  = refl

  pure-sigop-value-correct :
      ∀ {A B} (si : SigOpInfo A B) (fitness : FitsInReg B) (rA : Readable A)
      → effect si ≡ Pure
      → ∀ {mIn} (x : ⟦ ⌊ A ⌋ ⟧) (input-loc : ValueLocation FS)
          (s : LocState FS) (alloc : AllocState {FS})
      → ValidAtWF mIn alloc x input-loc s
      → halted s ≡ false
      → InputAt x input-loc s
      → readReg (regs (forced (floc (flat-run 2 (SigOp si) s alloc)))) Output
          ≡ prim-sv (fits-erase fitness) (eval (SigOp si) x)
  pure-sigop-value-correct si fits-intˢ rA pure-eq x input-loc s alloc valid nh (in-reg fit rdi-eq) =
    pure-sigop-value-reg si fits-intˢ rA pure-eq x s alloc fit rdi-eq nh
  pure-sigop-value-correct si fits-floatˢ rA pure-eq x input-loc s alloc valid nh (in-reg fit rdi-eq) =
    pure-sigop-value-reg si fits-floatˢ rA pure-eq x s alloc fit rdi-eq nh
  pure-sigop-value-correct si fits-intˢ rA pure-eq x input-loc s alloc valid nh (in-loc rdi-eq)
    rewrite nh | sigop-halts-false si pure-eq s =
    trans (cong (λ e → exec-sigop-output-of e si s) pure-eq) step2
    where
      step2 : exec-sigop-output-of Pure si s ≡ prim-sv fits-int (eval (SigOp si) x)
      step2 rewrite sv-loc-of s input-loc rdi-eq | readTyped-adequate rA valid = refl
  pure-sigop-value-correct si fits-floatˢ rA pure-eq x input-loc s alloc valid nh (in-loc rdi-eq)
    rewrite nh | sigop-halts-false si pure-eq s =
    trans (cong (λ e → exec-sigop-output-of e si s) pure-eq) step2
    where
      step2 : exec-sigop-output-of Pure si s ≡ prim-sv fits-float (eval (SigOp si) x)
      step2 rewrite sv-loc-of s input-loc rdi-eq | readTyped-adequate rA valid = refl
  -- D074: the unit-input route. `r-unit` pins `A ≡ Unitˢ`, so `⌊A⌋ ≡ Unit`
  -- holds by `refl` and the other two readable shapes refute the equality.
  pure-sigop-value-correct si fits-intˢ r-unit pure-eq x input-loc s alloc valid nh (in-unit refl)
    rewrite nh | sigop-halts-false si pure-eq s =
    trans (cong (λ e → exec-sigop-output-of e si s) pure-eq)
          (pure-sigop-out-unit si fits-intˢ s (sv-as-loc (readReg (regs s) Input1)))
  pure-sigop-value-correct si fits-floatˢ r-unit pure-eq x input-loc s alloc valid nh (in-unit refl)
    rewrite nh | sigop-halts-false si pure-eq s =
    trans (cong (λ e → exec-sigop-output-of e si s) pure-eq)
          (pure-sigop-out-unit si fits-floatˢ s (sv-as-loc (readReg (regs s) Input1)))
  pure-sigop-value-correct si fitness r-int        pure-eq x input-loc s alloc valid nh (in-unit ())
  pure-sigop-value-correct si fitness (r-pair _ _) pure-eq x input-loc s alloc valid nh (in-unit ())

  pure-obs-correct-sigop :
    ∀ {A B} (si : SigOpInfo A B) (fitness : FitsInReg B) (rA : Readable A)
    → effect si ≡ Pure → IRObsCorrectF (SigOp si)
  pure-obs-correct-sigop {A} {B} si fitness rA pure-eq
    _ mIn x input-loc s alloc _ valid input-before not-halted rdi-eq =
    record
      { traces-agree = λ k →
          2 , trans (cong (take k) (mach-[] 2))
                    (cong (take k) (sym (denot-[] k)))
      ; value-realized =
          2 , Stack , falloc (flat-run 2 (SigOp si) s alloc) ,
          at-reg input-loc (fits-erase fitness) before
            (pure-sigop-value-correct si fitness rA pure-eq x input-loc s alloc valid not-halted rdi-eq) before
      }
    where
      -- Machine side: no fetchable instr emits an event (the sole
      -- instruction `instr-sigop si` is `Pure`), so the whole trace is `[]`.
      ev-[] : ∀ pc i → fetch (ir-to-trace (SigOp si)) pc ≡ just i
            → ∀ fs → event-of i fs ≡ []
      ev-[] zero    .(instr-sigop si) refl fs rewrite pure-eq = refl
      ev-[] (suc n) i                 ()   fs

      mach-[] : ∀ f → flat-events f (ir-to-trace (SigOp si)) (mkFlat s alloc 0) ≡ []
      mach-[] f = flat-events-[] (ir-to-trace (SigOp si)) ev-[] f (mkFlat s alloc 0)

      -- Denotation side: a `Pure` SigOp emits nothing (`emit-D … ≡ []`).
      denot-[] : ∀ k → projTrace (evalᴰ (SigOp si) (inject x)) k ≡ []
      denot-[] k rewrite pure-eq = refl

      -- The single `instr-sigop` step leaves the allocator untouched.
      keeps-alloc : falloc (flat-run 2 (SigOp si) s alloc) ≡ alloc
      keeps-alloc rewrite not-halted | pure-eq = refl

      before : BeforeFrontier (falloc (flat-run 2 (SigOp si) s alloc)) input-loc
      before rewrite keeps-alloc = input-before

  -- The SigOp cases the Pure discharge does NOT cover, named separately (Plan
  -- 0.68 step 0). They used to fall back into the whole-IR `obs-correct-rest`,
  -- which meant an EFFECTFUL SigOp — the only kind that puts anything in the
  -- observable trace at all — was assumed by the same postulate as `Para`'s
  -- missing codegen. Split out so the effectful case has its own row.
  postulate
    obs-correct-sigop-rest : ∀ {A B} (si : SigOpInfo A B) → IRObsCorrectF (SigOp si)

  obs-correct-sigop : ∀ {A B} (si : SigOpInfo A B) → IRObsCorrectF (SigOp si)
  -- Route on BOTH the codomain (register-resident result) and the domain
  -- (readable input ⇒ the machine can materialise it and apply `semM`). A Pure
  -- SigOp over a non-readable input keeps the sentinel, so it makes no value
  -- claim and falls back to `obs-correct-sigop-rest`. Arith is always readable.
  obs-correct-sigop {A} {B} si with fits-in-reg? B | readable? A
  ... | nothing      | _       = obs-correct-sigop-rest si
  ... | just fitness | nothing = obs-correct-sigop-rest si
  ... | just fitness | just rA with effect si in pure-eq
  ...   | Pure    = pure-obs-correct-sigop si fitness rA pure-eq
  ...   | Emits _ = obs-correct-sigop-rest si
  ...   | Halts _ = obs-correct-sigop-rest si

  -- ════════════════════════════════════════════════════════════════════
  -- `comp-obs-correct` — the COMPOSITION case, CARVED from `obs-correct-rest`
  -- top-down (Plan 0.54 rung A). `ir-to-trace (g ∘ f) = ft ++ mov-to-input ∷ gt`:
  -- run `f` (result in `Output`), `mov-to-input` (`Input1 := Output`), run `g`.
  -- So the discharge COMPOSES the sub-witnesses — making them load-bearing:
  --   * `traces-agree (g ∘ f)` = `traces-agree f` ++ (mov, no event) ++
  --     `traces-agree g` with `g`'s input `= f`'s result. The value threading
  --     `Output → Input1` is supplied by **`f`'s `value-realized`** — this is
  --     exactly why the value lemmas support trace correctness.
  --   * `value-realized (g ∘ f)` rides `g`'s `value-realized`.
  -- Currently a NAMED obligation taking the two IHs (recurses, unlike the flat
  -- `obs-correct-rest` postulate); its body decomposes into the state-threading
  -- + `flat-events`-`++` supporting lemmas (next).
  -- ════════════════════════════════════════════════════════════════════
  -- The two named supporting obligations the composition discharge DECOMPOSES
  -- into (top-down; each is a real lemma, not the flat `obs-correct-rest`):
  -- Sub-term size bounds — PROVED (were named obligations). `ir-size (g ∘ f)`
  -- is `1 + ir-size g + ir-size f`, so each sub-term is under the bound.
  comp-size-f : ∀ {A B C} {g : IR B C} {f : IR A B}
              → ir-size (g ∘ f) < program-bound → ir-size f < program-bound
  comp-size-f {g = g} {f} sz =
    ≤-<-trans (≤-trans (m≤n+m (ir-size f) (ir-size g)) (n≤1+n _)) sz

  comp-size-g : ∀ {A B C} {g : IR B C} {f : IR A B}
              → ir-size (g ∘ f) < program-bound → ir-size g < program-bound
  comp-size-g {g = g} {f} sz =
    ≤-<-trans (≤-trans (m≤m+n (ir-size g) (ir-size f)) (n≤1+n _)) sz

  -- THE composition step. `ir-to-trace (g ∘ f) = ft ++ mov-to-input ∷ gt`: run
  -- `f` (result in `Output`), `mov-to-input` (`Input1 := Output`), run `g`.
  --
  -- Its discharge needs FOUR pieces (all machinery identified, none yet written):
  --  (1) machine split — run `ft`, the mov, then `gt` AT A PC OFFSET. Template:
  --      `ComposeWF.exec-trace-compose-eq` (the structured machine's compose
  --      equation; an island pending M2 — D141);
  --      relocation: was `CataAtRelocate` (deleted, D132).
  --  (2) event split — `flat-events` over the concatenation, the mov emitting
  --      nothing: `flat-events-steps`, `chain-events-++`, `chain-events-subst*`,
  --      `flat-events-settled`, `flat-events-reify` (Adequacy/FlatEvents).
  --  (3) denotational split — `evalᴰ (g ∘ f) a = evalᴰ f a >>=T evalᴰ g`
  --      (DenotTrace:121) is a TRACE-MONAD BIND, so `projTrace … k` splits into
  --      the two prefixes. (`eval (g ∘ f) x = eval g (eval f x)`, Eval:59.)
  --  (4) `g`'s PRECONDITION at the post-mov state — and this is decided by `f`'s
  --      RESIDENCE, which is why `value-realized` is a `ResultPlace`:
  --        * `at-loc`      — `Output ≡ SV-Ptr loc`, so after the mov
  --                          `Input1 ≡ SV-Ptr loc`: precondition MET AS-IS.
  --        * `unit-result` — `Unit` erased; nothing to thread.
  --        * `at-reg`      — `Output ≡ prim-sv fit v`, so `Input1` holds an
  --                          `SV-Lit`, NOT a pointer: `g`'s precondition as
  --                          stated CANNOT be met. THIS is what forces the
  --                          Place-aware INPUT precondition (the input-side
  --                          mirror of `at-reg`), and it is the case a
  --                          primitive-returning (arith) `f` takes — so it is
  --                          the load-bearing one for rung A.
  --      Let the discharge dictate that generalisation; do not guess it here.
  --
  -- Kept as ONE obligation deliberately: (1)-(3) are COMMON to all three
  -- residences, so splitting per-residence would duplicate the hard part while
  -- tripling the postulate count. Only (4) differs, and it is a spec change.
  postulate
    comp-step : ∀ {A B C} {g : IR B C} {f : IR A B} {x : ⟦ A ⟧} {s alloc}
              → ir-size g < program-bound
              → IRObsCorrectF g → MachineRefinesObsF f x s alloc
              → MachineRefinesObsF (g ∘ f) x s alloc

  comp-obs-correct : ∀ {A B C} {g : IR B C} {f : IR A B}
                   → IRObsCorrectF g → IRObsCorrectF f → IRObsCorrectF (g ∘ f)
  comp-obs-correct {g = g} {f} ihg ihf sz mIn x il s alloc ns valid before nh rdi =
    comp-step (comp-size-g {g = g} {f} sz) ihg
      (ihf (comp-size-f {g = g} {f} sz) mIn x il s alloc ns valid before nh rdi)

  -- TOTAL, and now with NO CATCH-ALL (Plan 0.68 step 0). Every constructor has
  -- its own clause and its own named obligation, in `Once.IR`'s order — so a
  -- constructor that is added, removed or renamed is a TYPE ERROR here rather
  -- than a silent variable pattern absorbing it (the retired-ctor trap).
  ir-obs-correct : ∀ {A B} (ir : IR A B) → IRObsCorrectF ir
  -- category structure
  ir-obs-correct id                  = obs-correct-id
  ir-obs-correct (g ∘ f)             = comp-obs-correct (ir-obs-correct g) (ir-obs-correct f)
  -- products
  ir-obs-correct (⟨ f , g ⟩ m)       = obs-correct-pair f g m
  ir-obs-correct fst                 = obs-correct-fst
  ir-obs-correct snd                 = obs-correct-snd
  -- sums
  ir-obs-correct (inl m)             = obs-correct-inl m
  ir-obs-correct (inr m)             = obs-correct-inr m
  ir-obs-correct (case f g)          = obs-correct-case f g
  -- terminal / initial
  ir-obs-correct terminal            = obs-correct-terminal
  ir-obs-correct initial             = obs-correct-initial
  -- exponentials — THE LABEL-BEARING PAIR
  ir-obs-correct (curry body m)      = obs-correct-curry body m
  ir-obs-correct apply               = obs-correct-apply
  -- μ / ν structure
  ir-obs-correct (In wf m)           = obs-correct-In wf m
  ir-obs-correct (out-μ wf)          = obs-correct-out-μ wf
  ir-obs-correct (Cata wf alg)       = cata-correct wf alg (ir-obs-correct alg)
  ir-obs-correct (Para wf f)         = obs-correct-Para wf f
  ir-obs-correct (Out wf)            = obs-correct-Out wf
  ir-obs-correct (in-ν wf m)         = obs-correct-in-ν wf m
  ir-obs-correct (Ana wf f)          = obs-correct-Ana wf f
  ir-obs-correct (Hylo wfF wfG a nt) = obs-correct-Hylo wfF wfG a nt
  ir-obs-correct (Fuse wfF wfG a nt) = obs-correct-Fuse wfF wfG a nt
  -- misc
  ir-obs-correct (free-heap r)       = obs-correct-free-heap r
  ir-obs-correct (const fit v)       = obs-correct-const fit v
  ir-obs-correct (SigOp si)          = obs-correct-sigop si
