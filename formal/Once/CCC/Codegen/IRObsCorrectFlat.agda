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

open import Data.Nat using (ℕ; zero; suc; _<_; _≤_; _+_)
open import Data.Bool using (false; true)
open import Data.List using (length; take; []; _∷_; _++_; map)
open import Data.List.Properties using (++-assoc; length-++)
open import Data.Maybe using (Maybe; just; nothing) renaming (map to mmap)
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
open import Relation.Binary.PropositionalEquality using (refl; sym; trans; cong; subst; subst₂)
open import Once.IR.Size using (ir-size)
open import Data.Nat.Properties using (≤-<-trans; ≤-trans; ≤-reflexive; m≤m+n; m≤n+m; n≤1+n; +-identityʳ; +-assoc; +-suc; +-comm)
open import Function using (case_of_)
import Once.CCC.Eval as Ev
import Once.Semantics.Machine as EvV
open import Once.CCC.Machine.SMCore
  using (LocState; ValueLocation; SV-Ptr; sv-as-loc; halted; regs; readReg; Input1; Output;
         instr-sigop; mov-to-output; mov-to-input; instr-load-const; SV-Lit; writeReg; writeReg-same; AbstractTrace;
         -- D155: the closure register's type — the entry state's one open
         -- component (see `entry-flat`).
         StoredValue; AbstractInstr; module AbstractExec; module MemOps;
         -- D171: the store instruction and the location vocabulary its
         -- read-back needs.
         store-at-slot; AtStack; current-frame)
open import Once.CCC.Machine.Validity using (module ValidityDef)
open import Once.CCC.Machine.ValidAtWFHalted o using (validAtWF-set-halted)
open import Once.CCC.Machine.Allocation using (AllocState; next-slot; module FrontierInvariant)
open import Once.CCC.Machine.Flat using (module FlatMachine)
open import Once.CCC.Codegen.FlatStepLemmas using (module FlatStepsAPI)
open import Once.CCC.Codegen.IRToTrace o using (ir-to-trace; ir-to-trace')
open import Once.CCC.Codegen.CataNextSlot using (module CataNextSlot)
open import Once.CCC.Codegen.SlotBudget o using (frontier-mono; budget-of)
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
  open FlatStepsAPI {FS} using (FlatSteps; []; _∷_; exec-flat-steps; FlatSteps-++; FlatSteps-prefix; FlatSteps-reloc)
  open AbstractExec {FS} using (exec-abstract; exec-sigop-halts; exec-sigop-halts-of; exec-sigop-output-of; pure-sigop-output; pure-sigop-out-aux; pure-sigop-out-val; readTyped; readReg-typed)
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
  open FlatEventTrace {FS} using (flat-events; event-of; flat-events-[]; chain-events; chain-events-nil)
  open RTA o {FS} program-bound using (Readable; r-unit; r-int; r-pair; readable?; readTyped-adequate)
  open CataNextSlot {FS} using (exec-flat-keeps-next-slot; AllSlotStable)
  open CataIRSlotStable {FS} using (ir-to-trace-slot-stable; ir-stable)

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

  -- D152: the trace the compiler ACTUALLY emits for `ir` at emission site
  -- `(n , l)`. (`IRToTrace.proj-trace` is `private`, so the projection is
  -- restated rather than that module's interface widened.)
  emitted : ∀ {A B} → ℕ → ℕ → IR A B → AbstractTrace
  emitted n l ir = proj₁ (proj₂ (proj₂ (ir-to-trace' n l ir)))

  -- D155: THE ENTRY STATE, NAMED — and with the closure register open.
  --
  -- A composition hands `g` the state `f`'s run left behind, and `Shifted`
  -- (plan 0.88 A) names SIX components of a flat state. Four of them are the
  -- same at an entry and at a clean hand-over (`fpc ≡ 0`, `fret ≡ []`,
  -- `flink ≡ nothing`, and `floc`/`falloc` are what is handed over). The
  -- remaining one is `fclosure`, which `mkFlat` hardwires to the entry filler
  -- and which `instr-save-closure-reg` legitimately changes — so an interface
  -- entered only at `mkFlat` cannot RECEIVE a hand-over at all. `cl` is that
  -- component, quantified rather than fixed; `entry-flat s alloc (SV-Tag 0)`
  -- IS `mkFlat s alloc 0`, so the entry instance is unchanged.
  entry-flat : ℕ → LocState FS → AllocState {FS} → StoredValue FS → FlatState
  entry-flat base s alloc cl = mkFlatFull s alloc base [] cl nothing

  -- D158: THE FRAGMENT'S PLACEMENT, as a hypothesis rather than an identity.
  --
  -- `emitted n l ir` is what the emitter produces for `ir`; `SpanAt prog base`
  -- says that text occurs in `prog` starting at `base`. Stated as fetch
  -- agreement — the weakest form, and the only thing a run ever asks of a
  -- program. Every witness below is universally quantified over `prog` and
  -- `base`, which IS the position-independence a relocation lemma was trying
  -- to prove: a fragment's correctness cannot depend on where it lands,
  -- because it is asserted for every landing.
  --
  -- WHY QUANTIFY RATHER THAN RELOCATE (D158). A single shift can place a
  -- fragment, but not a fragment AND the code it calls into. `curry` emits its
  -- body at offset 7 of its own trace, so in `apply ∘ curry body` the body and
  -- `apply` sit at unrelated offsets; no `shift d` maps both. Quantifying over
  -- placement costs nothing and covers both, because each is placed on its own.
  --
  -- `k + base`, not `base + k`: at `k ≡ 0` it reduces to `base`, which is the
  -- entry state's pc, and at literal `k` it reduces to `sucᵏ base`, which is
  -- where the machine actually is after `k` straight steps. The proofs are
  -- `refl` because of that choice.
  SpanAt : AbstractTrace → ℕ → AbstractTrace → Set
  SpanAt prog base t =
    ∀ (k : ℕ) (i : AbstractInstr) → fetch t k ≡ just i → fetch prog (k + base) ≡ just i

  -- D152: the flat run of `ir` AT THE FRONTIER AND LABEL BASE IT IS EMITTED
  -- AT. It used to be hardwired to frontier 0, which is only ever true of the
  -- top-level `ir` — every sub-IR of a composite is emitted at a nonzero `n`.
  flat-run : ℕ → AbstractTrace → ℕ → LocState FS → AllocState {FS}
           → StoredValue FS → FlatState
  flat-run fuel prog base s alloc cl =
    exec-flat fuel prog (entry-flat base s alloc cl)

  -- Frame discipline (codegen-image half + machine half wired together):
  -- running any compiled IR preserves the stack-frame frontier `next-slot`.
  -- `ir-to-trace-slot-stable` (no trace touches next-slot) + `exec-flat-
  -- keeps-next-slot` (exec-flat preserves it for slot-stable traces). This
  -- is what `value-realized` needs to apply the algebra's `IRObsCorrectF`
  -- IH at every cata layer: the cata scaffold keeps `next-slot ≡ 0`, so the
  -- algebra's `next-slot alloc ≡ 0` precondition holds at each layer's run.
  flat-run-keeps-next-slot :
    ∀ (fuel : ℕ) (prog : AbstractTrace) → AllSlotStable prog
    → ∀ (base : ℕ) (s : LocState FS) (alloc : AllocState {FS}) (cl : StoredValue FS)
    → next-slot (falloc (flat-run fuel prog base s alloc cl)) ≡ next-slot alloc
  flat-run-keeps-next-slot fuel prog ss base s alloc cl =
    exec-flat-keeps-next-slot prog ss fuel (entry-flat base s alloc cl)

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
  -- D152: indexed by the frontier `n` and label base `l` the IR is EMITTED at.
  -- The correctness statement must thread whatever the emitter threads:
  -- `ir-to-trace' n l (g ∘ f)` emits `g` at `f`'s output frontier, so a
  -- sub-witness stated only at frontier 0 is about a DIFFERENT trace than the
  -- one spliced into the composite. That is what made `comp-step` unprovable
  -- and hence a postulate.
  -- D155: THE VALUE HALF, AS A HAND-OVER RATHER THAN A FUEL.
  --
  -- The old form was `∃ fuel` and read the run's state through `forced`
  -- (halted forced to `true`). It cannot compose, and the reason is not a
  -- missing lemma: at a fuel large enough to finish `ir`, the run has fallen
  -- off the end of `ir`'s own trace and `flat-halt` has set `halted := true`,
  -- so the NEXT component's `halted s ≡ false` premise is false at exactly the
  -- state the composition has to hand it. `forced` was papering over that: it
  -- made the statement insensitive to a flag the sequel depends on.
  --
  -- What composes is a STEP CHAIN to a NAMED settle state. `FlatSteps` records
  -- the instruction fetched at every step, which is what survives splicing the
  -- trace into a longer program; a fuel does not, because the same fuel in the
  -- composite keeps running into `g`. The four control fields are stated
  -- because `Shifted` asks for them: `at-end` gives the pc the sequel is
  -- relocated by, and `no-ret`/`no-link` say the run left no return pending.
  -- `fclosure` is deliberately NOT constrained — it is what `ir` hands on.
  record ValueRealized (prog : AbstractTrace) (base : ℕ)
                       {A B} (n l : ℕ) (ir : IR A B) (x : ⟦ A ⟧)
                       (s : LocState FS) (alloc : AllocState {FS})
                       (cl : StoredValue FS) : Set where
    constructor realized
    field
      steps      : ℕ
      settle     : FlatState
      out-mode   : AllocMode
      cont-alloc : AllocState {FS}
      run        : FlatSteps prog steps (entry-flat base s alloc cl) settle
      live       : halted (floc settle) ≡ false
      at-end     : fpc settle ≡ length (emitted n l ir) + base
      no-ret     : fret settle ≡ []
      no-link    : flink settle ≡ nothing
      place      : ResultPlace B out-mode (falloc settle) cont-alloc
                     (eval ir x) (floc settle)

  record MachineRefinesObsF (prog : AbstractTrace) (base : ℕ)
                             {A B} (n l : ℕ) (ir : IR A B) (x : ⟦ A ⟧)
                             (s : LocState FS) (alloc : AllocState {FS})
                             (cl : StoredValue FS) : Set where
    field
      -- NO completion fields (M3, D058: "productivity — not termination").
      -- `run-halts` ("the run halts") is exactly what excludes `Ana`; instead,
      -- the machine REFINES the denotational `evalᴰ` at each observation depth
      -- `k` PRODUCTIVELY: there EXISTS a fuel `f` that emits the first `k`
      -- effectful events, matching `evalᴰ`'s depth-`k` event-prefix. The `∃ f`
      -- is the productivity witness, never the observable index (which is `k`).
      -- (Cata emits a full finite trace; Ana grows with depth — both composed
      -- correctly in `evalᴰ`, observed by the `take k` event-prefix.)
      -- D158/D159: the value half comes FIRST, because the trace half is
      -- stated along ITS chain.
      value-realized : ValueRealized prog base n l ir x s alloc cl
      -- …and the trace half, BOUNDED BY THAT CHAIN rather than by a fuel.
      --
      -- The old form was `∀ k → ∃ f` over `flat-events f (emitted n l ir)` —
      -- the fragment run as if it were the whole program. Once the witness is
      -- program-indexed (D158) that is wrong in a way a fuel cannot fix: a run
      -- inside a program that CONTINUES past the fragment collects the
      -- successor's events too, so `take k` of the machine stream would have to
      -- equal `take k` of a denotation that stops. The events belonging to
      -- `ir` are exactly the events along `ir`'s own step chain.
      --
      -- What this gives up is the `∃ f` productivity witness (D058:
      -- "productivity — not termination"). That costs nothing TODAY: `Ana`,
      -- `Hylo`, `Fuse` and `Para` all emit `[]`, so no non-terminating code is
      -- emitted at all and the ∃ was vacuous. It becomes real again when `Ana`
      -- gets an emitter, which CLASS G already records as codegen work rather
      -- than proof work.
      traces-agree :
        ∀ (k : ℕ) →
          take k (chain-events (ValueRealized.run value-realized))
            ≡ take k (projTrace (evalᴰ ir (inject x)) k)
      -- The value device: "the value the next effectful SigOp reads is right".
      -- Plan 0.54 rung A: a `ResultPlace` (register `at-reg` OR memory `at-loc`),
      -- NOT bare `ValidAtWF` at a memory loc — a Pure primitive result is
      -- register-resident (`Output`), so the memory-only form could not capture
      -- it. This is the `Place` split (register-allocation both-residences); the
      -- register count per arch is rung B. Final-value form (its own fuel `f`).

  -- The INPUT's residence — the input-side mirror of `ResultPlace`. `Input1`
  -- either POINTS at the value in memory (`in-loc`, the spill path) or HOLDS it
  -- directly as a register literal (`in-reg`, the fast path). Forced top-down by
  -- `comp-step`: `emitted n l (g ∘ f) = ft ++ mov-to-input ∷ gt`, so after a
  -- primitive-returning `f` the mov leaves `Input1` holding an `SV-Lit` — a
  -- pointer-only precondition could never be met, and `g`'s IH could not be
  -- applied at all. Generalising a PRECONDITION strengthens the obligation (it
  -- must now hold in more situations); the apex statement is untouched.
  -- D153: the input's residence AND ITS EVIDENCE, together.
  --
  -- `in-reg` was already here, added (per the note below) because "a
  -- pointer-only precondition could never be met, and `g`'s IH could not be
  -- applied at all". But `IRObsCorrectF` kept a separate
  -- `ValidAtWF mIn alloc x input-loc s` premise beside it — memory-residency
  -- evidence at a location — which re-imposed exactly the requirement `in-reg`
  -- was added to lift. `valid-int-wf` needs `readLoc s loc ≡ just (prim-sv …)`,
  -- a MEMORY read, and a register-resident value has no such `loc`. So the
  -- register case could still never be instantiated, and `comp-step` was
  -- unprovable in precisely the case its own piece (4) calls load-bearing.
  --
  -- Half a fix is no fix: residence and evidence must travel in ONE premise, so
  -- that choosing `in-reg` DISCHARGES the memory obligation rather than leaving
  -- it to be supplied separately.
  data InputAt {A : IRTy} (mIn : AllocMode) (alloc : AllocState {FS})
               (v : ⟦ A ⟧) (s : LocState FS) : Set where
    in-loc : (loc : ValueLocation FS)
           → ValidAtWF mIn alloc v loc s
           → BeforeFrontier alloc loc
           → readReg (regs s) Input1 ≡ SV-Ptr loc → InputAt mIn alloc v s
    in-reg : (fit : FitsInRegI A) → readReg (regs s) Input1 ≡ prim-sv fit v
           → InputAt mIn alloc v s
    -- D074: a UNIT input has no residence at all — `Input1` may hold anything
    -- (the entry state's tag filler; after `f : IR A Unit` in a composition,
    -- `f`'s unit output is likewise unconstrained, so a residence premise
    -- would make `comp-step`'s IH inapplicable). The machine never reads a
    -- unit input: `readTyped Unit` and `readReg-typed Unit` both materialise
    -- `tt` regardless of what is there.
    in-unit : A ≡ Unit → InputAt mIn alloc v s

  -- Same preconditions as `compile-correct-flat`'s semantic side (entry
  -- frontier 0), minus `StraightIR` (loops are allowed); conclusion is
  -- the flat refinement.
  IRObsCorrectF : ∀ {A B} → IR A B → Set
  IRObsCorrectF {A} {B} ir =
    ir-size ir < program-bound →
    -- D152: quantified over the EMISSION SITE `(n , l)`, and the runtime
    -- frontier is `n` rather than 0. `n = l = 0` is the entry instance, which
    -- is all `ir-flat-correct-of` ever uses.
    ∀ (n l : ℕ)
      -- D158: ∀ PLACEMENT. `prog` is the program the fragment is part of and
      -- `base` where its own text begins; `SpanAt` is the only thing tying
      -- them together, and `AllSlotStable prog` is what `next-slot`
      -- preservation needs once the run is no longer confined to `emitted`.
      (prog : AbstractTrace) (base : ℕ) →
      AllSlotStable prog →
      SpanAt prog base (emitted n l ir) →
    ∀ (mIn : AllocMode) (x : ⟦ A ⟧)
      (s : LocState FS) (alloc : AllocState {FS}) (cl : StoredValue FS) →
    -- D155: `≤`, not `≡`. What this premise is FOR is that the emitter's
    -- scratch region `[n , …)` is above anything the caller has live —
    -- `BeforeFrontier` bounds live data by `next-slot alloc`. Stated as an
    -- EQUATION it says more than that, and D150 showed the extra content is
    -- false: `next-slot` never moves at run time, while the emission frontier
    -- advances through the program, so `next-slot alloc ≡ n` can hold at ONE
    -- emission site and nowhere after it. In `g ∘ f` the second component is
    -- always emitted at `n1 ≥ n`, so the equation made `comp-value-realized`'s
    -- own induction hypothesis inapplicable (D154). No discharged shape ever
    -- used it — every one of them takes this argument as `_` — so nothing is
    -- weakened by asking only for what the invariant means.
    next-slot alloc ≤ n →
    halted s ≡ false →
    -- D153: ONE residence premise, carrying its own evidence. The separate
    -- `input-loc` / `ValidAtWF` / `BeforeFrontier` triple is gone — it made
    -- the `in-reg` case unusable.
    InputAt mIn alloc x s →
    MachineRefinesObsF prog base n l ir x s alloc cl

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
  obs-correct-id {A} _ n l prog base _ span mIn x s alloc cl _ nh rdi-eq =
    record
      { traces-agree = λ k → cong (take k) (sym (denot-[] k))
      ; value-realized =
          realized 1 fs₁ mIn (falloc fs₁) ((nh , span 0 _ refl) ∷ []) nh refl refl refl
                   (place rdi-eq)
      }
    where
      -- The post-`mov` register file and the intermediate flat state. `run-eq`
      -- is derived from the two step lemmas rather than by `rewrite nh`: the
      -- second step's `halted` test is not a syntactic occurrence in the goal.
      regs' = writeReg (regs s) Output (readReg (regs s) Input1)
      fs₁   = flat-exec-instr mov-to-output prog (entry-flat base s alloc cl)


      -- Machine side: the only fetchable instruction is `mov-to-output`, which
      -- emits nothing.
      ev-[] : ∀ pc i → fetch (emitted n l (id {A})) pc ≡ just i → ∀ fs → event-of i fs ≡ []
      ev-[] zero    .mov-to-output refl fs = refl
      ev-[] (suc n) i              ()   fs

      mach-[] : ∀ f → flat-events f (emitted n l (id {A})) (entry-flat 0 s alloc cl) ≡ []
      mach-[] f = flat-events-[] (emitted n l (id {A})) ev-[] f (entry-flat 0 s alloc cl)

      -- Denotation side: `evalᴰ id a = returnT a` emits nothing.
      denot-[] : ∀ k → projTrace (evalᴰ (id {A}) (inject x)) k ≡ []
      denot-[] k = refl

      keeps-alloc : falloc fs₁ ≡ alloc
      keeps-alloc = refl

      -- A register write is invisible to `readLoc` (there is no register
      -- `ValueLocation`), and so is the halt flag.
      mem-eq : ∀ loc' → readLoc (floc fs₁) loc' ≡ readLoc s loc'
      mem-eq loc' = reg-write-readLoc s regs' (halted s) loc'

      -- D153: the located case's evidence now arrives WITH the residence, so
      -- these are parameterised by it instead of reading it off the clause head.
      valid' : ∀ (il : ValueLocation FS) → BeforeFrontier alloc il
             → ValidAtWF mIn alloc x il s
             → ValidAtWF mIn alloc x il (floc fs₁)
      valid' il bf v = validityWF-mem-preserved x il s _ bf (λ loc' _ → mem-eq loc') v

      out-ptr : ∀ (il : ValueLocation FS) → readReg (regs s) Input1 ≡ SV-Ptr il
              → readReg (regs (floc fs₁)) Output ≡ SV-Ptr il
      out-ptr il eq =
        trans (writeReg-same (regs s) Output (readReg (regs s) Input1)) eq

      out-lit : ∀ (fit : FitsInRegI A) → readReg (regs s) Input1 ≡ prim-sv fit x
              → readReg (regs (floc fs₁)) Output ≡ prim-sv fit x
      out-lit fit eq =
        trans (writeReg-same (regs s) Output (readReg (regs s) Input1)) eq

      before' : ∀ (il : ValueLocation FS) → BeforeFrontier alloc il
              → BeforeFrontier (falloc fs₁) il
      before' il bf = bf

      place : InputAt mIn alloc x s
            → ResultPlace A mIn (falloc fs₁)
                (falloc fs₁) (eval (id {A}) x)
                (floc fs₁)
      place (in-loc il v bf eq) =
        at-loc il (valid'' il bf v) (before' il bf) (out-ptr il eq)
                  (valid'' il bf v) (before' il bf)
        where valid'' : ∀ il' → BeforeFrontier alloc il' → ValidAtWF mIn alloc x il' s
                      → ValidAtWF mIn (falloc fs₁) x il'
                          (floc fs₁)
              valid'' il' bf' v' =
                subst (λ a → ValidAtWF mIn a x il'
                               (floc fs₁))
                      (sym keeps-alloc) (valid' il' bf' v')
      place (in-reg fit eq)  = at-reg fit (out-lit fit eq)
      place (in-unit refl)   = unit-result

  -- ── `terminal` — DISCHARGED. The emitter emits NOTHING for it
  -- (`ir-to-trace terminal = []`), which is right: the codomain is `Unit`, the
  -- erased type, so there is no value to place and no event to emit. `fetch []`
  -- is `nothing` at every pc, so both `ev-[]` clauses are absurd, and the
  -- result place is `unit-result` — which asserts nothing about the state,
  -- exactly because a unit result has no residence (D074).
  obs-correct-terminal : ∀ {A} → IRObsCorrectF (terminal {A})
  obs-correct-terminal {A} _ n l prog base _ span mIn x s alloc cl _ nh rdi-eq =
    record
      { traces-agree = λ k → cong (take k) (sym (denot-[] k))
      ; value-realized =
          realized 0 (entry-flat base s alloc cl) mIn alloc [] nh refl refl refl unit-result
      }
    where
      ev-[] : ∀ pc i → fetch (emitted n l (terminal {A})) pc ≡ just i → ∀ fs → event-of i fs ≡ []
      ev-[] zero    i () fs
      ev-[] (suc n) i () fs

      mach-[] : ∀ f → flat-events f (emitted n l (terminal {A})) (entry-flat 0 s alloc cl) ≡ []
      mach-[] f = flat-events-[] (emitted n l (terminal {A})) ev-[] f (entry-flat 0 s alloc cl)

      denot-[] : ∀ k → projTrace (evalᴰ (terminal {A}) (inject x)) k ≡ []
      denot-[] k = refl

  -- ── `initial` — DISCHARGED, VACUOUSLY, and that is the honest reading.
  -- `initial : IR Void A` and `⟦ Void ⟧ᴵ` is `⊥`, so there is no input to run
  -- on. The denotation agrees: `evalᴰ initial ()` is itself defined by an
  -- absurd pattern. The emitter's `mov-to-output` is never reached because the
  -- state it would run from cannot exist.
  obs-correct-initial : ∀ {A} → IRObsCorrectF (initial {A})
  obs-correct-initial _ n l prog base _ span mIn ()

  -- ── `free-heap` — DISCHARGED. `IR Unit Unit`, a semantic no-op that still
  -- compiles to `mov-to-output ∷ []` (copy through, so the register discipline
  -- holds). Unit codomain ⇒ `unit-result`; no event on either side.
  -- D171 / Phase E2: THE FLAT LAYER'S READ-BACK FOR A STORE.
  --
  -- Every discharged `obs-correct-*` clause so far touches at most
  -- `mov-to-output`; NONE handles `store-at-slot`. That — not four separate
  -- difficulties — is why `obs-correct-{pair,inl,inr,curry}` are all still
  -- axioms: they share one missing foundation, the flat layer's store/read
  -- vocabulary. The `LocState` half already exists (`SMCore`'s
  -- `writeLoc-read-same-stack` and its disjoint-location sibling); what was
  -- missing is the bridge from `flat-exec-instr` to `writeLoc`, and
  -- `store-at-slot` goes through `flat-step-straight`, so it is definitional.
  flat-store-floc : ∀ (slot : ℕ) (prog : AbstractTrace) (fs : FlatState)
    → floc (flat-exec-instr (store-at-slot slot) prog fs)
      ≡ MemOps.writeLoc (floc fs) (AtStack (current-frame (falloc fs)) slot)
                 (readReg (regs (floc fs)) Output)
  flat-store-floc slot prog fs = refl

  flat-store-falloc : ∀ (slot : ℕ) (prog : AbstractTrace) (fs : FlatState)
    → falloc (flat-exec-instr (store-at-slot slot) prog fs) ≡ falloc fs
  flat-store-falloc slot prog fs = refl

  flat-store-fpc : ∀ (slot : ℕ) (prog : AbstractTrace) (fs : FlatState)
    → fpc (flat-exec-instr (store-at-slot slot) prog fs) ≡ suc (fpc fs)
  flat-store-fpc slot prog fs = refl

  -- D170 / Phase E2 probe: the DENOTATION half of `obs-correct-curry`.
  -- `curry` builds a value; it invokes no SigOp, so its trace is empty at every
  -- depth. Named here because it is one of the two halves the discharge needs,
  -- and because it is `refl` — which is the evidence that the clause is
  -- Class-B shaped rather than label-bearing.
  curry-denot-[] : ∀ {A B C} (body : IR (A * B) C) (m : AllocMode)
                   {x : ⟦ A ⟧} (k : ℕ)
                 → projTrace (evalᴰ (curry body) (inject x)) k ≡ []
  curry-denot-[] body m k = refl

  obs-correct-free-heap : ∀ (r : HeapRef) → IRObsCorrectF (free-heap r)
  obs-correct-free-heap r _ n l prog base _ span mIn x s alloc cl _ nh rdi-eq =    record
      { traces-agree = λ k → cong (take k) (sym (denot-[] k))
      ; value-realized =
          realized 1 fs₁ mIn (falloc fs₁) ((nh , span 0 _ refl) ∷ []) nh refl refl refl unit-result
      }
    where
      fs₁ = flat-exec-instr mov-to-output prog (entry-flat base s alloc cl)

      ev-[] : ∀ pc i → fetch (emitted n l (free-heap r)) pc ≡ just i → ∀ fs → event-of i fs ≡ []
      ev-[] zero    .mov-to-output refl fs = refl
      ev-[] (suc n) i              ()   fs

      mach-[] : ∀ f → flat-events f (emitted n l (free-heap r)) (entry-flat 0 s alloc cl) ≡ []
      mach-[] f = flat-events-[] (emitted n l (free-heap r)) ev-[] f (entry-flat 0 s alloc cl)

      denot-[] : ∀ k → projTrace (evalᴰ (free-heap r) (inject x)) k ≡ []
      denot-[] k = refl

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
  obs-correct-out-μ {F} wf _ n l prog base _ span mIn x s alloc cl _ nh rdi-eq =    record
      { traces-agree = λ k → cong (take k) (sym (denot-[] k))
      ; value-realized =
          realized 1 fs₁ mIn (falloc fs₁) ((nh , span 0 _ refl) ∷ []) nh refl refl refl
                   (place rdi-eq)
      }
    where
      regs' = writeReg (regs s) Output (readReg (regs s) Input1)
      fs₁   = flat-exec-instr mov-to-output prog (entry-flat base s alloc cl)


      ev-[] : ∀ pc i → fetch (emitted n l (out-μ wf)) pc ≡ just i → ∀ fs → event-of i fs ≡ []
      ev-[] zero    .mov-to-output refl fs = refl
      ev-[] (suc n) i              ()   fs

      mach-[] : ∀ f → flat-events f (emitted n l (out-μ wf)) (entry-flat 0 s alloc cl) ≡ []
      mach-[] f = flat-events-[] (emitted n l (out-μ wf)) ev-[] f (entry-flat 0 s alloc cl)

      denot-[] : ∀ k → projTrace (evalᴰ (out-μ wf) (inject x)) k ≡ []
      denot-[] k = refl

      keeps-alloc : falloc fs₁ ≡ alloc
      keeps-alloc = refl

      mem-eq : ∀ loc' → readLoc (floc fs₁) loc' ≡ readLoc s loc'
      mem-eq loc' = reg-write-readLoc s regs' (halted s) loc'

      valid' : ∀ (il : ValueLocation FS) → BeforeFrontier alloc il
             → ValidAtWF mIn alloc x il s
             → ValidAtWF mIn alloc x il (floc fs₁)
      valid' il bf v = validityWF-mem-preserved x il s _ bf (λ loc' _ → mem-eq loc') v

      valid'' : ∀ (il : ValueLocation FS) → BeforeFrontier alloc il
              → ValidAtWF mIn alloc x il s
              → ValidAtWF mIn (falloc fs₁)
                  (eval (out-μ wf) x) il
                  (floc fs₁)
      valid'' il bf v = subst (λ a → ValidAtWF mIn a (eval (out-μ wf) x) il
                               (floc fs₁))
                      (sym keeps-alloc) (μ-layer-iso wf x (valid' il bf v))

      out-ptr : ∀ (il : ValueLocation FS) → readReg (regs s) Input1 ≡ SV-Ptr il
              → readReg (regs (floc fs₁)) Output
                ≡ SV-Ptr il
      out-ptr il eq =
        trans (writeReg-same (regs s) Output (readReg (regs s) Input1)) eq

      before' : ∀ (il : ValueLocation FS) → BeforeFrontier alloc il
              → BeforeFrontier (falloc fs₁) il
      before' il bf = bf

      place : InputAt mIn alloc x s
            → ResultPlace (⟦ F ⟧TI (μ-type F)) mIn (falloc fs₁)
                (falloc fs₁) (eval (out-μ wf) x)
                (floc fs₁)
      place (in-loc il v bf eq) =
        at-loc il (valid'' il bf v) (before' il bf) (out-ptr il eq)
                  (valid'' il bf v) (before' il bf)
      place (in-reg () _)
      place (in-unit ())

  obs-correct-Out : ∀ {F} (wf : WellFormedFI F) → IRObsCorrectF (Out wf)
  obs-correct-Out {F} wf _ n l prog base _ span mIn x s alloc cl _ nh rdi-eq =    record
      { traces-agree = λ k → cong (take k) (sym (denot-[] k))
      ; value-realized =
          realized 1 fs₁ mIn (falloc fs₁) ((nh , span 0 _ refl) ∷ []) nh refl refl refl
                   (place rdi-eq)
      }
    where
      regs' = writeReg (regs s) Output (readReg (regs s) Input1)
      fs₁   = flat-exec-instr mov-to-output prog (entry-flat base s alloc cl)


      ev-[] : ∀ pc i → fetch (emitted n l (Out wf)) pc ≡ just i → ∀ fs → event-of i fs ≡ []
      ev-[] zero    .mov-to-output refl fs = refl
      ev-[] (suc n) i              ()   fs

      mach-[] : ∀ f → flat-events f (emitted n l (Out wf)) (entry-flat 0 s alloc cl) ≡ []
      mach-[] f = flat-events-[] (emitted n l (Out wf)) ev-[] f (entry-flat 0 s alloc cl)

      denot-[] : ∀ k → projTrace (evalᴰ (Out wf) (inject x)) k ≡ []
      denot-[] k = refl

      keeps-alloc : falloc fs₁ ≡ alloc
      keeps-alloc = refl

      mem-eq : ∀ loc' → readLoc (floc fs₁) loc' ≡ readLoc s loc'
      mem-eq loc' = reg-write-readLoc s regs' (halted s) loc'

      valid' : ∀ (il : ValueLocation FS) → BeforeFrontier alloc il
             → ValidAtWF mIn alloc x il s
             → ValidAtWF mIn alloc x il (floc fs₁)
      valid' il bf v = validityWF-mem-preserved x il s _ bf (λ loc' _ → mem-eq loc') v

      valid'' : ∀ (il : ValueLocation FS) → BeforeFrontier alloc il
              → ValidAtWF mIn alloc x il s
              → ValidAtWF mIn (falloc fs₁)
                  (eval (Out wf) x) il
                  (floc fs₁)
      valid'' il bf v = subst (λ a → ValidAtWF mIn a (eval (Out wf) x) il
                               (floc fs₁))
                      (sym keeps-alloc) (ν-layer-iso wf x (valid' il bf v))

      out-ptr : ∀ (il : ValueLocation FS) → readReg (regs s) Input1 ≡ SV-Ptr il
              → readReg (regs (floc fs₁)) Output
                ≡ SV-Ptr il
      out-ptr il eq =
        trans (writeReg-same (regs s) Output (readReg (regs s) Input1)) eq

      before' : ∀ (il : ValueLocation FS) → BeforeFrontier alloc il
              → BeforeFrontier (falloc fs₁) il
      before' il bf = bf

      place : InputAt mIn alloc x s
            → ResultPlace (⟦ F ⟧TI (ν-type F)) mIn (falloc fs₁)
                (falloc fs₁) (eval (Out wf) x)
                (floc fs₁)
      place (in-loc il v bf eq) =
        at-loc il (valid'' il bf v) (before' il bf) (out-ptr il eq)
                  (valid'' il bf v) (before' il bf)
      place (in-reg () _)
      place (in-unit ())

  -- ── `const` — DISCHARGED, and it is the first REGISTER-resident result of
  -- class A. `emitted n l (const fit v) = instr-load-const fitˢ v ∷ []`, whose
  -- `exec-abstract` writes `SV-Lit fitˢ v` to `Output` — which is exactly
  -- `prim-sv fit v`, the literal `at-reg` claims. The domain is `Unit`, so the
  -- input residence plays no part at all (nothing is read).
  --
  -- Two clauses because `prim-sv` dispatches on the `FitsInRegI` evidence; the
  -- bodies are identical.
  obs-correct-const : ∀ {A} (fit : FitsInRegI A) (v : ⟦ ℤ , Decimal ⟧-baseI A)
                    → IRObsCorrectF (const fit v)
  obs-correct-const fits-int v _ n l prog base _ span mIn x s alloc cl _ nh rdi-eq =    record
      { traces-agree = λ k → cong (take k) (sym (denot-[] k))
      ; value-realized =
          realized 1 fs₁ mIn (falloc fs₁) ((nh , span 0 _ refl) ∷ []) nh refl refl refl
                   (at-reg fits-int out-lit)
      }
    where
      instr = instr-load-const fits-intˢ v
      fs₁   = flat-exec-instr instr prog (entry-flat base s alloc cl)


      ev-[] : ∀ pc i → fetch (emitted n l (const fits-int v)) pc ≡ just i → ∀ fs → event-of i fs ≡ []
      ev-[] zero    .instr refl fs = refl
      ev-[] (suc n) i      ()   fs

      mach-[] : ∀ f → flat-events f (emitted n l (const fits-int v)) (entry-flat 0 s alloc cl) ≡ []
      mach-[] f = flat-events-[] (emitted n l (const fits-int v)) ev-[] f (entry-flat 0 s alloc cl)

      denot-[] : ∀ k → projTrace (evalᴰ (const fits-int v) (inject x)) k ≡ []
      denot-[] k = refl

      keeps-alloc : falloc fs₁ ≡ alloc
      keeps-alloc = refl

      out-lit : readReg (regs (floc fs₁)) Output
              ≡ prim-sv fits-int (eval (const fits-int v) x)
      -- D115: the machine MATERIALISES the literal, exactly as the float
      -- case below does — `lit-value` is two's complement at this width.
      out-lit =
        writeReg-same (regs s) Output (SV-Lit fits-intˢ (AbstractExec.lit-value {FS} fits-intˢ v))

  obs-correct-const fits-float v _ n l prog base _ span mIn x s alloc cl _ nh rdi-eq =    record
      { traces-agree = λ k → cong (take k) (sym (denot-[] k))
      ; value-realized =
          realized 1 fs₁ mIn (falloc fs₁) ((nh , span 0 _ refl) ∷ []) nh refl refl refl
                   (at-reg fits-float out-lit)
      }
    where
      instr = instr-load-const fits-floatˢ v
      fs₁   = flat-exec-instr instr prog (entry-flat base s alloc cl)


      ev-[] : ∀ pc i → fetch (emitted n l (const fits-float v)) pc ≡ just i → ∀ fs → event-of i fs ≡ []
      ev-[] zero    .instr refl fs = refl
      ev-[] (suc n) i      ()   fs

      mach-[] : ∀ f → flat-events f (emitted n l (const fits-float v)) (entry-flat 0 s alloc cl) ≡ []
      mach-[] f = flat-events-[] (emitted n l (const fits-float v)) ev-[] f (entry-flat 0 s alloc cl)

      denot-[] : ∀ k → projTrace (evalᴰ (const fits-float v) (inject x)) k ≡ []
      denot-[] k = refl

      keeps-alloc : falloc fs₁ ≡ alloc
      keeps-alloc = refl

      out-lit : readReg (regs (floc fs₁)) Output
              ≡ prim-sv fits-float (eval (const fits-float v) x)
      -- Plan 0.73 (D113): the machine MATERIALISES the literal as it executes —
      -- `exec-abstract` writes `round (float-format FS) v`, not the payload.
      -- The denotation says the same because `eval` above is at the same
      -- format; that agreement is the whole point of reading it from one place.
      out-lit =
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
    obs-correct-pair : ∀ {A B C} (f : IR A B) (g : IR A C)
                     → IRObsCorrectF ⟨ f , g ⟩
    -- D171: THE DISCHARGE DICTATED A SPEC QUESTION — named, not guessed.
    --
    -- With `flat-store-floc` (above) the store read-back is no longer the
    -- obstacle, so the `in-loc` residence goes through: the payload cell holds
    -- `SV-Ptr loc` and `valid-inl-wf` is exactly what the two stores wrote.
    --
    -- The `in-reg` residence does NOT. `InputAt`'s `in-reg fit` says `Input1`
    -- holds `prim-sv fit v` — a LITERAL — so `mov-to-output` then
    -- `store-at-slot` writes a literal into the payload cell, while
    -- `valid-inl-wf` demands `readLoc s (sucLoc sum-loc) ≡ just (SV-Ptr
    -- payload-loc)`. A pointer. There is nothing to build, and no amount of
    -- proof effort closes it: the WITNESS and the EMITTER disagree about what a
    -- sum's payload cell contains when the payload fits in a register.
    --
    -- RESOLVED (2026-09-09) — and the EMITTER IS RIGHT, the witness is wrong.
    --
    -- First, a distinction worth keeping: a SUM never fits in a register
    -- (`FitsInReg` has only `fits-int`/`fits-float`), so a sum value is always
    -- memory-resident, two cells, tag and payload. It is only the PAYLOAD that
    -- may be a register-fitting primitive.
    --
    -- And the round trip is coherent. `case` reads the payload back with
    -- `load-indirect-suc ∷ mov-to-input` — the payload CELL'S CONTENT goes into
    -- `Input1` for the branch body — and that body's `InputAt` accepts EITHER
    -- residence: `in-reg` for a literal, `in-loc` for a pointer. So `inl`
    -- storing a literal and `case` loading it back is exactly right, and
    -- `valid-inl-wf`'s `SV-Ptr` demand is what excludes it.
    --
    -- …AND THAT CASE ALREADY EXISTS. The paragraph that stood here prescribed
    -- it as future work — "`valid-inl-wf`/`valid-inr-wf` gain a LITERAL-PAYLOAD
    -- case, following `valid-int-wf`". It landed on 2026-09-05 in 0.86 F (9/n)
    -- as `valid-inl-reg-wf`/`valid-inr-reg-wf` (`ClosureWellFormed:303`), with
    -- `PayloadAt`'s two constructors (`payload-at-loc`, `payload-in-reg`) and
    -- `decomposeInlWF` dispatching on them. Writing the prescription without
    -- checking was the D172 mistake a second time: concluding a witness cannot
    -- express something without enumerating the constructors that would.
    --
    -- SO WHAT ACTUALLY BLOCKS THIS IS NOW UNKNOWN, and that is the honest
    -- state. Two of the three recorded obstacles are gone:
    --   * the literal payload — solved by stage F, above;
    --   * D173's frontier — dissolved by 0.86 stage G. A Stack result landed in
    --     an `AtStack` cell at a frontier nothing bumps, so `BeforeFrontier`
    --     had no constructor to offer; the surviving lowering allocates with
    --     `instr-alloc-heap 2`, which advances `next-heap-ref`, so
    --     `heap-before` applies.
    -- The remaining obligation must be re-derived against the trace that now
    -- exists — the 10-instruction heap build — rather than inherited from prose
    -- about the 5-instruction stack lowering, which stage G deleted.
    obs-correct-inl  : ∀ {A B} → IRObsCorrectF (inl {A} {B})
    obs-correct-inr  : ∀ {A B} → IRObsCorrectF (inr {A} {B})

    -- CLASS D — LABEL-BEARING.
    --
    -- `obs-correct-curry` IS NO LONGER IN THIS CLASS (reclassified 2026-09-09).
    -- The justification here read: "`curry` emits `c-jmp end ∷ c-thunk this bb
    -- ∷ body ++ c-ret bb ∷ c-label end ∷ []` in one literal list, so matching
    -- `⟦curry⟧` requires that the parent's jump lands on THIS clause's
    -- `c-label end`". D159 deleted that shape. `curry` now emits FIVE
    -- instructions (ten in Heap mode), the body is a NAMED BLOCK reached by
    -- `link`, and `labels-in (curry b)` is `li-none` throughout — the clause
    -- mentions no label at all. There is no jump to land, so the converse of
    -- `find-label-sound` is not needed and this is not `labels-unique`'s
    -- consumer.
    --
    -- WHAT IT NEEDS NOW, and it is Class-B shaped (allocate, no control flow):
    --   * `traces-agree` — both sides empty; `curry` emits no event and the
    --     denotation of a value construction emits none either. Same shape as
    --     `obs-correct-free-heap`.
    --   * `value-realized` — a 5-step (resp. 10-step) straight-line chain, with
    --     `place` a `ResultPlace (A ⇛ B)` whose `ValidAtWF` is
    --     `valid-closure-wf` applied to the two `readLoc` equations those
    --     instructions establish (`SV-Ptr env-loc` at the closure cell,
    --     `SV-Code (ℓ o this-label)` at its successor) plus the env's validity.
    --
    -- D170 IS WHAT MAKES THAT REACHABLE. Building `valid-closure-wf` used to
    -- require producing a `BodyCorrect` — a full behavioural proof of the body,
    -- from inside the clause that merely BUILDS the closure record. With the
    -- value carrying only its representation, the witness is exactly what
    -- `store-at-slot` / `instr-load-code-addr` just wrote.
    obs-correct-curry : ∀ {A B C} (body : IR (A * B) C)
                      → IRObsCorrectF (curry body)
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
      ∀ {A B} (n l : ℕ) (si : SigOpInfo A B) (fitness : FitsInReg B) (rA : Readable A)
      → effect si ≡ Pure
      → ∀ (x : ⟦ ⌊ A ⌋ ⟧) (s : LocState FS) (alloc : AllocState {FS})
          (fit : FitsInRegI ⌊ A ⌋)
      → readReg (regs s) Input1 ≡ prim-sv fit x
      → halted s ≡ false
      → readReg (regs (proj₁ (exec-abstract (instr-sigop si) s alloc))) Output
          ≡ prim-sv (fits-erase fitness) (eval (SigOp si) x)
  pure-sigop-value-reg n l si fits-intˢ r-int pure-eq x s alloc fits-int rdi-eq nh
    rewrite nh | sigop-halts-false si pure-eq s =
    trans (cong (λ e → exec-sigop-output-of e si s) pure-eq) step2
    where
      step2 : exec-sigop-output-of Pure si s ≡ prim-sv fits-int (eval (SigOp si) x)
      step2 rewrite cong sv-as-loc rdi-eq | cong (readReg-typed Intˢ) rdi-eq = refl
  pure-sigop-value-reg n l si fits-floatˢ r-int pure-eq x s alloc fits-int rdi-eq nh
    rewrite nh | sigop-halts-false si pure-eq s =
    trans (cong (λ e → exec-sigop-output-of e si s) pure-eq) step2
    where
      step2 : exec-sigop-output-of Pure si s ≡ prim-sv fits-float (eval (SigOp si) x)
      step2 rewrite cong sv-as-loc rdi-eq | cong (readReg-typed Intˢ) rdi-eq = refl
  pure-sigop-value-reg n l si fitness r-unit       pure-eq x s alloc () rdi-eq nh
  pure-sigop-value-reg n l si fitness (r-pair _ _) pure-eq x s alloc () rdi-eq nh

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
      ∀ {A B} (n l : ℕ) (si : SigOpInfo A B) (fitness : FitsInReg B) (rA : Readable A)
      → effect si ≡ Pure
      → ∀ {mIn} (x : ⟦ ⌊ A ⌋ ⟧)
          (s : LocState FS) (alloc : AllocState {FS})
      → halted s ≡ false
      → InputAt mIn alloc x s
      → readReg (regs (proj₁ (exec-abstract (instr-sigop si) s alloc))) Output
          ≡ prim-sv (fits-erase fitness) (eval (SigOp si) x)
  pure-sigop-value-correct n l si fits-intˢ rA pure-eq x s alloc nh (in-reg fit rdi-eq) =
    pure-sigop-value-reg n l si fits-intˢ rA pure-eq x s alloc fit rdi-eq nh
  pure-sigop-value-correct n l si fits-floatˢ rA pure-eq x s alloc nh (in-reg fit rdi-eq) =
    pure-sigop-value-reg n l si fits-floatˢ rA pure-eq x s alloc fit rdi-eq nh
  pure-sigop-value-correct n l si fits-intˢ rA pure-eq x s alloc nh (in-loc input-loc valid _ rdi-eq)
    rewrite nh | sigop-halts-false si pure-eq s =
    trans (cong (λ e → exec-sigop-output-of e si s) pure-eq) step2
    where
      step2 : exec-sigop-output-of Pure si s ≡ prim-sv fits-int (eval (SigOp si) x)
      step2 rewrite sv-loc-of s input-loc rdi-eq | readTyped-adequate rA valid = refl
  pure-sigop-value-correct n l si fits-floatˢ rA pure-eq x s alloc nh (in-loc input-loc valid _ rdi-eq)
    rewrite nh | sigop-halts-false si pure-eq s =
    trans (cong (λ e → exec-sigop-output-of e si s) pure-eq) step2
    where
      step2 : exec-sigop-output-of Pure si s ≡ prim-sv fits-float (eval (SigOp si) x)
      step2 rewrite sv-loc-of s input-loc rdi-eq | readTyped-adequate rA valid = refl
  -- D074: the unit-input route. `r-unit` pins `A ≡ Unitˢ`, so `⌊A⌋ ≡ Unit`
  -- holds by `refl` and the other two readable shapes refute the equality.
  pure-sigop-value-correct n l si fits-intˢ r-unit pure-eq x s alloc nh (in-unit refl)
    rewrite nh | sigop-halts-false si pure-eq s =
    trans (cong (λ e → exec-sigop-output-of e si s) pure-eq)
          (pure-sigop-out-unit si fits-intˢ s (sv-as-loc (readReg (regs s) Input1)))
  pure-sigop-value-correct n l si fits-floatˢ r-unit pure-eq x s alloc nh (in-unit refl)
    rewrite nh | sigop-halts-false si pure-eq s =
    trans (cong (λ e → exec-sigop-output-of e si s) pure-eq)
          (pure-sigop-out-unit si fits-floatˢ s (sv-as-loc (readReg (regs s) Input1)))
  pure-sigop-value-correct n l si fitness r-int pure-eq x s alloc nh (in-unit ())
  pure-sigop-value-correct n l si fitness (r-pair _ _) pure-eq x s alloc nh (in-unit ())

  pure-obs-correct-sigop :
    ∀ {A B} (si : SigOpInfo A B) (fitness : FitsInReg B) (rA : Readable A)
    → effect si ≡ Pure → IRObsCorrectF (SigOp si)
  pure-obs-correct-sigop {A} {B} si fitness rA pure-eq
    _ n l prog base _ span mIn x s alloc cl _ not-halted rdi-eq =
    record
      { traces-agree = λ k →
          trans (cong (take k)
                  (cong (_++ []) (ev-[] 0 (instr-sigop si) refl
                                    (entry-flat base s alloc cl))))
                (cong (take k) (sym (denot-[] k)))
      ; value-realized =
          realized 1 fs₁ Stack (falloc fs₁) ((not-halted , span 0 _ refl) ∷ [])
                   -- A `Pure` SigOp does not halt, so the settle state is LIVE
                   -- (which is what the sequel's `halted s ≡ false` needs).
                   (sigop-halts-false si pure-eq s) refl refl refl
                   (at-reg (fits-erase fitness)
                     (pure-sigop-value-correct n l si fitness rA pure-eq x s alloc
                        not-halted rdi-eq))
      }
    where
      fs₁ = flat-exec-instr (instr-sigop si) prog (entry-flat base s alloc cl)

      -- Machine side: no fetchable instr emits an event (the sole
      -- instruction `instr-sigop si` is `Pure`), so the whole trace is `[]`.
      ev-[] : ∀ pc i → fetch (emitted n l (SigOp si)) pc ≡ just i
            → ∀ fs → event-of i fs ≡ []
      ev-[] zero    .(instr-sigop si) refl fs rewrite pure-eq = refl
      ev-[] (suc pc') i               ()   fs

      mach-[] : ∀ f → flat-events f (emitted n l (SigOp si)) (entry-flat 0 s alloc cl) ≡ []
      mach-[] f = flat-events-[] (emitted n l (SigOp si)) ev-[] f (entry-flat 0 s alloc cl)


      -- Denotation side: a `Pure` SigOp emits nothing (`emit-D … ≡ []`).
      denot-[] : ∀ k → projTrace (evalᴰ (SigOp si) (inject x)) k ≡ []
      denot-[] k rewrite pure-eq = refl

      -- The single `instr-sigop` step leaves the allocator untouched.
      keeps-alloc : falloc fs₁ ≡ alloc
      keeps-alloc rewrite not-halted | pure-eq = refl

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
  -- top-down (Plan 0.54 rung A). `emitted n l (g ∘ f) = ft ++ mov-to-input ∷ gt`:
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

  -- THE composition step. `emitted n l (g ∘ f) = ft ++ mov-to-input ∷ gt`: run
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
  -- D152: `comp-step` now names the ACTUAL emission sites. `ir-to-trace' n l
  -- (g ∘ f)` emits `f` at `(n , l)` and `g` at `(n1 , l1)` — the frontier and
  -- label base `f` LEFT BEHIND. Before the re-indexing this could not even be
  -- SAID: every witness was pinned to frontier 0, so `g`'s hypothesis was about
  -- a different trace than the one spliced into the composite, and the
  -- postulate was covering that mismatch rather than a hard proof.
  --
  -- It is still an axiom, but now it is an axiom of the right shape: `ihg` is
  -- instantiable exactly where `g` is emitted.
  -- D152 A1: the RESULT-to-INPUT bridge, which piece (4) of `comp-step` is
  -- about. `emitted n l (g ∘ f) = ft ++ mov-to-input ∷ gt`, so `g`'s input
  -- residence is `f`'s RESULT residence carried across the mov — and the three
  -- `ResultPlace` shapes map onto the three `InputAt` shapes one for one:
  --
  --     at-loc loc … rax-eq …  ↦  in-loc   (Output held a pointer)
  --     at-reg fit rax-eq      ↦  in-reg   (Output held the literal)
  --     unit-result            ↦  in-unit  (Unit has no residence)
  --
  -- Parameterised by the register equation the mov ESTABLISHES rather than by
  -- the mov itself — the codebase's own rule (`ArithSimCore`): parameterise
  -- over what holds AFTER the step, never over how the step is built. So this
  -- says nothing about `flat-exec-instr` and is reusable wherever a value moves
  -- Output → Input1.
  -- D153: with residence and evidence in ONE premise this states cleanly —
  -- no existential, and no `dflt` location for the caller to invent. The
  -- earlier version needed both purely because `InputAt` was indexed by a
  -- location that `in-reg`/`in-unit` do not constrain; a lemma getting
  -- SIMPLER under the change is the sign the change removed an artifact.
  --
  -- The memory evidence carries across because the mov touches registers
  -- only, which is what `mem-eq` supplies at each call site.
  result→input :
    ∀ {B} {v : ⟦ B ⟧} {mOut alloc ca} {s s' : LocState FS}
    → ResultPlace B mOut alloc ca v s
    → readReg (regs s') Input1 ≡ readReg (regs s) Output
    → (∀ loc → readLoc s' loc ≡ readLoc s loc)
    → InputAt mOut alloc v s'
  result→input (at-loc loc valid before rax-eq _ _) mov-eq mem-eq =
    in-loc loc (validityWF-mem-preserved _ loc _ _ before (λ loc' _ → mem-eq loc') valid)
               before (trans mov-eq rax-eq)
  result→input (at-reg fit rax-eq) mov-eq _ = in-reg fit (trans mov-eq rax-eq)
  result→input unit-result         _      _ = in-unit refl

  -- D152 A1, TOP-DOWN ASSEMBLY. `comp-step` is no longer one axiom: the
  -- record has exactly two fields, so the goal splits into exactly two
  -- obligations, each carrying the field's own type. Nothing is glued upward
  -- from the four supporting pieces — each obligation states what it needs and
  -- the pieces are consumed where the goal asks for them.
  postulate
    -- D158: still fragment-local on the RIGHT (the events of `g ∘ f` run
    -- alone), which is the staged half — `value-realized` moved to the
    -- program-indexed form and this must follow, bounded by the chain rather
    -- than by a fuel, or it over-collects the successor's events.


  -- D158: the hand-over state, as a RECORD EQUATION — and with NO shift. Both
  -- fragments run in the SAME program, so `g`'s entry pc is simply where `f`
  -- left off plus the bridge, and the sequel's entry state IS the state the
  -- bridge produced. This is what quantifying over placement buys: the
  -- relocation that D156's version needed here has nothing left to do.
  handover-eq : ∀ (b : ℕ) (fs : FlatState)
              → fpc fs ≡ b → fret fs ≡ [] → flink fs ≡ nothing
              → fs ≡ entry-flat b (floc fs) (falloc fs) (fclosure fs)
  handover-eq b (mkFlatFull lo al pc rt cls lk) refl refl refl = refl

  -- `(a + suc b) + c ≡ b + suc (a + c)` — the one arithmetic shuffle the
  -- splice needs, in both directions (the sequel's span index, and its end).
  shuffle : ∀ (a b c : ℕ) → (a + suc b) + c ≡ b + suc (a + c)
  shuffle a b c =
    trans (cong (_+ c) (+-suc a b))
          (trans (cong suc (trans (+-assoc a b c)
                           (trans (cong (a +_) (+-comm b c))
                                  (trans (sym (+-assoc a c b))
                                         (+-comm (a + c) b)))))
                 (sym (+-suc b (a + c))))

  -- The composite's span restricted to each component. `f` is a PREFIX of
  -- `ft ++ mov ∷ gt`, `g` a suffix past the bridge.
  comp-span-f : ∀ {A B C} (g : IR B C) (f : IR A B) (prog : AbstractTrace) (base n l : ℕ)
              → SpanAt prog base (emitted n l (g ∘ f))
              → SpanAt prog base (emitted n l f)
  comp-span-f g f prog base n l span k i eq =
    span k i (fetch-++-left (emitted n l f)
                (mov-to-input ∷ emitted (proj₁ (ir-to-trace' n l f))
                                        (proj₁ (proj₂ (ir-to-trace' n l f))) g)
                k i eq)

  -- ══════════════════════════════════════════════════════════════════════
  -- D158: `comp-value-realized`, ASSEMBLED — and now unconditionally.
  --
  -- D156 proved this modulo two splice agreements, and D157 showed the call
  -- case of those is refutable: a fragment-local witness cannot describe a
  -- call that leaves the fragment. Quantifying over placement (D158) removes
  -- the question rather than answering it — `f` and `g` are witnessed IN THE SAME
  -- PROGRAM, at `base` and at `base + length ft + 1`, so there is no second
  -- program for their scans to disagree with. `find-thunk prog ℓ` is the same
  -- scan on both sides, which is exactly what `apply ∘ curry body` needs.
  -- ══════════════════════════════════════════════════════════════════════
  comp-value-realized-of :
    ∀ {A B C} {g : IR B C} {f : IR A B} {x : ⟦ A ⟧} {s alloc cl}
      (prog : AbstractTrace) (base n l : ℕ)
    → ir-size g < program-bound
    → next-slot alloc ≤ n
    → AllSlotStable prog
    → SpanAt prog base (emitted n l (g ∘ f))
    → IRObsCorrectF g → MachineRefinesObsF prog base n l f x s alloc cl
    → ValueRealized prog base n l (g ∘ f) x s alloc cl
  comp-value-realized-of {g = g} {f} {x} {s} {alloc} {cl} prog base n l szg ns ss span ihg mf =
    go (MachineRefinesObsF.value-realized mf)
    where
      module VR = ValueRealized

      ft    = emitted n l f
      n1    = proj₁ (ir-to-trace' n l f)
      l1    = proj₁ (proj₂ (ir-to-trace' n l f))
      gt    = emitted n1 l1 g
      base' = suc (length ft + base)

      span-g : SpanAt prog base' gt
      span-g k i eq =
        subst (λ m → fetch prog m ≡ just i) (shuffle (length ft) k base)
              (span (length ft + suc k) i
                    (trans (fetch-++-right ft (mov-to-input ∷ gt) (suc k)) eq))

      mov-in-prog : fetch prog (length ft + base) ≡ just mov-to-input
      mov-in-prog =
        span (length ft) mov-to-input
             (trans (cong (fetch (ft ++ mov-to-input ∷ gt))
                          (sym (+-identityʳ (length ft))))
                    (fetch-++-right ft (mov-to-input ∷ gt) 0))

      go : ValueRealized prog base n l f x s alloc cl
         → ValueRealized prog base n l (g ∘ f) x s alloc cl
      go (realized kf fsF mOutf caf chainF liveF endF retF linkF placeF) =
        realized (kf + suc (VR.steps vg)) (VR.settle vg)
                 (VR.out-mode vg) (VR.cont-alloc vg)
                 chain (VR.live vg) atEnd (VR.no-ret vg) (VR.no-link vg) (VR.place vg)
        where
          fsM : FlatState
          fsM = flat-exec-instr mov-to-input prog fsF

          runF≡ : exec-flat kf prog (entry-flat base s alloc cl) ≡ fsF
          runF≡ = trans (cong (λ m → exec-flat m prog (entry-flat base s alloc cl))
                              (sym (+-identityʳ kf)))
                        (exec-flat-steps chainF 0)

          nsF : next-slot (falloc fsF) ≡ next-slot alloc
          nsF = trans (cong (λ st → next-slot (falloc st)) (sym runF≡))
                      (flat-run-keeps-next-slot kf prog ss base s alloc cl)

          nsG : next-slot (falloc fsM) ≤ n1
          nsG = ≤-trans (≤-reflexive nsF) (≤-trans ns (frontier-mono f n l))

          liveM : halted (floc fsM) ≡ false
          liveM = liveF

          movEq : readReg (regs (floc fsM)) Input1 ≡ readReg (regs (floc fsF)) Output
          movEq = writeReg-same (regs (floc fsF)) Input1 (readReg (regs (floc fsF)) Output)

          memEq : ∀ loc → readLoc (floc fsM) loc ≡ readLoc (floc fsF) loc
          memEq loc = reg-write-readLoc (floc fsF) _ (halted (floc fsF)) loc

          inputM : InputAt mOutf (falloc fsM) (eval f x) (floc fsM)
          inputM = result→input placeF movEq memEq

          vg : ValueRealized prog base' n1 l1 g (eval f x)
                             (floc fsM) (falloc fsM) (fclosure fsM)
          vg = MachineRefinesObsF.value-realized
                 (ihg szg n1 l1 prog base' ss span-g mOutf (eval f x)
                      (floc fsM) (falloc fsM) (fclosure fsM) nsG liveM inputM)

          movStep : FlatSteps prog 1 fsF fsM
          movStep = (liveF , trans (cong (fetch prog) endF) mov-in-prog) ∷ []

          handover : fsM ≡ entry-flat base' (floc fsM) (falloc fsM) (fclosure fsM)
          handover = handover-eq base' fsM (cong suc endF) retF linkF

          chainG : FlatSteps prog (VR.steps vg) fsM (VR.settle vg)
          chainG = subst (λ st → FlatSteps prog (VR.steps vg) st (VR.settle vg))
                         (sym handover) (VR.run vg)

          chain : FlatSteps prog (kf + suc (VR.steps vg))
                            (entry-flat base s alloc cl) (VR.settle vg)
          chain = FlatSteps-++ chainF (FlatSteps-++ movStep chainG)

          atEnd : fpc (VR.settle vg) ≡ length (emitted n l (g ∘ f)) + base
          atEnd = trans (VR.at-end vg)
                        (sym (trans (cong (_+ base) (length-++ ft {mov-to-input ∷ gt}))
                                    (shuffle (length ft) (length gt) base)))


  -- (moved below `comp-value-realized-of`: it names that proof's chain, so it
  -- cannot be declared above it.)
  postulate
    -- D159: chain-bounded, like the field it now sits beside, and stated about
    -- THE SAME chain `comp-value-realized-of` builds — not about an arbitrary
    -- `ValueRealized`, which would be the D157 mistake again (a universally
    -- quantified witness nothing ties to the run).
    --
    -- This one looks PROVABLE now, and that is the point of the shape: the
    -- composite's chain is `chainF ++ mov ++ chainG`, so `chain-events-++`
    -- splits its events into `f`'s ++ `[]` ++ `g`'s, while `evalᴰ (g ∘ f)`
    -- splits DEFINITIONALLY into `evalᴰ f >>=T evalᴰ g` (DenotTrace:129). The
    -- two halves are then the components' own `traces-agree`. Left as an axiom
    -- only because the `projTrace`/`>>=T` event-concatenation step is its own
    -- piece of work.
    comp-traces-agree :
      ∀ {A B C} {g : IR B C} {f : IR A B} {x : ⟦ A ⟧} {s alloc cl}
        (prog : AbstractTrace) (base n l : ℕ)
        (szg : ir-size g < program-bound) (ns : next-slot alloc ≤ n)
        (ss : AllSlotStable prog) (span : SpanAt prog base (emitted n l (g ∘ f)))
        (ihg : IRObsCorrectF g) (mf : MachineRefinesObsF prog base n l f x s alloc cl)
      → ∀ (k : ℕ) →
          take k (chain-events (ValueRealized.run
                    (comp-value-realized-of prog base n l szg ns ss span ihg mf)))
            ≡ take k (projTrace (evalᴰ (g ∘ f) (inject x)) k)

  comp-step : ∀ {A B C} {g : IR B C} {f : IR A B} {x : ⟦ A ⟧} {s alloc cl}
                (prog : AbstractTrace) (base n l : ℕ)
            → ir-size g < program-bound
            → next-slot alloc ≤ n
            → AllSlotStable prog
            → SpanAt prog base (emitted n l (g ∘ f))
            → IRObsCorrectF g → MachineRefinesObsF prog base n l f x s alloc cl
            → MachineRefinesObsF prog base n l (g ∘ f) x s alloc cl
  comp-step prog base n l szg ns ss span ihg mf = record
    { value-realized = comp-value-realized-of prog base n l szg ns ss span ihg mf
    ; traces-agree   = comp-traces-agree      prog base n l szg ns ss span ihg mf
    }

  comp-obs-correct : ∀ {A B C} {g : IR B C} {f : IR A B}
                   → IRObsCorrectF g → IRObsCorrectF f → IRObsCorrectF (g ∘ f)
  comp-obs-correct {g = g} {f} ihg ihf sz n l prog base ss span mIn x s alloc cl ns nh inp =
    comp-step prog base n l (comp-size-g {g = g} {f} sz) ns ss span ihg
      (ihf (comp-size-f {g = g} {f} sz) n l prog base ss
           (comp-span-f g f prog base n l span) mIn x s alloc cl ns nh inp)

  -- TOTAL, and now with NO CATCH-ALL (Plan 0.68 step 0). Every constructor has
  -- its own clause and its own named obligation, in `Once.IR`'s order — so a
  -- constructor that is added, removed or renamed is a TYPE ERROR here rather
  -- than a silent variable pattern absorbing it (the retired-ctor trap).
  ir-obs-correct : ∀ {A B} (ir : IR A B) → IRObsCorrectF ir
  -- category structure
  ir-obs-correct id                  = obs-correct-id
  ir-obs-correct (g ∘ f)             = comp-obs-correct (ir-obs-correct g) (ir-obs-correct f)
  -- products
  ir-obs-correct ⟨ f , g ⟩         = obs-correct-pair f g
  ir-obs-correct fst                 = obs-correct-fst
  ir-obs-correct snd                 = obs-correct-snd
  -- sums
  ir-obs-correct inl                 = obs-correct-inl
  ir-obs-correct inr                 = obs-correct-inr
  ir-obs-correct (case f g)          = obs-correct-case f g
  -- terminal / initial
  ir-obs-correct terminal            = obs-correct-terminal
  ir-obs-correct initial             = obs-correct-initial
  -- exponentials — THE LABEL-BEARING PAIR
  ir-obs-correct (curry body)      = obs-correct-curry body
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
