-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.IRObsCorrect.Interface
--
-- D200: the SHARED VOCABULARY of the observable-correctness development —
-- the obligation `IRObsCorrectF` and everything its statement mentions.
--
-- Why the split. `IRObsCorrectFlat` was one 4358-line module, and a genuine
-- recheck of it costs 728 s / 2.2 GB (measured, with every dependency cached).
-- Ten postulates are still open in it, so that price was going to be paid a
-- few dozen more times. `ir-obs-correct` is the ONLY recursive definition —
-- its two recursive cases (`comp-obs-correct`, `cata-correct`) take the
-- induction hypothesis as an ARGUMENT rather than calling back — so the
-- per-constructor clauses do not depend on each other at all, and each can
-- live in its own part over this interface.
--
-- (`bundle-telescope-for-oom` records a case where splitting a file did NOT
-- help because the real cost was a 64-parameter module telescope. That failure
-- mode does not apply here: this telescope is `{FS}` and `program-bound`.)
------------------------------------------------------------------------

open import Once.CanonicalName using (CanonicalName)

module Once.CCC.Codegen.IRObsCorrect.Interface (o : CanonicalName) where

open import Once.CCC.Codegen.IRObsCorrect.Prelude o public

-- Qualified aliases cannot be re-exported, so each part repeats these. The
-- bare `import` of FrameSemantics is for the FULLY QUALIFIED
-- `Once.CCC.FrameSemantics.fs-numerics`, which a `using`-re-export does not
-- carry (a `public` re-export carries NAMES, not the module itself).
import Once.CCC.FrameSemantics
import Once.CCC.Machine.SMPrimitives
import Once.IRTy
import Once.IR
import Once.Semantics.Machine as EvV
import Once.CCC.Machine.ReadTypedAdequate as RTA
import Once.Denotation.DenotTrace as DT
import Once.Denotation.TraceMonad as TM
open import Once.Res using (Res; stopped; returns)

module Core {FS : FrameSemantics} where
  -- …and the reference DENOTATION at the same format. That the machine and the
  -- denotation read the format from ONE place is what makes this module's
  -- obligations discharge: `float-format FS` is what `exec-abstract` encodes a
  -- float literal at, so it is what `evalᴰ` must mean by one.
  evalᴰ : ∀ {A B} → IR A B → DT.⟦ A ⟧ᴰᴵ → TM.T DT.⟦ B ⟧ᴰᴵ
  evalᴰ = DT.evalᴰ (Once.CCC.FrameSemantics.fs-numerics FS)

  -- D174: the STEP vocabulary for a run that allocates and dereferences.
  -- `flat-step-straight` threads `exec-abstract` definitionally, so the
  -- structured machine's halt lemmas apply to a flat chain unchanged — the
  -- conditional form is the one `inl`'s indirect stores and slot loads need.
  open TracePrimitives {FS} using (InstrWF; exec-abstract-preserves-halted-WF; load-indirect-twf; load-indirect-suc-twf) public
  open InstrPrimitives {FS} using (exec-abstract-preserves-stack-slot; store-at-slot-preserves-below; exec-abstract-preserves-frame; exec-abstract-preserves-heapMem; store-at-slot-preserves-ancestor) public
  open RecSchemeSemantics {FS} using (exec-abstract-load-indirect-output; exec-abstract-load-indirect-preserves-mem;
                                     exec-abstract-load-indirect-suc-output; exec-abstract-load-indirect-suc-preserves-mem) public
  open Once.CCC.Machine.SMPrimitives using (nhw-load-indirect; nhw-load-indirect-suc; nhw-instr-save-closure-reg; nhw-instr-load-tag-lit; nhw-mov-to-input; nhw-instr-alloc-heap; nhw-instr-load-code-addr; nhw-load-from-slot; InstrNoHeapWrite; instr-writes-slot; nhw-mov-to-output; nhw-instr-load-const; nhw-instr-sigop) public
  open RecSchemeSemantics {FS} using (exec-abstract-preserves-heap-ref) public

  open FlatMachine {FS} public
  open FlatStepsAPI {FS} using (FlatSteps; []; _∷_; exec-flat-steps; FlatSteps-++; FlatSteps-prefix; FlatSteps-reloc) public
  open AbstractExec {FS} using (exec-abstract; exec-sigop-halts; exec-sigop-halts-of; exec-sigop-output-of; pure-sigop-output; pure-sigop-out-aux; pure-sigop-out-val; readTyped; readReg-typed) public
  open FrontierInvariant {FS} using (BeforeFrontier; frontier-monotone) public
  open ClosureWellFormedDef {FS}
    using (ValidAtWF; valid-μ-wf; valid-primitive-wf; ResultPlace; at-loc; at-reg; unit-result; prim-sv
          -- Plan 0.68 step 1: the class-A discharges move the value witness
          -- across a REGISTER write. `ValueLocation` is `AtStack`/`AtDynamic`
          -- only — there is no register location — so `readLoc` cannot see a
          -- register write at all, and this is the combinator that says so.
          ; validityWF-mem-preserved
          ; validityWF-with-bf-transfer
          -- D174: the SUM witnesses. `valid-inl-reg-wf` is stage F's
          -- inline-payload form (no payload location, no payload validity);
          -- `validityWF-frontier-advance` carries a witness across the
          -- allocation this clause performs.
          ; valid-inl-wf; valid-inl-reg-wf; valid-inr-wf; valid-inr-reg-wf
          -- D181: the CLOSURE witnesses. `valid-closure-reg-wf` is the
          -- inline-env form the `curry` discharge needs for a register-literal
          -- or `Unit` environment.
          ; valid-closure-wf; valid-closure-reg-wf; valid-pair-wf; valid-ν-susp-wf
          -- D187: the pair's cells, each carrying its own residence.
          ; CellAt; cell-ptr; cell-inline
          ; module PairValidWF; decomposePairWF
          -- D188: the closure decomposition, which `apply` reads the body, the
          -- environment, the label and the residence off.
          ; module ClosureValidWF; decomposeClosureWF
          ; EnvAt; env-at-loc; env-in-cell
          ; InlineRep; rep-prim; rep-unit; inline-sv
          ; validityWF-frontier-advance) public
  open MemOps {FS} using (readLoc) public
  open ReadLocEq {FS} using (readLoc-stack-heap-eq) public
  open FlatEventTrace {FS} using (flat-events; event-of; flat-events-[]; chain-events; chain-events-nil; chain-events-++; chain-events-subst-start) public
  open RTA o {FS} using (Readable; r-unit; r-int; r-pair; readable?; readTyped-adequate) public
  open CataNextSlot {FS} using (exec-flat-keeps-next-slot; AllSlotStable) public
  open CataIRSlotStable {FS} using (ir-to-trace-slot-stable; ir-stable) public

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
              → ValidAtWF m alloc {⟦ F ⟧TI (μ-type F)}
                  (TM.valueT (evalᴰ (out-μ wf) x) 0) loc s
  μ-layer-iso wf x (valid-μ-wf wf′ .x layer-v)
    rewrite WellFormedFI-irrelevant wf wf′ = layer-v

  -- D189 RETRACTS `ν-not-resident`. It said a ν-typed value is never
  -- machine-resident, and it was provable only because the machine could not
  -- build one: `Ana` emitted no instructions. That made `obs-correct-Out` a
  -- theorem about an empty case — the audit's finding, and the reason this
  -- lemma is gone rather than weakened. A ν IS resident now, as a SUSPENSION
  -- (seed cell + coalgebra code cell — `valid-ν-susp-wf`), so `Out` owes a
  -- real proof against a machine that forces, not one that moves a pointer.

  -- D152: the trace the compiler ACTUALLY emits for `ir` at emission site
  -- `(n , l)`. (`IRToTrace.proj-trace` is `private`, so the projection is
  -- restated rather than that module's interface widened.)
  emitted : ∀ {A B} → ℕ → ℕ → IR A B → AbstractTrace
  emitted n l ir = proj₁ (proj₂ (proj₂ (ir-to-trace' n l ir)))

  -- plan 0.91 S2: the fragment's OTHER output channel. `ir-to-trace'` returns
  -- `(budget , next-label , trace , BLOCKS)`, and until now this obligation
  -- quantified only over the trace. `curry` and `Ana` do not put their body in
  -- the trace — they put it HERE, and `blocks-layout` links it in elsewhere.
  blocks : ∀ {A B} → ℕ → ℕ → IR A B → List (LabelId × ℕ × AbstractTrace)
  blocks n l ir = proj₂ (proj₂ (proj₂ (ir-to-trace' n l ir)))

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

  -- plan 0.88: `SpanAt`'s DUAL, for the other way a fragment addresses itself.
  --
  -- `SpanAt` says the program FETCHES what the fragment's own text does. A
  -- branch does not fetch, it RESOLVES: `c-branch-tag-zero (ℓ o l)` becomes
  -- `do-jump (find-label prog (ℓ o l))`, a scan of the WHOLE program. Nothing
  -- among the premises said that scan lands inside the fragment, so `case` was
  -- not merely unproved — its two jumps had no stated destination, and an
  -- earlier `c-label (ℓ o l)` anywhere in `prog` would have taken them.
  --
  -- Stated in `SpanAt`'s own shape: whatever the fragment's text resolves for
  -- itself, the program resolves at the fragment's offset.
  LabelsAt : AbstractTrace → ℕ → AbstractTrace → Set
  LabelsAt prog base t =
    ∀ (m : LabelId) (j : ℕ) → find-label t m ≡ just j → find-label prog m ≡ just (j + base)

  -- plan 0.91 S2 — THE PLACEMENT PREMISE, and the thing `block-runs` was
  -- assuming (D213 refuted it: a MEMORY fact was being asked to underwrite a
  -- PROGRAM fact). `BlockAt prog blk` says the program actually IMPLEMENTS the
  -- block: the call scan resolves its label, and the whole laid-out block —
  -- `c-thunk` marker, body, `c-ret` — spans there.
  --
  -- `block-layout` rather than the bare body text on purpose. The three parts
  -- are placed contiguously by `blocks-layout`, `find-thunk` resolves to the
  -- `c-thunk` itself (`ft-match true _ _ i = just i`, no successor), and
  -- saying it in ONE `SpanAt` keeps the off-by-one where the layout function
  -- can settle it instead of at every consumer.
  BlockAt : AbstractTrace → LabelId × ℕ × AbstractTrace → Set
  BlockAt prog blk@(lbl , _ , _) =
    ∃[ j ] ((find-thunk prog lbl ≡ just j) × SpanAt prog j (block-layout blk))

  -- `All`, matching `SlotBudget.blocks-below : All BlockOK (bodies-of …)` —
  -- S5's whole-program proof is that induction with this predicate.
  BlocksAt : AbstractTrace → List (LabelId × ℕ × AbstractTrace) → Set
  BlocksAt prog bs = All (BlockAt prog) bs

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
                       {A B} (n l : ℕ) (ir : IR A B) (x : DT.⟦ A ⟧ᴰᴵ)
                       (s : LocState FS) (alloc : AllocState {FS})
                       (cl : StoredValue FS) (k : ℕ) : Set where
    constructor realized
    field
      steps      : ℕ
      settle     : FlatState
      out-mode   : AllocMode
      cont-alloc : AllocState {FS}
      run        : FlatSteps prog steps (entry-flat base s alloc cl) settle
      -- plan 0.97: CONDITIONED ON WHAT THE SPEC SAYS. `live` used to be
      -- `halted (floc settle) ≡ false` outright, which no program that exits
      -- can satisfy — the settle state of a fragment ending in a halting
      -- SigOp has the flag set. That made the obligation unsatisfiable rather
      -- than merely unproved (plan 0.97 §1), and the defect was inherited
      -- from a Spec that said programs never stop.
      --
      -- Now the machine and the Spec agree in BOTH directions: while the
      -- Spec has not stopped the run is live and sits at the end of the
      -- fragment's text; once the Spec has stopped, so has the machine — and
      -- the pc is wherever the halting instruction left it, INSIDE the text,
      -- which is why `at-end` is conditioned too.
      live       : TM.stoppedT (evalᴰ ir x) k ≡ false → halted (floc settle) ≡ false
      at-end     : TM.stoppedT (evalᴰ ir x) k ≡ false
                 → fpc settle ≡ length (emitted n l ir) + base
      stops      : TM.stoppedT (evalᴰ ir x) k ≡ true  → halted (floc settle) ≡ true
      no-ret     : fret settle ≡ []
      no-link    : flink settle ≡ nothing
      -- D179: the value comes from `evalᴰ`, not the pure `eval`. While it was
      -- `eval ir x` the value half refined a DIFFERENT semantics from the
      -- trace half — the same two-models category error this codebase retired
      -- for `Cata`/`Ana`, still live on the machine boundary.
      --
      -- …AT THE OBSERVATION DEPTH `k`, which is now the obligation's own
      -- parameter rather than a number the producer picks. `valueT … k` is
      -- budget-indexed while a run is one concrete run, so the two must be
      -- tied, and an existential "realized at SOME budget" does not compose:
      -- `g ∘ f` must hand `g` the value `f` realizes at the COMPOSITE's depth
      -- (`evalᴰ (g ∘ f) x = evalᴰ f x >>=T evalᴰ g` spends `f`'s events out of
      -- the same budget), and a producer that chose its own could not be asked
      -- for that one. Depth-indexing makes the composition definitional.
      --
      -- …and CONDITIONED for the same reason as `live` (plan 0.97). When the
      -- Spec has stopped the run, the machine is sitting at the halting
      -- instruction and the sequel never executed — so nothing put the
      -- sequel's value anywhere. `>>=T` keeps a value field in the stopped
      -- case only because `T X` has no empty value; that field is not a
      -- result, and a producer must not be asked to place it. The one
      -- consumer that needs a result — a fragment feeding its successor —
      -- only ever needs it on the branch where the successor runs.
      --
      -- plan 0.98: THE PREMISE SUPPLIES THE VALUE. 0.97 wrote the condition as
      -- a boolean equation and then named the value separately, which meant
      -- the obligation could be stated with the two out of step — the premise
      -- said "not stopped" while `valueT` reached into a total value field
      -- that existed even when it was. With the result inside `Res` there is
      -- one fact, and it carries the value: `resT ≡ returns v` is BOTH the
      -- condition and the witness, and `v` is bound by it rather than
      -- computed beside it. The obligation can no longer be mis-stated.
      place      : ∀ {v} → TM.T.resT (evalᴰ ir x) ≡ returns v
                 → ResultPlace B out-mode (falloc settle) cont-alloc
                     v (floc settle)
      -- D204: WHAT THE RUN LEAVES ALONE.
      --
      -- A fragment writes stack slots at or above its own frontier, allocates
      -- only fresh heap, and a call runs in its own frame — so everything the
      -- CALLER has live (`BeforeFrontier alloc`) reads the same after the run
      -- as before it.
      --
      -- Without this field `⟨ f , g ⟩` is unprovable rather than unproved: it
      -- stashes its input at `backup-slot`, runs `f`, and then
      -- `restore-input backup-slot` to hand the same input to `g`. Nothing
      -- else in this record says `f` did not write that slot. (`SlotBudget`
      -- bounds slots from ABOVE — below the budget — which is the other end.)
      --
      -- It is also not new work for most clauses: `TwoCellBuild`,
      -- `OutSetupPres` and `ApplySetupPres` each already prove their own
      -- version internally, and D174's heap lemmas cover `inl`/`inr`. What
      -- was missing was exporting it as part of the obligation.
      -- D208: SPLIT, because the two halves have different fates.
      --
      -- `BeforeFrontier`'s heap constructor IS the bump allocator's encoding —
      -- `heap-before : ref-id (heap-ref hl) < next-heap-ref alloc`. "Live on
      -- the heap" is defined there as "ref-id below the frontier", which is
      -- true of a bump allocator and FALSE of a reusing one: a freed-then-
      -- reallocated `Mempool`/`Slab` slot has a low ref-id and is not the
      -- caller's live data. Plan 0.35 M2 replaces that notion with the
      -- allocator interface's liveness property; until it does, anything
      -- stated over heap locations is instance-specific.
      --
      -- The STACK half is not. Frames are the machine's, not the allocator's,
      -- and `free` never touches a stack slot — so `stack-pres` is permanent,
      -- and it is the half `⟨ f , g ⟩` actually needs (`restore-input backup`
      -- reads `AtStack (current-frame alloc) n`).
      --
      -- Keeping them as one field hid a bump-specific assumption inside a
      -- fact that is otherwise allocator-independent. Split, the contingent
      -- part is named and quarantined.

      -- PERMANENT. Slots below the fragment's own frontier are untouched.
      stack-pres : ∀ (fr : FrameSemantics.Frame FS) (j : ℕ)
                 → BeforeFrontier (record alloc { next-slot = n }) (AtStack fr j)
                 → MemOps.readLoc (floc settle) (AtStack fr j)
                   ≡ MemOps.readLoc s (AtStack fr j)

      -- CONTINGENT on the bump encoding; to be restated as 0.35 M2's liveness
      -- property when the allocator is wired.
      heap-pres  : ∀ (hl : HeapLocation)
                 → BeforeFrontier (record alloc { next-slot = n }) (AtDynamic hl)
                 → MemOps.readLoc (floc settle) (AtDynamic hl)
                   ≡ MemOps.readLoc s (AtDynamic hl)

      -- D210: THE FRAME DOES NOT MOVE.
      --
      -- Found by scouting `⟨ f , g ⟩` top-down: `restore-input backup` reads
      -- `AtStack (current-frame alloc) backup` AFTER `f`'s run, and
      -- transporting `f`'s result validity to the final state wants
      -- `validityWF-frontier-advance`, whose first premise is exactly this.
      -- Nothing in the record said it, and nothing in the tree derives it at
      -- `exec-flat`/`ValueRealized` level — `bf-mono` encodes it only up to
      -- `stack-ancestor`, which is weaker than an equation.
      --
      -- It is cheap and it is TRUE: none of the emitted instructions is a
      -- frame op (that is `FrameFreeTrace`, already proved for every emitted
      -- trace), and a call enters and leaves its own frame. Every discharged
      -- clause already proves its own version of it internally —
      -- `cf-fs10` (Sum, TwoCell), `cf-a16` (ApplySetupPres), `cf-t1`/`cf-u3`
      -- (TenStepPres/NineStepPres) — so the field exports what was already
      -- there rather than asking for new work.
      frame-pres : current-frame (falloc settle) ≡ current-frame alloc

      -- D206: over an arbitrary slot bound `m`, for the same reason
      -- `CalleeRun.mem-pres` is: the run keeps the frame and only grows the
      -- heap, so it carries a `BeforeFrontier` at WHATEVER slot bound the
      -- consumer is working with — `g ∘ f` needs it at `f`'s bound to spend
      -- `f`'s preservation and at `g`'s to spend `g`'s.
      bf-mono    : ∀ (m : ℕ) (loc : ValueLocation FS)
                 → BeforeFrontier (record alloc { next-slot = m }) loc
                 → BeforeFrontier (record (falloc settle) { next-slot = m }) loc

  -- D208: the combined form, DERIVED once rather than assumed per clause.
  -- Consumers that do not care which half they are using (`valid-transport`,
  -- the call-site compositions) keep asking for this; the split is visible
  -- only to whoever needs to know that the heap half is contingent.
  vr-mem-pres : ∀ {prog base A B n l} {ir : IR A B} {x s alloc cl k}
              → (vr : ValueRealized prog base n l ir x s alloc cl k)
              → ∀ (loc : ValueLocation FS)
              → BeforeFrontier (record alloc { next-slot = n }) loc
              → MemOps.readLoc (floc (ValueRealized.settle vr)) loc
                ≡ MemOps.readLoc s loc
  vr-mem-pres vr (AtStack fr j) bf = ValueRealized.stack-pres vr fr j bf
  vr-mem-pres vr (AtDynamic hl) bf = ValueRealized.heap-pres  vr hl bf

  record MachineRefinesObsF (prog : AbstractTrace) (base : ℕ)
                             {A B} (n l : ℕ) (ir : IR A B) (x : DT.⟦ A ⟧ᴰᴵ)
                             (s : LocState FS) (alloc : AllocState {FS})
                             (cl : StoredValue FS) (k : ℕ) : Set where
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
      value-realized : ValueRealized prog base n l ir x s alloc cl k
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
        take k (chain-events (ValueRealized.run value-realized))
          ≡ take k (projTrace (evalᴰ ir x) k)
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
           → ValidAtWF mIn alloc {A} v loc s
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
  ------------------------------------------------------------------------
  -- D188: THE CALLEE'S RUN, at the state the call leaves.
  --
  -- `apply` cannot reuse the body's own `MachineRefinesObsF`: that one starts
  -- from an `entry-flat`, whose `fret` is `[]`, while the call leaves one
  -- pending return address — and `Shifted` relates only stacks of the SAME
  -- length, so nothing bridges them. There is no `fret`-weakening lemma, and
  -- writing one needs a "balanced return stack" invariant (`c-ret` on an empty
  -- `fret` HALTS, so a run that would underflow behaves differently under a
  -- deeper stack). Stating the obligation where the machine actually IS avoids
  -- inventing that.
  ------------------------------------------------------------------------
  -- D198: indexed by ANY `IR A B` and any input, not by a body-of-a-closure.
  -- Nothing in the fields ever used the `E * A` shape — they mention only
  -- `evalᴰ ir inp` and `B` — and the ν force needs the same record at a
  -- COALGEBRA `IR A (⟦F⟧TI A)` called on a bare seed. `apply` instantiates
  -- this at `E * A` and is otherwise unchanged.
  record CalleeRun (prog : AbstractTrace) (fs : FlatState) (ret-pc : ℕ)
                   -- D199: `B` is EXPLICIT. Indexing by the computation
                   -- rather than by `(ir , inp)` costs its inferability —
                   -- `TM.T ⟦ B ⟧` pins `⟦ B ⟧`, and `⟦_⟧` is not injective.
                   (B : IRTy) (comp : TM.T ⟦ B ⟧)
                   (k : ℕ) : Set where
    constructor callee-run
    field
      steps      : ℕ
      settle     : FlatState
      out-mode   : AllocMode
      cont-alloc : AllocState {FS}
      run        : FlatSteps prog steps fs settle
      -- plan 0.97: CONDITIONED, exactly as `ValueRealized`'s three are — and
      -- for the callee this is not a technicality but the point. A called
      -- closure may invoke a halting SigOp; then it never reaches its `c-ret`
      -- and never returns. `live`/`returned`/`place` are what a RETURNING
      -- callee leaves, and `stops` is the other half.
      live       : TM.stoppedT comp k ≡ false → halted (floc settle) ≡ false
      -- …and it RETURNED: the block ends in `c-ret`, which pops the address
      -- the call pushed and leaves the caller's own (empty) stack behind.
      returned   : TM.stoppedT comp k ≡ false → fpc settle ≡ ret-pc
      stops      : TM.stoppedT comp k ≡ true  → halted (floc settle) ≡ true
      no-ret     : fret settle ≡ []
      no-link    : flink settle ≡ nothing
      -- plan 0.98: the premise supplies the value — see `ValueRealized.place`.
      place      : ∀ {v} → TM.T.resT comp ≡ returns v
                 → ResultPlace B out-mode (falloc settle) cont-alloc
                     v (floc settle)
      events     : take k (chain-events run)
                   ≡ take k (projTrace comp k)
      -- D204: WHAT THE CALL LEAVES ALONE — the call half of the same fact
      -- `ValueRealized.mem-pres` states for a straight-line fragment.
      --
      -- This is the deeper of the two. `apply` and `Out` cannot prove it: the
      -- callee's run arrives from `BlockRuns`, so whatever the callee does to
      -- memory is only ever ASSUMED. Until the field existed, "a call
      -- preserves the caller's live data" was hidden inside `block-runs`,
      -- which is why the gap surfaced at `pair` — the one clause that has to
      -- read a slot back after a sub-run — rather than at the call sites.
      --
      -- True for the same reason: the callee runs in its OWN frame
      -- (`enter-call`) and allocates only fresh heap.
      -- Conditioned on the CALLER's frontier, not `falloc fs`. `falloc fs` is
      -- `enter-call pre`, i.e. the CALLEE's — the caller's live data is not
      -- before that, so the obvious phrasing states something else entirely
      -- (and something the caller cannot use). The caller supplies `pre` and
      -- the `enter-call` equation it already has as a premise of `CalleeRuns`.
      -- D206: quantified over the slot bound `m`, because a callee preserves
      -- the caller's frame ENTIRELY — it runs in its own (`enter-call`) — not
      -- merely below some frontier. The caller picks the bound it needs; a
      -- straight-line fragment could not make this claim, which is why
      -- `ValueRealized`'s version is fixed at its own `n`.
      mem-pres   : ∀ (pre : AllocState {FS}) (m : ℕ) → falloc fs ≡ enter-call pre
                 → ∀ (loc : ValueLocation FS)
                 → BeforeFrontier (record pre { next-slot = m }) loc
                 → MemOps.readLoc (floc settle) loc ≡ MemOps.readLoc (floc fs) loc
      -- D210: …and the call's. `enter-call` SHIFTS the frame, so the claim is
      -- against the caller's `pre`, which is what a returning callee restores.
      frame-pres : ∀ (pre : AllocState {FS}) → falloc fs ≡ enter-call pre
                 → current-frame (falloc settle) ≡ current-frame pre

      bf-mono    : ∀ (pre : AllocState {FS}) (m : ℕ) → falloc fs ≡ enter-call pre
                 → ∀ (loc : ValueLocation FS)
                 → BeforeFrontier (record pre { next-slot = m }) loc
                 → BeforeFrontier (record (falloc settle) { next-slot = m }) loc

  ------------------------------------------------------------------------
  -- D188: THE BLOCK TABLE, as the machine needs it — the one fact `apply`
  -- cannot get from the value.
  --
  -- The value↔label link is NOT missing: `callView` reads the label out of the
  -- closure's code cell, and `valid-closure-wf` says both what that cell holds
  -- and what the closure MEANS. What no value can say is that the program's
  -- block table implements that label — D170 removed the value's ability to
  -- carry it on purpose. So it arrives here, conditioned on the closure
  -- witness so the body and the label are the SAME ONES the witness names.
  ------------------------------------------------------------------------
  CalleeRuns : AbstractTrace → Set
  CalleeRuns prog =
    ∀ {E A B : IRTy} (body : IR (E IRTy.* A) B) (env : ⟦ E ⟧) (ℓ : LabelId)
      {m : AllocMode} {alloc' : AllocState {FS}}
      {cloc : ValueLocation FS} {st : LocState FS}
    → ValidAtWF m alloc' {A IRTy.⇛ B} (λ arg → evalᴰ body (env , arg)) cloc st
    → MemOps.readLoc st (sucLoc cloc) ≡ just (SV-Code ℓ)
    → ∃[ j ]
        ( (find-thunk prog ℓ ≡ just j)
        -- The argument's residence is stated at the CALLER's frontier, and the
        -- call's frame entry named separately: `enter-call` SHIFTS the frame,
        -- so a caller-resident component is an ancestor afterwards, and that
        -- transfer belongs with the callee's proof, not at every call site.
        × (∀ (fs : FlatState) (pre-alloc : AllocState {FS})
             (envArg : ⟦ E IRTy.* A ⟧) (ret-pc k : ℕ) (mIn' : AllocMode)
           → fpc fs ≡ j → halted (floc fs) ≡ false → fret fs ≡ ret-pc ∷ []
           → falloc fs ≡ enter-call pre-alloc
           → InputAt {E IRTy.* A} mIn' pre-alloc envArg (floc fs)
           → CalleeRun prog fs ret-pc B (evalᴰ body envArg) k))

  -- D198: the ν analogue of `CalleeRuns`, and a SIBLING rather than an
  -- instance because the two block kinds are called differently BY
  -- CONSTRUCTION: `apply` packs an `(env , arg)` pair on the heap and points
  -- `Input1` at it, while `Out` puts the SEED in `Input1` directly. That is
  -- what makes a ν's code cell a coalgebra rather than a closure body, so one
  -- premise cannot serve both.
  CoalgRuns : AbstractTrace → Set
  CoalgRuns prog =
    ∀ {A : IRTy} {F : Once.IRTy.IRFunctor} (wf : WellFormedFI F)
      (coalg : IR A (⟦ F ⟧TI A)) (seed : ⟦ A ⟧) (ℓ : LabelId)
      {m : AllocMode} {alloc' : AllocState {FS}}
      {vloc : ValueLocation FS} {st : LocState FS}
    → ValidAtWF m alloc' {ν-type F}
        (TM.valueT (evalᴰ (Ana wf coalg) seed) 0) vloc st
    → MemOps.readLoc st (sucLoc vloc) ≡ just (SV-Code ℓ)
    → ∃[ j ]
        ( (find-thunk prog ℓ ≡ just j)
        × (∀ (fs : FlatState) (pre-alloc : AllocState {FS})
             (ret-pc k : ℕ) (mIn' : AllocMode)
           → fpc fs ≡ j → halted (floc fs) ≡ false → fret fs ≡ ret-pc ∷ []
           → falloc fs ≡ enter-call pre-alloc
           → InputAt {A} mIn' pre-alloc seed (floc fs)
           -- D199: the block is the coalgebra FOLLOWED BY the re-suspension of
           -- every recursive position, so what it computes is not `coalg` but
           -- the FORCED LAYER — `evalᴰ (Out wf)` of the very ν whose code cell
           -- named this label. That is `mapAnaᵈ H H coalg (valueT (coalg a))`,
           -- which is precisely the half of `forceᵈ` the emitter used to skip.
           → CalleeRun prog fs ret-pc (⟦ F ⟧TI (ν-type F))
               (evalᴰ (Out wf) (TM.valueT (evalᴰ (Ana wf coalg) seed) 0)) k))

  -- Both block-table premises in ONE slot, so adding the second does not
  -- re-thread the fourteen discharge clauses that only pass it along.
  record BlockRuns (prog : AbstractTrace) : Set where
    field
      closures : CalleeRuns prog
      coalgs   : CoalgRuns prog

  IRObsCorrectF : ∀ {A B} → IR A B → Set
  IRObsCorrectF {A} {B} ir =
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
      -- D188: …and the program's BLOCK TABLE implements the labels its
      -- closures name. Every other premise here is about the fragment; this
      -- one is about the whole image, and it is the only thing `apply` needs
      -- that no value can supply (D170 removed that ability on purpose).
      BlockRuns prog →
      SpanAt prog base (emitted n l ir) →
      -- plan 0.91 S2: …and the program implements the blocks THIS fragment
      -- emits. `SpanAt` covers the fragment's straight-line text; nothing
      -- covered its block channel, which is why `apply` and `Out` had to be
      -- handed `block-runs` — an axiom about arbitrary states — to learn where
      -- a callee lives. This premise is about the fragment, and `curry`/`Ana`
      -- can DISCHARGE it for the blocks they mint.
      BlocksAt prog (blocks n l ir) →
      -- plan 0.88: …and the program RESOLVES the labels this fragment defines
      -- where the fragment puts them. See `LabelsAt`.
      LabelsAt prog base (emitted n l ir) →
    -- D179 (top-down): the input ranges over the MONADIC domain. While it was
    -- `⟦ A ⟧` (pure), `inject x` made every closure trace-free and every ν a
    -- trace-free suspension — so `apply` could never observe a closure emit and
    -- `Out` could never observe a layer emit. The statement was true of a case
    -- that cannot carry effects.
    ∀ (mIn : AllocMode) (x : DT.⟦ A ⟧ᴰᴵ)
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
    InputAt {A} mIn alloc x s →
    -- The OBSERVATION DEPTH, quantified OUTSIDE the witness (D058's "∃ fuel
    -- per depth" shape, now carried by the statement instead of a field). The
    -- machine run does not depend on it; asking for one run that works at
    -- EVERY depth would additionally demand value-stability of `evalᴰ`, a
    -- theorem nothing here needs.
    ∀ (k : ℕ) →
    MachineRefinesObsF prog base n l ir x s alloc cl k

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
