-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

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

module Once.CCC.Codegen.IRObsCorrectFlat where

open import Data.Nat using (ℕ; zero; suc; _<_)
open import Data.Bool using (false; true)
open import Data.List using (length; take; []; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_×_; _,_; ∃; ∃-syntax; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.Type using (Type; ⟦_⟧T; μ-type; FitsInReg; fits-in-reg?)
open import Once.Functor.Translate using (WellFormedF; WellFormedF-irrelevant)
open import Once.Semantics.Machine using (⟦_⟧)
open import Once.IR using (IR; AllocMode; Stack; Cata; SigOp; SigOpInfo; out-μ; id)
open import Once.SigOp.Info using (effect; EffectShape; Pure; Emits; Halts)
open import Relation.Binary.PropositionalEquality using (refl; sym; trans; cong; subst)
open import Once.IR.Size using (ir-size)
open import Once.CCC.Eval using (eval; ⟦_⟧)
open import Once.CCC.Machine.SMCore
  using (LocState; ValueLocation; SV-Ptr; halted; regs; readReg; Input1;
         instr-sigop; mov-to-output; module AbstractExec)
open import Once.CCC.Machine.Allocation using (AllocState; next-slot; module FrontierInvariant)
open import Once.CCC.Machine.Flat using (module FlatMachine)
open import Once.CCC.Codegen.IRToTrace using (ir-to-trace)
open import Once.CCC.Codegen.CataNextSlot using (module CataNextSlot)
open import Once.CCC.Codegen.CataIRSlotStable using (module CataIRSlotStable)
open import Once.CCC.Machine.ClosureWellFormed using (module ClosureWellFormedDef)
open import Once.Denotation.Trace using (SigOpEvent)
open import Once.Denotation.DenotTrace using (evalᴰ; inject)
open import Once.Denotation.TraceMonad using (projTrace)
open import Once.Adequacy.FlatEvents using (module FlatEventTrace)
import Once.CCC.Machine.IR.SimpleWF as SimpleWF
open import Once.CCC.Codegen.FlatSemanticLift using (lift-validAtWF-flat)
open import Data.List.Relation.Unary.All using () renaming ([] to []ᴬ; _∷_ to _∷ᴬ_)
open import Data.Product using (proj₁; proj₂)

module IRObsCorrectFlatness {FS : FrameSemantics} (program-bound : ℕ) where
  open FlatMachine {FS}
  open AbstractExec {FS} using (exec-sigop-halts; exec-trace-single; exec-trace)
  open FrontierInvariant {FS} using (BeforeFrontier)
  open ClosureWellFormedDef {FS} program-bound
    using (ValidAtWF; valid-μ-wf; valid-primitive-wf; place-valid; place-loc; result-place;
           validityWF-mem-only)
  open FlatEventTrace {FS} using (flat-events; event-of; flat-events-[])
  open CataNextSlot {FS} using (exec-flat-keeps-next-slot)
  open CataIRSlotStable {FS} using (ir-to-trace-slot-stable)
  open SimpleWF.SimpleWFImpl {FS} program-bound using (run-id)

  -- μ↔layer iso (the strat-const crux), general in F. A μ-value's
  -- validity at `loc` IS its destructured layer's validity at the SAME
  -- `loc` — `valid-μ-wf` (Plan 0.27 Option 3) bakes this in by carrying
  -- the layer's own `ValidAtWF`. Inverting it yields the layer validity
  -- the algebra consumes. (For a `strat-const` functor, `rec-count F = 0`
  -- ⇒ `⟦F⟧T (μ-type F) ≡ ⟦F⟧T A`, so this layer IS `alg`'s input.)
  -- `WellFormedF-irrelevant` bridges the lemma's `wf` and the proof's.
  μ-layer-iso : ∀ {m F} (wf : WellFormedF F) (x : ⟦ μ-type F ⟧)
                {alloc : AllocState {FS}} {loc : ValueLocation FS} {s : LocState FS}
              → ValidAtWF m alloc {μ-type F} x loc s
              → ValidAtWF m alloc {⟦ F ⟧T (μ-type F)} (eval (out-μ wf) x) loc s
  μ-layer-iso wf x (valid-μ-wf wf′ .x layer-v)
    rewrite WellFormedF-irrelevant wf wf′ = layer-v

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
      -- The value device (`ValidAtWF` — "the value the next effectful SigOp
      -- reads is right", Behavior.agda). Final-value form (terminating
      -- specialization, its own fuel `f`); the per-effectful-SigOp form for
      -- productive `Ana` (no final value) is the next value-device refinement.
      value-realized :
        ∃[ f ] ∃[ mOut ] ∃[ result-loc ]
          ValidAtWF mOut (falloc (flat-run f ir s alloc))
            (eval ir x) result-loc
            (forced (floc (flat-run f ir s alloc)))

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
    readReg (regs s) Input1 ≡ SV-Ptr input-loc →
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
    cata-correct : ∀ {F} (wf : WellFormedF F) {A} (alg : IR (⟦ F ⟧T A) A)
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
  --   * `Cata` routes to `cata-correct` (the loop obligation, discharged by
  --     the descend/base/ascend μ-induction — CataNat*).
  --   * everything else is `obs-correct-rest` — a NAMED scaffold bundling the
  --     straight constructors (id/∘/⟨,⟩/fst/snd/inl/inr/case/terminal/curry/
  --     apply/arr/SigOp — pure cases via `flat-events-[]`, SigOp via the
  --     per-SigOp value correspondence) AND the other recursion schemes
  --     (Para/Hylo/Fuse folds, Ana/Out/in-ν unfolds). To be split per
  --     constructor and discharged; deferred as one obligation for now.
  -- ════════════════════════════════════════════════════════════════════
  postulate
    obs-correct-rest : ∀ {A B} (ir : IR A B) → IRObsCorrectF ir

  -- ════════════════════════════════════════════════════════════════════
  -- `obs-correct-sigop` — the `SigOp` case carved OUT of `obs-correct-rest`
  -- and discharged DIRECTLY (zero new postulates) for the tractable class:
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
  pure-obs-correct-sigop :
    ∀ {A B} (si : SigOpInfo A B) (fitness : FitsInReg B)
    → effect si ≡ Pure → IRObsCorrectF (SigOp si)
  pure-obs-correct-sigop {A} {B} si fitness pure-eq
    _ mIn x input-loc s alloc _ valid input-before not-halted _ =
    record
      { traces-agree = λ k →
          2 , trans (cong (take k) (mach-[] 2))
                    (cong (take k) (sym (denot-[] k)))
      ; value-realized =
          2 , Stack , input-loc , valid-primitive-wf fitness before
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

  obs-correct-sigop : ∀ {A B} (si : SigOpInfo A B) → IRObsCorrectF (SigOp si)
  obs-correct-sigop {A} {B} si with fits-in-reg? B
  ... | nothing = obs-correct-rest (SigOp si)
  ... | just fitness with effect si in pure-eq
  ...   | Pure    = pure-obs-correct-sigop si fitness pure-eq
  ...   | Emits _ = obs-correct-rest (SigOp si)
  ...   | Halts _ = obs-correct-rest (SigOp si)

  -- ════════════════════════════════════════════════════════════════════
  -- `obs-correct-id` — the `id` case carved OUT of `obs-correct-rest`.
  -- `id` is a pure identity: `ir-to-trace id = mov-to-output ∷ []` (a single
  -- register move, emits nothing) and `evalᴰ id a = returnT a` (emits
  -- nothing). So `traces-agree` is `[]` on both sides (same as SigOp). Its
  -- `value-realized` transports the input's own `ValidAtWF` across the
  -- (allocator-neutral) `mov-to-output` step, since `eval id x = x`.
  -- ════════════════════════════════════════════════════════════════════
  obs-correct-id : ∀ {A} → IRObsCorrectF (id {A})
  obs-correct-id {A} _ mIn x input-loc s alloc _ valid input-before not-halted rdi =
    record
      { traces-agree = λ k →
          2 , trans (cong (take k) (mach-[] 2))
                    (cong (take k) (sym (denot-[] k)))
      ; value-realized =
          2 , mIn , place-loc (result-place r) , id-value
      }
    where
      ev-[] : ∀ pc i → fetch (ir-to-trace (id {A})) pc ≡ just i
            → ∀ fs → event-of i fs ≡ []
      ev-[] zero    .mov-to-output refl fs = refl
      ev-[] (suc n) i                 ()   fs

      mach-[] : ∀ f → flat-events f (ir-to-trace (id {A})) (mkFlat s alloc 0) ≡ []
      mach-[] f = flat-events-[] (ir-to-trace (id {A})) ev-[] f (mkFlat s alloc 0)

      denot-[] : ∀ k → projTrace (evalᴰ (id {A}) (inject x)) k ≡ []
      denot-[] k = refl

      -- `run-id` (the abstract codegen correctness for `id`) gives an
      -- `IRResultAWF` whose `result-place` carries `ValidAtWF` at the abstract
      -- post-state. The reusable `lift-validAtWF-flat` (`FlatSemanticLift`, now
      -- rebuilt on the LIVE `validityWF-mem-only`) lifts that to the FLAT
      -- post-state up to `forced`. Every straight constructor reuses it.
      r = run-id x input-loc s alloc valid input-before not-halted rdi

      -- `ir-to-trace id = mov-to-output ∷ []`; `mov-to-output` is a straight
      -- (non-control) instr (`StraightStep = λ _ _ → refl`), built inline —
      -- no red `StraightTrace`.
      straight-id : Straight (ir-to-trace (id {A}))
      straight-id = (λ _ _ → refl) ∷ᴬ []ᴬ

      -- `mov-to-output` doesn't allocate: `proj₂ (exec-trace …) ≡ alloc`.
      alloc-eq : proj₂ (exec-trace (ir-to-trace (id {A})) s alloc) ≡ alloc
      alloc-eq = cong proj₂ (exec-trace-single mov-to-output s alloc not-halted)

      id-value :
        ValidAtWF mIn (falloc (flat-run 2 (id {A}) s alloc))
          (eval (id {A}) x) (place-loc (result-place r))
          (forced (floc (flat-run 2 (id {A}) s alloc)))
      id-value =
        lift-validAtWF-flat program-bound (ir-to-trace (id {A})) s alloc straight-id
          (subst (λ a → ValidAtWF mIn a (eval (id {A}) x) (place-loc (result-place r))
                   (proj₁ (exec-trace (ir-to-trace (id {A})) s alloc)))
                 (sym alloc-eq) (place-valid (result-place r)))

  ir-obs-correct : ∀ {A B} (ir : IR A B) → IRObsCorrectF ir
  ir-obs-correct (Cata wf alg) = cata-correct wf alg (ir-obs-correct alg)
  ir-obs-correct (SigOp si)    = obs-correct-sigop si
  ir-obs-correct id            = obs-correct-id
  ir-obs-correct ir            = obs-correct-rest ir
