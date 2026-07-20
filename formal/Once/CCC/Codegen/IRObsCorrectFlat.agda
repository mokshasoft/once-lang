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
-- SigOpInfo is over SURFACE Type (`SigOp : SigOpInfo A B → IR ⌊A⌋ ⌊B⌋`), so the
-- surface `FitsInReg`/`fits-in-reg?` stay; the μ/functor + value-domain layer is IRTy.
open import Once.Type using (Type; FitsInReg; fits-in-reg?)
  renaming (fits-int to fits-intˢ; fits-float to fits-floatˢ)
open import Once.IRTy using (WellFormedFI-irrelevant)
open import Once.Semantics.Machine using () renaming (⟦_⟧ᴵ to ⟦_⟧)
open import Once.IR using (IR; IRTy; AllocMode; Stack; Cata; SigOp; SigOpInfo; out-μ; _∘_;
  μ-type; ⟦_⟧TI; WellFormedFI; FitsInRegI; fits-int; fits-float; ⌊_⌋)

-- Surface `FitsInReg B` ⇒ erased `FitsInRegI ⌊B⌋`: `⌊Int⌋=Int`, `⌊Float⌋=Float`
-- definitionally, so this is a match-to-refl coherence.
fits-erase : ∀ {B} → FitsInReg B → FitsInRegI ⌊ B ⌋
fits-erase fits-intˢ   = fits-int
fits-erase fits-floatˢ = fits-float
open import Once.SigOp.Info using (effect; EffectShape; Pure; Emits; Halts)
open import Relation.Binary.PropositionalEquality using (refl; sym; trans; cong)
open import Once.IR.Size using (ir-size)
open import Data.Nat.Properties using (≤-<-trans; ≤-trans; m≤m+n; m≤n+m; n≤1+n)
open import Function using (case_of_)
open import Once.CCC.Eval using (eval)
open import Once.CCC.Machine.SMCore
  using (LocState; ValueLocation; SV-Ptr; sv-as-loc; halted; regs; readReg; Input1; Output;
         instr-sigop; module AbstractExec)
open import Once.CCC.Machine.Allocation using (AllocState; next-slot; module FrontierInvariant)
open import Once.CCC.Machine.Flat using (module FlatMachine)
open import Once.CCC.Codegen.IRToTrace using (ir-to-trace)
open import Once.CCC.Codegen.CataNextSlot using (module CataNextSlot)
open import Once.CCC.Codegen.CataIRSlotStable using (module CataIRSlotStable)
open import Once.CCC.Machine.ClosureWellFormed using (module ClosureWellFormedDef)
import Once.CCC.Machine.ReadTypedAdequate as RTA
open import Once.Denotation.Trace using (SigOpEvent)
open import Once.Denotation.DenotTrace using (evalᴰ; inject)
open import Once.Denotation.TraceMonad using (projTrace)
open import Once.Adequacy.FlatEvents using (module FlatEventTrace)

module IRObsCorrectFlatness {FS : FrameSemantics} (program-bound : ℕ) where
  open FlatMachine {FS}
  open AbstractExec {FS} using (exec-sigop-halts; exec-sigop-halts-of; exec-sigop-output-of; pure-sigop-output; readTyped)
  open FrontierInvariant {FS} using (BeforeFrontier)
  open ClosureWellFormedDef {FS} program-bound
    using (ValidAtWF; valid-μ-wf; valid-primitive-wf; ResultPlace; at-loc; at-reg; unit-result; prim-sv)
  open FlatEventTrace {FS} using (flat-events; event-of; flat-events-[])
  open RTA {FS} program-bound using (Readable; readable?; readTyped-adequate)
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
    cata-correct : ∀ {F} (wf : WellFormedFI F) {A} (alg : IR (⟦ F ⟧TI A) A)
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
  postulate
    pure-sigop-value-reg :
      ∀ {A B} (si : SigOpInfo A B) (fitness : FitsInReg B) → effect si ≡ Pure
      → ∀ (x : ⟦ ⌊ A ⌋ ⟧) (s : LocState FS) (alloc : AllocState {FS})
          (fit : FitsInRegI ⌊ A ⌋)
      → readReg (regs s) Input1 ≡ prim-sv fit x
      → halted s ≡ false
      → readReg (regs (forced (floc (flat-run 2 (SigOp si) s alloc)))) Output
          ≡ prim-sv (fits-erase fitness) (eval (SigOp si) x)

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
    pure-sigop-value-reg si fits-intˢ pure-eq x s alloc fit rdi-eq nh
  pure-sigop-value-correct si fits-floatˢ rA pure-eq x input-loc s alloc valid nh (in-reg fit rdi-eq) =
    pure-sigop-value-reg si fits-floatˢ pure-eq x s alloc fit rdi-eq nh
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

  obs-correct-sigop : ∀ {A B} (si : SigOpInfo A B) → IRObsCorrectF (SigOp si)
  -- Route on BOTH the codomain (register-resident result) and the domain
  -- (readable input ⇒ the machine can materialise it and apply `semM`). A Pure
  -- SigOp over a non-readable input keeps the sentinel, so it makes no value
  -- claim and falls back to `obs-correct-rest`. Arith is always readable.
  obs-correct-sigop {A} {B} si with fits-in-reg? B | readable? A
  ... | nothing      | _       = obs-correct-rest (SigOp si)
  ... | just fitness | nothing = obs-correct-rest (SigOp si)
  ... | just fitness | just rA with effect si in pure-eq
  ...   | Pure    = pure-obs-correct-sigop si fitness rA pure-eq
  ...   | Emits _ = obs-correct-rest (SigOp si)
  ...   | Halts _ = obs-correct-rest (SigOp si)

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
  --      `ComposeWF.exec-trace-compose-eq` (same thing for the straight machine);
  --      relocation: `CataAtRelocate.{shift-pc, flat-relocate-straight/-label/-jmp}`.
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

  ir-obs-correct : ∀ {A B} (ir : IR A B) → IRObsCorrectF ir
  ir-obs-correct (Cata wf alg) = cata-correct wf alg (ir-obs-correct alg)
  ir-obs-correct (SigOp si)    = obs-correct-sigop si
  ir-obs-correct (g ∘ f)       = comp-obs-correct (ir-obs-correct g) (ir-obs-correct f)
  ir-obs-correct ir            = obs-correct-rest ir
