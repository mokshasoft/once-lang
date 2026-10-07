-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.FlatEvents — the machine SigOp-event trace.
--
-- Plan 0.36 (machine side): `flat-events` is the machine counterpart of
-- the source observable `obs` (Once.Denotation.TraceDenote). It mirrors
-- `exec-flat`'s three mutual fuel functions (Once.CCC.Machine.Flat) and
-- emits a `SigOpEvent` at each `instr-sigop` it executes — leaving
-- `exec-flat`/`FlatState` untouched (a parallel observation, not an
-- accumulator threaded through the machine).
--
-- It runs over `exec-flat` (pc + jump + fuel), NOT the straight-line
-- `exec-trace`, because the recursion schemes compile to LOOPS
-- (`instr-ctrl` jumps) which only the flat machine can execute. The
-- machine is architecture-GENERIC (`FrameSemantics`-parameterised), so
-- `flat-events` — and the `traces-agree` theorem over it — is one
-- definition for all targets; the per-target bridge is the IR-agnostic
-- `flat-sim`.
--
-- FAITHFUL arguments: the Layer-0 observable IS the exit-syscall
-- argument, so the trace must carry it. `SigOpEvent` coarsens the
-- argument to `ev-argℕ : Maybe ℕ`; `flat-events` decodes the machine's
-- `Input1` (`SV-Lit {Int}` → the ℕ) — a function. `traces-agree` (next)
-- proves this ℕ equals `obs`'s via the per-SigOp value-correspondence.
------------------------------------------------------------------------

module Once.Adequacy.FlatEvents where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Properties using (++-assoc; ++-identityʳ)
open import Data.Nat using (_+_)
open import Data.Product using (_,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

-- `fits-int`/`fits-float` must be IMPORTED, not just written: out of scope
-- they parse as variable patterns and `decode-arg`'s scalar clauses silently
-- stop refining `SV-Lit`'s index.
open import Once.CCC.FrameSemantics using (FrameSemantics)
-- The observable's value domain — the same `⟦_⟧` the event carries.
open import Once.CCC.Machine.SMCore
  using (LocState; module LocState; halted; module AbstractExec; AbstractTrace; AbstractInstr; instr-sigop)
open import Once.CCC.Machine.Flat
open import Once.CCC.Codegen.FlatStepLemmas using (module FlatStepsAPI)
open import Once.Denotation.Trace using (SigOpEvent)
open import Once.CCC.Machine.FlatLog using (LogFree)
import Once.CCC.Machine.FlatLog
import Once.CCC.Machine.SMCore as SMC
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Product using (_×_)

module FlatEventTrace {FS : FrameSemantics} where
  open FlatMachine {FS}
  open FlatStepsAPI {FS}

  -- The decoder and the event a SigOp invocation is live in `SMCore`'s
  -- `AbstractExec` (plan 0.105: the machine logs its events, so it decodes
  -- them itself).
  open AbstractExec {FS} using (sigop-events)
  private module LP = Once.CCC.Machine.FlatLog.LogPres {FS}

  ev-of-loc : AbstractInstr → LocState FS → List SigOpEvent
  -- The step's own events: what `exec-abstract` appends to the log.
  ev-of-loc (instr-sigop si) loc = sigop-events si loc
  {-# CATCHALL #-}
  ev-of-loc _                _   = []

  -- Events emitted by executing one instruction from state `fs`.
  event-of : AbstractInstr → FlatState → List SigOpEvent
  event-of i fs = ev-of-loc i (floc fs)

  -- The SigOp-event trace, mirroring `exec-flat`'s fuel/fetch dispatch.
  flat-events       : ℕ → AbstractTrace → FlatState → List SigOpEvent
  flat-events-step  : Bool → ℕ → AbstractTrace → FlatState → List SigOpEvent
  flat-events-fetch : Maybe AbstractInstr → ℕ → AbstractTrace → FlatState → List SigOpEvent

  flat-events zero    _    fs = []
  flat-events (suc n) prog fs = flat-events-step (halted (floc fs)) n prog fs

  flat-events-step true  _ _    fs = []
  flat-events-step false n prog fs = flat-events-fetch (fetch prog (fpc fs)) n prog fs

  flat-events-fetch nothing  _ _    fs = []
  flat-events-fetch (just i) n prog fs =
    event-of i fs ++ flat-events n prog (flat-exec-instr i prog fs)

  -- A HALTED flat state emits nothing, at any fuel — the abstract counterpart of
  -- `RunTraceCore.run-events-halted` / `-stuck`. Used by every "both machines
  -- stop here" correspondence case.
  flat-events-halted : ∀ (n : ℕ) (prog : AbstractTrace) (fs : FlatState)
                     → halted (floc fs) ≡ true → flat-events n prog fs ≡ []
  flat-events-halted zero    prog fs _ = refl
  flat-events-halted (suc n) prog fs h rewrite h = refl

  ----------------------------------------------------------------------
  -- Machine-side "no SigOp ⇒ empty trace": if every instruction the run
  -- can fetch emits nothing (`event-of … ≡ []` — i.e. no `instr-sigop`),
  -- the whole `flat-events` trace is `[]`. By fuel induction, mirroring
  -- `flat-events`'s dispatch. This discharges `traces-agree` for a PURE
  -- cata (with `pure-cata-emits-[]`: both sides `[]`) and is what
  -- `pure-refines` consumes for straight-line IRs.
  ----------------------------------------------------------------------

  flat-events-[] : ∀ (prog : AbstractTrace)
                 → (∀ pc i → fetch prog pc ≡ just i → ∀ fs → event-of i fs ≡ [])
                 → ∀ (fuel : ℕ) (fs : FlatState) → flat-events fuel prog fs ≡ []
  flat-events-[] prog H zero    fs = refl
  flat-events-[] prog H (suc n) fs with halted (floc fs)
  ... | true  = refl
  ... | false with fetch prog (fpc fs) in eq
  ...   | nothing = refl
  ...   | just i  rewrite H (fpc fs) i eq fs =
            flat-events-[] prog H n (flat-exec-instr i prog fs)

  ----------------------------------------------------------------------
  -- Events analogue of `exec-flat-steps`: peel a whole `FlatSteps` chain
  -- off `flat-events`, accumulating each link's emitted events. The
  -- emitted events of a chain are `chain-events` — the concatenation of
  -- `event-of` at each link's start state. This lets the cata's
  -- per-iteration reasoning REUSE the `FlatSteps` chains already built in
  -- the deleted CataNat* descend/ascend modules (D132) for the trace,
  -- not just the state. For a SILENT chain (control/reg/load/build-layer
  -- — no `instr-sigop`), `chain-events` reduces to `[]` definitionally,
  -- so `flat-events` simply skips it to the chain's end state.
  ----------------------------------------------------------------------
  chain-events : ∀ {prog k fs fs'} → FlatSteps prog k fs fs' → List SigOpEvent
  chain-events []                            = []
  chain-events (_∷_ {fs = fs} {i = i} _ rest) = event-of i fs ++ chain-events rest

  -- The empty chain emits no events. Trivially `refl` HERE (inside the
  -- defining module, where `chain-events` reduces); exported so downstream
  -- callers — under `open FlatEventTrace`, where the recursive `chain-
  -- events` does not unfold to `refl` — can still close `chain-events [] ≡ []`
  -- base cases.
  chain-events-nil : ∀ {prog fs} → chain-events {prog} {0} {fs} {fs} [] ≡ []
  chain-events-nil = refl

  -- ANY length-0 chain emits no events. Stated over a VARIABLE chain `c`
  -- (not a reducible application), so the exported type stays neutral —
  -- `chain-events c ≡ []` — instead of normalising to `[] ≡ []`. Downstream
  -- it applies to any concrete length-0 chain (e.g. the descend-loop
  -- μ-induction base `chain-steps k zero st f`, whose length index `zero * k`
  -- is `0`), closing `chain-events that ≡ []` directly — sidestepping the
  -- cross-module reduction that `open` blocks. The `∷` constructor has
  -- length `suc`, so the `[]` clause is the only cover.
  chain-events-len0 : ∀ {prog fs fs'} (c : FlatSteps prog 0 fs fs') → chain-events c ≡ []
  chain-events-len0 [] = refl

  -- `chain-events` is invariant under transport of the LENGTH index (it
  -- pattern-matches the chain's structure, never reading its length).
  -- Lets a depth-0 chain whose length is a stuck application (e.g. `zero *
  -- k` from `chain-steps`'s `n * k` return index) be retyped to literal `0`
  -- so `chain-events-len0` applies, then bridged back.
  chain-events-subst-len : ∀ {prog n m fs fs'} (eq : n ≡ m) (c : FlatSteps prog n fs fs')
                         → chain-events (subst (λ k → FlatSteps prog k fs fs') eq c) ≡ chain-events c
  chain-events-subst-len refl c = refl

  flat-events-steps : ∀ {prog k fs fs'} (steps : FlatSteps prog k fs fs')
                    → ∀ b → flat-events (k + b) prog fs
                              ≡ chain-events steps ++ flat-events b prog fs'
  flat-events-steps []                              b = refl
  flat-events-steps (_∷_ {fs = fs} {i = i} (h , f) rest) b
    rewrite h | f =
      trans (cong (event-of i fs ++_) (flat-events-steps rest b))
            (sym (++-assoc (event-of i fs) (chain-events rest) (flat-events b _ _)))

  -- `chain-events` is COMPOSITIONAL: the two lemmas that make it survive
  -- the way `FlatSteps` chains are actually built (`flat-step1` retypes a
  -- link's result via a `subst` along a step-lemma equality, and phases
  -- compose via `FlatSteps-++`). Without them `chain-events` is stuck on
  -- the opaque `subst`. With them, the events of any composite/retyped
  -- chain reduce to the obvious concatenation — so a silent phase's
  -- events provably vanish even though its chain is full of substs.

  -- Distributes over `FlatSteps-++`.
  chain-events-++ : ∀ {prog k₁ k₂ fs₁ fs₂ fs₃}
                      (xs : FlatSteps prog k₁ fs₁ fs₂) (ys : FlatSteps prog k₂ fs₂ fs₃)
                  → chain-events (FlatSteps-++ xs ys) ≡ chain-events xs ++ chain-events ys
  chain-events-++ []                            ys = refl
  chain-events-++ (_∷_ {fs = fs} {i = i} _ xs) ys =
    trans (cong (event-of i fs ++_) (chain-events-++ xs ys))
          (sym (++-assoc (event-of i fs) (chain-events xs) (chain-events ys)))

  -- Invariant under the index `subst` (it transports the chain's END
  -- state, which `chain-events` never reads — events depend only on each
  -- link's FROM state + instruction, both preserved by the transport).
  chain-events-subst : ∀ {prog k fs fs₁ fs₂} (eq : fs₁ ≡ fs₂) (stp : FlatSteps prog k fs fs₁)
                     → chain-events (subst (FlatSteps prog k fs) eq stp) ≡ chain-events stp
  chain-events-subst refl stp = refl

  -- Invariant under transport of the START state too (the relocation's
  -- `subst` realigns the tail's start state, not its end). Same `refl`.
  chain-events-subst-start : ∀ {prog k fs₁ fs₂ fs'} (eq : fs₁ ≡ fs₂) (stp : FlatSteps prog k fs₁ fs')
                           → chain-events (subst (λ s → FlatSteps prog k s fs') eq stp) ≡ chain-events stp
  chain-events-subst-start refl stp = refl

  ------------------------------------------------------------------------
  -- Plan 0.105: THE LOG GROWS BY EXACTLY THE EVENTS. A step appends its own
  -- `event-of` to the machine's log (the SigOp step by definition, every other
  -- step leaves it alone — `FlatLog`), so a chain grows the log by its
  -- `chain-events`. `NotNested` excludes the two retired nested instructions,
  -- which run a trace inside one step; nothing emits them.
  ------------------------------------------------------------------------
  NotNested : AbstractInstr → Set
  NotNested (SMC.instr-case-on-tag _ _) = ⊥
  NotNested (SMC.instr-loop _)          = ⊥
  {-# CATCHALL #-}
  NotNested _                       = ⊤

  private
    flog : FlatState → List SigOpEvent
    flog fs = LocState.ev-log (floc fs)

    silent : ∀ (i : AbstractInstr) → LogFree i → ∀ prog fs → event-of i fs ≡ []
           → flog (flat-exec-instr i prog fs) ≡ flog fs ++ event-of i fs
    silent i lf prog fs ev = trans (LP.flat-exec-instr-log i lf prog fs)
                                   (trans (sym (++-identityʳ _)) (cong (flog fs ++_) (sym ev)))

  step-log : ∀ (i : AbstractInstr) → NotNested i → ∀ prog fs
           → flog (flat-exec-instr i prog fs) ≡ flog fs ++ event-of i fs
  step-log SMC.mov-to-output nn prog fs = silent SMC.mov-to-output tt prog fs refl
  step-log SMC.mov-to-input nn prog fs = silent SMC.mov-to-input tt prog fs refl
  step-log SMC.load-indirect nn prog fs = silent SMC.load-indirect tt prog fs refl
  step-log SMC.load-indirect-suc nn prog fs = silent SMC.load-indirect-suc tt prog fs refl
  step-log (SMC.load-from-slot slot) nn prog fs = silent (SMC.load-from-slot slot) tt prog fs refl
  step-log (SMC.store-at-slot slot) nn prog fs = silent (SMC.store-at-slot slot) tt prog fs refl
  step-log SMC.store-indirect nn prog fs = silent SMC.store-indirect tt prog fs refl
  step-log SMC.store-indirect-suc nn prog fs = silent SMC.store-indirect-suc tt prog fs refl
  step-log (SMC.lea-slot slot) nn prog fs = silent (SMC.lea-slot slot) tt prog fs refl
  step-log (SMC.restore-input slot) nn prog fs = silent (SMC.restore-input slot) tt prog fs refl
  step-log (SMC.lea-indexed slot) nn prog fs = silent (SMC.lea-indexed slot) tt prog fs refl
  step-log (SMC.instr-alloc-stack n) nn prog fs = silent (SMC.instr-alloc-stack n) tt prog fs refl
  step-log (SMC.instr-dealloc-stack n) nn prog fs = silent (SMC.instr-dealloc-stack n) tt prog fs refl
  step-log (SMC.instr-reclaim-to n) nn prog fs = silent (SMC.instr-reclaim-to n) tt prog fs refl
  step-log (SMC.instr-push-frame cap) nn prog fs = silent (SMC.instr-push-frame cap) tt prog fs refl
  step-log SMC.instr-pop-frame nn prog fs = silent SMC.instr-pop-frame tt prog fs refl
  step-log SMC.instr-call-closure nn prog fs = silent SMC.instr-call-closure tt prog fs refl
  step-log (SMC.worklist-init slot) nn prog fs = silent (SMC.worklist-init slot) tt prog fs refl
  step-log (SMC.worklist-push slot) nn prog fs = silent (SMC.worklist-push slot) tt prog fs refl
  step-log (SMC.worklist-pop slot) nn prog fs = silent (SMC.worklist-pop slot) tt prog fs refl
  step-log (SMC.worklist-check slot) nn prog fs = silent (SMC.worklist-check slot) tt prog fs refl
  step-log (instr-sigop si)        _  prog fs = refl
  step-log (SMC.instr-load-const p v) nn prog fs = silent (SMC.instr-load-const p v) tt prog fs refl
  step-log (SMC.instr-load-code-addr n) nn prog fs = silent (SMC.instr-load-code-addr n) tt prog fs refl
  step-log SMC.instr-save-closure-reg nn prog fs = silent SMC.instr-save-closure-reg tt prog fs refl
  step-log (SMC.instr-load-tag-lit n) nn prog fs = silent (SMC.instr-load-tag-lit n) tt prog fs refl
  step-log (SMC.instr-case-on-tag f g) () prog fs
  step-log (SMC.instr-alloc-heap n) nn prog fs = silent (SMC.instr-alloc-heap n) tt prog fs refl
  step-log (SMC.instr-loop body) () prog fs
  step-log (SMC.instr-reg-op op) nn prog fs = silent (SMC.instr-reg-op op) tt prog fs refl
  step-log (SMC.instr-ctrl c) nn prog fs = silent (SMC.instr-ctrl c) tt prog fs refl

  -- Every instruction a chain fetches is not nested.
  ChainNotNested : ∀ {prog k fs fs'} → FlatSteps prog k fs fs' → Set
  ChainNotNested []                      = ⊤
  ChainNotNested (_∷_ {i = i} _ rest)    = NotNested i × ChainNotNested rest

  chain-log : ∀ {prog k fs fs'} (r : FlatSteps prog k fs fs') → ChainNotNested r
            → flog fs' ≡ flog fs ++ chain-events r
  chain-log []                                  _          = sym (++-identityʳ _)
  chain-log {prog} (_∷_ {fs = fs} {i = i} _ rest) (nn , nns) =
    trans (chain-log rest nns)
          (trans (cong (_++ chain-events rest) (step-log i nn prog fs))
                 (++-assoc (flog fs) (event-of i fs) (chain-events rest)))

  -- A SETTLED state (halted, or nothing to fetch) emits no events for any
  -- fuel — the run is over. (`flat-events`'s first dispatch returns `[]`.)
  flat-events-settled : ∀ (prog : AbstractTrace) (fs : FlatState) (r : ℕ)
                      → (halted (floc fs) ≡ true) ⊎ (fetch prog (fpc fs) ≡ nothing)
                      → flat-events r prog fs ≡ []
  flat-events-settled prog fs zero    _        = refl
  flat-events-settled prog fs (suc r) (inj₁ h) rewrite h = refl
  flat-events-settled prog fs (suc r) (inj₂ f) with halted (floc fs)
  ... | true  = refl
  ... | false rewrite f = refl

  -- The trace of a HALTING run equals the events of its reified chain:
  -- peel the chain off the fuel (`flat-events-steps`, via `fuel-split`),
  -- and the settled tail contributes nothing (`flat-events-settled`). This
  -- is what lets `at`'s standalone `traces-agree` (stated over `flat-
  -- events`) feed the chain-level relocation (`chain-events-relocate`).
  flat-events-reify : ∀ (n : ℕ) (prog : AbstractTrace) (fs : FlatState)
                        (rr : RunReified prog fs n)
                    → flat-events n prog fs ≡ chain-events (RunReified.chain rr)
  flat-events-reify n prog fs (reified N r fs' ch st fsp) =
    trans (cong (λ m → flat-events m prog fs) fsp)
          (trans (flat-events-steps ch r)
                 (trans (cong (chain-events ch ++_) (flat-events-settled prog fs' r st))
                        (++-identityʳ (chain-events ch))))
