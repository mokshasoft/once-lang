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
open import Data.Nat using (_+_; _≤_; s≤s; z≤n)
open import Data.Nat.Properties using (+-assoc; m≤n+m; m≤m+n)
open import Data.Product using (_,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

-- `fits-int`/`fits-float` must be IMPORTED, not just written: out of scope
-- they parse as variable patterns and `decode-arg`'s scalar clauses silently
-- stop refining `SV-Lit`'s index.
open import Once.CCC.FrameSemantics using (FrameSemantics)
-- The observable's value domain — the same `⟦_⟧` the event carries.
open import Once.CCC.Machine.SMCore
  using (LocState; module LocState; module AbstractExec; AbstractTrace; AbstractInstr; instr-sigop; instr-ctrl)
open import Once.CCC.Machine.SMCore
  using ( mov-to-output; mov-to-input; load-indirect; load-indirect-suc; load-from-slot; store-at-slot; store-indirect
        ; store-indirect-suc; lea-slot; restore-input; instr-alloc-stack; instr-dealloc-stack; instr-reclaim-to
        ; instr-push-frame; instr-pop-frame; instr-call-closure; worklist-init; worklist-push; worklist-pop
        ; worklist-check; instr-load-const; instr-load-code-addr; instr-save-closure-reg; instr-load-tag-lit
        ; instr-alloc-heap; instr-reg-op )
open LocState using (halted)
open import Once.CCC.Machine.Flat
open import Once.CCC.Codegen.FlatStepLemmas using (module FlatStepsAPI)
open import Once.Internal.Event using (SigOpEvent)
open import Once.CCC.Machine.FlatLog using (LogFree)
open import Once.CCC.Machine.FlatLeft using (LeftFree)
import Once.CCC.Machine.FlatLeft
import Once.CCC.Machine.FlatLog
import Once.CCC.Machine.SMCore as SMC
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (_×_; proj₁)
open import Once.Internal.Out using (Out; cut; stop; ended; end-of-left; _▹_; ▹-assoc)

module FlatEventTrace {FS : FrameSemantics} where
  open FlatMachine {FS}
  open FlatStepsAPI {FS}

  -- The decoder and the event a SigOp invocation is live in `SMCore`'s
  -- `AbstractExec` (plan 0.105: the machine logs its events, so it decodes
  -- them itself).
  open AbstractExec {FS} using (sigop-events)
  private module LP = Once.CCC.Machine.FlatLog.LogPres {FS}
  private module LL = Once.CCC.Machine.FlatLeft.LeftPres {FS}

  ev-of-loc : AbstractInstr → LocState FS → List SigOpEvent
  -- The step's own events: what `exec-abstract` appends to the log.
  ev-of-loc (instr-sigop si) loc = sigop-events si loc
  {-# CATCHALL #-}
  ev-of-loc _                _   = []

  -- Events emitted by executing one instruction from state `fs`.
  event-of : AbstractInstr → FlatState → List SigOpEvent
  event-of i fs = ev-of-loc i (floc fs)

  -- The SigOp-event trace, mirroring `exec-flat`'s fuel/fetch dispatch.
  -- D320: the calls AND how the run ended (`Once.Internal.Out`): a halted machine
  -- ends it — `returned` if it left by the Host's `leave` (`c-leave`), `halted`
  -- otherwise — and so does a pc off the code; running out of fuel says nothing.
  flat-events       : ℕ → AbstractTrace → FlatState → Out
  flat-events-step  : Bool → ℕ → AbstractTrace → FlatState → Out
  flat-events-fetch : Maybe AbstractInstr → ℕ → AbstractTrace → FlatState → Out

  flat-events zero    _    fs = cut
  flat-events (suc n) prog fs = flat-events-step (halted (floc fs)) n prog fs

  flat-events-step true  _ _    fs = ended (end-of-left (LocState.left (floc fs)))
  flat-events-step false n prog fs = flat-events-fetch (fetch prog (fpc fs)) n prog fs

  flat-events-fetch nothing  _ _    fs = stop
  flat-events-fetch (just i) n prog fs =
    event-of i fs ▹ flat-events n prog (flat-exec-instr i prog fs)

  -- A HALTED flat state emits nothing, at any fuel — the abstract counterpart of
  -- `RunTraceCore.run-events-halted` / `-stuck`. Used by every "both machines
  -- stop here" correspondence case.
  flat-events-halted : ∀ (n : ℕ) (prog : AbstractTrace) (fs : FlatState)
                     → halted (floc fs) ≡ true → proj₁ (flat-events n prog fs) ≡ []
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
                 → ∀ (fuel : ℕ) (fs : FlatState) → proj₁ (flat-events fuel prog fs) ≡ []
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
                              ≡ chain-events steps ▹ flat-events b prog fs'
  flat-events-steps []                              b = refl
  flat-events-steps (_∷_ {fs = fs} {i = i} (h , f) rest) b
    rewrite h | f =
      trans (cong (event-of i fs ▹_) (flat-events-steps rest b))
            (sym (▹-assoc (event-of i fs) (chain-events rest) (flat-events b _ _)))

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
  -- plan 0.119 D5: the CONTROL steps of a chain — the steps every target
  -- lowers to at least one instruction (a straight-line step may lower to
  -- none). A loop's round ends at a jump, so a run's silent steps are paid
  -- for in control steps (`ValueRealized.progress`).
  ------------------------------------------------------------------------

  ctrl-of : AbstractInstr → ℕ
  ctrl-of mov-to-output = 0
  ctrl-of mov-to-input = 0
  ctrl-of load-indirect = 0
  ctrl-of load-indirect-suc = 0
  ctrl-of (load-from-slot _) = 0
  ctrl-of (store-at-slot _) = 0
  ctrl-of store-indirect = 0
  ctrl-of store-indirect-suc = 0
  ctrl-of (lea-slot _) = 0
  ctrl-of (restore-input _) = 0
  ctrl-of (instr-alloc-stack _) = 0
  ctrl-of (instr-dealloc-stack _) = 0
  ctrl-of (instr-reclaim-to _) = 0
  ctrl-of (instr-push-frame _) = 0
  ctrl-of instr-pop-frame = 0
  ctrl-of instr-call-closure = 0
  ctrl-of (worklist-init _) = 0
  ctrl-of (worklist-push _) = 0
  ctrl-of (worklist-pop _) = 0
  ctrl-of (worklist-check _) = 0
  ctrl-of (instr-sigop _) = 0
  ctrl-of (instr-load-const _ _) = 0
  ctrl-of (instr-load-code-addr _) = 0
  ctrl-of instr-save-closure-reg = 0
  ctrl-of (instr-load-tag-lit _) = 0
  ctrl-of (instr-alloc-heap _) = 0
  ctrl-of (instr-reg-op _) = 0
  ctrl-of (instr-ctrl _) = 1

  ctrl-≤1 : ∀ i → ctrl-of i ≤ 1
  ctrl-≤1 mov-to-output = z≤n
  ctrl-≤1 mov-to-input = z≤n
  ctrl-≤1 load-indirect = z≤n
  ctrl-≤1 load-indirect-suc = z≤n
  ctrl-≤1 (load-from-slot _) = z≤n
  ctrl-≤1 (store-at-slot _) = z≤n
  ctrl-≤1 store-indirect = z≤n
  ctrl-≤1 store-indirect-suc = z≤n
  ctrl-≤1 (lea-slot _) = z≤n
  ctrl-≤1 (restore-input _) = z≤n
  ctrl-≤1 (instr-alloc-stack _) = z≤n
  ctrl-≤1 (instr-dealloc-stack _) = z≤n
  ctrl-≤1 (instr-reclaim-to _) = z≤n
  ctrl-≤1 (instr-push-frame _) = z≤n
  ctrl-≤1 instr-pop-frame = z≤n
  ctrl-≤1 instr-call-closure = z≤n
  ctrl-≤1 (worklist-init _) = z≤n
  ctrl-≤1 (worklist-push _) = z≤n
  ctrl-≤1 (worklist-pop _) = z≤n
  ctrl-≤1 (worklist-check _) = z≤n
  ctrl-≤1 (instr-sigop _) = z≤n
  ctrl-≤1 (instr-load-const _ _) = z≤n
  ctrl-≤1 (instr-load-code-addr _) = z≤n
  ctrl-≤1 instr-save-closure-reg = z≤n
  ctrl-≤1 (instr-load-tag-lit _) = z≤n
  ctrl-≤1 (instr-alloc-heap _) = z≤n
  ctrl-≤1 (instr-reg-op _) = z≤n
  ctrl-≤1 (instr-ctrl _) = s≤s z≤n

  chain-ctrls : ∀ {prog k fs fs'} → FlatSteps prog k fs fs' → ℕ
  chain-ctrls []                    = 0
  chain-ctrls (_∷_ {i = i} _ rest)  = ctrl-of i + chain-ctrls rest

  chain-ctrls-++ : ∀ {prog k₁ k₂ fs₁ fs₂ fs₃}
                     (xs : FlatSteps prog k₁ fs₁ fs₂) (ys : FlatSteps prog k₂ fs₂ fs₃)
                 → chain-ctrls (FlatSteps-++ xs ys) ≡ chain-ctrls xs + chain-ctrls ys
  chain-ctrls-++ []                     ys = refl
  chain-ctrls-++ (_∷_ {i = i} _ xs) ys =
    trans (cong (ctrl-of i +_) (chain-ctrls-++ xs ys)) (sym (+-assoc (ctrl-of i) (chain-ctrls xs) (chain-ctrls ys)))

  chain-ctrls-subst-start : ∀ {prog k fs₁ fs₂ fs'} (eq : fs₁ ≡ fs₂) (stp : FlatSteps prog k fs₁ fs')
                          → chain-ctrls (subst (λ s → FlatSteps prog k s fs') eq stp) ≡ chain-ctrls stp
  chain-ctrls-subst-start refl stp = refl

  -- A chain's control steps are at least those of a part of it.
  ctrls-≤ʳ : ∀ {prog k₁ k₂ fs₁ fs₂ fs₃}
               (xs : FlatSteps prog k₁ fs₁ fs₂) (ys : FlatSteps prog k₂ fs₂ fs₃)
           → chain-ctrls ys ≤ chain-ctrls (FlatSteps-++ xs ys)
  ctrls-≤ʳ xs ys = subst (chain-ctrls ys ≤_) (sym (chain-ctrls-++ xs ys)) (m≤n+m (chain-ctrls ys) (chain-ctrls xs))

  ctrls-≤ˡ : ∀ {prog k₁ k₂ fs₁ fs₂ fs₃}
               (xs : FlatSteps prog k₁ fs₁ fs₂) (ys : FlatSteps prog k₂ fs₂ fs₃)
           → chain-ctrls xs ≤ chain-ctrls (FlatSteps-++ xs ys)
  ctrls-≤ˡ xs ys = subst (chain-ctrls xs ≤_) (sym (chain-ctrls-++ xs ys)) (m≤m+n (chain-ctrls xs) (chain-ctrls ys))

  -- The control steps of a FUELLED run (`flat-events`' shape).
  flat-ctrls       : ℕ → AbstractTrace → FlatState → ℕ
  flat-ctrls-step  : Bool → ℕ → AbstractTrace → FlatState → ℕ
  flat-ctrls-fetch : Maybe AbstractInstr → ℕ → AbstractTrace → FlatState → ℕ
  flat-ctrls zero    _    fs = 0
  flat-ctrls (suc n) prog fs = flat-ctrls-step (halted (floc fs)) n prog fs
  flat-ctrls-step true  _ _    fs = 0
  flat-ctrls-step false n prog fs = flat-ctrls-fetch (fetch prog (fpc fs)) n prog fs
  flat-ctrls-fetch nothing  _ _    fs = 0
  flat-ctrls-fetch (just i) n prog fs = ctrl-of i + flat-ctrls n prog (flat-exec-instr i prog fs)

  -- …which a chain's control steps start.
  flat-ctrls-steps : ∀ {prog k fs fs'} (steps : FlatSteps prog k fs fs')
                   → ∀ b → flat-ctrls (k + b) prog fs ≡ chain-ctrls steps + flat-ctrls b prog fs'
  flat-ctrls-steps []                              b = refl
  flat-ctrls-steps (_∷_ {fs = fs} {i = i} (h , f) rest) b
    rewrite h | f =
      trans (cong (ctrl-of i +_) (flat-ctrls-steps rest b))
            (sym (+-assoc (ctrl-of i) (chain-ctrls rest) (flat-ctrls b _ _)))

  ------------------------------------------------------------------------
  -- Plan 0.105: THE LOG GROWS BY EXACTLY THE EVENTS. A step appends its own
  -- `event-of` to the machine's log (the SigOp step by definition, every other
  -- step leaves it alone — `FlatLog`), so a chain grows the log by its
  -- `chain-events`.
  ------------------------------------------------------------------------

  private
    flog : FlatState → List SigOpEvent
    flog fs = LocState.ev-log (floc fs)

    silent : ∀ (i : AbstractInstr) → LogFree i → ∀ prog fs → event-of i fs ≡ []
           → flog (flat-exec-instr i prog fs) ≡ flog fs ++ event-of i fs
    silent i lf prog fs ev = trans (LP.flat-exec-instr-log i lf prog fs)
                                   (trans (sym (++-identityʳ _)) (cong (flog fs ++_) (sym ev)))

  step-log : ∀ (i : AbstractInstr) → ∀ prog fs
           → flog (flat-exec-instr i prog fs) ≡ flog fs ++ event-of i fs
  step-log SMC.mov-to-output prog fs = silent SMC.mov-to-output tt prog fs refl
  step-log SMC.mov-to-input prog fs = silent SMC.mov-to-input tt prog fs refl
  step-log SMC.load-indirect prog fs = silent SMC.load-indirect tt prog fs refl
  step-log SMC.load-indirect-suc prog fs = silent SMC.load-indirect-suc tt prog fs refl
  step-log (SMC.load-from-slot slot) prog fs = silent (SMC.load-from-slot slot) tt prog fs refl
  step-log (SMC.store-at-slot slot) prog fs = silent (SMC.store-at-slot slot) tt prog fs refl
  step-log SMC.store-indirect prog fs = silent SMC.store-indirect tt prog fs refl
  step-log SMC.store-indirect-suc prog fs = silent SMC.store-indirect-suc tt prog fs refl
  step-log (SMC.lea-slot slot) prog fs = silent (SMC.lea-slot slot) tt prog fs refl
  step-log (SMC.restore-input slot) prog fs = silent (SMC.restore-input slot) tt prog fs refl
  step-log (SMC.instr-alloc-stack n) prog fs = silent (SMC.instr-alloc-stack n) tt prog fs refl
  step-log (SMC.instr-dealloc-stack n) prog fs = silent (SMC.instr-dealloc-stack n) tt prog fs refl
  step-log (SMC.instr-reclaim-to n) prog fs = silent (SMC.instr-reclaim-to n) tt prog fs refl
  step-log (SMC.instr-push-frame cap) prog fs = silent (SMC.instr-push-frame cap) tt prog fs refl
  step-log SMC.instr-pop-frame prog fs = silent SMC.instr-pop-frame tt prog fs refl
  step-log SMC.instr-call-closure prog fs = silent SMC.instr-call-closure tt prog fs refl
  step-log (SMC.worklist-init slot) prog fs = silent (SMC.worklist-init slot) tt prog fs refl
  step-log (SMC.worklist-push slot) prog fs = silent (SMC.worklist-push slot) tt prog fs refl
  step-log (SMC.worklist-pop slot) prog fs = silent (SMC.worklist-pop slot) tt prog fs refl
  step-log (SMC.worklist-check slot) prog fs = silent (SMC.worklist-check slot) tt prog fs refl
  step-log (instr-sigop si)        prog fs = refl
  step-log (SMC.instr-load-const p v) prog fs = silent (SMC.instr-load-const p v) tt prog fs refl
  step-log (SMC.instr-load-code-addr n) prog fs = silent (SMC.instr-load-code-addr n) tt prog fs refl
  step-log SMC.instr-save-closure-reg prog fs = silent SMC.instr-save-closure-reg tt prog fs refl
  step-log (SMC.instr-load-tag-lit n) prog fs = silent (SMC.instr-load-tag-lit n) tt prog fs refl
  step-log (SMC.instr-alloc-heap n) prog fs = silent (SMC.instr-alloc-heap n) tt prog fs refl
  step-log (SMC.instr-reg-op op) prog fs = silent (SMC.instr-reg-op op) tt prog fs refl
  step-log (SMC.instr-ctrl c) prog fs = silent (SMC.instr-ctrl c) tt prog fs refl


  chain-log : ∀ {prog k fs fs'} (r : FlatSteps prog k fs fs')
            → flog fs' ≡ flog fs ++ chain-events r
  chain-log []                                  = sym (++-identityʳ _)
  chain-log {prog} (_∷_ {fs = fs} {i = i} _ rest) =
    trans (chain-log rest)
          (trans (cong (_++ chain-events rest) (step-log i prog fs))
                 (++-assoc (flog fs) (event-of i fs) (chain-events rest)))

  ------------------------------------------------------------------------
  -- D320: A RUN THAT ENDS RUNNING HAS NOT LEFT. Only `c-leave` sets the flag
  -- (`FlatLeft`), and it halts the machine, so no step follows it.
  ------------------------------------------------------------------------
  private
    leave-or-free : ∀ (i : AbstractInstr) → (i ≡ SMC.instr-ctrl SMC.c-leave) ⊎ LeftFree i
    leave-or-free (SMC.instr-ctrl (SMC.c-label _)) = inj₂ tt
    leave-or-free (SMC.instr-ctrl (SMC.c-entry _ _)) = inj₂ tt
    leave-or-free (SMC.instr-ctrl (SMC.c-start _)) = inj₂ tt
    leave-or-free (SMC.instr-ctrl SMC.c-leave) = inj₁ refl
    leave-or-free (SMC.instr-ctrl (SMC.c-call-fn _)) = inj₂ tt
    leave-or-free (SMC.instr-ctrl (SMC.c-ret _)) = inj₂ tt
    leave-or-free (SMC.instr-ctrl (SMC.c-jmp _)) = inj₂ tt
    leave-or-free (SMC.instr-ctrl (SMC.c-branch-tag-zero _)) = inj₂ tt
    leave-or-free SMC.instr-call-closure = inj₂ tt
    leave-or-free SMC.instr-save-closure-reg = inj₂ tt
    leave-or-free (SMC.instr-alloc-stack _) = inj₂ tt
    leave-or-free (SMC.instr-dealloc-stack _) = inj₂ tt
    leave-or-free (SMC.instr-push-frame _) = inj₂ tt
    leave-or-free SMC.instr-pop-frame = inj₂ tt
    leave-or-free SMC.mov-to-output = inj₂ tt
    leave-or-free SMC.mov-to-input = inj₂ tt
    leave-or-free SMC.load-indirect = inj₂ tt
    leave-or-free SMC.load-indirect-suc = inj₂ tt
    leave-or-free (SMC.load-from-slot _) = inj₂ tt
    leave-or-free (SMC.store-at-slot _) = inj₂ tt
    leave-or-free SMC.store-indirect = inj₂ tt
    leave-or-free SMC.store-indirect-suc = inj₂ tt
    leave-or-free (SMC.lea-slot _) = inj₂ tt
    leave-or-free (SMC.restore-input _) = inj₂ tt
    leave-or-free (SMC.instr-reclaim-to _) = inj₂ tt
    leave-or-free (SMC.worklist-init _) = inj₂ tt
    leave-or-free (SMC.worklist-push _) = inj₂ tt
    leave-or-free (SMC.worklist-pop _) = inj₂ tt
    leave-or-free (SMC.worklist-check _) = inj₂ tt
    leave-or-free (SMC.instr-sigop _) = inj₂ tt
    leave-or-free (SMC.instr-load-const _ _) = inj₂ tt
    leave-or-free (SMC.instr-load-code-addr _) = inj₂ tt
    leave-or-free (SMC.instr-load-tag-lit _) = inj₂ tt
    leave-or-free (SMC.instr-alloc-heap _) = inj₂ tt
    leave-or-free (SMC.instr-reg-op _) = inj₂ tt

    leave-halts : ∀ {prog k fs fs'} → halted (floc fs) ≡ true → FlatSteps prog k fs fs' → halted (floc fs') ≡ false → ⊥
    leave-halts h []            hp = true≢false (trans (sym h) hp)
      where true≢false : true ≡ false → ⊥
            true≢false ()
    leave-halts h ((h′ , _) ∷ _) hp = true≢false (trans (sym h) h′)
      where true≢false : true ≡ false → ⊥
            true≢false ()

  chain-left : ∀ {prog k fs fs'} (r : FlatSteps prog k fs fs') → halted (floc fs') ≡ false
             → LocState.left (floc fs') ≡ LocState.left (floc fs)
  chain-left-at : ∀ {prog k fs fs'} (i : AbstractInstr) → (i ≡ SMC.instr-ctrl SMC.c-leave) ⊎ LeftFree i
                → FlatSteps prog k (flat-exec-instr i prog fs) fs' → halted (floc fs') ≡ false
                → LocState.left (floc fs') ≡ LocState.left (floc fs)
  chain-left []                              hp = refl
  chain-left (_∷_ {i = i} _ rest)            hp = chain-left-at i (leave-or-free i) rest hp
  chain-left-at .(SMC.instr-ctrl SMC.c-leave) (inj₁ refl) rest hp = ⊥-elim (leave-halts refl rest hp)
  chain-left-at {prog} {fs = fs} i (inj₂ lf) rest hp = trans (chain-left rest hp) (LL.flat-exec-instr-left i lf prog fs)

  -- A SETTLED state (halted, or nothing to fetch) emits no events for any
  -- fuel — the run is over. (`flat-events`'s first dispatch returns `[]`.)
  flat-events-settled : ∀ (prog : AbstractTrace) (fs : FlatState) (r : ℕ)
                      → (halted (floc fs) ≡ true) ⊎ (fetch prog (fpc fs) ≡ nothing)
                      → proj₁ (flat-events r prog fs) ≡ []
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
                    → proj₁ (flat-events n prog fs) ≡ chain-events (RunReified.chain rr)
  flat-events-reify n prog fs (reified N r fs' ch st fsp) =
    trans (cong (λ m → proj₁ (flat-events m prog fs)) fsp)
          (trans (cong proj₁ (flat-events-steps ch r))
                 (trans (cong (chain-events ch ++_) (flat-events-settled prog fs' r st))
                        (++-identityʳ (chain-events ch))))
