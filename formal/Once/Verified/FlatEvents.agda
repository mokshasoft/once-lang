-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Verified.FlatEvents — the machine SigOp-event trace.
--
-- Plan 0.36 (machine side): `flat-events` is the machine counterpart of
-- the source observable `obs` (Once.Verified.TraceDenote). It mirrors
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
-- FAITHFUL arguments: the Layer-0 observable IS the `linux.exit`
-- argument, so the trace must carry it. `SigOpEvent` coarsens the
-- argument to `ev-argℕ : Maybe ℕ`; `flat-events` decodes the machine's
-- `Input1` (`SV-Lit {Int}` → the ℕ) — a function. `traces-agree` (next)
-- proves this ℕ equals `obs`'s via the per-SigOp value-correspondence.
------------------------------------------------------------------------

module Once.Verified.FlatEvents where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Properties using (++-assoc; ++-identityʳ)
open import Data.Nat using (_+_)
open import Data.Product using (_,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

open import Once.Type using (Int)
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.SigOp.Info using (SigOpInfo; name)
open import Once.CCC.Machine.SMCore
  using (LocState; halted; regs; readReg; Input1;
         StoredValue; SV-Lit;
         AbstractTrace; AbstractInstr; instr-sigop)
open import Once.CCC.Machine.Flat
open import Once.CCC.Codegen.FlatStepLemmas using (module FlatStepsAPI)
open import Once.Verified.Trace using (SigOpEvent; mk-event; isInt?)

module FlatEventTrace {FS : FrameSemantics} where
  open FlatMachine {FS}
  open FlatStepsAPI {FS}

  -- Decode a register cell to a ℕ argument (only `Int` literals decode).
  decode-ℕ : StoredValue FS → Maybe ℕ
  decode-ℕ (SV-Lit {Int} _ v) = just v
  decode-ℕ _                  = nothing

  -- The event a `SigOp` invocation emits, read off the machine: name
  -- from the descriptor, ℕ argument decoded from `Input1` when the
  -- input type is `Int` (matching `mkEvent`'s `isInt?` gate on the
  -- source side, so the two sides can be proven equal).
  machine-event : ∀ {A B} → SigOpInfo A B → StoredValue FS → SigOpEvent
  machine-event {A} si sv with isInt? A
  ... | just _  = mk-event (name si) (decode-ℕ sv)
  ... | nothing = mk-event (name si) nothing

  -- Events emitted by executing one instruction depend on the
  -- instruction + the LOCATION state only (the `Input1` register).
  -- Factored through `floc` so any transform preserving `floc` (e.g. the
  -- relocation `shift-pc`, which only bumps the pc) leaves events
  -- definitionally unchanged — no per-constructor enumeration needed.
  ev-of-loc : AbstractInstr → LocState FS → List SigOpEvent
  ev-of-loc (instr-sigop si) loc = machine-event si (readReg (regs loc) Input1) ∷ []
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
  -- CataNatDescend/CataNatAscend (descend-iter-flat etc.) for the trace,
  -- not just the state. For a SILENT chain (control/reg/load/build-layer
  -- — no `instr-sigop`), `chain-events` reduces to `[]` definitionally,
  -- so `flat-events` simply skips it to the chain's end state.
  ----------------------------------------------------------------------
  chain-events : ∀ {prog k fs fs'} → FlatSteps prog k fs fs' → List SigOpEvent
  chain-events []                            = []
  chain-events (_∷_ {fs = fs} {i = i} _ rest) = event-of i fs ++ chain-events rest

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
