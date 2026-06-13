-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.CCC.Codegen.CataNatAscend — the strat-nat cata ASCEND phase's
-- CONTROL wrappers, toward discharging `cata-correct` (IRObsCorrectFlat).
--
-- The ascend loop (cata-trace-nat) is
--   c-label la-top ∷ c-branch-scratch-zero la-end ∷
--   (ascend-body ++ (c-jmp la-top ∷ c-label la-end ∷ []))
-- where `ascend-body = mov-to-input ∷ build-layer 1 ++ (mov-to-input ∷ at
-- ++ (scratch-dec ∷ []))`. Each continue iteration rebuilds one `inr`
-- layer and runs the algebra `at`, decrementing the depth counter.
--
-- This module builds the iteration's PRE-control (`c-label la-top` +
-- `c-branch-scratch-zero la-end` NOT taken, i.e. depth ≠ 0) and the
-- POST-control (`c-jmp la-top`, loop back), via the same `flat-step1` +
-- label-resolution-fact idiom as `CataNatDescend`. This isolates the
-- remaining semantic gap to the iteration's MIDDLE (`build-layer` block +
-- the abstract algebra trace `at`, which carries the SigOp content) — the
-- crux of `traces-agree`, deferred to the `at`-semantics build.
------------------------------------------------------------------------

module Once.CCC.Codegen.CataNatAscend where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Bool using (true; false)
open import Data.Maybe using (just)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Data.List using (List; []; _++_)
open import Data.List.Properties using (++-identityʳ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)

open import Once.Verified.Trace using (SigOpEvent)
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.SMCore
  using (halted; regs; readReg; Scratch; SV-Tag; AbstractTrace;
         mov-to-input; instr-reg-op; scratch-dec; scratch-load-count; instr-load-tag-lit;
         instr-ctrl; c-label; c-jmp; c-branch-scratch-zero)
open import Once.CCC.Machine.Flat using (module FlatMachine)
open import Once.CCC.Codegen.FlatStepLemmas using (module FlatStepsAPI)
open import Once.Verified.FlatEvents using (module FlatEventTrace)

module CataNatAscend {FS : FrameSemantics} where
  open FlatMachine {FS}
  open FlatStepsAPI {FS}
  open FlatEventTrace {FS}

  -- The ascend iteration's PRE-control (continue path, depth ≠ 0):
  -- `c-label la-top` (loop head) then `c-branch-scratch-zero la-end` NOT
  -- taken. Both touch only `fpc`; state stays `fs`, pc advances 2×. The
  -- branch condition is over the VARIABLE `floc fs`, so it transfers to
  -- the post-label state definitionally.
  ascend-pre-flat : ∀ (prog : AbstractTrace) (fs : FlatState) (la-top la-end : ℕ)
    → halted (floc fs) ≡ false
    → sv-is-zero (readReg (regs (floc fs)) Scratch) ≡ false
    → fetch prog (fpc fs)       ≡ just (instr-ctrl (c-label la-top))
    → fetch prog (suc (fpc fs)) ≡ just (instr-ctrl (c-branch-scratch-zero la-end))
    → FlatSteps prog 2 fs (record fs { fpc = suc (suc (fpc fs)) })
  ascend-pre-flat prog fs la-top la-end hf scond fL fB =
    FlatSteps-++
      (flat-step1 hf fL (flat-label               prog fs la-top))
      (flat-step1 hf fB (flat-scratch-branch-not  prog _  la-end scond))

  -- The ascend iteration's POST-control: `c-jmp la-top` (loop back). The
  -- jump resolves via `find-label`, so it is parameterized over the
  -- resolution fact (`find-label prog la-top ≡ just q-latop`); result pc =
  -- `q-latop` (the resolved loop head) — the fixpoint the descending-depth
  -- induction folds over. State stays `fs` (the jump touches only `fpc`).
  ascend-post-flat : ∀ (prog : AbstractTrace) (fs : FlatState) (la-top q-latop : ℕ)
    → halted (floc fs) ≡ false
    → fetch prog (fpc fs)    ≡ just (instr-ctrl (c-jmp la-top))
    → find-label prog la-top ≡ just q-latop
    → FlatSteps prog 1 fs (record fs { fpc = q-latop })
  ascend-post-flat prog fs la-top q-latop hf fJ top-res =
    flat-step1 hf fJ (trans (flat-jmp prog fs la-top)
                            (cong (λ m → do-jump m fs) top-res))

  -- The ascend iteration's BODY runs as one FlatSteps chain:
  --   mov-to-input ∷ build-layer 1 (10) ∷ mov-to-input ∷ at (N) ∷ scratch-dec
  -- The build-layer run (`bl-steps` + its completion `bl-halted`) and the
  -- algebra run (`at-chain`, ending non-halted at the scratch-dec position,
  -- since spliced `at` flows on rather than halting) are taken as decoupled
  -- hypotheses — the caller supplies them via `build-layer-runs` and
  -- `at-relocated-emits`. The two movs (set Input1 := the accumulator, then
  -- Input1 := the freshly-built layer node) and scratch-dec are straight
  -- non-halting steps; `halted` threads from `fs` through `bl-halted` and
  -- `at-end-nh`. `blf` is the build-layer result state; `S12` the post-2nd-
  -- mov state at which `at` starts.
  ascend-body-runs : ∀ (prog : AbstractTrace) (fs blf : FlatState) {N : ℕ} {at-end : FlatState}
                       (E : List SigOpEvent)
    → halted (floc fs) ≡ false
    → fetch prog (fpc fs) ≡ just mov-to-input
    → (bl-steps : FlatSteps prog 10 (flat-exec-instr mov-to-input prog fs) blf)
    → chain-events bl-steps ≡ []
    → halted (floc blf) ≡ false
    → fetch prog (fpc blf) ≡ just mov-to-input
    → (at-chain : FlatSteps prog N (flat-exec-instr mov-to-input prog blf) at-end)
    → chain-events at-chain ≡ E
    → halted (floc at-end) ≡ false
    → fetch prog (fpc at-end) ≡ just (instr-reg-op scratch-dec)
    → Σ[ n ∈ ℕ ] Σ[ final ∈ FlatState ]
        Σ[ steps ∈ FlatSteps prog n fs final ] (chain-events steps ≡ E)
  ascend-body-runs prog fs blf E hf mov1 bl-steps bl-silent bl-halted mov2 at-chain at-events at-end-nh scrd =
    _ , _ , chain , events
    where
      mov1L = (hf , mov1) ∷ []
      mov2L = (bl-halted , mov2) ∷ []
      scrL  = (at-end-nh , scrd) ∷ []
      R3    = FlatSteps-++ at-chain scrL
      R2    = FlatSteps-++ mov2L R3
      R1    = FlatSteps-++ bl-steps R2
      chain = FlatSteps-++ mov1L R1
      -- the two movs + scratch-dec emit nothing (event-of of a non-sigop
      -- reduces to [] definitionally), build-layer is silent by hypothesis,
      -- and the algebra `at` contributes exactly E.
      ev-R3 : chain-events R3 ≡ E
      ev-R3 = trans (chain-events-++ at-chain scrL)
                    (trans (++-identityʳ (chain-events at-chain)) at-events)
      ev-R2 : chain-events R2 ≡ E
      ev-R2 = trans (chain-events-++ mov2L R3) ev-R3
      ev-R1 : chain-events R1 ≡ E
      ev-R1 = trans (chain-events-++ bl-steps R2)
                    (trans (cong (_++ chain-events R2) bl-silent) ev-R2)
      events : chain-events chain ≡ E
      events = trans (chain-events-++ mov1L R1) ev-R1

  ----------------------------------------------------------------------
  -- One full ascend ITERATION = pre-control (label + branch-not) ++ body
  -- ++ post-control (jmp back to head). The control wraps are silent, so
  -- the iteration's events = the body's events = E.
  ----------------------------------------------------------------------

  -- generic silence helpers (a control/reg step emits nothing).
  step1-silent : ∀ {prog fs fs'} {i} (h : halted (floc fs) ≡ false)
                   (f : fetch prog (fpc fs) ≡ just i) (eq : flat-exec-instr i prog fs ≡ fs')
               → event-of i fs ≡ [] → chain-events (flat-step1 h f eq) ≡ []
  step1-silent {fs = fs} {i = i} h f eq ev =
    trans (chain-events-subst eq ((h , f) ∷ [])) (cong (_++ []) ev)

  ++-silent : ∀ {prog k₁ k₂ fs₁ fs₂ fs₃}
                (xs : FlatSteps prog k₁ fs₁ fs₂) (ys : FlatSteps prog k₂ fs₂ fs₃)
            → chain-events xs ≡ [] → chain-events ys ≡ []
            → chain-events (FlatSteps-++ xs ys) ≡ []
  ++-silent xs ys px py =
    trans (chain-events-++ xs ys) (trans (cong (_++ chain-events ys) px) py)

  -- The ascend pre-control (label la-top + branch-scratch-zero not taken)
  -- is silent.
  ascend-pre-silent : ∀ (prog : AbstractTrace) (fs : FlatState) (la-top la-end : ℕ)
    → (hf : halted (floc fs) ≡ false)
    → (scond : sv-is-zero (readReg (regs (floc fs)) Scratch) ≡ false)
    → (fL : fetch prog (fpc fs)       ≡ just (instr-ctrl (c-label la-top)))
    → (fB : fetch prog (suc (fpc fs)) ≡ just (instr-ctrl (c-branch-scratch-zero la-end)))
    → chain-events (ascend-pre-flat prog fs la-top la-end hf scond fL fB) ≡ []
  ascend-pre-silent prog fs la-top la-end hf scond fL fB =
    ++-silent (flat-step1 {prog = prog} hf fL eqL) (flat-step1 {prog = prog} hf fB eqB)
      (step1-silent {prog = prog} hf fL eqL refl)
      (step1-silent {prog = prog} {fs = record fs { fpc = suc (fpc fs) }} hf fB eqB refl)
    where
      eqL = flat-label              prog fs la-top
      eqB = flat-scratch-branch-not prog (record fs { fpc = suc (fpc fs) }) la-end scond

  -- The ascend post-control (jmp back to la-top) is silent.
  ascend-post-silent : ∀ (prog : AbstractTrace) (fs : FlatState) (la-top q-latop : ℕ)
    → (hf : halted (floc fs) ≡ false)
    → (fJ : fetch prog (fpc fs)    ≡ just (instr-ctrl (c-jmp la-top)))
    → (top-res : find-label prog la-top ≡ just q-latop)
    → chain-events (ascend-post-flat prog fs la-top q-latop hf fJ top-res) ≡ []
  ascend-post-silent prog fs la-top q-latop hf fJ top-res =
    step1-silent {prog = prog} hf fJ
      (trans (flat-jmp prog fs la-top) (cong (λ m → do-jump m fs) top-res)) refl

  -- The ascend EXIT (Scratch = 0): `c-label la-top` then `c-branch-
  -- scratch-zero la-end` TAKEN, jumping to the resolved loop-end. This is
  -- the loop's base case (depth 0 = the fold is done). State stays `fs`
  -- (control only); ends at `q-laend`.
  ascend-exit-flat : ∀ (prog : AbstractTrace) (fs : FlatState) (la-top la-end q-laend : ℕ)
    → halted (floc fs) ≡ false
    → sv-is-zero (readReg (regs (floc fs)) Scratch) ≡ true
    → fetch prog (fpc fs)       ≡ just (instr-ctrl (c-label la-top))
    → fetch prog (suc (fpc fs)) ≡ just (instr-ctrl (c-branch-scratch-zero la-end))
    → find-label prog la-end ≡ just q-laend
    → FlatSteps prog 2 fs (record fs { fpc = q-laend })
  ascend-exit-flat prog fs la-top la-end q-laend hf scond fL fB end-res =
    FlatSteps-++ (flat-step1 hf fL (flat-label prog fs la-top))
                 (flat-step1 hf fB
                   (trans (flat-scratch-branch-yes prog (record fs { fpc = suc (fpc fs) }) la-end scond)
                          (cong (λ m → do-jump m (record fs { fpc = suc (fpc fs) })) end-res)))

  ascend-exit-silent : ∀ (prog : AbstractTrace) (fs : FlatState) (la-top la-end q-laend : ℕ)
    → (hf : halted (floc fs) ≡ false)
    → (scond : sv-is-zero (readReg (regs (floc fs)) Scratch) ≡ true)
    → (fL : fetch prog (fpc fs)       ≡ just (instr-ctrl (c-label la-top)))
    → (fB : fetch prog (suc (fpc fs)) ≡ just (instr-ctrl (c-branch-scratch-zero la-end)))
    → (end-res : find-label prog la-end ≡ just q-laend)
    → chain-events (ascend-exit-flat prog fs la-top la-end q-laend hf scond fL fB end-res) ≡ []
  ascend-exit-silent prog fs la-top la-end q-laend hf scond fL fB end-res =
    ++-silent (flat-step1 {prog = prog} hf fL eqL) (flat-step1 {prog = prog} hf fB eqB)
      (step1-silent {prog = prog} hf fL eqL refl)
      (step1-silent {prog = prog} {fs = record fs { fpc = suc (fpc fs) }} hf fB eqB refl)
    where
      eqL = flat-label prog fs la-top
      eqB = trans (flat-scratch-branch-yes prog (record fs { fpc = suc (fpc fs) }) la-end scond)
                  (cong (λ m → do-jump m (record fs { fpc = suc (fpc fs) })) end-res)

  -- One continue iteration runs (pre ++ body ++ post) and emits exactly
  -- the body's events E; it ends back at the loop head `q-latop`, non-
  -- halted, ready for the next iteration. The body run is a hypothesis
  -- (supplied via `ascend-body-runs`).
  ascend-iter-runs : ∀ (prog : AbstractTrace) (fs : FlatState) (la-top la-end q-latop : ℕ)
                       {N : ℕ} {final-body : FlatState} (E : List SigOpEvent)
    → halted (floc fs) ≡ false
    → sv-is-zero (readReg (regs (floc fs)) Scratch) ≡ false
    → fetch prog (fpc fs)       ≡ just (instr-ctrl (c-label la-top))
    → fetch prog (suc (fpc fs)) ≡ just (instr-ctrl (c-branch-scratch-zero la-end))
    → (body-steps : FlatSteps prog N (record fs { fpc = suc (suc (fpc fs)) }) final-body)
    → chain-events body-steps ≡ E
    → halted (floc final-body) ≡ false
    → fetch prog (fpc final-body) ≡ just (instr-ctrl (c-jmp la-top))
    → find-label prog la-top ≡ just q-latop
    → Σ[ n ∈ ℕ ] Σ[ final ∈ FlatState ]
        Σ[ steps ∈ FlatSteps prog n fs final ] (chain-events steps ≡ E × halted (floc final) ≡ false)
  ascend-iter-runs prog fs la-top la-end q-latop E hf scond fL fB
                   body-steps body-events body-halted fJ top-res =
    _ , _ , chain , events , body-halted
    where
      PRE   = ascend-pre-flat  prog fs la-top la-end hf scond fL fB
      POST  = ascend-post-flat prog _ la-top q-latop body-halted fJ top-res
      chain = FlatSteps-++ PRE (FlatSteps-++ body-steps POST)
      ev-bp : chain-events (FlatSteps-++ body-steps POST) ≡ E
      ev-bp = trans (chain-events-++ body-steps POST)
                    (trans (cong (chain-events body-steps ++_)
                                 (ascend-post-silent prog _ la-top q-latop body-halted fJ top-res))
                           (trans (++-identityʳ (chain-events body-steps)) body-events))
      events : chain-events chain ≡ E
      events = trans (chain-events-++ PRE (FlatSteps-++ body-steps POST))
                     (trans (cong (_++ chain-events (FlatSteps-++ body-steps POST))
                                  (ascend-pre-silent prog fs la-top la-end hf scond fL fB))
                            ev-bp)

  ----------------------------------------------------------------------
  -- The ASCEND LOOP: μ-induction over the depth counter `Scratch = SV-Tag
  -- n`, chaining `n` continue iterations then the exit. Each iteration's
  -- run is supplied by `step` (the caller builds it from `ascend-iter-runs`
  -- + the algebra IH); `step k` consumes one layer (Scratch SV-Tag (suc k)
  -- → SV-Tag k) emitting that layer's events `E k`. The loop accumulates
  -- `loop-events E n = E (n-1) ++ … ++ E 0` — the fold's events in
  -- innermost-first order, matching `obs(Cata)`'s post-order fold.
  ----------------------------------------------------------------------

  loop-events : (ℕ → List SigOpEvent) → ℕ → List SigOpEvent
  loop-events E zero    = []
  loop-events E (suc k) = E k ++ loop-events E k

  ascend-loop-runs : ∀ (prog : AbstractTrace) (la-top la-end qh q-laend : ℕ)
                       (E : ℕ → List SigOpEvent)
    → (step : ∀ (k : ℕ) (entry : FlatState)
              → halted (floc entry) ≡ false
              → readReg (regs (floc entry)) Scratch ≡ SV-Tag (suc k)
              → fpc entry ≡ qh
              → Σ[ exit ∈ FlatState ] Σ[ m ∈ ℕ ] Σ[ steps ∈ FlatSteps prog m entry exit ]
                  (chain-events steps ≡ E k × halted (floc exit) ≡ false
                   × readReg (regs (floc exit)) Scratch ≡ SV-Tag k × fpc exit ≡ qh))
    → fetch prog qh       ≡ just (instr-ctrl (c-label la-top))
    → fetch prog (suc qh) ≡ just (instr-ctrl (c-branch-scratch-zero la-end))
    → find-label prog la-end ≡ just q-laend
    → ∀ (n : ℕ) (fs : FlatState)
    → halted (floc fs) ≡ false
    → readReg (regs (floc fs)) Scratch ≡ SV-Tag n
    → fpc fs ≡ qh
    → Σ[ final ∈ FlatState ] Σ[ m ∈ ℕ ] Σ[ steps ∈ FlatSteps prog m fs final ]
        (chain-events steps ≡ loop-events E n × fpc final ≡ q-laend)
  ascend-loop-runs prog la-top la-end qh q-laend E step fLq fBq end-res zero fs hf scr fpc-eq =
    record fs { fpc = q-laend } , 2 , exit-steps , exit-silent , refl
    where
      scond : sv-is-zero (readReg (regs (floc fs)) Scratch) ≡ true
      scond = cong sv-is-zero scr
      fL : fetch prog (fpc fs)       ≡ just (instr-ctrl (c-label la-top))
      fL = subst (λ p → fetch prog p       ≡ just (instr-ctrl (c-label la-top)))            (sym fpc-eq) fLq
      fB : fetch prog (suc (fpc fs)) ≡ just (instr-ctrl (c-branch-scratch-zero la-end))
      fB = subst (λ p → fetch prog (suc p) ≡ just (instr-ctrl (c-branch-scratch-zero la-end))) (sym fpc-eq) fBq
      exit-steps  = ascend-exit-flat   prog fs la-top la-end q-laend hf scond fL fB end-res
      exit-silent = ascend-exit-silent prog fs la-top la-end q-laend hf scond fL fB end-res
  ascend-loop-runs prog la-top la-end qh q-laend E step fLq fBq end-res (suc k) fs hf scr fpc-eq =
    let (exit , m , steps , ev , he , se , fe) = step k fs hf scr fpc-eq
        (final , m' , steps' , ev' , fpc-final) =
          ascend-loop-runs prog la-top la-end qh q-laend E step fLq fBq end-res k exit he se fe
    in final , m + m' , FlatSteps-++ steps steps'
       , trans (chain-events-++ steps steps') (cong₂ _++_ ev ev')
       , fpc-final

  ----------------------------------------------------------------------
  -- The BASE phase (between descend and ascend, IRToTrace:199):
  --   scratch-load-count ∷ instr-load-tag-lit 0 ∷ mov-to-input ∷
  --   build-layer 0 ∷ mov-to-input ∷ at
  -- It sets `Scratch := Input2` (the depth count → SV-Tag n), builds the
  -- base layer node `[0, SV-Tag 0]` (tag-0, the inl/base), and runs the
  -- algebra `at` on it → Output = alg(base), emitting `E_base`. Control
  -- then flows into the ascend loop (the `at`-chain ends at the loop head).
  -- Structurally like `ascend-body-runs` minus the scratch-dec, with the
  -- scratch-load-count + load-tag prefix; the three prefix reg/mov steps,
  -- build-layer, and the post-build mov are all silent, so the base phase
  -- emits exactly E_base.
  base-phase-runs : ∀ (prog : AbstractTrace) (fs blf : FlatState) {N : ℕ} {at-end : FlatState}
                      (E : List SigOpEvent)
    → halted (floc fs) ≡ false
    → fetch prog (fpc fs)             ≡ just (instr-reg-op scratch-load-count)
    → fetch prog (suc (fpc fs))       ≡ just (instr-load-tag-lit 0)
    → fetch prog (suc (suc (fpc fs))) ≡ just mov-to-input
    → (bl-steps : FlatSteps prog 10
        (flat-exec-instr mov-to-input prog
          (flat-exec-instr (instr-load-tag-lit 0) prog
            (flat-exec-instr (instr-reg-op scratch-load-count) prog fs))) blf)
    → chain-events bl-steps ≡ []
    → halted (floc blf) ≡ false
    → fetch prog (fpc blf) ≡ just mov-to-input
    → (at-chain : FlatSteps prog N (flat-exec-instr mov-to-input prog blf) at-end)
    → chain-events at-chain ≡ E
    → Σ[ n ∈ ℕ ] Σ[ final ∈ FlatState ]
        Σ[ steps ∈ FlatSteps prog n fs final ] (chain-events steps ≡ E)
  base-phase-runs prog fs blf E hf fSc fT fM1 bl-steps bl-silent bl-halted fM2 at-chain at-events =
    _ , _ , chain , events
    where
      L1 = (hf , fSc) ∷ []
      L2 = (hf , fT)  ∷ []
      L3 = (hf , fM1) ∷ []
      L4 = (bl-halted , fM2) ∷ []
      R4 = FlatSteps-++ L4 at-chain
      R3 = FlatSteps-++ bl-steps R4
      R2 = FlatSteps-++ L3 R3
      R1 = FlatSteps-++ L2 R2
      chain = FlatSteps-++ L1 R1
      ev-R4 : chain-events R4 ≡ E
      ev-R4 = trans (chain-events-++ L4 at-chain) at-events
      ev-R3 : chain-events R3 ≡ E
      ev-R3 = trans (chain-events-++ bl-steps R4)
                    (trans (cong (_++ chain-events R4) bl-silent) ev-R4)
      ev-R2 : chain-events R2 ≡ E
      ev-R2 = trans (chain-events-++ L3 R3) ev-R3
      ev-R1 : chain-events R1 ≡ E
      ev-R1 = trans (chain-events-++ L2 R2) ev-R2
      events : chain-events chain ≡ E
      events = trans (chain-events-++ L1 R1) ev-R1
