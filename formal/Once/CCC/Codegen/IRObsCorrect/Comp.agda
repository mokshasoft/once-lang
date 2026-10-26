-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.IRObsCorrect.Comp
--
-- D200: composition — `g ∘ f` runs `f`'s fragment, hands its result to `g`
-- as an input residence (`result→input`), and concatenates the chains.
------------------------------------------------------------------------

open import Once.Spec.Name using (CanonicalName)
import Once.CCC.Machine.SMCore as SMCore

import Data.List as DL
open import Once.Denotation.Program using (IRFun)
module Once.CCC.Codegen.IRObsCorrect.Comp (o : CanonicalName) (tbl : DL.List IRFun) where

open import Once.CCC.Codegen.IRObsCorrect.Machine o tbl
open import Once.CCC.Codegen.FlatStepLemmas using (module FlatStepsAPI)
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.Locations using (AtStack; AtDynamic; ValueLocation)
open import Once.CCC.Machine.SMCore using (LocState; readReg; Input1; Output; AbstractTrace; mov-to-input; writeReg-same; module LocState; module AllocState)
open AllocState using (next-slot)
open LocState using (regs; halted)
open import Once.Internal.Event using (SigOpEvent)
open import Once.CCC.Codegen.LabelResolve o using (module Resolve)
open import Once.CCC.Codegen.LabelScope o using (labels-in)
open import Once.CCC.Label using (module LabelId)
open LabelId using (idx)
open import Data.Nat.Properties using (1+n≰n)

import Once.CCC.FrameSemantics
import Once.CCC.Machine.SMPrimitives
import Once.IRTy
import Once.IR
import Once.Semantics.Machine as EvV
import Once.CCC.Machine.ReadTypedAdequate as RTA
import Once.Denotation.DenotTrace as DT
import Once.Denotation.ValueDomain as ValueDomain
import Once.Internal.Trace as TM
open import Once.Denotation.Approx using (Ap; done; cut; NotCut; budgetLeft; thenAp; run-approx-bind)
open import Data.Nat.Properties using (+-monoʳ-≤)
open import Once.Internal.Res using (Res; stopped; returns; is-stopped)

module CompC {FS : FrameSemantics} where

  open Core {FS}
  open Resolve {FS} using (found-in-window; noLabel-outside; NoLabel)
  open FlatStepsAPI {FS} using (fl-go-skip; fl-go-shift; fl-go-prefix)

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
    -- D158: still fragment-local on the RIGHT (the events of `g ∘ f` run
    -- alone), which is the staged half — `value-realized` moved to the
    -- program-indexed form and this must follow, bounded by the chain rather
    -- than by a fuel, or it over-collects the successor's events.


  -- D158: the hand-over state, as a RECORD EQUATION — and with NO shift. Both
  -- fragments run in the SAME program, so `g`'s entry pc is simply where `f`
  -- left off plus the bridge, and the sequel's entry state IS the state the
  -- bridge produced. This is what quantifying over placement buys: the
  -- relocation that D156's version needed here has nothing left to do.
  handover-eq : ∀ (b : ℕ) (fs : FlatState) (rs : List ℕ)
              → fpc fs ≡ b → fret fs ≡ rs → flink fs ≡ nothing
              → fs ≡ entry-flat b (floc fs) (falloc fs) (fclosure fs) rs
  handover-eq b (mkFlatFull lo al pc rt cls lk) _ refl refl refl = refl

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

  -- plan 0.91 S2: the BLOCK channel splits the same way, and more simply.
  -- `ir-to-trace' n l (g ∘ f)` concatenates the two block lists literally
  -- (`… , (ft ++ mov-to-input ∷ gt) , (fb ++ gb)`, IRToTrace:772), so unlike
  -- the trace — where `g` sits past a bridge instruction — both halves come
  -- straight off one `++⁻`. `g`'s blocks are emitted at `f`'s output frontier
  -- and label base, the same `n1`/`l1` the span split uses.
  comp-blocks-f : ∀ {A B C} (g : IR B C) (f : IR A B) (prog : AbstractTrace) (n l : ℕ)
                → BlocksAt prog (blocks n l (g ∘ f))
                → BlocksAt prog (blocks n l f)
  comp-blocks-f g f prog n l bl = proj₁ (++⁻ (blocks n l f) bl)

  -- plan 0.88: THE LABEL CHANNEL SPLITS TOO, and unlike the block channel it
  -- is not a `++⁻`. `f`'s labels resolve inside its own PREFIX, so the
  -- composite's resolution of them is the same scan (`label-prefix`); `g`'s
  -- sit past the bridge, so the scan must first MISS `ft` — and that is where
  -- the windows are spent. A label `gt` resolves is in `g`'s window `[l1,l2)`
  -- by `found-in-window`, and `f`'s labels are all below `l1`, so
  -- `noLabel-outside` applies.
  comp-labels-f : ∀ {A B C} (g : IR B C) (f : IR A B) (prog : AbstractTrace) (base n l : ℕ)
                → LabelsAt prog base (emitted n l (g ∘ f))
                → LabelsAt prog base (emitted n l f)
  comp-labels-f g f prog base n l la m j eq =
    la m j (fl-go-prefix (emitted n l f)
              (mov-to-input ∷ emitted (proj₁ (ir-to-trace' n l f))
                                      (proj₁ (proj₂ (ir-to-trace' n l f))) g)
              m 0 j eq)

  comp-labels-g : ∀ {A B C} (g : IR B C) (f : IR A B) (prog : AbstractTrace) (base n l : ℕ)
                → LabelsAt prog base (emitted n l (g ∘ f))
                → LabelsAt prog (suc (length (emitted n l f) + base))
                          (emitted (proj₁ (ir-to-trace' n l f))
                                   (proj₁ (proj₂ (ir-to-trace' n l f))) g)
  comp-labels-g {A} {B} {C} g f prog base n l la m j eq =
    subst (λ z → find-label prog m ≡ just z) assoc
          (la m (j + suc (length ft)) scan)
    where
      ft = emitted n l f
      n1 = proj₁ (ir-to-trace' n l f)
      l1 = proj₁ (proj₂ (ir-to-trace' n l f))
      gt = emitted n1 l1 g

      -- `m` is one of `g`'s, so it is at or above `l1`…
      inW : l1 ≤ idx m
      inW = proj₁ (found-in-window gt m j eq (labels-in g n1 l1))

      -- …and `f`'s are all below `l1`, so the scan passes `ft` untouched.
      noF : NoLabel m ft
      noF = noLabel-outside m ft (labels-in f n l)
              (λ w → 1+n≰n (≤-trans (proj₂ w) inW))

      shiftEq : fl-go gt m (0 + suc (length ft)) ≡ just (j + suc (length ft))
      shiftEq = trans (fl-go-shift gt m (suc (length ft)) 0) (cong (mmap (_+ suc (length ft))) eq)

      scan : find-label (ft ++ mov-to-input ∷ gt) m ≡ just (j + suc (length ft))
      scan = trans (fl-go-skip ft (mov-to-input ∷ gt) m 0 noF) shiftEq

      assoc : (j + suc (length ft)) + base ≡ j + suc (length ft + base)
      assoc = +-assoc j (suc (length ft)) base

  comp-blocks-g : ∀ {A B C} (g : IR B C) (f : IR A B) (prog : AbstractTrace) (n l : ℕ)
                → BlocksAt prog (blocks n l (g ∘ f))
                → BlocksAt prog (blocks (proj₁ (ir-to-trace' n l f))
                                        (proj₁ (proj₂ (ir-to-trace' n l f))) g)
  comp-blocks-g g f prog n l bl = proj₂ (++⁻ (blocks n l f) bl)

  -- ══════════════════════════════════════════════════════════════════════
  -- D158: `comp-value-realized`, ASSEMBLED — and now unconditionally.
  --
  -- D156 proved this modulo two splice agreements, and D157 showed the call
  -- case of those is refutable: a fragment-local witness cannot describe a
  -- call that leaves the fragment. Quantifying over placement (D158) removes
  -- the question rather than answering it — `f` and `g` are witnessed IN THE SAME
  -- PROGRAM, at `base` and at `base + length ft + 1`, so there is no second
  -- program for their scans to disagree with. `find-thunk prog blbl` is the same
  -- scan on both sides, which is exactly what `apply ∘ curry body` needs.
  -- ══════════════════════════════════════════════════════════════════════
  comp-value-realized-of :
    ∀ {A B C} {g : IR B C} {f : IR A B} {x : ⟦ A ⟧} {s alloc cl rs}
      (prog : AbstractTrace) (base n l k : ℕ)
    → next-slot alloc ≤ n
    → AllSlotStable prog
    → BlockRuns prog
    → SpanAt prog base (emitted n l (g ∘ f))
    -- plan 0.91 S2: and the program implements the composite's blocks — which
    -- are exactly `f`'s followed by `g`'s.
    → BlocksAt prog (blocks n l (g ∘ f))
    -- plan 0.88: …and the program's resolution of the composite's labels.
    → LabelsAt prog base (emitted n l (g ∘ f))
    → IRObsCorrectF g → MachineRefinesObsF prog base n l f x s alloc cl rs k
    → MachineRefinesObsF prog base n l (g ∘ f) x s alloc cl rs k
  comp-value-realized-of {B = B} {C} {g = g} {f} {x} {s} {alloc} {cl} {rs} prog base n l k ns ss cr span bl la ihg mf =
    go (resultAt s (⟪ evalᴰ f x ⟫ k)) refl
       (MachineRefinesObsF.value-realized mf) (MachineRefinesObsF.traces-agree mf)
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

      -- plan 0.105: `g ∘ f` means `evalᴰ f x >>=∞ evalᴰ g`, and the budgeted RUN
      -- of a bind is the budgeted runs of its parts with the history threaded
      -- (`run-approx-bind`, plan 0.119 D5): `g` runs from the composite's entry
      -- log followed by `f`'s calls, AT THE BUDGET `f` LEFT. `f`'s `log` field
      -- says the machine is at exactly that log when `g` starts.
      h : DL.List SigOpEvent
      h = SMCore.LocState.ev-log s

      esF : DL.List SigOpEvent
      esF = eventsAt s (⟪ evalᴰ f x ⟫ k)

      comp-run : ∀ (ρ : Res (Ap ValueDomain.⟦ B ⟧ᴰᴵ)) → resultAt s (⟪ evalᴰ f x ⟫ k) ≡ ρ
               → runAt s (⟪ evalᴰ (g ∘ f) x ⟫ k) ≡ thenAp ιᶠ h esF ρ (evalᴰ g)
      comp-run ρ rfeq = trans (run-approx-bind ιᶠ h k (evalᴰ f x) (evalᴰ g))
                              (cong (λ ρ′ → thenAp ιᶠ h esF ρ′ (evalᴰ g)) rfeq)

      -- D203: `go` builds BOTH halves, split on `f`'s budgeted RESULT (plan
      -- 0.98, 0.119 D5): `done vf r′` binds the value `g` consumes and the
      -- budget it runs at; `stopped` and `cut` mean `g` never runs and the
      -- composite's machine run IS `f`'s. Taken as an ARGUMENT with its own
      -- equation rather than `with`-abstracted.
      go : (ρ : Res (Ap ValueDomain.⟦ B ⟧ᴰᴵ)) → resultAt s (⟪ evalᴰ f x ⟫ k) ≡ ρ
         → (vr : ValueRealized prog base n l f x s alloc cl rs k)
         → chain-events (VR.run vr) ≡ eventsAt s (⟪ evalᴰ f x ⟫ k)
         → MachineRefinesObsF prog base n l (g ∘ f) x s alloc cl rs k
      -- ── `f` RAN TO ITS END ────────────────────────────────────────────
      go (returns (done vf r′)) rfeq
         (realized kf fsF mOutf caf chainF liveF endF stopsF retF linkF logF placeF progF spF hpF cfF bfF) tf =
        record
          { value-realized =
              realized (kf + suc (VR.steps vg)) (VR.settle vg)
                       (VR.out-mode vg) (VR.cont-alloc vg)
                       chain (λ p → VR.live vg (to-g p)) (λ p → atEnd (to-g-res p))
                       (λ p → proj₁ (VR.stops vg (to-g p))
                            , trans (proj₂ (VR.stops vg (to-g p))) (chain-left (FlatSteps-++ chainF movStep) liveM))
                       (λ p → VR.no-ret vg (to-g-res p)) (λ nc → VR.no-link vg (to-g-nc nc))
                       log-comp
                       (λ p → VR.place vg (to-g-res p))
                       (subst (λ ρ → k ≤ budgetLeft k ρ + chain-ctrls chain) (sym res-comp)
                              (progress-bind (resultAt (floc fsM) (⟪ evalᴰ g vf ⟫ r′))
                                             (subst (λ ρ → k ≤ budgetLeft k ρ + chain-ctrls chainF) rfeq progF)
                                             (VR.progress vg) ctrls-comp))
                       (λ nc fr j bf → mem-pres-comp nc (AtStack fr j) bf) (λ nc hl bf → mem-pres-comp nc (AtDynamic hl) bf)
                       (λ p → trans (VR.frame-pres vg (to-g-res p)) (cfF rfeq))
                       bf-mono-comp
          ; traces-agree = traces
          }
        where
          -- `f` returned, so it was not cut.
          ncF : NotCut (resultAt s (⟪ evalᴰ f x ⟫ k))
          ncF = subst NotCut (sym rfeq) tt

          fsM : FlatState
          fsM = flat-exec-instr mov-to-input prog fsF

          runF≡ : exec-flat kf prog (entry-flat base s alloc cl rs) ≡ fsF
          runF≡ = trans (cong (λ m → exec-flat m prog (entry-flat base s alloc cl rs))
                              (sym (+-identityʳ kf)))
                        (exec-flat-steps chainF 0)

          nsF : next-slot (falloc fsF) ≡ next-slot alloc
          nsF = trans (cong (λ st → next-slot (falloc st)) (sym runF≡))
                      (flat-run-keeps-next-slot kf prog ss base s alloc cl rs)

          nsG : next-slot (falloc fsM) ≤ n1
          nsG = ≤-trans (≤-reflexive nsF) (≤-trans ns (frontier-mono f n l))

          -- `f` returned, so `f` did not stop.
          sfeq : stopsAt s (⟪ evalᴰ f x ⟫ k) ≡ false
          sfeq = cong is-stopped rfeq

          liveM : halted (floc fsM) ≡ false
          liveM = liveF sfeq

          movEq : readReg (regs (floc fsM)) Input1 ≡ readReg (regs (floc fsF)) Output
          movEq = writeReg-same (regs (floc fsF)) Input1 (readReg (regs (floc fsF)) Output)

          memEq : ∀ loc → readLoc (floc fsM) loc ≡ readLoc (floc fsF) loc
          memEq loc = reg-write-readLoc (floc fsF) _ (halted (floc fsF)) loc

          inputM : InputAt mOutf (falloc fsM) vf (floc fsM)
          inputM = result→input (placeF rfeq) movEq memEq

          -- `g` runs at the budget `f` left.
          mg : MachineRefinesObsF prog base' n1 l1 g vf
                                  (floc fsM) (falloc fsM) (fclosure fsM) rs r′
          mg = ihg n1 l1 prog base' ss cr span-g
                   (comp-blocks-g g f prog n l bl)
                   (comp-labels-g g f prog base n l la) mOutf vf
                   (floc fsM) (falloc fsM) (fclosure fsM) nsG liveM inputM r′ rs

          vg : ValueRealized prog base' n1 l1 g vf
                             (floc fsM) (falloc fsM) (fclosure fsM) rs r′
          vg = MachineRefinesObsF.value-realized mg

          movStep : FlatSteps prog 1 fsF fsM
          movStep = (liveF sfeq , trans (cong (fetch prog) (endF rfeq)) mov-in-prog) ∷ []

          handover : fsM ≡ entry-flat base' (floc fsM) (falloc fsM) (fclosure fsM) rs
          handover = handover-eq base' fsM rs (cong suc (endF rfeq)) (retF rfeq) (linkF ncF)

          chainG : FlatSteps prog (VR.steps vg) fsM (VR.settle vg)
          chainG = subst (λ st → FlatSteps prog (VR.steps vg) st (VR.settle vg))
                         (sym handover) (VR.run vg)

          chain : FlatSteps prog (kf + suc (VR.steps vg))
                            (entry-flat base s alloc cl rs) (VR.settle vg)
          chain = FlatSteps-++ chainF (FlatSteps-++ movStep chainG)

          -- The composite's control steps cover both parts'.
          ctrls-comp : chain-ctrls chainF + chain-ctrls (VR.run vg) ≤ chain-ctrls chain
          ctrls-comp =
            subst (chain-ctrls chainF + chain-ctrls (VR.run vg) ≤_)
                  (sym (trans (chain-ctrls-++ chainF (FlatSteps-++ movStep chainG))
                              (cong (chain-ctrls chainF +_) (chain-ctrls-++ movStep chainG))))
                  (+-monoʳ-≤ (chain-ctrls chainF)
                     (≤-trans (≤-reflexive (sym (chain-ctrls-subst-start (sym handover) (VR.run vg))))
                              (m≤n+m _ (chain-ctrls movStep))))

          -- ── THE RUN OF `g` IS THE COMPOSITE'S TAIL ─────────────────────
          -- `mov-to-input` leaves the log alone, so `g` starts at `f`'s settle
          -- log, which is `h ++ esF` (`f`'s `log`).
          RG : runAt (floc fsM) (⟪ evalᴰ g vf ⟫ r′) ≡ TM.run ιᶠ (h DL.++ esF) (⟪ evalᴰ g vf ⟫ r′)
          RG = cong (λ hh → TM.run ιᶠ hh (⟪ evalᴰ g vf ⟫ r′)) logF

          CR : runAt s (⟪ evalᴰ (g ∘ f) x ⟫ k) ≡ TM.appE esF (runAt (floc fsM) (⟪ evalᴰ g vf ⟫ r′))
          CR = trans (comp-run (returns (done vf r′)) rfeq) (cong (TM.appE esF) (sym RG))

          evG : DL.List SigOpEvent
          evG = eventsAt (floc fsM) (⟪ evalᴰ g vf ⟫ r′)

          ev-comp : eventsAt s (⟪ evalᴰ (g ∘ f) x ⟫ k) ≡ esF DL.++ evG
          ev-comp = cong proj₁ CR

          -- THE TRACE HALF (D203): the chain is `chainF ++ mov ++ chainG`.
          events-split : chain-events chain ≡ chain-events chainF DL.++ chain-events chainG
          events-split =
            trans (chain-events-++ chainF (FlatSteps-++ movStep chainG))
                  (cong (chain-events chainF DL.++_) (chain-events-++ movStep chainG))

          evG-eq : chain-events chainG ≡ chain-events (VR.run vg)
          evG-eq = chain-events-subst-start (sym handover) (VR.run vg)

          traces : chain-events chain ≡ eventsAt s (⟪ evalᴰ (g ∘ f) x ⟫ k)
          traces =
            trans events-split
            (trans (cong₂ DL._++_ tf (trans evG-eq (MachineRefinesObsF.traces-agree mg)))
                   (sym ev-comp))

          -- …and the log grows by both.
          log-comp : SMCore.LocState.ev-log (floc (VR.settle vg)) ≡ h DL.++ eventsAt s (⟪ evalᴰ (g ∘ f) x ⟫ k)
          log-comp =
            trans (VR.log vg)
            (trans (cong (DL._++ evG) logF)
            (trans (++-assoc h esF evG)
                   (cong (h DL.++_) (sym ev-comp))))

          -- `f` RETURNED, so the composite's result is `g`'s.
          res-comp : resultAt s (⟪ evalᴰ (g ∘ f) x ⟫ k) ≡ resultAt (floc fsM) (⟪ evalᴰ g vf ⟫ r′)
          res-comp = cong proj₂ CR

          to-g : ∀ {b} → stopsAt s (⟪ evalᴰ (g ∘ f) x ⟫ k) ≡ b → stopsAt (floc fsM) (⟪ evalᴰ g vf ⟫ r′) ≡ b
          to-g p = trans (sym (cong is-stopped res-comp)) p

          to-g-res : ∀ {v} → resultAt s (⟪ evalᴰ (g ∘ f) x ⟫ k) ≡ returns v
                   → resultAt (floc fsM) (⟪ evalᴰ g vf ⟫ r′) ≡ returns v
          to-g-res p = trans (sym res-comp) p

          to-g-nc : NotCut (resultAt s (⟪ evalᴰ (g ∘ f) x ⟫ k)) → NotCut (resultAt (floc fsM) (⟪ evalᴰ g vf ⟫ r′))
          to-g-nc = subst NotCut res-comp

          atEnd : ∀ {v r} → resultAt (floc fsM) (⟪ evalᴰ g vf ⟫ r′) ≡ returns (done v r)
                → fpc (VR.settle vg) ≡ length (emitted n l (g ∘ f)) + base
          atEnd q = trans (VR.at-end vg q)
                        (sym (trans (cong (_+ base) (length-++ ft {mov-to-input ∷ gt}))
                                    (shuffle (length ft) (length gt) base)))

          -- D204: `g ∘ f` preserves what BOTH preserve.
          mem-pres-comp : NotCut (resultAt s (⟪ evalᴰ (g ∘ f) x ⟫ k))
                        → ∀ (loc : ValueLocation FS)
                        → BeforeFrontier (record alloc { next-slot = n }) loc
                        → SMCore.MemOps.readLoc (floc (VR.settle vg)) loc
                          ≡ SMCore.MemOps.readLoc s loc
          mem-pres-comp nc loc bf =
            trans (vr-mem-pres vg (to-g-nc nc) loc
                    (frontier-monotone (record (falloc fsM) { next-slot = n })
                                       (record (falloc fsM) { next-slot = n1 })
                                       refl (frontier-mono f n l) ≤-refl loc
                                       (bfF ncF n loc bf)))
                  (trans (memEq loc) (mpF loc bf))
            where
              mpF : ∀ (l' : ValueLocation FS)
                  → BeforeFrontier (record alloc { next-slot = n }) l'
                  → SMCore.MemOps.readLoc (floc fsF) l' ≡ SMCore.MemOps.readLoc s l'
              mpF (AtStack fr j) b = spF ncF fr j b
              mpF (AtDynamic hl) b = hpF ncF hl b

          bf-mono-comp : NotCut (resultAt s (⟪ evalᴰ (g ∘ f) x ⟫ k))
                       → ∀ (m : ℕ) (loc : ValueLocation FS)
                       → BeforeFrontier (record alloc { next-slot = m }) loc
                       → BeforeFrontier (record (falloc (VR.settle vg)) { next-slot = m }) loc
          bf-mono-comp nc m loc bf = VR.bf-mono vg (to-g-nc nc) m loc (bfF ncF m loc bf)

      -- ── `f` STOPPED THE PROGRAM ───────────────────────────────────────
      -- `g` NEVER RUNS: `thenAp … stopped` never mentions it. So the
      -- composite's machine run IS `f`'s run, and the three fields describing
      -- a fragment which REACHED ITS END are vacuous.
      go stopped rfeq
         (realized kf fsF mOutf caf chainF liveF endF stopsF retF linkF logF placeF progF spF hpF cfF bfF) tf =
        record
          { value-realized =
              realized kf fsF mOutf caf chainF
                       absurd (λ p → case trans (sym res-comp) p of λ ()) (λ _ → stopsF sfeq)
                       (λ p → case trans (sym res-comp) p of λ ()) (λ _ → linkF ncF)
                       (trans logF (cong (h DL.++_) (sym ev-comp)))
                       (λ p → case trans (sym res-comp) p of λ ())
                       (subst (λ ρ → k ≤ budgetLeft k ρ + chain-ctrls chainF) (sym res-comp) (m≤m+n k _))
                       (λ _ → spF ncF) (λ _ → hpF ncF) (λ p → case trans (sym res-comp) p of λ ()) (λ _ → bfF ncF)
          ; traces-agree = trans tf (sym ev-comp)
          }
        where
          ncF : NotCut (resultAt s (⟪ evalᴰ f x ⟫ k))
          ncF = subst NotCut (sym rfeq) tt

          sfeq : stopsAt s (⟪ evalᴰ f x ⟫ k) ≡ true
          sfeq = cong is-stopped rfeq

          CR : runAt s (⟪ evalᴰ (g ∘ f) x ⟫ k) ≡ (esF , stopped)
          CR = comp-run stopped rfeq

          ev-comp : eventsAt s (⟪ evalᴰ (g ∘ f) x ⟫ k) ≡ esF
          ev-comp = cong proj₁ CR

          res-comp : resultAt s (⟪ evalᴰ (g ∘ f) x ⟫ k) ≡ stopped
          res-comp = cong proj₂ CR

          absurd : ∀ {X : Set} → stopsAt s (⟪ evalᴰ (g ∘ f) x ⟫ k) ≡ false → X
          absurd p = case trans (sym (cong is-stopped res-comp)) p of λ ()

      -- ── `f` WAS CUT ───────────────────────────────────────────────────
      -- The budget ran out inside `f`: `g` never runs, the composite is cut
      -- where `f` is, and the machine is still running there.
      go (returns cut) rfeq
         (realized kf fsF mOutf caf chainF liveF endF stopsF retF linkF logF placeF progF spF hpF cfF bfF) tf =
        record
          { value-realized =
              realized kf fsF mOutf caf chainF
                       (λ _ → liveF (cong is-stopped rfeq))
                       (λ p → case trans (sym res-comp) p of λ ())
                       (λ p → case trans (sym (cong is-stopped res-comp)) p of λ ())
                       (λ p → case trans (sym res-comp) p of λ ()) (cut-absurd res-comp)
                       (trans logF (cong (h DL.++_) (sym ev-comp)))
                       (λ p → case trans (sym res-comp) p of λ ())
                       (subst (λ ρ → k ≤ budgetLeft k ρ + chain-ctrls chainF) (sym res-comp) (subst (λ ρ → k ≤ budgetLeft k ρ + chain-ctrls chainF) rfeq progF))
                       (cut-absurd res-comp) (cut-absurd res-comp) (λ p → case trans (sym res-comp) p of λ ()) (cut-absurd res-comp)
          ; traces-agree = trans tf (sym ev-comp)
          }
        where
          CR : runAt s (⟪ evalᴰ (g ∘ f) x ⟫ k) ≡ (esF , returns cut)
          CR = comp-run (returns cut) rfeq

          ev-comp : eventsAt s (⟪ evalᴰ (g ∘ f) x ⟫ k) ≡ esF
          ev-comp = cong proj₁ CR

          res-comp : resultAt s (⟪ evalᴰ (g ∘ f) x ⟫ k) ≡ returns cut
          res-comp = cong proj₂ CR


  -- (moved below `comp-value-realized-of`: it names that proof's chain, so it
  -- cannot be declared above it.)
  -- D203: `comp-traces-agree` was here, and is GONE — it is `go`'s
  -- `traces` field now. Its own comment said it "looks PROVABLE now" and was
  -- "left as an axiom only because the `projTrace`/`>>=T` event-concatenation
  -- step is its own piece of work". That step is `take-++-threaded` /
  -- `minus-take` (TraceMonad), and the reason it could not simply be written
  -- here was structural: the chain it talks about exists only inside `go`'s
  -- pattern match.

  comp-step : ∀ {A B C} {g : IR B C} {f : IR A B} {x : ⟦ A ⟧} {s alloc cl rs}
                (prog : AbstractTrace) (base n l k : ℕ)
            → next-slot alloc ≤ n
            → AllSlotStable prog
            → BlockRuns prog
            → SpanAt prog base (emitted n l (g ∘ f))
            → BlocksAt prog (blocks n l (g ∘ f))
            → LabelsAt prog base (emitted n l (g ∘ f))
            → IRObsCorrectF g → MachineRefinesObsF prog base n l f x s alloc cl rs k
            → MachineRefinesObsF prog base n l (g ∘ f) x s alloc cl rs k
  comp-step prog base n l k ns ss cr span bl la ihg mf =
    comp-value-realized-of prog base n l k ns ss cr span bl la ihg mf

  comp-obs-correct : ∀ {A B C} {g : IR B C} {f : IR A B}
                   → IRObsCorrectF g → IRObsCorrectF f → IRObsCorrectF (g ∘ f)
  comp-obs-correct {g = g} {f} ihg ihf n l prog base ss cr span bl la mIn x s alloc cl ns nh inp k rs =
    comp-step prog base n l k ns ss cr span bl la ihg
      (ihf n l prog base ss cr
           (comp-span-f g f prog base n l span)
           (comp-blocks-f g f prog n l bl)
           (comp-labels-f g f prog base n l la) mIn x s alloc cl ns nh inp k rs)

  -- TOTAL, and now with NO CATCH-ALL (Plan 0.68 step 0). Every constructor has
  -- its own clause and its own named obligation, in `Once.IR`'s order — so a
  -- constructor that is added, removed or renamed is a TYPE ERROR here rather
  -- than a silent variable pattern absorbing it (the retired-ctor trap).

