-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.IRObsCorrect.Comp
--
-- D200: composition — `g ∘ f` runs `f`'s fragment, hands its result to `g`
-- as an input residence (`result→input`), and concatenates the chains.
------------------------------------------------------------------------

open import Once.CanonicalName using (CanonicalName)

module Once.CCC.Codegen.IRObsCorrect.Comp (o : CanonicalName) where

open import Once.CCC.Codegen.IRObsCorrect.Machine o

import Once.CCC.FrameSemantics
import Once.CCC.Machine.SMPrimitives
import Once.IRTy
import Once.IR
import Once.CCC.Eval as Ev
import Once.Semantics.Machine as EvV
import Once.CCC.Machine.ReadTypedAdequate as RTA
import Once.Denotation.DenotTrace as DT
import Once.Denotation.TraceMonad as TM

module CompC {FS : FrameSemantics} where

  open Core {FS}
  open Mach {FS}

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
  -- program for their scans to disagree with. `find-thunk prog blbl` is the same
  -- scan on both sides, which is exactly what `apply ∘ curry body` needs.
  -- ══════════════════════════════════════════════════════════════════════
  comp-value-realized-of :
    ∀ {A B C} {g : IR B C} {f : IR A B} {x : ⟦ A ⟧} {s alloc cl}
      (prog : AbstractTrace) (base n l k : ℕ)
    → next-slot alloc ≤ n
    → AllSlotStable prog
    → BlockRuns prog
    → SpanAt prog base (emitted n l (g ∘ f))
    → IRObsCorrectF g → MachineRefinesObsF prog base n l f x s alloc cl k
    → MachineRefinesObsF prog base n l (g ∘ f) x s alloc cl k
  comp-value-realized-of {g = g} {f} {x} {s} {alloc} {cl} prog base n l k ns ss cr span ihg mf =
    go (MachineRefinesObsF.value-realized mf) (MachineRefinesObsF.traces-agree mf)
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

      -- D180: the budget `g` observes is what `f` LEFT of the composite's — the
      -- same arithmetic `_>>=T_` does (`n ∸ length (proj₁ (m n))`), so the
      -- composite's value and `g`'s coincide DEFINITIONALLY and no transport
      -- is needed at the seam.
      kg : ℕ
      kg = k ∸ length (projTrace (evalᴰ f x) k)

      -- D203: `go` builds BOTH halves. It used to build only the value half,
      -- and the trace half was a separate postulate — which it had to be,
      -- because the chain it must talk about (`chainF`, `chainG`) only exists
      -- inside this pattern match. Stating it outside meant either a `with`
      -- abstraction over a projection or an axiom; the honest fix is to widen
      -- what the match produces. `f`'s own trace agreement comes in as an
      -- argument for the same reason: it mentions the matched chain.
      go : (vr : ValueRealized prog base n l f x s alloc cl k)
         → take k (chain-events (VR.run vr)) ≡ take k (projTrace (evalᴰ f x) k)
         → MachineRefinesObsF prog base n l (g ∘ f) x s alloc cl k
      go (realized kf fsF mOutf caf chainF liveF endF retF linkF placeF spF hpF cfF bfF) tf =
        record
          { value-realized =
              realized (kf + suc (VR.steps vg)) (VR.settle vg)
                       (VR.out-mode vg) (VR.cont-alloc vg)
                       chain (VR.live vg) atEnd (VR.no-ret vg) (VR.no-link vg)
                       (VR.place vg)
                       (λ fr j bf → mem-pres-comp (AtStack fr j) bf) (λ hl bf → mem-pres-comp (AtDynamic hl) bf)
                       (trans (VR.frame-pres vg) cfF)
                       bf-mono-comp
          ; traces-agree = traces
          }
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

          inputM : InputAt mOutf (falloc fsM) (TM.valueT (evalᴰ f x) k) (floc fsM)
          inputM = result→input placeF movEq memEq

          mg : MachineRefinesObsF prog base' n1 l1 g (TM.valueT (evalᴰ f x) k)
                                  (floc fsM) (falloc fsM) (fclosure fsM) kg
          mg = ihg n1 l1 prog base' ss cr span-g mOutf (TM.valueT (evalᴰ f x) k)
                   (floc fsM) (falloc fsM) (fclosure fsM) nsG liveM inputM kg

          vg : ValueRealized prog base' n1 l1 g (TM.valueT (evalᴰ f x) k)
                             (floc fsM) (falloc fsM) (fclosure fsM) kg
          vg = MachineRefinesObsF.value-realized mg

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

          -- D204: `g ∘ f` preserves what BOTH preserve. `g` runs from `fsM`,
          -- whose frontier is `falloc fsM` — equal to `alloc`'s at the slot
          -- `mov-to-input` does not touch the allocator, so `falloc fsM` IS
          -- `falloc fsF` and `f`'s own `bf-mono` is the whole lift.
          mem-pres-comp : ∀ (loc : ValueLocation FS)
                        → BeforeFrontier (record alloc { next-slot = n }) loc
                        → MemOps.readLoc (floc (VR.settle vg)) loc
                          ≡ MemOps.readLoc s loc
          -- `g` is emitted at `n1 ≥ n`, so its preservation covers everything
          -- below `n` too; the witness is carried across `f`'s run by `f`'s own
          -- `bf-mono` at the composite's bound, then widened to `g`'s.
          mem-pres-comp loc bf =
            trans (vr-mem-pres vg loc
                    (frontier-monotone (record (falloc fsM) { next-slot = n })
                                       (record (falloc fsM) { next-slot = n1 })
                                       refl (frontier-mono f n l) ≤-refl loc
                                       (bfF n loc bf)))
                  (trans (memEq loc) (mpF loc bf))
            where
              mpF : ∀ (l' : ValueLocation FS)
                  → BeforeFrontier (record alloc { next-slot = n }) l'
                  → MemOps.readLoc (floc fsF) l' ≡ MemOps.readLoc s l'
              mpF (AtStack fr j) b = spF fr j b
              mpF (AtDynamic hl) b = hpF hl b

          bf-mono-comp : ∀ (m : ℕ) (loc : ValueLocation FS)
                       → BeforeFrontier (record alloc { next-slot = m }) loc
                       → BeforeFrontier (record (falloc (VR.settle vg)) { next-slot = m }) loc
          bf-mono-comp m loc bf = VR.bf-mono vg m loc (bfF m loc bf)

          -- ── THE TRACE HALF (D203) ──────────────────────────────────────
          -- The composite's chain is `chainF ++ mov ++ chainG` and the
          -- composite's meaning is `evalᴰ f x >>=T evalᴰ g`, whose trace is
          -- DEFINITIONALLY `dEvF ++ dEvG` with `g`'s budget THREADED as
          -- `k ∸ length dEvF`. So both sides are a concatenation observed at
          -- `k`, and `take-++-threaded` splits each the same way.
          --
          -- The step that makes it go through without a boundedness
          -- hypothesis is `minus-take`: the residual budget cannot tell
          -- whether the prefix was truncated, so the machine's
          -- `k ∸ length (take k mEvF)` and the denotation's `k ∸ length dEvF`
          -- are the same number — which is `kg`, the budget `mg` was already
          -- instantiated at.
          mEvF = chain-events chainF
          mEvG = chain-events chainG
          dEvF = projTrace (evalᴰ f x) k
          dEvG = projTrace (evalᴰ g (TM.valueT (evalᴰ f x) k)) kg

          events-split : chain-events chain ≡ mEvF ++ mEvG
          events-split =
            trans (chain-events-++ chainF (FlatSteps-++ movStep chainG))
                  (cong (mEvF ++_) (chain-events-++ movStep chainG))

          evG-eq : mEvG ≡ chain-events (VR.run vg)
          evG-eq = chain-events-subst-start (sym handover) (VR.run vg)

          budget-eq : k ∸ length (take k dEvF) ≡ kg
          budget-eq = TM.minus-take k dEvF

          tail-eq : take (k ∸ length (take k mEvF)) mEvG
                  ≡ take (k ∸ length (take k dEvF)) dEvG
          tail-eq =
            trans (cong (λ m → take (k ∸ length m) mEvG) tf)
            (trans (cong (λ j → take j mEvG) budget-eq)
            (trans (cong (take kg) evG-eq)
            (trans (MachineRefinesObsF.traces-agree mg)
                   (sym (cong (λ j → take j dEvG) budget-eq)))))

          traces : take k (chain-events chain)
                 ≡ take k (projTrace (evalᴰ (g ∘ f) x) k)
          traces =
            trans (cong (take k) events-split)
            (trans (TM.take-++-threaded k mEvF mEvG)
            (trans (cong₂ _++_ tf tail-eq)
                   (sym (TM.take-++-threaded k dEvF dEvG))))

          atEnd : fpc (VR.settle vg) ≡ length (emitted n l (g ∘ f)) + base
          atEnd = trans (VR.at-end vg)
                        (sym (trans (cong (_+ base) (length-++ ft {mov-to-input ∷ gt}))
                                    (shuffle (length ft) (length gt) base)))


  -- (moved below `comp-value-realized-of`: it names that proof's chain, so it
  -- cannot be declared above it.)
  -- D203: `comp-traces-agree` was here, and is GONE — it is `go`'s
  -- `traces` field now. Its own comment said it "looks PROVABLE now" and was
  -- "left as an axiom only because the `projTrace`/`>>=T` event-concatenation
  -- step is its own piece of work". That step is `take-++-threaded` /
  -- `minus-take` (TraceMonad), and the reason it could not simply be written
  -- here was structural: the chain it talks about exists only inside `go`'s
  -- pattern match.

  comp-step : ∀ {A B C} {g : IR B C} {f : IR A B} {x : ⟦ A ⟧} {s alloc cl}
                (prog : AbstractTrace) (base n l k : ℕ)
            → next-slot alloc ≤ n
            → AllSlotStable prog
            → BlockRuns prog
            → SpanAt prog base (emitted n l (g ∘ f))
            → IRObsCorrectF g → MachineRefinesObsF prog base n l f x s alloc cl k
            → MachineRefinesObsF prog base n l (g ∘ f) x s alloc cl k
  comp-step prog base n l k ns ss cr span ihg mf =
    comp-value-realized-of prog base n l k ns ss cr span ihg mf

  comp-obs-correct : ∀ {A B C} {g : IR B C} {f : IR A B}
                   → IRObsCorrectF g → IRObsCorrectF f → IRObsCorrectF (g ∘ f)
  comp-obs-correct {g = g} {f} ihg ihf n l prog base ss cr span mIn x s alloc cl ns nh inp k =
    comp-step prog base n l k ns ss cr span ihg
      (ihf n l prog base ss cr
           (comp-span-f g f prog base n l span) mIn x s alloc cl ns nh inp k)

  -- TOTAL, and now with NO CATCH-ALL (Plan 0.68 step 0). Every constructor has
  -- its own clause and its own named obligation, in `Once.IR`'s order — so a
  -- constructor that is added, removed or renamed is a TYPE ERROR here rather
  -- than a silent variable pattern absorbing it (the retired-ctor trap).

