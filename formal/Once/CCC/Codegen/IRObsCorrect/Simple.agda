-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.IRObsCorrect.Simple
--
-- D200: the clauses whose whole content is "one register move, then run off
-- the end of the fragment" — `id`, `terminal`, `initial`, `free-heap`, `fst`,
-- `snd`, `out-μ`, `const` — together with the postulate block for the shapes
-- that are still open (`In`, `pair`, `case`, `Para`, `in-ν`, `Hylo`, `Fuse`).
------------------------------------------------------------------------

open import Once.CanonicalName using (CanonicalName)

module Once.CCC.Codegen.IRObsCorrect.Simple (o : CanonicalName) where

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

module Simp {FS : FrameSemantics} (program-bound : ℕ) where

  open Core {FS} program-bound
  open Mach {FS} program-bound


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
  obs-correct-id {A} _ n l prog base _ cr span mIn x s alloc cl _ nh rdi-eq k =
    record
      { traces-agree = cong (take k) (sym (denot-[] k))
      ; value-realized =
          realized 1 fs₁ mIn (falloc fs₁) ((nh , span 0 _ refl) ∷ []) nh refl refl refl
                   (place rdi-eq) (λ fr j _ → mem-eq (AtStack fr j)) (λ hl _ → mem-eq (AtDynamic hl)) (λ _ _ bf → bf)
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
      denot-[] : ∀ k → projTrace (evalᴰ (id {A}) x) k ≡ []
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
                (falloc fs₁) (TM.valueT (evalᴰ (id {A}) x) 0)
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
  obs-correct-terminal {A} _ n l prog base _ cr span mIn x s alloc cl _ nh rdi-eq k =
    record
      { traces-agree = cong (take k) (sym (denot-[] k))
      ; value-realized =
          realized 0 (entry-flat base s alloc cl) mIn alloc [] nh refl refl refl unit-result (λ _ _ _ → refl) (λ _ _ → refl) (λ _ _ bf → bf)
      }
    where
      ev-[] : ∀ pc i → fetch (emitted n l (terminal {A})) pc ≡ just i → ∀ fs → event-of i fs ≡ []
      ev-[] zero    i () fs
      ev-[] (suc n) i () fs

      mach-[] : ∀ f → flat-events f (emitted n l (terminal {A})) (entry-flat 0 s alloc cl) ≡ []
      mach-[] f = flat-events-[] (emitted n l (terminal {A})) ev-[] f (entry-flat 0 s alloc cl)

      denot-[] : ∀ k → projTrace (evalᴰ (terminal {A}) x) k ≡ []
      denot-[] k = refl

  -- ── `initial` — DISCHARGED, VACUOUSLY, and that is the honest reading.
  -- `initial : IR Void A` and `⟦ Void ⟧ᴵ` is `⊥`, so there is no input to run
  -- on. The denotation agrees: `evalᴰ initial ()` is itself defined by an
  -- absurd pattern. The emitter's `mov-to-output` is never reached because the
  -- state it would run from cannot exist.
  obs-correct-initial : ∀ {A} → IRObsCorrectF (initial {A})
  obs-correct-initial _ n l prog base _ cr span mIn ()

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

  obs-correct-free-heap : ∀ (r : HeapRef) → IRObsCorrectF (free-heap r)
  obs-correct-free-heap r _ n l prog base _ cr span mIn x s alloc cl _ nh rdi-eq k =    record
      { traces-agree = cong (take k) (sym (denot-[] k))
      ; value-realized =
          realized 1 fs₁ mIn (falloc fs₁) ((nh , span 0 _ refl) ∷ []) nh refl refl refl unit-result (λ fr j _ → mem-untouched mov-to-output s alloc (AtStack fr j) nhw-mov-to-output refl)
                   (λ hl _ → mem-untouched mov-to-output s alloc (AtDynamic hl) nhw-mov-to-output refl) (λ _ _ bf → bf)
      }
    where
      fs₁ = flat-exec-instr mov-to-output prog (entry-flat base s alloc cl)

      ev-[] : ∀ pc i → fetch (emitted n l (free-heap r)) pc ≡ just i → ∀ fs → event-of i fs ≡ []
      ev-[] zero    .mov-to-output refl fs = refl
      ev-[] (suc n) i              ()   fs

      mach-[] : ∀ f → flat-events f (emitted n l (free-heap r)) (entry-flat 0 s alloc cl) ≡ []
      mach-[] f = flat-events-[] (emitted n l (free-heap r)) ev-[] f (entry-flat 0 s alloc cl)

      denot-[] : ∀ k → projTrace (evalᴰ (free-heap r) x) k ≡ []
      denot-[] k = refl

  -- ── `fst` / `snd` — DISCHARGED (D178). One instruction each,
  -- `load-indirect` / `load-indirect-suc`, and the witness is already carried
  -- by the INPUT: `valid-pair-wf` holds `readLoc s pair-loc ≡ just (SV-Ptr
  -- fst-loc)` together with that component's own `BeforeFrontier` and
  -- `ValidAtWF`, so `decomposePairWF` hands over exactly what `at-loc` wants.
  --
  -- The other two input residences are absurd, as for `out-μ`: `in-reg`
  -- carries `FitsInRegI (A * B)` and `FitsInRegI` has only `fits-int` /
  -- `fits-float`; `in-unit` claims `A * B ≡ Unit`, refuted by constructor
  -- disjointness. So only the pointer residence survives.
  --
  -- Memory is untouched (`load-indirect` writes the Output REGISTER — see
  -- `instr-writes-mem load-indirect … = nothing`), so the component's validity
  -- transports by `validityWF-mem-preserved` over a register write.
  obs-correct-fst : ∀ {A B} → IRObsCorrectF (fst {A} {B})
  obs-correct-fst {A} {B} _ n l prog base _ cr span mIn x s alloc cl _ nh inp k = mr-of inp
    where
      fs₁ = flat-exec-instr load-indirect prog (entry-flat base s alloc cl)

      denot-[] : ∀ k → projTrace (evalᴰ (fst {A} {B}) x) k ≡ []
      denot-[] k = refl

      mem-eq : ∀ loc' → readLoc (floc fs₁) loc' ≡ readLoc s loc'
      mem-eq loc' = exec-abstract-load-indirect-preserves-mem s alloc loc'

      -- THE WHOLE RECORD is built per input-residence, not just its
      -- `value-realized` field: `traces-agree` is stated over
      -- `chain-events (ValueRealized.run value-realized)`, which cannot
      -- reduce while the run is a function of an undestructured `inp`. And
      -- the RESULT's mode is the COMPONENT's (`mA` inside the pair
      -- witness), never the input's — `at-loc`'s mode is fixed by the
      -- `ValidAtWF` handed to it.
      mr-of : InputAt mIn alloc x s
            → MachineRefinesObsF prog base n l (fst {A} {B}) x s alloc cl k
      -- D187: the pair's first CELL, and `load-indirect` reads it whatever it
      -- holds. A POINTER cell still places the result in memory; an INLINE one
      -- lands the component in `Output` as a literal, so its place is `at-reg`
      -- — the same split stage F gave the sums, arriving here because the
      -- witness can finally describe it.
      mr-of (in-loc pair-loc pv bf eq) = go (PairValidWF.fst-cell (decomposePairWF pv))
        where
          go : CellAt alloc A (proj₁ x) pair-loc s
             → MachineRefinesObsF prog base n l (fst {A} {B}) x s alloc cl k
          go (cell-ptr {comp-loc = cloc} cp cbef cv) =
            let cval  = validityWF-mem-preserved (proj₁ x) cloc s (floc fs₁) cbef
                          (λ loc' _ → mem-eq loc') cv
                live' = exec-abstract-preserves-halted-WF load-indirect s alloc nh
                          (load-indirect-twf {alloc = alloc} pair-loc (SV-Ptr cloc) eq cp)
            in record
                 { traces-agree = cong (take k) (sym (denot-[] k))
                 ; value-realized =
                     realized 1 fs₁ _ (falloc fs₁)
                       ((nh , span 0 _ refl) ∷ []) live' refl refl refl
                       (at-loc cloc cval cbef
                          (exec-abstract-load-indirect-output s alloc pair-loc (SV-Ptr cloc) eq cp)
                          cval cbef) (λ fr j _ → mem-eq (AtStack fr j)) (λ hl _ → mem-eq (AtDynamic hl)) (λ _ _ bf → bf)
                 }
          go (cell-inline (rep-prim fit) cp) =
            let live' = exec-abstract-preserves-halted-WF load-indirect s alloc nh
                          (load-indirect-twf {alloc = alloc} pair-loc (prim-sv fit (proj₁ x)) eq cp)
            in record
                 { traces-agree = cong (take k) (sym (denot-[] k))
                 ; value-realized =
                     realized 1 fs₁ mIn (falloc fs₁)
                       ((nh , span 0 _ refl) ∷ []) live' refl refl refl
                       (at-reg fit
                          (exec-abstract-load-indirect-output s alloc pair-loc
                             (prim-sv fit (proj₁ x)) eq cp)) (λ fr j _ → mem-eq (AtStack fr j)) (λ hl _ → mem-eq (AtDynamic hl)) (λ _ _ bf → bf)
                 }
          go (cell-inline (rep-unit refl sv) cp) =
            let live' = exec-abstract-preserves-halted-WF load-indirect s alloc nh
                          (load-indirect-twf {alloc = alloc} pair-loc sv eq cp)
            in record
                 { traces-agree = cong (take k) (sym (denot-[] k))
                 ; value-realized =
                     realized 1 fs₁ mIn (falloc fs₁)
                       ((nh , span 0 _ refl) ∷ []) live' refl refl refl unit-result
                       (λ fr j _ → mem-eq (AtStack fr j)) (λ hl _ → mem-eq (AtDynamic hl)) (λ _ _ bf → bf)
                 }
      mr-of (in-reg () _)
      mr-of (in-unit ())

  obs-correct-snd : ∀ {A B} → IRObsCorrectF (snd {A} {B})
  obs-correct-snd {A} {B} _ n l prog base _ cr span mIn x s alloc cl _ nh inp k = mr-of inp
    where
      fs₁ = flat-exec-instr load-indirect-suc prog (entry-flat base s alloc cl)

      denot-[] : ∀ k → projTrace (evalᴰ (snd {A} {B}) x) k ≡ []
      denot-[] k = refl

      mem-eq : ∀ loc' → readLoc (floc fs₁) loc' ≡ readLoc s loc'
      mem-eq loc' = exec-abstract-load-indirect-suc-preserves-mem s alloc loc'

      -- THE WHOLE RECORD is built per input-residence, not just its
      -- `value-realized` field: `traces-agree` is stated over
      -- `chain-events (ValueRealized.run value-realized)`, which cannot
      -- reduce while the run is a function of an undestructured `inp`. And
      -- the RESULT's mode is the COMPONENT's (`mB` inside the pair
      -- witness), never the input's — `at-loc`'s mode is fixed by the
      -- `ValidAtWF` handed to it.
      mr-of : InputAt mIn alloc x s
            → MachineRefinesObsF prog base n l (snd {A} {B}) x s alloc cl k
      -- D187: the `fst` mirror at the pair's SECOND cell.
      mr-of (in-loc pair-loc pv bf eq) = go (PairValidWF.snd-cell (decomposePairWF pv))
        where
          go : CellAt alloc B (proj₂ x) (sucLoc pair-loc) s
             → MachineRefinesObsF prog base n l (snd {A} {B}) x s alloc cl k
          go (cell-ptr {comp-loc = cloc} cp cbef cv) =
            let cval  = validityWF-mem-preserved (proj₂ x) cloc s (floc fs₁) cbef
                          (λ loc' _ → mem-eq loc') cv
                live' = exec-abstract-preserves-halted-WF load-indirect-suc s alloc nh
                          (load-indirect-suc-twf {alloc = alloc} pair-loc (SV-Ptr cloc) eq cp)
            in record
                 { traces-agree = cong (take k) (sym (denot-[] k))
                 ; value-realized =
                     realized 1 fs₁ _ (falloc fs₁)
                       ((nh , span 0 _ refl) ∷ []) live' refl refl refl
                       (at-loc cloc cval cbef
                          (exec-abstract-load-indirect-suc-output s alloc pair-loc (SV-Ptr cloc) eq cp)
                          cval cbef) (λ fr j _ → mem-eq (AtStack fr j)) (λ hl _ → mem-eq (AtDynamic hl)) (λ _ _ bf → bf)
                 }
          go (cell-inline (rep-prim fit) cp) =
            let live' = exec-abstract-preserves-halted-WF load-indirect-suc s alloc nh
                          (load-indirect-suc-twf {alloc = alloc} pair-loc (prim-sv fit (proj₂ x)) eq cp)
            in record
                 { traces-agree = cong (take k) (sym (denot-[] k))
                 ; value-realized =
                     realized 1 fs₁ mIn (falloc fs₁)
                       ((nh , span 0 _ refl) ∷ []) live' refl refl refl
                       (at-reg fit
                          (exec-abstract-load-indirect-suc-output s alloc pair-loc
                             (prim-sv fit (proj₂ x)) eq cp)) (λ fr j _ → mem-eq (AtStack fr j)) (λ hl _ → mem-eq (AtDynamic hl)) (λ _ _ bf → bf)
                 }
          go (cell-inline (rep-unit refl sv) cp) =
            let live' = exec-abstract-preserves-halted-WF load-indirect-suc s alloc nh
                          (load-indirect-suc-twf {alloc = alloc} pair-loc sv eq cp)
            in record
                 { traces-agree = cong (take k) (sym (denot-[] k))
                 ; value-realized =
                     realized 1 fs₁ mIn (falloc fs₁)
                       ((nh , span 0 _ refl) ∷ []) live' refl refl refl unit-result
                       (λ fr j _ → mem-eq (AtStack fr j)) (λ hl _ → mem-eq (AtDynamic hl)) (λ _ _ bf → bf)
                 }
      mr-of (in-reg () _)
      mr-of (in-unit ())

  -- ── `out-μ` / `Out` — DISCHARGED. Both are Lambek inverses compiling to the
  -- same `mov-to-output ∷ []` as `id`, and both are DOMAIN-RESTRICTED in a way
  -- that kills two of the three input residences outright:
  --   * `in-reg` carries `FitsInRegI (μ-type F)`, and `FitsInRegI` has only
  --     `fits-int`/`fits-float` — absurd;
  --   * `in-unit` claims `μ-type F ≡ Unit` — absurd by constructor disjointness.
  -- So only the pointer residence survives, and the value witness is exactly
  -- the layer iso: `valid-μ-wf` CARRIES the layer's own `ValidAtWF`
  -- (Plan 0.27 Option 3), so destructing one yields what `at-loc` wants.
  obs-correct-out-μ : ∀ {F} (wf : WellFormedFI F) → IRObsCorrectF (out-μ wf)
  obs-correct-out-μ {F} wf _ n l prog base _ cr span mIn x s alloc cl _ nh rdi-eq k =    record
      { traces-agree = cong (take k) (sym (denot-[] k))
      ; value-realized =
          realized 1 fs₁ mIn (falloc fs₁) ((nh , span 0 _ refl) ∷ []) nh refl refl refl
                   (place rdi-eq) (λ fr j _ → mem-eq (AtStack fr j)) (λ hl _ → mem-eq (AtDynamic hl)) (λ _ _ bf → bf)
      }
    where
      regs' = writeReg (regs s) Output (readReg (regs s) Input1)
      fs₁   = flat-exec-instr mov-to-output prog (entry-flat base s alloc cl)


      ev-[] : ∀ pc i → fetch (emitted n l (out-μ wf)) pc ≡ just i → ∀ fs → event-of i fs ≡ []
      ev-[] zero    .mov-to-output refl fs = refl
      ev-[] (suc n) i              ()   fs

      mach-[] : ∀ f → flat-events f (emitted n l (out-μ wf)) (entry-flat 0 s alloc cl) ≡ []
      mach-[] f = flat-events-[] (emitted n l (out-μ wf)) ev-[] f (entry-flat 0 s alloc cl)

      denot-[] : ∀ k → projTrace (evalᴰ (out-μ wf) x) k ≡ []
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
                  (TM.valueT (evalᴰ (out-μ wf) x) 0) il
                  (floc fs₁)
      valid'' il bf v = subst (λ a → ValidAtWF mIn a (TM.valueT (evalᴰ (out-μ wf) x) 0) il
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
                (falloc fs₁) (TM.valueT (evalᴰ (out-μ wf) x) 0)
                (floc fs₁)
      place (in-loc il v bf eq) =
        at-loc il (valid'' il bf v) (before' il bf) (out-ptr il eq)
                  (valid'' il bf v) (before' il bf)
      place (in-reg () _)
      place (in-unit ())

  -- ── `Out` — NO LONGER DISCHARGED (D189), and the retraction is the point.
  -- What stood here was a proof by absurdity whose absurdity was the emitter's
  -- own silence. It read: A ν is now a KLEISLI value: forcing a layer is a computation, so
  -- `evalᴰ (Out wf) x = forceᵈ x` may EMIT. The machine's `Out` is one
  -- `mov-to-output`, which emits nothing — so if a ν could reach this
  -- instruction, the obligation would be FALSE, not provable.
  --
  -- It cannot. Class G: the emitter produces NO instructions for `Ana`/`in-ν`,
  -- so no ν value is ever built in memory, and `ValidAtWF` has no ν
  -- constructor to witness one (`ν-not-resident`). Both other residences are
  -- refuted outright: a ν does not fit in a register and is not `Unit`.
  --
  -- This is where the audit lands: the old proof looked like a theorem about
  -- `Out` and was a theorem about `inject x`, a ν that could not emit. When
  -- `Ana` gets an emitter, THIS case is the one that must be reproved for real
  -- — against a machine that forces layers, not one that moves a pointer.

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
  obs-correct-const fits-int v _ n l prog base _ cr span mIn x s alloc cl _ nh rdi-eq k =    record
      { traces-agree = cong (take k) (sym (denot-[] k))
      ; value-realized =
          realized 1 fs₁ mIn (falloc fs₁) ((nh , span 0 _ refl) ∷ []) nh refl refl refl
                   (at-reg fits-int out-lit) (λ fr j _ → mem-untouched (instr-load-const fits-intˢ v) s alloc (AtStack fr j) nhw-instr-load-const refl)
                   (λ hl _ → mem-untouched (instr-load-const fits-intˢ v) s alloc (AtDynamic hl) nhw-instr-load-const refl) (λ _ _ bf → bf)
      }
    where
      instr = instr-load-const fits-intˢ v
      fs₁   = flat-exec-instr instr prog (entry-flat base s alloc cl)


      ev-[] : ∀ pc i → fetch (emitted n l (const fits-int v)) pc ≡ just i → ∀ fs → event-of i fs ≡ []
      ev-[] zero    .instr refl fs = refl
      ev-[] (suc n) i      ()   fs

      mach-[] : ∀ f → flat-events f (emitted n l (const fits-int v)) (entry-flat 0 s alloc cl) ≡ []
      mach-[] f = flat-events-[] (emitted n l (const fits-int v)) ev-[] f (entry-flat 0 s alloc cl)

      denot-[] : ∀ k → projTrace (evalᴰ (const fits-int v) x) k ≡ []
      denot-[] k = refl

      keeps-alloc : falloc fs₁ ≡ alloc
      keeps-alloc = refl

      out-lit : readReg (regs (floc fs₁)) Output
              ≡ prim-sv fits-int (TM.valueT (evalᴰ (const fits-int v) x) 0)
      -- D115: the machine MATERIALISES the literal, exactly as the float
      -- case below does — `lit-value` is two's complement at this width.
      out-lit =
        writeReg-same (regs s) Output (SV-Lit fits-intˢ (AbstractExec.lit-value {FS} fits-intˢ v))

  obs-correct-const fits-float v _ n l prog base _ cr span mIn x s alloc cl _ nh rdi-eq k =    record
      { traces-agree = cong (take k) (sym (denot-[] k))
      ; value-realized =
          realized 1 fs₁ mIn (falloc fs₁) ((nh , span 0 _ refl) ∷ []) nh refl refl refl
                   (at-reg fits-float out-lit) (λ fr j _ → mem-untouched (instr-load-const fits-floatˢ v) s alloc (AtStack fr j) nhw-instr-load-const refl)
                   (λ hl _ → mem-untouched (instr-load-const fits-floatˢ v) s alloc (AtDynamic hl) nhw-instr-load-const refl) (λ _ _ bf → bf)
      }
    where
      instr = instr-load-const fits-floatˢ v
      fs₁   = flat-exec-instr instr prog (entry-flat base s alloc cl)


      ev-[] : ∀ pc i → fetch (emitted n l (const fits-float v)) pc ≡ just i → ∀ fs → event-of i fs ≡ []
      ev-[] zero    .instr refl fs = refl
      ev-[] (suc n) i      ()   fs

      mach-[] : ∀ f → flat-events f (emitted n l (const fits-float v)) (entry-flat 0 s alloc cl) ≡ []
      mach-[] f = flat-events-[] (emitted n l (const fits-float v)) ev-[] f (entry-flat 0 s alloc cl)

      denot-[] : ∀ k → projTrace (evalᴰ (const fits-float v) x) k ≡ []
      denot-[] k = refl

      keeps-alloc : falloc fs₁ ≡ alloc
      keeps-alloc = refl

      out-lit : readReg (regs (floc fs₁)) Output
              ≡ prim-sv fits-float (TM.valueT (evalᴰ (const fits-float v) x) 0)
      -- Plan 0.73 (D113): the machine MATERIALISES the literal as it executes —
      -- `exec-abstract` writes `round (float-format FS) v`, not the payload.
      -- The denotation says the same because `eval` above is at the same
      -- format; that agreement is the whole point of reading it from one place.
      out-lit =
        writeReg-same (regs s) Output (SV-Lit fits-floatˢ (round (FrameSemantics.float-format FS) v))

  postulate
    -- (`obs-correct-fst`/`-snd` MOVED OUT — discharged above, D178.)
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
    obs-correct-In        : ∀ {F} (wf : WellFormedFI F)
                          → IRObsCorrectF (In wf)

    -- CLASS B — allocating, no control flow. Step 1; adds the frontier thread.
    --
    -- D202: takes the SUB-PROOFS. `⟨ f , g ⟩` splices two sub-IR runs
    -- (`emitted = mov ∷ store ∷ ft ++ store ∷ restore ∷ gt ++ <heap build>`),
    -- so like `g ∘ f` it cannot be proved without them — and unlike `g ∘ f`
    -- the dispatcher was not passing them, which made the clause unprovable in
    -- principle rather than merely unproved. The induction hypotheses arrive
    -- as ARGUMENTS, so the parts keep the D200 star shape: no clause calls
    -- back into `ir-obs-correct`.
    --
    -- Still an axiom, but a strictly weaker one: it now asks for more.
    obs-correct-pair : ∀ {A B C} {f : IR A B} {g : IR A C}
                     → IRObsCorrectF f → IRObsCorrectF g
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
    -- (`obs-correct-inl` and `-inr` MOVED OUT of this block — both are
    -- discharged below, `inr` as the mechanical mirror of `inl`.)

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
    -- (`obs-correct-curry` MOVED OUT — discharged below, D181, as the
    -- mechanical mirror of `obs-correct-inl`: the same ten-instruction heap
    -- build, with the tag write replaced by the env load and the payload load
    -- replaced by `instr-load-code-addr`.)
    obs-correct-case  : ∀ {A B C} (f : IR A C) (g : IR B C)
                      → IRObsCorrectF (case f g)

    -- (`obs-correct-apply` MOVED OUT — discharged below, D188.)

    -- CLASS G — THE EMITTER IS MISSING. Each of these compiles to `[]`, so the
    -- obligation is refutable whenever the denotation emits an event. NOT a
    -- proof task: implement the codegen, restrict the IR so they cannot be
    -- built, or condition the obligation to exclude them (Plan 0.68 step 5, and
    -- it needs a decision-log entry either way). Named so the choice is forced.
    obs-correct-Para : ∀ {F} (wf : WellFormedFI F) {A} (f : IR (⟦ F ⟧TI (μ-type F * A)) A)
                     → IRObsCorrectF (Para wf f)
    obs-correct-in-ν : ∀ {F} (wf : WellFormedFI F)
                     → IRObsCorrectF (in-ν wf)
    -- D189: `obs-correct-Ana` LEFT this class — the emitter exists and the case
    -- is discharged below. D199: `obs-correct-Out` left it too, from the other
    -- direction — it was FALSE while the machine did not re-suspend, and is
    -- proved below now that it does.
    obs-correct-Hylo : ∀ {F G} (wfF : WellFormedFI F) (wfG : WellFormedFI G) {B}
                       (alg : IR (⟦ F ⟧TI B) B) (nt : NatTr G F)
                     → IRObsCorrectF (Hylo wfF wfG alg nt)
    obs-correct-Fuse : ∀ {F G} (wfF : WellFormedFI F) (wfG : WellFormedFI G) {B}
                       (alg : IR (⟦ F ⟧TI B) B) (nt : NatTr G F)
                     → IRObsCorrectF (Fuse wfF wfG alg nt)

