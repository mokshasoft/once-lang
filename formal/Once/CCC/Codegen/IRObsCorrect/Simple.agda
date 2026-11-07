-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.IRObsCorrect.Simple
--
-- D200: the clauses whose whole content is "one register move, then run off
-- the end of the fragment" — `id`, `terminal`, `initial`, `free-heap`, `fst`,
-- `snd`, `out-μ`, `const`. The postulate block that stood at the end (`In`)
-- is gone: `obs-correct-In` was FALSE (D366) and is proved in `InMu`; the
-- block's history is kept below as comments.
------------------------------------------------------------------------

open import Once.Spec.Name using (CanonicalName)
import Once.CCC.Machine.SMCore as SMCore
import Once.CCC.FrameSemantics as FrameSemantics′

import Data.List as DL
open import Once.Denotation.Program using (IRFun)
module Once.CCC.Codegen.IRObsCorrect.Simple (o : CanonicalName) (tbl : DL.List IRFun) where

open import Once.CCC.Codegen.IRObsCorrect.Machine o tbl
open import Once.CCC.Codegen.IRObsCorrect.Get o tbl using (module GetC)
open import Once.CCC.Codegen.Size using (size)
open import Once.CCC.Codegen.FlatLayout using (get)
open import Once.CCC.Machine.SMCore using (load-at)
open import Once.CCC.Machine.SMCore using (writeReg; Output; readReg; Input1; mov-to-output; SV-Ptr; writeReg-same; load-indirect; load-indirect-suc; sucLoc; instr-load-const; SV-Lit; module LocState)
open LocState using (regs; halted)
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.Locations using (AtStack; AtDynamic; ValueLocation)
open import Once.Spec.Float.Decimal using (Decimal; round)
open import Once.IRTy using (WellFormedFI; ⟦_⟧TI; μ-type; ⟦_,_⟧-baseI; wf-K; wf-Id; wf-Sum; wf-Prod;
                             base-Int; base-Float; base-Unit; base-Void; base-Prod; base-Sum; Unit)
open import Once.CCC.Machine.MuRep using (mu-rep; mu-box; Unboxed; box-fit; fit-not-unit)

import Once.CCC.FrameSemantics
import Once.CCC.Machine.SMPrimitives
import Once.IRTy
import Once.IR
import Once.Semantics.Machine as EvV
import Once.CCC.Machine.ReadTypedAdequate as RTA
import Once.Denotation.DenotTrace as DT
import Once.IR.Semantics.Trace as TM

module Simp {FS : FrameSemantics} where

  open Core {FS}
  open Mach {FS}
  open GetC {FS} using (module GetOut; get-run; setOut; out-mem; get-len; offset-zero; get-word; scalar-kind)


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
  --
  -- plan 0.98: `place`'s premise BINDS the value — `resT ≡ returns v` is one
  -- fact where 0.97 had a boolean condition beside a total value field. These
  -- clauses all return unconditionally, so matching the premise to `refl` is
  -- what identifies the bound `v` with the value the clause placed; ignoring
  -- the premise (`λ _ → …`) would leave the two free to differ.
  obs-correct-id : ∀ {A} → IRObsCorrectF (id {A})
  obs-correct-id {A} n l prog base _ cr span _ _ mIn x s alloc cl _ nh rdi-eq k rs =
    record
      { traces-agree = sym (denot-[] k)
      ; value-realized =
          realized 1 fs₁ mIn (falloc fs₁) ((nh , span 0 _ refl) ∷ []) (λ _ → nh) (λ _ → refl) (λ ()) (λ _ → refl) (λ _ → refl) (log-pure {s})
                   (λ { refl → place rdi-eq }) (m≤m+n k _) (λ _ → (λ fr j _ → mem-eq (AtStack fr j))) (λ _ → (λ hl _ → mem-eq (AtDynamic hl))) (λ _ → refl) (λ _ → (λ _ _ bf → bf)) (λ _ → refl) (λ _ _ _ ib → ib)
      }
    where
      -- The post-`mov` register file and the intermediate flat state. `run-eq`
      -- is derived from the two step lemmas rather than by `rewrite nh`: the
      -- second step's `halted` test is not a syntactic occurrence in the goal.
      regs' = writeReg (regs s) Output (readReg (regs s) Input1)
      fs₁   = flat-exec-instr mov-to-output prog (entry-flat base s alloc cl rs)


      -- Machine side: the only fetchable instruction is `mov-to-output`, which
      -- emits nothing.
      ev-[] : ∀ pc i → fetch (emitted n l (id {A})) pc ≡ just i → ∀ fs → event-of i fs ≡ []
      ev-[] zero    .mov-to-output refl fs = refl
      ev-[] (suc n) i              ()   fs

      mach-[] : ∀ f → proj₁ (flat-events f (emitted n l (id {A})) (entry-flat 0 s alloc cl rs)) ≡ []
      mach-[] f = flat-events-[] (emitted n l (id {A})) ev-[] f (entry-flat 0 s alloc cl rs)

      -- Denotation side: `evalᴰ id a = returnT a` emits nothing.
      denot-[] : ∀ k → eventsAt s (⟪ evalᴰ (id {A}) x ⟫ k) ≡ []
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

      before' : ∀ (il : ValueLocation FS) → Live alloc il
              → Live (falloc fs₁) il
      before' il bf = bf

      place : InputAt mIn alloc x s
            → ResultPlace A mIn (falloc fs₁)
                (falloc fs₁) (retVal (evalᴰ (id {A}) x))
                (floc fs₁)
      place (in-loc il v bf eq) =
        at-loc il (valid'' il (live→bf bf) v) (before' il bf) (out-ptr il eq)
                  (valid'' il (live→bf bf) v) (before' il bf)
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
  obs-correct-terminal {A} n l prog base _ cr span _ _ mIn x s alloc cl _ nh rdi-eq k rs =
    record
      { traces-agree = sym (denot-[] k)
      ; value-realized =
          realized 0 (entry-flat base s alloc cl rs) mIn alloc [] (λ _ → nh) (λ _ → refl) (λ ()) (λ _ → refl) (λ _ → refl) (log-pure {s}) (λ { refl → unit-result }) (m≤m+n k _) (λ _ → (λ _ _ _ → refl)) (λ _ → (λ _ _ → refl)) (λ _ → refl) (λ _ → (λ _ _ bf → bf)) (λ _ → refl) (λ _ _ _ ib → ib)
      }
    where
      ev-[] : ∀ pc i → fetch (emitted n l (terminal {A})) pc ≡ just i → ∀ fs → event-of i fs ≡ []
      ev-[] zero    i () fs
      ev-[] (suc n) i () fs

      mach-[] : ∀ f → proj₁ (flat-events f (emitted n l (terminal {A})) (entry-flat 0 s alloc cl rs)) ≡ []
      mach-[] f = flat-events-[] (emitted n l (terminal {A})) ev-[] f (entry-flat 0 s alloc cl rs)

      denot-[] : ∀ k → eventsAt s (⟪ evalᴰ (terminal {A}) x ⟫ k) ≡ []
      denot-[] k = refl

  -- ── `initial` — DISCHARGED, VACUOUSLY, and that is the honest reading.
  -- `initial : IR Void A` and `⟦ Void ⟧ᴵ` is `⊥`, so there is no input to run
  -- on. The denotation agrees: `evalᴰ initial ()` is itself defined by an
  -- absurd pattern. The emitter's `mov-to-output` is never reached because the
  -- state it would run from cannot exist.
  obs-correct-initial : ∀ {A} → IRObsCorrectF (initial {A})
  obs-correct-initial n l prog base _ cr span _ _ mIn ()

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

  -- ── `fst` / `snd` — DISCHARGED (D178), and since plan 0.123 B.4 α ONE `get` of the input pair's
  -- component (`IRObsCorrect.Get`). The pair is flat (D381): the first
  -- component at word 0, the second after the first's words, each in its
  -- register form (a node's or scalar's word, a flat component's address, a
  -- 0-word component's container pointer, D387). `get-run` runs the step and
  -- says where the component is; the record is the step's frame.
  obs-correct-fst : ∀ {A B} → IRObsCorrectF (fst {A} {B})
  obs-correct-fst {A} {B} n l prog base _ cr span _ _ mIn x s alloc cl _ nh inp k rs = mr-of inp
    where
      fs₀ = entry-flat base s alloc cl rs

      denot-[] : ∀ k → eventsAt s (⟪ evalᴰ (fst {A} {B}) x ⟫ k) ≡ []
      denot-[] k = refl

      done : GetC.GetOut {FS} {prog} A (proj₁ x) fs₀
           → MachineRefinesObsF prog base n l (fst {A} {B}) x s alloc cl rs k
      done g = record
        { traces-agree = trans (GetOut.silent g) (sym (denot-[] k))
        ; value-realized =
            realized 1 (setOut fs₀ (GetOut.out g)) (GetOut.mode g) alloc (GetOut.step g)
              (λ _ → nh) (λ _ → cong (_+ base) (sym (get-len A 0))) (λ ()) (λ _ → refl) (λ _ → refl)
              (log-of (GetOut.step g) (trans (GetOut.silent g) (sym (denot-[] k))))
              (λ { refl → GetOut.place g })
              (m≤m+n k _)
              (λ _ fr j _ → out-mem fs₀ (GetOut.out g) (AtStack fr j)) (λ _ hl _ → out-mem fs₀ (GetOut.out g) (AtDynamic hl))
              (λ _ → refl) (λ _ _ _ bf → bf) (λ _ → refl) (λ _ _ _ ib → ib)
        }

      mr-of : InputAt mIn alloc x s → MachineRefinesObsF prog base n l (fst {A} {B}) x s alloc cl rs k
      mr-of (in-loc pair-loc pv lv eq) =
        done (get-run A 0 fs₀ pair-loc nh (λ i f → span 0 i f) eq lv
               (subst (λ z → CellAt {prog = prog} alloc A (proj₁ x) z s) (sym (offset-zero pair-loc))
                      (PairValidWF.fst-cell (decomposePairWF pv))))
      mr-of (in-reg () _)
      mr-of (in-unit ())

  obs-correct-snd : ∀ {A B} → IRObsCorrectF (snd {A} {B})
  obs-correct-snd {A} {B} n l prog base _ cr span _ _ mIn x s alloc cl _ nh inp k rs = mr-of inp
    where
      fs₀ = entry-flat base s alloc cl rs

      denot-[] : ∀ k → eventsAt s (⟪ evalᴰ (snd {A} {B}) x ⟫ k) ≡ []
      denot-[] k = refl

      done : GetC.GetOut {FS} {prog} B (proj₂ x) fs₀
           → MachineRefinesObsF prog base n l (snd {A} {B}) x s alloc cl rs k
      done g = record
        { traces-agree = trans (GetOut.silent g) (sym (denot-[] k))
        ; value-realized =
            realized 1 (setOut fs₀ (GetOut.out g)) (GetOut.mode g) alloc (GetOut.step g)
              (λ _ → nh) (λ _ → cong (_+ base) (sym (get-len B (size A)))) (λ ()) (λ _ → refl) (λ _ → refl)
              (log-of (GetOut.step g) (trans (GetOut.silent g) (sym (denot-[] k))))
              (λ { refl → GetOut.place g })
              (m≤m+n k _)
              (λ _ fr j _ → out-mem fs₀ (GetOut.out g) (AtStack fr j)) (λ _ hl _ → out-mem fs₀ (GetOut.out g) (AtDynamic hl))
              (λ _ → refl) (λ _ _ _ bf → bf) (λ _ → refl) (λ _ _ _ ib → ib)
        }

      mr-of : InputAt mIn alloc x s → MachineRefinesObsF prog base n l (snd {A} {B}) x s alloc cl rs k
      mr-of (in-loc pair-loc pv lv eq) =
        done (get-run B (size A) fs₀ pair-loc nh (λ i f → span 0 i f) eq lv
               (PairValidWF.snd-cell (decomposePairWF pv)))
      mr-of (in-reg () _)
      mr-of (in-unit ())

  -- ── `out-μ` — DISCHARGED. A Lambek inverse compiling (at an unboxed
  -- functor, D366) to the same `mov-to-output ∷ []` as `id`, and DOMAIN-RESTRICTED in a way
  -- that kills two of the three input residences outright:
  --   * `in-reg` carries `FitsInRegI (μ-type F)`, and `FitsInRegI` has only
  --     `fits-int`/`fits-float` — absurd;
  --   * `in-unit` claims `μ-type F ≡ Unit` — absurd by constructor disjointness.
  -- So only the pointer residence survives, and the value witness is exactly
  -- the layer iso: `valid-μ-wf` CARRIES the layer's own `ValidAtWF`
  -- (Plan 0.27 Option 3), so destructing one yields what `at-loc` wants.
  -- D366: at an UNBOXED functor (`MuRep`) `out-μ` is `mov-to-output`; the
  -- clause is stated over that trace equation (`teq`), so one proof serves
  -- every such functor.
  obs-correct-out-μ-mov : ∀ {F} (wf : WellFormedFI F) → Unboxed F
                        → (∀ n l → emitted n l (out-μ wf) ≡ mov-to-output ∷ [])
                        → IRObsCorrectF (out-μ wf)
  obs-correct-out-μ-mov {F} wf ub teq n l prog base _ cr span _ _ mIn x s alloc cl _ nh rdi-eq k rs =    record
      { traces-agree = sym (denot-[] k)
      ; value-realized =
          realized 1 fs₁ mIn (falloc fs₁) ((nh , span 0 _ (cong (λ t → fetch t 0) (teq n l))) ∷ []) (λ _ → nh)
                   (λ _ → cong (λ t → length t + base) (sym (teq n l))) (λ ()) (λ _ → refl) (λ _ → refl) (log-pure {s})
                   (λ { refl → place rdi-eq }) (m≤m+n k _) (λ _ → (λ fr j _ → mem-eq (AtStack fr j))) (λ _ → (λ hl _ → mem-eq (AtDynamic hl))) (λ _ → refl) (λ _ → (λ _ _ bf → bf)) (λ _ → refl) (λ _ _ _ ib → ib)
      }
    where
      regs' = writeReg (regs s) Output (readReg (regs s) Input1)
      fs₁   = flat-exec-instr mov-to-output prog (entry-flat base s alloc cl rs)

      denot-[] : ∀ k → eventsAt s (⟪ evalᴰ (out-μ wf) x ⟫ k) ≡ []
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
                  (retVal (evalᴰ (out-μ wf) x)) il
                  (floc fs₁)
      valid'' il bf v = subst (λ a → ValidAtWF mIn a (retVal (evalᴰ (out-μ wf) x)) il
                               (floc fs₁))
                      (sym keeps-alloc) (μ-layer-iso wf x ub (valid' il bf v))

      out-ptr : ∀ (il : ValueLocation FS) → readReg (regs s) Input1 ≡ SV-Ptr il
              → readReg (regs (floc fs₁)) Output
                ≡ SV-Ptr il
      out-ptr il eq =
        trans (writeReg-same (regs s) Output (readReg (regs s) Input1)) eq

      before' : ∀ (il : ValueLocation FS) → Live alloc il
              → Live (falloc fs₁) il
      before' il bf = bf

      place : InputAt mIn alloc x s
            → ResultPlace (⟦ F ⟧TI (μ-type F)) mIn (falloc fs₁)
                (falloc fs₁) (retVal (evalᴰ (out-μ wf) x))
                (floc fs₁)
      place (in-loc il v bf eq) =
        at-loc il (valid'' il (live→bf bf) v) (before' il bf) (out-ptr il eq)
                  (valid'' il (live→bf bf) v) (before' il bf)
      place (in-reg () _)
      place (in-unit ())

  -- D366: at a BOXED functor (`K Int`/`K Float`) the μ is a block whose first
  -- word holds the layer, a scalar, so `out-μ` is `load-at 0` — `get` of the
  -- layer at word 0 (plan 0.123 B.4 α), and its proof is `fst`'s.
  obs-correct-out-μ-box : ∀ {F} (wf : WellFormedFI F) → mu-rep F ≡ mu-box
                        → (∀ n l → emitted n l (out-μ wf) ≡ load-at 0 ∷ [])
                        → IRObsCorrectF (out-μ wf)
  obs-correct-out-μ-box {F} wf bx teq n l prog base _ cr span _ _ mIn x s alloc cl _ nh inp k rs = mr-of inp
    where
      fs₀ = entry-flat base s alloc cl rs
      L   = ⟦ F ⟧TI (μ-type F)
      v   = retVal (evalᴰ (out-μ wf) x)

      denot-[] : ∀ k → eventsAt s (⟪ evalᴰ (out-μ wf) x ⟫ k) ≡ []
      denot-[] k = refl

      fit : FitsInRegI L
      fit = box-fit bx

      -- the emitted text is `get L 0`
      at : ∀ i → fetch (get L 0) 0 ≡ just i → fetch prog (fpc fs₀) ≡ just i
      at i f = span 0 i (trans (cong (λ t → fetch t 0) (teq n l))
                               (trans (cong (λ t → fetch t 0) (sym (get-word 0 (scalar-kind fit)))) f))

      done : GetC.GetOut {FS} {prog} L v fs₀
           → MachineRefinesObsF prog base n l (out-μ wf) x s alloc cl rs k
      done g = record
        { traces-agree = trans (GetOut.silent g) (sym (denot-[] k))
        ; value-realized =
            realized 1 (setOut fs₀ (GetOut.out g)) (GetOut.mode g) alloc (GetOut.step g)
              (λ _ → nh) (λ _ → cong (λ t → length t + base) (sym (teq n l))) (λ ()) (λ _ → refl) (λ _ → refl)
              (log-of (GetOut.step g) (trans (GetOut.silent g) (sym (denot-[] k))))
              (λ { refl → GetOut.place g })
              (m≤m+n k _)
              (λ _ fr j _ → out-mem fs₀ (GetOut.out g) (AtStack fr j)) (λ _ hl _ → out-mem fs₀ (GetOut.out g) (AtDynamic hl))
              (λ _ → refl) (λ _ _ _ bf → bf) (λ _ → refl) (λ _ _ _ ib → ib)
        }

      mr-of : InputAt mIn alloc x s
            → MachineRefinesObsF prog base n l (out-μ wf) x s alloc cl rs k
      mr-of (in-loc box-loc pv lv eq) =
        done (get-run L 0 fs₀ box-loc nh at eq lv
               (subst (λ z → CellAt {prog = prog} alloc L v z s) (sym (offset-zero box-loc))
                      (μ-box-cell {wf = wf} bx pv)))
      mr-of (in-reg () _)
      mr-of (in-unit ())

  -- …dispatched on the functor's shape, where the trace reduces.
  obs-correct-out-μ : ∀ {F} (wf : WellFormedFI F) → IRObsCorrectF (out-μ wf)
  obs-correct-out-μ wf@(wf-K base-Int)        = obs-correct-out-μ-box wf refl (λ _ _ → refl)
  obs-correct-out-μ wf@(wf-K base-Float)      = obs-correct-out-μ-box wf refl (λ _ _ → refl)
  obs-correct-out-μ wf@(wf-K base-Unit)       = obs-correct-out-μ-mov wf tt (λ _ _ → refl)
  obs-correct-out-μ wf@(wf-K base-Void)       = obs-correct-out-μ-mov wf tt (λ _ _ → refl)
  obs-correct-out-μ wf@(wf-K (base-Prod a b)) = obs-correct-out-μ-mov wf tt (λ _ _ → refl)
  obs-correct-out-μ wf@(wf-K (base-Sum a b))  = obs-correct-out-μ-mov wf tt (λ _ _ → refl)
  obs-correct-out-μ wf@wf-Id                  = obs-correct-out-μ-mov wf tt (λ _ _ → refl)
  obs-correct-out-μ wf@(wf-Sum f g)           = obs-correct-out-μ-mov wf tt (λ _ _ → refl)
  obs-correct-out-μ wf@(wf-Prod f g)          = obs-correct-out-μ-mov wf tt (λ _ _ → refl)

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
  -- (Both happened: D189 gave `Ana` and `in-ν` their two-cell emitter, and
  -- D199 reproved `Out` against it, in `IRObsCorrect.Out`.)

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
  obs-correct-const fits-int v n l prog base _ cr span _ _ mIn x s alloc cl _ nh rdi-eq k rs =    record
      { traces-agree = sym (denot-[] k)
      ; value-realized =
          realized 1 fs₁ mIn (falloc fs₁) ((nh , span 0 _ refl) ∷ []) (λ _ → nh) (λ _ → refl) (λ ()) (λ _ → refl) (λ _ → refl) (log-pure {s})
                   (λ { refl → at-reg fits-int out-lit }) (m≤m+n k _) (λ _ → (λ fr j _ → mem-untouched (instr-load-const fits-intˢ v) s alloc (AtStack fr j) nhw-instr-load-const refl))
                   (λ _ → (λ hl _ → mem-untouched (instr-load-const fits-intˢ v) s alloc (AtDynamic hl) nhw-instr-load-const refl)) (λ _ → refl) (λ _ → (λ _ _ bf → bf)) (λ _ → refl) (λ _ _ _ ib → ib)
      }
    where
      instr = instr-load-const fits-intˢ v
      fs₁   = flat-exec-instr instr prog (entry-flat base s alloc cl rs)


      ev-[] : ∀ pc i → fetch (emitted n l (const fits-int v)) pc ≡ just i → ∀ fs → event-of i fs ≡ []
      ev-[] zero    .instr refl fs = refl
      ev-[] (suc n) i      ()   fs

      mach-[] : ∀ f → proj₁ (flat-events f (emitted n l (const fits-int v)) (entry-flat 0 s alloc cl rs)) ≡ []
      mach-[] f = flat-events-[] (emitted n l (const fits-int v)) ev-[] f (entry-flat 0 s alloc cl rs)

      denot-[] : ∀ k → eventsAt s (⟪ evalᴰ (const fits-int v) x ⟫ k) ≡ []
      denot-[] k = refl

      keeps-alloc : falloc fs₁ ≡ alloc
      keeps-alloc = refl

      out-lit : readReg (regs (floc fs₁)) Output
              ≡ prim-sv fits-int (retVal (evalᴰ (const fits-int v) x))
      -- D115: the machine MATERIALISES the literal, exactly as the float
      -- case below does — `lit-value` is two's complement at this width.
      out-lit =
        writeReg-same (regs s) Output (SV-Lit fits-intˢ (SMCore.AbstractExec.lit-value {FS} fits-intˢ v))

  obs-correct-const fits-float v n l prog base _ cr span _ _ mIn x s alloc cl _ nh rdi-eq k rs =    record
      { traces-agree = sym (denot-[] k)
      ; value-realized =
          realized 1 fs₁ mIn (falloc fs₁) ((nh , span 0 _ refl) ∷ []) (λ _ → nh) (λ _ → refl) (λ ()) (λ _ → refl) (λ _ → refl) (log-pure {s})
                   (λ { refl → at-reg fits-float out-lit }) (m≤m+n k _) (λ _ → (λ fr j _ → mem-untouched (instr-load-const fits-floatˢ v) s alloc (AtStack fr j) nhw-instr-load-const refl))
                   (λ _ → (λ hl _ → mem-untouched (instr-load-const fits-floatˢ v) s alloc (AtDynamic hl) nhw-instr-load-const refl)) (λ _ → refl) (λ _ → (λ _ _ bf → bf)) (λ _ → refl) (λ _ _ _ ib → ib)
      }
    where
      instr = instr-load-const fits-floatˢ v
      fs₁   = flat-exec-instr instr prog (entry-flat base s alloc cl rs)


      ev-[] : ∀ pc i → fetch (emitted n l (const fits-float v)) pc ≡ just i → ∀ fs → event-of i fs ≡ []
      ev-[] zero    .instr refl fs = refl
      ev-[] (suc n) i      ()   fs

      mach-[] : ∀ f → proj₁ (flat-events f (emitted n l (const fits-float v)) (entry-flat 0 s alloc cl rs)) ≡ []
      mach-[] f = flat-events-[] (emitted n l (const fits-float v)) ev-[] f (entry-flat 0 s alloc cl rs)

      denot-[] : ∀ k → eventsAt s (⟪ evalᴰ (const fits-float v) x ⟫ k) ≡ []
      denot-[] k = refl

      keeps-alloc : falloc fs₁ ≡ alloc
      keeps-alloc = refl

      out-lit : readReg (regs (floc fs₁)) Output
              ≡ prim-sv fits-float (retVal (evalᴰ (const fits-float v) x))
      -- Plan 0.73 (D113): the machine MATERIALISES the literal as it executes —
      -- `exec-abstract` writes `round (float-format FS) v`, not the payload.
      -- The denotation says the same because `eval` above is at the same
      -- format; that agreement is the whole point of reading it from one place.
      out-lit =
        writeReg-same (regs s) Output (SV-Lit fits-floatˢ (round (FrameSemantics.float-format FS) v))

  -- THE POSTULATE BLOCK THAT STOOD HERE IS GONE (D366). Its history:
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
    --
    -- D366 (2026-10-31): THAT CASE MADE THE POSTULATE FALSE, and so did a second
    -- one. At `K Int`/`K Float` with the layer in a register, `Output` held a
    -- LITERAL, and no `ResultPlace (μ-type F)` fits a literal (refuted with no
    -- postulate). The fix is not a residence in `ResultPlace` but the EMITTER:
    -- `In` boxes an inline layer (`MuRep`), so a μ is a heap pointer at every
    -- functor, and `obs-correct-In` is a proof (`IRObsCorrect.InMu`).

    -- (`obs-correct-pair` MOVED OUT — DISCHARGED, D211. It is
    -- `PairAssemble.obs-correct-pair-proof`, assembled from `Pair.agda`'s four
    -- clusters; D202's "takes the SUB-PROOFS" shape is what made it provable,
    -- and the file keeps that shape — the induction hypotheses are arguments,
    -- so no clause calls back into `ir-obs-correct`.)

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
    -- WHAT BLOCKS THIS IS KNOWN AGAIN (2026-09-21), and half of it is now
    -- built. The line here said "NOW UNKNOWN"; that was true when two of the
    -- three recorded obstacles dissolved, and it is no longer.
    --
    -- `case` is the ONLY label-bearing per-constructor postulate left (`curry`
    -- was reclassified out by D159, `Cata` is `cata-correct`), so there is no
    -- discharged sibling to model on. It needs:
    --
    --   1. THE CONVERSE OF `find-label-sound` — a jump lands where the label
    --      is. This did NOT exist (`grep find-label-complete` → nothing) and
    --      now does: `Once.CCC.Codegen.LabelResolve` (`fl-hit`,
    --      `label-resolves`, `NoLabel`/`no-label-miss`, `noLabel-outside`),
    --      the `once`-namespace mirror of the `thunk`-namespace lemmas in
    --      `BlockLayout`. Zero postulates.
    --
    --      NOTE what it is NOT: `EmittedWF.labels-unique`. That is about
    --      `labels-def`, which RECURSED into the (since retired) nested instructions;
    --      `fl-go` scans with `label-of?`, which does not. Proving
    --      `labels-unique` would have been a large induction aimed slightly
    --      off target. What the scan needs is CONTAINMENT, and
    --      `LabelScope.labels-in` already had it.
    --
    --   2. THE DISJOINTNESS PLUMBING — `[lo,hi)` window facts from
    --      `label-mono` at each use site, so `noLabel-outside` applies.
    --      Mechanical.
    --
    --   3. THE BRANCH CORRESPONDENCE — the machine takes the branch the
    --      denotation's scrutinee selects. `inj₁` ⇒ `c-branch-tag-zero` fires
    --      and control lands on `c-label (ℓ o l)`; `inj₂` ⇒ it does not, `gt`
    --      runs and `c-jmp (ℓ o (suc l))` reaches the join. THIS has no model
    --      anywhere — no discharged constructor has control flow — and it is
    --      the real remaining work. Calibration: `Sum.agda` is 807 lines for
    --      the straight-line `inl`/`inr`.
    --
    -- The three recorded obstacles, for the record — two were already gone:
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
    -- (`obs-correct-case` MOVED OUT — discharged in `Case.agda`. The branch
    -- correspondence needed no new machine model: the tag is the input's own
    -- residence, and `LabelsAt` says where the jumps land.)

    -- (`obs-correct-apply` MOVED OUT — discharged below, D188.)

    -- CLASS G — THE EMITTER IS MISSING. Compiles to `[]`, so the obligation is
    -- refutable whenever the denotation emits an event. NOT a proof task:
    -- implement the codegen, restrict the IR so it cannot be built, or
    -- condition the obligation to exclude it (Plan 0.68 step 5).
    --
    -- plan 0.98 TOOK THE SECOND OPTION for `Para`/`Hylo`/`Fuse`: the
    -- constructors are DELETED, so `obs-correct-Para`/`-Hylo`/`-Fuse` are gone
    -- rather than assumed. They were derived schemes (D062), unreachable from
    -- source, and their meaning was the last consumer of the pure `eval`.
    --
    -- (`obs-correct-in-ν` MOVED OUT — discharged in `TwoCell`, plan 0.88. It
    -- was not a codegen gap: D189 gave it the two-cell emitter. What it lacked
    -- was a WITNESS — the ν constructor spoke only of `Ana` — and `νOrigin`
    -- now indexes it by where the ν came from.)
    -- D189: `obs-correct-Ana` LEFT this class — the emitter exists and the case
    -- is discharged below. D199: `obs-correct-Out` left it too, from the other
    -- direction — it was FALSE while the machine did not re-suspend, and is
    -- proved below now that it does.

