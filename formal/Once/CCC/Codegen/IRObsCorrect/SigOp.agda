-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.IRObsCorrect.SigOp
--
-- D200: the `SigOp` clause. Plan 0.105: dispatched on the CONTRACT
-- (`SigOpSem`), not on its effect shape — the shape is derived from the
-- contract, and the denotation (`sigOpSemT`) and the machine (`effect-of`)
-- both read the contract, so one `cong` on `sem si` aligns them.
--
--   * an internal or pure FFI contract (`pureV`/`primV`/`ffiV`) computes a
--     value in a register and makes no call;
--   * an emitting one (`emitsV`) is a call answered by `⊤`;
--   * a halting one (`haltsV`) is a call that ends the program;
--   * an answering one (`callsV`) is a call the WORLD answers — the machine
--     reads the interpretation at its log (`call-sigop-val`), the denotation
--     runs the call node from the same log.
--
-- What does not fit a register (a non-register codomain, an unreadable input)
-- routes to `obs-correct-sigop-rest`.
------------------------------------------------------------------------

open import Once.CanonicalName using (CanonicalName)

import Data.List as DL
open import Once.Denotation.Program using (IRFun; tableEnv)
module Once.CCC.Codegen.IRObsCorrect.SigOp (o : CanonicalName) (tbl : DL.List IRFun) where

open import Once.CCC.Codegen.IRObsCorrect.Machine o tbl
open import Once.Type using () renaming (Unit to Unitᵀ; Void to Voidᵀ)
open import Once.Functor.Translate using (IsBaseType; base-Unit; base-Void; base-Int; base-Float; base-Str; base-Buffer; base-Prod; base-Sum)
open import Function using () renaming (id to idᶠ)
open import Data.List.Properties using (++-identityʳ)
open import Once.Denotation.Trace using (mk-event)

import Once.CCC.FrameSemantics
import Once.CCC.Machine.SMPrimitives
import Once.IRTy
import Once.IR
import Once.Semantics.Machine as EvV
import Once.Denotation.DenotTrace as DT
import Once.Denotation.TraceMonad as TM
open import Once.Denotation.ValueDomain using (forgetᵇ; injectᵇ; cohᴰ)
open import Once.Res using (Res; stopped; returns; returns-inj)
open import Data.Product using (Σ)
open import Once.Spec.Contract using (key; yes-of; _∈K?_)
open import Relation.Nullary using (Dec; yes; no)
open import Once.Type using (isUnit?)
open import Once.Denotation.Program using (Declared; Declared-at)
open import Once.CanonicalName using (showCanonical)
open import Once.Res using (is-stopped)
open import Once.SigOp.Info using (SigOpSem; sem; effect-of; semM; baseA; conB; name;
                                   pureV; primV; emitsV; haltsV; ffiV; callsV)

module SigOpC {FS : FrameSemantics} where

  open Core {FS}
  open FlatEventTrace {FS} using (ev-of-loc)
  open Mach {FS}
  open AbstractExec {FS} using (decode-arg; machine-event; sigop-events; sigop-events-of; exec-sigop-output; res-sv; call-sigop-val; call-sigop-output; call-sigop-ans)

  private
    fmt = Once.CCC.FrameSemantics.fs-numerics FS
    φ   = TM.pureHalf ιᶠ
    -- plan 0.105: the signatures the machine's interpretation declares.
    σᶠ  = TM.sig ιᶠ

  ------------------------------------------------------------------------
  -- The denotation of a SigOp node, at its contract. A SigOp's argument and
  -- result are first-order, so they cross the value domains at the info's
  -- base-type witnesses (`DenotTrace`'s `SigOp` clause).
  ------------------------------------------------------------------------
  argOf : ∀ {A B} → SigOpInfo A B → ⟦ ⌊ A ⌋ ⟧ → EvV.⟦ A ⟧
  argOf {A} si x = forgetᵇ (baseA si) (subst idᶠ (cohᴰ A) x)

  resOf : ∀ {A B} → SigOpInfo A B → EvV.⟦ B ⟧ → ⟦ ⌊ B ⌋ ⟧
  resOf {B = B} si v = subst idᶠ (sym (cohᴰ B)) (injectᵇ (conB si) v)

  evalᴰ-at : ∀ {A B} (si : SigOpInfo A B) (c : SigOpSem A B) → sem si ≡ c → ∀ x
           → evalᴰ (SigOp si) x ≡ TM.fmapT (resOf si) (DT.sigOpSemT fmt φ si c (argOf si x))
  evalᴰ-at si c e x = cong (λ c′ → TM.fmapT (resOf si) (DT.sigOpSemT fmt φ si c′ (argOf si x))) e

  -- …and the machine's three readings of the same contract.
  events-at : ∀ {A B} (si : SigOpInfo A B) (c : SigOpSem A B) → sem si ≡ c → ∀ s
            → sigop-events si s ≡ sigop-events-of (effect-of c) si s
  events-at si c e s = cong (λ c′ → sigop-events-of (effect-of c′) si s) e

  output-at : ∀ {A B} (si : SigOpInfo A B) (c : SigOpSem A B) → sem si ≡ c → ∀ s
            → exec-sigop-output si s ≡ exec-sigop-output-of (effect-of c) si s
  output-at si c e s = cong (λ c′ → exec-sigop-output-of (effect-of c′) si s) e

  halts-at : ∀ {A B} (si : SigOpInfo A B) (c : SigOpSem A B) → sem si ≡ c → ∀ s
           → exec-sigop-halts si s ≡ exec-sigop-halts-of (effect-of c) si s
  halts-at si c e s = cong (λ c′ → exec-sigop-halts-of (effect-of c′) si s) e

  ------------------------------------------------------------------------
  -- THE ARGUMENT CORRESPONDENCE: the argument the machine decodes is the one
  -- the denotation passes. It splits on the DOMAIN's base type:
  --   * `Unit` — `⟦ Unit ⟧` is `⊤`, so the two agree by η (D074);
  --   * `Int`/`Float` REGISTER-RESIDENT — `decode-arg`'s two real clauses.
  -- What is left is a BOXED base argument: D114's `decode-unread` hole,
  -- restated where it is consumed.
  ------------------------------------------------------------------------
  postulate
    decode-boxed : ∀ {A : Type} (bt : IsBaseType A) {mIn alloc}
                     (x : ⟦ ⌊ A ⌋ ⟧) (s : LocState FS)
                 → InputAt {⌊ A ⌋} mIn alloc x s
                 → decode-arg bt (readReg (regs s) Input1) ≡ forgetᵇ bt (subst idᶠ (cohᴰ A) x)

  arg-agree : ∀ {A : Type} (bt : IsBaseType A) {mIn alloc}
                (x : ⟦ ⌊ A ⌋ ⟧) (s : LocState FS)
            → InputAt {⌊ A ⌋} mIn alloc x s
            → decode-arg bt (readReg (regs s) Input1) ≡ forgetᵇ bt (subst idᶠ (cohᴰ A) x)
  arg-agree base-Unit  x s inp = refl
  arg-agree base-Int   x s (in-reg fits-int   eq) rewrite eq = refl
  arg-agree base-Float x s (in-reg fits-float eq) rewrite eq = refl
  arg-agree bt         x s inp = decode-boxed bt x s inp

  -- The event a calling SigOp's step logs IS the call the denotation makes.
  event-agree : ∀ {A B} (si : SigOpInfo A B) {mIn alloc} (x : ⟦ ⌊ A ⌋ ⟧) (s : LocState FS)
              → InputAt {⌊ A ⌋} mIn alloc x s
              → machine-event si (readReg (regs s) Input1)
                ≡ mk-event (name si) A (baseA si) (argOf si x)
  event-agree {A} si x s inp = cong (mk-event (name si) A (baseA si)) (arg-agree (baseA si) x s inp)

  ------------------------------------------------------------------------
  -- ONE SigOp STEP, as an obligation witness. Every contract runs the same
  -- single instruction; what differs is what it logs, whether it halts and
  -- where its result is — so those are the builder's arguments.
  ------------------------------------------------------------------------
  module Step {A B} (si : SigOpInfo A B)
              (n l : ℕ) (prog : AbstractTrace) (base : ℕ)
              (span : SpanAt prog base (emitted n l (SigOp si)))
              (x : ⟦ ⌊ A ⌋ ⟧) (s : LocState FS) (alloc : AllocState {FS}) (cl : StoredValue FS)
              (nh : halted s ≡ false) where

    E : TM.T ⟦ ⌊ B ⌋ ⟧
    E = evalᴰ (SigOp si) x

    fs₁ : FlatState
    fs₁ = flat-exec-instr (instr-sigop si) prog (entry-flat base s alloc cl)

    build : (ev-eq : sigop-events si s ≡ eventsAt s E)
          → (stopsAt s E ≡ false → exec-sigop-halts si s ≡ false)
          → (stopsAt s E ≡ true  → exec-sigop-halts si s ≡ true)
          → (∀ {v} → resultAt s E ≡ returns v
               → ResultPlace ⌊ B ⌋ Stack (falloc fs₁) (falloc fs₁) v (floc fs₁))
          → ∀ k → MachineRefinesObsF prog base n l (SigOp si) x s alloc cl k
    build ev-eq live stops place k = record
      { traces-agree = trans (++-identityʳ _) ev-eq
      ; value-realized =
          realized 1 fs₁ Stack (falloc fs₁) ((nh , span 0 _ refl) ∷ [])
                   live (λ _ → refl) stops refl refl
                   (cong (LocState.ev-log s DL.++_) ev-eq)
                   place
                   -- D204: `exec-abstract (instr-sigop si)` writes the Output
                   -- register, the halt flag and the log — memory is untouched
                   -- whatever the SigOp means.
                   (λ fr j _ → mem-untouched (instr-sigop si) s alloc (AtStack fr j) nhw-instr-sigop refl)
                   (λ hl _ → mem-untouched (instr-sigop si) s alloc (AtDynamic hl) nhw-instr-sigop refl)
                   refl (λ _ _ bf → bf)
      }

  ------------------------------------------------------------------------
  -- A REGISTER RESULT. At a register-fitting codomain the result coercion is
  -- the identity, so the value the machine writes is the value the
  -- denotation returns.
  ------------------------------------------------------------------------
  res-reg : ∀ {B} (fit : FitsInReg B) (ib : IsBaseType B) (v : EvV.⟦ B ⟧)
          → SV-Lit fit v ≡ prim-sv (fits-erase fit) (subst idᶠ (sym (cohᴰ B)) (injectᵇ ib v))
  res-reg fits-intˢ   base-Int   v = refl
  res-reg fits-floatˢ base-Float v = refl

  -- A register-fitting input crosses unchanged.
  forget-reg : ∀ (bt : IsBaseType Intˢ) (x : EvV.⟦ Intˢ ⟧) → x ≡ forgetᵇ bt x
  forget-reg base-Int x = refl

  -- THE INPUT A CALL-FREE CONTRACT READS is the denotation's argument, in
  -- every residence: through the pointer (`readTyped-adequate`, at the info's
  -- own witness), from the register, or — for a unit input — by η.
  pure-input-aux : ∀ {A B} (si : SigOpInfo A B) (fit : FitsInReg B) (rA : Readable A)
                     {mIn alloc} (x : ⟦ ⌊ A ⌋ ⟧) (s : LocState FS)
                 → InputAt {⌊ A ⌋} mIn alloc x s
                 → pure-sigop-out-aux si s (just fit) (sv-as-loc (readReg (regs s) Input1))
                   ≡ pure-sigop-out-val si fit (just (argOf si x))
  pure-input-aux {A} si fit rA x s (in-loc loc valid _ eq) rewrite eq =
    cong (pure-sigop-out-val si fit) (readTyped-adequate {A = A} rA (baseA si) {v = x} valid)
  pure-input-aux si fit r-int x s (in-reg fits-int eq) =
    -- the register branch re-reads `Input1`, so the equation is spent twice
    trans (cong (λ sv → pure-sigop-out-aux si s (just fit) (sv-as-loc sv)) eq)
          (trans (cong (λ sv → pure-sigop-out-val si fit (readReg-typed Intˢ sv)) eq)
                 (cong (λ a → pure-sigop-out-val si fit (just a)) (forget-reg (baseA si) x)))
  pure-input-aux si fit r-unit x s (in-unit refl) =
    pure-sigop-out-unit-any (sv-as-loc (readReg (regs s) Input1))
    where
      pure-sigop-out-unit-any : ∀ ml → pure-sigop-out-aux si s (just fit) ml ≡ pure-sigop-out-val si fit (just tt)
      pure-sigop-out-unit-any (just _) = refl
      pure-sigop-out-unit-any nothing  = refl
  pure-input-aux si fit r-unit       x s (in-reg () _)
  pure-input-aux si fit (r-pair _ _) x s (in-reg () _)
  pure-input-aux si fit r-int        x s (in-unit ())
  pure-input-aux si fit (r-pair _ _) x s (in-unit ())

  pure-input : ∀ {A B} (si : SigOpInfo A B) (fit : FitsInReg B) (rA : Readable A)
                 {mIn alloc} (x : ⟦ ⌊ A ⌋ ⟧) (s : LocState FS)
             → InputAt {⌊ A ⌋} mIn alloc x s
             → pure-sigop-output si s ≡ pure-sigop-out-val si fit (just (argOf si x))
  pure-input si fits-intˢ   rA x s inp = pure-input-aux si fits-intˢ   rA x s inp
  pure-input si fits-floatˢ rA x s inp = pure-input-aux si fits-floatˢ rA x s inp

  -- A call-free contract's value, read the same way by the machine (`semM`)
  -- and the denotation (`sigOpSemT`).
  -- plan 0.105: a pure FFI contract is read at its DECLARATION — the shared
  -- membership decision is `yes`, so both readers take the implementation.
  pure-agree : ∀ {A B} (si : SigOpInfo A B) (c : SigOpSem A B) → effect-of c ≡ Pure → Declared-at σᶠ si c → ∀ a
             → Σ (EvV.⟦ B ⟧) λ w → (Once.SigOp.Info.semM-of φ (name si) c fmt a ≡ returns w)
                                  × (DT.sigOpSemT fmt φ si c a ≡ TM.ret w)
  pure-agree si (pureV f)  _ _ a = _ , refl , refl
  pure-agree si (primV p)  _ _ a = _ , refl , refl
  pure-agree {A} {B} si ffiV _ d a =
    TM.pure ιᶠ k (proj₁ y) a
    , cong (λ dd → TM.pureHalf-at ιᶠ k dd a) (proj₂ y)
    , cong (λ dd → TM.resT (TM.pureHalf-at ιᶠ k dd a)) (proj₂ y)
    where k = key (showCanonical (name si)) A B
          y = yes-of d
  pure-agree si (emitsV _) () _ a
  pure-agree si (haltsV _) () _ a
  pure-agree si callsV     () _ a

  ------------------------------------------------------------------------
  -- The four contract classes.
  ------------------------------------------------------------------------
  pure-obs : ∀ {A B} (si : SigOpInfo A B) (c : SigOpSem A B) → sem si ≡ c → effect-of c ≡ Pure
           → Declared-at σᶠ si c → FitsInReg B → Readable A → IRObsCorrectF (SigOp si)
  pure-obs {A} {B} si c e eff d fit rA n l prog base _ _ span _ _ mIn x s alloc cl _ nh inp =
    S.build ev-eq (λ _ → trans (halts-at si c e s) (cong (λ z → exec-sigop-halts-of z si s) eff))
                  (λ st → case trans (sym stops-f) st of λ ())
                  place
    where
      module S = Step si n l prog base span x s alloc cl nh
      a = argOf si x
      w = proj₁ (pure-agree si c eff d a)
      E≡ : evalᴰ (SigOp si) x ≡ TM.ret (resOf si w)
      E≡ = trans (evalᴰ-at si c e x) (cong (TM.fmapT (resOf si)) (proj₂ (proj₂ (pure-agree si c eff d a))))
      ev-eq : sigop-events si s ≡ eventsAt s (evalᴰ (SigOp si) x)
      ev-eq = trans (events-at si c e s)
                (trans (cong (λ z → sigop-events-of z si s) eff) (sym (cong (eventsAt s) E≡)))
      stops-f : stopsAt s (evalᴰ (SigOp si) x) ≡ false
      stops-f = cong (stopsAt s) E≡
      out≡ : exec-sigop-output si s ≡ prim-sv (fits-erase fit) (resOf si w)
      out≡ = trans (output-at si c e s)
              (trans (cong (λ z → exec-sigop-output-of z si s) eff)
               (trans (pure-input si fit rA x s inp)
                (trans (cong (λ r → res-sv fit r)
                         (trans (cong (λ c′ → Once.SigOp.Info.semM-of φ (name si) c′ fmt a) e)
                                (proj₁ (proj₂ (pure-agree si c eff d a)))))
                       (res-reg fit (conB si) w))))
      place : ∀ {v} → resultAt s (evalᴰ (SigOp si) x) ≡ returns v
            → ResultPlace ⌊ B ⌋ Stack (falloc S.fs₁) (falloc S.fs₁) v (floc S.fs₁)
      place p = subst (λ v → ResultPlace ⌊ B ⌋ Stack (falloc S.fs₁) (falloc S.fs₁) v (floc S.fs₁))
                  (returns-inj (trans (sym (cong (resultAt s) E≡)) p))
                  (at-reg (fits-erase fit)
                    (trans (writeReg-same (regs s) Output (exec-sigop-output si s)) out≡))

  emits-obs : ∀ {A} (si : SigOpInfo A Unitᵀ) → sem si ≡ emitsV refl → IRObsCorrectF (SigOp si)
  emits-obs {A} si e n l prog base _ _ span _ _ mIn x s alloc cl _ nh inp =
    S.build ev-eq (λ _ → halts-at si (emitsV refl) e s)
                  (λ st → case trans (sym (cong (stopsAt s) E≡)) st of λ ())
                  (λ _ → unit-result)
    where
      module S = Step si n l prog base span x s alloc cl nh
      E≡ = evalᴰ-at si (emitsV refl) e x
      ev-eq : sigop-events si s ≡ eventsAt s (evalᴰ (SigOp si) x)
      ev-eq = trans (events-at si (emitsV refl) e s)
                (trans (cong (DL._∷ DL.[]) (event-agree si x s inp)) (sym (cong (eventsAt s) E≡)))

  halts-obs : ∀ {A} (si : SigOpInfo A Voidᵀ) → sem si ≡ haltsV refl → IRObsCorrectF (SigOp si)
  halts-obs {A} si e n l prog base _ _ span _ _ mIn x s alloc cl _ nh inp =
    S.build ev-eq (λ lv → case trans (sym (cong (stopsAt s) E≡)) lv of λ ())
                  (λ _ → halts-at si (haltsV refl) e s)
                  (λ p → case trans (sym (cong (resultAt s) E≡)) p of λ ())
    where
      module S = Step si n l prog base span x s alloc cl nh
      E≡ = evalᴰ-at si (haltsV refl) e x
      ev-eq : sigop-events si s ≡ eventsAt s (evalᴰ (SigOp si) x)
      ev-eq = trans (events-at si (haltsV refl) e s)
                (trans (cong (DL._∷ DL.[]) (event-agree si x s inp)) (sym (cong (eventsAt s) E≡)))

  -- THE WORLD ANSWERS. The machine writes the interpretation's answer at its
  -- log (`call-sigop-val`); the denotation's call node, run from the same
  -- log, is answered by the same interpretation at the same history.
  -- A register-fitting value is never `Unit`.
  fits-not-unit : ∀ {B} → FitsInReg B → B ≡ Unitᵀ → ⊥
  fits-not-unit fits-intˢ   ()
  fits-not-unit fits-floatˢ ()

  -- plan 0.105: at its DECLARATION — the shared membership decision is `yes`.
  calls-obs : ∀ {A B} (si : SigOpInfo A B) → sem si ≡ callsV → Declared-at σᶠ si callsV → FitsInReg B → IRObsCorrectF (SigOp si)
  calls-obs {A} {B} si e d fit n l prog base _ _ span _ _ mIn x s alloc cl _ nh inp =
    S.build ev-eq (λ _ → halts-at si callsV e s)
                  (λ st → case trans (sym (cong is-stopped res-call)) (trans (sym (cong (stopsAt s) E≡)) st) of λ ())
                  place
    where
      module S = Step si n l prog base span x s alloc cl nh
      E≡ = evalᴰ-at si callsV e x
      op = TM.callOp (name si) A (baseA si) B
      y  = yes-of d
      p₀ = proj₁ y
      ans = TM.answer ιᶠ (LocState.ev-log s) op p₀ (argOf si x)
      -- the run of the call node, at the decided `yes`
      run-call : TM.run ιᶠ (LocState.ev-log s) (TM.fmapT (resOf si) (TM.call op (argOf si x) TM.ret))
               ≡ (TM.callEvent op (argOf si x) DL.∷ DL.[] , returns (resOf si ans))
      run-call = cong (TM.run-call ιᶠ (LocState.ev-log s) op (argOf si x) (λ b → TM.ret (resOf si b))) ans-eq
        where
          -- an answering call's result fits a register, so it is not `Unit`:
          -- the implementation answers it, at the decided `yes`
          ans-eq : TM.callAnswer ιᶠ (LocState.ev-log s) op (argOf si x) ≡ just ans
          ans-eq = go (isUnit? B)
            where go : (du : Dec (B ≡ Unitᵀ))
                     → TM.callAnswer-at ιᶠ (LocState.ev-log s) op (argOf si x) du (TM.callKey op ∈K? TM.calls ιᶠ) ≡ just ans
                  go (yes u) = ⊥-elim (fits-not-unit fit u)
                  go (no nu) = cong (TM.callAnswer-at ιᶠ (LocState.ev-log s) op (argOf si x) (no nu)) (proj₂ y)
      res-call : resultAt s (TM.fmapT (resOf si) (TM.call op (argOf si x) TM.ret)) ≡ returns (resOf si ans)
      res-call = cong proj₂ run-call
      ev-eq : sigop-events si s ≡ eventsAt s (evalᴰ (SigOp si) x)
      ev-eq = trans (events-at si callsV e s)
                (trans (cong (DL._∷ DL.[]) (event-agree si x s inp))
                  (trans (sym (cong proj₁ run-call)) (sym (cong (eventsAt s) E≡))))
      out≡ : ∀ (f : FitsInReg B) → call-sigop-val si s (just f) ≡ prim-sv (fits-erase f) (resOf si ans)
      out≡ f = trans (cong (λ dd → call-sigop-ans si s f dd) (proj₂ y))
                (trans (cong (λ a → SV-Lit f (TM.answer ιᶠ (LocState.ev-log s) op p₀ a))
                           (arg-agree (baseA si) x s inp))
                     (res-reg f (conB si) ans))
      out-fit : ∀ (f : FitsInReg B) → call-sigop-output si s ≡ prim-sv (fits-erase f) (resOf si ans)
      out-fit fits-intˢ   = out≡ fits-intˢ
      out-fit fits-floatˢ = out≡ fits-floatˢ
      place : ∀ {v} → resultAt s (evalᴰ (SigOp si) x) ≡ returns v
            → ResultPlace ⌊ B ⌋ Stack (falloc S.fs₁) (falloc S.fs₁) v (floc S.fs₁)
      place p = subst (λ v → ResultPlace ⌊ B ⌋ Stack (falloc S.fs₁) (falloc S.fs₁) v (floc S.fs₁))
                  (returns-inj (trans (sym res-call) (trans (sym (cong (resultAt s) E≡)) p)))
                  (at-reg (fits-erase fit)
                    (trans (writeReg-same (regs s) Output (exec-sigop-output si s))
                           (trans (output-at si callsV e s) (out-fit fit))))

  -- What has no register discharge: a non-register codomain, or an input the
  -- machine cannot read back. Its own row (Plan 0.68 step 0), not the
  -- whole-IR `obs-correct-rest`.
  postulate
    obs-correct-sigop-rest : ∀ {A B} (si : SigOpInfo A B) → IRObsCorrectF (SigOp si)

  -- The routing, by explicit-argument helpers (no `with`).
  pure-route : ∀ {A B} (si : SigOpInfo A B) (c : SigOpSem A B) → sem si ≡ c → effect-of c ≡ Pure → Declared-at σᶠ si c
             → Maybe (FitsInReg B) → Maybe (Readable A) → IRObsCorrectF (SigOp si)
  pure-route si c e eff d (just fit) (just rA) = pure-obs si c e eff d fit rA
  pure-route si c e eff d _          _         = obs-correct-sigop-rest si

  calls-route : ∀ {A B} (si : SigOpInfo A B) → sem si ≡ callsV → Declared-at σᶠ si callsV → Maybe (FitsInReg B) → IRObsCorrectF (SigOp si)
  calls-route si e d (just fit) = calls-obs si e d fit
  calls-route si e d nothing    = obs-correct-sigop-rest si

  by-sem : ∀ {A B} (si : SigOpInfo A B) (c : SigOpSem A B) → sem si ≡ c → Declared-at σᶠ si c → IRObsCorrectF (SigOp si)
  by-sem {A} {B} si (pureV f)     e d = pure-route si (pureV f) e refl d (fits-in-reg? B) (readable? A)
  by-sem {A} {B} si (primV p)     e d = pure-route si (primV p) e refl d (fits-in-reg? B) (readable? A)
  by-sem {A} {B} si ffiV          e d = pure-route si ffiV e refl d (fits-in-reg? B) (readable? A)
  by-sem         si (emitsV refl) e d = emits-obs si e
  by-sem         si (haltsV refl) e d = halts-obs si e
  by-sem {B = B} si callsV        e d = calls-route si e d (fits-in-reg? B)

  -- plan 0.105: at a SigOp the program's interpretation declares (`Linked`).
  obs-correct-sigop : ∀ {A B} (si : SigOpInfo A B) → Declared σᶠ si → IRObsCorrectF (SigOp si)
  obs-correct-sigop si d = by-sem si (sem si) refl d
