-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.IRObsCorrect.SigOp
--
-- D200: the `SigOp` clause. `pure-obs-correct-sigop` discharges the tractable
-- class directly — `Pure` + fits-in-reg, which is exactly `arith.block.*` —
-- and everything else routes to `obs-correct-sigop-rest`.
------------------------------------------------------------------------

open import Once.CanonicalName using (CanonicalName)

module Once.CCC.Codegen.IRObsCorrect.SigOp (o : CanonicalName) where

open import Once.CCC.Codegen.IRObsCorrect.Machine o
open import Once.Denotation.Trace using (mkEvent; mk-event)
open import Once.Type using () renaming (Unit to Unitᵀ)
open import Once.Functor.Translate using (IsBaseType; base-Unit; base-Void; base-Int; base-Float; base-Str; base-Buffer; base-Prod; base-Sum)

import Once.CCC.FrameSemantics
import Once.CCC.Machine.SMPrimitives
import Once.IRTy
import Once.IR
import Once.CCC.Eval as Ev
import Once.Semantics.Machine as EvV
import Once.CCC.Machine.ReadTypedAdequate as RTA
import Once.Denotation.DenotTrace as DT
import Once.Denotation.TraceMonad as TM
import Once.Denotation.ValueDomain as VD

module SigOpC {FS : FrameSemantics} where

  open Core {FS}
  open FlatEventTrace {FS} using (decode-arg; machine-event; ev-of-loc)
  open Mach {FS}


  -- ════════════════════════════════════════════════════════════════════
  -- `obs-correct-sigop` — the `SigOp` case carved OUT of `obs-correct-rest`
  -- and discharged DIRECTLY for the tractable class:
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
  -- `TM.valueT (evalᴰ (SigOp si) x) 0 = subst (sym (coh B)) (semM si (subst id (coh A) x))`
  -- (CCC.Eval:83) the two sides coincide modulo the `coh` transports (which are
  -- `refl` on the fits-in-reg base types). Discharge = the next step; stated
  -- here so the apex chain is verified end-to-end against ONE named equation.
  -- ════════════════════════════════════════════════════════════════════
  -- DISCHARGE STATUS: true by construction — `exec-abstract (instr-sigop si)`
  -- writes `pure-sigop-output si s = SV-Lit fit (semM si (readTyped A input-loc s))`
  -- (SMCore, Plan 0.54 A4) and `readTyped-adequate` turns the `ValidAtWF`
  -- hypothesis into `readTyped A input-loc s ≡ just (subst id (coh A) x)`, which
  -- with `TM.valueT (evalᴰ (SigOp si) x) 0 = subst (sym (coh B)) (semM si (subst id (coh A) x))`
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

  -- plan 0.97: the SPEC side of the very same dispatch. `stops-D si` is
  -- `stops-D-of (effect si)` for exactly this reason — a `with` would leave it
  -- stuck on an abstract `effect si`. Pure and Emits do not stop the program;
  -- `Halts` is the only shape that does, and it has no discharge here.
  sigop-stops-pure : ∀ {A B} (si : SigOpInfo A B) → effect si ≡ Pure
                   → VD.stops-D si ≡ false
  sigop-stops-pure si pure-eq = cong VD.stops-D-of pure-eq

  sigop-stops-emits : ∀ {A} (si : SigOpInfo A Unitᵀ) → effect si ≡ Emits refl
                    → VD.stops-D si ≡ false
  sigop-stops-emits si emits-eq = cong VD.stops-D-of emits-eq

  -- …and the absurdity form the record's `stops` field wants: a shape that
  -- does not stop cannot have stopped.
  no-stop-pure : ∀ {A B} (si : SigOpInfo A B) → effect si ≡ Pure
               → ∀ {X : Set} → VD.stops-D si ≡ true → X
  no-stop-pure si pure-eq st with trans (sym (sigop-stops-pure si pure-eq)) st
  ... | ()

  no-stop-emits : ∀ {A} (si : SigOpInfo A Unitᵀ) → effect si ≡ Emits refl
                → ∀ {X : Set} → VD.stops-D si ≡ true → X
  no-stop-emits si emits-eq st with trans (sym (sigop-stops-emits si emits-eq)) st
  ... | ()

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
  -- REGISTER-RESIDENT INPUT (`in-reg`) — PROVED. `Input1` holds the value, so
  -- `sv-as-loc` is `nothing` and `pure-sigop-out-aux` takes its register branch,
  -- reading the value back with `readReg-typed` (SMCore).
  --
  -- The IRTy/Type seam on the INPUT type is supplied by the `Readable A`
  -- evidence the caller already carries: `r-int` gives `A ≡ Int` DIRECTLY (no
  -- separate `⌊A⌋ ≡ Int` inversion needed), and the other two readable shapes
  -- are impossible here — `FitsInRegI ⌊Unit⌋` and `FitsInRegI ⌊_ * _⌋` are empty,
  -- so those clauses are absurd. (Float is not `Readable`, so no float-input case
  -- arises.)
  pure-sigop-value-reg :
      ∀ {A B} (n l : ℕ) (si : SigOpInfo A B) (fitness : FitsInReg B) (rA : Readable A)
      → effect si ≡ Pure
      → ∀ (x : ⟦ ⌊ A ⌋ ⟧) (s : LocState FS) (alloc : AllocState {FS})
          (fit : FitsInRegI ⌊ A ⌋)
      → readReg (regs s) Input1 ≡ prim-sv fit x
      → halted s ≡ false
      → readReg (regs (proj₁ (exec-abstract (instr-sigop si) s alloc))) Output
          ≡ prim-sv (fits-erase fitness) (TM.valueT (evalᴰ (SigOp si) x) 0)
  pure-sigop-value-reg n l si fits-intˢ r-int pure-eq x s alloc fits-int rdi-eq nh
    rewrite nh | sigop-halts-false si pure-eq s =
    trans (cong (λ e → exec-sigop-output-of e si s) pure-eq) step2
    where
      step2 : exec-sigop-output-of Pure si s ≡ prim-sv fits-int (TM.valueT (evalᴰ (SigOp si) x) 0)
      step2 rewrite cong sv-as-loc rdi-eq | cong (readReg-typed Intˢ) rdi-eq = refl
  pure-sigop-value-reg n l si fits-floatˢ r-int pure-eq x s alloc fits-int rdi-eq nh
    rewrite nh | sigop-halts-false si pure-eq s =
    trans (cong (λ e → exec-sigop-output-of e si s) pure-eq) step2
    where
      step2 : exec-sigop-output-of Pure si s ≡ prim-sv fits-float (TM.valueT (evalᴰ (SigOp si) x) 0)
      step2 rewrite cong sv-as-loc rdi-eq | cong (readReg-typed Intˢ) rdi-eq = refl
  pure-sigop-value-reg n l si fitness r-unit       pure-eq x s alloc () rdi-eq nh
  pure-sigop-value-reg n l si fitness (r-pair _ _) pure-eq x s alloc () rdi-eq nh

  -- UNIT-DOMAIN input (`in-unit`, D074) — a unit input has no residence, so
  -- the output equation must hold whatever `Input1` contains. It does: the
  -- pointer branch ignores the pointee (`readTyped Unit loc s = just tt`) and
  -- the register branch materialises the unit (`readReg-typed Unit _ =
  -- just tt`), so both dispatch arms of `pure-sigop-out-aux` reduce to
  -- `just tt` and each clause is `refl`.
  pure-sigop-out-unit : ∀ {B} (si : SigOpInfo Unitˢ B) (fitB : FitsInReg B)
                        (s : LocState FS) (ml : Maybe (ValueLocation FS))
                      → pure-sigop-out-aux si s (just fitB) ml
                        ≡ pure-sigop-out-val si fitB (just tt)
  pure-sigop-out-unit si fitB s (just l) = refl
  pure-sigop-out-unit si fitB s nothing  = refl

  pure-sigop-value-correct :
      ∀ {A B} (n l : ℕ) (si : SigOpInfo A B) (fitness : FitsInReg B) (rA : Readable A)
      → effect si ≡ Pure
      → ∀ {mIn} (x : ⟦ ⌊ A ⌋ ⟧)
          (s : LocState FS) (alloc : AllocState {FS})
      → halted s ≡ false
      → InputAt {⌊ A ⌋} mIn alloc x s
      → readReg (regs (proj₁ (exec-abstract (instr-sigop si) s alloc))) Output
          ≡ prim-sv (fits-erase fitness) (TM.valueT (evalᴰ (SigOp si) x) 0)
  pure-sigop-value-correct n l si fits-intˢ rA pure-eq x s alloc nh (in-reg fit rdi-eq) =
    pure-sigop-value-reg n l si fits-intˢ rA pure-eq x s alloc fit rdi-eq nh
  pure-sigop-value-correct n l si fits-floatˢ rA pure-eq x s alloc nh (in-reg fit rdi-eq) =
    pure-sigop-value-reg n l si fits-floatˢ rA pure-eq x s alloc fit rdi-eq nh
  pure-sigop-value-correct {A} n l si fits-intˢ rA pure-eq x s alloc nh (in-loc input-loc valid _ rdi-eq)
    rewrite nh | sigop-halts-false si pure-eq s =
    trans (cong (λ e → exec-sigop-output-of e si s) pure-eq) step2
    where
      step2 : exec-sigop-output-of Pure si s ≡ prim-sv fits-int (TM.valueT (evalᴰ (SigOp si) x) 0)
      step2 rewrite sv-loc-of s input-loc rdi-eq | readTyped-adequate {A = A} rA {v = x} valid = refl
  pure-sigop-value-correct {A} n l si fits-floatˢ rA pure-eq x s alloc nh (in-loc input-loc valid _ rdi-eq)
    rewrite nh | sigop-halts-false si pure-eq s =
    trans (cong (λ e → exec-sigop-output-of e si s) pure-eq) step2
    where
      step2 : exec-sigop-output-of Pure si s ≡ prim-sv fits-float (TM.valueT (evalᴰ (SigOp si) x) 0)
      step2 rewrite sv-loc-of s input-loc rdi-eq | readTyped-adequate {A = A} rA {v = x} valid = refl
  -- D074: the unit-input route. `r-unit` pins `A ≡ Unitˢ`, so `⌊A⌋ ≡ Unit`
  -- holds by `refl` and the other two readable shapes refute the equality.
  pure-sigop-value-correct n l si fits-intˢ r-unit pure-eq x s alloc nh (in-unit refl)
    rewrite nh | sigop-halts-false si pure-eq s =
    trans (cong (λ e → exec-sigop-output-of e si s) pure-eq)
          (pure-sigop-out-unit si fits-intˢ s (sv-as-loc (readReg (regs s) Input1)))
  pure-sigop-value-correct n l si fits-floatˢ r-unit pure-eq x s alloc nh (in-unit refl)
    rewrite nh | sigop-halts-false si pure-eq s =
    trans (cong (λ e → exec-sigop-output-of e si s) pure-eq)
          (pure-sigop-out-unit si fits-floatˢ s (sv-as-loc (readReg (regs s) Input1)))
  pure-sigop-value-correct n l si fitness r-int pure-eq x s alloc nh (in-unit ())
  pure-sigop-value-correct n l si fitness (r-pair _ _) pure-eq x s alloc nh (in-unit ())

  pure-obs-correct-sigop :
    ∀ {A B} (si : SigOpInfo A B) (fitness : FitsInReg B) (rA : Readable A)
    → effect si ≡ Pure → IRObsCorrectF (SigOp si)
  pure-obs-correct-sigop {A} {B} si fitness rA pure-eq
    n l prog base _ cr span _ _ mIn x s alloc cl _ not-halted rdi-eq k =
    record
      { traces-agree =
          trans (cong (take k)
                  (cong (_++ []) (ev-[] 0 (instr-sigop si) refl
                                    (entry-flat base s alloc cl))))
                (cong (take k) (sym (denot-[] k)))
      ; value-realized =
          realized 1 fs₁ Stack (falloc fs₁) ((not-halted , span 0 _ refl) ∷ [])
                   -- A `Pure` SigOp does not halt, so the settle state is LIVE
                   -- (which is what the sequel's `halted s ≡ false` needs).
                   (λ _ → sigop-halts-false si pure-eq s) (λ _ → refl)
                   (no-stop-pure si pure-eq) refl refl
                   (λ _ → at-reg (fits-erase fitness)
                     (pure-sigop-value-correct n l si fitness rA pure-eq x s alloc
                        not-halted rdi-eq))
                   -- D204: `exec-abstract (instr-sigop si)` writes the Output
                   -- register and the halt flag and nothing else — memory is
                   -- untouched whatever the SigOp means.
                   (λ fr j _ → mem-untouched (instr-sigop si) s alloc (AtStack fr j)
                                 nhw-instr-sigop refl)
                   (λ hl _ → mem-untouched (instr-sigop si) s alloc (AtDynamic hl)
                               nhw-instr-sigop refl)
                   refl (λ _ _ bf → bf)
      }
    where
      fs₁ = flat-exec-instr (instr-sigop si) prog (entry-flat base s alloc cl)

      -- Machine side: no fetchable instr emits an event (the sole
      -- instruction `instr-sigop si` is `Pure`), so the whole trace is `[]`.
      ev-[] : ∀ pc i → fetch (emitted n l (SigOp si)) pc ≡ just i
            → ∀ fs → event-of i fs ≡ []
      ev-[] zero    .(instr-sigop si) refl fs rewrite pure-eq = refl
      ev-[] (suc pc') i               ()   fs

      mach-[] : ∀ f → flat-events f (emitted n l (SigOp si)) (entry-flat 0 s alloc cl) ≡ []
      mach-[] f = flat-events-[] (emitted n l (SigOp si)) ev-[] f (entry-flat 0 s alloc cl)


      -- Denotation side: a `Pure` SigOp emits nothing (`emit-D … ≡ []`).
      denot-[] : ∀ k → projTrace (evalᴰ (SigOp si) x) k ≡ []
      denot-[] k rewrite pure-eq = refl

      -- The single `instr-sigop` step leaves the allocator untouched.
      keeps-alloc : falloc fs₁ ≡ alloc
      keeps-alloc rewrite not-halted | pure-eq = refl

  ------------------------------------------------------------------------
  -- THE EFFECTFUL CASE. `Emits` does NOT halt (`exec-sigop-halts-of (Emits _)
  -- … ≡ false`), so the VALUE half is `pure-obs-correct-sigop`'s verbatim and
  -- only the trace half differs — which is the half D058 says is the claim.
  ------------------------------------------------------------------------
  emits-halts-false : ∀ {A B} (si : SigOpInfo A B) {e} → effect si ≡ Emits e
                    → (s : LocState FS) → exec-sigop-halts si s ≡ false
  emits-halts-false si emits-eq s = cong (λ z → exec-sigop-halts-of z si s) emits-eq

  ------------------------------------------------------------------------
  -- THE ARGUMENT CORRESPONDENCE: the event the machine emits records the same
  -- argument the denotation's does. `machine-event` and `mkEvent` are the SAME
  -- `mk-event (name si) A (baseA si) _`, so the whole content is this.
  --
  -- It splits on the DOMAIN's base type, not on the residence:
  --   * `Unit` — `⟦ Unit ⟧` is `⊤`, so the two agree by η whatever `Input1`
  --     holds. This is D074's observation on the argument side.
  --   * `Void` — the argument is `⊥`; there is no such call.
  --   * `Int`/`Float` REGISTER-RESIDENT — `decode-arg`'s two real clauses.
  -- What is left is a BOXED base argument, and that is D114's existing
  -- `decode-unread` hole, restated where it is actually consumed.
  ------------------------------------------------------------------------
  postulate
    decode-boxed : ∀ {A : Type} (bt : IsBaseType A) {mIn alloc}
                     (x : ⟦ ⌊ A ⌋ ⟧) (s : LocState FS)
                 → InputAt {⌊ A ⌋} mIn alloc x s
                 → decode-arg bt (readReg (regs s) Input1)
                   ≡ subst (λ z → z) (EvV.coh A) (DT.forget x)

  emits-arg-agree : ∀ {A : Type} (bt : IsBaseType A) {mIn alloc}
                      (x : ⟦ ⌊ A ⌋ ⟧) (s : LocState FS)
                  → InputAt {⌊ A ⌋} mIn alloc x s
                  → decode-arg bt (readReg (regs s) Input1)
                    ≡ subst (λ z → z) (EvV.coh A) (DT.forget x)
  emits-arg-agree base-Unit  x s inp = refl
  emits-arg-agree base-Int   x s (in-reg fits-int   eq) rewrite eq = refl
  emits-arg-agree base-Float x s (in-reg fits-float eq) rewrite eq = refl
  emits-arg-agree bt         x s inp = decode-boxed bt x s inp

  ------------------------------------------------------------------------
  -- THE EFFECTFUL DISCHARGE. `Emits` carries `B ≡ Unit` (SigOp/Info.agda:88),
  -- which settles the value half outright: the result is `tt` and
  -- `ResultPlace`'s `unit-result` needs no residence. `Emits` also does not
  -- halt, so the settle state is live. Everything real is in the trace.
  ------------------------------------------------------------------------
  -- The trace agreement, as a STANDALONE lemma: `rewrite` has to abstract
  -- `effect si` out of BOTH `ev-of-loc`'s `with` and `emit-D`'s, and inside
  -- the witness's `where` block — with the placement premises in context — it
  -- could not.
  emits-trace-agree :
    ∀ {A} (si : SigOpInfo A Unitᵀ) → effect si ≡ Emits refl
    → ∀ {mIn alloc} (x : ⟦ ⌊ A ⌋ ⟧) (s : LocState FS) (k : ℕ)
    → InputAt {⌊ A ⌋} mIn alloc x s
    → take k (ev-of-loc (instr-sigop si) s ++ [])
      ≡ take k (projTrace (evalᴰ (SigOp si) x) k)
  emits-trace-agree {A} si emits-eq x s k inp rewrite emits-eq = go k
    where
      ev-eq : machine-event si (readReg (regs s) Input1)
            ≡ mkEvent si (subst (λ z → z) (EvV.coh A) (DT.forget x))
      ev-eq = cong (mkEvent si) (emits-arg-agree (SigOpInfo.baseA si) x s inp)

      go : ∀ (j : ℕ)
         → take j (machine-event si (readReg (regs s) Input1) ∷ [])
           ≡ take j (DT.capN j (mkEvent si (subst (λ z → z) (EvV.coh A) (DT.forget x)) ∷ []))
      go zero    = refl
      go (suc j) = cong (_∷ take j []) ev-eq

  ------------------------------------------------------------------------
  -- THE EFFECTFUL DISCHARGE. `Emits` carries `B ≡ Unit` (SigOp/Info.agda:88),
  -- which settles the value half outright: the result is `tt` and
  -- `ResultPlace`'s `unit-result` needs no residence. `Emits` also does not
  -- halt, so the settle state is live. Everything real is in the trace.
  ------------------------------------------------------------------------
  emits-obs-correct-sigop :
    ∀ {A} (si : SigOpInfo A Unitᵀ) → effect si ≡ Emits refl → IRObsCorrectF (SigOp si)
  emits-obs-correct-sigop {A} si emits-eq
    n l prog base _ cr span _ _ mIn x s alloc cl _ not-halted inp k =
    record
      { traces-agree = emits-trace-agree si emits-eq x s k inp
      ; value-realized =
          realized 1 fs₁ Stack (falloc fs₁) ((not-halted , span 0 _ refl) ∷ [])
                   (λ _ → emits-halts-false si emits-eq s) (λ _ → refl)
                   (no-stop-emits si emits-eq) refl refl
                   (λ _ → unit-result)
                   (λ fr j _ → mem-untouched (instr-sigop si) s alloc (AtStack fr j)
                                 nhw-instr-sigop refl)
                   (λ hl _ → mem-untouched (instr-sigop si) s alloc (AtDynamic hl)
                               nhw-instr-sigop refl)
                   refl (λ _ _ bf → bf)
      }
    where
      fs₁ = flat-exec-instr (instr-sigop si) prog (entry-flat base s alloc cl)

  ------------------------------------------------------------------------
  -- THE HALTING DISCHARGE (plan 0.97). `Halts` is `Emits` plus one fact: the
  -- program ends. Machine side, `exec-sigop-halts-of (Halts _) ≡ true`; Spec
  -- side, `stops-D-of (Halts _) ≡ true`. The two now say the same thing, so
  -- the clause is provable — and the three fields that describe a fragment
  -- which reached its end are vacuous.
  --
  -- This row was `obs-correct-sigop-rest` until now, and not for want of
  -- effort: the obligation asserted `halted (floc settle) ≡ false` outright,
  -- which a run ending in `exit` REFUTES. The probe that derived `⊥` from it
  -- is what sent plan 0.97 to the Spec. The trace half is `Emits`'s verbatim
  -- — `ev-of-loc` and `emit-D` treat the two shapes identically — so only the
  -- halting facts are new.
  ------------------------------------------------------------------------
  halts-trace-agree :
    ∀ {A} (si : SigOpInfo A Unitᵀ) → effect si ≡ Halts refl
    → ∀ {mIn alloc} (x : ⟦ ⌊ A ⌋ ⟧) (s : LocState FS) (k : ℕ)
    → InputAt {⌊ A ⌋} mIn alloc x s
    → take k (ev-of-loc (instr-sigop si) s ++ [])
      ≡ take k (projTrace (evalᴰ (SigOp si) x) k)
  halts-trace-agree {A} si halts-eq x s k inp rewrite halts-eq = go k
    where
      ev-eq : machine-event si (readReg (regs s) Input1)
            ≡ mkEvent si (subst (λ z → z) (EvV.coh A) (DT.forget x))
      ev-eq = cong (mkEvent si) (emits-arg-agree (SigOpInfo.baseA si) x s inp)

      go : ∀ (j : ℕ)
         → take j (machine-event si (readReg (regs s) Input1) ∷ [])
           ≡ take j (DT.capN j (mkEvent si (subst (λ z → z) (EvV.coh A) (DT.forget x)) ∷ []))
      go zero    = refl
      go (suc j) = cong (_∷ take j []) ev-eq

  halts-halts-true : ∀ {A B} (si : SigOpInfo A B) {e} → effect si ≡ Halts e
                   → (s : LocState FS) → exec-sigop-halts si s ≡ true
  halts-halts-true si halts-eq s = cong (λ z → exec-sigop-halts-of z si s) halts-eq

  sigop-stops-halts : ∀ {A B} (si : SigOpInfo A B) {e} → effect si ≡ Halts e
                    → VD.stops-D si ≡ true
  sigop-stops-halts si halts-eq = cong VD.stops-D-of halts-eq

  -- …and the refutation the three conditioned fields want: a shape that
  -- STOPS cannot be live.
  no-live-halts : ∀ {A B} (si : SigOpInfo A B) {e} → effect si ≡ Halts e
                → ∀ {X : Set} → VD.stops-D si ≡ false → X
  no-live-halts si halts-eq p with trans (sym (sigop-stops-halts si halts-eq)) p
  ... | ()

  halts-obs-correct-sigop :
    ∀ {A} (si : SigOpInfo A Unitᵀ) → effect si ≡ Halts refl → IRObsCorrectF (SigOp si)
  halts-obs-correct-sigop {A} si halts-eq
    n l prog base _ cr span _ _ mIn x s alloc cl _ not-halted inp k =
    record
      { traces-agree = halts-trace-agree si halts-eq x s k inp
      ; value-realized =
          realized 1 fs₁ Stack (falloc fs₁) ((not-halted , span 0 _ refl) ∷ [])
                   (no-live-halts si halts-eq) (no-live-halts si halts-eq)
                   (λ _ → halts-halts-true si halts-eq s) refl refl
                   (no-live-halts si halts-eq)
                   (λ fr j _ → mem-untouched (instr-sigop si) s alloc (AtStack fr j)
                                 nhw-instr-sigop refl)
                   (λ hl _ → mem-untouched (instr-sigop si) s alloc (AtDynamic hl)
                               nhw-instr-sigop refl)
                   refl (λ _ _ bf → bf)
      }
    where
      fs₁ = flat-exec-instr (instr-sigop si) prog (entry-flat base s alloc cl)

  -- The SigOp cases the Pure discharge does NOT cover, named separately (Plan
  -- 0.68 step 0). They used to fall back into the whole-IR `obs-correct-rest`,
  -- which meant an EFFECTFUL SigOp — the only kind that puts anything in the
  -- observable trace at all — was assumed by the same postulate as `Para`'s
  -- missing codegen. Split out so the effectful case has its own row.
  postulate
    obs-correct-sigop-rest : ∀ {A B} (si : SigOpInfo A B) → IRObsCorrectF (SigOp si)

    -- ── D174, THE ONE RESIDUAL OF `obs-correct-inl` (deferred proof /
    -- machine invariant). Class: **invariant**, and BELIEVED TRUE for a
    -- reason the model already encodes.
    --
    -- `inl`'s ten instructions write exactly four cells: stack slots `n` and
    -- `n+1`, and the two cells of the block `instr-alloc-heap 2` just
    -- returned. The clause is handed `next-slot alloc ≤ n`, so NO
    -- `stack-before` location (`k < next-slot alloc`) can name either slot;
    -- and the fresh block's `ref-id` IS `next-heap-ref alloc`, so no
    -- `heap-before` location (`ref-id < next-heap-ref alloc`) can name either
    -- heap cell. `stack-ancestor` locations live in a caller's frame, which
    -- this clause never touches.
    --
    -- So every location the CALLER can name reads the same before and after —
    -- which is precisely what `BeforeFrontier` exists to say.
    --
    -- D182 — WRITTEN, AND IT RETIRED THREE POSTULATES AT ONCE. The note here
    -- used to end "that generalisation is the work, and it serves `pair`,
    -- `curry` and `case` identically", with `inl-mem-pres`, `inr-mem-pres` and
    -- `curry-mem-pres` standing as three statements of the SAME invariant about
    -- the SAME ten-instruction shape. `TenStepPres.mem-pres` (above) proves it
    -- once and each clause instantiates it at its own two middle rows — which
    -- touch no memory, so they are the only thing that had to be abstracted.
    --
    -- It could not reuse `derive-mem-preserved` (ClosureWellFormed): that one
    -- bans heap writes outright, and this run writes the heap twice. What makes
    -- those writes invisible is not their ABSENCE but their FRESHNESS.
    --
    -- WHAT IT REPLACED. Before this, `obs-correct-inl` was an axiom for the
    -- WHOLE clause — the run, its events, its halting, its frontier, its tag
    -- and payload cells, and all three input residences. Now the clause, and
    -- its `inr` and `curry` siblings, are postulate-free.

  ------------------------------------------------------------------------
  -- CLASS B, in progress: `inl` / `inr`. Skeleton only — the holes are the
  -- obligations, read off the goal rather than guessed at.
  ------------------------------------------------------------------------

  obs-correct-sigop : ∀ {A B} (si : SigOpInfo A B) → IRObsCorrectF (SigOp si)
  -- Route on BOTH the codomain (register-resident result) and the domain
  -- (readable input ⇒ the machine can materialise it and apply `semM`). A Pure
  -- SigOp over a non-readable input keeps the sentinel, so it makes no value
  -- claim and falls back to `obs-correct-sigop-rest`. Arith is always readable.
  -- Dispatch on the EFFECT first. The old order tested `fits-in-reg? B`
  -- first, which made the `Emits` row unreachable: `Emits` carries `B ≡ Unit`
  -- and `FitsInReg Unit` is empty, so every effectful SigOp fell through the
  -- FIRST row into `obs-correct-sigop-rest` — the row that reads as "a Pure
  -- SigOp whose result does not fit a register". The effectful case, which is
  -- the only kind that puts anything in the observable trace, was being
  -- assumed by a clause that looked like it was about something else.
  obs-correct-sigop {A} {B} si with effect si in eff-eq
  ... | Emits refl = emits-obs-correct-sigop si eff-eq
  ... | Halts refl = halts-obs-correct-sigop si eff-eq
  ... | Pure with fits-in-reg? B | readable? A
  ...   | nothing      | _       = obs-correct-sigop-rest si
  ...   | just fitness | nothing = obs-correct-sigop-rest si
  ...   | just fitness | just rA = pure-obs-correct-sigop si fitness rA eff-eq

  -- ════════════════════════════════════════════════════════════════════
  -- `comp-obs-correct` — the COMPOSITION case, CARVED from `obs-correct-rest`
  -- top-down (Plan 0.54 rung A). `emitted n l (g ∘ f) = ft ++ mov-to-input ∷ gt`:
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

