-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.RewritePreserves — THE ARITH LIFTING PRESERVES A PROGRAM'S
-- MEANING (D165, restated at the meaning in plan 0.103 6a″; over `T∞` runs in
-- plan 0.119 D5).
--
-- `rewrite-ir` replaces a recognised closed arithmetic subtree by one
-- `arith.block.<digest>` SigOp and otherwise walks the IR. The IR means `T∞`
-- runs, which are compared step for step (`RelS`), never by `≡` — so the
-- statement is a logical relation (`ValueRel.RelD`): the rewritten term at a
-- call environment and the original at a related one take related inputs to
-- related runs. A lifted block returns at once what the subtree returns at once
-- (`lift-now`); every other former is a congruence; the program's table,
-- rewritten entry by entry, is a related call environment; so the programs'
-- runs are related, and have the same trace (`TraceTr.RelS-tr`).
------------------------------------------------------------------------

module Once.Adequacy.RewritePreserves where

open import Data.Empty using (⊥-elim)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Relation.Nullary using (yes; no)

import Once.Adequacy.LiftSound as LS
open import Once.Spec.Numerics using (TargetNum)
open import Once.IR
open import Once.IRTy using (IRTy; ⌊_⌋; ⌈_⌉; ⌈_⌉F; ⌈⟧TI-commute; ⟦_⟧TI; _≟IRTy_; IsBaseTypeI; WellFormedFI)
import Once.IRTy as II
open import Once.IRTy.WF using (wf-⌈⌉; base-⌊⌋)
open import Once.CanonicalName using (_≟ᶜ_)
open import Once.Arith.Machine.IR using (ArithBlock)
open import Once.Arith.Machine.Rewrite using (rewrite-ir; rw-at; walk; try-lift; bare-at)
open import Once.Lang.Trace using (T; ret; call; halt; Interp; pureHalf; FFIAnswers; fmapT; RelT′; rel-ret; rel-call; rel-halt)
open import Once.Lang.Iterative using (T∞; return∞; _>>=∞_; embed; fmap∞)
open T∞ using (force)
open import Once.SigOp.Info using (SigOpInfo; module SigOpInfo)
open SigOpInfo using (baseA; conB)
open import Once.Denotation.DenotTrace using (evalᴰ; CallEnv; callEnv; cata-ev-algᴰ; sigOpT; module CallEnv)
open CallEnv using (callsE; ffiE)
open import Once.Denotation.ValueDomain using (⟦_⟧ᴰ; ⟦_⟧ᴰᴵ; cohᴰ; forgetᵇ; injectᵇ; coerce-functor-D; coerce-functor⁻¹-D)
open import Once.Denotation.Program using (IRFun; tableEnv; tableCalls; tableEnv-at; runIR; IRProgram)
open Once.Denotation.Program.IRProgram using (main; table)
open Once.Denotation.Program.IRFun using (fbody; fcod; fdom; fname)
open import Once.Denotation.TraceMonadInfLaws using (RelS; RelSB; module RelS; s-ret; s-next; s-call; s-halt; RelS-bind; relS-ret; RelS-embed; RelS-iter∞)
open RelS using (forceS)
open import Once.Denotation.ValueRel
open import Once.Denotation.EvalRel using (base-eqI; base-reflI; fo-eq; RelS-now; RelEnv; sigop-rel)
open import Once.Lang.StreamInf using (anaFᴵ; in-νᴵ; module νᴵ)
open νᴵ using (forceᴵ)
open import Once.Lang.Type using (μ-type; ν-type)
open import Once.Lang.FunctorMeaning using (translateF)
import Once.Lang.Type.WellFormed as LW
open import Once.Spec.Word using (Carrier)
open import Once.Lang.Value Carrier Carrier using () renaming (⟦_⟧F to ⟦_⟧F′)
open import Once.Semantics.Machine using (sem-cata; sem-In; sem-Out; coerce-ν-out; coerce-ν-in)
open import Once.Compile using (rewrite-program; rewrite-table; rewrite-fun)
open import Once.Spec.Trace using (_≈ᵗ⟨_⟩_)
open import Once.Denotation.TraceTr using (trT∞; RelS-tr)

------------------------------------------------------------------------
-- The relation on call environments, and the rewrite's soundness.
------------------------------------------------------------------------

module _ (fmt : TargetNum) where

  module _ {ρ ρ′ : CallEnv} (re : RelEnv fmt ρ ρ′) where
    private
      E  : ∀ {A B} → IR A B → ⟦ A ⟧ᴰᴵ → T∞ ⟦ B ⟧ᴰᴵ
      E  = evalᴰ fmt ρ
      E′ : ∀ {A B} → IR A B → ⟦ A ⟧ᴰᴵ → T∞ ⟦ B ⟧ᴰᴵ
      E′ = evalᴰ fmt ρ′

    rewrite-rel : ∀ {A B} (ir : IR A B) {a a′} → RelD ⌈ A ⌉ a a′ → RelS (RelD ⌈ B ⌉) (E (proj₁ (rewrite-ir ir)) a) (E′ ir a′)
    rw-at-rel   : ∀ {A B} (ir : IR A B) (d : Maybe (IR A B × ArithBlock)) → try-lift ir ≡ d
                → ∀ {a a′} → RelD ⌈ A ⌉ a a′ → RelS (RelD ⌈ B ⌉) (E (proj₁ (rw-at ir d)) a) (E′ ir a′)
    walk-rel    : ∀ {A B} (ir : IR A B) {a a′} → RelD ⌈ A ⌉ a a′ → RelS (RelD ⌈ B ⌉) (E (proj₁ (walk ir)) a) (E′ ir a′)

    -- A lifted subtree: the block and the subtree return the same value at
    -- once; the subtree's input and output are base types.
    lifted : ∀ {A B} (ir ir′ : IR A B) (blk : ArithBlock) → try-lift ir ≡ just (ir′ , blk)
           → ∀ {a a′} → RelD ⌈ A ⌉ a a′ → RelS (RelD ⌈ B ⌉) (E ir′ a) (E′ ir a′)
    lifted ir ir′ blk eq {a} r with LS.lift-now fmt ρ′ ir ir′ blk eq
    ... | bA , bB , now with base-eqI bA r
    ...   | refl with now ρ a
    ...     | v , e₁ , e₂ = RelS-now e₁ e₂ (base-reflI bB v)

    rewrite-rel ir = rw-at-rel ir (try-lift ir) refl

    rw-at-rel ir (just (ir′ , blk)) eq r = lifted ir ir′ blk eq r
    rw-at-rel ir nothing            eq r = walk-rel ir r

    walk-rel id         r = relS-ret r
    walk-rel (g ∘ f)    r = RelS-bind (rewrite-rel f r) (λ r′ → rewrite-rel g r′)
    walk-rel fst        r = relS-ret (proj₁ r)
    walk-rel snd        r = relS-ret (proj₂ r)
    walk-rel ⟨ f , g ⟩  r = RelS-bind (rewrite-rel f r) (λ rb → RelS-bind (rewrite-rel g r) (λ rc → relS-ret (rb , rc)))
    walk-rel inl        r = relS-ret r
    walk-rel inr        r = relS-ret r
    walk-rel (case f g) {inj₁ a} {inj₁ a′} r = rewrite-rel f r
    walk-rel (case f g) {inj₂ b} {inj₂ b′} r = rewrite-rel g r
    walk-rel (case f g) {inj₁ _} {inj₂ _} ()
    walk-rel (case f g) {inj₂ _} {inj₁ _} ()
    walk-rel terminal   r = relS-ret tt
    walk-rel initial {()}
    walk-rel (curry f)  r = relS-ret (λ r′ → rewrite-rel f (r , r′))
    walk-rel apply      r = proj₁ r (proj₂ r)
    walk-rel (In {F} w) r rewrite fo-eq w r = relS-ret refl
    walk-rel (out-μ {F} w) {x} r rewrite r =
      relS-ret (RelD-subst (sym (⌈⟧TI-commute F (II.μ-type F)))
                 (cfD⁻¹-rel (wf-⌈⌉ w) ⌈ II.μ-type F ⌉ (frefl (wf-⌈⌉ w) _)))
      where
        frefl : ∀ {G} (wg : LW.WellFormedF G) (l : ⟦ G ⟧F′ ⟦ ⌈ II.μ-type F ⌉ ⟧ᴰ)
              → FRel (RelD ⌈ II.μ-type F ⌉) G l l
        frefl (LW.wf-K b) l = fr-K
        frefl LW.wf-Id l = fr-Id refl
        frefl (LW.wf-Sum wf wg) (inj₁ l) = fr-inl (frefl wf l)
        frefl (LW.wf-Sum wf wg) (inj₂ l) = fr-inr (frefl wg l)
        frefl (LW.wf-Prod wf wg) (l , l′) = fr-pair (frefl wf l) (frefl wg l′)
    walk-rel (Cata {F} w {E₀} {C} alg) {e , x} {e′ , x′} (re′ , refl) =
      sem-cata-rel (wf-⌈⌉ w) (λ fr → alg-step fr) x
      where
        alg-step : ∀ {l₁ l₂} → FRel (RelS (RelD ⌈ C ⌉)) ⌈ F ⌉F l₁ l₂
                 → RelS (RelD ⌈ C ⌉) (cata-ev-algᴰ fmt ρ w (proj₁ (rewrite-ir alg)) e l₁) (cata-ev-algᴰ fmt ρ′ w alg e′ l₂)
        alg-step fr =
          RelS-bind (seqF∞-rel ⌈ F ⌉F fr)
            (λ fl → rewrite-rel alg (re′ , RelD-subst (sym (⌈⟧TI-commute F C)) (cfD⁻¹-rel (wf-⌈⌉ w) ⌈ C ⌉ fl)))
    walk-rel (Out {F} w) {v} {v′} r =
      RelS-fmap (StreamRel.forceR r)
        (λ l → RelD-subst (sym (⌈⟧TI-commute F (II.ν-type F)))
                 (cfD⁻¹-rel (wf-⌈⌉ w) ⌈ II.ν-type F ⌉ (cμout-rel (wf-⌈⌉ w) (layer→srel (translateF Carrier Carrier ⌈ F ⌉F) l))))
    walk-rel (in-ν {F} w) r =
      relS-ret (in-rel (cμin-rel ⌈ F ⌉F (cfD-rel (wf-⌈⌉ w) ⌈ II.ν-type F ⌉ (RelD-subst (⌈⟧TI-commute F (II.ν-type F)) r))))
    walk-rel (Ana {F} w {E₀} {A₀} c) {e , s} {e′ , s′} (re′ , rs) =
      relS-ret (anaᴵ-rel (λ r → RelS-fmap (RelS-fmap (rewrite-rel c (re′ , r))
                                            (λ q → cfD-rel (wf-⌈⌉ w) ⌈ A₀ ⌉ (RelD-subst (⌈⟧TI-commute F A₀) q)))
                                          (cμin-rel ⌈ F ⌉F))
                         rs)
    walk-rel (Iter {E₀} {A₀} {B₀} b) {e , s} {e′ , s′} (re′ , rs) =
      RelS-iter∞ {RB = RelD ⌈ B₀ ⌉} {S = RelD ⌈ B₀ II.+ A₀ ⌉}
                 {f = λ a → E (proj₁ (rewrite-ir b)) (e , a)} {f′ = λ a → E′ b (e′ , a)}
                 (λ r → r) (λ r → rewrite-rel b (re′ , r)) (λ ()) (λ ()) rs
    walk-rel (const II.fits-int v)   r = relS-ret refl
    walk-rel (const II.fits-float v) r = relS-ret refl
    walk-rel (SigOp si) r = bare-rel (try-lift (SigOp si ∘ id)) refl
      where
        bare-rel : ∀ d → try-lift (SigOp si ∘ id) ≡ d → RelS _ (E (proj₁ (bare-at si d)) _) (E′ (SigOp si) _)
        -- `SigOp si ∘ id` returns at once exactly when `SigOp si` does (its
        -- first block is the same block).
        bare-rel (just (ir′ , blk)) eq with LS.lift-now fmt ρ′ (SigOp si ∘ id) ir′ blk eq
        ... | bA , bB , now with base-eqI bA r
        ...   | refl with now ρ _
        ...     | v , e₁ , e₂ = RelS-now e₁ e₂ (base-reflI bB v)
        bare-rel nothing            eq = sigop-rel fmt re si r
    walk-rel (Call {A} {B} f) r = proj₁ re f A B r

------------------------------------------------------------------------
-- The table, rewritten entry by entry, is a related call environment; so the
-- program's runs are related, and have the same trace.
------------------------------------------------------------------------

module _ (fmt : TargetNum) (φ : FFIAnswers) where

  table-rel : ∀ (tbl : List IRFun) → RelEnv fmt (tableEnv fmt φ (rewrite-table tbl)) (tableEnv fmt φ tbl)
  calls-rel : ∀ (tbl : List IRFun) f (A B : IRTy) {a a′} → RelD ⌈ A ⌉ a a′
            → RelS (RelD ⌈ B ⌉) (tableCalls fmt φ (rewrite-table tbl) f A B a) (tableCalls fmt φ tbl f A B a′)
  table-rel tbl = calls-rel tbl , refl

  calls-rel []       f A B r = RelS-embed rel-halt
  calls-rel (e ∷ es) f A B r = at (fname e ≟ᶜ f) (fdom e ≟IRTy A) (fcod e ≟IRTy B) r
    where
      hit : ∀ {A B} (p : fdom e ≡ A) (q : fcod e ≡ B) {a a′} → RelD ⌈ A ⌉ a a′
          → RelS (RelD ⌈ B ⌉)
              (subst (λ Y → T∞ ⟦ Y ⟧ᴰᴵ) q (evalᴰ fmt (tableEnv fmt φ (rewrite-table es)) (proj₁ (rewrite-ir (fbody e))) (subst ⟦_⟧ᴰᴵ (sym p) a)))
              (subst (λ Y → T∞ ⟦ Y ⟧ᴰᴵ) q (evalᴰ fmt (tableEnv fmt φ es) (fbody e) (subst ⟦_⟧ᴰᴵ (sym p) a′)))
      hit refl refl r = rewrite-rel fmt (table-rel es) (fbody e) r
      at : ∀ d₁ d₂ d₃ {a a′} → RelD ⌈ A ⌉ a a′
         → RelS (RelD ⌈ B ⌉) (tableEnv-at fmt φ (rewrite-fun e) (rewrite-table es) f A B d₁ d₂ d₃ a)
                              (tableEnv-at fmt φ e es f A B d₁ d₂ d₃ a′)
      at (yes _) (yes p) (yes q) r = hit p q r
      at (yes _) (yes _) (no _)  r = calls-rel es f A B r
      at (yes _) (no _)  _       r = calls-rel es f A B r
      at (no _)  _       _       r = calls-rel es f A B r

  program-rel : ∀ (p : IRProgram) → RelS (RelD ⌈ II.Unit ⌉) (runIR fmt φ (rewrite-program p)) (runIR fmt φ p)
  program-rel p = rewrite-rel fmt (table-rel (table p)) (main p) tt

-- D320 / plan 0.119 D5: the rewritten program has the same TRACE.
rewrite-program-trace : ∀ (fmt : TargetNum) (ι : Interp) (p : IRProgram)
                      → trT∞ ι [] (runIR fmt (pureHalf ι) (rewrite-program p)) ≈ᵗ⟨ _≡_ ⟩ trT∞ ι [] (runIR fmt (pureHalf ι) p)
rewrite-program-trace fmt ι p = RelS-tr ι [] (program-rel fmt (pureHalf ι) p)
