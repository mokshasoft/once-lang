-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.LinCore.LinkedCore — plan 0.146 B1.5 (D448): MASTER'S LINKEDNESS AT
-- THE CORE. A linked IR program (`Denotation.Program.LinkedProgram`: every
-- SigOp leaf `Declared` by the interpretation) translates (`FromIR`, then
-- `Pass.tr`) to a core program whose universe's ops (`Keys.ops`) are all
-- declared: the translations are structural, and each keeps an IR's ops
-- among the ops it had (FromIR adds only the halting `unlinked` op, which
-- owes nothing).
------------------------------------------------------------------------

{-# OPTIONS --guardedness #-}

open import Data.Nat using (ℕ)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁻)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; subst₂; sym)
open import Once.IRTy using (μ-type; ν-type)
open import Once.SigOp.Info using (SigOpInfo; module SigOpInfo)
open import Once.Spec.Numerics using (TargetNum)
open import Once.IR.Semantics.Trace using (FFIAnswers)
open import Once.LinCore.Flat using (Base)
import Once.LinCore.PassTr

module Once.LinCore.LinkedCore (fmt : TargetNum) (ans : FFIAnswers) (bw : Base → ℕ) where

open import Once.LinCore.Core fmt
open import Once.LinCore.Flat using (Base)
open Sig using (info)
open import Once.LinCore.NbEPLinCore fmt ans
module P = Once.LinCore.PassTr fmt
open import Once.LinCore.Keys fmt bw using (Got; ps; tmGot; defsGot; univ; module Univ)
open Univ using (ops)

------------------------------------------------------------------------
-- 1. THE PASS IR'S OPS, and the core's are among them
------------------------------------------------------------------------

module _ (D : Sig → Set) where
  OpsOK : ∀ {Γ A B} → P.IR Γ A B → Set
  OpsOK (g P.∘ f)        = OpsOK g × OpsOK f
  OpsOK P.⟨ f , g ⟩      = OpsOK f × OpsOK g
  OpsOK (P.case f g)     = OpsOK f × OpsOK g
  OpsOK (P.curry g f γ)  = OpsOK f
  OpsOK (P.Cata F alg)   = OpsOK alg
  OpsOK (P.Ana F c φ)    = OpsOK c
  OpsOK (P.Iter body φ)  = OpsOK body
  OpsOK (P.SigOp s)      = D s
  {-# CATCHALL #-}
  OpsOK _                = ⊤

  data ProgOK : ∀ {Γ} → P.Prog Γ → Set where
    ε   : ProgOK P.ε
    _▹_ : ∀ {Γ g A B} {Q : P.Prog Γ} {f : P.IR Γ A B} {γ : P.GdIR Γ g f} → ProgOK Q → OpsOK f → ProgOK (Q P.▹ f ∣ γ)

  private
    either : ∀ {s : Sig} xs {ys} → s ∈ xs ++ ys → (s ∈ xs → D s) → (s ∈ ys → D s) → D s
    either xs m l r = case′ (∈-++⁻ xs m)
      where
        case′ : _ → _
        case′ (inj₁ a) = l a
        case′ (inj₂ b) = r b

  -- a layer's map names the ops its function does
  mapL-ps : ∀ {Γ} (ds : Defs Γ) G {E A B} (f : Tm Γ E A B) → (∀ {s} → s ∈ ps (tmGot ds f) → D s)
          → ∀ {s} → s ∈ ps (tmGot ds (P.mapL G f)) → D s
  mapL-ps ds Idf      f k m = k m
  mapL-ps ds Kone     f k ()
  mapL-ps ds Kzero    f k ()
  mapL-ps ds (Kb b)   f k ()
  mapL-ps ds (Kμ G)   f k ()
  mapL-ps ds (G ⊕f H) f k m = either (ps (tmGot ds (P.mapL G f))) m (mapL-ps ds G f k) (mapL-ps ds H f k)
  mapL-ps ds (G ⊗f H) f k m = either (ps (tmGot ds (P.mapL G f))) m (mapL-ps ds G f k) (mapL-ps ds H f k)

  -- Lambek's inverse names none
  inco-ps : ∀ {Γ} (ds : Defs Γ) F → ∀ {s} → s ∈ ps (tmGot ds (P.inco {Γ} F)) → D s
  inco-ps ds F m =
    either (ps (tmGot ds (P.mapL F linr))) m (mapL-ps ds F linr (λ ()))
      (λ m₁ → either (ps (tmGot ds (P.mapL F linr))) m₁ (mapL-ps ds F linr (λ ())) (λ ()))

  -- ★ the core term's ops are its IR's
  tr-ps : ∀ {Γ} (ds : Defs Γ) {A B} (g : P.IR Γ A B) → OpsOK g → ∀ {s} → s ∈ ps (tmGot ds (P.tr g)) → D s
  tr-ps ds P.id o ()
  tr-ps ds (g P.∘ f) (og , of) m = either (ps (tmGot ds (P.tr g))) m (tr-ps ds g og) (tr-ps ds f of)
  tr-ps ds P.⟨ f , g ⟩ (of , og) m =
    either (ps (tmGot ds (P.tr f)) ++ ps (tmGot ds (P.tr g))) m
      (λ m′ → either (ps (tmGot ds (P.tr f))) m′ (tr-ps ds f of) (tr-ps ds g og)) (λ ())
  tr-ps ds P.fst o ()
  tr-ps ds P.snd o ()
  tr-ps ds P.inl o ()
  tr-ps ds P.inr o ()
  tr-ps ds (P.case f g) (of , og) m = either (ps (tmGot ds (P.tr f))) m (tr-ps ds f of) (tr-ps ds g og)
  tr-ps ds P.terminal o ()
  tr-ps ds P.initial o ()
  tr-ps ds (P.curry g f γ) o m = either (ps (tmGot ds (P.tr f))) m (tr-ps ds f o) (λ ())
  tr-ps ds P.apply o ()
  tr-ps ds (P.In F) o ()
  tr-ps ds (P.out-μ F) o ()
  tr-ps ds (P.Cata F alg) o m = either (ps (tmGot ds (P.tr alg))) m (tr-ps ds alg o) (λ ())
  tr-ps ds (P.Ana F c φ) o m = either (ps (tmGot ds (P.tr c)) ++ []) m (λ m′ → either (ps (tmGot ds (P.tr c))) m′ (tr-ps ds c o) (λ ())) (λ ())
  tr-ps ds (P.Out F) o ()
  tr-ps ds (P.in-ν F) o m =
    either (ps (tmGot ds (P.inco F)) ++ []) m (λ m₁ → either (ps (tmGot ds (P.inco F))) m₁ (inco-ps ds F) (λ ())) (λ ())
  tr-ps ds (P.Iter body φ) o m = either (ps (tmGot ds (P.tr body))) m (tr-ps ds body o) (λ ())
  tr-ps ds (P.const v) o ()
  tr-ps ds (P.SigOp s) o (here refl) = o
  tr-ps ds (P.Call p) o ()

  -- the table's
  defs-ps : ∀ {Γ} (Q : P.Prog Γ) → ProgOK Q → ∀ {s} → s ∈ ps (defsGot (P.trP Q)) → D s
  defs-ps P.ε ε ()
  defs-ps (Q P.▹ f ∣ γ) (oq ▹ of) m =
    either (ps (defsGot (P.trP Q))) m (defs-ps Q oq)
      (λ m′ → either (ps (tmGot (P.trP Q) (P.tr f))) m′ (tr-ps (P.trP Q) f of) (λ ()))

  -- ★ a program's universe's ops
  univ-ps : ∀ {Γ} (Q : P.Prog Γ) (f : P.IR Γ One One) → ProgOK Q → OpsOK f
          → ∀ {s} → s ∈ ops (univ (P.trP Q) (P.tr f)) → D s
  univ-ps Q f oq of m = either (ps (defsGot (P.trP Q))) m (defs-ps Q oq) (tr-ps (P.trP Q) f of)

------------------------------------------------------------------------
-- 2. ★ FROM MASTER'S IR: a linked term's ops are declared, and so are a
-- linked table's
------------------------------------------------------------------------

open import Data.Maybe using (Maybe; just; nothing; _>>=_)
open import Once.Contract using (ISig)
open import Once.Denotation.Program using (Declared; Leaves; TeleLinked; IRFun; module IRFun)
import Once.IR as M
import Once.LinCore.FromIR
module FromIR = Once.LinCore.FromIR fmt

module FromLinked (Σι : ISig) where
  Dc : Sig → Set
  Dc s = Declared Σι (info s)

  private
    ok-subst : ∀ {Γ} {I : Set} (F G : I → LTy) {i j} (e : i ≡ j) {g : P.IR Γ (F i) (G i)}
             → OpsOK Dc g → OpsOK Dc (subst (λ k → P.IR Γ (F k) (G k)) e g)
    ok-subst F G refl o = o

    ok-subst₂ : ∀ {Γ} {A A′ B B′} (p : A ≡ A′) (q : B ≡ B′) {g : P.IR Γ A B}
              → OpsOK Dc g → OpsOK Dc (subst₂ (P.IR Γ) p q g)
    ok-subst₂ refl refl o = o

  -- ★ a translated term's ops are its IR's (the unlinked op owes nothing)
  tr-ok : ∀ {Γ} {rs : FromIR.Resolver Γ} {A B} {ir : M.IR A B} {c} → FromIR.Tr rs ir c
        → ∀ {I : Set} {C} {i : I} → Leaves C i (Declared Σι) ir → OpsOK Dc c
  tr-ok FromIR.t-id l = tt
  tr-ok (FromIR.t-∘ tg tf) (lg , lf) = tr-ok tg lg , tr-ok tf lf
  tr-ok (FromIR.t-pair tf tg) (lf , lg) = tr-ok tf lf , tr-ok tg lg
  tr-ok FromIR.t-fst l = tt
  tr-ok FromIR.t-snd l = tt
  tr-ok FromIR.t-inl l = tt
  tr-ok FromIR.t-inr l = tt
  tr-ok (FromIR.t-case tf tg) (lf , lg) = tr-ok tf lf , tr-ok tg lg
  tr-ok FromIR.t-term l = tt
  tr-ok FromIR.t-init l = tt
  tr-ok (FromIR.t-curry tf) l = tr-ok tf l
  tr-ok FromIR.t-apply l = tt
  tr-ok {Γ} (FromIR.t-In {F} wf) l = ok-subst {Γ} (λ X → X) (λ _ → FromIR.⟪_⟫ (μ-type F)) (sym (FromIR.⟪⟫-TI wf (μ-type F))) {g = P.In (FromIR.lf F)} tt
  tr-ok {Γ} (FromIR.t-out {F} wf) l = ok-subst {Γ} (λ _ → FromIR.⟪_⟫ (μ-type F)) (λ X → X) (sym (FromIR.⟪⟫-TI wf (μ-type F))) {g = P.out-μ (FromIR.lf F)} tt
  tr-ok {Γ} (FromIR.t-cata {F} wf {E} {A} {a′ = a′} ta) l = ok-subst {Γ} (λ X → FromIR.⟪_⟫ E ⊗t X) (λ _ → FromIR.⟪_⟫ A) (FromIR.⟪⟫-TI wf A) {g = a′} (tr-ok ta l)
  tr-ok {Γ} (FromIR.t-Out {F} wf) l = ok-subst {Γ} (λ _ → FromIR.⟪_⟫ (ν-type F)) (λ X → X) (sym (FromIR.⟪⟫-TI wf (ν-type F))) {g = P.Out (FromIR.lf F)} tt
  tr-ok {Γ} (FromIR.t-inν {F} wf) l = ok-subst {Γ} (λ X → X) (λ _ → FromIR.⟪_⟫ (ν-type F)) (sym (FromIR.⟪⟫-TI wf (ν-type F))) {g = P.in-ν (FromIR.lf F)} tt
  tr-ok {Γ} (FromIR.t-ana {F} wf {E} {A} {c′ = c′} tc φ) l = ok-subst {Γ} (λ _ → FromIR.⟪_⟫ E ⊗t FromIR.⟪_⟫ A) (λ X → X) (FromIR.⟪⟫-TI wf A) {g = c′} (tr-ok tc l)
  tr-ok (FromIR.t-iter tb φ) l = tr-ok tb l
  tr-ok FromIR.t-int l = tt
  tr-ok FromIR.t-float l = tt
  tr-ok {Γ} (FromIR.t-op si) l = ok-subst₂ {Γ} (sym (FromIR.⟪⌊⌋⟫-flat (SigOpInfo.baseA si))) (sym (FromIR.⟪⌊⌋⟫-flat (SigOpInfo.conB si))) {g = P.SigOp (sig si)} l
  tr-ok (FromIR.t-hit e) l = tt
  tr-ok (FromIR.t-miss e) l = tt , tt , tt

  private
    bind-just : ∀ {X Y : Set} {m : Maybe X} {k : X → Maybe Y} {y} → (m >>= k) ≡ just y
              → Σ X (λ x → m ≡ just x × k x ≡ just y)
    bind-just {m = just x} e = x , refl , e

    entry-ok : ∀ {Γ} (Q : P.Prog Γ) rs (e : IRFun) b (mφ : Maybe (P.BlkIR Γ b)) → ProgOK Dc Q → OpsOK Dc b
             → ProgOK Dc (FromIR.TrProg.prog (FromIR.entry-at Q rs e b mφ))
    entry-ok Q rs e b (just φ) oq ob = oq ▹ ob
    entry-ok Q rs e b nothing  oq ob = oq ▹ ob

    just-inj : ∀ {X : Set} {x y : X} → just x ≡ just y → x ≡ y
    just-inj refl = refl

  -- ★ a linked table's ops are declared
  table-ok : ∀ es {tp} → FromIR.trTable es ≡ just tp → TeleLinked Σι es → ProgOK Dc (FromIR.TrProg.prog tp)
  table-ok [] refl _ = ε
  table-ok (e ∷ es) {tp} eq (le , lt) =
    let (t , et , e₁) = bind-just {m = FromIR.trTable es} eq
        (b , eb , e₂) = bind-just {m = FromIR.trI (FromIR.TrProg.rs t) (IRFun.fbody e)} e₁
    in subst (λ z → ProgOK Dc (FromIR.TrProg.prog z)) (just-inj e₂)
         (entry-ok (FromIR.TrProg.prog t) (FromIR.TrProg.rs t) e b (FromIR.blk? b) (table-ok es et lt)
                   (tr-ok (FromIR.trI-Tr (FromIR.TrProg.rs t) (IRFun.fbody e) eb) le))
