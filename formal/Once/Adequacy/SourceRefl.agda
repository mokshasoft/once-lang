-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.SourceRefl — the source semantics respects the value relation
-- (plan 0.119 D5).
--
-- The fundamental lemma of `ValueRel.RelD` for `⟦_⟧ˢ`: a term at related
-- environments, in related definitions environments, has related runs. Every
-- clause of `⟦_⟧ˢ` is a combination of binds, closures and the monadic layer
-- maps, each of which preserves relatedness; a pre-built morphism and a
-- reference's call go through the evaluator's lemma (`EvalRel.liftFn-rel`).
-- With one environment on both sides this says a meaning is related to itself
-- — what the graded relation needs of the implementation's closures.
------------------------------------------------------------------------

import Once.Spec.Type as SpT

open import Once.Weaken using (RelS-wk₀)
open import Once.Spec.Type using (Ty; Fun; KCtx; WFFun)
open import Once.Spec.Numerics using (TargetNum)

module Once.Adequacy.SourceRefl (fmt : TargetNum) where

open import Data.Empty using (⊥-elim)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Once.Spec.Grade using (Zero; One; Many; mk-kind; pure; eff; act; fin)
open import Once.Spec.Type using (Type; Unit; Void; Int; Float; _*_; _+_; _⇒[_]_)
open import Once.Spec.Type using (μ; ν)
open import Once.Type.Concrete using (con-base; con-fun)
open import Once.Spec.Type using (WFFun; b-Unit; ∅ₖ)
open import Once.Semantics.Machine using (sem-cata)
open import Once.IR.Semantics.StreamInf using (anaFᴵ)
open import Once.Denotation.ValueDomain using (coerce-functor-D)
open import Once.Context using (⟦_⟧ᶜ; _↾_)
open import Once.Spec.Context using (Ctx; Usage)
open import Once.Surface.Syntax using (Expr)
open import Once.Type.Sub
open import Once.Spec.Sub using (sub-*; sub-+)
open import Once.Spec.Sub using (_<:_; _<:ᶜ_; _⊔_≔_; sub-*; sub-+; subᶜ-*; subᶜ-+; sub-void; sub-var; sub-unit; sub-int; sub-float; sub-arr; sub-μ; sub-ν; subᶜ-void; subᶜ-var; subᶜ-unit; subᶜ-int; subᶜ-float; subᶜ-arr; subᶜ-μ; subᶜ-ν)
open import Once.Spec.Grade using (_⊑π_; ⊑-pure; ⊑-eff; ⊑-pe; ⊑-act; ⊑-pa; ⊑-ae)
open import Once.Type.SubDecide
open import Once.IR.Semantics.Iterative using (T∞; return∞; _>>=∞_; fmap∞)
open import Once.Denotation.DenotTrace using (CallEnv; module CallEnv)
open CallEnv using (ffiE)
open import Once.Denotation.ValueDomain using (⟦_⟧ᴰ)
open import Once.Denotation.Sub using (⟦_⟧<:; <:-refl-rel)
open import Once.Denotation.ValueRelPER using (RelD-sym)
open import Once.Laws.Sub using (<:-trans)
open import Once.Denotation.TraceMonadInfLaws using (RelS; RelS-bind; relS-ret; RelS-embed; RelS-iter∞)
open import Once.Denotation.ValueRel using (RelD; RelS-mono; base-eq; base-refl; RelS-fmap; RelS-fmapˡ; seqF∞-rel; cfD⁻¹-rel; cfD-rel; cμin-rel; sem-cata-rel; anaᴵ-rel; retargetˡ; retargetʳ)
open import Once.Denotation.EvalRel using (RelEnv; liftFn-rel; RelT′-refl)
open import Once.Adequacy.EnvRel using (restrict-rel; lookup-rel; bind-rel)
open import Once.SigOp.Info using (SigOpInfo; module SigOpInfo)
open SigOpInfo using (baseA; conB)
open import Once.IR.Ref using (refIR)
open import Once.Spec.Name using (bare)
open import Once.Arith.SigOp.Builders
import Once.Denotation.SourceDenote as SD
open SD using (DefsSem; module DefsSem)
open DefsSem using (calls; refs)

open Once.Surface.Syntax.Expr

-- The fold of related algebras is a related closure.
cata-clo-rel : ∀ {m} {Δₖ : KCtx m} {A : Ty m} {F : Fun m} {π} (wf : WFFun Δₖ F) {va vb : ⟦ SpT.⟦ F ⟧F A ⇒[ mk-kind Many π ] A ⟧ᴰ}
             → RelD (SpT.⟦ F ⟧F A ⇒[ mk-kind Many π ] A) va vb
             → RelD (μ F ⇒[ mk-kind Many π ] A) (λ x → sem-cata wf (SD.cata-ev-algˢ {C = A} {F = F} wf (return∞ va)) x)
                                                       (λ x → sem-cata wf (SD.cata-ev-algˢ {C = A} {F = F} wf (return∞ vb)) x)
cata-clo-rel {A = A} {F = F} wf {va} {vb} ralg {x} refl =
  sem-cata-rel wf {R = RelS (RelD A)} {SD.cata-ev-algˢ wf (return∞ va)} {SD.cata-ev-algˢ wf (return∞ vb)}
    (λ fr → RelS-bind (seqF∞-rel F fr) λ fl → retargetˡ refl (retargetʳ refl (ralg (cfD⁻¹-rel wf A fl)))) x

-- The unfold of related coalgebras, from related seeds, is a related stream.
ana-clo-rel : ∀ {m} {Δₖ : KCtx m} {A : Ty m} {F : Fun m} {φ} (wf : WFFun Δₖ F) {c c′ : ⟦ A ⇒[ mk-kind Many (fin φ) ] SpT.⟦ F ⟧F A ⟧ᴰ}
            → RelD (A ⇒[ mk-kind Many (fin φ) ] SpT.⟦ F ⟧F A) c c′
            → ∀ {a a′} → RelD A a a′
            → RelD (ν F φ) (anaFᴵ F (λ a' → fmap∞ (coerce-functor-D wf A) (c a')) a)
                                (anaFᴵ F (λ a' → fmap∞ (coerce-functor-D wf A) (c′ a')) a′)
ana-clo-rel {A = A} {F = F} wf rc ra = anaᴵ-rel (λ ra′ → RelS-fmap (RelS-fmap (rc ra′) (cfD-rel wf A)) (cμin-rel F)) ra

-- Related definitions environments: related calls, related references.
RelDefs : DefsSem → DefsSem → Set
RelDefs σ σ′ = RelEnv fmt (calls σ) (calls σ′) × (∀ {m} (x : String) (A : Ty m) → RelS (RelD A) (refs σ x A) (refs σ′ x A))

-- A conversion maps related values to related values.
<:-rel : ∀ {m} {A B : Ty m} (p : A <: B) {x y : ⟦ A ⟧ᴰ} → RelD A x y → RelD B (⟦ p ⟧<: x) (⟦ p ⟧<: y)
<:-rel sub-void {()}
<:-rel sub-unit  r = r
<:-rel sub-int   r = r
<:-rel sub-float r = r
<:-rel sub-μ     r = r
<:-rel (sub-ν _) r = r
<:-rel sub-var {()}
<:-rel (sub-arr {q = Zero} a b _) r = RelS-fmap r (<:-rel b)
<:-rel (sub-arr {q = One}  a b _) r ra = RelS-fmap (r (<:-rel a ra)) (<:-rel b)
<:-rel (sub-arr {q = Many} a b _) r ra = RelS-fmap (r (<:-rel a ra)) (<:-rel b)
<:-rel (sub-* a b) {_ , _} {_ , _} (r , s) = <:-rel a r , <:-rel b s
<:-rel (sub-+ a b) {inj₁ _} {inj₁ _} r = <:-rel a r
<:-rel (sub-+ a b) {inj₂ _} {inj₂ _} r = <:-rel b r
<:-rel (sub-+ a b) {inj₁ _} {inj₂ _} ()
<:-rel (sub-+ a b) {inj₂ _} {inj₁ _} ()

-- Two conversions in sequence relate to the composite conversion.
<:-trans-rel : ∀ {m} {A B C : Ty m} (p : A <: B) (q : B <: C) {x y : ⟦ A ⟧ᴰ} → RelD A x y
             → RelD C (⟦ q ⟧<: (⟦ p ⟧<: x)) (⟦ <:-trans p q ⟧<: y)
<:-trans-rel sub-void q {()}
<:-trans-rel sub-unit  q r = <:-rel q r
<:-trans-rel sub-int   q r = <:-rel q r
<:-trans-rel sub-float q r = <:-rel q r
<:-trans-rel sub-μ     q r = <:-rel q r
<:-trans-rel sub-var q {()}
<:-trans-rel (sub-arr {q = Zero} a b _) (sub-arr a′ b′ _) r =
  RelS-fmapˡ (RelS-fmap r (<:-trans-rel b b′)) (λ z → z)
<:-trans-rel (sub-arr {q = One} a b _) (sub-arr a′ b′ _) r rx =
  RelS-fmapˡ (RelS-fmap (r (<:-trans-rel a′ a rx)) (<:-trans-rel b b′)) (λ z → z)
<:-trans-rel (sub-arr {q = Many} a b _) (sub-arr a′ b′ _) r rx =
  RelS-fmapˡ (RelS-fmap (r (<:-trans-rel a′ a rx)) (<:-trans-rel b b′)) (λ z → z)
<:-trans-rel (sub-* a b) (sub-* a′ b′) {_ , _} {_ , _} (r , s) = <:-trans-rel a a′ r , <:-trans-rel b b′ s
<:-trans-rel (sub-+ a b) (sub-+ a′ b′) {inj₁ _} {inj₁ _} r = <:-trans-rel a a′ r
<:-trans-rel (sub-+ a b) (sub-+ a′ b′) {inj₂ _} {inj₂ _} r = <:-trans-rel b b′ r
<:-trans-rel (sub-+ a b) (sub-+ a′ b′) {inj₁ _} {inj₂ _} ()
<:-trans-rel (sub-+ a b) (sub-+ a′ b′) {inj₂ _} {inj₁ _} ()
<:-trans-rel (sub-ν _) (sub-ν _) r = r

-- The identity conversion on the right.
<:-refl-relʳ : ∀ {m} (A : Ty m) {x y : ⟦ A ⟧ᴰ} → RelD A x y → RelD A x (⟦ <:-refl A ⟧<: y)
<:-refl-relʳ A r = RelD-sym A (<:-refl-rel A (RelD-sym A r))

module _ {σ σ′ : DefsSem} (rσ : RelDefs σ σ′) where

  -- A SigOp: first-order arguments, the same finite tree on both sides.
  sigOp-rel : ∀ {X Y} (si : SigOpInfo X Y) {a a′ : ⟦ X ⟧ᴰ} → RelD X a a′
            → RelS (RelD Y) (SD.sigOpˢ fmt σ si a) (SD.sigOpˢ fmt σ′ si a′)
  sigOp-rel si r with base-eq (baseA si) r | proj₂ (proj₁ rσ)
  ... | refl | e rewrite e = RelS-embed (RelT′-refl (base-refl (conB si)) _)

  -- A comparison's result type `Unit + Unit` is closed: related at one index, at any.
  bool-rel : ∀ {m m′} {x y} → RelD {m} (Unit + Unit) x y → RelD {m′} (Unit + Unit) x y
  bool-rel {x = inj₁ _} {inj₁ _} r = r
  bool-rel {x = inj₂ _} {inj₂ _} r = r

  -- An external operation's meaning, related at its ground type.
  sigOpSem-rel : (A : Type) (name : Once.Spec.Name.CanonicalName) (c : Once.Type.Concrete.IsConcrete A)
               → RelS (RelD A) (SD.sigOpSem A name c fmt σ) (SD.sigOpSem A name c fmt σ′)
  sigOpSem-rel (Dom ⇒[ mk-kind Zero pure ] Cod) name (con-fun bD bC) = relS-ret (sigOp-rel (value-info name b-Unit bC) tt)
  sigOpSem-rel (Dom ⇒[ mk-kind Zero eff ] Cod) name (con-fun bD bC) = relS-ret (sigOp-rel (arrow-info (mk-kind Zero eff) name b-Unit bC) tt)
  sigOpSem-rel (Dom ⇒[ mk-kind Zero act ] Cod) name (con-fun bD bC) = relS-ret (sigOp-rel (arrow-info (mk-kind Zero act) name b-Unit bC) tt)
  sigOpSem-rel (Dom ⇒[ mk-kind One π ] Cod) name (con-fun bD bC) = relS-ret (sigOp-rel (arrow-info (mk-kind One π) name bD bC))
  sigOpSem-rel (Dom ⇒[ mk-kind Many π ] Cod) name (con-fun bD bC) = relS-ret (sigOp-rel (arrow-info (mk-kind Many π) name bD bC))
  sigOpSem-rel Unit name (con-base ib) = sigOp-rel (value-info name b-Unit ib) tt
  sigOpSem-rel Void name (con-base ib) = sigOp-rel (value-info name b-Unit ib) tt
  sigOpSem-rel Int name (con-base ib) = sigOp-rel (value-info name b-Unit ib) tt
  sigOpSem-rel Float name (con-base ib) = sigOp-rel (value-info name b-Unit ib) tt
  sigOpSem-rel (_ * _) name (con-base ib) = sigOp-rel (value-info name b-Unit ib) tt
  sigOpSem-rel (_ + _) name (con-base ib) = sigOp-rel (value-info name b-Unit ib) tt
  sigOpSem-rel (μ _) name (con-base ())
  sigOpSem-rel (ν _ _) name (con-base ())
  sigOpSem-rel (_ ⇒[ _ ] _) name (con-base ())

  SD-rel : ∀ {m} {n} {Γ : Ctx m n} {Ψ : Usage n} {A : Ty m} (e : Expr Γ Ψ A) {d d′ : ⟦ ⟦ Γ ↾ Ψ ⟧ᶜ ⟧ᴰ}
         → RelD ⟦ Γ ↾ Ψ ⟧ᶜ d d′ → RelS (RelD A) (SD.⟦ e ⟧ˢ fmt σ d) (SD.⟦ e ⟧ˢ fmt σ′ d′)
  SD-rel (var {Γ = Γ} i) r = relS-ret (lookup-rel Γ i r)
  SD-rel (lam {q' = Zero} Zero _ e) r = relS-ret (SD-rel e r)
  SD-rel (lam {q' = Zero} One  _ e) r = relS-ret (λ _ → SD-rel e r)
  SD-rel (lam {q' = Zero} Many _ e) r = relS-ret (λ _ → SD-rel e r)
  SD-rel (lam {q' = One}  One  _ e) r = relS-ret (λ ra → SD-rel e (r , ra))
  SD-rel (lam {q' = One}  Many _ e) r = relS-ret (λ ra → SD-rel e (r , ra))
  SD-rel (lam {q' = Many} Many _ e) r = relS-ret (λ ra → SD-rel e (r , ra))
  SD-rel (app {Γ = Γ} {q = Zero} f x) r = RelS-bind (SD-rel f (restrict-rel {Γ = Γ} _ r)) (λ rf → rf)
  SD-rel (app {Γ = Γ} {q = One} f x) r =
    RelS-bind (SD-rel f (restrict-rel {Γ = Γ} _ r)) λ rf → RelS-bind (SD-rel x (restrict-rel {Γ = Γ} _ r)) λ rx → rf rx
  SD-rel (app {Γ = Γ} {q = Many} f x) r =
    RelS-bind (SD-rel f (restrict-rel {Γ = Γ} _ r)) λ rf → RelS-bind (SD-rel x (restrict-rel {Γ = Γ} _ r)) λ rx → rf rx
  SD-rel (effApp {Γ = Γ} f x) r =
    relS-ret λ _ → RelS-bind (SD-rel f (restrict-rel {Γ = Γ} _ r)) λ rf → RelS-bind (SD-rel x (restrict-rel {Γ = Γ} _ r)) λ rx → rf rx
  SD-rel (pair {Γ = Γ} a b) r =
    RelS-bind (SD-rel a (restrict-rel {Γ = Γ} _ r)) λ ra → RelS-bind (SD-rel b (restrict-rel {Γ = Γ} _ r)) λ rb → relS-ret (ra , rb)
  SD-rel (comp' {Γ = Γ} f g) r =
    RelS-bind (SD-rel f (restrict-rel {Γ = Γ} _ r)) λ rf → RelS-bind (SD-rel g (restrict-rel {Γ = Γ} _ r)) λ rg →
    relS-ret (λ ra → RelS-bind (rg ra) rf)
  SD-rel (copair' {Γ = Γ} f g) r =
    RelS-bind (SD-rel f (restrict-rel {Γ = Γ} _ r)) λ rf → RelS-bind (SD-rel g (restrict-rel {Γ = Γ} _ r)) λ rg →
    relS-ret λ { {inj₁ _} {inj₁ _} ra → rf ra ; {inj₂ _} {inj₂ _} rb → rg rb ; {inj₁ _} {inj₂ _} () ; {inj₂ _} {inj₁ _} () }
  SD-rel (fork' {Γ = Γ} f g) r =
    RelS-bind (SD-rel f (restrict-rel {Γ = Γ} _ r)) λ rf → RelS-bind (SD-rel g (restrict-rel {Γ = Γ} _ r)) λ rg →
    relS-ret (λ ra → RelS-bind (rf ra) λ rb → RelS-bind (rg ra) λ rc → relS-ret (rb , rc))
  SD-rel (curry' f) r = RelS-bind (SD-rel f r) λ rf → relS-ret (λ ra → relS-ret (λ rb → rf (ra , rb)))
  SD-rel (fst' e) r = RelS-bind (SD-rel e r) λ rv → relS-ret (proj₁ rv)
  SD-rel (snd' e) r = RelS-bind (SD-rel e r) λ rv → relS-ret (proj₂ rv)
  SD-rel (inl' e) r = RelS-bind (SD-rel e r) λ rv → relS-ret rv
  SD-rel (inr' e) r = RelS-bind (SD-rel e r) λ rv → relS-ret rv
  SD-rel (case' {Γ = Γ} {qℓ = qℓ} {qr = qr} s l r′) r =
    RelS-bind (SD-rel s (restrict-rel {Γ = Γ} _ r))
      λ { {inj₁ _} {inj₁ _} ra → SD-rel l (bind-rel {Γ = Γ} qℓ (restrict-rel {Γ = Γ} _ (restrict-rel {Γ = Γ} _ r)) ra)
        ; {inj₂ _} {inj₂ _} rb → SD-rel r′ (bind-rel {Γ = Γ} qr (restrict-rel {Γ = Γ} _ (restrict-rel {Γ = Γ} _ r)) rb)
        ; {inj₁ _} {inj₂ _} ()
        ; {inj₂ _} {inj₁ _} () }
  SD-rel unit r = relS-ret tt
  SD-rel (absurd e) r = RelS-bind (SD-rel e r) (λ {a} _ → ⊥-elim a)
  SD-rel (let' {Γ = Γ} {q = Zero} e1 e2) r = SD-rel e2 (restrict-rel {Γ = Γ} _ r)
  SD-rel (let' {Γ = Γ} {q = One} e1 e2) r =
    RelS-bind (SD-rel e1 (restrict-rel {Γ = Γ} _ r)) λ rv → SD-rel e2 (restrict-rel {Γ = Γ} _ r , rv)
  SD-rel (let' {Γ = Γ} {q = Many} e1 e2) r =
    RelS-bind (SD-rel e1 (restrict-rel {Γ = Γ} _ r)) λ rv → SD-rel e2 (restrict-rel {Γ = Γ} _ r , rv)
  SD-rel (int n) r = relS-ret refl
  SD-rel (float d) r = relS-ret refl
  SD-rel (add {Γ = Γ} a b) r =
    RelS-bind (SD-rel a (restrict-rel {Γ = Γ} _ r)) λ ra → RelS-bind (SD-rel b (restrict-rel {Γ = Γ} _ r)) λ rb → sigOp-rel add-info (ra , rb)
  SD-rel (sub {Γ = Γ} a b) r =
    RelS-bind (SD-rel a (restrict-rel {Γ = Γ} _ r)) λ ra → RelS-bind (SD-rel b (restrict-rel {Γ = Γ} _ r)) λ rb → sigOp-rel sub-info (ra , rb)
  SD-rel (mul {Γ = Γ} a b) r =
    RelS-bind (SD-rel a (restrict-rel {Γ = Γ} _ r)) λ ra → RelS-bind (SD-rel b (restrict-rel {Γ = Γ} _ r)) λ rb → sigOp-rel mul-info (ra , rb)
  SD-rel (fadd {Γ = Γ} a b) r =
    RelS-bind (SD-rel a (restrict-rel {Γ = Γ} _ r)) λ ra → RelS-bind (SD-rel b (restrict-rel {Γ = Γ} _ r)) λ rb → sigOp-rel fadd-info (ra , rb)
  SD-rel (fsub {Γ = Γ} a b) r =
    RelS-bind (SD-rel a (restrict-rel {Γ = Γ} _ r)) λ ra → RelS-bind (SD-rel b (restrict-rel {Γ = Γ} _ r)) λ rb → sigOp-rel fsub-info (ra , rb)
  SD-rel (fmul {Γ = Γ} a b) r =
    RelS-bind (SD-rel a (restrict-rel {Γ = Γ} _ r)) λ ra → RelS-bind (SD-rel b (restrict-rel {Γ = Γ} _ r)) λ rb → sigOp-rel fmul-info (ra , rb)
  SD-rel (fdiv {Γ = Γ} a b) r =
    RelS-bind (SD-rel a (restrict-rel {Γ = Γ} _ r)) λ ra → RelS-bind (SD-rel b (restrict-rel {Γ = Γ} _ r)) λ rb → sigOp-rel fdiv-info (ra , rb)
  SD-rel (div {Γ = Γ} a b) r =
    RelS-bind (SD-rel a (restrict-rel {Γ = Γ} _ r)) λ ra → RelS-bind (SD-rel b (restrict-rel {Γ = Γ} _ r)) λ rb → sigOp-rel div-info (ra , rb)
  SD-rel (mod' {Γ = Γ} a b) r =
    RelS-bind (SD-rel a (restrict-rel {Γ = Γ} _ r)) λ ra → RelS-bind (SD-rel b (restrict-rel {Γ = Γ} _ r)) λ rb → sigOp-rel mod-info (ra , rb)
  SD-rel (lt {Γ = Γ} a b) r =
    RelS-bind (SD-rel a (restrict-rel {Γ = Γ} _ r)) λ ra → RelS-bind (SD-rel b (restrict-rel {Γ = Γ} _ r)) λ rb → RelS-mono (λ {x} {y} → bool-rel {x = x} {y = y}) (sigOp-rel lt-info (ra , rb))
  SD-rel (le {Γ = Γ} a b) r =
    RelS-bind (SD-rel a (restrict-rel {Γ = Γ} _ r)) λ ra → RelS-bind (SD-rel b (restrict-rel {Γ = Γ} _ r)) λ rb → RelS-mono (λ {x} {y} → bool-rel {x = x} {y = y}) (sigOp-rel le-info (ra , rb))
  SD-rel (gt {Γ = Γ} a b) r =
    RelS-bind (SD-rel a (restrict-rel {Γ = Γ} _ r)) λ ra → RelS-bind (SD-rel b (restrict-rel {Γ = Γ} _ r)) λ rb → RelS-mono (λ {x} {y} → bool-rel {x = x} {y = y}) (sigOp-rel gt-info (ra , rb))
  SD-rel (ge {Γ = Γ} a b) r =
    RelS-bind (SD-rel a (restrict-rel {Γ = Γ} _ r)) λ ra → RelS-bind (SD-rel b (restrict-rel {Γ = Γ} _ r)) λ rb → RelS-mono (λ {x} {y} → bool-rel {x = x} {y = y}) (sigOp-rel ge-info (ra , rb))
  SD-rel (eq {Γ = Γ} a b) r =
    RelS-bind (SD-rel a (restrict-rel {Γ = Γ} _ r)) λ ra → RelS-bind (SD-rel b (restrict-rel {Γ = Γ} _ r)) λ rb → RelS-mono (λ {x} {y} → bool-rel {x = x} {y = y}) (sigOp-rel eq-info (ra , rb))
  SD-rel (ne {Γ = Γ} a b) r =
    RelS-bind (SD-rel a (restrict-rel {Γ = Γ} _ r)) λ ra → RelS-bind (SD-rel b (restrict-rel {Γ = Γ} _ r)) λ rb → RelS-mono (λ {x} {y} → bool-rel {x = x} {y = y}) (sigOp-rel ne-info (ra , rb))
  SD-rel (i2f a) r = RelS-bind (SD-rel a r) (sigOp-rel i2f-info)
  SD-rel (neg a) r = RelS-bind (SD-rel a r) (sigOp-rel neg-info)
  SD-rel (coerce p e) r = RelS-fmap (SD-rel e r) (<:-rel p)
  SD-rel (lift-morphism {A = A} {B = B} ir) r = relS-ret (liftFn-rel fmt (proj₁ rσ) {A} {B} ir)
  SD-rel (morph-app {Γ = Γ} {A = A} {B = B} ir e) r =
    RelS-bind (SD-rel e (restrict-rel {Γ = Γ} _ r)) (liftFn-rel fmt (proj₁ rσ) {A} {B} ir)
  SD-rel (cata {Γ = Γ} {F = F} {A = A} {π = π} wf alg) r =
    RelS-bind (SD-rel alg (restrict-rel {Γ = Γ} _ r)) λ ralg → relS-ret (cata-clo-rel {A = A} {F = F} {π = π} wf ralg)
  SD-rel (ana {Γ = Γ} {F = F} {A = A} {π₀ = π₀} {φ = φ} wf coalg) r =
    RelS-bind (SD-rel coalg (restrict-rel {Γ = Γ} _ r)) λ rc → relS-ret (λ ra → relS-ret (ana-clo-rel {A = A} {F = F} {φ = φ} wf rc ra))
  SD-rel (loop {Γ = Γ} {A = A} {B = B} round) r =
    RelS-bind (SD-rel round (restrict-rel {Γ = Γ} _ r)) λ {c} {c′} rc →
      relS-ret (λ ra → RelS-iter∞ {RB = RelD B} {S = RelD (B + A)} {f = c} {f′ = c′}
                                  (λ rb → rb) rc (λ ()) (λ ()) ra)
  SD-rel (sigOp {A = A} name c) r = RelS-wk₀ A (sigOpSem-rel A name c)
  SD-rel (closure {A = A} name) r = liftFn-rel fmt (proj₁ rσ) {Unit} {A} (refIR A (bare name)) {tt} {tt} tt
  SD-rel (poly name PT) r = proj₂ rσ name PT
  SD-rel (closed e) r = SD-rel e {tt} {tt} tt
