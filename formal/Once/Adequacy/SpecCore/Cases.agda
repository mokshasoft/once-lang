{-# OPTIONS --guardedness #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.SpecCore.Cases — the rules of the fundamental lemma whose
-- meanings differ in more than the indices (plan 0.121 §3.5; plan 0.122:
-- over the one core): literals, primitive operations, coercions, the loop,
-- the recursion formers, the signature's declarations and definitions.
--
-- The arithmetic is the target's on both sides, written the same way: a
-- primitive is the same function of the same words. A declaration of Σ is
-- read the same way at every instance (`sig-R`), in one model; a definition
-- at the instantiated instance read at no variable is the definition at the
-- instance (`ref-R`, along `⟨⟩-0`).
------------------------------------------------------------------------

open import Data.Nat using (ℕ)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Product using (_,_)
open import Once.Spec.Signature using (Signature; _∶_; ⌜_⌝ᵈ; ⌜_⌝; DeclType; BTy; constant; value; operation; op; call)
open import Once.Spec.Core.Syntax using (Defs)
open import Once.Spec.Numerics using (TargetNum)

import Once.Spec.Grade
module Once.Adequacy.SpecCore.Cases (Σ : Signature) {s : ℕ} (S : Defs s) (fmt : TargetNum) where

open import Data.Unit using (tt)
open import Data.Fin using (Fin; zero; suc)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; cong)

import Once.Spec.Grade as LG
import Once.Spec.Grade as SG
import Once.Spec.Signature as SSig
import Once.Spec.Type as ST
open ST using (Ty; Type; Fun; KCtx; ∅ₖ; TySub; Respects; WFFun; _⟨_⟩; _⟨_⟩F; _⇒[_]_; _+_; μ; ν; ⟦_⟧F)
import Once.Spec.Type.Substitution as STS
import Once.Spec.Core.Syntax as SC
open SC using (Prim; primDom; primCod; Schema; _!!_)
open Schema using (arity; kinds; type)
open import Once.Spec.Context using (Ctx; _*ᵘ_)
open import Once.Spec.Sub using (_<:_)
open import Once.Spec.Core.Typing Σ S
open import Once.Spec.Core.Program Σ using (noVars)
open import Once.Spec.Observation Σ using (Model; module Model)
import Once.Spec.Core.Meaning Σ fmt S as SM
import Once.Metatheory.TermModel.TySubst Σ S as TS
import Once.Internal.Core.TySubstZero Σ S as TZ
open import Once.Functor.Translate using (Base-irrelevant)
open import Once.Postulates using (extensionality)
import Once.Spec.Effect Σ as SE
import Once.Spec.Domain Σ as SD
open import Once.Adequacy.SpecCore.Index
open import Once.Adequacy.SpecCore.Value Σ
open νpR
open νdR
open import Once.Adequacy.SpecCore.Monad Σ
open import Once.Adequacy.SpecCore.Env Σ S fmt
open import Once.Adequacy.SpecCore.Fundamental Σ S fmt
open import Once.Adequacy.SpecCore.Conv Σ S using (conv-R)
open import Once.Adequacy.SpecCore.Layer Σ
import Once.Adequacy.SpecCore.Fold as Fold
import Once.Adequacy.SpecCore.Unfold as Unfold

------------------------------------------------------------------------
-- Literals and primitive operations
------------------------------------------------------------------------

private
  bool-refl : ∀ (v : SD.⟦ ST.Unit {0} ST.+ ST.Unit ⟧ᵛ) → ValR (g-+ g-unit g-unit) v v
  bool-refl (inj₁ _) = tt
  bool-refl (inj₂ _) = tt

  ii = g-* g-int g-int
  ff = g-* g-float g-float
  bb = g-+ g-unit g-unit

module _ {m} (σ : TySub m 0) where

  gDom : ∀ p → GR (primDom {0} p ⟨ noVars ⟩) (primDom p ⟨ σ ⟩)
  gDom SC.p-add  = ii
  gDom SC.p-sub  = ii
  gDom SC.p-mul  = ii
  gDom SC.p-div  = ii
  gDom SC.p-mod  = ii
  gDom SC.p-neg  = g-int
  gDom SC.p-lt   = ii
  gDom SC.p-le   = ii
  gDom SC.p-gt   = ii
  gDom SC.p-ge   = ii
  gDom SC.p-eq   = ii
  gDom SC.p-ne   = ii
  gDom SC.p-fadd = ff
  gDom SC.p-fsub = ff
  gDom SC.p-fmul = ff
  gDom SC.p-fdiv = ff
  gDom SC.p-i2f  = g-int

  gCod : ∀ p → GR (primCod {0} p ⟨ noVars ⟩) (primCod p ⟨ σ ⟩)
  gCod SC.p-add  = g-int
  gCod SC.p-sub  = g-int
  gCod SC.p-mul  = g-int
  gCod SC.p-div  = g-int
  gCod SC.p-mod  = g-int
  gCod SC.p-neg  = g-int
  gCod SC.p-lt   = bb
  gCod SC.p-le   = bb
  gCod SC.p-gt   = bb
  gCod SC.p-ge   = bb
  gCod SC.p-eq   = bb
  gCod SC.p-ne   = bb
  gCod SC.p-fadd = g-float
  gCod SC.p-fsub = g-float
  gCod SC.p-fmul = g-float
  gCod SC.p-fdiv = g-float
  gCod SC.p-i2f  = g-float

  prim-R : ∀ p {x x′} → ValR (gDom p) x x′ → ValR (gCod p) (SM.primᵛ noVars p x) (SM.primᵛ σ p x′)
  prim-R SC.p-add  (refl , refl) = refl
  prim-R SC.p-sub  (refl , refl) = refl
  prim-R SC.p-mul  (refl , refl) = refl
  prim-R SC.p-div  (refl , refl) = refl
  prim-R SC.p-mod  (refl , refl) = refl
  prim-R SC.p-neg  refl          = refl
  prim-R SC.p-lt {a , b} {.a , .b} (refl , refl) = bool-refl (SM.primᵛ noVars SC.p-lt (a , b))
  prim-R SC.p-le {a , b} {.a , .b} (refl , refl) = bool-refl (SM.primᵛ noVars SC.p-le (a , b))
  prim-R SC.p-gt {a , b} {.a , .b} (refl , refl) = bool-refl (SM.primᵛ noVars SC.p-gt (a , b))
  prim-R SC.p-ge {a , b} {.a , .b} (refl , refl) = bool-refl (SM.primᵛ noVars SC.p-ge (a , b))
  prim-R SC.p-eq {a , b} {.a , .b} (refl , refl) = bool-refl (SM.primᵛ noVars SC.p-eq (a , b))
  prim-R SC.p-ne {a , b} {.a , .b} (refl , refl) = bool-refl (SM.primᵛ noVars SC.p-ne (a , b))
  prim-R SC.p-fadd (refl , refl) = refl
  prim-R SC.p-fsub (refl , refl) = refl
  prim-R SC.p-fmul (refl , refl) = refl
  prim-R SC.p-fdiv (refl , refl) = refl
  prim-R SC.p-i2f  refl          = refl

------------------------------------------------------------------------
-- The signature's declarations: read alike at every instance
------------------------------------------------------------------------

module _ {m} (σ : TySub m 0) where

  gb : ∀ (b : BTy) → GR (⌜_⌝ {0} b ⟨ noVars ⟩) (⌜_⌝ {m} b ⟨ σ ⟩)
  gb SSig.unit    = g-unit
  gb SSig.void    = g-void
  gb SSig.int     = g-int
  gb SSig.float   = g-float
  gb (a SSig.* b) = g-* (gb a) (gb b)
  gb (a SSig.+ b) = g-+ (gb a) (gb b)

  gS : ∀ (t : DeclType) → GR (⌜_⌝ᵈ {0} t ⟨ noVars ⟩) (⌜_⌝ᵈ {m} t ⟨ σ ⟩)
  gS (constant b)      = gb b
  gS (value a q b)     = g-⇒ (gb a) (gb b)
  gS (operation a q b) = g-⇒ (gb a) (gb b)

  fromB-R : ∀ b v → ValR (gb b) (SD.fromB noVars b v) (SD.fromB σ b v)
  fromB-R SSig.unit    v        = tt
  fromB-R SSig.void    ()
  fromB-R SSig.int     v        = refl
  fromB-R SSig.float   v        = refl
  fromB-R (a SSig.* b) (x , y)  = fromB-R a x , fromB-R b y
  fromB-R (a SSig.+ b) (inj₁ x) = fromB-R a x
  fromB-R (a SSig.+ b) (inj₂ y) = fromB-R b y

  toB-R : ∀ b {x x′} → ValR (gb b) x x′ → SD.toB noVars b x ≡ SD.toB σ b x′
  toB-R SSig.unit    r = refl
  toB-R SSig.void    {()} r
  toB-R SSig.int     r = r
  toB-R SSig.float   r = r
  toB-R (a SSig.* b) {_ , _} {_ , _} (r , r′) = cong₂′ (toB-R a r) (toB-R b r′)
    where cong₂′ : ∀ {A B : Set} {x x′ : A} {y y′ : B} → x ≡ x′ → y ≡ y′ → (x , y) ≡ (x′ , y′)
          cong₂′ refl refl = refl
  toB-R (a SSig.+ b) {inj₁ _} {inj₁ _} r = cong inj₁ (toB-R a r)
  toB-R (a SSig.+ b) {inj₂ _} {inj₂ _} r = cong inj₂ (toB-R b r)
  toB-R (a SSig.+ b) {inj₁ _} {inj₂ _} ()
  toB-R (a SSig.+ b) {inj₂ _} {inj₁ _} ()

  private
    call-R : ∀ {c a q b} (M : (c ∶ operation a q b) ∈ Σ) {y y′} → y ≡ y′
           → TR (ValR (gb b)) (SE.performT (call (op M) y (SD.fromB noVars b))) (SE.performT (call (op M) y′ (SD.fromB σ b)))
    call-R {b = b} M refl = call (λ v → ret (fromB-R b v))

  sig-R : ∀ (mo : Model) {c} {t : DeclType} (M : (c ∶ t) ∈ Σ)
        → ValR (gS t) (SM.sigopᵛ noVars c t M mo) (SM.sigopᵛ σ c t M mo)
  sig-R mo {t = constant b} M = fromB-R b _
  sig-R mo {t = value a LG.Zero b} M = fromB-R b _
  sig-R mo {t = value a LG.One  b} M {x} {x′} r =
    subst (λ z → ValR (gb b) (SD.fromB noVars b (Model.valueᵐ mo M (SD.toB noVars a x))) (SD.fromB σ b (Model.valueᵐ mo M z)))
          (toB-R a r) (fromB-R b _)
  sig-R mo {t = value a LG.Many b} M {x} {x′} r =
    subst (λ z → ValR (gb b) (SD.fromB noVars b (Model.valueᵐ mo M (SD.toB noVars a x))) (SD.fromB σ b (Model.valueᵐ mo M z)))
          (toB-R a r) (fromB-R b _)
  sig-R mo {t = operation a LG.Zero b} M = call-R M refl
  sig-R mo {t = operation a LG.One  b} M = λ r → call-R M (toB-R a r)
  sig-R mo {t = operation a LG.Many b} M = λ r → call-R M (toB-R a r)

------------------------------------------------------------------------
-- The rules on values and the loop
------------------------------------------------------------------------

module _ (ρ : SM.DefSem) (ρ′ : SM.DefSem) where

  lit-int : ∀ {m n} {Δ : KCtx m} {Γ : Ctx m n} {i} → Fund ρ ρ′ (⊢lit-int {Δ = Δ} {Γ = Γ} {i = i})
  lit-int σ r pr-pure e = refl

  lit-float : ∀ {m n} {Δ : KCtx m} {Γ : Ctx m n} {d} → Fund ρ ρ′ (⊢lit-float {Δ = Δ} {Γ = Γ} {d = d})
  lit-float σ r pr-pure e = refl

  prim : ∀ {m n} {Δ : KCtx m} {Γ : Ctx m n} {Ψ π t} (p : Prim)
         (d : Δ ⊩ Γ ⊢[ Ψ ] t ∷ primDom p ! π) → Fund ρ ρ′ d → Fund ρ ρ′ (⊢prim p d)
  prim p d ih σ r pp e =
    L-at ρ ρ′ σ r (sym (TS.primCod-⟨⟩ σ p)) _ pp (gCod σ p) (g⟨⟩ noVars _)
      (fmap-R pp (L-at ρ ρ′ σ r (TS.primDom-⟨⟩ σ p) (TS.ty-subst-⊢ σ r d) pp (g⟨⟩ noVars _) (gDom σ p) (ih σ r pp e)) (prim-R σ p))

  coerce : ∀ {m n} {Δ : KCtx m} {Γ : Ctx m n} {Ψ π A B t} (p : A <: B)
           (d : Δ ⊩ Γ ⊢[ Ψ ] t ∷ A ! π) → Fund ρ ρ′ d → Fund ρ ρ′ (⊢coerce p d)
  coerce p d ih σ r pp e = fmap-R pp (ih σ r pp e) (conv-R σ p)

  private
    toSum : ∀ {B B′ A A′} {gB : GR B B′} {gA : GR A A′} {v v′}
          → ValR (g-+ gB gA) v v′ → SumR (ValR gB) (ValR gA) v v′
    toSum {v = inj₁ _} {inj₁ _} r = left r
    toSum {v = inj₂ _} {inj₂ _} r = right r
    toSum {v = inj₁ _} {inj₂ _} ()
    toSum {v = inj₂ _} {inj₁ _} ()

  iter : ∀ {m n} {Δ : KCtx m} {Γ : Ctx m n} {Ψf Ψs π₁ π₂ A B f x}
         (df : Δ ⊩ Γ ⊢[ Ψf ] f ∷ A ⇒[ LG.mk-kind LG.Many LG.act ] (B + A) ! π₁)
         (dx : Δ ⊩ Γ ⊢[ Ψs ] x ∷ A ! π₂) → Fund ρ ρ′ df → Fund ρ ρ′ dx → Fund ρ ρ′ (⊢iter df dx)
  iter {Γ = Γ} {Ψf} {Ψs} {π₁} {π₂} df dx ihf ihx σ r pp e =
    re-pr ρ ρ′ (pr-· (pr π₁) (pr-· (pr π₂) pr-eff)) pp
      (bindᵍ-R (pr π₁) (pr-· (pr π₂) pr-eff)
         (ihf σ r (pr _) (env*Many-envˡ-R σ {Γ = Γ} Ψf Ψs e))
         (λ rf → bindᵍ-R (pr π₂) pr-eff (ihx σ r (pr _) (envʳ-R σ {Γ = Γ} (LG.Many *ᵘ Ψf) Ψs e))
                   (λ ra → loop-R (λ rx → TR-map toSum (rf rx)) ra)))

------------------------------------------------------------------------
-- References: the definitions and the declarations
------------------------------------------------------------------------

-- The definitions environments, related at every instance.
DefsR : SM.DefSem → SM.DefSem → Set
DefsR ρ ρ′ = ∀ d τ (r : Respects (kinds (S !! d)) ∅ₖ τ)
           → ValR (gr (type (S !! d) ⟨ τ ⟩)) (SM.DefSem.defs ρ d τ r) (SM.DefSem.defs ρ′ d τ r)

module _ (ρ : SM.DefSem) (ρ′ : SM.DefSem) (defsR : DefsR ρ ρ′) (model≡ : SM.DefSem.model ρ ≡ SM.DefSem.model ρ′) where

  private
    -- one definition, at equal instances, along equations of its type
    ref-R : ∀ d (τa τb : TySub (arity (S !! d)) 0) → τa ≡ τb
          → (ra : Respects (kinds (S !! d)) ∅ₖ τa) (rb : Respects (kinds (S !! d)) ∅ₖ τb)
          → ∀ {X Y} (ex : type (S !! d) ⟨ τa ⟩ ≡ X) (ey : type (S !! d) ⟨ τb ⟩ ≡ Y) (g : GR X Y)
          → ValR g (subst SD.⟦_⟧ᵛ ex (SM.DefSem.defs ρ d τa ra)) (subst SD.⟦_⟧ᵛ ey (SM.DefSem.defs ρ′ d τb rb))
    ref-R d τ .τ refl ra rb refl refl g =
      subst (λ q → ValR g (SM.DefSem.defs ρ d τ ra) (SM.DefSem.defs ρ′ d τ q))
            (extensionality λ i → extensionality λ e → Base-irrelevant _ _)
            (subst (λ g′ → ValR g′ _ _) (GR-unique (gr _) g) (defsR d τ ra))

  ref : ∀ {m n} {Δ : KCtx m} {Γ : Ctx m n} d τ rs → Fund ρ ρ′ (⊢ref {Δ = Δ} {Γ = Γ} d τ rs)
  ref d τ rs σ r pr-pure e =
    L-at ρ ρ′ σ r (sym e∘) (⊢ref {Δ = ∅ₖ} d τ′ (STS.respects-∘ rs r)) pr-pure gI (g⟨⟩ noVars _)
      (ref-R d (λ i → τ′ i ⟨ noVars ⟩) τ′ (extensionality λ i → TZ.⟨⟩-0 noVars (τ′ i)) _ (STS.respects-∘ rs r)
             (sym (STS.⟨⟩-∘ (type (S !! d)) τ′ noVars)) (sym e∘) gI)
    where
      τ′ = λ i → τ i ⟨ σ ⟩
      e∘ = STS.⟨⟩-∘ (type (S !! d)) τ σ
      gI = subst (λ Z → GR (type (S !! d) ⟨ τ′ ⟩ ⟨ noVars ⟩) Z) (sym e∘) (g⟨⟩ noVars _)

  sigop : ∀ {m n} {Δ : KCtx m} {Γ : Ctx m n} {c} {t : DeclType} (mem : (c ∶ t) ∈ Σ)
        → Fund ρ ρ′ (⊢sigop {Δ = Δ} {Γ = Γ} mem)
  sigop {c = c} {t} mem σ r pr-pure e =
    L-at ρ ρ′ σ r (sym (TS.⌜⌝ᵈ-⟨⟩ σ t)) _ pr-pure (gS σ t) (g⟨⟩ noVars _)
      (subst (λ mo → ValR (gS σ t) (SM.sigopᵛ noVars c t mem (SM.DefSem.model ρ)) (SM.sigopᵛ σ c t mem mo))
             model≡ (sig-R σ (SM.DefSem.model ρ) mem))

------------------------------------------------------------------------
-- The recursion formers
------------------------------------------------------------------------

module _ (ρ : SM.DefSem) (ρ′ : SM.DefSem) where

  roll : ∀ {m n} {Δ : KCtx m} {Γ : Ctx m n} {Ψ π F t} (wf : WFFun Δ F)
         (d : Δ ⊩ Γ ⊢[ Ψ ] t ∷ ⟦ F ⟧F (μ F) ! π) → Fund ρ ρ′ d → Fund ρ ρ′ (⊢roll wf d)
  roll {F = F} wf d ih σ r pp e =
    fmap-R pp
      (L-at ρ ρ′ σ r (TS.⟦⟧F-⟨⟩ σ F (μ F)) (TS.ty-subst-⊢ σ r d) pp (g⟨⟩ noVars _) (GR-⟦⟧σ σ F gμ) (ih σ r pp e))
      (λ rx → inR (toL-R σ F gμ rx))
    where gμ = g⟨⟩ noVars (μ F ⟨ σ ⟩)

  private
    outν-R : ∀ {m} (σ : TySub m 0) (F : Fun m) (wf : WFFun ∅ₖ (F ⟨ σ ⟩F)) φ {v w}
           → ValR (g⟨⟩ noVars (ν F φ ⟨ σ ⟩)) v w
           → MR (pr-fin φ) (ValR (GR-⟦⟧σ σ F (g⟨⟩ noVars (ν F φ ⟨ σ ⟩))))
                (SE.fmap (SG.fin φ) (SD.fromL noVars (F ⟨ σ ⟩F) (ν (F ⟨ σ ⟩F) φ)) (SE.νM.outν v))
                (SE.fmap (SG.fin φ) (SD.fromL σ F (ν F φ)) (SE.νM.outν w))
    outν-R σ F wf LG.pureᶠ rv = fromL-R σ F wf _ (forceᵖR rv)
    outν-R σ F wf LG.actᶠ  rv = fmap-R pr-act (forceᵈR rv) (fromL-R σ F wf _)

  out : ∀ {m n} {Δ : KCtx m} {Γ : Ctx m n} {Ψ} {φ : LG.Finite} {π₁ F t} (wf : WFFun Δ F)
        (d : Δ ⊩ Γ ⊢[ Ψ ] t ∷ ν F φ ! π₁) → Fund ρ ρ′ d → Fund ρ ρ′ (⊢out wf d)
  out {φ = φ} {π₁} {F} wf d ih σ r pp e =
    L-at ρ ρ′ σ r (sym (TS.⟦⟧F-⟨⟩ σ F (ν F φ))) _ pp (GR-⟦⟧σ σ F (g⟨⟩ noVars (ν F φ ⟨ σ ⟩))) (g⟨⟩ noVars _)
      (re-pr ρ ρ′ (pr-· (pr π₁) (pr-fin φ)) pp
        (bindᵍ-R (pr π₁) (pr-fin φ) (ih σ r (pr _) e) (outν-R σ F (TS.wf-⟨⟩ σ r wf) φ)))

  fold : ∀ {m n} {Δ : KCtx m} {Γ : Ctx m n} {Ψa Ψt π π₁ π₂ F A alg t} (wf : WFFun Δ F)
         (da : Δ ⊩ Γ ⊢[ Ψa ] alg ∷ ⟦ F ⟧F A ⇒[ LG.mk-kind LG.Many π ] A ! π₁)
         (dt : Δ ⊩ Γ ⊢[ Ψt ] t ∷ μ F ! π₂)
       → Fund ρ ρ′ da → Fund ρ ρ′ dt → Fund ρ ρ′ (⊢fold wf da dt)
  fold {Γ = Γ} {Ψa} {Ψt} {π} {π₁} {π₂} {F} {A} wf da dt iha iht σ r pp e =
    re-pr ρ ρ′ (pr-· (pr π₁) (pr-· (pr π₂) (pr π))) pp
      (bindᵍ-R (pr π₁) (pr-· (pr π₂) (pr π))
         (L-at ρ ρ′ σ r (cong (λ X → X ⇒[ LG.mk-kind LG.Many π ] A ⟨ σ ⟩) (TS.⟦⟧F-⟨⟩ σ F A)) (TS.ty-subst-⊢ σ r da)
               (pr π₁) (g⟨⟩ noVars _) gAlg
               (iha σ r (pr _) (env*Many-envˡ-R σ {Γ = Γ} Ψa Ψt e)))
         (λ ralg → bindᵍ-R (pr π₂) (pr π) (iht σ r (pr _) (envʳ-R σ {Γ = Γ} (LG.Many *ᵘ Ψa) Ψt e))
                     (λ rv → Fold.fold-R Σ (gf⟨⟩ noVars (F ⟨ σ ⟩F)) π
                               (λ rl → ralg (fromL-R σ F (TS.wf-⟨⟩ σ r wf) gA rl)) rv)))
    where
      gA   = g⟨⟩ noVars (A ⟨ σ ⟩)
      gAlg = g-⇒ {q = LG.Many} {π = π} (GR-⟦⟧σ σ F gA) gA

  unfold : ∀ {m n} {Δ : KCtx m} {Γ : Ctx m n} {Ψc Ψs} {φ : LG.Finite} {π₁ π₂ F A c x} (wf : WFFun Δ F)
           (dc : Δ ⊩ Γ ⊢[ Ψc ] c ∷ A ⇒[ LG.mk-kind LG.Many (LG.fin φ) ] ⟦ F ⟧F A ! π₁)
           (dx : Δ ⊩ Γ ⊢[ Ψs ] x ∷ A ! π₂) → Fund ρ ρ′ dc → Fund ρ ρ′ dx → Fund ρ ρ′ (⊢unfold wf dc dx)
  unfold {Γ = Γ} {Ψc} {Ψs} {LG.pureᶠ} {π₁} {π₂} {F} {A} wf dc dx ihc ihx σ r pp e =
    re-pr ρ ρ′ (pr-· (pr π₁) (pr π₂)) pp
      (bindᵍ-R (pr π₁) (pr π₂)
         (L-at ρ ρ′ σ r (cong (λ X → A ⟨ σ ⟩ ⇒[ LG.mk-kind LG.Many LG.pure ] X) (TS.⟦⟧F-⟨⟩ σ F A)) (TS.ty-subst-⊢ σ r dc)
               (pr π₁) (g⟨⟩ noVars _) gC
               (ihc σ r (pr _) (env*Many-envˡ-R σ {Γ = Γ} Ψc Ψs e)))
         (λ rc → fmap-R (pr π₂) (ihx σ r (pr _) (envʳ-R σ {Γ = Γ} (LG.Many *ᵘ Ψc) Ψs e))
                   (λ ra → Unfold.anaP-R Σ (gf⟨⟩ noVars (F ⟨ σ ⟩F)) (λ rx → toL-R σ F gA (rc rx)) ra)))
    where
      gA = g⟨⟩ noVars (A ⟨ σ ⟩)
      gC = g-⇒ {q = LG.Many} {π = LG.pure} gA (GR-⟦⟧σ σ F gA)
  unfold {Γ = Γ} {Ψc} {Ψs} {LG.actᶠ} {π₁} {π₂} {F} {A} wf dc dx ihc ihx σ r pp e =
    re-pr ρ ρ′ (pr-· (pr π₁) (pr π₂)) pp
      (bindᵍ-R (pr π₁) (pr π₂)
         (L-at ρ ρ′ σ r (cong (λ X → A ⟨ σ ⟩ ⇒[ LG.mk-kind LG.Many LG.act ] X) (TS.⟦⟧F-⟨⟩ σ F A)) (TS.ty-subst-⊢ σ r dc)
               (pr π₁) (g⟨⟩ noVars _) gC
               (ihc σ r (pr _) (env*Many-envˡ-R σ {Γ = Γ} Ψc Ψs e)))
         (λ rc → fmap-R (pr π₂) (ihx σ r (pr _) (envʳ-R σ {Γ = Γ} (LG.Many *ᵘ Ψc) Ψs e))
                   (λ ra → Unfold.anaA-R Σ (gf⟨⟩ noVars (F ⟨ σ ⟩F))
                              (λ rx → fmap-R pr-act (rc rx) (toL-R σ F gA)) ra)))
    where
      gA = g⟨⟩ noVars (A ⟨ σ ⟩)
      gC = g-⇒ {q = LG.Many} {π = LG.act} gA (GR-⟦⟧σ σ F gA)

------------------------------------------------------------------------
-- All of them
------------------------------------------------------------------------

module _ (ρ : SM.DefSem) (ρ′ : SM.DefSem) (defsR : DefsR ρ ρ′) (model≡ : SM.DefSem.model ρ ≡ SM.DefSem.model ρ′) where

  allCases : Cases ρ ρ′
  allCases = record
    { c-roll      = roll ρ ρ′
    ; c-fold      = fold ρ ρ′
    ; c-unfold    = unfold ρ ρ′
    ; c-out       = out ρ ρ′
    ; c-iter      = iter ρ ρ′
    ; c-coerce    = coerce ρ ρ′
    ; c-lit-int   = λ {m} {n} {Δ} {Γ} {i} → lit-int ρ ρ′ {i = i}
    ; c-lit-float = λ {m} {n} {Δ} {Γ} {d} → lit-float ρ ρ′ {d = d}
    ; c-prim      = prim ρ ρ′
    ; c-sigop     = sigop ρ ρ′ defsR model≡
    ; c-ref       = ref ρ ρ′ defsR model≡
    }

  fundamental : ∀ {m n} {Δ : KCtx m} {Γ : Ctx m n} {Ψ t A π} (D : Δ ⊩ Γ ⊢[ Ψ ] t ∷ A ! π) → Fund ρ ρ′ D
  fundamental = fund ρ ρ′ allCases
