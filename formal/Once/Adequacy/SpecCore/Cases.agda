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
-- primitive is the same function of the same words.
------------------------------------------------------------------------

open import Data.Nat using (ℕ)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Product using (_,_)
open import Once.Spec.Signature using (Signature; _∶_; ⌜_⌝ᵈ; DeclType)
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
import Once.Spec.Type as ST
open ST using (Ty; Type; Fun; KCtx; ∅ₖ; TySub; Respects; WFFun; _⟨_⟩; _⟨_⟩F; _⇒[_]_; _+_; μ; ν; ⟦_⟧F)
import Once.Spec.Type.Substitution as STS
import Once.Internal.Type.WellFormed as LW
import Once.Internal.GradedOps as LOps
import Once.Internal.Graded as LGr
open import Once.Internal.Type.Sub using (pure-⊑)
open import Once.Internal.Core.Decl using (toISig; ∈-toISig; ⌜⌝ᵈ-concrete)
import Once.Spec.Core.Syntax as SC
open SC using (Prim; primDom; primCod; Schema; _!!_)
open Schema using (arity; kinds; type)
open import Once.Spec.Context using (Ctx; _*ᵘ_)
open import Once.Internal.Context using (⊑ᵘ-+ˡ; ⊑ᵘ-+ʳ; ⊑ᵘ-trans; ⊑ᵘ-*Many)
open import Once.Spec.Sub using (_<:_)
open import Once.Spec.Core.Typing Σ S
import Once.Internal.Core.Meaning Σ S as GM
import Once.Spec.Core.Meaning Σ fmt S as SM
import Once.Metatheory.TermModel.TySubst Σ S as TS
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
-- Primitive operations: the same function of the same words
------------------------------------------------------------------------

private
  bool-refl : ∀ (v : LGr.⟦ ST.Unit {0} ST.+ ST.Unit ⟧ᵛ) → ValR (g-+ g-unit g-unit) v v
  bool-refl (inj₁ _) = tt
  bool-refl (inj₂ _) = tt

  ii = g-* g-int g-int
  ff = g-* g-float g-float
  bb = g-+ g-unit g-unit

module _ {m} (σ : TySub m 0) where

  gDom : ∀ p → GR (primDom {0} p) (primDom p ⟨ σ ⟩)
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

  gCod : ∀ p → GR (primCod {0} p) (primCod p ⟨ σ ⟩)
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

  prim-R : ∀ p {x x′} → ValR (gDom p) x x′ → ValR (gCod p) (GM.primSem p fmt x) (SM.primᵛ σ p x′)
  prim-R SC.p-add  (refl , refl) = refl
  prim-R SC.p-sub  (refl , refl) = refl
  prim-R SC.p-mul  (refl , refl) = refl
  prim-R SC.p-div  (refl , refl) = refl
  prim-R SC.p-mod  (refl , refl) = refl
  prim-R SC.p-neg  refl          = refl
  prim-R SC.p-lt {a , b} {.a , .b} (refl , refl) = bool-refl (GM.primSem SC.p-lt fmt (a , b))
  prim-R SC.p-le {a , b} {.a , .b} (refl , refl) = bool-refl (GM.primSem SC.p-le fmt (a , b))
  prim-R SC.p-gt {a , b} {.a , .b} (refl , refl) = bool-refl (GM.primSem SC.p-gt fmt (a , b))
  prim-R SC.p-ge {a , b} {.a , .b} (refl , refl) = bool-refl (GM.primSem SC.p-ge fmt (a , b))
  prim-R SC.p-eq {a , b} {.a , .b} (refl , refl) = bool-refl (GM.primSem SC.p-eq fmt (a , b))
  prim-R SC.p-ne {a , b} {.a , .b} (refl , refl) = bool-refl (GM.primSem SC.p-ne fmt (a , b))
  prim-R SC.p-fadd (refl , refl) = refl
  prim-R SC.p-fsub (refl , refl) = refl
  prim-R SC.p-fmul (refl , refl) = refl
  prim-R SC.p-fdiv (refl , refl) = refl
  prim-R SC.p-i2f  refl          = refl

------------------------------------------------------------------------
-- The cases
------------------------------------------------------------------------

module _ (ρ : GM.DefSem) (ρ′ : SM.DefSem) where

  lit-int : ∀ {m n} {Δ : KCtx m} {Γ : Ctx m n} {i} → Fund ρ ρ′ (⊢lit-int {Δ = Δ} {Γ = Γ} {i = i})
  lit-int σ r u pr-pure e = refl

  lit-float : ∀ {m n} {Δ : KCtx m} {Γ : Ctx m n} {d} → Fund ρ ρ′ (⊢lit-float {Δ = Δ} {Γ = Γ} {d = d})
  lit-float σ r u pr-pure e = refl

  prim : ∀ {m n} {Δ : KCtx m} {Γ : Ctx m n} {Ψ π t} (p : Prim)
         (d : Δ ⊩ Γ ⊢[ Ψ ] t ∷ primDom p ! π) → Fund ρ ρ′ d → Fund ρ ρ′ (⊢prim p d)
  prim p d ih σ r u pp e =
    L-at ρ ρ′ σ r (sym (TS.primCod-⟨⟩ σ p)) _ pp (gCod σ p) (gr _)
      (fmap-R pp (L-at ρ ρ′ σ r (TS.primDom-⟨⟩ σ p) (TS.ty-subst-⊢ σ r d) pp (gr _) (gDom σ p) (ih σ r u pp e)) (prim-R σ p))

  coerce : ∀ {m n} {Δ : KCtx m} {Γ : Ctx m n} {Ψ π A B t} (p : A <: B)
           (d : Δ ⊩ Γ ⊢[ Ψ ] t ∷ A ! π) → Fund ρ ρ′ d → Fund ρ ρ′ (⊢coerce p d)
  coerce p d ih σ r u pp e = fmap-R pp (ih σ r u pp e) (conv-R σ p)

  -- (a pure sum value, read as a step of the loop)
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
  iter {Γ = Γ} {Ψf} {Ψs} {π₁} {π₂} df dx ihf ihx σ r u pp e =
    re-pr ρ ρ′ (pr-· (pr π₁) (pr-· (pr π₂) pr-eff)) pp
      (bindᵍ-R (pr π₁) (pr-· (pr π₂) pr-eff)
         (ihf σ r (ur Ψf) (pr _) (env*Many-envˡ-R σ {Γ = Γ} (⊑ᵘ-trans (⊑ᵘ-*Many Ψf) (⊑ᵘ-+ˡ (LG.Many *ᵘ Ψf) Ψs)) u (ur Ψf) e))
         (λ rf → bindᵍ-R (pr π₂) pr-eff (ihx σ r (ur Ψs) (pr _) (envʳ-R σ {Γ = Γ} (⊑ᵘ-+ʳ (LG.Many *ᵘ Ψf) Ψs) u (ur Ψs) e))
                   (λ ra → loop-R (λ rx → TR-map toSum (rf rx)) ra)))

------------------------------------------------------------------------
-- Definitions and declarations: the definitions environments related
------------------------------------------------------------------------

-- The definitions mean related values at each instance.
DefsR : GM.DefSem → SM.DefSem → Set
DefsR ρ ρ′ = ∀ d τ (r : Respects (kinds (S !! d)) ∅ₖ τ)
           → ValR (gr (type (S !! d) ⟨ τ ⟩)) (GM.DefSem.defs ρ d τ r) (SM.DefSem.defs ρ′ d τ r)

-- A declaration's type, at an instance, is its own.
gS : ∀ {m} (σ : TySub m 0) (t : DeclType) → GR (⌜ t ⌝ᵈ) (⌜ t ⌝ᵈ ⟨ σ ⟩)
gS σ t = subst (λ Z → GR ⌜ t ⌝ᵈ Z) (sym (TS.⌜⌝ᵈ-⟨⟩ σ t)) (gr _)

-- The signature's declarations mean related values.
SigR : GM.DefSem → SM.DefSem → Set
SigR ρ ρ′ = ∀ {m} (σ : TySub m 0) {c t} (mem : (c ∶ t) ∈ Σ)
          → ValR (gS σ t) (LOps.sigOpRefᵛ {A = ⌜ t ⌝ᵈ} fmt (toISig Σ) (GM.DefSem.impl ρ) c (⌜⌝ᵈ-concrete t) (∈-toISig mem))
                          (SM.sigopᵛ σ c t mem (SM.DefSem.model ρ′))

-- (a Spec value moved along an equation of its type)
ValR-substʳ : ∀ {X A′ A″} (e : A′ ≡ A″) (g′ : GR X A′) (g″ : GR X A″) {x y}
            → ValR g′ x y → ValR g″ x (subst SD.⟦_⟧ᵛ e y)
ValR-substʳ refl g′ g″ r = subst (λ g → ValR g _ _) (GR-unique g′ g″) r

module _ (ρ : GM.DefSem) (ρ′ : SM.DefSem) (defsR : DefsR ρ ρ′) (sigR : SigR ρ ρ′) where

  ref : ∀ {m n} {Δ : KCtx m} {Γ : Ctx m n} d τ rs → Fund ρ ρ′ (⊢ref {Δ = Δ} {Γ = Γ} d τ rs)
  ref d τ rs σ r u pr-pure e =
    L-at ρ ρ′ σ r (sym e∘) (⊢ref {Δ = ∅ₖ} d τ′ (STS.respects-∘ rs r)) pr-pure gI (gr _)
      (ValR-substʳ (sym e∘) (gr _) gI (defsR d τ′ (STS.respects-∘ rs r)))
    where
      τ′ = λ i → τ i ⟨ σ ⟩
      e∘ = STS.⟨⟩-∘ (type (S !! d)) τ σ
      gI = subst (λ Z → GR (type (S !! d) ⟨ τ′ ⟩) Z) (sym e∘) (gr _)

  sigop : ∀ {m n} {Δ : KCtx m} {Γ : Ctx m n} {c} {t : DeclType} (mem : (c ∶ t) ∈ Σ)
        → Fund ρ ρ′ (⊢sigop {Δ = Δ} {Γ = Γ} mem)
  sigop {t = t} mem σ r u pr-pure e =
    L-at ρ ρ′ σ r (sym (TS.⌜⌝ᵈ-⟨⟩ σ t)) _ pr-pure (gS σ t) (gr _) (sigR σ mem)

------------------------------------------------------------------------
-- Recursive types
------------------------------------------------------------------------

module _ (ρ : GM.DefSem) (ρ′ : SM.DefSem) where

  roll : ∀ {m n} {Δ : KCtx m} {Γ : Ctx m n} {Ψ π F t} (wf : WFFun Δ F)
         (d : Δ ⊩ Γ ⊢[ Ψ ] t ∷ ⟦ F ⟧F (μ F) ! π) → Fund ρ ρ′ d → Fund ρ ρ′ (⊢roll wf d)
  roll {F = F} wf d ih σ r u pp e =
    fmap-R pp
      (L-at ρ ρ′ σ r (TS.⟦⟧F-⟨⟩ σ F (μ F)) (TS.ty-subst-⊢ σ r d) pp (gr _) (GR-⟦⟧σ σ F gμ) (ih σ r u pp e))
      (λ rx → inR (in-R (gf (F ⟨ σ ⟩F)) (cf-R σ F (TS.wf-⟨⟩ σ r wf) gμ rx)))
    where gμ = gr (μ F ⟨ σ ⟩)

  private
    -- one layer of a stream, read on both sides
    outν-R : ∀ {m} (σ : TySub m 0) (F : Fun m) (wf : LW.WellFormedF (F ⟨ σ ⟩F)) φ {v w}
           → ValR (gr (ν F φ ⟨ σ ⟩)) v w
           → MR (pr-fin φ) (ValR (GR-⟦⟧σ σ F (gr (ν F φ ⟨ σ ⟩))))
                (LOps.out-semᵛ φ wf v) (SE.fmap (SG.fin φ) (SD.fromL σ F (ν F φ)) (SE.νM.outν w))
    outν-R σ F wf LG.pureᶠ rv = cf⁻¹-R σ F wf _ (out-R (gf (F ⟨ σ ⟩F)) wf (forceᵖR rv))
    outν-R σ F wf LG.actᶠ  rv =
      bindT-R (forceᵈR rv) (λ rl → ret (cf⁻¹-R σ F wf _ (out-R (gf (F ⟨ σ ⟩F)) wf rl)))

  out : ∀ {m n} {Δ : KCtx m} {Γ : Ctx m n} {Ψ} {φ : LG.Finite} {π₁ F t} (wf : WFFun Δ F)
        (d : Δ ⊩ Γ ⊢[ Ψ ] t ∷ ν F φ ! π₁) → Fund ρ ρ′ d → Fund ρ ρ′ (⊢out wf d)
  out {φ = φ} {π₁} {F} wf d ih σ r u pp e =
    L-at ρ ρ′ σ r (sym (TS.⟦⟧F-⟨⟩ σ F (ν F φ))) _ pp (GR-⟦⟧σ σ F (gr (ν F φ ⟨ σ ⟩))) (gr _)
      (re-pr ρ ρ′ (pr-· (pr π₁) (pr-fin φ)) pp
        (bindᵍ-R (pr π₁) (pr-fin φ) (ih σ r u (pr _) e) (outν-R σ F (TS.wf-⟨⟩ σ r wf) φ)))

  fold : ∀ {m n} {Δ : KCtx m} {Γ : Ctx m n} {Ψa Ψt π π₁ π₂ F A alg t} (wf : WFFun Δ F)
         (da : Δ ⊩ Γ ⊢[ Ψa ] alg ∷ ⟦ F ⟧F A ⇒[ LG.mk-kind LG.Many π ] A ! π₁)
         (dt : Δ ⊩ Γ ⊢[ Ψt ] t ∷ μ F ! π₂)
       → Fund ρ ρ′ da → Fund ρ ρ′ dt → Fund ρ ρ′ (⊢fold wf da dt)
  fold {Γ = Γ} {Ψa} {Ψt} {π} {π₁} {π₂} {F} {A} wf da dt iha iht σ r u pp e =
    re-pr ρ ρ′ (pr-· (pr π₁) (pr-· (pr π₂) (pr π))) pp
      (bindᵍ-R (pr π₁) (pr-· (pr π₂) (pr π))
         (L-at ρ ρ′ σ r (cong (λ X → X ⇒[ LG.mk-kind LG.Many π ] A ⟨ σ ⟩) (TS.⟦⟧F-⟨⟩ σ F A)) (TS.ty-subst-⊢ σ r da)
               (pr π₁) (gr _) gAlg
               (iha σ r (ur Ψa) (pr _) (env*Many-envˡ-R σ {Γ = Γ} (⊑ᵘ-trans (⊑ᵘ-*Many Ψa) (⊑ᵘ-+ˡ (LG.Many *ᵘ Ψa) Ψt)) u (ur Ψa) e)))
         (λ ralg → bindᵍ-R (pr π₂) (pr π) (iht σ r (ur Ψt) (pr _) (envʳ-R σ {Γ = Γ} (⊑ᵘ-+ʳ (LG.Many *ᵘ Ψa) Ψt) u (ur Ψt) e))
                     (λ rv → Fold.fold-R Σ σ F A (TS.wf-⟨⟩ σ r wf) (pure-⊑ π) (λ {x} {y} r₀ → ralg r₀) rv)))
    where
      gA   = gr (A ⟨ σ ⟩)
      gAlg = g-⇒ {q = LG.Many} {π = π} (GR-⟦⟧σ σ F gA) gA

  unfold : ∀ {m n} {Δ : KCtx m} {Γ : Ctx m n} {Ψc Ψs} {φ : LG.Finite} {π₁ π₂ F A c x} (wf : WFFun Δ F)
           (dc : Δ ⊩ Γ ⊢[ Ψc ] c ∷ A ⇒[ LG.mk-kind LG.Many (LG.fin φ) ] ⟦ F ⟧F A ! π₁)
           (dx : Δ ⊩ Γ ⊢[ Ψs ] x ∷ A ! π₂) → Fund ρ ρ′ dc → Fund ρ ρ′ dx → Fund ρ ρ′ (⊢unfold wf dc dx)
  unfold {Γ = Γ} {Ψc} {Ψs} {LG.pureᶠ} {π₁} {π₂} {F} {A} wf dc dx ihc ihx σ r u pp e =
    re-pr ρ ρ′ (pr-· (pr π₁) (pr π₂)) pp
      (bindᵍ-R (pr π₁) (pr π₂)
         (L-at ρ ρ′ σ r (cong (λ X → A ⟨ σ ⟩ ⇒[ LG.mk-kind LG.Many LG.pure ] X) (TS.⟦⟧F-⟨⟩ σ F A)) (TS.ty-subst-⊢ σ r dc)
               (pr π₁) (gr _) gC
               (ihc σ r (ur Ψc) (pr _) (env*Many-envˡ-R σ {Γ = Γ} (⊑ᵘ-trans (⊑ᵘ-*Many Ψc) (⊑ᵘ-+ˡ (LG.Many *ᵘ Ψc) Ψs)) u (ur Ψc) e)))
         (λ rc → fmap-R (pr π₂) (ihx σ r (ur Ψs) (pr _) (envʳ-R σ {Γ = Γ} (⊑ᵘ-+ʳ (LG.Many *ᵘ Ψc) Ψs) u (ur Ψs) e))
                   (λ ra → Unfold.anaP-R Σ (gf (F ⟨ σ ⟩F))
                              (λ rx → in-R (gf (F ⟨ σ ⟩F)) (cf-R σ F (TS.wf-⟨⟩ σ r wf) gA (rc rx))) ra)))
    where
      gA = gr (A ⟨ σ ⟩)
      gC = g-⇒ {q = LG.Many} {π = LG.pure} gA (GR-⟦⟧σ σ F gA)
  unfold {Γ = Γ} {Ψc} {Ψs} {LG.actᶠ} {π₁} {π₂} {F} {A} wf dc dx ihc ihx σ r u pp e =
    re-pr ρ ρ′ (pr-· (pr π₁) (pr π₂)) pp
      (bindᵍ-R (pr π₁) (pr π₂)
         (L-at ρ ρ′ σ r (cong (λ X → A ⟨ σ ⟩ ⇒[ LG.mk-kind LG.Many LG.act ] X) (TS.⟦⟧F-⟨⟩ σ F A)) (TS.ty-subst-⊢ σ r dc)
               (pr π₁) (gr _) gC
               (ihc σ r (ur Ψc) (pr _) (env*Many-envˡ-R σ {Γ = Γ} (⊑ᵘ-trans (⊑ᵘ-*Many Ψc) (⊑ᵘ-+ˡ (LG.Many *ᵘ Ψc) Ψs)) u (ur Ψc) e)))
         (λ rc → fmap-R (pr π₂) (ihx σ r (ur Ψs) (pr _) (envʳ-R σ {Γ = Γ} (⊑ᵘ-+ʳ (LG.Many *ᵘ Ψc) Ψs) u (ur Ψs) e))
                   (λ ra → Unfold.anaA-R Σ (gf (F ⟨ σ ⟩F))
                              (λ rx → fmap-R pr-act (rc rx)
                                        (λ rl → in-R (gf (F ⟨ σ ⟩F)) (cf-R σ F (TS.wf-⟨⟩ σ r wf) gA rl))) ra)))
    where
      gA = gr (A ⟨ σ ⟩)
      gC = g-⇒ {q = LG.Many} {π = LG.act} gA (GR-⟦⟧σ σ F gA)

------------------------------------------------------------------------
-- The fundamental lemma, every rule
------------------------------------------------------------------------

module _ (ρ : GM.DefSem) (ρ′ : SM.DefSem) (defsR : DefsR ρ ρ′) (sigR : SigR ρ ρ′) where

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
    ; c-sigop     = sigop ρ ρ′ defsR sigR
    ; c-ref       = ref ρ ρ′ defsR sigR
    }

  -- A derivation, instantiated, and read at the instance, mean related computations.
  fundamental : ∀ {m n} {Δ : KCtx m} {Γ : Ctx m n} {Ψ t A π} (D : Δ ⊩ Γ ⊢[ Ψ ] t ∷ A ! π) → Fund ρ ρ′ D
  fundamental = fund ρ ρ′ allCases
