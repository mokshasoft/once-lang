{-# OPTIONS --guardedness #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.SpecCore.Cases — the rules of the fundamental lemma whose
-- meanings differ in more than the indices (plan 0.121 §3.5): literals,
-- primitive operations, …
--
-- The arithmetic is the target's on both sides, written the same way: a
-- primitive is the same function of the same words.
------------------------------------------------------------------------

open import Data.Nat using (ℕ)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Product using (_,_)
open import Once.Lang.Contract using (ISig)
open import Once.Lang.Name using (showCanonical)
import Once.Lang.Core.PolyTy as LP
open import Once.Spec.Signature using (Signature; _∶_; ⌜_⌝ᵈ)
open import Once.Spec.Numerics using (TargetNum)
open import Once.Adequacy.SpecCore.Poly using (declS; declS-S; ptyS-⟦⟧; wfS)

module Once.Adequacy.SpecCore.Cases
  {Fs : ISig} {s : ℕ} (S : LP.Sig Fs s) (Σ : Signature)
  (sigop-S : ∀ {c A} → (showCanonical c , A) ∈ Fs → (c ∶ declS A) ∈ Σ)
  (fmt : TargetNum) where

open import Data.Unit using (tt)
open import Data.Fin using (Fin; zero; suc)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; cong)

import Once.Lang.Type as LT
import Once.Lang.Type.Grade as LG
import Once.Lang.Type.WellFormed as LW
import Once.Lang.Type.Honest as LH
import Once.Lang.GradedOps as LOps
import Once.Spec.Type as ST
import Once.Lang.Graded as LGr
import Once.Lang.Core.PolyTyping S as PT
import Once.Lang.Core.Syntax S as L
import Once.Lang.Core.Typing S as GT
import Once.Lang.Core.Meaning S as GM
import Once.Spec.Core.Syntax as SC
open import Once.Adequacy.SpecCore.Schema using (kindsS; defsS; castSub; ptyS; pfunS)
open import Once.Adequacy.SpecGrammar.Conv using (φS)
import Once.Spec.Grade as SG
import Once.Spec.Effect Σ as SE
open import Once.Adequacy.SpecCore.Context using (uS-zero)
open import Once.Adequacy.SpecCore.Prim S using (primS; primDom-S; primCod-S)
open import Once.Adequacy.SpecCore.Poly using (module Translate)
open Translate S Σ sigop-S
import Once.Spec.Core.Typing Σ S′ as S⊢
import Once.Spec.Core.Meaning Σ fmt S′ as SM
import Once.Spec.Domain Σ as SD
open import Once.Adequacy.SpecCore.Index
open import Once.Adequacy.SpecCore.Value Σ
open νpR
open νdR
open import Once.Adequacy.SpecCore.Monad Σ
open import Once.Adequacy.SpecCore.Env S Σ fmt
open import Once.Adequacy.SpecCore.Fundamental S Σ sigop-S fmt
open import Once.Adequacy.SpecCore.Conv S Σ using (conv-R)
open import Once.Adequacy.SpecCore.Layer Σ
import Once.Adequacy.SpecCore.Fold as Fold
import Once.Adequacy.SpecCore.Unfold as Unfold
import Once.Lang.Context as LC
import Once.Lang.Type.Sub as LS

------------------------------------------------------------------------
-- Primitive operations: the same function of the same words
------------------------------------------------------------------------

private
  bool-refl : ∀ (v : LGr.⟦ LT.Unit LT.+ LT.Unit ⟧ᵛ) → ValR (g-+ g-unit g-unit) v v
  bool-refl (inj₁ _) = tt
  bool-refl (inj₂ _) = tt

  ii : GR (LT.Int LT.* LT.Int) (ST.Int ST.* ST.Int)
  ii = g-* g-int g-int
  ff : GR (LT.Float LT.* LT.Float) (ST.Float ST.* ST.Float)
  ff = g-* g-float g-float
  bb : GR (LT.Unit LT.+ LT.Unit) (ST.Unit ST.+ ST.Unit)
  bb = g-+ g-unit g-unit

module _ {m} (σ′ : ST.TySub m 0) where

  gDom : ∀ p → GR (L.primDom p) (SC.primDom (primS p) ST.⟨ σ′ ⟩)
  gDom L.p-add  = ii
  gDom L.p-sub  = ii
  gDom L.p-mul  = ii
  gDom L.p-div  = ii
  gDom L.p-mod  = ii
  gDom L.p-neg  = g-int
  gDom L.p-lt   = ii
  gDom L.p-le   = ii
  gDom L.p-gt   = ii
  gDom L.p-ge   = ii
  gDom L.p-eq   = ii
  gDom L.p-ne   = ii
  gDom L.p-fadd = ff
  gDom L.p-fsub = ff
  gDom L.p-fmul = ff
  gDom L.p-fdiv = ff
  gDom L.p-i2f  = g-int

  gCod : ∀ p → GR (L.primCod p) (SC.primCod (primS p) ST.⟨ σ′ ⟩)
  gCod L.p-add  = g-int
  gCod L.p-sub  = g-int
  gCod L.p-mul  = g-int
  gCod L.p-div  = g-int
  gCod L.p-mod  = g-int
  gCod L.p-neg  = g-int
  gCod L.p-lt   = bb
  gCod L.p-le   = bb
  gCod L.p-gt   = bb
  gCod L.p-ge   = bb
  gCod L.p-eq   = bb
  gCod L.p-ne   = bb
  gCod L.p-fadd = g-float
  gCod L.p-fsub = g-float
  gCod L.p-fmul = g-float
  gCod L.p-fdiv = g-float
  gCod L.p-i2f  = g-float

  prim-R : ∀ p {x x′} → ValR (gDom p) x x′ → ValR (gCod p) (GM.primSem p fmt x) (SM.primᵛ σ′ (primS p) x′)
  prim-R L.p-add  (refl , refl) = refl
  prim-R L.p-sub  (refl , refl) = refl
  prim-R L.p-mul  (refl , refl) = refl
  prim-R L.p-div  (refl , refl) = refl
  prim-R L.p-mod  (refl , refl) = refl
  prim-R L.p-neg  refl          = refl
  prim-R L.p-lt {a , b} {.a , .b} (refl , refl) = bool-refl (GM.primSem L.p-lt fmt (a , b))
  prim-R L.p-le {a , b} {.a , .b} (refl , refl) = bool-refl (GM.primSem L.p-le fmt (a , b))
  prim-R L.p-gt {a , b} {.a , .b} (refl , refl) = bool-refl (GM.primSem L.p-gt fmt (a , b))
  prim-R L.p-ge {a , b} {.a , .b} (refl , refl) = bool-refl (GM.primSem L.p-ge fmt (a , b))
  prim-R L.p-eq {a , b} {.a , .b} (refl , refl) = bool-refl (GM.primSem L.p-eq fmt (a , b))
  prim-R L.p-ne {a , b} {.a , .b} (refl , refl) = bool-refl (GM.primSem L.p-ne fmt (a , b))
  prim-R L.p-fadd (refl , refl) = refl
  prim-R L.p-fsub (refl , refl) = refl
  prim-R L.p-fmul (refl , refl) = refl
  prim-R L.p-fdiv (refl , refl) = refl
  prim-R L.p-i2f  refl          = refl

------------------------------------------------------------------------
-- The cases
------------------------------------------------------------------------

module _ (ρ : GM.DefSem) (ρ′ : SM.DefSem) where

  lit-int : ∀ {m n} {Δ : LP.KCtx m} {Γ : PT.PCtx m n} {i} → Fund ρ ρ′ (PT.⊢lit-int {Δ = Δ} {Γ = Γ} {i = i})
  lit-int {n = n} {Δ} {Γ} r r′ g e =
    S-at ρ ρ′ g {Γ = Γ} (sym (uS-zero {n})) refl refl (S⊢.⊢lit-int {Δ = kindsS Δ} {Γ = pctxS Γ}) (crΓ Γ) ur-zero (ur _)
         g-int g-int pr-pure pr-pure _ (λ _ → refl) e

  lit-float : ∀ {m n} {Δ : LP.KCtx m} {Γ : PT.PCtx m n} {d} → Fund ρ ρ′ (PT.⊢lit-float {Δ = Δ} {Γ = Γ} {d = d})
  lit-float {n = n} {Δ} {Γ} r r′ g e =
    S-at ρ ρ′ g {Γ = Γ} (sym (uS-zero {n})) refl refl (S⊢.⊢lit-float {Δ = kindsS Δ} {Γ = pctxS Γ}) (crΓ Γ) ur-zero (ur _)
         g-float g-float pr-pure pr-pure _ (λ _ → refl) e

  prim : ∀ {m n} {Δ : LP.KCtx m} {Γ : PT.PCtx m n} {Ψ π t} (p : L.Prim)
         (d : PT._⊩_⊢[_]_∷_!_ Δ Γ Ψ t LP.⌈ L.primDom p ⌉ π) → Fund ρ ρ′ d → Fund ρ ρ′ (PT.⊢prim p d)
  prim {Γ = Γ} {Ψ} {π} p d ih {σ} {σ′} r r′ g e =
    L-at ρ ρ′ (sym (LP.⌈⌉-⟪⟫ (L.primCod p) σ)) _ (pr π) gC (GR-inst (ptr LP.⌈ L.primCod p ⌉) g)
      (S-at ρ ρ′ g refl (sym (primCod-S p)) refl (S⊢.⊢prim (primS p) (atS refl (primDom-S p) refl (trD d)))
            (crΓ Γ) (ur Ψ) (ur Ψ) (gCod σ′ p) gC (pr π) (pr π) _
            (λ e₀ → fmap-R (pr π)
                       (L-at ρ ρ′ (LP.⌈⌉-⟪⟫ (L.primDom p) σ) (PT.instantiate σ r d) (pr π) gD (gDom σ′ p)
                          (S-at ρ ρ′ g refl (primDom-S p) refl (trD d) (crΓ Γ) (ur Ψ) (ur Ψ)
                                (GR-inst (ptr LP.⌈ L.primDom p ⌉) g) gD (pr π) (pr π) _ (ih r r′ g) e₀))
                       (prim-R σ′ p))
            e)
    where
      gC = subst (λ Z → GR Z _) (LP.⌈⌉-⟪⟫ (L.primCod p) σ) (GR-inst (ptr LP.⌈ L.primCod p ⌉) g)
      gD = subst (λ Z → GR Z _) (sym (LP.⌈⌉-⟪⟫ (L.primDom p) σ)) (gDom σ′ p)

  coerce : ∀ {m n} {Δ : LP.KCtx m} {Γ : PT.PCtx m n} {Ψ π A B t} (p : A PT.<:ₚ B)
           (d : PT._⊩_⊢[_]_∷_!_ Δ Γ Ψ t A π) → Fund ρ ρ′ d → Fund ρ ρ′ (PT.⊢coerce p d)
  coerce {π = π} p d ih r r′ g e = fmap-R (pr π) (ih r r′ g e) (conv-R p g)

  -- (a pure sum value, read as a step of the loop)
  private
    toSum : ∀ {B B′ A A′} {gB : GR B B′} {gA : GR A A′} {v v′}
          → ValR (g-+ gB gA) v v′ → SumR (ValR gB) (ValR gA) v v′
    toSum {v = inj₁ _} {inj₁ _} r = left r
    toSum {v = inj₂ _} {inj₂ _} r = right r
    toSum {v = inj₁ _} {inj₂ _} ()
    toSum {v = inj₂ _} {inj₁ _} ()

  iter : ∀ {m n} {Δ : LP.KCtx m} {Γ : PT.PCtx m n} {Ψf Ψs π₁ π₂ A B f x}
         (df : PT._⊩_⊢[_]_∷_!_ Δ Γ Ψf f (A LP.⇒[ LG.mk-kind LG.Many LG.act ] (B LP.+ A)) π₁)
         (dx : PT._⊩_⊢[_]_∷_!_ Δ Γ Ψs x A π₂) → Fund ρ ρ′ df → Fund ρ ρ′ dx → Fund ρ ρ′ (PT.⊢iter df dx)
  iter {Γ = Γ} {Ψf} {Ψs} {π₁} {π₂} {A} {B} df dx ihf ihx r r′ g e =
    S-at ρ ρ′ g (eqᵘ-many Ψf Ψs) refl (eqᵍ-3 π₁ π₂ LG.eff) (S⊢.⊢iter (trD df) (trD dx)) (crΓ Γ)
         (ur-+ (ur-* qr-many (ur Ψf)) (ur Ψs)) (ur _) gB gB (pr-· (pr π₁) (pr-· (pr π₂) pr-eff)) (pr _) _
         (λ e₀ → bindᵍ-R (pr π₁) (pr-· (pr π₂) pr-eff) (ihf r r′ g (restrict-R g (crΓ Γ) _ _ _ (ur Ψf) e₀))
                   (λ rf → bindᵍ-R (pr π₂) pr-eff (ihx r r′ g (restrict-R g (crΓ Γ) _ _ _ (ur Ψs) e₀))
                             (λ ra → loop-R (λ rx → TR-map toSum (rf rx)) ra)))
         e
    where gB = GR-inst (ptr B) g

------------------------------------------------------------------------
-- Definitions and declarations: the definitions environments related
------------------------------------------------------------------------

-- The definitions mean related values at related instances.
DefsR : GM.DefSem → SM.DefSem → Set
DefsR ρ ρ′ = ∀ d τ r τ′ r′ (i : InstD S d τ τ′) → ValR (GR-def S d i) (GM.DefSem.defs ρ d τ r) (SM.DefSem.defs ρ′ d τ′ r′)

-- The signature's declarations mean related values.
SigR : GM.DefSem → SM.DefSem → Set
SigR ρ ρ′ = ∀ {m} (σ′ : ST.TySub m 0) {c A} (k : LW.IsConcrete A) (h : LH.HonestFFI A) (rf : LW.RigidFree A)
            (mem : (showCanonical c , A) ∈ Fs) (gs : GR A (⌜ declS A ⌝ᵈ ST.⟨ σ′ ⟩))
          → ValR gs (LOps.sigOpRefᵛ fmt Fs (GM.DefSem.impl ρ) c k mem) (SM.sigopᵛ σ′ c (declS A) (sigop-S mem) (SM.DefSem.model ρ′))

-- (a Spec value moved along an equation of its type)
ValR-substʳ : ∀ {X A′ A″} (e : A′ ≡ A″) (g′ : GR X A′) (g″ : GR X A″) {x y}
            → ValR g′ x y → ValR g″ x (subst SD.⟦_⟧ᵛ e y)
ValR-substʳ refl g′ g″ r = subst (λ g → ValR g _ _) (GR-unique g′ g″) r

module _ (ρ : GM.DefSem) (ρ′ : SM.DefSem) (defsR : DefsR ρ ρ′) (sigR : SigR ρ ρ′) where

  ref : ∀ {m n} {Δ : LP.KCtx m} {Γ : PT.PCtx m n} d τ rs → Fund ρ ρ′ (PT.⊢ref {Δ = Δ} {Γ = Γ} d τ rs)
  ref {n = n} {Δ} {Γ} d τ rs {σ} {σ′} r r′ g e =
    L-at ρ ρ′ (sym (LP.⟨⟩-⟪⟫ (LP.Schema.type (S LP.!! d)) τ σ))
         (GT.⊢ref {Γ = Γ PT.⟪ σ ⟫ᶜ} d (λ i → τ i LP.⟪ σ ⟫) (λ i e₁ → LP.base-⟪⟫ r (rs i e₁))) pr-pure gX
         (GR-inst (ptr (LP.Schema.type (S LP.!! d) LP.⟨ τ ⟩)) g)
      (S-at ρ ρ′ g {Γ = Γ} (sym (uS-zero {n})) (sym (ref-ty S d τ)) refl
            (S⊢.⊢ref {Δ = kindsS Δ} {Γ = pctxS Γ} d (castSub S d (λ i → ptyS (τ i))) (ref-resp S d τ rs))
            (crΓ Γ) ur-zero (ur _) gI gX pr-pure pr-pure _
            (λ _ → ValR-substʳ (sym (ST.⟨⟩-∘ (SC.Schema.type (S′ SC.!! d)) (castSub S d (λ i → ptyS (τ i))) σ′))
                                (GR-def S d (inst-ref S d τ g)) gI
                     (defsR d _ _ _ _ (inst-ref S d τ g)))
            e)
    where
      gI = subst (λ Z → GR _ Z) (sym (ST.⟨⟩-∘ (SC.Schema.type (S′ SC.!! d)) (castSub S d (λ i → ptyS (τ i))) σ′))
                 (GR-def S d (inst-ref S d τ g))
      gX = subst (λ Z → GR Z _) (LP.⟨⟩-⟪⟫ (LP.Schema.type (S LP.!! d)) τ σ) (GR-inst (ptr (LP.Schema.type (S LP.!! d) LP.⟨ τ ⟩)) g)

  sigop : ∀ {m n} {Δ : LP.KCtx m} {Γ : PT.PCtx m n} {A} c k h rf mem
        → Fund ρ ρ′ (PT.⊢sigop {Δ = Δ} {Γ = Γ} {A = A} c k h rf mem)
  sigop {n = n} {Δ} {Γ} {A} c k h rf mem {σ} {σ′} r r′ g e =
    L-at ρ ρ′ (sym (LP.⌈⌉-⟪⟫ A σ)) (GT.⊢sigop {Γ = Γ PT.⟪ σ ⟫ᶜ} c k h rf mem) pr-pure gX (GR-inst (ptr LP.⌈ A ⌉) g)
      (S-at ρ ρ′ g {Γ = Γ} (sym (uS-zero {n})) (declS-S k h rf) refl
            (S⊢.⊢sigop {Δ = kindsS Δ} {Γ = pctxS Γ} (sigop-S mem))
            (crΓ Γ) ur-zero (ur _) gs gX pr-pure pr-pure _ (λ _ → sigR σ′ k h rf mem gs) e)
    where
      gX = subst (λ Z → GR Z _) (LP.⌈⌉-⟪⟫ A σ) (GR-inst (ptr LP.⌈ A ⌉) g)
      gs = subst (λ Z → GR A (Z ST.⟨ σ′ ⟩)) (sym (declS-S k h rf)) gX

------------------------------------------------------------------------
-- Recursive types
------------------------------------------------------------------------

module _ (ρ : GM.DefSem) (ρ′ : SM.DefSem) where

  roll : ∀ {m n} {Δ : LP.KCtx m} {Γ : PT.PCtx m n} {Ψ π F t} (wf : LP.WFFun Δ F)
         (d : PT._⊩_⊢[_]_∷_!_ Δ Γ Ψ t (LP.⟦ F ⟧F (LP.μ-type F)) π) → Fund ρ ρ′ d → Fund ρ ρ′ (PT.⊢roll wf d)
  roll {Γ = Γ} {Ψ} {π} {F} wf d ih {σ} {σ′} r r′ g e =
    fmap-R (pr π)
      (L-at ρ ρ′ (LP.⟦⟧F-⟪⟫ F (LP.μ-type F) σ) (PT.instantiate σ r d) (pr π) gIn (GR-⟦⟧ g (pfr F) gμ)
         (S-at ρ ρ′ g refl (ptyS-⟦⟧ F (LP.μ-type F)) refl (trD d) (crΓ Γ) (ur Ψ) (ur Ψ)
               (GR-inst (ptr (LP.⟦ F ⟧F (LP.μ-type F))) g) gIn (pr π) (pr π) _ (ih r r′ g) e))
      (λ rx → inR (in-R (GF-inst (pfr F) g) (cf-R g (pfr F) (LP.wf-⟪⟫ r wf) gμ rx)))
    where
      gμ = GR-inst (ptr (LP.μ-type F)) g
      gIn = subst (λ Z → GR Z _) (sym (LP.⟦⟧F-⟪⟫ F (LP.μ-type F) σ)) (GR-⟦⟧ g (pfr F) gμ)

  private
    -- one layer of a stream, read on both sides
    outν-R : ∀ {m} {F : LP.Fun m} {σ σ′} (g : InstG σ σ′) (wf : LW.WellFormedF (F LP.⟪ σ ⟫F)) φ {v w}
           → ValR (GR-inst (ptr (LP.ν-type F φ)) g) v w
           → MR (pr-fin φ) (ValR (GR-⟦⟧ g (pfr F) (GR-inst (ptr (LP.ν-type F φ)) g)))
                (LOps.out-semᵛ φ wf v) (SE.fmap (SG.fin (φS φ)) (SD.fromL σ′ (pfunS F) (ST.ν (pfunS F) (φS φ))) (SE.νM.outν w))
    outν-R {F = F} g wf LG.pure rv = cf⁻¹-R g (pfr F) wf _ (out-R (GF-inst (pfr F) g) wf (forceᵖR rv))
    outν-R {F = F} g wf LG.act  rv =
      bindT-R (forceᵈR rv) (λ rl → ret (cf⁻¹-R g (pfr F) wf _ (out-R (GF-inst (pfr F) g) wf rl)))

  out : ∀ {m n} {Δ : LP.KCtx m} {Γ : PT.PCtx m n} {Ψ φ π₁ F t} (wf : LP.WFFun Δ F)
        (d : PT._⊩_⊢[_]_∷_!_ Δ Γ Ψ t (LP.ν-type F φ) π₁) → Fund ρ ρ′ d → Fund ρ ρ′ (PT.⊢out wf d)
  out {Γ = Γ} {Ψ} {φ} {π₁} {F} wf d ih {σ} {σ′} r r′ g e =
    L-at ρ ρ′ (sym (LP.⟦⟧F-⟪⟫ F (LP.ν-type F φ) σ)) (GT.⊢out (LP.wf-⟪⟫ r wf) (PT.instantiate σ r d)) (pr _) gX gY
      (S-at ρ ρ′ g refl (sym (ptyS-⟦⟧ F (LP.ν-type F φ))) (eqᵍ-out π₁ φ) (S⊢.⊢out (wfS wf) (trD d)) (crΓ Γ) (ur Ψ) (ur Ψ)
            (GR-⟦⟧ g (pfr F) (GR-inst (ptr (LP.ν-type F φ)) g)) gX (pr-· (pr π₁) (pr-fin φ)) (pr _) _
            (λ e₀ → bindᵍ-R (pr π₁) (pr-fin φ) (ih r r′ g e₀) (outν-R g (LP.wf-⟪⟫ r wf) φ))
            e)
    where
      gY = GR-inst (ptr (LP.⟦ F ⟧F (LP.ν-type F φ))) g
      gX = subst (λ Z → GR Z _) (LP.⟦⟧F-⟪⟫ F (LP.ν-type F φ) σ) gY

  -- (the compiler's typing moved along an equation inside its type)
  L-at′ : ∀ {n} {Γ : LC.Ctx n} {Ψ t X Y π π′ B′} (h : LT.Type → LT.Type) (e : X ≡ Y)
          (d : Γ GT.⊢[ Ψ ] t ∷ h X ! π) (p : PR π π′) (gX : GR (h X) B′) (gY : GR (h Y) B′) {γ y}
        → MR p (ValR gX) (GM.⟦ d ⟧ fmt ρ γ) y
        → MR p (ValR gY) (GM.⟦ subst (λ Z → Γ GT.⊢[ Ψ ] t ∷ h Z ! π) e d ⟧ fmt ρ γ) y
  L-at′ h refl d p gX gY r = subst (λ x → MR p (ValR x) (GM.⟦ d ⟧ fmt ρ _) _) (GR-unique gX gY) r

  fold : ∀ {m n} {Δ : LP.KCtx m} {Γ : PT.PCtx m n} {Ψa Ψt π π₁ π₂ F A alg t}
         (u : LG.pure LS.⊑π π) (wf : LP.WFFun Δ F)
         (da : PT._⊩_⊢[_]_∷_!_ Δ Γ Ψa alg (LP.⟦ F ⟧F A LP.⇒[ LG.mk-kind LG.Many π ] A) π₁)
         (dt : PT._⊩_⊢[_]_∷_!_ Δ Γ Ψt t (LP.μ-type F) π₂)
       → Fund ρ ρ′ da → Fund ρ ρ′ dt → Fund ρ ρ′ (PT.⊢fold u wf da dt)
  fold {Γ = Γ} {Ψa} {Ψt} {π} {π₁} {π₂} {F} {A} u wf da dt iha iht {σ} {σ′} r r′ g e =
    S-at ρ ρ′ g (eqᵘ-many Ψa Ψt) refl (eqᵍ-3 π₁ π₂ π)
         (S⊢.⊢fold (wfS wf) (atS refl (cong (λ X → X ST.⇒[ _ ] _) (ptyS-⟦⟧ F A)) refl (trD da)) (trD dt)) (crΓ Γ)
         (ur-+ (ur-* qr-many (ur Ψa)) (ur Ψt)) (ur _) gA gA (pr-· (pr π₁) (pr-· (pr π₂) (pr π))) (pr _) _
         (λ e₀ → bindᵍ-R (pr π₁) (pr-· (pr π₂) (pr π))
                   (L-at′ (λ X → X LT.⇒[ LG.mk-kind LG.Many π ] (A LP.⟪ σ ⟫)) (LP.⟦⟧F-⟪⟫ F A σ)
                          (PT.instantiate σ r da) (pr π₁) gAlgX gAlg
                          (S-at ρ ρ′ g refl (cong (λ X → X ST.⇒[ _ ] _) (ptyS-⟦⟧ F A)) refl (trD da) (crΓ Γ) (ur Ψa) (ur Ψa)
                                (GR-inst (ptr (LP.⟦ F ⟧F A LP.⇒[ LG.mk-kind LG.Many π ] A)) g) gAlgX (pr π₁) (pr π₁) _
                                (iha r r′ g) (restrict-R g (crΓ Γ) _ _ _ (ur Ψa) e₀)))
                   (λ ralg → bindᵍ-R (pr π₂) (pr π) (iht r r′ g (restrict-R g (crΓ Γ) _ _ _ (ur Ψt) e₀))
                               (λ rv → Fold.fold-R Σ g F A (LP.wf-⟪⟫ r wf) u (λ {x} {y} r₀ → ralg r₀) rv)))
         e
    where
      gA    = GR-inst (ptr A) g
      gAlg  = g-⇒ {q = LG.Many} {π = π} (GR-⟦⟧ g (pfr F) gA) gA
      gAlgX = subst (λ Z → GR (Z LT.⇒[ LG.mk-kind LG.Many π ] (A LP.⟪ σ ⟫)) _) (sym (LP.⟦⟧F-⟪⟫ F A σ)) gAlg

  unfold : ∀ {m n} {Δ : LP.KCtx m} {Γ : PT.PCtx m n} {Ψc Ψs φ π₁ π₂ F A c x} (wf : LP.WFFun Δ F)
           (dc : PT._⊩_⊢[_]_∷_!_ Δ Γ Ψc c (A LP.⇒[ LG.mk-kind LG.Many (LG.fin φ) ] LP.⟦ F ⟧F A) π₁)
           (dx : PT._⊩_⊢[_]_∷_!_ Δ Γ Ψs x A π₂) → Fund ρ ρ′ dc → Fund ρ ρ′ dx → Fund ρ ρ′ (PT.⊢unfold wf dc dx)
  unfold {Γ = Γ} {Ψc} {Ψs} {LG.pure} {π₁} {π₂} {F} {A} wf dc dx ihc ihx {σ} {σ′} r r′ g e =
    S-at ρ ρ′ g (eqᵘ-many Ψc Ψs) refl (eqᵍ-· π₁ π₂)
         (S⊢.⊢unfold (wfS wf) (atS refl (arr-fin LG.pure (ptyS-⟦⟧ F A)) refl (trD dc)) (trD dx)) (crΓ Γ)
         (ur-+ (ur-* qr-many (ur Ψc)) (ur Ψs)) (ur _) gν gν (pr-· (pr π₁) (pr π₂)) (pr _) _
         (λ e₀ → bindᵍ-R (pr π₁) (pr π₂)
                   (L-at′ (λ X → A LP.⟪ σ ⟫ LT.⇒[ LG.mk-kind LG.Many LG.pure ] X) (LP.⟦⟧F-⟪⟫ F A σ)
                          (PT.instantiate σ r dc) (pr π₁) gCX gC
                          (S-at ρ ρ′ g refl (arr-fin LG.pure (ptyS-⟦⟧ F A)) refl (trD dc) (crΓ Γ) (ur Ψc) (ur Ψc)
                                (GR-inst (ptr (A LP.⇒[ LG.mk-kind LG.Many LG.pure ] LP.⟦ F ⟧F A)) g) gCX (pr π₁) (pr π₁) _
                                (ihc r r′ g) (restrict-R g (crΓ Γ) _ _ _ (ur Ψc) e₀)))
                   (λ rc → fmap-R (pr π₂) (ihx r r′ g (restrict-R g (crΓ Γ) _ _ _ (ur Ψs) e₀))
                             (λ ra → Unfold.anaP-R Σ (GF-inst (pfr F) g)
                                        (λ rx → in-R (GF-inst (pfr F) g) (cf-R g (pfr F) (LP.wf-⟪⟫ r wf) gA (rc rx))) ra)))
         e
    where
      gA  = GR-inst (ptr A) g
      gν  = GR-inst (ptr (LP.ν-type F LG.pure)) g
      gC  = g-⇒ {q = LG.Many} {π = LG.pure} gA (GR-⟦⟧ g (pfr F) gA)
      gCX = subst (λ Z → GR (A LP.⟪ σ ⟫ LT.⇒[ LG.mk-kind LG.Many LG.pure ] Z) _) (sym (LP.⟦⟧F-⟪⟫ F A σ)) gC
  unfold {Γ = Γ} {Ψc} {Ψs} {LG.act} {π₁} {π₂} {F} {A} wf dc dx ihc ihx {σ} {σ′} r r′ g e =
    S-at ρ ρ′ g (eqᵘ-many Ψc Ψs) refl (eqᵍ-· π₁ π₂)
         (S⊢.⊢unfold (wfS wf) (atS refl (arr-fin LG.act (ptyS-⟦⟧ F A)) refl (trD dc)) (trD dx)) (crΓ Γ)
         (ur-+ (ur-* qr-many (ur Ψc)) (ur Ψs)) (ur _) gν gν (pr-· (pr π₁) (pr π₂)) (pr _) _
         (λ e₀ → bindᵍ-R (pr π₁) (pr π₂)
                   (L-at′ (λ X → A LP.⟪ σ ⟫ LT.⇒[ LG.mk-kind LG.Many LG.act ] X) (LP.⟦⟧F-⟪⟫ F A σ)
                          (PT.instantiate σ r dc) (pr π₁) gCX gC
                          (S-at ρ ρ′ g refl (arr-fin LG.act (ptyS-⟦⟧ F A)) refl (trD dc) (crΓ Γ) (ur Ψc) (ur Ψc)
                                (GR-inst (ptr (A LP.⇒[ LG.mk-kind LG.Many LG.act ] LP.⟦ F ⟧F A)) g) gCX (pr π₁) (pr π₁) _
                                (ihc r r′ g) (restrict-R g (crΓ Γ) _ _ _ (ur Ψc) e₀)))
                   (λ rc → fmap-R (pr π₂) (ihx r r′ g (restrict-R g (crΓ Γ) _ _ _ (ur Ψs) e₀))
                             (λ ra → Unfold.anaA-R Σ (GF-inst (pfr F) g)
                                        (λ rx → fmap-R pr-act (rc rx)
                                                  (λ rl → in-R (GF-inst (pfr F) g) (cf-R g (pfr F) (LP.wf-⟪⟫ r wf) gA rl))) ra)))
         e
    where
      gA  = GR-inst (ptr A) g
      gν  = GR-inst (ptr (LP.ν-type F LG.act)) g
      gC  = g-⇒ {q = LG.Many} {π = LG.act} gA (GR-⟦⟧ g (pfr F) gA)
      gCX = subst (λ Z → GR (A LP.⟪ σ ⟫ LT.⇒[ LG.mk-kind LG.Many LG.act ] Z) _) (sym (LP.⟦⟧F-⟪⟫ F A σ)) gC

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
    ; c-lit-int   = lit-int ρ ρ′
    ; c-lit-float = lit-float ρ ρ′
    ; c-prim      = prim ρ ρ′
    ; c-sigop     = sigop ρ ρ′ defsR sigR
    ; c-ref       = ref ρ ρ′ defsR sigR
    }

  -- A compiler core derivation and its Spec translation mean related computations.
  fundamental : ∀ {m n} {Δ : LP.KCtx m} {Γ : PT.PCtx m n} {Ψ t A π} (D : PT._⊩_⊢[_]_∷_!_ Δ Γ Ψ t A π) → Fund ρ ρ′ D
  fundamental = fund ρ ρ′ allCases
