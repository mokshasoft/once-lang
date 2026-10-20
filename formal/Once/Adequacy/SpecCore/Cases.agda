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
open import Once.Adequacy.SpecCore.Poly using (declS; declS-S)

module Once.Adequacy.SpecCore.Cases
  {Fs : ISig} {s : ℕ} (S : LP.Sig Fs s) (Σ : Signature)
  (sigop-S : ∀ {c A} → (showCanonical c , A) ∈ Fs → (c ∶ declS A) ∈ Σ)
  (fmt : TargetNum) where

open import Data.Unit using (tt)
open import Data.Fin using (Fin; zero; suc)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)

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
open import Once.Adequacy.SpecCore.Schema using (kindsS; defsS; castSub; ptyS)
open import Once.Adequacy.SpecCore.Context using (uS-zero)
open import Once.Adequacy.SpecCore.Prim S using (primS; primDom-S; primCod-S)
open import Once.Adequacy.SpecCore.Poly using (module Translate)
open Translate S Σ sigop-S
import Once.Spec.Core.Typing Σ S′ as S⊢
import Once.Spec.Core.Meaning Σ fmt S′ as SM
import Once.Spec.Domain Σ as SD
open import Once.Adequacy.SpecCore.Index
open import Once.Adequacy.SpecCore.Value Σ
open import Once.Adequacy.SpecCore.Monad Σ
open import Once.Adequacy.SpecCore.Env S Σ fmt
open import Once.Adequacy.SpecCore.Fundamental S Σ sigop-S fmt
open import Once.Adequacy.SpecCore.Conv S Σ using (conv-R)

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

-- An instance of the `d`-th definition, on both sides.
InstD : ∀ {s₀} (S₀ : LP.Sig Fs s₀) (d : Fin s₀) → LP.GSub (LP.Schema.arity (S₀ LP.!! d))
      → ST.TySub (SC.Schema.arity (defsS S₀ SC.!! d)) 0 → Set
InstD (S₀ LP.▷ sc) zero    τ τ′ = InstG τ τ′
InstD (S₀ LP.▷ sc) (suc d) τ τ′ = InstD S₀ d τ τ′

GR-def : ∀ {s₀} (S₀ : LP.Sig Fs s₀) (d : Fin s₀) {τ τ′} → InstD S₀ d τ τ′
       → GR (LP.Schema.type (S₀ LP.!! d) LP.⟪ τ ⟫) (SC.Schema.type (defsS S₀ SC.!! d) ST.⟨ τ′ ⟩)
GR-def (S₀ LP.▷ sc) zero    i = GR-inst (ptr (LP.Schema.type sc)) i
GR-def (S₀ LP.▷ sc) (suc d) i = GR-def S₀ d i

-- A reference's instance, instantiated on both sides.
inst-ref : ∀ {s₀ m} (S₀ : LP.Sig Fs s₀) (d : Fin s₀) (τ : LP.Sub (LP.Schema.arity (S₀ LP.!! d)) m)
           {σ σ′} → InstG σ σ′
         → InstD S₀ d (λ i → τ i LP.⟪ σ ⟫) (λ i → castSub S₀ d (λ j → ptyS (τ j)) i ST.⟨ σ′ ⟩)
inst-ref (S₀ LP.▷ sc) zero    τ g i = GR-inst (ptr (τ i)) g
inst-ref (S₀ LP.▷ sc) (suc d) τ g   = inst-ref S₀ d τ g

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
