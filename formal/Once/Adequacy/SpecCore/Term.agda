-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.SpecCore.Term — the compiler's core terms as the Spec's, and
-- their typing (plan 0.121, the core bridge).
--
-- The two cores have the same formers (the Spec's was transcribed from the
-- compiler's). `TmR Δ t t′`: the compiler's term `t` is the Spec's `t′`,
-- former by former, its annotations related by `TyR`. A typing of `t` gives
-- one of `t′` at the related type, usage and grade (`⊢-S`).
--
-- The signature Σ is a parameter: which Spec declaration a compiler FFI
-- declaration is (`sigop-S`) is the program's business, not the core's.
------------------------------------------------------------------------

open import Data.Nat using (ℕ)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Product using (_,_)
open import Once.Lang.Contract using (ISig)
open import Once.Lang.Name using (showCanonical)
import Once.Lang.Core.PolyTy as LP
import Once.Spec.Type as ST
open import Once.Spec.Signature using (Signature; _∶_; ⌜_⌝ᵈ)
open import Once.Adequacy.SpecCore.Type using (TyR)

module Once.Adequacy.SpecCore.Term
  {Fs : ISig} {s : ℕ} (S : LP.Sig Fs s) (Σ : Signature)
  -- an FFI declaration of the compiler's is the Spec's declaration at the
  -- related type
  (sigop-S : ∀ {m} {Δ : ST.KCtx m} {c A t} → (showCanonical c , A) ∈ Fs → TyR Δ A (⌜_⌝ᵈ {m} t) → (c ∶ t) ∈ Σ)
  where

open import Data.Fin using (Fin; zero; suc)
open import Data.Product using (Σ-syntax; _×_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Data.Bool using (true)

import Once.Lang.Type as LT
import Once.Lang.Type.Grade as LG
import Once.Lang.Type.Sub as LS
import Once.Lang.Type.WellFormed as LW
import Once.Spec.Grade as SG
import Once.Lang.Context as LC
import Once.Spec.Context as SCx
import Once.Spec.Core.Syntax as SC
import Once.Lang.Core.Syntax S as L
import Once.Lang.Core.Typing S as L⊢
open import Once.Adequacy.SpecGrammar.Conv using (qS; πS; φS; kS)
open import Once.Adequacy.SpecCore.Type
open import Once.Adequacy.SpecCore.Context
open import Once.Adequacy.SpecCore.Schema

S′ : SC.Defs s
S′ = defsS S

import Once.Spec.Core.Typing Σ S′ as S⊢
open S⊢ using (_⊩_⊢[_]_∷_!_)

------------------------------------------------------------------------
-- Literals and primitives
------------------------------------------------------------------------

open import Once.Adequacy.SpecCore.Prim S using (litS; primS)

module _ {m} {Δ : ST.KCtx m} where

  private
    ii : TyR Δ (LT.Int LT.* LT.Int) (ST.Int ST.* ST.Int)
    ii = r-* r-int r-int
    ff : TyR Δ (LT.Float LT.* LT.Float) (ST.Float ST.* ST.Float)
    ff = r-* r-float r-float
    bool : TyR Δ (LT.Unit LT.+ LT.Unit) (ST.Unit ST.+ ST.Unit)
    bool = r-+ r-unit r-unit

  primDom-R : ∀ p → TyR Δ (L.primDom p) (SC.primDom (primS p))
  primDom-R L.p-add  = ii
  primDom-R L.p-sub  = ii
  primDom-R L.p-mul  = ii
  primDom-R L.p-div  = ii
  primDom-R L.p-mod  = ii
  primDom-R L.p-neg  = r-int
  primDom-R L.p-lt   = ii
  primDom-R L.p-le   = ii
  primDom-R L.p-gt   = ii
  primDom-R L.p-ge   = ii
  primDom-R L.p-eq   = ii
  primDom-R L.p-ne   = ii
  primDom-R L.p-fadd = ff
  primDom-R L.p-fsub = ff
  primDom-R L.p-fmul = ff
  primDom-R L.p-fdiv = ff
  primDom-R L.p-i2f  = r-int

  primCod-R : ∀ p → TyR Δ (L.primCod p) (SC.primCod (primS p))
  primCod-R L.p-add  = r-int
  primCod-R L.p-sub  = r-int
  primCod-R L.p-mul  = r-int
  primCod-R L.p-div  = r-int
  primCod-R L.p-mod  = r-int
  primCod-R L.p-neg  = r-int
  primCod-R L.p-lt   = bool
  primCod-R L.p-le   = bool
  primCod-R L.p-gt   = bool
  primCod-R L.p-ge   = bool
  primCod-R L.p-eq   = bool
  primCod-R L.p-ne   = bool
  primCod-R L.p-fadd = r-float
  primCod-R L.p-fsub = r-float
  primCod-R L.p-fmul = r-float
  primCod-R L.p-fdiv = r-float
  primCod-R L.p-i2f  = r-float

------------------------------------------------------------------------
-- References to definitions
------------------------------------------------------------------------

module _ {m} {Δ : ST.KCtx m} where

  ref-type : ∀ {s′} (S₀ : LP.Sig Fs s′) (d : Fin s′) {τ τ′}
           → Clean (LP.Schema.type (S₀ LP.!! d)) → InstR {Δ = Δ} τ τ′
           → TyR Δ (LP.Schema.type (S₀ LP.!! d) LP.⟪ τ ⟫) (SC.Schema.type (defsS S₀ SC.!! d) ST.⟨ castSub S₀ d τ′ ⟩)
  ref-type (S₀ LP.▷ sc) zero    c r = TyR-inst c r
  ref-type (S₀ LP.▷ sc) (suc d) c r = ref-type S₀ d c r

  ref-respects : ∀ {s′} (S₀ : LP.Sig Fs s′) (d : Fin s′) {τ τ′}
               → LP.Respects (LP.Schema.kinds (S₀ LP.!! d)) τ → InstR {Δ = Δ} τ τ′
               → ST.Respects (SC.Schema.kinds (defsS S₀ SC.!! d)) Δ (castSub S₀ d τ′)
  ref-respects (S₀ LP.▷ sc) zero    rs r = respects-S rs r
  ref-respects (S₀ LP.▷ sc) (suc d) rs r = ref-respects S₀ d rs r

------------------------------------------------------------------------
-- Terms
------------------------------------------------------------------------

data TmR {m} (Δ : ST.KCtx m) : ∀ {n} → L.Tm n → SC.Tm S′ m n → Set where
  r-var    : ∀ {n} (i : Fin n) → TmR Δ (L.var i) (SC.var i)
  r-lam    : ∀ {n A A′ q π} {t : L.Tm (ℕ.suc n)} {t′}
           → TyR Δ A A′ → TmR Δ t t′ → TmR Δ (L.lam A q π t) (SC.lam A′ (qS q) (πS π) t′)
  r-app    : ∀ {n} {f x : L.Tm n} {f′ x′} → TmR Δ f f′ → TmR Δ x x′ → TmR Δ (L.app f x) (SC.app f′ x′)
  r-let    : ∀ {n q} {e : L.Tm n} {b e′ b′} → TmR Δ e e′ → TmR Δ b b′ → TmR Δ (L.let′ q e b) (SC.let′ (qS q) e′ b′)
  r-unit   : ∀ {n} → TmR Δ (L.unit {n}) SC.unit
  r-pair   : ∀ {n} {a b : L.Tm n} {a′ b′} → TmR Δ a a′ → TmR Δ b b′ → TmR Δ (L.pair a b) (SC.pair a′ b′)
  r-fst    : ∀ {n} {p : L.Tm n} {p′} → TmR Δ p p′ → TmR Δ (L.fst p) (SC.fst p′)
  r-snd    : ∀ {n} {p : L.Tm n} {p′} → TmR Δ p p′ → TmR Δ (L.snd p) (SC.snd p′)
  r-inl    : ∀ {n B B′} {a : L.Tm n} {a′} → TyR Δ B B′ → TmR Δ a a′ → TmR Δ (L.inl B a) (SC.inl B′ a′)
  r-inr    : ∀ {n A A′} {b : L.Tm n} {b′} → TyR Δ A A′ → TmR Δ b b′ → TmR Δ (L.inr A b) (SC.inr A′ b′)
  r-case   : ∀ {n qℓ qr} {e : L.Tm n} {l r e′ l′ r′} → TmR Δ e e′ → TmR Δ l l′ → TmR Δ r r′
           → TmR Δ (L.case qℓ qr e l r) (SC.case (qS qℓ) (qS qr) e′ l′ r′)
  r-absurd : ∀ {n A A′} {e : L.Tm n} {e′} → TyR Δ A A′ → TmR Δ e e′ → TmR Δ (L.absurd A e) (SC.absurd A′ e′)
  r-roll   : ∀ {n F F′} {t : L.Tm n} {t′} → FunR Δ F F′ → TmR Δ t t′ → TmR Δ (L.roll F t) (SC.roll F′ t′)
  r-fold   : ∀ {n F F′} {a t : L.Tm n} {a′ t′} → FunR Δ F F′ → TmR Δ a a′ → TmR Δ t t′
           → TmR Δ (L.fold F a t) (SC.fold F′ a′ t′)
  r-unfold : ∀ {n F F′} {c t : L.Tm n} {c′ t′} → FunR Δ F F′ → TmR Δ c c′ → TmR Δ t t′
           → TmR Δ (L.unfold F c t) (SC.unfold F′ c′ t′)
  r-out    : ∀ {n} {t : L.Tm n} {t′} → TmR Δ t t′ → TmR Δ (L.out t) (SC.out t′)
  r-iter   : ∀ {n} {f t : L.Tm n} {f′ t′} → TmR Δ f f′ → TmR Δ t t′ → TmR Δ (L.iter f t) (SC.iter f′ t′)
  r-coerce : ∀ {n A A′ B B′} {t : L.Tm n} {t′} → TyR Δ A A′ → TyR Δ B B′ → TmR Δ t t′
           → TmR Δ (L.coerce A B t) (SC.coerce A′ B′ t′)
  r-lit    : ∀ {n} l → TmR Δ (L.lit {n} l) (SC.lit (litS l))
  r-prim   : ∀ {n} p {t : L.Tm n} {t′} → TmR Δ t t′ → TmR Δ (L.prim p t) (SC.prim (primS p) t′)
  r-sigop  : ∀ {n c A t} → TyR Δ A (⌜_⌝ᵈ {m} t) → TmR Δ (L.sigop {n} c A) (SC.sigop c t)
  r-ref    : ∀ {n} (d : Fin s) {τ τ′} → InstR {Δ = Δ} τ τ′ → TmR Δ (L.ref {n} d τ) (SC.ref d (castSub S d τ′))

------------------------------------------------------------------------
-- Typing
------------------------------------------------------------------------

module _ {m} {Δ : ST.KCtx m} where

  private
    at : ∀ {n} {Γ : SCx.Ctx m n} {Ψ Ψ′ t A π π′} → Ψ ≡ Ψ′ → π ≡ π′
       → Δ ⊩ Γ ⊢[ Ψ ] t ∷ A ! π → Δ ⊩ Γ ⊢[ Ψ′ ] t ∷ A ! π′
    at refl refl d = d

    atT : ∀ {n} {Γ : SCx.Ctx m n} {Ψ t A A′ π} → A ≡ A′ → Δ ⊩ Γ ⊢[ Ψ ] t ∷ A ! π → Δ ⊩ Γ ⊢[ Ψ ] t ∷ A′ ! π
    atT refl d = d

    usage-app : ∀ {n} (Ψ₁ : LC.Usage n) q Ψ₂ → uS Ψ₁ SCx.+ᵘ qS q SCx.*ᵘ uS Ψ₂ ≡ uS (Ψ₁ LC.+ᵘ q LC.*ᵘ Ψ₂)
    usage-app Ψ₁ q Ψ₂ = sym (trans (uS-+ Ψ₁ (q LC.*ᵘ Ψ₂)) (cong (uS Ψ₁ SCx.+ᵘ_) (uS-* q Ψ₂)))

    usage-many : ∀ {n} (Ψ₁ Ψ₂ : LC.Usage n) → SG.Many SCx.*ᵘ uS Ψ₁ SCx.+ᵘ uS Ψ₂ ≡ uS (LG.Many LC.*ᵘ Ψ₁ LC.+ᵘ Ψ₂)
    usage-many Ψ₁ Ψ₂ = sym (trans (uS-+ (LG.Many LC.*ᵘ Ψ₁) Ψ₂) (cong (SCx._+ᵘ uS Ψ₂) (uS-* LG.Many Ψ₁)))

    grade2 : ∀ π₁ π₂ → πS π₁ SG.·p πS π₂ ≡ πS (π₁ LG.·p π₂)
    grade2 π₁ π₂ = sym (·p-S π₁ π₂)

    grade3 : ∀ π₁ π₂ π → πS π₁ SG.·p πS π₂ SG.·p πS π ≡ πS (π₁ LG.·p π₂ LG.·p π)
    grade3 π₁ π₂ π = sym (trans (·p-S π₁ _) (cong (πS π₁ SG.·p_) (·p-S π₂ π)))

  -- A typing of the compiler's term, as the Spec's at a related type.
  Typed : ∀ {n} → SCx.Ctx m n → LC.Usage n → SC.Tm S′ m n → LT.Type → LG.Purity → Set
  Typed Γ′ Ψ t′ A π = Σ[ A′ ∈ ST.Ty m ] TyR Δ A A′ × (Δ ⊩ Γ′ ⊢[ uS Ψ ] t′ ∷ A′ ! πS π)

  -- (at a type already related)
  typed-at : ∀ {n} {Γ′ : SCx.Ctx m n} {Ψ t′ A A′ π} → TyR Δ A A′ → Typed Γ′ Ψ t′ A π
           → Δ ⊩ Γ′ ⊢[ uS Ψ ] t′ ∷ A′ ! πS π
  typed-at r (A″ , r′ , d) = atT (TyR-uniqueˢ r′ r) d

  ------------------------------------------------------------------------
  -- Each rule's step, from its premises' typings

  lam-S : ∀ {n} {Γ′ : SCx.Ctx m n} {Ψ q q′ π A A′ B t′} → (q′ LG.≤q q) ≡ true → TyR Δ A A′
        → Typed (Γ′ SCx.▸ A′) (q′ LC.∷ Ψ) t′ B π
        → Typed Γ′ Ψ (SC.lam A′ (qS q) (πS π) t′) (A LT.⇒[ LG.mk-kind q π ] B) LG.pure
  lam-S {q = q} {q′} le ra (B′ , rb , d) = _ , r-⇒ refl ra rb , S⊢.⊢lam (≤q-S q′ q le) d

  app-S : ∀ {n} {Γ′ : SCx.Ctx m n} {Ψ₁ Ψ₂ : LC.Usage n} {q π π₁ π₂ A B f′ x′}
        → Typed Γ′ Ψ₁ f′ (A LT.⇒[ LG.mk-kind q π ] B) π₁ → Typed Γ′ Ψ₂ x′ A (LG.positionGrade q π₂)
        → Typed Γ′ (Ψ₁ LC.+ᵘ q LC.*ᵘ Ψ₂) (SC.app f′ x′) B (π₁ LG.·p LG.positionGrade q π₂ LG.·p π)
  app-S {Ψ₁ = Ψ₁} {Ψ₂} {q} {π} {π₁} {π₂} (._ , r-⇒ refl ra rb , d) dx =
    _ , rb , at (usage-app Ψ₁ q Ψ₂)
                (trans (cong (λ x → πS π₁ SG.·p x SG.·p πS π) (sym (positionGrade-S q π₂))) (grade3 π₁ _ π))
                (S⊢.⊢app d (at refl (positionGrade-S q π₂) (typed-at ra dx)))

  let-S : ∀ {n} {Γ′ : SCx.Ctx m n} {Ψ₁ Ψ₂ : LC.Usage n} {q π₁ π₂ A B e′ b′}
        → Typed Γ′ Ψ₁ e′ A (LG.positionGrade q π₁)
        → (∀ {A′} → TyR Δ A A′ → Typed (Γ′ SCx.▸ A′) (q LC.∷ Ψ₂) b′ B π₂)
        → Typed Γ′ (Ψ₂ LC.+ᵘ q LC.*ᵘ Ψ₁) (SC.let′ (qS q) e′ b′) B (LG.positionGrade q π₁ LG.·p π₂)
  let-S {Ψ₁ = Ψ₁} {Ψ₂} {q} {π₁} {π₂} (A′ , ra , d) db = let-S′ (db ra)
    where
      let-S′ : Typed _ (q LC.∷ Ψ₂) _ _ π₂ → Typed _ (Ψ₂ LC.+ᵘ q LC.*ᵘ Ψ₁) _ _ _
      let-S′ (B′ , rb , d′) =
        _ , rb , at (usage-app Ψ₂ q Ψ₁)
                    (trans (cong (SG._·p πS π₂) (sym (positionGrade-S q π₁))) (grade2 _ π₂))
                    (S⊢.⊢let (at refl (positionGrade-S q π₁) d) d′)

  pair-S : ∀ {n} {Γ′ : SCx.Ctx m n} {Ψ₁ Ψ₂ : LC.Usage n} {π₁ π₂ A B a′ b′}
         → Typed Γ′ Ψ₁ a′ A π₁ → Typed Γ′ Ψ₂ b′ B π₂ → Typed Γ′ (Ψ₁ LC.+ᵘ Ψ₂) (SC.pair a′ b′) (A LT.* B) (π₁ LG.·p π₂)
  pair-S {Ψ₁ = Ψ₁} {Ψ₂} {π₁} {π₂} (A′ , ra , d) (B′ , rb , d′) =
    _ , r-* ra rb , at (sym (uS-+ Ψ₁ Ψ₂)) (grade2 π₁ π₂) (S⊢.⊢pair d d′)

  fst-S : ∀ {n} {Γ′ : SCx.Ctx m n} {Ψ π A B p′} → Typed Γ′ Ψ p′ (A LT.* B) π → Typed Γ′ Ψ (SC.fst p′) A π
  fst-S (._ , r-* ra rb , d) = _ , ra , S⊢.⊢fst d

  snd-S : ∀ {n} {Γ′ : SCx.Ctx m n} {Ψ π A B p′} → Typed Γ′ Ψ p′ (A LT.* B) π → Typed Γ′ Ψ (SC.snd p′) B π
  snd-S (._ , r-* ra rb , d) = _ , rb , S⊢.⊢snd d

  inl-S : ∀ {n} {Γ′ : SCx.Ctx m n} {Ψ π A B B′ a′} → TyR Δ B B′ → Typed Γ′ Ψ a′ A π
        → Typed Γ′ Ψ (SC.inl B′ a′) (A LT.+ B) π
  inl-S rB (A′ , ra , d) = _ , r-+ ra rB , S⊢.⊢inl d

  inr-S : ∀ {n} {Γ′ : SCx.Ctx m n} {Ψ π A A′ B b′} → TyR Δ A A′ → Typed Γ′ Ψ b′ B π
        → Typed Γ′ Ψ (SC.inr A′ b′) (A LT.+ B) π
  inr-S rA (B′ , rb , d) = _ , r-+ rA rb , S⊢.⊢inr d

  case-S : ∀ {n} {Γ′ : SCx.Ctx m n} {Ψs Ψ : LC.Usage n} {qℓ qr π₁ π₂ A B C e′ l′ r′}
         → Typed Γ′ Ψs e′ (A LT.+ B) π₁
         → (∀ {A′} → TyR Δ A A′ → Typed (Γ′ SCx.▸ A′) (qℓ LC.∷ Ψ) l′ C π₂)
         → (∀ {B′} → TyR Δ B B′ → Typed (Γ′ SCx.▸ B′) (qr LC.∷ Ψ) r′ C π₂)
         → Typed Γ′ (Ψs LC.+ᵘ Ψ) (SC.case (qS qℓ) (qS qr) e′ l′ r′) C (π₁ LG.·p π₂)
  case-S {Ψs = Ψs} {Ψ} {π₁ = π₁} {π₂} (._ , r-+ ra rb , d) dl dr = case-S′ (dl ra)
    where
      case-S′ : Typed _ _ _ _ π₂ → Typed _ (Ψs LC.+ᵘ Ψ) _ _ _
      case-S′ (C′ , rc , dl′) =
        _ , rc , at (sym (uS-+ Ψs Ψ)) (grade2 π₁ π₂) (S⊢.⊢case d dl′ (typed-at rc (dr rb)))

  fold-S : ∀ {n} {Γ′ : SCx.Ctx m n} {Ψa Ψt : LC.Usage n} {π π₁ π₂ F F′ A a′ t′}
         → LW.WellFormedF F → FunR Δ F F′
         → Typed Γ′ Ψa a′ (LT.⟦ F ⟧T A LT.⇒[ LG.mk-kind LG.Many π ] A) π₁ → Typed Γ′ Ψt t′ (LT.μ-type F) π₂
         → Typed Γ′ (LG.Many LC.*ᵘ Ψa LC.+ᵘ Ψt) (SC.fold F′ a′ t′) A (π₁ LG.·p π₂ LG.·p π)
  fold-S {Ψa = Ψa} {Ψt} {π} {π₁} {π₂} wf rF (._ , r-⇒ refl rFA rA , d) dt =
    _ , rA , at (usage-many Ψa Ψt) (grade3 π₁ π₂ π)
                (S⊢.⊢fold (wf-S wf rF) (atT (cong (λ X → X ST.⇒[ _ ] _) (TyR-uniqueˢ rFA (TyR-⟦⟧ rF rA))) d)
                          (typed-at (r-μ rF) dt))

  unfold-S : ∀ {n} {Γ′ : SCx.Ctx m n} {Ψc Ψs : LC.Usage n} {φ π₁ π₂ F F′ A c′ t′}
           → LW.WellFormedF F → FunR Δ F F′
           → Typed Γ′ Ψc c′ (A LT.⇒[ LG.mk-kind LG.Many (LG.fin φ) ] LT.⟦ F ⟧T A) π₁ → Typed Γ′ Ψs t′ A π₂
           → Typed Γ′ (LG.Many LC.*ᵘ Ψc LC.+ᵘ Ψs) (SC.unfold F′ c′ t′) (LT.ν-type F φ) (π₁ LG.·p π₂)
  unfold-S {Ψc = Ψc} {Ψs} {φ} {π₁} {π₂} wf rF (._ , r-⇒ refl rA rFA , d) dt =
    _ , r-ν refl rF , at (usage-many Ψc Ψs) (grade2 π₁ π₂)
                         (S⊢.⊢unfold (wf-S wf rF) (atT (arr-fin φ (TyR-uniqueˢ rFA (TyR-⟦⟧ rF rA))) d)
                                     (typed-at rA dt))
    where
      arr-fin : ∀ {A′ X Y} φ → X ≡ Y
              → (A′ ST.⇒[ SG.mk-kind SG.Many (πS (LG.fin φ)) ] X) ≡ (A′ ST.⇒[ SG.mk-kind SG.Many (SG.fin (φS φ)) ] Y)
      arr-fin LG.pure refl = refl
      arr-fin LG.act  refl = refl

  out-S : ∀ {n} {Γ′ : SCx.Ctx m n} {Ψ φ π₁ F t′} → LW.WellFormedF F
        → Typed Γ′ Ψ t′ (LT.ν-type F φ) π₁ → Typed Γ′ Ψ (SC.out t′) (LT.⟦ F ⟧T (LT.ν-type F φ)) (π₁ LG.·p LG.fin φ)
  out-S {φ = φ} {π₁} wf (._ , r-ν refl rF , d) =
    _ , TyR-⟦⟧ rF (r-ν refl rF) , at refl (sym (trans (·p-S π₁ (LG.fin φ)) (cong (πS π₁ SG.·p_) (πS-fin φ))))
                                     (S⊢.⊢out (wf-S wf rF) d)

  iter-S : ∀ {n} {Γ′ : SCx.Ctx m n} {Ψf Ψs : LC.Usage n} {π₁ π₂ A B f′ t′}
         → Typed Γ′ Ψf f′ (A LT.⇒[ LG.mk-kind LG.Many LG.act ] (B LT.+ A)) π₁ → Typed Γ′ Ψs t′ A π₂
         → Typed Γ′ (LG.Many LC.*ᵘ Ψf LC.+ᵘ Ψs) (SC.iter f′ t′) B (π₁ LG.·p π₂ LG.·p LG.eff)
  iter-S {Ψf = Ψf} {Ψs} {π₁} {π₂} (._ , r-⇒ refl rA (r-+ rB rA′) , d) dt =
    _ , rB , at (usage-many Ψf Ψs) (grade3 π₁ π₂ LG.eff)
                (S⊢.⊢iter (atT (cong (λ X → _ ST.⇒[ _ ] (_ ST.+ X)) (TyR-uniqueˢ rA′ rA)) d) (typed-at rA dt))

  sub-use-S : ∀ {n} {Γ′ : SCx.Ctx m n} {Ψ Ψ′ π A t′} → Ψ LC.⊑ᵘ Ψ′ → Typed Γ′ Ψ t′ A π → Typed Γ′ Ψ′ t′ A π
  sub-use-S s (A′ , ra , d) = A′ , ra , S⊢.⊢sub-use (⊑ᵘ-S s) d

  sub-eff-S : ∀ {n} {Γ′ : SCx.Ctx m n} {Ψ π π′ A t′} → π LS.⊑π π′ → Typed Γ′ Ψ t′ A π → Typed Γ′ Ψ t′ A π′
  sub-eff-S p (A′ , ra , d) = A′ , ra , S⊢.⊢sub-eff (⊑π-S p) d

  ------------------------------------------------------------------------
  -- The compiler's typing, as the Spec's

  ⊢-S : ∀ {n} {Γ : LC.Ctx n} {Γ′ Ψ t t′ A π} → CleanSig S → CtxR Δ Γ Γ′ → TmR Δ t t′
      → Γ L⊢.⊢[ Ψ ] t ∷ A ! π → Typed Γ′ Ψ t′ A π
  ⊢-S c g rt (L⊢.⊢sub-use s dt) = sub-use-S s (⊢-S c g rt dt)
  ⊢-S c g rt (L⊢.⊢sub-eff p dt) = sub-eff-S p (⊢-S c g rt dt)
  ⊢-S c g (r-var i) (L⊢.⊢var .i) = _ , lookup-R g i , at (sym (uS-single i LG.One)) refl (S⊢.⊢var i)
  ⊢-S c g (r-lam ra rt) (L⊢.⊢lam le dt) = lam-S le ra (⊢-S c (r-▸ g ra) rt dt)
  ⊢-S c g (r-app rf rx) (L⊢.⊢app df dx) = app-S (⊢-S c g rf df) (⊢-S c g rx dx)
  ⊢-S c g (r-let re rb) (L⊢.⊢let de db) = let-S (⊢-S c g re de) (λ ra → ⊢-S c (r-▸ g ra) rb db)
  ⊢-S c g r-unit L⊢.⊢unit = _ , r-unit , at (sym uS-zero) refl S⊢.⊢unit
  ⊢-S c g (r-pair ra rb) (L⊢.⊢pair da db) = pair-S (⊢-S c g ra da) (⊢-S c g rb db)
  ⊢-S c g (r-fst rp) (L⊢.⊢fst dp) = fst-S (⊢-S c g rp dp)
  ⊢-S c g (r-snd rp) (L⊢.⊢snd dp) = snd-S (⊢-S c g rp dp)
  ⊢-S c g (r-inl rB ra) (L⊢.⊢inl da) = inl-S rB (⊢-S c g ra da)
  ⊢-S c g (r-inr rA rb) (L⊢.⊢inr db) = inr-S rA (⊢-S c g rb db)
  ⊢-S c g (r-case re rl rr) (L⊢.⊢case de dl dr) =
    case-S (⊢-S c g re de) (λ ra → ⊢-S c (r-▸ g ra) rl dl) (λ rb → ⊢-S c (r-▸ g rb) rr dr)
  ⊢-S c g (r-absurd rA re) (L⊢.⊢absurd de) = _ , rA , S⊢.⊢absurd (typed-at r-void (⊢-S c g re de))
  ⊢-S c g (r-roll rF rt) (L⊢.⊢roll wf dt) =
    _ , r-μ rF , S⊢.⊢roll (wf-S wf rF) (typed-at (TyR-⟦⟧ rF (r-μ rF)) (⊢-S c g rt dt))
  ⊢-S c g (r-fold rF ra rt) (L⊢.⊢fold _ wf da dt) = fold-S wf rF (⊢-S c g ra da) (⊢-S c g rt dt)
  ⊢-S c g (r-unfold rF rc rt) (L⊢.⊢unfold wf dc dt) = unfold-S wf rF (⊢-S c g rc dc) (⊢-S c g rt dt)
  ⊢-S c g (r-out rt) (L⊢.⊢out wf dt) = out-S wf (⊢-S c g rt dt)
  ⊢-S c g (r-iter rf rt) (L⊢.⊢iter df dt) = iter-S (⊢-S c g rf df) (⊢-S c g rt dt)
  ⊢-S c g (r-coerce rA rB rt) (L⊢.⊢coerce s dt) = _ , rB , S⊢.⊢coerce (sub-S s rA rB) (typed-at rA (⊢-S c g rt dt))
  ⊢-S c g (r-lit (L.lit-int i)) L⊢.⊢lit-int = _ , r-int , at (sym uS-zero) refl S⊢.⊢lit-int
  ⊢-S c g (r-lit (L.lit-float d)) L⊢.⊢lit-float = _ , r-float , at (sym uS-zero) refl S⊢.⊢lit-float
  ⊢-S c g (r-prim p rt) (L⊢.⊢prim .p dt) =
    _ , primCod-R p , S⊢.⊢prim (primS p) (typed-at (primDom-R p) (⊢-S c g rt dt))
  ⊢-S c g (r-sigop rA) (L⊢.⊢sigop _ _ _ _ mem) = _ , rA , at (sym uS-zero) refl (S⊢.⊢sigop (sigop-S mem rA))
  ⊢-S c g (r-ref d r) (L⊢.⊢ref .d τ rs) =
    _ , ref-type S d (c d) r , at (sym uS-zero) refl (S⊢.⊢ref d (castSub S d _) (ref-respects S d rs r))
