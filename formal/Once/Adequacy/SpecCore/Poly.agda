-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.SpecCore.Poly — the compiler's core program terms as the
-- Spec's (plan 0.121, the core bridge).
--
-- A definition's body in the compiler's core telescope (`Lang.Core.Telescope`)
-- is a term over its type variables (`Lang.Core.PolyTyping`), the same calculus
-- as the Spec's core (`Spec.Core.Typing`), transcribed one from the other: the
-- translation is a function on contexts, terms and derivations (`trD`). The
-- Spec program the bridge builds has these derivations as its bodies' typings,
-- so the two meanings are compared along `trD`.
--
-- The compiler's types also have the constant `rigid k i`, which no program's
-- body contains; it goes to `Unit`. An FFI declaration goes to the Spec
-- declaration of its type (`declS`); that it is one of Σ's is a parameter
-- (`sigop-S`), discharged where the program's signature is built.
------------------------------------------------------------------------

open import Data.Nat using (ℕ)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Product using (_,_)
open import Once.Lang.Contract using (ISig)
open import Once.Lang.Name using (showCanonical; WordName)
import Once.Lang.Core.PolyTy as LP
import Once.Lang.Type as LT
import Once.Lang.Type.Grade as LG
open import Once.Spec.Signature using (Signature; DeclType; BTy; constant; value; operation; _∶_; ⌜_⌝; ⌜_⌝ᵈ)
import Once.Spec.Signature as SSig
open import Once.Adequacy.SpecGrammar.Conv using (qS)

module Once.Adequacy.SpecCore.Poly where

open import Data.Fin using (Fin; zero; suc)
open import Data.Bool using (true)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)

import Once.Lang.Type.Sub as LS
import Once.Lang.Type.WellFormed as LW
import Once.Lang.Type.Honest as LH
import Once.Lang.Context as LC
import Once.Spec.Grade as SG
import Once.Spec.Type as ST
import Once.Spec.Sub as SSub
import Once.Spec.Context as SCx
import Once.Spec.Core.Syntax as SC
open import Once.Adequacy.SpecGrammar.Conv using (πS; φS; kS)
open import Once.Adequacy.SpecCore.Type using (kindS; ⊑π-S; ⊑φ-S; ·p-S; positionGrade-S; πS-fin)
open import Once.Adequacy.SpecCore.Context using (uS; uS-zero; uS-single; uS-+; uS-*; ⊑ᵘ-S; ≤q-S)
open import Once.Adequacy.SpecCore.Schema using (ptyS; pfunS; kindsS; schS; defsS; castSub)

------------------------------------------------------------------------
-- Declarations
------------------------------------------------------------------------

-- A base type's code (anything else: `unit`, never used).
toB : LT.Type → BTy
toB LT.Unit           = SSig.unit
toB LT.Void           = SSig.void
toB LT.Int            = SSig.int
toB LT.Float          = SSig.float
toB (A LT.* B)        = toB A SSig.* toB B
toB (A LT.+ B)        = toB A SSig.+ toB B
toB (_ LT.⇒[ _ ] _)   = SSig.unit
toB (LT.μ-type _)     = SSig.unit
toB (LT.ν-type _ _)   = SSig.unit
toB (LT.rigid _ _)    = SSig.unit

-- An FFI declaration's type, as a Spec declaration: a pure arrow a value, an
-- acting one an operation, a base type a constant.
declS : LT.Type → DeclType
declS (A LT.⇒[ LG.mk-kind q LG.pure ] B) = value (toB A) (qS q) (toB B)
declS (A LT.⇒[ LG.mk-kind q LG.act ] B)  = operation (toB A) (qS q) (toB B)
declS (A LT.⇒[ LG.mk-kind q LG.eff ] B)  = operation (toB A) (qS q) (toB B)
declS LT.Unit         = constant (toB LT.Unit)
declS LT.Void         = constant (toB LT.Void)
declS LT.Int          = constant (toB LT.Int)
declS LT.Float        = constant (toB LT.Float)
declS (A LT.* B)      = constant (toB (A LT.* B))
declS (A LT.+ B)      = constant (toB (A LT.+ B))
declS (LT.μ-type F)   = constant (toB (LT.μ-type F))
declS (LT.ν-type F φ) = constant (toB (LT.ν-type F φ))
declS (LT.rigid k i)  = constant (toB (LT.rigid k i))

module _ {m : ℕ} where

  toB-S : ∀ {A} → LW.IsBaseType A → LW.RigidFree A → ⌜ toB A ⌝ ≡ ptyS (LP.⌈_⌉ {m} A)
  toB-S LW.base-Unit  _ = refl
  toB-S LW.base-Void  _ = refl
  toB-S LW.base-Int   _ = refl
  toB-S LW.base-Float _ = refl
  toB-S (LW.base-Prod a b) (LW.rf-* ra rb) = cong₂ ST._*_ (toB-S a ra) (toB-S b rb)
  toB-S (LW.base-Sum a b)  (LW.rf-+ ra rb) = cong₂ ST._+_ (toB-S a ra) (toB-S b rb)
  toB-S LW.base-rigid ()

  -- An honest FFI type is its declaration's.
  declS-S : ∀ {A} → LW.IsConcrete A → LH.HonestFFI A → LW.RigidFree A → ⌜ declS A ⌝ᵈ ≡ ptyS (LP.⌈_⌉ {m} A)
  declS-S {A LT.⇒[ LG.mk-kind q LG.pure ] B} (LW.con-fun a b) h (LW.rf-⇒ ra rb) =
    cong₂ (λ x y → x ST.⇒[ SG.mk-kind (qS q) SG.pure ] y) (toB-S a ra) (toB-S b rb)
  declS-S {A LT.⇒[ LG.mk-kind q LG.act ] B} (LW.con-fun a b) h (LW.rf-⇒ ra rb) =
    cong₂ (λ x y → x ST.⇒[ SG.mk-kind (qS q) SG.act ] y) (toB-S a ra) (toB-S b rb)
  declS-S {A LT.⇒[ LG.mk-kind LG.Zero LG.eff ] B} _ () _
  declS-S {A LT.⇒[ LG.mk-kind LG.One  LG.eff ] B} _ () _
  declS-S {A LT.⇒[ LG.mk-kind LG.Many LG.eff ] B} _ () _
  declS-S (LW.con-base LW.base-Unit) () _
  declS-S (LW.con-base LW.base-Void) () _
  declS-S (LW.con-base LW.base-Int) _ _ = refl
  declS-S (LW.con-base LW.base-Float) _ _ = refl
  declS-S (LW.con-base b@(LW.base-Prod _ _)) _ r = toB-S b r
  declS-S (LW.con-base b@(LW.base-Sum _ _)) _ r = toB-S b r
  declS-S (LW.con-base LW.base-rigid) () _

------------------------------------------------------------------------
-- Types: instances and functor application commute with the translation
------------------------------------------------------------------------

mutual
  ptyS-⟨⟩ : ∀ {a k} (A : LP.Ty a) (τ : LP.Sub a k) → ptyS (A LP.⟨ τ ⟩) ≡ ptyS A ST.⟨ (λ i → ptyS (τ i)) ⟩
  ptyS-⟨⟩ (LP.var i)      τ = refl
  ptyS-⟨⟩ LP.Unit         τ = refl
  ptyS-⟨⟩ LP.Void         τ = refl
  ptyS-⟨⟩ LP.Int          τ = refl
  ptyS-⟨⟩ LP.Float        τ = refl
  ptyS-⟨⟩ (LP.rigid k i)  τ = refl
  ptyS-⟨⟩ (A LP.* B)      τ = cong₂ ST._*_ (ptyS-⟨⟩ A τ) (ptyS-⟨⟩ B τ)
  ptyS-⟨⟩ (A LP.+ B)      τ = cong₂ ST._+_ (ptyS-⟨⟩ A τ) (ptyS-⟨⟩ B τ)
  ptyS-⟨⟩ (A LP.⇒[ k ] B) τ = cong₂ (λ x y → x ST.⇒[ kS k ] y) (ptyS-⟨⟩ A τ) (ptyS-⟨⟩ B τ)
  ptyS-⟨⟩ (LP.μ-type F)   τ = cong ST.μ (pfunS-⟨⟩ F τ)
  ptyS-⟨⟩ (LP.ν-type F φ) τ = cong (λ G → ST.ν G (φS φ)) (pfunS-⟨⟩ F τ)

  pfunS-⟨⟩ : ∀ {a k} (F : LP.Fun a) (τ : LP.Sub a k) → pfunS (F LP.⟨ τ ⟩F) ≡ pfunS F ST.⟨ (λ i → ptyS (τ i)) ⟩F
  pfunS-⟨⟩ (LP.K A)   τ = cong ST.K (ptyS-⟨⟩ A τ)
  pfunS-⟨⟩ LP.Id      τ = refl
  pfunS-⟨⟩ (F LP.⊕ G) τ = cong₂ ST._⊕_ (pfunS-⟨⟩ F τ) (pfunS-⟨⟩ G τ)
  pfunS-⟨⟩ (F LP.⊗ G) τ = cong₂ ST._⊗_ (pfunS-⟨⟩ F τ) (pfunS-⟨⟩ G τ)

ptyS-⟦⟧ : ∀ {a} (F : LP.Fun a) (X : LP.Ty a) → ptyS (LP.⟦ F ⟧F X) ≡ ST.⟦ pfunS F ⟧F (ptyS X)
ptyS-⟦⟧ (LP.K A)   X = refl
ptyS-⟦⟧ LP.Id      X = refl
ptyS-⟦⟧ (F LP.⊕ G) X = cong₂ ST._+_ (ptyS-⟦⟧ F X) (ptyS-⟦⟧ G X)
ptyS-⟦⟧ (F LP.⊗ G) X = cong₂ ST._*_ (ptyS-⟦⟧ F X) (ptyS-⟦⟧ G X)

module _ {a} {Δ : LP.KCtx a} where

  baseS : ∀ {A} → LP.Base Δ A → ST.Base (kindsS Δ) (ptyS A)
  baseS (LP.b-var e)   = ST.b-var (cong kindS e)
  baseS LP.b-Unit      = ST.b-Unit
  baseS LP.b-Void      = ST.b-Void
  baseS LP.b-Int       = ST.b-Int
  baseS LP.b-Float     = ST.b-Float
  baseS LP.b-rigid     = ST.b-Unit
  baseS (LP.b-Prod x y) = ST.b-* (baseS x) (baseS y)
  baseS (LP.b-Sum x y)  = ST.b-+ (baseS x) (baseS y)

  wfS : ∀ {F} → LP.WFFun Δ F → ST.WFFun (kindsS Δ) (pfunS F)
  wfS (LP.wf-K b)      = ST.wf-K (baseS b)
  wfS LP.wf-Id         = ST.wf-Id
  wfS (LP.wf-Sum f g)  = ST.wf-⊕ (wfS f) (wfS g)
  wfS (LP.wf-Prod f g) = ST.wf-⊗ (wfS f) (wfS g)

-- (a kind is `base` on one side when on the other)
kindS-base : ∀ k → kindS k ≡ ST.base → k ≡ LT.k-base
kindS-base LT.k-base _ = refl
kindS-base LT.k-any  ()

------------------------------------------------------------------------
-- Terms and derivations
------------------------------------------------------------------------

-- Subtyping, over the definitions signature's terms' types.
module SubS {Fs : ISig} {s : ℕ} (S : LP.Sig Fs s) where
  import Once.Lang.Core.PolyTyping S as PT
  import Once.Lang.Core.PolySub as PS

  subS : ∀ {a} {A B : LP.Ty a} → A PS.<:ₚ B → ptyS A SSub.<: ptyS B
  subS PS.sub-var         = SSub.sub-var
  subS PS.sub-void        = SSub.sub-void
  subS PS.sub-unit        = SSub.sub-unit
  subS PS.sub-int         = SSub.sub-int
  subS PS.sub-float       = SSub.sub-float
  subS PS.sub-rigid       = SSub.sub-unit
  subS (PS.sub-arr x y g) = SSub.sub-arr (subS x) (subS y) (⊑π-S g)
  subS (PS.sub-prod x y)  = SSub.sub-* (subS x) (subS y)
  subS (PS.sub-sum x y)   = SSub.sub-+ (subS x) (subS y)
  subS PS.sub-μ           = SSub.sub-μ
  subS (PS.sub-ν {φ = φ} {φ′} g) = SSub.sub-ν (⊑φ-S φ φ′ g)

module Translate {Fs : ISig} {s : ℕ} (S : LP.Sig Fs s) (Σ : Signature)
  (sigop-S : ∀ {c A} → WordName c → (showCanonical c , A) ∈ Fs → (c ∶ declS A) ∈ Σ) where

  import Once.Lang.Core.PolyTyping S as PT
  import Once.Lang.Core.PolySub as PS
  import Once.Lang.Core.Syntax S as L
  open SubS S using (subS)
  open import Once.Adequacy.SpecCore.Prim S using (litS; primS; primDom-S; primCod-S)

  S′ : SC.Defs s
  S′ = defsS S

  import Once.Spec.Core.Typing Σ S′ as S⊢

  pctxS : ∀ {a n} → PT.PCtx a n → SCx.Ctx a n
  pctxS PT.∅           = SCx.∅
  pctxS (Γ PT., A ^ q) = pctxS Γ SCx.▸ ptyS A

  lookupS : ∀ {a n} (Γ : PT.PCtx a n) (i : Fin n) → ptyS (PT.lookupP Γ i) ≡ SCx.lookup (pctxS Γ) i
  lookupS (Γ PT., A ^ q) zero    = refl
  lookupS (Γ PT., A ^ q) (suc i) = lookupS Γ i

  ptmS : ∀ {a n} → PT.PTm a n → SC.Tm S′ a n
  ptmS (PT.var i)             = SC.var i
  ptmS (PT.lam A q π t)       = SC.lam (ptyS A) (qS q) (πS π) (ptmS t)
  ptmS (PT.app f x)           = SC.app (ptmS f) (ptmS x)
  ptmS (PT.let′ q e b)        = SC.let′ (qS q) (ptmS e) (ptmS b)
  ptmS PT.unit                = SC.unit
  ptmS (PT.pair x y)          = SC.pair (ptmS x) (ptmS y)
  ptmS (PT.fst p)             = SC.fst (ptmS p)
  ptmS (PT.snd p)             = SC.snd (ptmS p)
  ptmS (PT.inl B t)           = SC.inl (ptyS B) (ptmS t)
  ptmS (PT.inr A t)           = SC.inr (ptyS A) (ptmS t)
  ptmS (PT.case qℓ qr e l r)  = SC.case (qS qℓ) (qS qr) (ptmS e) (ptmS l) (ptmS r)
  ptmS (PT.absurd A t)        = SC.absurd (ptyS A) (ptmS t)
  ptmS (PT.roll F t)          = SC.roll (pfunS F) (ptmS t)
  ptmS (PT.fold F x t)        = SC.fold (pfunS F) (ptmS x) (ptmS t)
  ptmS (PT.unfold F c t)      = SC.unfold (pfunS F) (ptmS c) (ptmS t)
  ptmS (PT.iter f t)          = SC.iter (ptmS f) (ptmS t)
  ptmS (PT.out t)             = SC.out (ptmS t)
  ptmS (PT.coerce A B t)      = SC.coerce (ptyS A) (ptyS B) (ptmS t)
  ptmS (PT.lit l)             = SC.lit (litS l)
  ptmS (PT.prim p t)          = SC.prim (primS p) (ptmS t)
  ptmS (PT.sigop c A)         = SC.sigop c (declS A)
  ptmS (PT.ref d τ)           = SC.ref d (castSub S d (λ i → ptyS (τ i)))

  -- A reference's type and kinds, at the Spec's schema.
  ref-ty : ∀ {s₀ a} (S₀ : LP.Sig Fs s₀) (d : Fin s₀) (τ : LP.Sub (LP.Schema.arity (S₀ LP.!! d)) a)
         → ptyS (LP.Schema.type (S₀ LP.!! d) LP.⟨ τ ⟩)
           ≡ SC.Schema.type (defsS S₀ SC.!! d) ST.⟨ castSub S₀ d (λ i → ptyS (τ i)) ⟩
  ref-ty (S₀ LP.▷ sc) zero    τ = ptyS-⟨⟩ (LP.Schema.type sc) τ
  ref-ty (S₀ LP.▷ sc) (suc d) τ = ref-ty S₀ d τ

  ref-resp : ∀ {s₀ a} {Δ : LP.KCtx a} (S₀ : LP.Sig Fs s₀) (d : Fin s₀) (τ : LP.Sub (LP.Schema.arity (S₀ LP.!! d)) a)
           → (∀ i → LP.Schema.kinds (S₀ LP.!! d) i ≡ LT.k-base → LP.Base Δ (τ i))
           → ST.Respects (SC.Schema.kinds (defsS S₀ SC.!! d)) (kindsS Δ) (castSub S₀ d (λ i → ptyS (τ i)))
  ref-resp (S₀ LP.▷ sc) zero    τ rs i e = baseS (rs i (kindS-base _ e))
  ref-resp (S₀ LP.▷ sc) (suc d) τ rs   = ref-resp S₀ d τ rs

  -- (a Spec typing, moved along equal usages, grades and types)
  atS : ∀ {a n} {Δ : ST.KCtx a} {Γ : SCx.Ctx a n} {Ψ Ψ′ t A A′ π π′} → Ψ ≡ Ψ′ → A ≡ A′ → π ≡ π′
       → S⊢._⊩_⊢[_]_∷_!_ Δ Γ Ψ t A π → S⊢._⊩_⊢[_]_∷_!_ Δ Γ Ψ′ t A′ π′
  atS refl refl refl d = d

  -- (the equations the translation moves its typings along)
  eqᵘ-var : ∀ {n} (i : Fin n) → SCx.singleUse i SG.One ≡ uS (LC.singleUse i LG.One)
  eqᵘ-var i = sym (uS-single i LG.One)

  eqᵘ-app : ∀ {n} (Ψ₁ : LC.Usage n) q Ψ₂ → uS Ψ₁ SCx.+ᵘ qS q SCx.*ᵘ uS Ψ₂ ≡ uS (Ψ₁ LC.+ᵘ q LC.*ᵘ Ψ₂)
  eqᵘ-app Ψ₁ q Ψ₂ = sym (trans (uS-+ Ψ₁ (q LC.*ᵘ Ψ₂)) (cong (uS Ψ₁ SCx.+ᵘ_) (uS-* q Ψ₂)))

  eqᵘ-+ : ∀ {n} (Ψ₁ Ψ₂ : LC.Usage n) → uS Ψ₁ SCx.+ᵘ uS Ψ₂ ≡ uS (Ψ₁ LC.+ᵘ Ψ₂)
  eqᵘ-+ Ψ₁ Ψ₂ = sym (uS-+ Ψ₁ Ψ₂)

  eqᵍ-· : ∀ π₁ π₂ → πS π₁ SG.·p πS π₂ ≡ πS (π₁ LG.·p π₂)
  eqᵍ-· π₁ π₂ = sym (·p-S π₁ π₂)

  eqᵍ-app : ∀ π₁ q π₂ π → πS π₁ SG.·p SG.positionGrade (qS q) (πS π₂) SG.·p πS π
                        ≡ πS (π₁ LG.·p LG.positionGrade q π₂ LG.·p π)
  eqᵍ-app π₁ q π₂ π = sym (trans (·p-S π₁ _) (cong (πS π₁ SG.·p_) (trans (·p-S (LG.positionGrade q π₂) π)
                                                     (cong (SG._·p πS π) (positionGrade-S q π₂)))))

  eqᵍ-let : ∀ q π₁ π₂ → SG.positionGrade (qS q) (πS π₁) SG.·p πS π₂ ≡ πS (LG.positionGrade q π₁ LG.·p π₂)
  eqᵍ-let q π₁ π₂ = sym (trans (·p-S (LG.positionGrade q π₁) π₂) (cong (SG._·p πS π₂) (positionGrade-S q π₁)))

  eqᵘ-many : ∀ {n} (Ψ₁ Ψ₂ : LC.Usage n) → SG.Many SCx.*ᵘ uS Ψ₁ SCx.+ᵘ uS Ψ₂ ≡ uS (LG.Many LC.*ᵘ Ψ₁ LC.+ᵘ Ψ₂)
  eqᵘ-many Ψ₁ Ψ₂ = sym (trans (uS-+ (LG.Many LC.*ᵘ Ψ₁) Ψ₂) (cong (SCx._+ᵘ uS Ψ₂) (uS-* LG.Many Ψ₁)))

  eqᵍ-3 : ∀ π₁ π₂ π → πS π₁ SG.·p πS π₂ SG.·p πS π ≡ πS (π₁ LG.·p π₂ LG.·p π)
  eqᵍ-3 π₁ π₂ π = sym (trans (·p-S π₁ _) (cong (πS π₁ SG.·p_) (·p-S π₂ π)))

  eqᵍ-out : ∀ π₁ φ → πS π₁ SG.·p SG.fin (φS φ) ≡ πS (π₁ LG.·p LG.fin φ)
  eqᵍ-out π₁ φ = sym (trans (·p-S π₁ (LG.fin φ)) (cong (πS π₁ SG.·p_) (πS-fin φ)))

  arr-fin : ∀ {a} {A′ X Y : ST.Ty a} φ → X ≡ Y
          → (A′ ST.⇒[ SG.mk-kind SG.Many (πS (LG.fin φ)) ] X) ≡ (A′ ST.⇒[ SG.mk-kind SG.Many (SG.fin (φS φ)) ] Y)
  arr-fin LG.pure refl = refl
  arr-fin LG.act  refl = refl

  -- The Spec's typing of a translated term.
  trD : ∀ {a n} {Δ : LP.KCtx a} {Γ : PT.PCtx a n} {Ψ t A π}
      → PT._⊩_⊢[_]_∷_!_ Δ Γ Ψ t A π
      → S⊢._⊩_⊢[_]_∷_!_ (kindsS Δ) (pctxS Γ) (uS Ψ) (ptmS t) (ptyS A) (πS π)
  trD {Γ = Γ} (PT.⊢var i) = atS (eqᵘ-var i) (sym (lookupS Γ i)) refl (S⊢.⊢var i)
  trD (PT.⊢lam {q = q} {q′} le d) = S⊢.⊢lam (≤q-S q′ q le) (trD d)
  trD (PT.⊢app {Ψ₁ = Ψ₁} {Ψ₂} {q} {π} {π₁} {π₂} df dx) =
    atS (eqᵘ-app Ψ₁ q Ψ₂) refl (eqᵍ-app π₁ q π₂ π)
       (S⊢.⊢app (trD df) (atS refl refl (positionGrade-S q π₂) (trD dx)))
  trD (PT.⊢let {Ψ₁ = Ψ₁} {Ψ₂} {q} {π₁} {π₂} de db) =
    atS (eqᵘ-app Ψ₂ q Ψ₁) refl (eqᵍ-let q π₁ π₂)
       (S⊢.⊢let (atS refl refl (positionGrade-S q π₁) (trD de)) (trD db))
  trD PT.⊢unit = atS (sym uS-zero) refl refl S⊢.⊢unit
  trD (PT.⊢pair {Ψ₁ = Ψ₁} {Ψ₂} {π₁} {π₂} da db) =
    atS (eqᵘ-+ Ψ₁ Ψ₂) refl (eqᵍ-· π₁ π₂) (S⊢.⊢pair (trD da) (trD db))
  trD (PT.⊢fst d) = S⊢.⊢fst (trD d)
  trD (PT.⊢snd d) = S⊢.⊢snd (trD d)
  trD (PT.⊢inl d) = S⊢.⊢inl (trD d)
  trD (PT.⊢inr d) = S⊢.⊢inr (trD d)
  trD (PT.⊢case {Ψs = Ψs} {Ψ} {π₁ = π₁} {π₂} ds dl dr) =
    atS (eqᵘ-+ Ψs Ψ) refl (eqᵍ-· π₁ π₂) (S⊢.⊢case (trD ds) (trD dl) (trD dr))
  trD (PT.⊢absurd d) = S⊢.⊢absurd (trD d)
  trD (PT.⊢roll {F = F} wf d) = S⊢.⊢roll (wfS wf) (atS refl (ptyS-⟦⟧ F (LP.μ-type F)) refl (trD d))
  trD (PT.⊢fold {Ψa = Ψa} {Ψt} {π} {π₁} {π₂} {F} {A} _ wf da dt) =
    atS (eqᵘ-many Ψa Ψt) refl (eqᵍ-3 π₁ π₂ π)
       (S⊢.⊢fold (wfS wf) (atS refl (cong (λ X → X ST.⇒[ _ ] _) (ptyS-⟦⟧ F A)) refl (trD da)) (trD dt))
  trD (PT.⊢unfold {Ψc = Ψc} {Ψs} {φ} {π₁} {π₂} {F} {A} wf dc ds) =
    atS (eqᵘ-many Ψc Ψs) refl (eqᵍ-· π₁ π₂)
       (S⊢.⊢unfold (wfS wf) (atS refl (arr-fin φ (ptyS-⟦⟧ F A)) refl (trD dc)) (trD ds))
  trD (PT.⊢out {φ = φ} {π₁} {F} wf d) =
    atS refl (sym (ptyS-⟦⟧ F (LP.ν-type F φ))) (eqᵍ-out π₁ φ)
       (S⊢.⊢out (wfS wf) (trD d))
  trD (PT.⊢iter {Ψf = Ψf} {Ψs} {π₁} {π₂} df ds) =
    atS (eqᵘ-many Ψf Ψs) refl (eqᵍ-3 π₁ π₂ LG.eff)
       (S⊢.⊢iter (trD df) (trD ds))
  trD (PT.⊢coerce p d) = S⊢.⊢coerce (subS p) (trD d)
  trD PT.⊢lit-int = atS (sym uS-zero) refl refl S⊢.⊢lit-int
  trD PT.⊢lit-float = atS (sym uS-zero) refl refl S⊢.⊢lit-float
  trD (PT.⊢prim p d) = atS refl (sym (primCod-S p)) refl (S⊢.⊢prim (primS p) (atS refl (primDom-S p) refl (trD d)))
  trD (PT.⊢sigop c k h r wn mem) = atS (sym uS-zero) (declS-S k h r) refl (S⊢.⊢sigop (sigop-S wn mem))
  trD (PT.⊢sub-eff g d) = S⊢.⊢sub-eff (⊑π-S g) (trD d)
  trD (PT.⊢sub-use p d) = S⊢.⊢sub-use (⊑ᵘ-S p) (trD d)
  trD (PT.⊢ref d τ rs) = atS (sym uS-zero) (sym (ref-ty S d τ)) refl (S⊢.⊢ref d _ (ref-resp S d τ rs))
