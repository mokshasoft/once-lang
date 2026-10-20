-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.SpecFront.Types — the facts about related types the
-- surface typing translation needs (plan 0.121 §3.6, F4/F5).
--
-- `SpecCore.Type.TyR Δ A A′` relates a compiler type (a rigid constant for
-- each of Δ's variables) to the Spec's. Every Spec type is related to one
-- (`back`), and a compiler type below a related one is related too
-- (`below-R`). The subtyping that keeps domains (`<:ᶜ`) crosses both ways,
-- and so does a join (`join-S`), whose leastness ranges over all types: an
-- upper bound in either world gives one in the other.
-- The rest are the types surface rules read off: an annotation's, a
-- declaration's, a functor applied.
------------------------------------------------------------------------

open import Data.Nat using (ℕ)
import Once.Spec.Type as ST

module Once.Adequacy.SpecFront.Types {m : ℕ} (Δ : ST.KCtx m) where

open import Data.Fin using (Fin; toℕ)
open import Data.Fin.Properties using (toℕ-injective)
open import Data.Nat using (_<?_)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)

import Once.Lang.Type.Grade as LG
import Once.Spec.Grade as SG
import Once.Lang.Type as LT
import Once.Lang.Type.Sub as LS
import Once.Lang.Type.WellFormed as LW
import Once.Lang.Type.Honest as LH
import Once.Spec.Sub as SS
open import Once.Spec.Signature using (⌜_⌝; ⌜_⌝ᵈ)
open import Once.Adequacy.SpecGrammar.Conv using (qS; πS; φS; kS; toTy; toFun)
open import Once.Adequacy.SpecCore.Type
open import Once.Adequacy.SpecCore.Poly using (toB; declS)

------------------------------------------------------------------------
-- Every Spec type is a compiler one
------------------------------------------------------------------------

private
  qL : SG.Quantity → LG.Quantity
  qL SG.Zero = LG.Zero
  qL SG.One  = LG.One
  qL SG.Many = LG.Many

  πL : SG.Purity → LG.Purity
  πL SG.pure = LG.pure
  πL SG.act  = LG.act
  πL SG.eff  = LG.eff

  kL : SG.ArrowKind → LG.ArrowKind
  kL (SG.mk-kind q π) = LG.mk-kind (qL q) (πL π)

  kS-kL : ∀ k → kS (kL k) ≡ k
  kS-kL (SG.mk-kind SG.Zero SG.pure) = refl
  kS-kL (SG.mk-kind SG.Zero SG.act)  = refl
  kS-kL (SG.mk-kind SG.Zero SG.eff)  = refl
  kS-kL (SG.mk-kind SG.One  SG.pure) = refl
  kS-kL (SG.mk-kind SG.One  SG.act)  = refl
  kS-kL (SG.mk-kind SG.One  SG.eff)  = refl
  kS-kL (SG.mk-kind SG.Many SG.pure) = refl
  kS-kL (SG.mk-kind SG.Many SG.act)  = refl
  kS-kL (SG.mk-kind SG.Many SG.eff)  = refl

  φL : SG.Finite → LG.Finite
  φL SG.pureᶠ = LG.pure
  φL SG.actᶠ  = LG.act

  φS-φL : ∀ f → φS (φL f) ≡ f
  φS-φL SG.pureᶠ = refl
  φS-φL SG.actᶠ  = refl

  κL : ST.Kind → LT.TKind
  κL ST.base = LT.k-base
  κL ST.any  = LT.k-any

  kindS-κL : ∀ κ → kindS (κL κ) ≡ κ
  kindS-κL ST.base = refl
  kindS-κL ST.any  = refl

mutual
  back : ∀ (D : ST.Ty m) → Σ[ D₀ ∈ LT.Type ] TyR Δ D₀ D
  back (ST.var j)   = LT.rigid (κL (Δ j)) (toℕ j) , r-rigid j refl (sym (kindS-κL (Δ j)))
  back ST.Unit      = LT.Unit , r-unit
  back ST.Void      = LT.Void , r-void
  back ST.Int       = LT.Int , r-int
  back ST.Float     = LT.Float , r-float
  back (A ST.* B)   = (proj₁ (back A) LT.* proj₁ (back B)) , r-* (proj₂ (back A)) (proj₂ (back B))
  back (A ST.+ B)   = (proj₁ (back A) LT.+ proj₁ (back B)) , r-+ (proj₂ (back A)) (proj₂ (back B))
  back (A ST.⇒[ k ] B) = (proj₁ (back A) LT.⇒[ kL k ] proj₁ (back B)) , r-⇒ (kS-kL k) (proj₂ (back A)) (proj₂ (back B))
  back (ST.μ F)     = LT.μ-type (proj₁ (backF F)) , r-μ (proj₂ (backF F))
  back (ST.ν F f)   = LT.ν-type (proj₁ (backF F)) (φL f) , r-ν (φS-φL f) (proj₂ (backF F))

  backF : ∀ (F : ST.Fun m) → Σ[ F₀ ∈ LT.Functor ] FunR Δ F₀ F
  backF (ST.K A)   = LT.K (proj₁ (back A)) , r-K (proj₂ (back A))
  backF ST.Id      = LT.Id , r-Id
  backF (F ST.⊕ G) = (proj₁ (backF F) LT.⊕ proj₁ (backF G)) , r-⊕ (proj₂ (backF F)) (proj₂ (backF G))
  backF (F ST.⊗ G) = (proj₁ (backF F) LT.⊗ proj₁ (backF G)) , r-⊗ (proj₂ (backF F)) (proj₂ (backF G))

------------------------------------------------------------------------
-- Keeping domains, both ways
------------------------------------------------------------------------

subᶜ-S : ∀ {A B A′ B′} → A LS.<:ᶜ B → TyR Δ A A′ → TyR Δ B B′ → A′ SS.<:ᶜ B′
subᶜ-S LS.subᶜ-void  r-void  _       = SS.subᶜ-void
subᶜ-S LS.subᶜ-unit  r-unit  r-unit  = SS.subᶜ-unit
subᶜ-S LS.subᶜ-int   r-int   r-int   = SS.subᶜ-int
subᶜ-S LS.subᶜ-float r-float r-float = SS.subᶜ-float
subᶜ-S (LS.subᶜ-arr b p) (r-⇒ refl ra rb) (r-⇒ refl ra′ rb′) =
  subst (λ X → _ SS.<:ᶜ (X ST.⇒[ _ ] _)) (TyR-uniqueˢ ra ra′) (SS.subᶜ-arr (subᶜ-S b rb rb′) (⊑π-S p))
subᶜ-S (LS.subᶜ-prod a b) (r-* ra rb) (r-* ra′ rb′) = SS.subᶜ-* (subᶜ-S a ra ra′) (subᶜ-S b rb rb′)
subᶜ-S (LS.subᶜ-sum a b)  (r-+ ra rb) (r-+ ra′ rb′) = SS.subᶜ-+ (subᶜ-S a ra ra′) (subᶜ-S b rb rb′)
subᶜ-S LS.subᶜ-μ (r-μ f) (r-μ f′) = subst (λ G → ST.μ _ SS.<:ᶜ ST.μ G) (FunR-uniqueˢ f f′) SS.subᶜ-μ
subᶜ-S (LS.subᶜ-ν {φ = φ} {φ′} p) (r-ν refl f) (r-ν refl f′) =
  subst (λ G → ST.ν _ _ SS.<:ᶜ ST.ν G _) (FunR-uniqueˢ f f′) (SS.subᶜ-ν (⊑φ-S φ φ′ p))
subᶜ-S LS.subᶜ-rigid r@(r-rigid _ _ _) r′ = subst (λ X → ST.var _ SS.<:ᶜ X) (TyR-uniqueˢ r r′) SS.subᶜ-var

subᶜ-L : ∀ {A B A′ B′} → A′ SS.<:ᶜ B′ → TyR Δ A A′ → TyR Δ B B′ → A LS.<:ᶜ B
subᶜ-L SS.subᶜ-void r-void _ = LS.subᶜ-void
subᶜ-L SS.subᶜ-var r@(r-rigid _ _ _) r′ = subst (λ X → _ LS.<:ᶜ X) (TyR-uniqueˡ r r′) LS.subᶜ-rigid
subᶜ-L SS.subᶜ-unit r-unit r-unit = LS.subᶜ-unit
subᶜ-L SS.subᶜ-int r-int r-int = LS.subᶜ-int
subᶜ-L SS.subᶜ-float r-float r-float = LS.subᶜ-float
subᶜ-L (SS.subᶜ-arr b p) (r-⇒ {k = LG.mk-kind q π} e ra rb) (r-⇒ {k = LG.mk-kind q′ π′} e′ ra′ rb′) =
  arr (qS-injective (trans (cong SG.ArrowKind.quantity e) (sym (cong SG.ArrowKind.quantity e′))))
      (⊑π-L π π′ (grade (cong SG.ArrowKind.purity e) (cong SG.ArrowKind.purity e′) p))
      (TyR-uniqueˡ ra ra′) (subᶜ-L b rb rb′)
  where
    grade : ∀ {x y x′ y′} → x ≡ x′ → y ≡ y′ → x′ SG.⊑π y′ → x SG.⊑π y
    grade refl refl p = p
    arr : ∀ {A A′ B B′} → q ≡ q′ → π LS.⊑π π′ → A ≡ A′ → B LS.<:ᶜ B′
        → (A LT.⇒[ LG.mk-kind q π ] B) LS.<:ᶜ (A′ LT.⇒[ LG.mk-kind q′ π′ ] B′)
    arr refl p refl b = LS.subᶜ-arr b p
subᶜ-L (SS.subᶜ-* a b) (r-* ra rb) (r-* ra′ rb′) = LS.subᶜ-prod (subᶜ-L a ra ra′) (subᶜ-L b rb rb′)
subᶜ-L (SS.subᶜ-+ a b) (r-+ ra rb) (r-+ ra′ rb′) = LS.subᶜ-sum (subᶜ-L a ra ra′) (subᶜ-L b rb rb′)
subᶜ-L SS.subᶜ-μ (r-μ f) (r-μ f′) = subst (λ G → LT.μ-type _ LS.<:ᶜ LT.μ-type G) (FunR-uniqueˡ f f′) LS.subᶜ-μ
subᶜ-L (SS.subᶜ-ν p) (r-ν {φ = φ} e f) (r-ν {φ = φ′} e′ f′) =
  subst (λ G → LT.ν-type _ φ LS.<:ᶜ LT.ν-type G φ′) (FunR-uniqueˡ f f′) (LS.subᶜ-ν (⊑φ-L φ φ′ (grade e e′ p)))
  where
    grade : ∀ {x y x′ y′} → x ≡ x′ → y ≡ y′ → SG.fin x′ SG.⊑π SG.fin y′ → SG.fin x SG.⊑π SG.fin y
    grade refl refl p = p

------------------------------------------------------------------------
-- A type below a related one is related
------------------------------------------------------------------------

below-R : ∀ {A B B′} → A LS.<:ᶜ B → TyR Δ B B′ → Σ[ A′ ∈ ST.Ty m ] TyR Δ A A′
below-R LS.subᶜ-void  _       = ST.Void , r-void
below-R LS.subᶜ-unit  r       = _ , r
below-R LS.subᶜ-int   r       = _ , r
below-R LS.subᶜ-float r       = _ , r
below-R (LS.subᶜ-arr b p) (r-⇒ {B′ = B′} e ra rb) =
  (_ ST.⇒[ kS _ ] proj₁ (below-R b rb)) , r-⇒ refl ra (proj₂ (below-R b rb))
below-R (LS.subᶜ-prod a b) (r-* ra rb) = _ , r-* (proj₂ (below-R a ra)) (proj₂ (below-R b rb))
below-R (LS.subᶜ-sum a b)  (r-+ ra rb) = _ , r-+ (proj₂ (below-R a ra)) (proj₂ (below-R b rb))
below-R LS.subᶜ-μ r = _ , r
below-R (LS.subᶜ-ν _) (r-ν _ f) = _ , r-ν refl f
below-R LS.subᶜ-rigid r = _ , r

------------------------------------------------------------------------
-- An upper bound made related: a rigid constant of no parameter of Δ sits
-- above only `Void` in a related type, so it may be `Void` there
------------------------------------------------------------------------

private
  Bound : LT.TKind → ℕ → Set
  Bound k i = Σ[ j ∈ Fin m ] (toℕ j ≡ i × Δ j ≡ kindS k)

  bound? : ∀ k i → Dec (Bound k i)
  bound? k i = at (i <? m)
    where
      open import Data.Fin using (fromℕ<)
      open import Data.Fin.Properties using (toℕ-fromℕ<)
      open import Data.Nat using (_<_)
      kindEq? : ∀ (a b : ST.Kind) → Dec (a ≡ b)
      kindEq? ST.base ST.base = yes refl
      kindEq? ST.any  ST.any  = yes refl
      kindEq? ST.base ST.any  = no λ ()
      kindEq? ST.any  ST.base = no λ ()
      at : Dec (i < m) → Dec (Bound k i)
      at (no ¬lt) = no λ { (j , e , _) → ¬lt (subst (_< m) e (Data.Fin.Properties.toℕ<n j)) }
      at (yes lt) = kd (kindEq? (Δ (fromℕ< lt)) (kindS k))
        where
          kd : Dec (Δ (fromℕ< lt) ≡ kindS k) → Dec (Bound k i)
          kd (yes e) = yes (fromℕ< lt , toℕ-fromℕ< lt , e)
          kd (no ¬e) = no λ { (j , e₁ , e₂) → ¬e (subst (λ j′ → Δ j′ ≡ kindS k) (toℕ-injective (trans e₁ (sym (toℕ-fromℕ< lt)))) e₂) }

  rigid-or : ∀ k i → Dec (Bound k i) → LT.Type
  rigid-or k i (yes _) = LT.rigid k i
  rigid-or k i (no _)  = LT.Void

mutual
  scrub : LT.Type → LT.Type
  scrub LT.Unit           = LT.Unit
  scrub LT.Void           = LT.Void
  scrub LT.Int            = LT.Int
  scrub LT.Float          = LT.Float
  scrub (A LT.* B)        = scrub A LT.* scrub B
  scrub (A LT.+ B)        = scrub A LT.+ scrub B
  scrub (A LT.⇒[ k ] B)   = scrub A LT.⇒[ k ] scrub B
  scrub (LT.μ-type F)     = LT.μ-type (scrubF F)
  scrub (LT.ν-type F φ)   = LT.ν-type (scrubF F) φ
  scrub (LT.rigid k i)    = rigid-or k i (bound? k i)

  scrubF : LT.Functor → LT.Functor
  scrubF (LT.K A)   = LT.K (scrub A)
  scrubF LT.Id      = LT.Id
  scrubF (F LT.⊕ G) = scrubF F LT.⊕ scrubF G
  scrubF (F LT.⊗ G) = scrubF F LT.⊗ scrubF G

private
  rigid-or-R : ∀ k i (d : Dec (Bound k i)) → Σ[ A′ ∈ ST.Ty m ] TyR Δ (rigid-or k i d) A′
  rigid-or-R k i (yes (j , e , κ)) = ST.var j , r-rigid j e κ
  rigid-or-R k i (no _)            = ST.Void , r-void

  rigid-or-id : ∀ {k i j} → toℕ j ≡ i → Δ j ≡ kindS k → ∀ d → rigid-or k i d ≡ LT.rigid k i
  rigid-or-id e κ (yes _)  = refl
  rigid-or-id e κ (no ¬b)  = ⊥-elim (¬b (_ , e , κ))

mutual
  scrub-R : ∀ A → Σ[ A′ ∈ ST.Ty m ] TyR Δ (scrub A) A′
  scrub-R LT.Unit  = _ , r-unit
  scrub-R LT.Void  = _ , r-void
  scrub-R LT.Int   = _ , r-int
  scrub-R LT.Float = _ , r-float
  scrub-R (A LT.* B) = _ , r-* (proj₂ (scrub-R A)) (proj₂ (scrub-R B))
  scrub-R (A LT.+ B) = _ , r-+ (proj₂ (scrub-R A)) (proj₂ (scrub-R B))
  scrub-R (A LT.⇒[ k ] B) = _ , r-⇒ refl (proj₂ (scrub-R A)) (proj₂ (scrub-R B))
  scrub-R (LT.μ-type F) = _ , r-μ (proj₂ (scrubF-R F))
  scrub-R (LT.ν-type F φ) = _ , r-ν refl (proj₂ (scrubF-R F))
  scrub-R (LT.rigid k i) = rigid-or-R k i (bound? k i)

  scrubF-R : ∀ F → Σ[ F′ ∈ ST.Fun m ] FunR Δ (scrubF F) F′
  scrubF-R (LT.K A)   = _ , r-K (proj₂ (scrub-R A))
  scrubF-R LT.Id      = _ , r-Id
  scrubF-R (F LT.⊕ G) = _ , r-⊕ (proj₂ (scrubF-R F)) (proj₂ (scrubF-R G))
  scrubF-R (F LT.⊗ G) = _ , r-⊗ (proj₂ (scrubF-R F)) (proj₂ (scrubF-R G))

mutual
  scrub-id : ∀ {A A′} → TyR Δ A A′ → scrub A ≡ A
  scrub-id r-unit    = refl
  scrub-id r-void    = refl
  scrub-id r-int     = refl
  scrub-id r-float   = refl
  scrub-id (r-* a b) = cong₂ LT._*_ (scrub-id a) (scrub-id b)
  scrub-id (r-+ a b) = cong₂ LT._+_ (scrub-id a) (scrub-id b)
  scrub-id (r-⇒ {k = k} _ a b) = cong₂ (λ x y → x LT.⇒[ k ] y) (scrub-id a) (scrub-id b)
  scrub-id (r-μ f)   = cong LT.μ-type (scrubF-id f)
  scrub-id (r-ν {φ = φ} _ f) = cong (λ G → LT.ν-type G φ) (scrubF-id f)
  scrub-id (r-rigid {k} {i} j e κ) = rigid-or-id e κ (bound? k i)

  scrubF-id : ∀ {F F′} → FunR Δ F F′ → scrubF F ≡ F
  scrubF-id (r-K a)   = cong LT.K (scrub-id a)
  scrubF-id r-Id      = refl
  scrubF-id (r-⊕ f g) = cong₂ LT._⊕_ (scrubF-id f) (scrubF-id g)
  scrubF-id (r-⊗ f g) = cong₂ LT._⊗_ (scrubF-id f) (scrubF-id g)

-- A related type below a type stays below the type made related.
scrub-<: : ∀ {A A′ C} → TyR Δ A A′ → A LS.<:ᶜ C → A LS.<:ᶜ scrub C
scrub-<: r LS.subᶜ-void = LS.subᶜ-void
scrub-<: r LS.subᶜ-unit = LS.subᶜ-unit
scrub-<: r LS.subᶜ-int = LS.subᶜ-int
scrub-<: r LS.subᶜ-float = LS.subᶜ-float
scrub-<: (r-⇒ _ ra rb) (LS.subᶜ-arr b p) =
  subst (λ X → _ LS.<:ᶜ (X LT.⇒[ _ ] _)) (sym (scrub-id ra)) (LS.subᶜ-arr (scrub-<: rb b) p)
scrub-<: (r-* ra rb) (LS.subᶜ-prod a b) = LS.subᶜ-prod (scrub-<: ra a) (scrub-<: rb b)
scrub-<: (r-+ ra rb) (LS.subᶜ-sum a b) = LS.subᶜ-sum (scrub-<: ra a) (scrub-<: rb b)
scrub-<: (r-μ f) LS.subᶜ-μ = subst (λ G → _ LS.<:ᶜ LT.μ-type G) (sym (scrubF-id f)) LS.subᶜ-μ
scrub-<: (r-ν _ f) (LS.subᶜ-ν p) = subst (λ G → _ LS.<:ᶜ LT.ν-type G _) (sym (scrubF-id f)) (LS.subᶜ-ν p)
scrub-<: r@(r-rigid _ _ _) LS.subᶜ-rigid = subst (λ X → _ LS.<:ᶜ X) (sym (scrub-id r)) LS.subᶜ-rigid

------------------------------------------------------------------------
-- Joins, both ways
------------------------------------------------------------------------

-- The join of related types is related, and is the Spec's join of theirs.
join-S : ∀ {A B C A′ B′} → A LS.⊔ B ≔ C → TyR Δ A A′ → TyR Δ B B′
       → Σ[ C′ ∈ ST.Ty m ] (TyR Δ C C′ × A′ SS.⊔ B′ ≔ C′)
join-S {C = C} J ra rb = C′ , rc , record
  { left  = subᶜ-S (LS._⊔_≔_.left J) ra rc
  ; right = subᶜ-S (LS._⊔_≔_.right J) rb rc
  ; least = λ {D} da db → let (D₀ , rd) = back D in
              subᶜ-S (LS._⊔_≔_.least J (subᶜ-L da ra rd) (subᶜ-L db rb rd)) rc rd
  }
  where
    up : C LS.<:ᶜ scrub C
    up = LS._⊔_≔_.least J (scrub-<: ra (LS._⊔_≔_.left J)) (scrub-<: rb (LS._⊔_≔_.right J))
    C′ = proj₁ (below-R up (proj₂ (scrub-R C)))
    rc = proj₂ (below-R up (proj₂ (scrub-R C)))

------------------------------------------------------------------------
-- The types the surface rules read off
------------------------------------------------------------------------

-- A functor applied.
⟦⟧-R : ∀ {F F′ A A′} → FunR Δ F F′ → TyR Δ A A′ → TyR Δ (LT.⟦ F ⟧T A) (ST.⟦ F′ ⟧F A′)
⟦⟧-R (r-K b)   a = b
⟦⟧-R r-Id      a = a
⟦⟧-R (r-⊕ f g) a = r-+ (⟦⟧-R f a) (⟦⟧-R g a)
⟦⟧-R (r-⊗ f g) a = r-* (⟦⟧-R f a) (⟦⟧-R g a)

-- An annotation's type (a surface type, so ground: read at any instance).
mutual
  annot-R : ∀ {T} (σ : ST.TySub 0 m) → LW.RigidFree T → TyR Δ T (toTy T ST.⟨ σ ⟩)
  annot-R σ LW.rf-Unit   = r-unit
  annot-R σ LW.rf-Void   = r-void
  annot-R σ LW.rf-Int    = r-int
  annot-R σ LW.rf-Float  = r-float
  annot-R σ (LW.rf-* a b) = r-* (annot-R σ a) (annot-R σ b)
  annot-R σ (LW.rf-+ a b) = r-+ (annot-R σ a) (annot-R σ b)
  annot-R σ (LW.rf-⇒ a b) = r-⇒ refl (annot-R σ a) (annot-R σ b)
  annot-R σ (LW.rf-μ f)   = r-μ (annotF-R σ f)
  annot-R σ (LW.rf-ν f)   = r-ν refl (annotF-R σ f)

  annotF-R : ∀ {F} (σ : ST.TySub 0 m) → LW.RigidFreeF F → FunR Δ F (toFun F ST.⟨ σ ⟩F)
  annotF-R σ (LW.rf-K a)   = r-K (annot-R σ a)
  annotF-R σ LW.rf-Id      = r-Id
  annotF-R σ (LW.rf-⊕ f g) = r-⊕ (annotF-R σ f) (annotF-R σ g)
  annotF-R σ (LW.rf-⊗ f g) = r-⊗ (annotF-R σ f) (annotF-R σ g)

-- A declaration's type.
base-R : ∀ {A} → LW.IsBaseType A → LW.RigidFree A → TyR Δ A ⌜ toB A ⌝
base-R LW.base-Unit  _ = r-unit
base-R LW.base-Void  _ = r-void
base-R LW.base-Int   _ = r-int
base-R LW.base-Float _ = r-float
base-R (LW.base-Prod a b) (LW.rf-* ra rb) = r-* (base-R a ra) (base-R b rb)
base-R (LW.base-Sum a b)  (LW.rf-+ ra rb) = r-+ (base-R a ra) (base-R b rb)
base-R LW.base-rigid ()

decl-R : ∀ {A} → LW.IsConcrete A → LH.HonestFFI A → LW.RigidFree A → TyR Δ A ⌜ declS A ⌝ᵈ
decl-R {A LT.⇒[ LG.mk-kind q LG.pure ] B} (LW.con-fun a b) h (LW.rf-⇒ ra rb) = r-⇒ refl (base-R a ra) (base-R b rb)
decl-R {A LT.⇒[ LG.mk-kind q LG.act ] B}  (LW.con-fun a b) h (LW.rf-⇒ ra rb) = r-⇒ refl (base-R a ra) (base-R b rb)
decl-R {A LT.⇒[ LG.mk-kind LG.Zero LG.eff ] B} _ () _
decl-R {A LT.⇒[ LG.mk-kind LG.One  LG.eff ] B} _ () _
decl-R {A LT.⇒[ LG.mk-kind LG.Many LG.eff ] B} _ () _
decl-R (LW.con-base LW.base-Unit) () _
decl-R (LW.con-base LW.base-Void) () _
decl-R (LW.con-base LW.base-Int) _ _ = r-int
decl-R (LW.con-base LW.base-Float) _ _ = r-float
decl-R (LW.con-base b@(LW.base-Prod _ _)) _ r = base-R b r
decl-R (LW.con-base b@(LW.base-Sum _ _)) _ r = base-R b r
decl-R (LW.con-base LW.base-rigid) () _

-- An effectful grade.
eff-S : ∀ {π} → LG.EffGrade π → SG.EffGrade (πS π)
eff-S LG.eg-act = SG.eg-act
eff-S LG.eg-eff = SG.eg-eff
