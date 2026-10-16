-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Type.Rigid — facts and deciders about kinded instances.
--
-- Parameters, kinds and kinded instances are the Spec's
-- (`Once.Lang.Type.Instance`). This module proves that a ground schema is its
-- own kinded instance and decides `KindedInstance`.
------------------------------------------------------------------------

module Once.Type.Rigid where

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Data.String using (String; _≟_)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Nullary using (yes; no)
open import Data.List.Membership.Propositional using (_∈_)

open import Once.Lang.Type.Grade
open import Once.Lang.Type
open import Once.Lang.Type.Poly
open import Once.Type
open import Once.Lang.Type.WellFormed using (IsBaseType; RigidFree; RigidFreeF; rf-Unit; rf-Void; rf-Int; rf-Float; rf-*; rf-+; rf-⇒; rf-μ; rf-ν; rf-K; rf-Id; rf-⊕; rf-⊗)
open import Once.Lang.Type.Instance

------------------------------------------------------------------------
-- A ground schema is its own (unique) kinded instance
------------------------------------------------------------------------

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (refl; cong; cong₂)
open import Data.List.Membership.Propositional.Properties using (∈-++⁻)
open import Data.List.Relation.Unary.Any using (here; there)

mutual
  subst-ground : ∀ θ (A : PolyType) (g : Ground A) → substPoly θ A ≡ extractGround A g
  subst-ground θ (PTVar _) ()
  subst-ground θ PUnit   _ = refl
  subst-ground θ PVoid   _ = refl
  subst-ground θ PInt    _ = refl
  subst-ground θ PFloat  _ = refl
  subst-ground θ (A P* B) (gA , gB) = cong₂ _*_ (subst-ground θ A gA) (subst-ground θ B gB)
  subst-ground θ (A P+ B) (gA , gB) = cong₂ _+_ (subst-ground θ A gA) (subst-ground θ B gB)
  subst-ground θ (A P⇒[ q ] B) (gA , gB) =
    cong₂ (λ a b → a ⇒[ mk-kind q pure ] b) (subst-ground θ A gA) (subst-ground θ B gB)
  subst-ground θ (PEff A B) (gA , gB) =
    cong₂ (λ a b → a ⇒[ mk-kind Many eff ] b) (subst-ground θ A gA) (subst-ground θ B gB)
  subst-ground θ (PAct A B) (gA , gB) =
    cong₂ (λ a b → a ⇒[ mk-kind Many act ] b) (subst-ground θ A gA) (subst-ground θ B gB)
  subst-ground θ (Pμ-type F) g = cong μ-type (subst-groundF θ F g)
  subst-ground θ (Pν-type F π) g = cong (λ G → ν-type G π) (subst-groundF θ F g)

  subst-groundF : ∀ θ (F : PolyFunctor) (g : GroundF F) → substPolyF θ F ≡ extractGroundF F g
  subst-groundF θ (PK A) g = cong K (subst-ground θ A g)
  subst-groundF θ PId _ = refl
  subst-groundF θ (F P⊕ G) (gF , gG) = cong₂ _⊕_ (subst-groundF θ F gF) (subst-groundF θ G gG)
  subst-groundF θ (F P⊗ G) (gF , gG) = cong₂ _⊗_ (subst-groundF θ F gF) (subst-groundF θ G gG)

private
  ++-⊥ : ∀ {x} (xs ys : List String) → (x ∈ xs → ⊥) → (x ∈ ys → ⊥) → x ∈ xs ++ ys → ⊥
  ++-⊥ xs ys nx ny m with ∈-++⁻ xs m
  ... | inj₁ p = nx p
  ... | inj₂ p = ny p

mutual
  ftv-ground : ∀ (A : PolyType) → Ground A → ∀ {x} → x ∈ ftv A → ⊥
  ftv-ground (PTVar _) ()
  ftv-ground PUnit   _ ()
  ftv-ground PVoid   _ ()
  ftv-ground PInt    _ ()
  ftv-ground PFloat  _ ()
  ftv-ground (A P* B) (gA , gB) = ++-⊥ (ftv A) (ftv B) (ftv-ground A gA) (ftv-ground B gB)
  ftv-ground (A P+ B) (gA , gB) = ++-⊥ (ftv A) (ftv B) (ftv-ground A gA) (ftv-ground B gB)
  ftv-ground (A P⇒[ _ ] B) (gA , gB) = ++-⊥ (ftv A) (ftv B) (ftv-ground A gA) (ftv-ground B gB)
  ftv-ground (PEff A B) (gA , gB) = ++-⊥ (ftv A) (ftv B) (ftv-ground A gA) (ftv-ground B gB)
  ftv-ground (PAct A B) (gA , gB) = ++-⊥ (ftv A) (ftv B) (ftv-ground A gA) (ftv-ground B gB)
  ftv-ground (Pμ-type F) g = ftvF-ground F g
  ftv-ground (Pν-type F _) g = ftvF-ground F g

  ftvF-ground : ∀ (F : PolyFunctor) → GroundF F → ∀ {x} → x ∈ ftvF F → ⊥
  ftvF-ground (PK A) g = ftv-ground A g
  ftvF-ground PId _ ()
  ftvF-ground (F P⊕ G) (gF , gG) = ++-⊥ (ftvF F) (ftvF G) (ftvF-ground F gF) (ftvF-ground G gG)
  ftvF-ground (F P⊗ G) (gF , gG) = ++-⊥ (ftvF F) (ftvF G) (ftvF-ground F gF) (ftvF-ground G gG)

mutual
  ftvK-ground : ∀ (A : PolyType) → Ground A → ∀ {x} → x ∈ ftvK A → ⊥
  ftvK-ground (PTVar _) ()
  ftvK-ground PUnit   _ ()
  ftvK-ground PVoid   _ ()
  ftvK-ground PInt    _ ()
  ftvK-ground PFloat  _ ()
  ftvK-ground (A P* B) (gA , gB) = ++-⊥ (ftvK A) (ftvK B) (ftvK-ground A gA) (ftvK-ground B gB)
  ftvK-ground (A P+ B) (gA , gB) = ++-⊥ (ftvK A) (ftvK B) (ftvK-ground A gA) (ftvK-ground B gB)
  ftvK-ground (A P⇒[ _ ] B) (gA , gB) = ++-⊥ (ftvK A) (ftvK B) (ftvK-ground A gA) (ftvK-ground B gB)
  ftvK-ground (PEff A B) (gA , gB) = ++-⊥ (ftvK A) (ftvK B) (ftvK-ground A gA) (ftvK-ground B gB)
  ftvK-ground (PAct A B) (gA , gB) = ++-⊥ (ftvK A) (ftvK B) (ftvK-ground A gA) (ftvK-ground B gB)
  ftvK-ground (Pμ-type F) g = ftvKF-ground F g
  ftvK-ground (Pν-type F _) g = ftvKF-ground F g

  ftvKF-ground : ∀ (F : PolyFunctor) → GroundF F → ∀ {x} → x ∈ ftvKF F → ⊥
  ftvKF-ground (PK A) g = ftv-ground A g
  ftvKF-ground PId _ ()
  ftvKF-ground (F P⊕ G) (gF , gG) = ++-⊥ (ftvKF F) (ftvKF G) (ftvKF-ground F gF) (ftvKF-ground G gG)
  ftvKF-ground (F P⊗ G) (gF , gG) = ++-⊥ (ftvKF F) (ftvKF G) (ftvKF-ground F gF) (ftvKF-ground G gG)

ground-kinded : (A : PolyType) (g : Ground A) → KindedInstance A (extractGround A g)
ground-kinded A g = (λ _ → Unit) , subst-ground _ A g , λ m → ⊥-elim (ftvK-ground A g m)

------------------------------------------------------------------------
-- Deciding a kinded instance (what the elaborator runs at a use)
------------------------------------------------------------------------

open import Relation.Nullary using (Dec)
open import Relation.Binary.PropositionalEquality using (sym; trans; subst)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ; ∈-++⁺ʳ)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (proj₂)
open import Once.Type.Match using (instantiate)
open import Once.Type.Instance using (instantiate-sound; instantiate-complete)
open import Once.Type.Determined using (agree-from)
open import Once.Functor.Decide using (isBaseType?; isBaseType?-complete)

-- The base-kinded variables are variables.
mutual
  ftvK⊆ftv : ∀ (A : PolyType) {x} → x ∈ ftvK A → x ∈ ftv A
  ftvK⊆ftv (PTVar _) ()
  ftvK⊆ftv PUnit ()
  ftvK⊆ftv PVoid ()
  ftvK⊆ftv PInt ()
  ftvK⊆ftv PFloat ()
  ftvK⊆ftv (A P* B) m = ++-mono (ftvK A) (ftv A) (ftvK⊆ftv A) (ftvK⊆ftv B) m
  ftvK⊆ftv (A P+ B) m = ++-mono (ftvK A) (ftv A) (ftvK⊆ftv A) (ftvK⊆ftv B) m
  ftvK⊆ftv (A P⇒[ _ ] B) m = ++-mono (ftvK A) (ftv A) (ftvK⊆ftv A) (ftvK⊆ftv B) m
  ftvK⊆ftv (PEff A B) m = ++-mono (ftvK A) (ftv A) (ftvK⊆ftv A) (ftvK⊆ftv B) m
  ftvK⊆ftv (PAct A B) m = ++-mono (ftvK A) (ftv A) (ftvK⊆ftv A) (ftvK⊆ftv B) m
  ftvK⊆ftv (Pμ-type F) m = ftvKF⊆ftvF F m
  ftvK⊆ftv (Pν-type F _) m = ftvKF⊆ftvF F m

  ftvKF⊆ftvF : ∀ (F : PolyFunctor) {x} → x ∈ ftvKF F → x ∈ ftvF F
  ftvKF⊆ftvF (PK A) m = m
  ftvKF⊆ftvF PId ()
  ftvKF⊆ftvF (F P⊕ G) m = ++-mono (ftvKF F) (ftvF F) (ftvKF⊆ftvF F) (ftvKF⊆ftvF G) m
  ftvKF⊆ftvF (F P⊗ G) m = ++-mono (ftvKF F) (ftvF F) (ftvKF⊆ftvF F) (ftvKF⊆ftvF G) m

  ++-mono : ∀ {x} (xs xs′ : List String) {ys ys′ : List String}
          → (∀ {y} → y ∈ xs → y ∈ xs′) → (∀ {y} → y ∈ ys → y ∈ ys′) → x ∈ xs ++ ys → x ∈ xs′ ++ ys′
  ++-mono xs xs′ f g m with ∈-++⁻ xs m
  ... | inj₁ p = ∈-++⁺ˡ (f p)
  ... | inj₂ p = ∈-++⁺ʳ xs′ (g p)

-- Every listed variable is sent to a base type.
AllBase : (String → Type) → List String → Set
AllBase θ xs = ∀ {x} → x ∈ xs → IsBaseType (θ x)

allBase? : ∀ θ xs → Dec (AllBase θ xs)
allBase? θ [] = yes (λ ())
allBase? θ (x ∷ xs) with isBaseType? (θ x) in eqb | allBase? θ xs
... | just b  | yes h = yes λ { (here refl) → b ; (there m) → h m }
... | just _  | no ¬h = no λ h → ¬h (λ m → h (there m))
... | nothing | _     = no λ h → nothing≢just (trans (sym eqb) (proj₂ (isBaseType?-complete (h (here refl)))))
  where
    nothing≢just : ∀ {A : Set} {a : A} → nothing ≡ just a → ⊥
    nothing≢just ()

kindedInstance? : ∀ (s : PolyType) (T : Type) → Dec (KindedInstance s T)
kindedInstance? s T with instantiate s T in eqi
... | nothing = no λ (θ , e , _) → absurd (trans (sym eqi) (proj₂ (instantiate-complete s T (θ , e))))
  where
    absurd : ∀ {σ} → nothing ≡ just σ → ⊥
    absurd ()
... | just σ with instantiate-sound s T eqi
...   | θ , e with allBase? θ (ftvK s)
...     | yes h = yes (θ , e , h)
...     | no ¬h = no λ (θ′ , e′ , h′) →
            ¬h (λ {x} m → subst IsBaseType (sym (agree-from θ θ′ s (trans e (sym e′)) (ftvK⊆ftv s m))) (h′ m))

private
  both : ∀ {X Y Z : Set} → (X → Y → Z) → Maybe X → Maybe Y → Maybe Z
  both f (just x) (just y) = just (f x y)
  {-# CATCHALL #-}
  both f _        _        = nothing

  one : ∀ {X Z : Set} → (X → Z) → Maybe X → Maybe Z
  one f (just x) = just (f x)
  one f nothing  = nothing

mutual
  rigidFree? : (A : Type) → Maybe (RigidFree A)
  rigidFree? Unit         = just rf-Unit
  rigidFree? Void         = just rf-Void
  rigidFree? Int          = just rf-Int
  rigidFree? Float        = just rf-Float
  rigidFree? (A * B)      = both rf-* (rigidFree? A) (rigidFree? B)
  rigidFree? (A + B)      = both rf-+ (rigidFree? A) (rigidFree? B)
  rigidFree? (A ⇒[ k ] B) = both rf-⇒ (rigidFree? A) (rigidFree? B)
  rigidFree? (μ-type F)   = one rf-μ (rigidFreeF? F)
  rigidFree? (ν-type F π) = one rf-ν (rigidFreeF? F)
  rigidFree? (rigid _ _)  = nothing

  rigidFreeF? : (F : Functor) → Maybe (RigidFreeF F)
  rigidFreeF? (K A)   = one rf-K (rigidFree? A)
  rigidFreeF? Id      = just rf-Id
  rigidFreeF? (F ⊕ G) = both rf-⊕ (rigidFreeF? F) (rigidFreeF? G)
  rigidFreeF? (F ⊗ G) = both rf-⊗ (rigidFreeF? F) (rigidFreeF? G)

mutual
  rigidFree?-complete : ∀ {A} (r : RigidFree A) → rigidFree? A ≡ just r
  rigidFree?-complete rf-Unit   = refl
  rigidFree?-complete rf-Void   = refl
  rigidFree?-complete rf-Int    = refl
  rigidFree?-complete rf-Float  = refl
  rigidFree?-complete (rf-* a b) rewrite rigidFree?-complete a | rigidFree?-complete b = refl
  rigidFree?-complete (rf-+ a b) rewrite rigidFree?-complete a | rigidFree?-complete b = refl
  rigidFree?-complete (rf-⇒ a b) rewrite rigidFree?-complete a | rigidFree?-complete b = refl
  rigidFree?-complete (rf-μ f) rewrite rigidFreeF?-complete f = refl
  rigidFree?-complete (rf-ν f) rewrite rigidFreeF?-complete f = refl

  rigidFreeF?-complete : ∀ {F} (r : RigidFreeF F) → rigidFreeF? F ≡ just r
  rigidFreeF?-complete (rf-K a) rewrite rigidFree?-complete a = refl
  rigidFreeF?-complete rf-Id = refl
  rigidFreeF?-complete (rf-⊕ f g) rewrite rigidFreeF?-complete f | rigidFreeF?-complete g = refl
  rigidFreeF?-complete (rf-⊗ f g) rewrite rigidFreeF?-complete f | rigidFreeF?-complete g = refl

-- A ground schema's type mentions no parameter, so it is rigid-free (D252: a
-- ground instance may annotate).
mutual
  extractGround-rf : ∀ (A : PolyType) (g : Ground A) → RigidFree (extractGround A g)
  extractGround-rf (PTVar _)     ()
  extractGround-rf PUnit         _         = rf-Unit
  extractGround-rf PVoid         _         = rf-Void
  extractGround-rf PInt          _         = rf-Int
  extractGround-rf PFloat        _         = rf-Float
  extractGround-rf (A P* B)      (gA , gB) = rf-* (extractGround-rf A gA) (extractGround-rf B gB)
  extractGround-rf (A P+ B)      (gA , gB) = rf-+ (extractGround-rf A gA) (extractGround-rf B gB)
  extractGround-rf (A P⇒[ q ] B) (gA , gB) = rf-⇒ (extractGround-rf A gA) (extractGround-rf B gB)
  extractGround-rf (PEff A B)    (gA , gB) = rf-⇒ (extractGround-rf A gA) (extractGround-rf B gB)
  extractGround-rf (PAct A B)    (gA , gB) = rf-⇒ (extractGround-rf A gA) (extractGround-rf B gB)
  extractGround-rf (Pμ-type F)   g         = rf-μ (extractGroundF-rf F g)
  extractGround-rf (Pν-type F π) g         = rf-ν (extractGroundF-rf F g)

  extractGroundF-rf : ∀ (F : PolyFunctor) (g : GroundF F) → RigidFreeF (extractGroundF F g)
  extractGroundF-rf (PK A)   g         = rf-K (extractGround-rf A g)
  extractGroundF-rf PId      _         = rf-Id
  extractGroundF-rf (F P⊕ G) (gF , gG) = rf-⊕ (extractGroundF-rf F gF) (extractGroundF-rf G gG)
  extractGroundF-rf (F P⊗ G) (gF , gG) = rf-⊗ (extractGroundF-rf F gF) (extractGroundF-rf G gG)
