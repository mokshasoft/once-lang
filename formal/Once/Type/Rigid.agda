-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Type.Rigid — facts and deciders about kinded instances.
--
-- Parameters, kinds and kinded instances are the Spec's
-- (`Once.Internal.Type.Instance`). This module proves that a ground schema is its
-- own kinded instance and decides `KindedInstance`.
------------------------------------------------------------------------

module Once.Type.Rigid where

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Once.Spec.Type using (Base; ∅ₖ)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Data.String using (String; _≟_)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Nullary using (yes; no)
open import Data.List.Membership.Propositional using (_∈_)

open import Once.Spec.Grade
open import Once.Type.Grade
open import Once.Internal.Type
open import Once.Spec.Type using (Fun; μ; ν)
open import Once.Spec.Type using (Ty; KCtx; Base; Type; Unit; Void; _*_; _+_; _⇒[_]_; Int; Float; K; Id; _⊕_; _⊗_)
open import Once.Spec.Surface.Syntax using (PolyType; PolyFunctor; PK; PId; _P⊕_; _P⊗_; PUnit; PVoid; _P*_; _P+_; _P⇒[_]_; PEff; PAct; Pμ; Pν; PInt; PFloat; PTVar)
open import Once.Internal.Type.Poly
open import Once.Type
open import Once.Internal.Type.Instance

------------------------------------------------------------------------
-- A ground schema is its own (unique) kinded instance
------------------------------------------------------------------------

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (refl; cong; cong₂)
open import Data.List.Membership.Propositional.Properties using (∈-++⁻)
open import Data.List.Relation.Unary.Any using (here; there)

mutual
  subst-ground : ∀ {m} (θ : String → Ty m) (A : PolyType) (g : Ground A) → substPoly θ A ≡ extractGround A g
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
  subst-ground θ (Pμ F) g = cong μ (subst-groundF θ F g)
  subst-ground θ (Pν F π) g = cong (λ G → ν G π) (subst-groundF θ F g)

  subst-groundF : ∀ {m} (θ : String → Ty m) (F : PolyFunctor) (g : GroundF F) → substPolyF θ F ≡ extractGroundF F g
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
  ftv-ground (Pμ F) g = ftvF-ground F g
  ftv-ground (Pν F _) g = ftvF-ground F g

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
  ftvK-ground (Pμ F) g = ftvKF-ground F g
  ftvK-ground (Pν F _) g = ftvKF-ground F g

  ftvKF-ground : ∀ (F : PolyFunctor) → GroundF F → ∀ {x} → x ∈ ftvKF F → ⊥
  ftvKF-ground (PK A) g = ftv-ground A g
  ftvKF-ground PId _ ()
  ftvKF-ground (F P⊕ G) (gF , gG) = ++-⊥ (ftvKF F) (ftvKF G) (ftvKF-ground F gF) (ftvKF-ground G gG)
  ftvKF-ground (F P⊗ G) (gF , gG) = ++-⊥ (ftvKF F) (ftvKF G) (ftvKF-ground F gF) (ftvKF-ground G gG)

ground-kinded : ∀ {m} {Δ : KCtx m} (A : PolyType) (g : Ground A) → KindedInstance Δ A (extractGround A g)
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
open import Once.Functor.Decide using (base?; base?-complete; isBaseType?; isBaseType?-complete)

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
  ftvK⊆ftv (Pμ F) m = ftvKF⊆ftvF F m
  ftvK⊆ftv (Pν F _) m = ftvKF⊆ftvF F m

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
AllBase : ∀ {m} → KCtx m → (String → Ty m) → List String → Set
AllBase Δ θ xs = ∀ {x} → x ∈ xs → Base Δ (θ x)

allBase? : ∀ {m} (Δ : KCtx m) θ xs → Dec (AllBase Δ θ xs)
allBase? Δ θ [] = yes (λ ())
allBase? Δ θ (x ∷ xs) with base? Δ (θ x) in eqb | allBase? Δ θ xs
... | just b  | yes h = yes λ { (here refl) → b ; (there m) → h m }
... | just _  | no ¬h = no λ h → ¬h (λ m → h (there m))
... | nothing | _     = no λ h → nothing≢just (trans (sym eqb) (proj₂ (base?-complete (h (here refl)))))
  where
    nothing≢just : ∀ {A : Set} {a : A} → nothing ≡ just a → ⊥
    nothing≢just ()

kindedInstance? : ∀ {m} (Δ : KCtx m) (s : PolyType) (T : Ty m) → Dec (KindedInstance Δ s T)
kindedInstance? Δ s T with instantiate s T in eqi
... | nothing = no λ (θ , e , _) → absurd (trans (sym eqi) (proj₂ (instantiate-complete s T (θ , e))))
  where
    absurd : ∀ {σ} → nothing ≡ just σ → ⊥
    absurd ()
... | just σ with instantiate-sound s T eqi
...   | θ , e with allBase? Δ θ (ftvK s)
...     | yes h = yes (θ , e , h)
...     | no ¬h = no λ (θ′ , e′ , h′) →
            ¬h (λ {x} m → subst (Base Δ) (sym (agree-from θ θ′ s (trans e (sym e′)) (ftvK⊆ftv s m))) (h′ m))

