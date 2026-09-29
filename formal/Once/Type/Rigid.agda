-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Type.Rigid — D243 (plan 0.103 phase 6d): a schema's PARAMETERS, their
-- KINDS, its RIGID instance, and the KINDED instances a use may be at.
--
-- SPEC.
--   * The parameters of `∀ā.T` are its free variables in order of first
--     occurrence (`params`).
--   * A parameter is `k-base` iff it occurs inside a functor constant (`PK`):
--     there `WellFormedF` needs a base type at every instance. Every other
--     parameter is `k-any`. Kinds are read off the SCHEMA, never off a body.
--   * The body of `d : ∀ā.T` is typed ONCE, at `rigidOf T`: parameter `i`
--     held rigid as `rigid kᵢ i`, its position in the definition's telescope
--     (the core's `var i`; the DT POC's context variable).
--   * A use is at a KINDED instance: some `θ` with `substPoly θ T ≡ U` that
--     instantiates every base-kinded parameter at a base type.
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

open import Once.Type
open import Once.Functor.Translate using (IsBaseType)

------------------------------------------------------------------------
-- Parameters and kinds
------------------------------------------------------------------------

-- The variables occurring inside a functor constant: the base-kinded ones.
mutual
  ftvK : PolyType → List String
  ftvK (PTVar _)     = []
  ftvK PUnit         = []
  ftvK PVoid         = []
  ftvK PInt          = []
  ftvK PFloat        = []
  ftvK PStr          = []
  ftvK PBuffer       = []
  ftvK (A P* B)      = ftvK A ++ ftvK B
  ftvK (A P+ B)      = ftvK A ++ ftvK B
  ftvK (A P⇒[ _ ] B) = ftvK A ++ ftvK B
  ftvK (PEff A B)    = ftvK A ++ ftvK B
  ftvK (Pμ-type F)   = ftvKF F
  ftvK (Pν-type F _) = ftvKF F

  ftvKF : PolyFunctor → List String
  ftvKF (PK A)   = ftv A            -- everything under a constant is base
  ftvKF PId      = []
  ftvKF (F P⊕ G) = ftvKF F ++ ftvKF G
  ftvKF (F P⊗ G) = ftvKF F ++ ftvKF G

memberB : String → List String → Bool
memberB x []       = false
memberB x (y ∷ ys) with x ≟ y
... | yes _ = true
... | no  _ = memberB x ys

-- First occurrences, in order.
nub : List String → List String
nub = go []
  where
    go : List String → List String → List String
    go seen []       = []
    go seen (x ∷ xs) = if memberB x seen then go seen xs else x ∷ go (x ∷ seen) xs

params : PolyType → List String
params T = nub (ftv T)

arityOf : PolyType → ℕ
arityOf T = length (params T)

kindOf : PolyType → String → TKind
kindOf T x = if memberB x (ftvK T) then k-base else k-any

-- A parameter's position (its index in the definition's telescope).
indexOf : String → List String → ℕ
indexOf x []       = zero
indexOf x (y ∷ ys) with x ≟ y
... | yes _ = zero
... | no  _ = suc (indexOf x ys)

------------------------------------------------------------------------
-- The rigid instance: the type the body is checked at
------------------------------------------------------------------------

rigidSubst : PolyType → String → Type
rigidSubst T x = rigid (kindOf T x) (indexOf x (params T))

rigidOf : PolyType → Type
rigidOf T = substPoly (rigidSubst T) T

------------------------------------------------------------------------
-- Kinded instances: what a use may be at
------------------------------------------------------------------------

RespectsKinds : PolyType → (String → Type) → Set
RespectsKinds T θ = ∀ {x} → x ∈ ftvK T → IsBaseType (θ x)

KindedInstance : PolyType → Type → Set
KindedInstance T U = Σ[ θ ∈ (String → Type) ] (substPoly θ T ≡ U) × RespectsKinds T θ

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
  subst-ground θ PStr    _ = refl
  subst-ground θ PBuffer _ = refl
  subst-ground θ (A P* B) (gA , gB) = cong₂ _*_ (subst-ground θ A gA) (subst-ground θ B gB)
  subst-ground θ (A P+ B) (gA , gB) = cong₂ _+_ (subst-ground θ A gA) (subst-ground θ B gB)
  subst-ground θ (A P⇒[ q ] B) (gA , gB) =
    cong₂ (λ a b → a ⇒[ mk-kind q pure ] b) (subst-ground θ A gA) (subst-ground θ B gB)
  subst-ground θ (PEff A B) (gA , gB) =
    cong₂ (λ a b → a ⇒[ mk-kind Many eff ] b) (subst-ground θ A gA) (subst-ground θ B gB)
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
  ftv-ground PStr    _ ()
  ftv-ground PBuffer _ ()
  ftv-ground (A P* B) (gA , gB) = ++-⊥ (ftv A) (ftv B) (ftv-ground A gA) (ftv-ground B gB)
  ftv-ground (A P+ B) (gA , gB) = ++-⊥ (ftv A) (ftv B) (ftv-ground A gA) (ftv-ground B gB)
  ftv-ground (A P⇒[ _ ] B) (gA , gB) = ++-⊥ (ftv A) (ftv B) (ftv-ground A gA) (ftv-ground B gB)
  ftv-ground (PEff A B) (gA , gB) = ++-⊥ (ftv A) (ftv B) (ftv-ground A gA) (ftv-ground B gB)
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
  ftvK-ground PStr    _ ()
  ftvK-ground PBuffer _ ()
  ftvK-ground (A P* B) (gA , gB) = ++-⊥ (ftvK A) (ftvK B) (ftvK-ground A gA) (ftvK-ground B gB)
  ftvK-ground (A P+ B) (gA , gB) = ++-⊥ (ftvK A) (ftvK B) (ftvK-ground A gA) (ftvK-ground B gB)
  ftvK-ground (A P⇒[ _ ] B) (gA , gB) = ++-⊥ (ftvK A) (ftvK B) (ftvK-ground A gA) (ftvK-ground B gB)
  ftvK-ground (PEff A B) (gA , gB) = ++-⊥ (ftvK A) (ftvK B) (ftvK-ground A gA) (ftvK-ground B gB)
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

open import Relation.Nullary using (Dec; ¬_)
open import Relation.Binary.PropositionalEquality using (sym; trans; subst)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ; ∈-++⁺ʳ)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (proj₁; proj₂)
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
  ftvK⊆ftv PStr ()
  ftvK⊆ftv PBuffer ()
  ftvK⊆ftv (A P* B) m = ++-mono (ftvK A) (ftv A) (ftvK⊆ftv A) (ftvK⊆ftv B) m
  ftvK⊆ftv (A P+ B) m = ++-mono (ftvK A) (ftv A) (ftvK⊆ftv A) (ftvK⊆ftv B) m
  ftvK⊆ftv (A P⇒[ _ ] B) m = ++-mono (ftvK A) (ftv A) (ftvK⊆ftv A) (ftvK⊆ftv B) m
  ftvK⊆ftv (PEff A B) m = ++-mono (ftvK A) (ftv A) (ftvK⊆ftv A) (ftvK⊆ftv B) m
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
