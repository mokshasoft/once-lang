------------------------------------------------------------------------
-- Once.Functor.Base.Laws
--
-- Coinductive equational LAWS over the polynomial-functor kernel
-- (`Once.Functor.Base`), separated from the definitions module so the
-- denotational meaning can import the kernel *functions* without dragging
-- in the coalgebraic-extensionality axiom `bisimS-to-eq` (Plan 0.47 step 3).
--
-- Contents: the relational interpretation `⟦_⟧SF-rel`, the bisimulation
-- relation `_∼S_`, the `bisimS-to-eq` postulate (provable in Cubical Agda),
-- the relational-map lemmas, and the identity-anamorphism law `anaS-Out-id`.
------------------------------------------------------------------------

module Once.Functor.Base.Laws where

open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Once.Functor.Base

-- | Relational interpretation of semantic functors
--
-- Lifts a relation R : A → B → Set through functor structure.
-- Two F-structures are related if corresponding parts are related.
--
⟦_⟧SF-rel : (F : SFunctor) {A B : Set} (R : A → B → Set)
          → ⟦ F ⟧SF A → ⟦ F ⟧SF B → Set
⟦ SK _ ⟧SF-rel R x y = x ≡ y
⟦ SId ⟧SF-rel R x y = R x y
⟦ F S⊕ G ⟧SF-rel R (inj₁ x) (inj₁ y) = ⟦ F ⟧SF-rel R x y
⟦ F S⊕ G ⟧SF-rel R (inj₁ _) (inj₂ _) = ⊥
⟦ F S⊕ G ⟧SF-rel R (inj₂ _) (inj₁ _) = ⊥
⟦ F S⊕ G ⟧SF-rel R (inj₂ x) (inj₂ y) = ⟦ G ⟧SF-rel R x y
⟦ F S⊗ G ⟧SF-rel R (x₁ , x₂) (y₁ , y₂) = ⟦ F ⟧SF-rel R x₁ y₁ × ⟦ G ⟧SF-rel R x₂ y₂

-- | Bisimulation relation on νS F (coinductive)
--
-- Two coinductive values are bisimilar if their unfoldings are related
-- through the relational interpretation, with bisimilarity at recursive positions.
--
record _∼S_ {F : SFunctor} (x y : νS F) : Set where
  coinductive
  field
    unfoldS-∼ : ⟦ F ⟧SF-rel (_∼S_ {F}) (unfoldS x) (unfoldS y)

open _∼S_ public

-- | Bisimulation implies equality (coalgebraic extensionality)
--
-- This is a standard principle in coalgebra theory: bisimilar values are equal.
-- In Cubical Agda this can be proven; in standard Agda we postulate it.
--
postulate
  bisimS-to-eq : ∀ {F : SFunctor} (x y : νS F) → x ∼S y → x ≡ y

-- | sfmap preserves relational structure
--
-- If R relates recursive positions, then sfmap lifts R through F.
--
sfmap-rel : ∀ F {A B : Set} {R : A → B → Set} {f : A → A} {g : B → B}
          → (∀ a b → R a b → R (f a) (g b))
          → ∀ x y → ⟦ F ⟧SF-rel R x y → ⟦ F ⟧SF-rel R (sfmap F f x) (sfmap F g y)
sfmap-rel (SK _) pres x y r = r
sfmap-rel SId pres x y r = pres x y r
sfmap-rel (F S⊕ G) pres (inj₁ x) (inj₁ y) r = sfmap-rel F pres x y r
sfmap-rel (F S⊕ G) pres (inj₂ x) (inj₂ y) r = sfmap-rel G pres x y r
sfmap-rel (F S⊗ G) pres (x₁ , x₂) (y₁ , y₂) (r₁ , r₂) =
  sfmap-rel F pres x₁ y₁ r₁ , sfmap-rel G pres x₂ y₂ r₂

-- | sfmap f relates to identity when f relates to identity
--
sfmap-f-rel : ∀ F {A : Set} {R : A → A → Set} {f : A → A}
            → (∀ a → R (f a) a)
            → ∀ x → ⟦ F ⟧SF-rel R (sfmap F f x) x
sfmap-f-rel (SK _) hyp x = refl
sfmap-f-rel SId hyp x = hyp x
sfmap-f-rel (F S⊕ G) hyp (inj₁ x) = sfmap-f-rel F hyp x
sfmap-f-rel (F S⊕ G) hyp (inj₂ x) = sfmap-f-rel G hyp x
sfmap-f-rel (F S⊗ G) hyp (x₁ , x₂) = sfmap-f-rel F hyp x₁ , sfmap-f-rel G hyp x₂

-- | anaS unfoldS is bisimilar to id (coinductive proof)
--
-- D062: guardedness-CHECKED (global `--guardedness`). The dual mutual
-- `sfmapAna-bisim` places the corecursive `anaS-unfoldS-bisim` call structurally
-- at `SId`, so Agda sees the guard with no termination-pragma assertion.
mutual
  anaS-unfoldS-bisim : ∀ {F : SFunctor} (x : νS F) → anaS {F} unfoldS x ∼S x
  unfoldS-∼ (anaS-unfoldS-bisim {F} x) = sfmapAna-bisim F (unfoldS x)

  sfmapAna-bisim : ∀ {F : SFunctor} (H : SFunctor) (v : ⟦ H ⟧SF (νS F))
                 → ⟦ H ⟧SF-rel (_∼S_ {F}) (sfmapAna H unfoldS v) v
  sfmapAna-bisim (SK _)     v        = refl
  sfmapAna-bisim SId        v        = anaS-unfoldS-bisim v
  sfmapAna-bisim (H₁ S⊕ H₂) (inj₁ v) = sfmapAna-bisim H₁ v
  sfmapAna-bisim (H₁ S⊕ H₂) (inj₂ v) = sfmapAna-bisim H₂ v
  sfmapAna-bisim (H₁ S⊗ H₂) (v₁ , v₂) = sfmapAna-bisim H₁ v₁ , sfmapAna-bisim H₂ v₂

-- | Identity anamorphism: anaS unfoldS ≡ id (PROVEN via bisimulation)
anaS-Out-id : ∀ (F : SFunctor) (x : νS F) → anaS {F} unfoldS x ≡ x
anaS-Out-id F x = bisimS-to-eq (anaS unfoldS x) x (anaS-unfoldS-bisim x)
