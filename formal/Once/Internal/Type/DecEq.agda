-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Internal.Type.DecEq — decidable equality of the grades, kinds, functors
-- and types.
--
-- INTERNAL (D333): decision procedures.
------------------------------------------------------------------------

module Once.Internal.Type.DecEq where

open import Relation.Binary.Definitions using (DecidableEquality)

open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Once.Spec.Type using (Ty; Fun; var; Type; K; Id; _⊕_; _⊗_; Unit; Void; Int; Float; _⇒[_]_)
open import Once.Internal.Type using (Functor; μ-type; ν-type; TKind; k-base; k-any)
open import Once.Spec.Grade using (Quantity; Zero; One; Many; Purity; Finite; pureᶠ; actᶠ; pure; act; eff; ArrowKind; mk-kind)
import Data.Fin as Fin

-- Quantities, purities, kinds.

_≟q_ : DecidableEquality Quantity
Zero ≟q Zero = yes refl
Zero ≟q One = no λ ()
Zero ≟q Many = no λ ()
One ≟q Zero = no λ ()
One ≟q One = yes refl
One ≟q Many = no λ ()
Many ≟q Zero = no λ ()
Many ≟q One = no λ ()
Many ≟q Many = yes refl

-- | …and on a stream's finite grade (D318).
_≟f_ : DecidableEquality Finite
pureᶠ ≟f pureᶠ = yes refl
pureᶠ ≟f actᶠ  = no (λ ())
actᶠ  ≟f pureᶠ = no (λ ())
actᶠ  ≟f actᶠ  = yes refl

-- | Decidable equality on Purity (plan 0.5.1)
_≟p_ : DecidableEquality Purity
pure ≟p pure = yes refl
pure ≟p act = no (λ ())
pure ≟p eff = no (λ ())
act ≟p pure = no (λ ())
act ≟p act = yes refl
act ≟p eff = no (λ ())
eff ≟p pure = no (λ ())
eff ≟p act = no (λ ())
eff ≟p eff = yes refl

-- | Decidable equality on ArrowKind (plan 0.5.1)
≟k-aux : ∀ {q₁ q₂ p₁ p₂}
       → Dec (q₁ ≡ q₂) → Dec (p₁ ≡ p₂)
       → Dec (mk-kind q₁ p₁ ≡ mk-kind q₂ p₂)
-- `no` in EITHER column decides, without splitting the other. See the note on
-- `≟T-⇒-aux`: a decider that insists on both columns goes stuck on variables and
-- hides the decisions underneath it from a proof's `with`.
≟k-aux (no ¬q)    _          = no λ { refl → ¬q refl }
{-# CATCHALL #-}
≟k-aux _          (no ¬p)    = no λ { refl → ¬p refl }
≟k-aux (yes refl) (yes refl) = yes refl

_≟k_ : DecidableEquality ArrowKind
mk-kind q₁ p₁ ≟k mk-kind q₂ p₂ = ≟k-aux (q₁ ≟q q₂) (p₁ ≟p p₂)


-- Helpers for ≟T / ≟F matching-constructor cases (avoid `with`-blocks).

≟F-K-aux : ∀ {m} {A B : Ty m} → Dec (A ≡ B) → Dec (K A ≡ K B)
≟F-K-aux (yes refl) = yes refl
≟F-K-aux (no ¬p)    = no λ { refl → ¬p refl }

≟F-⊕-aux : ∀ {m} {F₁ G₁ F₂ G₂ : Fun m}
         → Dec (F₁ ≡ F₂) → Dec (G₁ ≡ G₂)
         → Dec ((F₁ ⊕ G₁) ≡ (F₂ ⊕ G₂))
≟F-⊕-aux (yes refl) (yes refl) = yes refl
≟F-⊕-aux (yes refl) (no ¬q)    = no λ { refl → ¬q refl }
≟F-⊕-aux (no ¬p)    (yes _)    = no λ { refl → ¬p refl }
≟F-⊕-aux (no ¬p)    (no _)     = no λ { refl → ¬p refl }

≟F-⊗-aux : ∀ {m} {F₁ G₁ F₂ G₂ : Fun m}
         → Dec (F₁ ≡ F₂) → Dec (G₁ ≡ G₂)
         → Dec ((F₁ ⊗ G₁) ≡ (F₂ ⊗ G₂))
≟F-⊗-aux (yes refl) (yes refl) = yes refl
≟F-⊗-aux (yes refl) (no ¬q)    = no λ { refl → ¬q refl }
≟F-⊗-aux (no ¬p)    (yes _)    = no λ { refl → ¬p refl }
≟F-⊗-aux (no ¬p)    (no _)     = no λ { refl → ¬p refl }

≟T-*-aux : ∀ {m} {A₁ B₁ A₂ B₂ : Ty m}
         → Dec (A₁ ≡ A₂) → Dec (B₁ ≡ B₂)
         → Dec ((A₁ Once.Spec.Type.* B₁) ≡ (A₂ Once.Spec.Type.* B₂))
≟T-*-aux (yes refl) (yes refl) = yes refl
≟T-*-aux (yes refl) (no ¬q)    = no λ { refl → ¬q refl }
≟T-*-aux (no ¬p)    (yes _)    = no λ { refl → ¬p refl }
≟T-*-aux (no ¬p)    (no _)     = no λ { refl → ¬p refl }

≟T-+-aux : ∀ {m} {A₁ B₁ A₂ B₂ : Ty m}
         → Dec (A₁ ≡ A₂) → Dec (B₁ ≡ B₂)
         → Dec ((A₁ Once.Spec.Type.+ B₁) ≡ (A₂ Once.Spec.Type.+ B₂))
≟T-+-aux (yes refl) (yes refl) = yes refl
≟T-+-aux (yes refl) (no ¬q)    = no λ { refl → ¬q refl }
≟T-+-aux (no ¬p)    (yes _)    = no λ { refl → ¬p refl }
≟T-+-aux (no ¬p)    (no _)     = no λ { refl → ¬p refl }

≟T-⇒-aux : ∀ {m} {A₁ B₁ A₂ B₂ : Ty m} {k₁ k₂}
         → Dec (A₁ ≡ A₂) → Dec (k₁ ≡ k₂) → Dec (B₁ ≡ B₂)
         → Dec ((A₁ ⇒[ k₁ ] B₁) ≡ (A₂ ⇒[ k₂ ] B₂))
-- Clause ORDER is load-bearing, not cosmetic: each `no` clause leaves the OTHER
-- two columns unsplit, so a kind clash (`pure` vs `eff`, `Many` vs `One`) decides
-- the arrow WITHOUT the domain/codomain deciders having to reduce first. With the
-- old all-eight-combinations order, `(A ⇒eff B) ≟T (A' ⇒pure B')` was stuck on
-- `A ≟T A'` for variable A/A' — and a stuck outer decision HIDES the inner ones
-- from a proof's `with`, which is what made D126's `embedOrSubsume-lifts`
-- unprovable. Same decisions, same results; just decided sooner.
≟T-⇒-aux _          (no ¬k)    _          = no λ { refl → ¬k refl }
{-# CATCHALL #-}
≟T-⇒-aux (no ¬p)    _          _          = no λ { refl → ¬p refl }
{-# CATCHALL #-}
≟T-⇒-aux _          _          (no ¬r)    = no λ { refl → ¬r refl }
≟T-⇒-aux (yes refl) (yes refl) (yes refl) = yes refl

≟T-μ-aux : ∀ {m} {F₁ F₂ : Fun m} → Dec (F₁ ≡ F₂) → Dec (μ-type F₁ ≡ μ-type F₂)
≟T-μ-aux (yes refl) = yes refl
≟T-μ-aux (no ¬p)    = no λ { refl → ¬p refl }

-- D233: the grade is decided FIRST, for the reason `≟T-⇒-aux` gives.
≟T-ν-aux : ∀ {m} {F₁ F₂ : Fun m} {π₁ π₂} → Dec (π₁ ≡ π₂) → Dec (F₁ ≡ F₂) → Dec (ν-type F₁ π₁ ≡ ν-type F₂ π₂)
≟T-ν-aux (no ¬π)    _          = no λ { refl → ¬π refl }
{-# CATCHALL #-}
≟T-ν-aux _          (no ¬p)    = no λ { refl → ¬p refl }
≟T-ν-aux (yes refl) (yes refl) = yes refl


-- Kinds, and type variables: equal iff their positions are.
_≟tk_ : DecidableEquality TKind
k-base ≟tk k-base = yes refl
k-base ≟tk k-any  = no λ ()
k-any  ≟tk k-base = no λ ()
k-any  ≟tk k-any  = yes refl

≟T-var-aux : ∀ {m} {i₁ i₂ : Fin.Fin m} → Dec (i₁ ≡ i₂) → Dec (var i₁ ≡ var i₂)
≟T-var-aux (no ¬i)    = no λ { refl → ¬i refl }
≟T-var-aux (yes refl) = yes refl

-- | Decidable functor and type equality (mutually recursive)
mutual
  -- | Decidable functor equality
  _≟F_ : ∀ {m} → DecidableEquality (Fun m)
  K A ≟F K B = ≟F-K-aux (A ≟T B)
  Id ≟F Id = yes refl
  (F₁ ⊕ G₁) ≟F (F₂ ⊕ G₂) = ≟F-⊕-aux (F₁ ≟F F₂) (G₁ ≟F G₂)
  (F₁ ⊗ G₁) ≟F (F₂ ⊗ G₂) = ≟F-⊗-aux (F₁ ≟F F₂) (G₁ ≟F G₂)
  -- Mismatched constructors
  K _ ≟F Id = no λ ()
  K _ ≟F (_ ⊕ _) = no λ ()
  K _ ≟F (_ ⊗ _) = no λ ()
  Id ≟F K _ = no λ ()
  Id ≟F (_ ⊕ _) = no λ ()
  Id ≟F (_ ⊗ _) = no λ ()
  (_ ⊕ _) ≟F K _ = no λ ()
  (_ ⊕ _) ≟F Id = no λ ()
  (_ ⊕ _) ≟F (_ ⊗ _) = no λ ()
  (_ ⊗ _) ≟F K _ = no λ ()
  (_ ⊗ _) ≟F Id = no λ ()
  (_ ⊗ _) ≟F (_ ⊕ _) = no λ ()

  -- | Decidable type equality
  _≟T_ : ∀ {m} → DecidableEquality (Ty m)
  Unit ≟T Unit = yes refl
  Void ≟T Void = yes refl
  Int ≟T Int = yes refl
  Float ≟T Float = yes refl
  (A₁ Once.Spec.Type.* B₁) ≟T (A₂ Once.Spec.Type.* B₂) = ≟T-*-aux (A₁ ≟T A₂) (B₁ ≟T B₂)
  (A₁ Once.Spec.Type.+ B₁) ≟T (A₂ Once.Spec.Type.+ B₂) = ≟T-+-aux (A₁ ≟T A₂) (B₁ ≟T B₂)
  (A₁ ⇒[ k₁ ] B₁) ≟T (A₂ ⇒[ k₂ ] B₂) = ≟T-⇒-aux (A₁ ≟T A₂) (k₁ ≟k k₂) (B₁ ≟T B₂)
  -- OCP-0003: Fix removed
  -- TVar removed from Type; now in PolyType (see Once.Type)
  -- All other combinations are unequal
  Unit ≟T Void = no λ ()
  Unit ≟T Int = no λ ()
  Unit ≟T Float = no λ ()
  Unit ≟T (_ Once.Spec.Type.* _) = no λ ()
  Unit ≟T (_ Once.Spec.Type.+ _) = no λ ()
  Unit ≟T (_ ⇒[ _ ] _) = no λ ()
  Void ≟T Unit = no λ ()
  Void ≟T Int = no λ ()
  Void ≟T Float = no λ ()
  Void ≟T (_ Once.Spec.Type.* _) = no λ ()
  Void ≟T (_ Once.Spec.Type.+ _) = no λ ()
  Void ≟T (_ ⇒[ _ ] _) = no λ ()
  Int ≟T Unit = no λ ()
  Int ≟T Void = no λ ()
  Int ≟T Float = no λ ()
  Int ≟T (_ Once.Spec.Type.* _) = no λ ()
  Int ≟T (_ Once.Spec.Type.+ _) = no λ ()
  Int ≟T (_ ⇒[ _ ] _) = no λ ()
  Float ≟T Unit = no λ ()
  Float ≟T Void = no λ ()
  Float ≟T Int = no λ ()
  Float ≟T (_ Once.Spec.Type.* _) = no λ ()
  Float ≟T (_ Once.Spec.Type.+ _) = no λ ()
  Float ≟T (_ ⇒[ _ ] _) = no λ ()
  (_ Once.Spec.Type.* _) ≟T Unit = no λ ()
  (_ Once.Spec.Type.* _) ≟T Void = no λ ()
  (_ Once.Spec.Type.* _) ≟T Int = no λ ()
  (_ Once.Spec.Type.* _) ≟T Float = no λ ()
  (_ Once.Spec.Type.* _) ≟T (_ Once.Spec.Type.+ _) = no λ ()
  (_ Once.Spec.Type.* _) ≟T (_ ⇒[ _ ] _) = no λ ()
  (_ Once.Spec.Type.+ _) ≟T Unit = no λ ()
  (_ Once.Spec.Type.+ _) ≟T Void = no λ ()
  (_ Once.Spec.Type.+ _) ≟T Int = no λ ()
  (_ Once.Spec.Type.+ _) ≟T Float = no λ ()
  (_ Once.Spec.Type.+ _) ≟T (_ Once.Spec.Type.* _) = no λ ()
  (_ Once.Spec.Type.+ _) ≟T (_ ⇒[ _ ] _) = no λ ()
  (_ ⇒[ _ ] _) ≟T Unit = no λ ()
  (_ ⇒[ _ ] _) ≟T Void = no λ ()
  (_ ⇒[ _ ] _) ≟T Int = no λ ()
  (_ ⇒[ _ ] _) ≟T Float = no λ ()
  (_ ⇒[ _ ] _) ≟T (_ Once.Spec.Type.* _) = no λ ()
  (_ ⇒[ _ ] _) ≟T (_ Once.Spec.Type.+ _) = no λ ()
  -- TVar removed from Type; now in PolyType (see Once.Type)
  -- OCP-0003: μ-type and ν-type cases
  (μ-type F₁) ≟T (μ-type F₂) = ≟T-μ-aux (F₁ ≟F F₂)
  (ν-type F₁ π₁) ≟T (ν-type F₂ π₂) = ≟T-ν-aux (π₁ ≟f π₂) (F₁ ≟F F₂)
  μ-type _ ≟T Unit = no λ ()
  μ-type _ ≟T Void = no λ ()
  μ-type _ ≟T Int = no λ ()
  μ-type _ ≟T Float = no λ ()
  μ-type _ ≟T (_ Once.Spec.Type.* _) = no λ ()
  μ-type _ ≟T (_ Once.Spec.Type.+ _) = no λ ()
  μ-type _ ≟T (_ ⇒[ _ ] _) = no λ ()
  μ-type _ ≟T ν-type _ _ = no λ ()
  ν-type _ _ ≟T Unit = no λ ()
  ν-type _ _ ≟T Void = no λ ()
  ν-type _ _ ≟T Int = no λ ()
  ν-type _ _ ≟T Float = no λ ()
  ν-type _ _ ≟T (_ Once.Spec.Type.* _) = no λ ()
  ν-type _ _ ≟T (_ Once.Spec.Type.+ _) = no λ ()
  ν-type _ _ ≟T (_ ⇒[ _ ] _) = no λ ()
  ν-type _ _ ≟T μ-type _ = no λ ()
  Unit ≟T μ-type _ = no λ ()
  Unit ≟T ν-type _ _ = no λ ()
  Void ≟T μ-type _ = no λ ()
  Void ≟T ν-type _ _ = no λ ()
  Int ≟T μ-type _ = no λ ()
  Int ≟T ν-type _ _ = no λ ()
  Float ≟T μ-type _ = no λ ()
  Float ≟T ν-type _ _ = no λ ()
  (_ Once.Spec.Type.* _) ≟T μ-type _ = no λ ()
  (_ Once.Spec.Type.* _) ≟T ν-type _ _ = no λ ()
  (_ Once.Spec.Type.+ _) ≟T μ-type _ = no λ ()
  (_ Once.Spec.Type.+ _) ≟T ν-type _ _ = no λ ()
  (_ ⇒[ _ ] _) ≟T μ-type _ = no λ ()
  (_ ⇒[ _ ] _) ≟T ν-type _ _ = no λ ()
  -- type variables
  var i₁ ≟T var i₂ = ≟T-var-aux (i₁ Fin.≟ i₂)
  var _ ≟T Unit = no λ ()
  Unit ≟T var _ = no λ ()
  var _ ≟T Void = no λ ()
  Void ≟T var _ = no λ ()
  var _ ≟T (_ Once.Spec.Type.* _) = no λ ()
  (_ Once.Spec.Type.* _) ≟T var _ = no λ ()
  var _ ≟T (_ Once.Spec.Type.+ _) = no λ ()
  (_ Once.Spec.Type.+ _) ≟T var _ = no λ ()
  var _ ≟T (_ ⇒[ _ ] _) = no λ ()
  (_ ⇒[ _ ] _) ≟T var _ = no λ ()
  var _ ≟T μ-type _ = no λ ()
  μ-type _ ≟T var _ = no λ ()
  var _ ≟T ν-type _ _ = no λ ()
  ν-type _ _ ≟T var _ = no λ ()
  var _ ≟T Int = no λ ()
  Int ≟T var _ = no λ ()
  var _ ≟T Float = no λ ()
  Float ≟T var _ = no λ ()
  -- GuardedT removed: productivity follows from IR totality
  -- TVar removed from Type; now in PolyType (see Once.Type)
