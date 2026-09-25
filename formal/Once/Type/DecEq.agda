-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Type.DecEq — decidable equality of `Functor` and `Type`.
--
-- Plan 0.99: the CANONICAL home. Deciding type equality is a fact about the
-- types, not about elaboration, and the Spec's subtyping decider (`Once.Type.Sub`)
-- needs functor equality at `μ`/`ν` without importing the elaborator. This is the
-- block `TypeCheck/Elaborate` has carried (and `Optimize` a second copy of, as
-- `_≟Type_`); plan 0.99 phase B deletes both copies and re-points their clients
-- here. Content moved verbatim.
------------------------------------------------------------------------

module Once.Type.DecEq where

open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import Once.Type
open import Once.Type using (Type; Functor; K; Id; _⊕_; _⊗_; Unit; Void; Int; Float; Str; Buffer;
                             _⇒[_]_; μ-type; ν-type; _≟k_)

-- Helpers for ≟T / ≟F matching-constructor cases (avoid `with`-blocks).

≟F-K-aux : ∀ {A B} → Dec (A ≡ B) → Dec (K A ≡ K B)
≟F-K-aux (yes refl) = yes refl
≟F-K-aux (no ¬p)    = no λ { refl → ¬p refl }

≟F-⊕-aux : ∀ {F₁ G₁ F₂ G₂}
         → Dec (F₁ ≡ F₂) → Dec (G₁ ≡ G₂)
         → Dec ((F₁ ⊕ G₁) ≡ (F₂ ⊕ G₂))
≟F-⊕-aux (yes refl) (yes refl) = yes refl
≟F-⊕-aux (yes refl) (no ¬q)    = no λ { refl → ¬q refl }
≟F-⊕-aux (no ¬p)    (yes _)    = no λ { refl → ¬p refl }
≟F-⊕-aux (no ¬p)    (no _)     = no λ { refl → ¬p refl }

≟F-⊗-aux : ∀ {F₁ G₁ F₂ G₂}
         → Dec (F₁ ≡ F₂) → Dec (G₁ ≡ G₂)
         → Dec ((F₁ ⊗ G₁) ≡ (F₂ ⊗ G₂))
≟F-⊗-aux (yes refl) (yes refl) = yes refl
≟F-⊗-aux (yes refl) (no ¬q)    = no λ { refl → ¬q refl }
≟F-⊗-aux (no ¬p)    (yes _)    = no λ { refl → ¬p refl }
≟F-⊗-aux (no ¬p)    (no _)     = no λ { refl → ¬p refl }

≟T-*-aux : ∀ {A₁ B₁ A₂ B₂}
         → Dec (A₁ ≡ A₂) → Dec (B₁ ≡ B₂)
         → Dec ((A₁ Once.Type.* B₁) ≡ (A₂ Once.Type.* B₂))
≟T-*-aux (yes refl) (yes refl) = yes refl
≟T-*-aux (yes refl) (no ¬q)    = no λ { refl → ¬q refl }
≟T-*-aux (no ¬p)    (yes _)    = no λ { refl → ¬p refl }
≟T-*-aux (no ¬p)    (no _)     = no λ { refl → ¬p refl }

≟T-+-aux : ∀ {A₁ B₁ A₂ B₂}
         → Dec (A₁ ≡ A₂) → Dec (B₁ ≡ B₂)
         → Dec ((A₁ Once.Type.+ B₁) ≡ (A₂ Once.Type.+ B₂))
≟T-+-aux (yes refl) (yes refl) = yes refl
≟T-+-aux (yes refl) (no ¬q)    = no λ { refl → ¬q refl }
≟T-+-aux (no ¬p)    (yes _)    = no λ { refl → ¬p refl }
≟T-+-aux (no ¬p)    (no _)     = no λ { refl → ¬p refl }

≟T-⇒-aux : ∀ {A₁ B₁ A₂ B₂ k₁ k₂}
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
≟T-⇒-aux (no ¬p)    _          _          = no λ { refl → ¬p refl }
≟T-⇒-aux _          _          (no ¬r)    = no λ { refl → ¬r refl }
≟T-⇒-aux (yes refl) (yes refl) (yes refl) = yes refl

≟T-μ-aux : ∀ {F₁ F₂} → Dec (F₁ ≡ F₂) → Dec (μ-type F₁ ≡ μ-type F₂)
≟T-μ-aux (yes refl) = yes refl
≟T-μ-aux (no ¬p)    = no λ { refl → ¬p refl }

≟T-ν-aux : ∀ {F₁ F₂} → Dec (F₁ ≡ F₂) → Dec (ν-type F₁ ≡ ν-type F₂)
≟T-ν-aux (yes refl) = yes refl
≟T-ν-aux (no ¬p)    = no λ { refl → ¬p refl }


-- | Decidable functor and type equality (mutually recursive)
mutual
  -- | Decidable functor equality
  _≟F_ : (F G : Functor) → Dec (F ≡ G)
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
  _≟T_ : (A B : Type) → Dec (A ≡ B)
  Unit ≟T Unit = yes refl
  Void ≟T Void = yes refl
  Int ≟T Int = yes refl
  Float ≟T Float = yes refl
  Str ≟T Str = yes refl
  Buffer ≟T Buffer = yes refl
  (A₁ Once.Type.* B₁) ≟T (A₂ Once.Type.* B₂) = ≟T-*-aux (A₁ ≟T A₂) (B₁ ≟T B₂)
  (A₁ Once.Type.+ B₁) ≟T (A₂ Once.Type.+ B₂) = ≟T-+-aux (A₁ ≟T A₂) (B₁ ≟T B₂)
  (A₁ ⇒[ k₁ ] B₁) ≟T (A₂ ⇒[ k₂ ] B₂) = ≟T-⇒-aux (A₁ ≟T A₂) (k₁ ≟k k₂) (B₁ ≟T B₂)
  -- OCP-0003: Fix removed
  -- TVar removed from Type; now in PolyType (see Once.Type)
  -- All other combinations are unequal
  Unit ≟T Void = no λ ()
  Unit ≟T Int = no λ ()
  Unit ≟T Float = no λ ()
  Unit ≟T Str = no λ ()
  Unit ≟T Buffer = no λ ()
  Unit ≟T (_ Once.Type.* _) = no λ ()
  Unit ≟T (_ Once.Type.+ _) = no λ ()
  Unit ≟T (_ ⇒[ _ ] _) = no λ ()
  Void ≟T Unit = no λ ()
  Void ≟T Int = no λ ()
  Void ≟T Float = no λ ()
  Void ≟T Str = no λ ()
  Void ≟T Buffer = no λ ()
  Void ≟T (_ Once.Type.* _) = no λ ()
  Void ≟T (_ Once.Type.+ _) = no λ ()
  Void ≟T (_ ⇒[ _ ] _) = no λ ()
  Int ≟T Unit = no λ ()
  Int ≟T Void = no λ ()
  Int ≟T Float = no λ ()
  Int ≟T Str = no λ ()
  Int ≟T Buffer = no λ ()
  Int ≟T (_ Once.Type.* _) = no λ ()
  Int ≟T (_ Once.Type.+ _) = no λ ()
  Int ≟T (_ ⇒[ _ ] _) = no λ ()
  Float ≟T Unit = no λ ()
  Float ≟T Void = no λ ()
  Float ≟T Int = no λ ()
  Float ≟T Str = no λ ()
  Float ≟T Buffer = no λ ()
  Float ≟T (_ Once.Type.* _) = no λ ()
  Float ≟T (_ Once.Type.+ _) = no λ ()
  Float ≟T (_ ⇒[ _ ] _) = no λ ()
  Str ≟T Unit = no λ ()
  Str ≟T Void = no λ ()
  Str ≟T Int = no λ ()
  Str ≟T Float = no λ ()
  Str ≟T Buffer = no λ ()
  Str ≟T (_ Once.Type.* _) = no λ ()
  Str ≟T (_ Once.Type.+ _) = no λ ()
  Str ≟T (_ ⇒[ _ ] _) = no λ ()
  Buffer ≟T Unit = no λ ()
  Buffer ≟T Void = no λ ()
  Buffer ≟T Int = no λ ()
  Buffer ≟T Float = no λ ()
  Buffer ≟T Str = no λ ()
  Buffer ≟T (_ Once.Type.* _) = no λ ()
  Buffer ≟T (_ Once.Type.+ _) = no λ ()
  Buffer ≟T (_ ⇒[ _ ] _) = no λ ()
  (_ Once.Type.* _) ≟T Unit = no λ ()
  (_ Once.Type.* _) ≟T Void = no λ ()
  (_ Once.Type.* _) ≟T Int = no λ ()
  (_ Once.Type.* _) ≟T Float = no λ ()
  (_ Once.Type.* _) ≟T Str = no λ ()
  (_ Once.Type.* _) ≟T Buffer = no λ ()
  (_ Once.Type.* _) ≟T (_ Once.Type.+ _) = no λ ()
  (_ Once.Type.* _) ≟T (_ ⇒[ _ ] _) = no λ ()
  (_ Once.Type.+ _) ≟T Unit = no λ ()
  (_ Once.Type.+ _) ≟T Void = no λ ()
  (_ Once.Type.+ _) ≟T Int = no λ ()
  (_ Once.Type.+ _) ≟T Float = no λ ()
  (_ Once.Type.+ _) ≟T Str = no λ ()
  (_ Once.Type.+ _) ≟T Buffer = no λ ()
  (_ Once.Type.+ _) ≟T (_ Once.Type.* _) = no λ ()
  (_ Once.Type.+ _) ≟T (_ ⇒[ _ ] _) = no λ ()
  (_ ⇒[ _ ] _) ≟T Unit = no λ ()
  (_ ⇒[ _ ] _) ≟T Void = no λ ()
  (_ ⇒[ _ ] _) ≟T Int = no λ ()
  (_ ⇒[ _ ] _) ≟T Float = no λ ()
  (_ ⇒[ _ ] _) ≟T Str = no λ ()
  (_ ⇒[ _ ] _) ≟T Buffer = no λ ()
  (_ ⇒[ _ ] _) ≟T (_ Once.Type.* _) = no λ ()
  (_ ⇒[ _ ] _) ≟T (_ Once.Type.+ _) = no λ ()
  -- TVar removed from Type; now in PolyType (see Once.Type)
  -- OCP-0003: μ-type and ν-type cases
  (μ-type F₁) ≟T (μ-type F₂) = ≟T-μ-aux (F₁ ≟F F₂)
  (ν-type F₁) ≟T (ν-type F₂) = ≟T-ν-aux (F₁ ≟F F₂)
  μ-type _ ≟T Unit = no λ ()
  μ-type _ ≟T Void = no λ ()
  μ-type _ ≟T Int = no λ ()
  μ-type _ ≟T Float = no λ ()
  μ-type _ ≟T Str = no λ ()
  μ-type _ ≟T Buffer = no λ ()
  μ-type _ ≟T (_ Once.Type.* _) = no λ ()
  μ-type _ ≟T (_ Once.Type.+ _) = no λ ()
  μ-type _ ≟T (_ ⇒[ _ ] _) = no λ ()
  μ-type _ ≟T ν-type _ = no λ ()
  ν-type _ ≟T Unit = no λ ()
  ν-type _ ≟T Void = no λ ()
  ν-type _ ≟T Int = no λ ()
  ν-type _ ≟T Float = no λ ()
  ν-type _ ≟T Str = no λ ()
  ν-type _ ≟T Buffer = no λ ()
  ν-type _ ≟T (_ Once.Type.* _) = no λ ()
  ν-type _ ≟T (_ Once.Type.+ _) = no λ ()
  ν-type _ ≟T (_ ⇒[ _ ] _) = no λ ()
  ν-type _ ≟T μ-type _ = no λ ()
  Unit ≟T μ-type _ = no λ ()
  Unit ≟T ν-type _ = no λ ()
  Void ≟T μ-type _ = no λ ()
  Void ≟T ν-type _ = no λ ()
  Int ≟T μ-type _ = no λ ()
  Int ≟T ν-type _ = no λ ()
  Float ≟T μ-type _ = no λ ()
  Float ≟T ν-type _ = no λ ()
  Str ≟T μ-type _ = no λ ()
  Str ≟T ν-type _ = no λ ()
  Buffer ≟T μ-type _ = no λ ()
  Buffer ≟T ν-type _ = no λ ()
  (_ Once.Type.* _) ≟T μ-type _ = no λ ()
  (_ Once.Type.* _) ≟T ν-type _ = no λ ()
  (_ Once.Type.+ _) ≟T μ-type _ = no λ ()
  (_ Once.Type.+ _) ≟T ν-type _ = no λ ()
  (_ ⇒[ _ ] _) ≟T μ-type _ = no λ ()
  (_ ⇒[ _ ] _) ≟T ν-type _ = no λ ()
  -- GuardedT removed: productivity follows from IR totality
  -- TVar removed from Type; now in PolyType (see Once.Type)
