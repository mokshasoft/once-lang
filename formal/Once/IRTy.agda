-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.IRTy
--
-- The UNGRADED object language of the IR — the "total core" objects
-- (OCP-0009 Rung 5: the runtime core stays fixed; the grade is erased).
--
-- `IRTy` mirrors `Once.Type` EXACTLY except the function arrow `_⇛_`
-- carries NO `ArrowKind`: pure and effectful arrows are the SAME IR
-- object. The grade (Quantity × Purity × Capabilities) lives ONLY on the
-- surface `Type`'s `_⇒[_]_`, where the type-checker checks it
-- (subsumption / attenuation, D068 / OCP-0007); it is erased here.
--
-- `⌊_⌋ : Type → IRTy` is that erasure. Because it drops the arrow kind,
-- `⌊ A ⇒[ k ] B ⌋ ≡ ⌊ A ⌋ ⇛ ⌊ B ⌋` holds DEFINITIONALLY for every `k`
-- (`erase-⇒` below is `refl`). That is exactly what makes `IR.arr`
-- (`IR (A ⇒[pure] B) (A ⇒[eff] B)`) collapse to an identity morphism at a
-- single object once `IR` is re-indexed over `IRTy` (Plan 0.52 M2 / S1).
------------------------------------------------------------------------

module Once.IRTy where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)
open import Data.Unit using (⊤)
open import Data.Empty using (⊥)
open import Data.Product using (_×_)
open import Data.Sum using (_⊎_)
open import Data.String using (String)
open import Data.Float using () renaming (Float to AgdaFloat)

open import Once.Type as T using (Type; Functor; ArrowKind)

------------------------------------------------------------------------
-- The ungraded object language (mirror of Type/Functor, minus the grade)

mutual
  -- | Ungraded functor codes (mirror of `Once.Type.Functor`).
  data IRFunctor : Set where
    K    : IRTy → IRFunctor            -- Constant
    Id   : IRFunctor                   -- Recursive position
    _⊕_  : IRFunctor → IRFunctor → IRFunctor  -- Sum
    _⊗_  : IRFunctor → IRFunctor → IRFunctor  -- Product

  -- | Ungraded IR objects. Identical to `Once.Type` EXCEPT the arrow
  -- `_⇛_` carries no `ArrowKind` — the grade is erased at this layer.
  data IRTy : Set where
    Unit   : IRTy                      -- Terminal object
    Void   : IRTy                      -- Initial object
    _*_    : IRTy → IRTy → IRTy        -- Product
    _+_    : IRTy → IRTy → IRTy        -- Coproduct (sum)
    _⇛_    : IRTy → IRTy → IRTy        -- UNGRADED exponential (grade erased)
    μ-type : IRFunctor → IRTy          -- Initial algebra
    ν-type : IRFunctor → IRTy          -- Final coalgebra
    Int    : IRTy                      -- Machine integers
    Float  : IRTy                      -- IEEE 754 double-precision floats
    Str    : IRTy                      -- UTF-8 strings
    Buffer : IRTy                      -- Raw byte buffers

infixr 40 _⊕_
infixr 50 _⊗_
infixr 30 _⇛_
infixr 40 _+_
infixr 50 _*_

------------------------------------------------------------------------
-- Grade erasure `⌊_⌋ : Type → IRTy` (drops every ArrowKind).

mutual
  ⌊_⌋ : Type → IRTy
  ⌊ Type.Unit        ⌋ = Unit
  ⌊ Type.Void        ⌋ = Void
  ⌊ A Type.* B       ⌋ = ⌊ A ⌋ * ⌊ B ⌋
  ⌊ A Type.+ B       ⌋ = ⌊ A ⌋ + ⌊ B ⌋
  ⌊ A Type.⇒[ _ ] B  ⌋ = ⌊ A ⌋ ⇛ ⌊ B ⌋       -- the grade is dropped here
  ⌊ Type.μ-type F    ⌋ = μ-type (eraseF F)
  ⌊ Type.ν-type F    ⌋ = ν-type (eraseF F)
  ⌊ Type.Int         ⌋ = Int
  ⌊ Type.Float       ⌋ = Float
  ⌊ Type.Str         ⌋ = Str
  ⌊ Type.Buffer      ⌋ = Buffer

  -- (plain prefix name, NOT `⌊_⌋F` — a second `⌊_…` mixfix collides with
  -- `⌊_⌋` when an application sits inside the brackets.)
  eraseF : Functor → IRFunctor
  eraseF (Functor.K A)   = K ⌊ A ⌋
  eraseF Functor.Id      = Id
  eraseF (F Functor.⊕ G) = eraseF F ⊕ eraseF G
  eraseF (F Functor.⊗ G) = eraseF F ⊗ eraseF G

------------------------------------------------------------------------
-- Functor machinery over IRTy (mirror of ⟦_⟧T / IsBaseType / WellFormedF,
-- needed to re-index IR's recursion schemes — In/Cata/Para/Out/Ana/Hylo —
-- over the ungraded objects). Self-contained (no Type-side imports).

-- | Interpret an ungraded functor code at an IRTy carrier (mirror ⟦_⟧T).
⟦_⟧TI : IRFunctor → IRTy → IRTy
⟦ K A   ⟧TI X = A
⟦ Id    ⟧TI X = X
⟦ F ⊕ G ⟧TI X = ⟦ F ⟧TI X + ⟦ G ⟧TI X
⟦ F ⊗ G ⟧TI X = ⟦ F ⟧TI X * ⟦ G ⟧TI X

-- | Base (non-arrow, non-fixpoint) IRTy objects (mirror IsBaseType).
data IsBaseTypeI : IRTy → Set where
  base-Unit   : IsBaseTypeI Unit
  base-Void   : IsBaseTypeI Void
  base-Int    : IsBaseTypeI Int
  base-Float  : IsBaseTypeI Float
  base-Str    : IsBaseTypeI Str
  base-Buffer : IsBaseTypeI Buffer
  base-Prod   : ∀ {A B} → IsBaseTypeI A → IsBaseTypeI B → IsBaseTypeI (A * B)
  base-Sum    : ∀ {A B} → IsBaseTypeI A → IsBaseTypeI B → IsBaseTypeI (A + B)

-- | Well-formed ungraded functor (mirror WellFormedF): `K` only at base.
data WellFormedFI : IRFunctor → Set where
  wf-K    : ∀ {A} → IsBaseTypeI A → WellFormedFI (K A)
  wf-Id   : WellFormedFI Id
  wf-Sum  : ∀ {F G} → WellFormedFI F → WellFormedFI G → WellFormedFI (F ⊕ G)
  wf-Prod : ∀ {F G} → WellFormedFI F → WellFormedFI G → WellFormedFI (F ⊗ G)

-- | Register-resident base IRTy objects (mirror `Once.Type.FitsInReg`),
-- for the `const` literal constructor.
data FitsInRegI : IRTy → Set where
  fits-int   : FitsInRegI Int
  fits-float : FitsInRegI Float

-- | The machine-carrier of a base IRTy object (mirror `⟦_⟧-base`), for the
-- `const` literal's payload. `⊤` for non-base objects (never used at `K`).
⟦_⟧-baseI : Set → IRTy → Set
⟦ IntRep ⟧-baseI Unit      = ⊤
⟦ IntRep ⟧-baseI Void      = ⊥
⟦ IntRep ⟧-baseI (A * B)   = ⟦ IntRep ⟧-baseI A × ⟦ IntRep ⟧-baseI B
⟦ IntRep ⟧-baseI (A + B)   = ⟦ IntRep ⟧-baseI A ⊎ ⟦ IntRep ⟧-baseI B
⟦ IntRep ⟧-baseI (_ ⇛ _)   = ⊤
⟦ IntRep ⟧-baseI (μ-type _) = ⊤
⟦ IntRep ⟧-baseI (ν-type _) = ⊤
⟦ IntRep ⟧-baseI Int       = IntRep
⟦ IntRep ⟧-baseI Float     = AgdaFloat
⟦ IntRep ⟧-baseI Str       = String
⟦ IntRep ⟧-baseI Buffer    = String

------------------------------------------------------------------------
-- The load-bearing definitional fact for Plan 0.52 M2: erasure sends
-- EVERY graded arrow to the single ungraded arrow object, so a pure and
-- an effectful arrow over the same A, B are the SAME IR object. `IR.arr`
-- becomes an identity morphism once `IR` is re-indexed over `IRTy`.

erase-⇒ : ∀ {A B : Type} (k : ArrowKind)
        → ⌊ A Type.⇒[ k ] B ⌋ ≡ ⌊ A ⌋ ⇛ ⌊ B ⌋
erase-⇒ _ = refl

-- Two arrows differing ONLY in their kind erase to the same object.
erase-⇒-kind-irrelevant
  : ∀ {A B : Type} (k₁ k₂ : ArrowKind)
  → ⌊ A Type.⇒[ k₁ ] B ⌋ ≡ ⌊ A Type.⇒[ k₂ ] B ⌋
erase-⇒-kind-irrelevant _ _ = refl

------------------------------------------------------------------------
-- Canonical section `⌈_⌉ : IRTy → Type` — picks a canonical graded
-- representative (every arrow re-graded to `effK`). Lets the IR-object
-- denotation REUSE the surface value domain: `⟦_⟧ᴵ A := ⟦ ⌈ A ⌉ ⟧`
-- (in `Once.Semantics.Value`), no fixpoint machinery re-built. Since the
-- value domain is grade-blind, the choice of grade is denotationally
-- irrelevant, and `⌊ ⌈ A ⌉ ⌋ ≡ A` (round-trip, `retract-⌈⌉` below).

mutual
  ⌈_⌉ : IRTy → Type
  ⌈ Unit     ⌉ = T.Unit
  ⌈ Void     ⌉ = T.Void
  ⌈ A * B    ⌉ = ⌈ A ⌉ T.* ⌈ B ⌉
  ⌈ A + B    ⌉ = ⌈ A ⌉ T.+ ⌈ B ⌉
  ⌈ A ⇛ B    ⌉ = ⌈ A ⌉ T.⇒[ T.effK ] ⌈ B ⌉   -- canonical grade
  ⌈ μ-type F ⌉ = T.μ-type ⌈ F ⌉F
  ⌈ ν-type F ⌉ = T.ν-type ⌈ F ⌉F
  ⌈ Int      ⌉ = T.Int
  ⌈ Float    ⌉ = T.Float
  ⌈ Str      ⌉ = T.Str
  ⌈ Buffer   ⌉ = T.Buffer

  ⌈_⌉F : IRFunctor → Functor
  ⌈ K A   ⌉F = T.K ⌈ A ⌉
  ⌈ Id    ⌉F = T.Id
  ⌈ F ⊕ G ⌉F = ⌈ F ⌉F T.⊕ ⌈ G ⌉F
  ⌈ F ⊗ G ⌉F = ⌈ F ⌉F T.⊗ ⌈ G ⌉F

-- `⌈_⌉` is a section of `⌊_⌋`: erasing the canonical representative gives
-- back the ungraded object (the grade `⌈_⌉` invented is dropped again).
mutual
  retract-⌈⌉ : ∀ (A : IRTy) → ⌊ ⌈ A ⌉ ⌋ ≡ A
  retract-⌈⌉ Unit       = refl
  retract-⌈⌉ Void       = refl
  retract-⌈⌉ (A * B)    = cong₂ _*_ (retract-⌈⌉ A) (retract-⌈⌉ B)
  retract-⌈⌉ (A + B)    = cong₂ _+_ (retract-⌈⌉ A) (retract-⌈⌉ B)
  retract-⌈⌉ (A ⇛ B)    = cong₂ _⇛_ (retract-⌈⌉ A) (retract-⌈⌉ B)
  retract-⌈⌉ (μ-type F) = cong μ-type (retract-⌈⌉F F)
  retract-⌈⌉ (ν-type F) = cong ν-type (retract-⌈⌉F F)
  retract-⌈⌉ Int        = refl
  retract-⌈⌉ Float      = refl
  retract-⌈⌉ Str        = refl
  retract-⌈⌉ Buffer     = refl

  retract-⌈⌉F : ∀ (F : IRFunctor) → eraseF ⌈ F ⌉F ≡ F
  retract-⌈⌉F (K A)   = cong K (retract-⌈⌉ A)
  retract-⌈⌉F Id      = refl
  retract-⌈⌉F (F ⊕ G) = cong₂ _⊕_ (retract-⌈⌉F F) (retract-⌈⌉F G)
  retract-⌈⌉F (F ⊗ G) = cong₂ _⊗_ (retract-⌈⌉F F) (retract-⌈⌉F G)

-- `⌈_⌉` commutes with functor application. Needed to re-thread the IR
-- recursion schemes' evaluator (Plan 0.52 M2 S2): their operand lives at
-- `⟦ F ⟧TI X` (IRTy), while the surface `coerce-functor`/`sem-*` helpers
-- expect `⟦ ⌈F⌉F ⟧T ⌈X⌉` (Type). Refl/cong by induction on the functor.
⌈⟧TI-commute : ∀ (F : IRFunctor) (X : IRTy) → ⌈ ⟦ F ⟧TI X ⌉ ≡ T.⟦ ⌈ F ⌉F ⟧T ⌈ X ⌉
⌈⟧TI-commute (K A)   X = refl
⌈⟧TI-commute Id      X = refl
⌈⟧TI-commute (F ⊕ G) X = cong₂ T._+_ (⌈⟧TI-commute F X) (⌈⟧TI-commute G X)
⌈⟧TI-commute (F ⊗ G) X = cong₂ T._*_ (⌈⟧TI-commute F X) (⌈⟧TI-commute G X)

-- The `⌊_⌋` dual: erasure commutes with functor application the other way.
-- Needed by the elaborator, which builds a `⟦F⟧T A`-shaped algebra (surface)
-- but feeds it to `Cata`/`Ana` demanding `⟦ eraseF F ⟧TI ⌊A⌋`.
⌊⟧T-commute : ∀ (F : Functor) (A : Type) → ⌊ T.⟦ F ⟧T A ⌋ ≡ ⟦ eraseF F ⟧TI ⌊ A ⌋
⌊⟧T-commute (T.K B)   A = refl
⌊⟧T-commute T.Id      A = refl
⌊⟧T-commute (F T.⊕ G) A = cong₂ _+_ (⌊⟧T-commute F A) (⌊⟧T-commute G A)
⌊⟧T-commute (F T.⊗ G) A = cong₂ _*_ (⌊⟧T-commute F A) (⌊⟧T-commute G A)
