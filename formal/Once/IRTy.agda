-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

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

import Once.Type.Grade
module Once.IRTy where


open import Relation.Binary.Definitions using (DecidableEquality)

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)
open import Relation.Nullary using (Dec; yes; no)
open import Data.Nat using (ℕ)
import Data.Nat.Properties as ℕP
open import Data.Unit using (⊤)
open import Data.Empty using (⊥)
open import Data.Product using (_×_)
open import Data.Sum using (_⊎_)

open import Once.Spec.Grade as T using (Quantity; Zero; One; Many; Purity; actᶠ)
open import Once.Spec.Type as T using (Ty; Fun; Type)
import Once.Spec.Type as ST
open import Once.Type.Core as T using (wk₀; wk₀F)
open import Once.Spec.Type using (Fun)
import Once.Spec.Type as T
open import Once.Type.DecEq using (_≟p_)

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
    -- D413: the exponential carries the Spec's PURITY (the linear core needs it:
    -- an `act` arrow is a finite block, D412); the quantity stays erased.
    _⇛[_]_ : IRTy → Purity → IRTy → IRTy
    μ-type : IRFunctor → IRTy          -- Initial algebra
    ν-type : IRFunctor → IRTy          -- Final coalgebra
    Int    : IRTy                      -- Machine integers
    Float  : IRTy                      -- IEEE 754 double-precision floats
    -- (`Str`/`Buffer` are gone, plan 0.106. Every type here has a case in the
    -- value relation, `ValueRel.VCase`. A type whose relation were EMPTY at an
    -- inhabited value would make every arrow from it vacuously valid, since
    -- the arrow case takes a valid argument as a premise; `Void` is the only
    -- empty case, which is right because `⟦ Void ⟧` is empty (D364).)

infixr 40 _⊕_
infixr 50 _⊗_
infixr 30 _⇛[_]_
infixr 40 _+_
infixr 50 _*_

------------------------------------------------------------------------
-- Grade erasure `⌊_⌋ : Type → IRTy`.
--
-- D143: erasure is NOT "drop the ArrowKind". It is: drop the PURITY (a pure and
-- an effectful arrow over the same A, B are the same runtime object — plan 0.52
-- M2, correctly), and INTERPRET the QUANTITY (a `Zero`-graded argument is
-- erased, so the arrow has NO ARGUMENT SLOT). M2 conflated the two and dropped
-- both; purity does not change the representation, a `Zero` quantity does.
--
-- This MIRRORS the spec's `⟦_⟧ᴰ`, which is now grade-aware at the same place.
-- Both sides must forget the argument together or `coh` loses its full→runtime
-- direction, which has no canonical inhabitant when only one side forgets.

-- | The arrow's runtime shape, decided by its QUANTITY.
-- (D413: and keeps its PURITY.)
eraseArrow : Quantity → Purity → IRTy → IRTy → IRTy
eraseArrow Zero π a b = Unit ⇛[ π ] b
eraseArrow One  π a b = a ⇛[ π ] b
eraseArrow Many π a b = a ⇛[ π ] b

mutual
  ⌊_⌋ : ∀ {m} → Ty m → IRTy
  ⌊ ST.Unit        ⌋ = Unit
  ⌊ ST.Void        ⌋ = Void
  ⌊ A ST.* B       ⌋ = ⌊ A ⌋ * ⌊ B ⌋
  ⌊ A ST.+ B       ⌋ = ⌊ A ⌋ + ⌊ B ⌋
  ⌊ A ST.⇒[ k ] B  ⌋ = eraseArrow (T.ArrowKind.quantity k) (T.ArrowKind.purity k) ⌊ A ⌋ ⌊ B ⌋
  ⌊ ST.μ F    ⌋ = μ-type (eraseF F)
  ⌊ ST.ν F _  ⌋ = ν-type (eraseF F)   -- D233: the grade is erased, as an arrow's
  ⌊ ST.Int         ⌋ = Int
  ⌊ ST.Float       ⌋ = Float
  -- A type variable (a parameter of the definition being compiled, D243) has
  -- no runtime value: it erases to `Void`.
  ⌊ ST.var _ ⌋ = Void

  -- (plain prefix name, NOT `⌊_⌋F` — a second `⌊_…` mixfix collides with
  -- `⌊_⌋` when an application sits inside the brackets.)
  eraseF : ∀ {m} → Fun m → IRFunctor
  eraseF (ST.K A)   = K ⌊ A ⌋
  eraseF ST.Id      = Id
  eraseF (F ST.⊕ G) = eraseF F ⊕ eraseF G
  eraseF (F ST.⊗ G) = eraseF F ⊗ eraseF G

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
  base-Prod   : ∀ {A B} → IsBaseTypeI A → IsBaseTypeI B → IsBaseTypeI (A * B)
  base-Sum    : ∀ {A B} → IsBaseTypeI A → IsBaseTypeI B → IsBaseTypeI (A + B)

-- | Well-formed ungraded functor (mirror WellFormedF): `K` only at base.
data WellFormedFI : IRFunctor → Set where
  wf-K    : ∀ {A} → IsBaseTypeI A → WellFormedFI (K A)
  wf-Id   : WellFormedFI Id
  wf-Sum  : ∀ {F G} → WellFormedFI F → WellFormedFI G → WellFormedFI (F ⊕ G)
  wf-Prod : ∀ {F G} → WellFormedFI F → WellFormedFI G → WellFormedFI (F ⊗ G)

-- Proof-irrelevance of the ungraded witnesses (mirror `Base-irrelevant` /
-- `WFFun-irrelevant`; needed by the IR decidable-equality deciders).
IsBaseTypeI-irrelevant : ∀ {A} (ib₁ ib₂ : IsBaseTypeI A) → ib₁ ≡ ib₂
IsBaseTypeI-irrelevant base-Unit   base-Unit   = refl
IsBaseTypeI-irrelevant base-Void   base-Void   = refl
IsBaseTypeI-irrelevant base-Int    base-Int    = refl
IsBaseTypeI-irrelevant base-Float  base-Float  = refl
IsBaseTypeI-irrelevant (base-Prod a₁ b₁) (base-Prod a₂ b₂) =
  cong₂ base-Prod (IsBaseTypeI-irrelevant a₁ a₂) (IsBaseTypeI-irrelevant b₁ b₂)
IsBaseTypeI-irrelevant (base-Sum a₁ b₁) (base-Sum a₂ b₂) =
  cong₂ base-Sum (IsBaseTypeI-irrelevant a₁ a₂) (IsBaseTypeI-irrelevant b₁ b₂)

WellFormedFI-irrelevant : ∀ {F} (wf₁ wf₂ : WellFormedFI F) → wf₁ ≡ wf₂
WellFormedFI-irrelevant (wf-K ib₁) (wf-K ib₂) = cong wf-K (IsBaseTypeI-irrelevant ib₁ ib₂)
WellFormedFI-irrelevant wf-Id wf-Id = refl
WellFormedFI-irrelevant (wf-Sum wfF₁ wfG₁) (wf-Sum wfF₂ wfG₂) =
  cong₂ wf-Sum (WellFormedFI-irrelevant wfF₁ wfF₂) (WellFormedFI-irrelevant wfG₁ wfG₂)
WellFormedFI-irrelevant (wf-Prod wfF₁ wfG₁) (wf-Prod wfF₂ wfG₂) =
  cong₂ wf-Prod (WellFormedFI-irrelevant wfF₁ wfF₂) (WellFormedFI-irrelevant wfG₁ wfG₂)

-- Decidable equality on IRTy objects (mutual with IRFunctor). Needed by the IR
-- optimizer's `≟IRH` deciders now that `_∘_`'s middle object is IRTy. `IRTy`
-- uses the tag+diag pattern (cross-tag cases pruned by the absurd tag equality).
irtyTag : IRTy → ℕ
irtyTag Unit       = 0
irtyTag Void       = 1
irtyTag (_ * _)    = 2
irtyTag (_ + _)    = 3
irtyTag (_ ⇛[ _ ] _) = 4
irtyTag (μ-type _) = 5
irtyTag (ν-type _) = 6
irtyTag Int        = 7
irtyTag Float      = 8

mutual
  _≟IRTy_ : DecidableEquality IRTy
  A ≟IRTy B = ≟IRTy-aux A B (irtyTag A ℕP.≟ irtyTag B)

  ≟IRTy-aux : (A B : IRTy) → Dec (irtyTag A ≡ irtyTag B) → Dec (A ≡ B)
  ≟IRTy-aux A B (no hne)  = no (λ eq → hne (cong irtyTag eq))
  ≟IRTy-aux A B (yes heq) = ≟IRTy-diag A B heq

  ≟IRTy-diag : (A B : IRTy) → irtyTag A ≡ irtyTag B → Dec (A ≡ B)
  ≟IRTy-diag Unit   Unit   _ = yes refl
  ≟IRTy-diag Void   Void   _ = yes refl
  ≟IRTy-diag (A * B) (C * D) _ with A ≟IRTy C | B ≟IRTy D
  ... | yes refl | yes refl = yes refl
  ... | no ne    | _        = no (λ { refl → ne refl })
  {-# CATCHALL #-}
  ... | _        | no ne    = no (λ { refl → ne refl })
  ≟IRTy-diag (A + B) (C + D) _ with A ≟IRTy C | B ≟IRTy D
  ... | yes refl | yes refl = yes refl
  ... | no ne    | _        = no (λ { refl → ne refl })
  {-# CATCHALL #-}
  ... | _        | no ne    = no (λ { refl → ne refl })
  ≟IRTy-diag (A ⇛[ π ] B) (C ⇛[ π′ ] D) _ with A ≟IRTy C | π ≟p π′ | B ≟IRTy D
  ... | yes refl | yes refl | yes refl = yes refl
  ... | no ne    | _        | _        = no (λ { refl → ne refl })
  {-# CATCHALL #-}
  ... | _        | no ne    | _        = no (λ { refl → ne refl })
  {-# CATCHALL #-}
  ... | _        | _        | no ne    = no (λ { refl → ne refl })
  ≟IRTy-diag (μ-type F) (μ-type G) _ with F ≟IRFun G
  ... | yes refl = yes refl
  ... | no ne    = no (λ { refl → ne refl })
  ≟IRTy-diag (ν-type F) (ν-type G) _ with F ≟IRFun G
  ... | yes refl = yes refl
  ... | no ne    = no (λ { refl → ne refl })
  ≟IRTy-diag Int    Int    _ = yes refl
  ≟IRTy-diag Float  Float  _ = yes refl

  _≟IRFun_ : DecidableEquality IRFunctor
  K A ≟IRFun K B with A ≟IRTy B
  ... | yes refl = yes refl
  ... | no ne    = no (λ { refl → ne refl })
  Id ≟IRFun Id = yes refl
  (F ⊕ G) ≟IRFun (F' ⊕ G') with F ≟IRFun F' | G ≟IRFun G'
  ... | yes refl | yes refl = yes refl
  ... | no ne    | _        = no (λ { refl → ne refl })
  {-# CATCHALL #-}
  ... | _        | no ne    = no (λ { refl → ne refl })
  (F ⊗ G) ≟IRFun (F' ⊗ G') with F ≟IRFun F' | G ≟IRFun G'
  ... | yes refl | yes refl = yes refl
  ... | no ne    | _        = no (λ { refl → ne refl })
  {-# CATCHALL #-}
  ... | _        | no ne    = no (λ { refl → ne refl })
  K _ ≟IRFun Id      = no (λ ())
  K _ ≟IRFun (_ ⊕ _) = no (λ ())
  K _ ≟IRFun (_ ⊗ _) = no (λ ())
  Id  ≟IRFun K _      = no (λ ())
  Id  ≟IRFun (_ ⊕ _) = no (λ ())
  Id  ≟IRFun (_ ⊗ _) = no (λ ())
  (_ ⊕ _) ≟IRFun K _  = no (λ ())
  (_ ⊕ _) ≟IRFun Id   = no (λ ())
  (_ ⊕ _) ≟IRFun (_ ⊗ _) = no (λ ())
  (_ ⊗ _) ≟IRFun K _  = no (λ ())
  (_ ⊗ _) ≟IRFun Id   = no (λ ())
  (_ ⊗ _) ≟IRFun (_ ⊕ _) = no (λ ())

-- | Register-resident base IRTy objects (mirror `Once.Type.FitsInReg`),
-- for the `const` literal constructor.
data FitsInRegI : IRTy → Set where
  fits-int   : FitsInRegI Int
  fits-float : FitsInRegI Float

-- | The machine-carrier of a base IRTy object (mirror `⟦_⟧-base`), for the
-- `const` literal's payload. `⊤` for non-base objects (never used at `K`).
-- PLAN 0.72 (D112): TWO carriers now, mirroring `Semantics.Value`'s two
-- parameters. `Int`'s was always a parameter; `Float`'s was `AgdaFloat`, a
-- 64-bit double baked into the IR regardless of the target's width.
⟦_,_⟧-baseI : Set → Set → IRTy → Set
⟦ IntRep , FloatRep ⟧-baseI Unit      = ⊤
⟦ IntRep , FloatRep ⟧-baseI Void      = ⊥
⟦ IntRep , FloatRep ⟧-baseI (A * B)   = ⟦ IntRep , FloatRep ⟧-baseI A × ⟦ IntRep , FloatRep ⟧-baseI B
⟦ IntRep , FloatRep ⟧-baseI (A + B)   = ⟦ IntRep , FloatRep ⟧-baseI A ⊎ ⟦ IntRep , FloatRep ⟧-baseI B
⟦ IntRep , FloatRep ⟧-baseI (_ ⇛[ _ ] _) = ⊤
⟦ IntRep , FloatRep ⟧-baseI (μ-type _) = ⊤
⟦ IntRep , FloatRep ⟧-baseI (ν-type _) = ⊤
⟦ IntRep , FloatRep ⟧-baseI Int       = IntRep
⟦ IntRep , FloatRep ⟧-baseI Float     = FloatRep

------------------------------------------------------------------------
-- Canonical section `⌈_⌉ : IRTy → Type` — picks a canonical graded
-- representative (every arrow re-graded to `effK`). Lets the IR-object
-- denotation REUSE the surface value domain: `⟦_⟧ᴵ A := ⟦ ⌈ A ⌉ ⟧`
-- (in `Once.Semantics.Value`), no fixpoint machinery re-built. Since the
-- value domain is grade-blind, the choice of grade is denotationally
-- irrelevant. (D413: the IR's arrow now keeps its purity, which the
-- meaning still ignores, so `⌈_⌉` is no longer a section of `⌊_⌋`.)

mutual
  ⌈_⌉ : IRTy → Type
  ⌈ Unit     ⌉ = T.Unit
  ⌈ Void     ⌉ = T.Void
  ⌈ A * B    ⌉ = ⌈ A ⌉ T.* ⌈ B ⌉
  ⌈ A + B    ⌉ = ⌈ A ⌉ T.+ ⌈ B ⌉
  ⌈ A ⇛[ _ ] B ⌉ = ⌈ A ⌉ T.⇒[ Once.Type.Grade.effK ] ⌈ B ⌉   -- canonical grade
  ⌈ μ-type F ⌉ = T.μ ⌈ F ⌉F
  ⌈ ν-type F ⌉ = T.ν ⌈ F ⌉F T.actᶠ   -- canonical grade (the top finite one, D318)
  ⌈ Int      ⌉ = T.Int
  ⌈ Float    ⌉ = T.Float

  ⌈_⌉F : IRFunctor → Fun 0
  ⌈ K A   ⌉F = T.K ⌈ A ⌉
  ⌈ Id    ⌉F = T.Id
  ⌈ F ⊕ G ⌉F = ⌈ F ⌉F T.⊕ ⌈ G ⌉F
  ⌈ F ⊗ G ⌉F = ⌈ F ⌉F T.⊗ ⌈ G ⌉F

-- `⌈_⌉` commutes with functor application. Needed to re-thread the IR
-- recursion schemes' evaluator (Plan 0.52 M2 S2): their operand lives at
-- `⟦ F ⟧TI X` (IRTy), while the surface `coerce-functor`/`sem-*` helpers
-- expect `⟦ ⌈F⌉F ⟧T ⌈X⌉` (Type). Refl/cong by induction on the functor.
⌈⟧TI-commute : ∀ (F : IRFunctor) (X : IRTy) → ⌈ ⟦ F ⟧TI X ⌉ ≡ T.⟦ ⌈ F ⌉F ⟧F ⌈ X ⌉
⌈⟧TI-commute (K A)   X = refl
⌈⟧TI-commute Id      X = refl
⌈⟧TI-commute (F ⊕ G) X = cong₂ T._+_ (⌈⟧TI-commute F X) (⌈⟧TI-commute G X)
⌈⟧TI-commute (F ⊗ G) X = cong₂ T._*_ (⌈⟧TI-commute F X) (⌈⟧TI-commute G X)

-- The `⌊_⌋` dual: erasure commutes with functor application the other way.
-- Needed by the elaborator, which builds a `⟦F⟧T A`-shaped algebra (surface)
-- but feeds it to `Cata`/`Ana` demanding `⟦ eraseF F ⟧TI ⌊A⌋`.
⌊⟧T-commute : ∀ {m} (F : Fun m) (A : Ty m) → ⌊ T.⟦ F ⟧F A ⌋ ≡ ⟦ eraseF F ⟧TI ⌊ A ⌋
⌊⟧T-commute (T.K B)   A = refl
⌊⟧T-commute T.Id      A = refl
⌊⟧T-commute (F T.⊕ G) A = cong₂ _+_ (⌊⟧T-commute F A) (⌊⟧T-commute G A)
⌊⟧T-commute (F T.⊗ G) A = cong₂ _*_ (⌊⟧T-commute F A) (⌊⟧T-commute G A)

-- A ground type read over `m` type variables (`wk₀`) erases as itself.
mutual
  ⌊wk₀⌋ : ∀ {m} (A : Type) → ⌊ T.wk₀ {m} A ⌋ ≡ ⌊ A ⌋
  ⌊wk₀⌋ ST.Unit         = refl
  ⌊wk₀⌋ ST.Void         = refl
  ⌊wk₀⌋ ST.Int          = refl
  ⌊wk₀⌋ ST.Float        = refl
  ⌊wk₀⌋ (A ST.* B)      = cong₂ _*_ (⌊wk₀⌋ A) (⌊wk₀⌋ B)
  ⌊wk₀⌋ (A ST.+ B)      = cong₂ _+_ (⌊wk₀⌋ A) (⌊wk₀⌋ B)
  ⌊wk₀⌋ (A ST.⇒[ k ] B) = cong₂ (eraseArrow (T.ArrowKind.quantity k) (T.ArrowKind.purity k)) (⌊wk₀⌋ A) (⌊wk₀⌋ B)
  ⌊wk₀⌋ (ST.μ F)        = cong μ-type (eraseF-wk₀ F)
  ⌊wk₀⌋ (ST.ν F _)      = cong ν-type (eraseF-wk₀ F)

  eraseF-wk₀ : ∀ {m} (F : T.Fun 0) → eraseF (T.wk₀F {m} F) ≡ eraseF F
  eraseF-wk₀ (ST.K A)   = cong K (⌊wk₀⌋ A)
  eraseF-wk₀ ST.Id      = refl
  eraseF-wk₀ (F ST.⊕ G) = cong₂ _⊕_ (eraseF-wk₀ F) (eraseF-wk₀ G)
  eraseF-wk₀ (F ST.⊗ G) = cong₂ _⊗_ (eraseF-wk₀ F) (eraseF-wk₀ G)
