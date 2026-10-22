-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Internal.Value — what a value of each type is, over the carriers chosen
-- for `Int` and `Float`.
--
-- INTERNAL (D333). `⟦ A ⟧` is the value space of `A`: products and sums are products and
-- sums of sets; an arrow is a function that may stop (`Res`), and an erased
-- (`Zero`) arrow takes no argument; `μ F` and `ν F` are the initial algebra and
-- the final coalgebra of `F`'s polynomial (`Spec.FunctorMeaning`). `⟦ A ⟧ᵍ`
-- is the graded contract domain (a pure contract returns a value), and
-- `eraseᵍ` takes it to `⟦ A ⟧`. The fold (`sem-cata`), the unfold (`sem-ana`)
-- and the layer maps between `⟦ F ⟧F` and the polynomial are defined
-- structurally, so they compute.
------------------------------------------------------------------------

module Once.Internal.Value (IntRep : Set) (FloatRep : Set) where

open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Once.Spec.Grade
open import Once.Type.Grade
open import Once.Internal.Type
open import Once.Spec.Type using (Type; Unit; Void; _*_; _+_; _⇒[_]_; Int; Float; K; Id; _⊕_; _⊗_)
open import Once.Internal.Res using (Res; stopped; returns; mapRes)
open import Once.Internal.Type.WellFormed using (IsBaseType; WellFormedF)
open import Once.Internal.FunctorMeaning using (μ-sem; ν-sem; translateF; ⟦_,_⟧-base)
open import Once.Spec.Type using (wf-K; wf-Id)
open import Once.Internal.Type.WellFormed using (base-Unit; base-Void; base-Int; base-Float; base-Prod; base-Sum; wf-Sum; wf-Prod)
open import Once.Internal.Polynomial
open Once.Internal.Polynomial.νS using (unfoldS)

-- | Semantic interpretation of μ-type (initial algebra)
--
-- Defined via translation to SFunctor.
-- μ-coherence is now provable (essentially refl).
--
⟦μ⟧ : Functor → Set
⟦μ⟧ = μ-sem IntRep FloatRep

-- | Semantic interpretation of ν-type (final coalgebra)
--
-- Defined via translation to SFunctor.
-- ν-coherence is now provable (essentially refl).
--
⟦ν⟧ : Functor → Set
⟦ν⟧ = ν-sem IntRep FloatRep

-- ⟦Guarded⟧ removed: productivity follows from IR totality (see IR/Totality.agda)

------------------------------------------------------------------------
-- Type Interpretation
------------------------------------------------------------------------

-- | Type interpretation
⟦_⟧ : Type → Set
⟦ Unit ⟧         = ⊤
⟦ Void ⟧         = ⊥
⟦ A * B ⟧        = ⟦ A ⟧ × ⟦ B ⟧
⟦ A + B ⟧        = ⟦ A ⟧ ⊎ ⟦ B ⟧
-- D143: GRADE-AWARE at the quantity. A `Zero`-graded argument is erased — it
-- has no runtime existence — so the erased arrow's value space takes NO
-- argument. Purity is still ignored (plan 0.52 M2: pure and eff arrows over the
-- same A, B are the same object); only the QUANTITY changes representation.
-- plan 0.98: the codomain is `Res`, because a function value CAN FAIL TO
-- RETURN. `curry (SigOp exit ∘ snd) : IR A (Int ⇛ Void)` is a closure whose
-- application ends the program, and at `B = Void` a total `⟦ A ⟧ → ⟦ B ⟧`
-- would be `⟦ A ⟧ → ⊥`. Same refutation as the deleted `eval` (D224) and the
-- same fix `semM` already took — the value domain admits "no value" wherever
-- a halt can reach. This does NOT duplicate `⟦_⟧ᴰ`: with `eval` gone this is
-- a value domain, not a second evaluator, and it carries no trace.
⟦ A ⇒[ mk-kind Zero π ] B ⟧ = ⟦ Unit ⟧ → Res ⟦ B ⟧   -- erased: no argument
⟦ A ⇒[ mk-kind One  π ] B ⟧ = ⟦ A ⟧ → Res ⟦ B ⟧
⟦ A ⇒[ mk-kind Many π ] B ⟧ = ⟦ A ⟧ → Res ⟦ B ⟧
-- OCP-0003: Fix removed, use μ-type/ν-type
⟦ μ-type F ⟧     = ⟦μ⟧ F
⟦ ν-type F _ ⟧   = ⟦ν⟧ F
-- GuardedT removed: productivity follows from IR totality
⟦ Int ⟧          = IntRep
⟦ Float ⟧        = FloatRep
-- TVar removed from Type; now in PolyType (see Once.Type)

------------------------------------------------------------------------
-- D250 (plan 0.104 A.2): the GRADED contract domain.
--
-- A contract is a value of its declared type, and `pure` is referential
-- transparency, so a pure contract's function pointer is TOTAL. `⟦_⟧ᵍ` is
-- `⟦_⟧` with that said at the arrow: a pure arrow returns a value, an effectful
-- one may stop (`Res`). Arrow domains stay machine values (a contract's
-- argument is a base type). `⟦_⟧` itself stays purity-blind: it is the
-- machine's value domain, and `eraseᵍ` is how a graded value reaches it.
------------------------------------------------------------------------

⟦_⟧ᵍ : Type → Set
⟦ A ⇒[ mk-kind Zero pure ] B ⟧ᵍ = ⟦ Unit ⟧ → ⟦ B ⟧ᵍ
⟦ A ⇒[ mk-kind One  pure ] B ⟧ᵍ = ⟦ A ⟧ → ⟦ B ⟧ᵍ
⟦ A ⇒[ mk-kind Many pure ] B ⟧ᵍ = ⟦ A ⟧ → ⟦ B ⟧ᵍ
⟦ A ⇒[ mk-kind Zero eff ] B ⟧ᵍ  = ⟦ Unit ⟧ → Res ⟦ B ⟧ᵍ
⟦ A ⇒[ mk-kind Zero act ] B ⟧ᵍ  = ⟦ Unit ⟧ → Res ⟦ B ⟧ᵍ
⟦ A ⇒[ mk-kind One  eff ] B ⟧ᵍ  = ⟦ A ⟧ → Res ⟦ B ⟧ᵍ
⟦ A ⇒[ mk-kind One  act ] B ⟧ᵍ  = ⟦ A ⟧ → Res ⟦ B ⟧ᵍ
⟦ A ⇒[ mk-kind Many eff ] B ⟧ᵍ  = ⟦ A ⟧ → Res ⟦ B ⟧ᵍ
⟦ A ⇒[ mk-kind Many act ] B ⟧ᵍ  = ⟦ A ⟧ → Res ⟦ B ⟧ᵍ
⟦ A * B ⟧ᵍ = ⟦ A ⟧ᵍ × ⟦ B ⟧ᵍ
⟦ A + B ⟧ᵍ = ⟦ A ⟧ᵍ ⊎ ⟦ B ⟧ᵍ
-- First-order: no arrow inside, so the machine value.
⟦ Unit ⟧ᵍ        = ⟦ Unit ⟧
⟦ Void ⟧ᵍ        = ⟦ Void ⟧
⟦ μ-type F ⟧ᵍ    = ⟦ μ-type F ⟧
⟦ ν-type F π ⟧ᵍ  = ⟦ ν-type F π ⟧
⟦ Int ⟧ᵍ         = ⟦ Int ⟧
⟦ Float ⟧ᵍ       = ⟦ Float ⟧

eraseᵍ : ∀ {B} → ⟦ B ⟧ᵍ → ⟦ B ⟧
eraseᵍ {A ⇒[ mk-kind Zero pure ] B} f = λ u → returns (eraseᵍ (f u))
eraseᵍ {A ⇒[ mk-kind One  pure ] B} f = λ x → returns (eraseᵍ (f x))
eraseᵍ {A ⇒[ mk-kind Many pure ] B} f = λ x → returns (eraseᵍ (f x))
eraseᵍ {A ⇒[ mk-kind Zero eff ] B}  f = λ u → mapRes eraseᵍ (f u)
eraseᵍ {A ⇒[ mk-kind Zero act ] B}  f = λ u → mapRes eraseᵍ (f u)
eraseᵍ {A ⇒[ mk-kind One  eff ] B}  f = λ x → mapRes eraseᵍ (f x)
eraseᵍ {A ⇒[ mk-kind One  act ] B}  f = λ x → mapRes eraseᵍ (f x)
eraseᵍ {A ⇒[ mk-kind Many eff ] B}  f = λ x → mapRes eraseᵍ (f x)
eraseᵍ {A ⇒[ mk-kind Many act ] B}  f = λ x → mapRes eraseᵍ (f x)
eraseᵍ {A * B} (a , b) = eraseᵍ a , eraseᵍ b
eraseᵍ {A + B} (inj₁ a) = inj₁ (eraseᵍ a)
eraseᵍ {A + B} (inj₂ b) = inj₂ (eraseᵍ b)
eraseᵍ {Unit} x = x
eraseᵍ {Void} x = x
eraseᵍ {μ-type F} x = x
eraseᵍ {ν-type F π} x = x
eraseᵍ {Int} x = x
eraseᵍ {Float} x = x

------------------------------------------------------------------------
-- Functor Interpretation (Set level)
--
-- Interprets Functor codes as Set → Set functions.
-- This parallels ⟦_⟧T at the Type level.
------------------------------------------------------------------------

⟦_⟧F : Functor → Set → Set
⟦ K A ⟧F X = ⟦ A ⟧
⟦ Id ⟧F X = X
⟦ F ⊕ G ⟧F X = ⟦ F ⟧F X ⊎ ⟦ G ⟧F X
⟦ F ⊗ G ⟧F X = ⟦ F ⟧F X × ⟦ G ⟧F X

------------------------------------------------------------------------
-- Coercions (Structural Definition)
--
-- Key insight: Define coercions by structural recursion on F, NOT via
-- subst on the coherence proof. This makes them compute properly and
-- allows definitional equality with structural operations.
------------------------------------------------------------------------

-- | Coercion from Type-level to Set-level functor application
coerce-functor : ∀ F X → ⟦ ⟦ F ⟧T X ⟧ → ⟦ F ⟧F ⟦ X ⟧
coerce-functor (K A) X x = x
coerce-functor Id X x = x
coerce-functor (F ⊕ G) X (inj₁ x) = inj₁ (coerce-functor F X x)
coerce-functor (F ⊕ G) X (inj₂ y) = inj₂ (coerce-functor G X y)
coerce-functor (F ⊗ G) X (x , y) = (coerce-functor F X x , coerce-functor G X y)

-- | Inverse coercion
coerce-functor⁻¹ : ∀ F X → ⟦ F ⟧F ⟦ X ⟧ → ⟦ ⟦ F ⟧T X ⟧
coerce-functor⁻¹ (K A) X x = x
coerce-functor⁻¹ Id X x = x
coerce-functor⁻¹ (F ⊕ G) X (inj₁ x) = inj₁ (coerce-functor⁻¹ F X x)
coerce-functor⁻¹ (F ⊕ G) X (inj₂ y) = inj₂ (coerce-functor⁻¹ G X y)
coerce-functor⁻¹ (F ⊗ G) X (x , y) = (coerce-functor⁻¹ F X x , coerce-functor⁻¹ G X y)
------------------------------------------------------------------------
-- Recursion Scheme Semantic Operations
--
-- These operations parallel the IR constructors for recursion schemes.
--
-- F is explicit where needed for Agda to resolve constraints.
------------------------------------------------------------------------

-- | Functorial map for polynomials (defined first for use in postulates)
sem-fmap : ∀ F {X Y : Set} → (X → Y) → ⟦ F ⟧F X → ⟦ F ⟧F Y
sem-fmap (K A) f x = x
sem-fmap Id f x = f x
sem-fmap (F ⊕ G) f (inj₁ x) = inj₁ (sem-fmap F f x)
sem-fmap (F ⊕ G) f (inj₂ y) = inj₂ (sem-fmap G f y)
sem-fmap (F ⊗ G) f (x , y) = (sem-fmap F f x , sem-fmap G f y)

------------------------------------------------------------------------
-- Type Coercions (Full ↔ Base Interpretation)
--
-- OCP-0003: For well-formed functors (K only with base types), the full
-- interpretation ⟦_⟧ equals the base interpretation ⟦_⟧-base. We prove
-- this by pattern matching on the Type.
--
-- For base types: definitionally equal
-- For complex types: ⟦_⟧-base returns ⊤, which is a "fallback" that
--   should never be reached for well-formed functors.
------------------------------------------------------------------------

-- | Coerce from full to base interpretation
--
-- This direction always works:
-- - Base types: identity (definitionally equal)
-- - Complex types: produce tt (base interp returns ⊤)
--
coerce-full-to-base : ∀ A → ⟦ A ⟧ → ⟦ IntRep , FloatRep ⟧-base A
coerce-full-to-base Unit x = x
coerce-full-to-base Void x = x
coerce-full-to-base (A * B) (a , b) = (coerce-full-to-base A a , coerce-full-to-base B b)
coerce-full-to-base (A + B) (inj₁ a) = inj₁ (coerce-full-to-base A a)
coerce-full-to-base (A + B) (inj₂ b) = inj₂ (coerce-full-to-base B b)
coerce-full-to-base (_ ⇒[ _ ] _) _ = tt   -- Functions (all kinds) → ⊤
coerce-full-to-base (μ-type _) _ = tt      -- μ → ⊤
coerce-full-to-base (ν-type _ _) _ = tt      -- ν → ⊤
-- GuardedT removed: productivity follows from IR totality
coerce-full-to-base Int x = x
coerce-full-to-base Float x = x
-- TVar removed from Type; now in PolyType (see Once.Type)

-- | Coerce from base to full interpretation
--
------------------------------------------------------------------------
-- Well-Formed Type Coercion
--
-- OCP-0003: Coercion from base to full interpretation requires an
-- IsBaseType proof, which is what makes it total.
--
-- For base types, the coercion is an identity (structurally).
-- Complex types (functions, μ-type, ν-type, GuardedT) are excluded
-- by the IsBaseType predicate, so we never need to produce values
-- we can't construct.
------------------------------------------------------------------------

-- | Coerce from base to full interpretation
--
-- Requires an IsBaseType proof, which is what makes it total.
--
coerce-base-to-full : ∀ {A} → IsBaseType A → ⟦ IntRep , FloatRep ⟧-base A → ⟦ A ⟧
coerce-base-to-full base-Unit x = x
coerce-base-to-full base-Void ()
coerce-base-to-full base-Int x = x
coerce-base-to-full base-Float x = x
coerce-base-to-full (base-Prod pA pB) (a , b) =
  (coerce-base-to-full pA a , coerce-base-to-full pB b)
coerce-base-to-full (base-Sum pA pB) (inj₁ a) = inj₁ (coerce-base-to-full pA a)
coerce-base-to-full (base-Sum pA pB) (inj₂ b) = inj₂ (coerce-base-to-full pB b)

------------------------------------------------------------------------
-- μ-type Coercions (OCP-0003)
--
-- Structural coercions between ⟦ F ⟧F X and ⟦ translateF IntRep FloatRep F ⟧SF X.
-- These use the type coercions above for the K case.
------------------------------------------------------------------------

-- | Coerce from ⟦ F ⟧F to ⟦ translateF F ⟧SF (for μ-type operations)
--
coerce-μ-in : ∀ F (X : Set) → ⟦ F ⟧F X → ⟦ translateF IntRep FloatRep F ⟧SF X
coerce-μ-in (K A) X x = coerce-full-to-base A x
coerce-μ-in Id X x = x
coerce-μ-in (F ⊕ G) X (inj₁ x) = inj₁ (coerce-μ-in F X x)
coerce-μ-in (F ⊕ G) X (inj₂ y) = inj₂ (coerce-μ-in G X y)
coerce-μ-in (F ⊗ G) X (x , y) = (coerce-μ-in F X x , coerce-μ-in G X y)

-- | Coerce from ⟦ translateF F ⟧SF to ⟦ F ⟧F (for μ-type operations)
--
-- Requires a WellFormedF proof to ensure K positions only use base types.
--
coerce-μ-out : ∀ {F} → WellFormedF F → (X : Set) → ⟦ translateF IntRep FloatRep F ⟧SF X → ⟦ F ⟧F X
coerce-μ-out (wf-K pA) X x = coerce-base-to-full pA x
coerce-μ-out wf-Id X x = x
coerce-μ-out (wf-Sum wfF wfG) X (inj₁ x) = inj₁ (coerce-μ-out wfF X x)
coerce-μ-out (wf-Sum wfF wfG) X (inj₂ y) = inj₂ (coerce-μ-out wfG X y)
coerce-μ-out (wf-Prod wfF wfG) X (x , y) = (coerce-μ-out wfF X x , coerce-μ-out wfG X y)

------------------------------------------------------------------------
-- μ-type Operations (OCP-0003: Defined via Once.Semantics.Functor)
--
-- These use Semantics.Functor's ⟨_⟩, outS, and cataS with structural
-- coercions to bridge between our ⟦_⟧F and its ⟦_⟧SF.
------------------------------------------------------------------------

-- | In: F(μF) → μF (algebra)
--
-- OCP-0003: Defined via Semantics.Functor's ⟨_⟩ constructor with coercion.
--
sem-In : ∀ (F : Functor) → ⟦ F ⟧F (⟦μ⟧ F) → ⟦μ⟧ F
sem-In F x = ⟨ coerce-μ-in F (⟦μ⟧ F) x ⟩

-- | Out: μF → F(μF) (destructor, inverse of In)
--
-- OCP-0003: Defined via Semantics.Functor's outS with coercion.
-- Requires a WellFormedF proof, which is what defines the coercion.
--
sem-Out : ∀ {F : Functor} → WellFormedF F → ⟦μ⟧ F → ⟦ F ⟧F (⟦μ⟧ F)
sem-Out {F} wf x = coerce-μ-out wf (⟦μ⟧ F) (outS (translateF IntRep FloatRep F) x)

-- | Catamorphism: given algebra F(A) → A, fold μF → A
--
-- OCP-0003: Defined via Semantics.Functor's cataS with coercions.
-- Requires a WellFormedF proof, which is what defines the coercion.
--
sem-cata : ∀ {F : Functor} → WellFormedF F → {A : Set} → (⟦ F ⟧F A → A) → ⟦μ⟧ F → A
sem-cata {F} wf {A} alg = cataS {translateF IntRep FloatRep F} (λ x → alg (coerce-μ-out wf A x))

-- | Paramorphism: fold with access to original substructure
--
-- OCP-0003 Phase 10: Derived from sem-cata, so termination is sem-cata's.
-- Para's algebra receives (⟦ F ⟧F (⟦μ⟧ F × A)), giving access to both
-- the original substructure (⟦μ⟧ F) and the recursive result (A).
--
-- Implementation: Encode via sem-cata with a product that carries both
-- the original structure and the recursive result.
--
sem-para : ∀ {F : Functor} → WellFormedF F → {A : Set}
         → (⟦ F ⟧F (⟦μ⟧ F × A) → A) → ⟦μ⟧ F → A
sem-para {F} wf {A} alg x = proj₂ (sem-cata wf alg' x)
  where
    alg' : ⟦ F ⟧F (⟦μ⟧ F × A) → (⟦μ⟧ F × A)
    alg' fx = (sem-In F (sem-fmap F proj₁ fx) , alg fx)

------------------------------------------------------------------------
-- ν-type Coercions (OCP-0003)
--
-- Similar to μ-type coercions, for ν-type (coinductive) operations.
------------------------------------------------------------------------

-- | Coerce from ⟦ F ⟧F to ⟦ translateF F ⟧SF (for ν-type operations)
coerce-ν-in : ∀ F (X : Set) → ⟦ F ⟧F X → ⟦ translateF IntRep FloatRep F ⟧SF X
coerce-ν-in = coerce-μ-in  -- Same structure

-- | Coerce from ⟦ translateF F ⟧SF to ⟦ F ⟧F (for ν-type operations)
-- Requires a WellFormedF proof, which is what defines the coercion.
coerce-ν-out : ∀ {F} → WellFormedF F → (X : Set) → ⟦ translateF IntRep FloatRep F ⟧SF X → ⟦ F ⟧F X
coerce-ν-out = coerce-μ-out  -- Same structure

------------------------------------------------------------------------
-- ν-type Operations (OCP-0003: Defined via Once.Semantics.Functor)
------------------------------------------------------------------------

-- | CoOut: νF → F(νF) (observation)
--
-- OCP-0003: Defined via Semantics.Functor's unfoldS with coercion.
-- Requires a WellFormedF proof, which is what defines the coercion.
--
-- plan 0.98: `Res`-valued — forcing a possibly-finite stream may find no
-- layer. This is `Out`'s pure counterpart and it stops exactly where `Out`'s
-- does.
sem-CoOut : ∀ {F : Functor} → WellFormedF F → ⟦ν⟧ F → Res (⟦ F ⟧F (⟦ν⟧ F))
sem-CoOut {F} wf x = mapRes (coerce-ν-out wf (⟦ν⟧ F)) (unfoldS x)

-- | CoIn: F(νF) → νF (coalgebra)
--
-- OCP-0003: Defined via Semantics.Functor's anaS with the identity coalgebra.
-- CoIn packages an F-layer observation as a ν-value.
--
sem-CoIn : ∀ (F : Functor) → ⟦ F ⟧F (⟦ν⟧ F) → ⟦ν⟧ F
unfoldS (sem-CoIn F x) = returns (coerce-ν-in F (⟦ν⟧ F) x)


-- | Anamorphism: given coalgebra A → F(A), unfold A → νF
--
-- D062: guardedness-CHECKED corecursion (global --guardedness) — the mutual
-- `sfmapSemAna` places the corecursive `sem-ana` calls structurally at SId, so
-- Agda sees the guard. Bridged to `sfmap` by `sfmapSemAna-is-sfmap`.
mutual
  sem-ana : ∀ (F : Functor) {A : Set} → (A → Res (⟦ F ⟧F A)) → A → ⟦ν⟧ F
  unfoldS (sem-ana F {A} coalg a) = semAnaLayer F A coalg (coalg a)

  -- Named and applied directly, not handed to `mapRes`: a partial application
  -- to a higher-order function hides the corecursive call from the
  -- guardedness checker.
  semAnaLayer : ∀ (F : Functor) (A : Set) → (A → Res (⟦ F ⟧F A))
              → Res (⟦ F ⟧F A) → Res (⟦ translateF IntRep FloatRep F ⟧SF (⟦ν⟧ F))
  semAnaLayer F A coalg stopped     = stopped
  semAnaLayer F A coalg (returns l) =
    returns (sfmapSemAna F (translateF IntRep FloatRep F) coalg (coerce-ν-in F A l))

  sfmapSemAna : ∀ (F : Functor) (H : SFunctor) {A : Set}
              → (A → Res (⟦ F ⟧F A)) → ⟦ H ⟧SF A → ⟦ H ⟧SF (⟦ν⟧ F)
  sfmapSemAna F (SK B)     coalg x        = x
  sfmapSemAna F SId        coalg a        = sem-ana F coalg a
  sfmapSemAna F (H₁ S⊕ H₂) coalg (inj₁ x) = inj₁ (sfmapSemAna F H₁ coalg x)
  sfmapSemAna F (H₁ S⊕ H₂) coalg (inj₂ y) = inj₂ (sfmapSemAna F H₂ coalg y)
  sfmapSemAna F (H₁ S⊗ H₂) coalg (x , y)  = (sfmapSemAna F H₁ coalg x , sfmapSemAna F H₂ coalg y)

