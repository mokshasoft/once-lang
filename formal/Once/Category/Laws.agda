-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson


------------------------------------------------------------------------
-- Once.Category.Laws
--
-- Proofs of the categorical laws for Once's IR.
-- These establish that IR forms a category.
------------------------------------------------------------------------

module Once.Category.Laws where


open import Once.Type
open import Once.IR
open import Once.Functor.Translate using (WellFormedF)
open import Once.CCC.Eval using (⟦_⟧; eval)

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; sym; trans; subst)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)

open import Function using (_∘′_)

------------------------------------------------------------------------
-- Category Laws
------------------------------------------------------------------------

-- | Left identity: id ∘ f ≡ f (semantically)
--
-- For any morphism f : A → B, composing with identity on the left
-- gives back f.
--
eval-id-left : ∀ {A B} (f : IR A B) (x : ⟦ A ⟧)
             → eval (id ∘ f) x ≡ eval f x
eval-id-left f x = refl

-- | Right identity: f ∘ id ≡ f (semantically)
--
-- For any morphism f : A → B, composing with identity on the right
-- gives back f.
--
eval-id-right : ∀ {A B} (f : IR A B) (x : ⟦ A ⟧)
              → eval (f ∘ id) x ≡ eval f x
eval-id-right f x = refl

-- | Associativity: (f ∘ g) ∘ h ≡ f ∘ (g ∘ h) (semantically)
--
-- Composition is associative.
--
eval-assoc : ∀ {A B C D} (f : IR C D) (g : IR B C) (h : IR A B) (x : ⟦ A ⟧)
           → eval ((f ∘ g) ∘ h) x ≡ eval (f ∘ (g ∘ h)) x
eval-assoc f g h x = refl

------------------------------------------------------------------------
-- Product Laws (Beta)
------------------------------------------------------------------------

-- | fst ∘ ⟨ f , g ⟩ ≡ f
--
-- Projecting the first component of a pair gives the first morphism.
--
eval-fst-pair : ∀ {A B C} (f : IR C A) (g : IR C B) (m : AllocMode) (x : ⟦ C ⟧)
              → eval (fst ∘ ⟨ f , g ⟩ m) x ≡ eval f x
eval-fst-pair f g m x = refl

-- | snd ∘ ⟨ f , g ⟩ ≡ g
--
-- Projecting the second component of a pair gives the second morphism.
--
eval-snd-pair : ∀ {A B C} (f : IR C A) (g : IR C B) (m : AllocMode) (x : ⟦ C ⟧)
              → eval (snd ∘ ⟨ f , g ⟩ m) x ≡ eval g x
eval-snd-pair f g m x = refl

------------------------------------------------------------------------
-- Product Laws (Eta/Uniqueness)
------------------------------------------------------------------------

-- | ⟨ fst , snd ⟩ ≡ id (semantically)
--
-- Pairing the projections gives back the identity on products.
--
eval-pair-eta : ∀ {A B} (m : AllocMode) (x : ⟦ A * B ⟧)
              → eval (⟨ fst , snd ⟩ m) x ≡ x
eval-pair-eta m (a , b) = refl

-- | Product uniqueness: ⟨ fst ∘ h , snd ∘ h ⟩ ≡ h (semantically)
--
-- Any morphism into a product is uniquely determined by its projections.
-- This is the universal property of products.
--
eval-pair-unique : ∀ {A B C} (h : IR C (A * B)) (m : AllocMode) (x : ⟦ C ⟧)
                 → eval (⟨ fst ∘ h , snd ∘ h ⟩ m) x ≡ eval h x
eval-pair-unique h m x with eval h x
... | (a , b) = refl

------------------------------------------------------------------------
-- Coproduct Laws (Beta)
------------------------------------------------------------------------

-- | (case f g) ∘ inl ≡ f
--
-- Case analysis on a left injection gives the left branch.
--
eval-case-inl : ∀ {A B C} (f : IR A C) (g : IR B C) (m : AllocMode) (x : ⟦ A ⟧)
              → eval ((case f g) ∘ inl m) x ≡ eval f x
eval-case-inl f g m x = refl

-- | (case f g) ∘ inr ≡ g
--
-- Case analysis on a right injection gives the right branch.
--
eval-case-inr : ∀ {A B C} (f : IR A C) (g : IR B C) (m : AllocMode) (x : ⟦ B ⟧)
              → eval ((case f g) ∘ inr m) x ≡ eval g x
eval-case-inr f g m x = refl

------------------------------------------------------------------------
-- Coproduct Laws (Eta/Uniqueness)
------------------------------------------------------------------------

-- | (case inl inr) ≡ id (semantically)
--
-- Case analysis that re-injects gives back identity on coproducts.
--
eval-case-eta : ∀ {A B} (m : AllocMode) (x : ⟦ A + B ⟧)
              → eval (case (inl m) (inr m)) x ≡ x
eval-case-eta m (inj₁ a) = refl
eval-case-eta m (inj₂ b) = refl

-- | Coproduct uniqueness: [ h ∘ inl , h ∘ inr ] ≡ h (semantically)
--
-- Any morphism from a coproduct is uniquely determined by its restrictions.
-- This is the universal property of coproducts.
--
eval-case-unique : ∀ {A B C} (h : IR (A + B) C) (m : AllocMode) (x : ⟦ A + B ⟧)
                 → eval (case (h ∘ inl m) (h ∘ inr m)) x ≡ eval h x
eval-case-unique h m (inj₁ a) = refl
eval-case-unique h m (inj₂ b) = refl

------------------------------------------------------------------------
-- Terminal Object Laws
------------------------------------------------------------------------

-- | Any two morphisms to Unit are equal (semantically)
--
-- Unit is terminal: there's a unique morphism from any object to Unit.
--
eval-terminal-unique : ∀ {A} (f : IR A Unit) (x : ⟦ A ⟧)
                     → eval f x ≡ eval terminal x
eval-terminal-unique f x with eval f x
... | tt = refl

------------------------------------------------------------------------
-- Initial Object Laws
------------------------------------------------------------------------

-- | Any two morphisms from Void are equal (semantically)
--
-- Void is initial: there's a unique morphism from Void to any object.
-- This is vacuously true since Void is empty.
--
eval-initial-unique : ∀ {A} (f : IR Void A) (x : ⟦ Void ⟧)
                    → eval f x ≡ eval initial x
eval-initial-unique f ()

------------------------------------------------------------------------
-- Exponential Laws (Curry/Apply adjunction)
------------------------------------------------------------------------

-- | apply ∘ ⟨ curry f ∘ fst , snd ⟩ ≡ f (semantically)
--
-- This is the beta law for exponentials.
-- The quantity {q} is phantom; the law holds for any quantity.
--
eval-curry-apply : ∀ {A B C k} (f : IR (A * B) C) (m₁ m₂ : AllocMode) (x : ⟦ A * B ⟧)
                 → eval (apply {k = k} ∘ ⟨ curry {k = k} f m₁ ∘ fst , snd ⟩ m₂) x ≡ eval f x
eval-curry-apply f m₁ m₂ (a , b) = refl

-- | curry (apply ∘ ⟨ g ∘ fst , snd ⟩) ≡ g (semantically, for functions)
--
-- This is the eta law for exponentials.
-- Note: This requires function extensionality for full generality,
-- but we can prove it pointwise.
--
-- With plain functions, application is direct function application.
-- The quantity {q} is phantom; the law holds for any quantity.
eval-curry-eta : ∀ {A B C k} (g : IR A (B ⇒[ k ] C)) (m₁ m₂ : AllocMode) (a : ⟦ A ⟧) (b : ⟦ B ⟧)
               → eval (curry {k = k} (apply {k = k} ∘ ⟨ g ∘ fst , snd ⟩ m₁) m₂) a b ≡ eval g a b
eval-curry-eta g m₁ m₂ a b = refl

------------------------------------------------------------------------
-- Distributivity Laws
------------------------------------------------------------------------

-- Distributivity of products over coproducts (C × (A + B) ≅ (C × A) + (C × B))
-- See Once.Surface.Correct (distribute-inl and distribute-inr).

------------------------------------------------------------------------
-- Functoriality of Product and Coproduct
------------------------------------------------------------------------

-- | bimap f g = ⟨ f ∘ fst , g ∘ snd ⟩ preserves identity
--
eval-bimap-id : ∀ {A B} (m : AllocMode) (x : ⟦ A * B ⟧)
              → eval (⟨ id ∘ fst , id ∘ snd ⟩ m) x ≡ x
eval-bimap-id m (a , b) = refl

-- | bimap preserves composition
--
eval-bimap-compose : ∀ {A B C D E F}
                     (f : IR B C) (g : IR A B) (h : IR E F) (i : IR D E)
                     (m₁ m₂ : AllocMode) (x : ⟦ A * D ⟧)
                   → eval (⟨ (f ∘ g) ∘ fst , (h ∘ i) ∘ snd ⟩ m₁) x
                     ≡ eval (⟨ f ∘ fst , h ∘ snd ⟩ m₁ ∘ ⟨ g ∘ fst , i ∘ snd ⟩ m₂) x
eval-bimap-compose f g h i m₁ m₂ (a , d) = refl

-- | bicase f g = [ inl ∘ f , inr ∘ g ] preserves identity
--
eval-bicase-id : ∀ {A B} (m : AllocMode) (x : ⟦ A + B ⟧)
               → eval (case (inl m ∘ id) (inr m ∘ id)) x ≡ x
eval-bicase-id m (inj₁ a) = refl
eval-bicase-id m (inj₂ b) = refl

------------------------------------------------------------------------
-- Recursion Scheme Laws (OCP-0003)
------------------------------------------------------------------------
--
-- The old fold/unfold laws have been replaced by structured recursion
-- schemes: In/Cata for initial algebras, Out/Ana for final coalgebras.
--
-- Identity laws (semantic):
--   Cata (In m) ≡ id   -- Identity catamorphism
--   Ana Out ≡ id       -- Identity anamorphism
--
-- Fusion laws (conceptual):
--   h ∘ cata alg = cata alg'   (if h ∘ alg = alg' ∘ fmap h)
--   ana coalg ∘ h = ana coalg' (if coalg ∘ h = fmap h ∘ coalg')
--
-- Hylomorphism deforestation:
--   cata alg ∘ ana coalg = hylo alg coalg
--
-- Full proofs require functor fmap operations and universal properties.
-- See SPF.agda for the semantic foundations.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Arrow Laws (D032: Effect System)
------------------------------------------------------------------------
--
-- The arr combinator lifts pure functions to effectful morphisms.
-- arr : (A ⇒ B) → Eff A B
--
-- At runtime, Eff A B is represented the same as A ⇒ B (a function).
-- The distinction is purely for effect tracking at the type level.
--
-- Arrow axioms (from Hughes' "Generalising Monads to Arrows"):
-- In the context of Once, arr is essentially identity on function values.
--
------------------------------------------------------------------------

-- | `arr` is RETIRED (plan 0.52 M2). With ungraded `IRTy`, `A ⇒[pure] B` and
-- `A ⇛ B` are the SAME object, so the lift was the identity morphism and the
-- constructor was removed from `Once.IR`.
--
-- The lemma that stood here — `eval (arr {q = Many}) f ≡ f` — is therefore not
-- merely unprovable but unstatable, and it is subsumed by `eval-id` above:
-- what `arr` denoted, `id` denotes. Deleted rather than adapted; there is no
-- content to carry over. (D141 / the plan-0.64 audit found it, three months
-- after M2 retired the constructor, because this module is an ISLAND that no
-- gate builds.)

-- | arr ∘ curry ≡ curry with effectful codomain (conceptually)
--
-- This captures that currying followed by arr produces an effectful
-- curried function. The semantics are the same because effects are
-- purely a type-level distinction.
--
-- Note: The exact formulation depends on how effectful composition
-- is defined. For Once's simple model where Eff = function at runtime,
-- this is trivially true.

------------------------------------------------------------------------
-- OCP-0003: Recursion Scheme Laws (Initial Algebras / Final Coalgebras)
------------------------------------------------------------------------
--
-- These laws establish the properties of the recursion scheme
-- constructors In, Cata, Out, Ana, and Hylo.
--
-- Key theorems:
-- 1. Lambek's Lemma: In and Out are inverses (μF ≅ F(μF))
-- 2. Catamorphism computation: how cata unfolds through In
-- 3. Anamorphism observation: how ana builds through Out
-- 4. Hylo fusion: cata ∘ ana = hylo (deforestation)
------------------------------------------------------------------------

-- Note: We import from IR (not Machine) to match the ℤ interpretation
-- used by eval. Machine uses ℕ which would cause type mismatches.
open import Once.Semantics.Machine
  using (sem-In; sem-Out; sem-cata; sem-CoOut; sem-ana;
         sem-fmap;
         coerce-functor; coerce-functor⁻¹; coerce-round-trip; coerce⁻¹-round-trip;
         ⟦_⟧F;
         -- Proven for well-formed functors
         sem-cata-compute)
-- 0.47: the axiom-using identity laws live in Once.Semantics.Machine.Laws.
open import Once.Semantics.Machine.Laws using (sem-cata-In-id; sem-ana-Out-id)
-- GuardedT/sem-unguard/sem-hylo-guarded removed: productivity follows from IR totality
open import Once.Functor.Translate using (WellFormedF)

open import Once.Postulates using (extensionality)

------------------------------------------------------------------------
-- Lambek's Lemma (Semantic Level)
--
-- At the semantic level, μF ≅ F(μF) via sem-In and sem-Out.
-- This is proven via sem-In-Out and sem-Out-In for well-formed functors.
--
-- At the IR level:
--   - In constructs μ-type values
--   - Cata folds μ-type values with an algebra
--   - Out destructs ν-type values (NOT μ-type!)
--   - Ana unfolds to build ν-type values
--
-- The key IR-level law is that Cata with the In algebra is identity.
------------------------------------------------------------------------

-- | Cata In ≡ id (identity catamorphism)
--
-- Folding with the constructor algebra gives back the original value.
-- This is the canonical way to express that μF ≅ F(μF) at the IR level.
--
-- Derivation from semantic laws:
--   eval (Cata (In m)) x
--   = sem-cata F (λ fa → eval (In m) (coerce⁻¹ fa)) x
--   = sem-cata F (λ fa → sem-In F (coerce (coerce⁻¹ fa))) x
--   = sem-cata F (λ fa → sem-In F fa) x           (by coerce⁻¹-round-trip)
--   = sem-cata F sem-In x                          (by funext)
--   = x                                            (by sem-cata-In-id)
--
-- Proven using function extensionality.
-- The semantic foundation is sem-cata-In-id in Once.Semantics.Value.
--
-- Note: Requires a WellFormedF proof.
--
eval-cata-In-id : ∀ {F : Functor} → (wf : WellFormedF F) → (m : AllocMode) (x : ⟦ μ-type F ⟧)
                → eval (Cata {F} wf (In {F} wf m)) x ≡ x
eval-cata-In-id {F} wf m x =
  let -- The algebra used by Cata evaluation: λ fa → eval (In m) (coerce⁻¹ fa)
      -- which equals λ fa → sem-In F (coerce (coerce⁻¹ fa))
      -- By round-trip, coerce (coerce⁻¹ fa) = fa
      alg-pointwise : ∀ fa → sem-In F (coerce-functor F (μ-type F) (coerce-functor⁻¹ F (μ-type F) fa)) ≡ sem-In F fa
      alg-pointwise fa = cong (sem-In F) (coerce⁻¹-round-trip F (μ-type F) fa)

      -- By function extensionality, the algebras are equal
      alg-eq : (λ fa → sem-In F (coerce-functor F (μ-type F) (coerce-functor⁻¹ F (μ-type F) fa))) ≡ sem-In F
      alg-eq = extensionality alg-pointwise

      -- Step 1: Substitute equal algebras in sem-cata
      step1 : sem-cata wf (λ fa → sem-In F (coerce-functor F (μ-type F) (coerce-functor⁻¹ F (μ-type F) fa))) x
            ≡ sem-cata wf (sem-In F) x
      step1 = cong (λ alg → sem-cata wf alg x) alg-eq

      -- Step 2: Apply sem-cata-In-id (well-formed)
      step2 : sem-cata wf (sem-In F) x ≡ x
      step2 = sem-cata-In-id wf x

  in trans step1 step2

------------------------------------------------------------------------
-- Catamorphism Laws
--
-- The catamorphism is the unique homomorphism from an initial algebra.
------------------------------------------------------------------------

-- | Functorial map at the Type level
--
-- This applies a function through the functor structure, working with
-- Type-level functor application (⟦ F ⟧T) rather than Set-level (⟦ F ⟧F).
--
fmap-Type : ∀ F {X Y : Type} → (⟦ X ⟧ → ⟦ Y ⟧) → ⟦ ⟦ F ⟧T X ⟧ → ⟦ ⟦ F ⟧T Y ⟧
fmap-Type (K A) f x = x
fmap-Type Id f x = f x
fmap-Type (F ⊕ G) f (inj₁ x) = inj₁ (fmap-Type F f x)
fmap-Type (F ⊕ G) f (inj₂ y) = inj₂ (fmap-Type G f y)
fmap-Type (F ⊗ G) f (x , y) = (fmap-Type F f x , fmap-Type G f y)

------------------------------------------------------------------------
-- Fmap-Coercion Coherence
--
-- This lemma relates sem-fmap (Set-level) with fmap-Type (Type-level)
-- through the coercion functions. It's key for proving cata/hylo laws.
--
-- The proof requires understanding how coercions interact with sum/product
-- constructors. Since coercions are defined via subst on non-trivial
-- equality proofs, we need auxiliary lemmas.
------------------------------------------------------------------------

-- | fmap-coerce coherence: coerce⁻¹ ∘ sem-fmap ∘ coerce ≡ fmap-Type
--
-- Postulated because the coercion functions (defined via subst on
-- sem-functor-coherence) don't compute for compound functors.
-- A full proof would require lemmas about how subst distributes over
-- sum and product constructors.
--
-- The semantic soundness is guaranteed by:
-- 1. sem-fmap and fmap-Type have identical recursive structure
-- 2. coerce/coerce⁻¹ are round-trip inverses
-- 3. For base functors (K, Id), coercions are definitionally refl
--
-- Import coherence lemmas from Core (coerce-struct = coerce-functor now)
open import Once.Semantics.Machine
  using (fmap-struct-coherence; fmap-struct-coherence′; sem-fmap-Type)

-- | fmap-Type equals sem-fmap-Type (both defined identically)
fmap-Type-eq : ∀ F {X Y : Type} (f : ⟦ X ⟧ → ⟦ Y ⟧) (x : ⟦ ⟦ F ⟧T X ⟧)
             → fmap-Type F f x ≡ sem-fmap-Type F f x
fmap-Type-eq (K A) f x = refl
fmap-Type-eq Id f x = refl
fmap-Type-eq (F ⊕ G) f (inj₁ x) = cong inj₁ (fmap-Type-eq F f x)
fmap-Type-eq (F ⊕ G) f (inj₂ y) = cong inj₂ (fmap-Type-eq G f y)
fmap-Type-eq (F ⊗ G) f (x , y) = cong₂ _,_ (fmap-Type-eq F f x) (fmap-Type-eq G f y)

-- | coerce⁻¹ ∘ sem-fmap ∘ coerce ≡ fmap-Type (for Type-level input)
--
-- Now that coerce-functor is defined structurally (not via subst),
-- this follows directly from fmap-struct-coherence and fmap-Type-eq.
--
fmap-coerce-coherence : ∀ F {X Y : Type} (f : ⟦ X ⟧ → ⟦ Y ⟧) (x : ⟦ ⟦ F ⟧T X ⟧)
                      → coerce-functor⁻¹ F Y (sem-fmap F f (coerce-functor F X x)) ≡ fmap-Type F f x
fmap-coerce-coherence F f x = trans (fmap-struct-coherence F f x) (sym (fmap-Type-eq F f x))

-- | coerce⁻¹ ∘ sem-fmap ≡ fmap-Type ∘ coerce⁻¹ (for Set-level input)
--
fmap-coerce-coherence′ : ∀ F {X Y : Type} (f : ⟦ X ⟧ → ⟦ Y ⟧) (y : ⟦ F ⟧F ⟦ X ⟧)
                       → coerce-functor⁻¹ F Y (sem-fmap F f y) ≡ fmap-Type F f (coerce-functor⁻¹ F X y)
fmap-coerce-coherence′ F f y = trans (fmap-struct-coherence′ F f y) (sym (fmap-Type-eq F f _))

-- | Catamorphism computation law
--
-- cata alg (In x) ≡ alg (fmap (cata alg) x)
--
-- This is the defining equation for catamorphisms: to fold a structure,
-- first recursively fold all substructures, then apply the algebra.
--
-- Proof:
--   eval (Cata alg ∘ In m) x
--   = eval (Cata alg) (sem-In F (coerce x))      (by eval composition and In)
--   = sem-cata F alg′ (sem-In F (coerce x))       (by eval Cata, where alg′ = λ fa → eval alg (coerce⁻¹ fa))
--   = alg′ (sem-fmap F (sem-cata F alg′) (coerce x))    (by sem-cata-compute)
--   = eval alg (coerce⁻¹ (sem-fmap F (sem-cata F alg′) (coerce x)))
--   = eval alg (fmap-Type F (sem-cata F alg′) x)       (by fmap-coerce-coherence)
--   = eval alg (fmap-Type F (eval (Cata alg)) x)      (by def of eval (Cata alg))
--
eval-cata-In : ∀ {F : Functor} → (wf : WellFormedF F) → ∀ {A : Type} (alg : IR (⟦ F ⟧T A) A) (m : AllocMode)
               (x : ⟦ ⟦ F ⟧T (μ-type F) ⟧)
             → eval (Cata {F} wf alg ∘ In {F} wf m) x ≡
               eval alg (fmap-Type F (eval (Cata {F} wf alg)) x)
eval-cata-In {F} wf {A} alg m x =
  let -- The algebra lifted to Set level
      alg′ : ⟦ F ⟧F ⟦ A ⟧ → ⟦ A ⟧
      alg′ = λ fa → eval alg (coerce-functor⁻¹ F A fa)

      -- Step 1: Apply sem-cata-compute (well-formed)
      -- sem-cata wf alg′ (sem-In F (coerce x)) = alg′ (sem-fmap F (sem-cata wf alg′) (coerce x))
      step1 : sem-cata wf alg′ (sem-In F (coerce-functor F (μ-type F) x))
            ≡ alg′ (sem-fmap F (sem-cata wf alg′) (coerce-functor F (μ-type F) x))
      step1 = sem-cata-compute wf alg′ (coerce-functor F (μ-type F) x)

      -- Step 2: Apply fmap-coerce-coherence
      -- coerce⁻¹ (sem-fmap F f (coerce x)) = fmap-Type F f x
      step2 : coerce-functor⁻¹ F A (sem-fmap F (sem-cata wf alg′) (coerce-functor F (μ-type F) x))
            ≡ fmap-Type F (sem-cata wf alg′) x
      step2 = fmap-coerce-coherence F (sem-cata wf alg′) x

      -- Step 3: Combine - alg′ of step1 = eval alg (coerce⁻¹ ...)
      -- eval alg (coerce⁻¹ (sem-fmap F ...)) = eval alg (fmap-Type F ... x)
      step3 : eval alg (coerce-functor⁻¹ F A (sem-fmap F (sem-cata wf alg′) (coerce-functor F (μ-type F) x)))
            ≡ eval alg (fmap-Type F (sem-cata wf alg′) x)
      step3 = cong (eval alg) step2

  in trans step1 step3

------------------------------------------------------------------------
-- Hylomorphism Laws
--
-- The hylomorphism combines an algebra and coalgebra into a single
-- recursive computation without building intermediate structure.
--
-- Note: Unlike in Haskell where Fix = μ = ν, Once distinguishes
-- μ-type (inductive) from ν-type (coinductive). Therefore the
-- composition Cata ∘ Ana doesn't type-check directly.
--
-- The hylo is the primitive operation; cata and ana are special cases.
------------------------------------------------------------------------

-- | Hylo is equivalent to Fuse (OCP-0003 / D062)
--
-- D062: `Hylo`/`Fuse` now carry the SAME natural transformation (`NatTr`), and
-- `eval` denotes both by the identical total fold `sem-fuseNat (appNatTr-F t)`.
-- So `fuse ≡ hylo` is definitional — one structural scheme, two packagings.
-- (The old IR-coalgebra bridge `eval (Hylo alg coalg) ≡ eval (Fuse alg (coalg
-- ∘ In))` is gone: the coalgebra is no longer a general IR morphism.)
eval-hylo-is-fuse : ∀ {F G : Functor} → (wfF : WellFormedF F) → (wfG : WellFormedF G)
                    → ∀ {B : Type} (alg : IR (⟦ F ⟧T B) B) (t : NatTr G F)
                    → (x : ⟦ μ-type G ⟧)
                    → eval (Hylo wfF wfG alg t) x ≡ eval (Fuse wfF wfG alg t) x
eval-hylo-is-fuse wfF wfG alg t x = refl

------------------------------------------------------------------------
-- Ana-Out Identity Law (Coinductive)
--
-- OCP-0003: With productivity derived from IR totality, Ana Out now type-checks.
-- Out : IR (ν-type F) (⟦ F ⟧T (ν-type F))
-- Ana : IR A (⟦ F ⟧T A) → IR A (ν-type F)
--
-- So Ana Out : IR (ν-type F) (ν-type F) is well-typed.
-- Semantically: Ana Out ≡ id (identity anamorphism)
------------------------------------------------------------------------

-- | Ana Out ≡ id (identity anamorphism)
--
-- Unfolding with the destructor coalgebra gives back the original value.
-- This is the dual of eval-cata-In-id.
--
-- Proof:
--   eval (Ana wf (Out wf)) x
--   = sem-ana F (λ a → coerce-functor F _ (eval (Out wf) a)) x
--   = sem-ana F (λ a → coerce-functor F _ (coerce-functor⁻¹ F _ (sem-CoOut wf a))) x
--   = sem-ana F (sem-CoOut wf) x   [by coerce⁻¹-round-trip + extensionality]
--   = x                            [by sem-ana-Out-id]
--
eval-ana-Out-id : ∀ {F : Functor} → (wf : WellFormedF F) (x : ⟦ ν-type F ⟧)
                → eval (Ana {F} wf (Out {F} wf)) x ≡ x
eval-ana-Out-id {F} wf x =
  let -- The actual coalgebra from eval (with round-trip coercions)
      actual-coalg : ⟦ ν-type F ⟧ → ⟦ F ⟧F ⟦ ν-type F ⟧
      actual-coalg a = coerce-functor F (ν-type F) (coerce-functor⁻¹ F (ν-type F) (sem-CoOut wf a))
      -- The coalgebra expected by sem-ana-Out-id
      expected-coalg : ⟦ ν-type F ⟧ → ⟦ F ⟧F ⟦ ν-type F ⟧
      expected-coalg = sem-CoOut wf
      -- They're pointwise equal via round-trip
      coalg-eq : ∀ a → actual-coalg a ≡ expected-coalg a
      coalg-eq a = coerce⁻¹-round-trip F (ν-type F) (sem-CoOut wf a)
      -- Therefore equal as functions (by extensionality)
      coalg-ext : actual-coalg ≡ expected-coalg
      coalg-ext = extensionality coalg-eq
      -- Substitute to get sem-ana with expected-coalg
      step : sem-ana F actual-coalg x ≡ sem-ana F expected-coalg x
      step = cong (λ c → sem-ana F c x) coalg-ext
  in trans step (sem-ana-Out-id wf x)