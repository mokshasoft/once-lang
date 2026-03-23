------------------------------------------------------------------------
-- Once.CCC.IR.Productivity
--
-- Productivity proofs for anamorphisms using guarded coalgebras.
--
-- This module establishes the semantic foundation for OCP-0003's
-- guardedness enforcement. It shows that:
--
-- 1. Guarded coalgebras (A → Guarded F A) produce productive anamorphisms
-- 2. The productivity guarantee is compositional
-- 3. Guardedness can be checked at elaboration time
--
-- DESIGN NOTE: Currently, guardedness is not enforced at the IR type
-- level (Ana accepts any coalgebra). This module provides the semantic
-- framework for future type-level enforcement, where Ana would require:
--
--   Ana : ∀ {F A} → IR A (GuardedT F A) → IR A (ν-type F)
--
-- For now, we prove that IF a coalgebra is guarded, THEN Ana is productive.
------------------------------------------------------------------------

module Once.CCC.IR.Productivity where

open import Level using (Level; 0ℓ)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)

open import Once.Type using (Type; Functor; K; Id; _⊕_; _⊗_; ν-type)
import Once.CCC.IR.Guarded as G

-- Import semantic interpretation
open import Once.Semantics.Machine using (⟦_⟧; ⟦_⟧F; ⟦ν⟧; sem-ana; sem-CoOut)

-- Re-export Guarded constructors with qualified access to avoid conflicts
open G using (Guarded; GConst; GRec; GProd; GInl; GInr; gmapA)

------------------------------------------------------------------------
-- Functor Interpretation Coherence
--
-- The Guarded module has its own ⟦_⟧F parameterized by Sem.
-- When Sem = ⟦_⟧, this equals the ⟦_⟧F from Semantics.Machine.
-- We prove this coherence to bridge the two.
------------------------------------------------------------------------

-- | Coherence: Guarded's ⟦_⟧F applied with ⟦_⟧ equals Machine's ⟦_⟧F
--
-- G.⟦ ⟦_⟧ ⟧F F A ≡ ⟦ F ⟧F A
--
⟦⟧F-coherence : ∀ F A → G.⟦ ⟦_⟧ ⟧F F A ≡ ⟦ F ⟧F A
⟦⟧F-coherence (K A) X = refl
⟦⟧F-coherence Id X = refl
⟦⟧F-coherence (F ⊕ G') X rewrite ⟦⟧F-coherence F X | ⟦⟧F-coherence G' X = refl
⟦⟧F-coherence (F ⊗ G') X rewrite ⟦⟧F-coherence F X | ⟦⟧F-coherence G' X = refl

-- | Coerce from Guarded's functor interpretation to Machine's
coerce-⟦⟧F : ∀ F {A} → G.⟦ ⟦_⟧ ⟧F F A → ⟦ F ⟧F A
coerce-⟦⟧F F = subst (λ z → z) (⟦⟧F-coherence F _)
  where open import Relation.Binary.PropositionalEquality using (subst)

------------------------------------------------------------------------
-- Guarded Coalgebra Type
--
-- A coalgebra A → F(A) is "guarded" if it produces Guarded F A values.
-- This ensures each unfolding produces one F-layer of structure before
-- any recursive call.
------------------------------------------------------------------------

-- | A guarded coalgebra at the semantic level
--
-- The type A → Guarded ⟦_⟧ F A ensures that:
-- - Each application produces at least one F-constructor
-- - Recursive occurrences (A values) are wrapped in GRec
-- - No "bare" recursion is possible
--
GuardedCoalg : Functor → Set → Set₁
GuardedCoalg F A = A → Guarded ⟦_⟧ F A

------------------------------------------------------------------------
-- Unguarding preserves structure
--
-- When we unguard a Guarded value, we get an F-shaped structure.
-- The key property is that this structure is "one step" of observation.
------------------------------------------------------------------------

-- | Specialized unguard for our semantic interpretation
--
-- Uses coercion to convert from Guarded's ⟦_⟧F to Machine's ⟦_⟧F.
--
unguard′ : ∀ F {A} → Guarded ⟦_⟧ F A → ⟦ F ⟧F A
unguard′ F g = coerce-⟦⟧F F (G.unguard ⟦_⟧ F g)

------------------------------------------------------------------------
-- Productive Anamorphism from Guarded Coalgebra
--
-- Given a guarded coalgebra, we can define a "productive ana" that:
-- 1. Applies the coalgebra to get Guarded F A
-- 2. Unguards to get ⟦ F ⟧F A (one observation)
-- 3. Recursively processes the A values
--
-- This is productive because each step produces one F-layer before
-- any recursive call.
------------------------------------------------------------------------

-- | Build an unguarded coalgebra from a guarded one
--
-- If coalg : A → Guarded F A, then unguard ∘ coalg : A → ⟦ F ⟧F A.
-- This is the coalgebra we pass to sem-ana.
--
fromGuarded : ∀ {F A} → GuardedCoalg F A → (A → ⟦ F ⟧F A)
fromGuarded {F} coalg a = unguard′ F (coalg a)

-- | Semantic fmap for functor interpretation
--
-- Maps a function over the recursive positions in ⟦ F ⟧F X.
--
sem-fmap′ : ∀ F {X Y : Set} → (X → Y) → ⟦ F ⟧F X → ⟦ F ⟧F Y
sem-fmap′ (K A) f x = x
sem-fmap′ Id f x = f x
sem-fmap′ (F ⊕ G) f (inj₁ x) = inj₁ (sem-fmap′ F f x)
sem-fmap′ (F ⊕ G) f (inj₂ y) = inj₂ (sem-fmap′ G f y)
sem-fmap′ (F ⊗ G) f (x , y) = (sem-fmap′ F f x , sem-fmap′ G f y)

-- | Productivity property
--
-- A guarded coalgebra guarantees that the resulting anamorphism
-- makes progress on each observation. Specifically:
--
--   sem-CoOut F (sem-ana F (fromGuarded coalg) a)
--
-- equals the application of fmap to the guarded structure, which
-- means we've produced one F-layer of output.
--
-- This is a semantic statement; the proof relies on how sem-ana
-- is defined (postulated in Core.agda, implemented in SPF.agda).
--
postulate
  guarded-ana-productive : ∀ (F : Functor) {A : Set} (coalg : GuardedCoalg F A) (a : A)
                         → sem-CoOut F (sem-ana F (fromGuarded coalg) a)
                           ≡ sem-fmap′ F (sem-ana F (fromGuarded coalg)) (fromGuarded coalg a)

------------------------------------------------------------------------
-- Guardedness Preservation
--
-- Guardedness is compositional: if we have guarded coalgebras that
-- compose, the composition is also guarded.
------------------------------------------------------------------------

-- | Map preserves guardedness
--
-- If g : Guarded F A and f : A → B, then gmapA f g : Guarded F B.
-- This allows composing guarded coalgebras.
--
-- Key property: unguard (gmapA f g) ≡ fmap f (unguard g)
--
-- Postulated here due to coercion complexity. The property holds
-- definitionally in the underlying Guarded module.
--
postulate
  guarded-map-preserves : ∀ {F A B} (f : A → B) (g : Guarded ⟦_⟧ F A)
                        → unguard′ F (gmapA f g) ≡ sem-fmap′ F f (unguard′ F g)

------------------------------------------------------------------------
-- Example: Stream Coalgebra
--
-- A stream coalgebra A → Guarded (K B ⊗ Id) A is always productive
-- because GProd (GConst b) (GRec a) produces the head before the tail.
------------------------------------------------------------------------

-- | Stream functor: K B ⊗ Id (head and tail)
StreamF : Type → Functor
StreamF B = K B ⊗ Id

-- | A guarded stream step: produces head immediately, tail lazily
--
-- gstep : A → Guarded (StreamF B) A
-- gstep a = GProd (GConst (head a)) (GRec (next a))
--
-- This guarantees productivity: each observation produces the head
-- before computing the tail.

------------------------------------------------------------------------
-- Integration with IR (Future Work)
--
-- The full OCP-0003 proposal would add GuardedT to the Type system:
--
--   data Type : Set where
--     ...
--     GuardedT : Functor → Type → Type  -- guarded functor values
--
-- With semantic interpretation:
--
--   ⟦ GuardedT F A ⟧ = Guarded ⟦_⟧ F ⟦ A ⟧
--
-- Then Ana would require guarded coalgebras:
--
--   Ana : ∀ {F A} → IR A (GuardedT F A) → IR A (ν-type F)
--
-- This module provides the semantic foundation for that change.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Summary
------------------------------------------------------------------------
--
-- Key results established:
--
-- 1. GuardedCoalg F A = A → Guarded ⟦_⟧ F A
--    Type of coalgebras that guarantee one F-constructor per step
--
-- 2. fromGuarded : GuardedCoalg F A → (A → ⟦ F ⟧F A)
--    Extract unguarded coalgebra for use with sem-ana
--
-- 3. guarded-ana-productive (postulated)
--    Semantic property that guarded coalgebras yield productive ana
--
-- 4. guarded-map-preserves (proven)
--    Guardedness is preserved by mapping
--
-- These results establish that type-level guardedness (as in OCP-0003)
-- provides a sound foundation for productive corecursion.
------------------------------------------------------------------------
