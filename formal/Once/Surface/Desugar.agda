------------------------------------------------------------------------
-- Once.Surface.Desugar
--
-- Desugaring transformation from Surface IR to Core IR.
-- Eliminates Let bindings by translating to categorical composition.
--
-- Parameterized by type interpretation and contract interface.
--
-- See D035: Two-Stage IR and MAlonzo Compilation
------------------------------------------------------------------------

open import Once.Type
open import Once.Contract using (ContractInterface)

module Once.Surface.Desugar
  (⟦_⟧ : Type → Set)
  (CI : ContractInterface)
  where

open import Once.Surface.IR ⟦_⟧ as S using (SurfaceIR; Let; Prim)
open import Once.IR using (module IRDef)
open import Data.String using (String)

module C = IRDef CI
open C
open ContractInterface CI

------------------------------------------------------------------------
-- Primitive support in Core IR
------------------------------------------------------------------------

-- | Primitive desugaring: needs a contract for the semantic function
--
-- TODO: This is a placeholder. Proper approach is:
-- 1. Surface Prim should become Domain expression
-- 2. Domain compiler creates proper contract
-- 3. For now, postulate a contract factory
--
postulate
  makeContract : ∀ {A B} → (⟦ A ⟧ → ⟦ B ⟧) → Contract A B

prim-desugar : ∀ {A B} → String → (⟦ A ⟧ → ⟦ B ⟧) → C.IR A B
prim-desugar name sem = C.Prim name (makeContract sem)

------------------------------------------------------------------------
-- Desugar transformation
------------------------------------------------------------------------

-- | Desugar: Surface IR → Core IR
--
-- Structural recursion that:
-- 1. Passes through all Core IR constructors unchanged
-- 2. Expands Let to composition + pairing
-- 3. Converts Prim to Core's prim
--
desugar : ∀ {A B} → SurfaceIR A B → C.IR A B

-- Category structure
desugar S.id = C.id
desugar (g S.∘ f) = desugar g C.∘ desugar f

-- Products
desugar S.fst = C.fst
desugar S.snd = C.snd
desugar S.⟨ f , g ⟩ = C.⟨ desugar f , desugar g ⟩

-- Coproducts
desugar S.inl = C.inl
desugar S.inr = C.inr
desugar S.[ f , g ] = C.[ desugar f , desugar g ]

-- Terminal/Initial
desugar S.terminal = C.terminal
desugar S.initial = C.initial

-- Exponential
desugar (S.curry f) = C.curry (desugar f)
desugar S.apply = C.apply

-- Recursive types
desugar S.fold = C.fold
desugar S.unfold = C.unfold

-- Effects
desugar S.arr = C.arr

-- | Let binding desugaring
--
-- let x = e1 in e2   desugars to   e2 ∘ ⟨ id , e1 ⟩
--
-- Intuition:
-- - Input a : A flows to both id (unchanged) and e1 (producing b : B)
-- - Result is pair (a, b) : A * B
-- - Body e2 : A * B → C receives this pair
-- - Body uses fst to access original input, snd for bound value
--
desugar (Let e1 e2) = desugar e2 C.∘ C.⟨ C.id , desugar e1 ⟩

-- | Primitive passthrough
--
-- Primitives are opaque - just convert to Core's Prim constructor
desugar (Prim name sem) = prim-desugar name sem
