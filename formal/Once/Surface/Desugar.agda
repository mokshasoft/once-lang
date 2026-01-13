------------------------------------------------------------------------
-- Once.Surface.Desugar
--
-- Desugaring transformation from Surface IR to Core IR.
-- Eliminates Let bindings by translating to categorical composition.
--
-- See D035: Two-Stage IR and MAlonzo Compilation
------------------------------------------------------------------------

module Once.Surface.Desugar where

open import Once.Type
open import Once.Surface.IR as S using (SurfaceIR; Let; Prim)
open import Once.IR as C

open import Data.String using (String)

------------------------------------------------------------------------
-- Primitive support in Core IR
------------------------------------------------------------------------

-- | Primitive desugaring: direct passthrough to Core IR
--
-- Prim is a real constructor in Once.IR. Primitives are opaque operations
-- that cannot be expressed in terms of categorical generators (id, ∘, fst,
-- snd, etc.). In MAlonzo compilation, this will be implemented via FFI.
--
-- The Core IR Prim constructor was added with:
--   1. Prim constructor in Once.IR
--   2. eval case in Once.Semantics (using evalPrim postulate)
--   3. optimize cases in Once.Optimize (pass through unchanged)
--   4. proof cases in Once.Optimize.Correct (all trivial refl)
--
prim-desugar : ∀ {A B} → String → C.IR A B
prim-desugar = C.Prim

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
desugar S.⟨ f , g ⟩ = C.⟨ desugar f , desugar g ⟩ C.Heap

-- Coproducts
desugar S.inl = C.inl C.Heap
desugar S.inr = C.inr C.Heap
desugar S.[ f , g ] = C.[ desugar f , desugar g ]

-- Terminal/Initial
desugar S.terminal = C.terminal
desugar S.initial = C.initial

-- Exponential
desugar (S.curry f) = C.curry (desugar f) C.Heap
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
desugar (Let e1 e2) = desugar e2 C.∘ C.⟨ C.id , desugar e1 ⟩ C.Heap

-- | Primitive passthrough
--
-- Primitives are opaque - just convert to Core's Prim constructor
desugar (Prim name) = prim-desugar name
