-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

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
open import Once.Surface.IR as S using (SurfaceIR; Let; SigOp)
open import Once.IR as C
open import Once.Arith.SigOp.Builders using (generic-info)
open import Once.Functor.Translate using (IsBaseType; IsConcrete)
open import Once.CanonicalName using (bare)

open import Data.String using (String)

------------------------------------------------------------------------
-- Primitive support in Core IR
------------------------------------------------------------------------

-- | Primitive desugaring: direct passthrough to Core IR
--
-- SigOp is a real constructor in Once.IR. Primitives are opaque operations
-- that cannot be expressed in terms of categorical generators (id, ∘, fst,
-- snd, etc.). In MAlonzo compilation, this will be implemented via FFI.
--
-- The Core IR SigOp constructor was added with:
--   1. SigOp constructor in Once.IR
--   2. eval case in Once.Semantics (using evalSigOp)
--   3. optimize cases in Once.Optimize (pass through unchanged)
--   4. proof cases in Once.Optimize.Correct (all trivial refl)
--
sigOp-desugar : ∀ {A B} → IsBaseType A → IsConcrete B → String → C.IR C.⌊ A ⌋ C.⌊ B ⌋
sigOp-desugar bA cB name = C.SigOp (generic-info (bare name) bA cB)

------------------------------------------------------------------------
-- Desugar transformation
------------------------------------------------------------------------

-- | Desugar: Surface IR → Core IR (parameterized on default allocation mode)
--
-- Plan 0.14 follow-up (2026-05-18): the default allocation mode for
-- pair/inl/inr/curry constructors is now a parameter, wired up from the
-- CLI `--alloc` flag. Previously hardcoded to Heap, which silently
-- dropped the user's CLI choice. The `desugar-default` alias preserves
-- the historical Heap behavior for callers that don't care.
--
-- Structural recursion that:
-- 1. Passes through all Core IR constructors unchanged
-- 2. Expands Let to composition + pairing
-- 3. Converts SigOp to Core's sigOp
--
desugar : ∀ {A B} → C.AllocMode → SurfaceIR A B → C.IR C.⌊ A ⌋ C.⌊ B ⌋

-- Category structure
desugar m S.id = C.id
desugar m (g S.∘ f) = desugar m g C.∘ desugar m f

-- Products
desugar m S.fst = C.fst
desugar m S.snd = C.snd
desugar m S.⟨ f , g ⟩ = C.⟨ desugar m f , desugar m g ⟩ m

-- Coproducts
desugar m S.inl = C.inl m
desugar m S.inr = C.inr m
desugar m S.[ f , g ] = C.case (desugar m f) (desugar m g)

-- Terminal/Initial
desugar m S.terminal = C.terminal
desugar m S.initial = C.initial

-- Exponential
desugar m (S.curry f) = C.curry (desugar m f) m
desugar m S.apply = C.apply

-- OCP-0003: fold/unfold removed

-- Effects
desugar m S.arr = C.id

-- | Let binding desugaring
--
-- let x = e1 in e2   desugars to   e2 ∘ ⟨ id , e1 ⟩
--
-- Intuition:
-- - Input1 a : A flows to both id (unchanged) and e1 (producing b : B)
-- - Result is pair (a, b) : A * B
-- - Body e2 : A * B → C receives this pair
-- - Body uses fst to access original input, snd for bound value
--
desugar m (Let e1 e2) = desugar m e2 C.∘ C.⟨ C.id , desugar m e1 ⟩ m

-- | Primitive passthrough
--
-- Primitives are opaque - just convert to Core's SigOp constructor
desugar m (SigOp name bA cB) = sigOp-desugar bA cB name

-- | Historical default: Heap allocation. Preserves pre-Plan-0.14
-- behavior for callers that don't thread an AllocMode.
desugar-default : ∀ {A B} → SurfaceIR A B → C.IR C.⌊ A ⌋ C.⌊ B ⌋
desugar-default = desugar C.Heap