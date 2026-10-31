-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Machine.MuRep   (D364)
--
-- HOW A μ VALUE IS REPRESENTED, decided by the functor's static shape. A μ
-- value is always a pointer to the heap; what `In` must do to make one
-- depends on how its layer `⟦ F ⟧TI (μ-type F)` arrives:
--
--   * `mu-box`  — `F = K Int` / `K Float`: the layer is a register literal
--     (or, as any `Int` input may be, a pointer to a cell holding one), so
--     `In` allocates a BOX and stores the layer's word in its first cell.
--     The consumers (`out-μ`, the cata's call) read that cell back.
--   * `mu-unit` — `F = K Unit`: the layer has no residence at all (D074),
--     so `In` allocates a block and stores nothing; a `Unit` layer is
--     valid anywhere.
--   (Both blocks are two cells, the second unused: every emitted allocation
--   is a pair block, `AllocMin`, which is what keeps a pointer's successor
--   cell in bounds, `FlatPtrBounds`.)
--   * `mu-ptr`  — every other functor: the layer (a sum, a product, a μ, or
--     `Void`) is already a heap pointer, and `In` hands it on unchanged.
--
-- Before D364 `In` was `mov-to-output` for every functor, which left a
-- literal (or nothing) where the value relation demands a pointer, so
-- `obs-correct-In` was false at the first two shapes.
------------------------------------------------------------------------

module Once.CCC.Machine.MuRep where

open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import Once.IRTy
  using (IRTy; IRFunctor; K; Id; _⊕_; _⊗_; Unit; Void; Int; Float; _*_; _+_; _⇛_; μ-type; ν-type;
         FitsInRegI; fits-int; fits-float; ⟦_⟧TI)

data MuRep : Set where
  mu-box mu-unit mu-ptr : MuRep

mu-rep : IRFunctor → MuRep
mu-rep (K Unit)        = mu-unit
mu-rep (K Void)        = mu-ptr
mu-rep (K Int)         = mu-box
mu-rep (K Float)       = mu-box
mu-rep (K (A * B))     = mu-ptr
mu-rep (K (A + B))     = mu-ptr
mu-rep (K (A ⇛ B))     = mu-ptr
mu-rep (K (μ-type G))  = mu-ptr
mu-rep (K (ν-type G))  = mu-ptr
mu-rep Id              = mu-ptr
mu-rep (F ⊕ G)         = mu-ptr
mu-rep (F ⊗ G)         = mu-ptr

-- "not boxed": what a μ whose relation is its layer at the same cell needs.
NotBox : MuRep → Set
NotBox mu-box  = ⊥
NotBox mu-unit = ⊤
NotBox mu-ptr  = ⊤

Unboxed : IRFunctor → Set
Unboxed F = NotBox (mu-rep F)

-- A boxed functor is `K` of a register-fitting type.
data BoxView : IRFunctor → Set where
  bv : ∀ {A} → FitsInRegI A → BoxView (K A)

box-view : ∀ F → mu-rep F ≡ mu-box → BoxView F
box-view (K Int)   refl = bv fits-int
box-view (K Float) refl = bv fits-float
box-view (K Unit)  ()
box-view (K Void)  ()
box-view (K (A * B)) ()
box-view (K (A + B)) ()
box-view (K (A ⇛ B)) ()
box-view (K (μ-type G)) ()
box-view (K (ν-type G)) ()
box-view Id ()
box-view (F ⊕ G) ()
box-view (F ⊗ G) ()

-- …and its layer fits a register.
box-fit : ∀ {F} → mu-rep F ≡ mu-box → FitsInRegI (⟦ F ⟧TI (μ-type F))
box-fit {F} e with box-view F e
... | bv fit = fit

-- a boxed functor is not unboxed
box-not-unboxed : ∀ {F} → mu-rep F ≡ mu-box → Unboxed F → ⊥
box-not-unboxed e u = subst NotBox e u

-- a register-fitting type is not `Unit`
fit-not-unit : ∀ {A} → FitsInRegI A → A ≡ Unit → ⊥
fit-not-unit fits-int   ()
fit-not-unit fits-float ()
