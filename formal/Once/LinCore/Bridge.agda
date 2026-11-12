-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.LinCore.Bridge — plan 0.146 B1.3: the core's values against
-- master's (`Once.Denotation.ValueDomain.⟦_⟧ᴰᴵ`), the logical relation the
-- pass's meaning (`Pass.ev`, over the core's values) is related to master's
-- `evalᴰ` by.
--
--   * base words and first-order data by equality, structurally (`WK`, `WMu`:
--     a μ's constants are base types, so its values carry no function);
--   * an arrow pointwise: related arguments give computations bisimilar up
--     to the relation (the core's `Fn g` means `⟦ A ⟧ → Mg g ⟦ B ⟧`; master's
--     every arrow `⟦ A ⟧ᴰ → T∞ ⟦ B ⟧ᴰ`, so the core's is read through `up g`);
--   * a ν coinductively (`WNu`): each observation (the core's a block, the
--     Spec's `νM act`; master's `νᴵ.forceᴵ` a `T∞`) bisimilar up to the
--     layers' relation.
------------------------------------------------------------------------

{-# OPTIONS --guardedness #-}

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Sum.Relation.Binary.Pointwise using (Pointwise)
open import Once.Spec.Numerics using (TargetNum)
open import Once.IR.Semantics.Trace using (FFIAnswers)
open import Once.Spec.Word using (Carrier)
open import Once.IRTy
  using (IRTy; IRFunctor; K; Id; Unit; Void; _*_; _+_; _⇛[_]_; μ-type; ν-type; Int; Float; ⌈_⌉; ⌈_⌉F)
  renaming (_⊕_ to _⊕ᴵ_; _⊗_ to _⊗ᴵ_)
open import Once.Denotation.ValueDomain using (⟦_⟧ᴰᴵ)
open import Once.IR.Semantics.FunctorMeaning using (⟦_,_⟧-base; translateF)
open import Once.Spec.Polynomial using (SFunctor; μS; inS; ⟦_⟧SF)
open import Once.IR.Semantics.StreamInf using (νᴵ; module νᴵ)
open νᴵ using (forceᴵ)
import Once.LinCore.FromIR
import Once.LinCore.Bisim

module Once.LinCore.Bridge (fmt : TargetNum) (ans : FFIAnswers) where

open import Once.LinCore.NbEPLinCore fmt ans
open Once.LinCore.FromIR fmt ans using (⟪_⟫; lf; lfK; grade)
open Once.LinCore.Bisim fmt ans using (_≈[_]_)

-- master's polynomial of an IR functor
SF : IRFunctor → SFunctor
SF G = translateF Carrier Carrier ⌈ G ⌉F

------------------------------------------------------------------------
-- 1. A FUNCTOR'S BASE CONSTANT: the core's code (`lfK`) against master's
-- base interpretation, structurally. Constants no well-formed functor has
-- (an arrow, a ν) are the core's `Kzero`: nothing relates there.
------------------------------------------------------------------------

WK : ∀ (A : IRTy) {X} → FS (lfK A) X → ⟦ Carrier , Carrier ⟧-base ⌈ A ⌉ → Set
WK Unit         _ _               = ⊤
WK Void         () _
WK Int          x x′              = x ≡ x′
WK Float        x x′              = x ≡ x′
WK (A * B)      (x , y) (x′ , y′) = WK A x x′ × WK B y y′
WK (A + B)      x x′              = Pointwise (WK A) (WK B) x x′
WK (μ-type G)   _ _               = ⊤
WK (_ ⇛[ _ ] _) () _
WK (ν-type _)   () _

------------------------------------------------------------------------
-- 2. FIRST-ORDER DATA: a μ's values, layer by layer.
------------------------------------------------------------------------

mutual
  data WMu (F : IRFunctor) : Mu (lf F) → μS (SF F) → Set where
    wmu : ∀ {w w′} → WLμ F F w w′ → WMu F (inμ w) (inS w′)

  -- a layer: `G` the position's functor, `F` the μ's
  WLμ : ∀ F (G : IRFunctor) → FS (lf G) (Mu (lf F)) → ⟦ SF G ⟧SF (μS (SF F)) → Set
  WLμ F (K A)     x x′ = WK A x x′
  WLμ F Id        x x′ = WMu F x x′
  WLμ F (G ⊕ᴵ H)  x x′ = Pointwise (WLμ F G) (WLμ F H) x x′
  WLμ F (G ⊗ᴵ H)  (x , y) (x′ , y′) = WLμ F G x x′ × WLμ F H y y′

------------------------------------------------------------------------
-- 3. A ν: each observation, the core's block against master's `T∞`, up to
-- the layers' relation; coinductively.
------------------------------------------------------------------------

mutual
  record WNu (F : IRFunctor) (v : Nuᵐ (lf F)) (v′ : νᴵ (SF F)) : Set where
    coinductive
    field wout : emb (outν v) ≈[ WLν F F ] forceᴵ v′

  WLν : ∀ F (G : IRFunctor) → FS (lf G) (Nuᵐ (lf F)) → ⟦ SF G ⟧SF (νᴵ (SF F)) → Set
  WLν F (K A)     x x′ = WK A x x′
  WLν F Id        x x′ = WNu F x x′
  WLν F (G ⊕ᴵ H)  x x′ = Pointwise (WLν F G) (WLν F H) x x′
  WLν F (G ⊗ᴵ H)  (x , y) (x′ , y′) = WLν F G x x′ × WLν F H y y′
open WNu public

------------------------------------------------------------------------
-- 4. ★ THE RELATION, by the type.
------------------------------------------------------------------------

W : (A : IRTy) → ⟦ ⟪ A ⟫ ⟧ → ⟦ A ⟧ᴰᴵ → Set
W Unit         _ _               = ⊤
W Void         () _
W (A * B)      (x , y) (x′ , y′) = W A x x′ × W B y y′
W (A + B)      x x′              = Pointwise (W A) (W B) x x′
W (A ⇛[ π ] B) f f′              = ∀ {a a′} → W A a a′ → up (grade π) (f a) ≈[ W B ] f′ a′
W (μ-type F)   x x′              = WMu F x x′
W (ν-type F)   v v′              = WNu F v v′
W Int          x x′              = x ≡ x′
W Float        x x′              = x ≡ x′
