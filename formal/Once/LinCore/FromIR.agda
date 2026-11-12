-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.LinCore.FromIR — plan 0.146 B1.3: master's IR into the linear core.
--
-- Master's IR (`Once.IR`) is translated into the RESOLVED, GRADED IR of
-- `Once.LinCore.Pass` (its definitions are labels over the earlier ones, its
-- blocks carry their grade judgments), which `Pass.tr` compiles into the core
-- and `Pass.pass-ok` proves. This module is the first half: the types.
--
--   * `⟪_⟫ : IRTy → LTy`. An arrow keeps its purity as the core's grade (D413:
--     `pure` and `act` are both a finite block); the IR's arrows are many-use.
--   * `lf : IRFunctor → LF`. A constant of a base type is a code built from
--     `Kone`, `Kzero`, `Kb` (`K (A * B)` is `K A ⊗ K B`), so `⟪ ⟦ F ⟧ X ⟫` is
--     `LF∙ (lf F) ⟪ X ⟫` for every well-formed functor (`⟪⟫-TI`).
------------------------------------------------------------------------

{-# OPTIONS --guardedness #-}

open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; cong₂)
open import Once.Spec.Numerics using (TargetNum)
open import Once.IR.Semantics.Trace using (FFIAnswers)
open import Once.Spec.Grade using (Purity; fin; eff)
open import Once.IRTy
  using (IRTy; IRFunctor; K; Id; Unit; Void; _*_; _+_; _⇛[_]_; μ-type; ν-type; Int; Float;
         ⟦_⟧TI; IsBaseTypeI; base-Unit; base-Void; base-Int; base-Float; base-Prod; base-Sum;
         WellFormedFI; wf-K; wf-Id; wf-Sum; wf-Prod)
  renaming (_⊕_ to _⊕ᴵ_; _⊗_ to _⊗ᴵ_)

module Once.LinCore.FromIR (fmt : TargetNum) (ans : FFIAnswers) where

open import Once.LinCore.NbEPLinCore fmt ans

------------------------------------------------------------------------
-- 1. THE TYPES.
------------------------------------------------------------------------

-- an arrow's purity, as far as the core tells grades apart (D412: the Spec's
-- `pure` is the block with no event)
grade : Purity → Gr
grade (fin _) = act
grade eff     = eff

mutual
  ⟪_⟫ : IRTy → LTy
  ⟪ Unit ⟫         = One
  ⟪ Void ⟫         = Zero
  ⟪ A * B ⟫        = ⟪ A ⟫ ⊗t ⟪ B ⟫
  ⟪ A + B ⟫        = ⟪ A ⟫ ⊕t ⟪ B ⟫
  ⟪ A ⇛[ π ] B ⟫   = Fn many (grade π) ⟪ A ⟫ ⟪ B ⟫
  ⟪ μ-type F ⟫     = μt (lf F)
  ⟪ ν-type F ⟫     = Nu (lf F)
  ⟪ Int ⟫          = Bt int
  ⟪ Float ⟫        = Bt float

  lf : IRFunctor → LF
  lf (K A)     = lfK A
  lf Id        = Idf
  lf (F ⊕ᴵ G)  = lf F ⊕f lf G
  lf (F ⊗ᴵ G)  = lf F ⊗f lf G

  -- a functor's constant. `WellFormedFI` admits only base types; an arrow or
  -- a ν has no code (the Spec's functor constants are base, `WFFun`), so they
  -- are given `Kzero`, which no well-formed functor reaches.
  lfK : IRTy → LF
  lfK Unit             = Kone
  lfK Void             = Kzero
  lfK Int              = Kb int
  lfK Float            = Kb float
  lfK (A * B)          = lfK A ⊗f lfK B
  lfK (A + B)          = lfK A ⊕f lfK B
  lfK (μ-type G)       = Kμ (lf G)
  lfK (_ ⇛[ _ ] _)     = Kzero
  lfK (ν-type _)       = Kzero

-- a base constant's code means the type, at every carrier
⟪⟫-K : ∀ {A} → IsBaseTypeI A → ∀ X → LF∙ (lfK A) X ≡ ⟪ A ⟫
⟪⟫-K base-Unit         X = refl
⟪⟫-K base-Void         X = refl
⟪⟫-K base-Int          X = refl
⟪⟫-K base-Float        X = refl
⟪⟫-K (base-Prod a b)   X = cong₂ _⊗t_ (⟪⟫-K a X) (⟪⟫-K b X)
⟪⟫-K (base-Sum a b)    X = cong₂ _⊕t_ (⟪⟫-K a X) (⟪⟫-K b X)

-- ★ a well-formed functor's layer translates as its code's layer
⟪⟫-TI : ∀ {F} → WellFormedFI F → ∀ X → ⟪ ⟦ F ⟧TI X ⟫ ≡ LF∙ (lf F) ⟪ X ⟫
⟪⟫-TI (wf-K b)      X = Relation.Binary.PropositionalEquality.sym (⟪⟫-K b ⟪ X ⟫)
⟪⟫-TI wf-Id         X = refl
⟪⟫-TI (wf-Sum f g)  X = cong₂ _⊕t_ (⟪⟫-TI f X) (⟪⟫-TI g X)
⟪⟫-TI (wf-Prod f g) X = cong₂ _⊗t_ (⟪⟫-TI f X) (⟪⟫-TI g X)
