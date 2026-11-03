{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Metatheory.Laws — the categorical structure and its internal
-- language (`Spec.Metatheory.Categorical`, `Equations`), proved.
--
--   Categorical   Laws.Categorical, Laws.Assoc (with Compose, ComposeG,
--                 ComposeShape, Combinators, Canon); the functors and the
--                 recursion schemes: Laws.MapFun, Laws.CataLaws,
--                 Laws.CataUnique, Laws.AnaLaws (with MapSem, MapLaws,
--                 MapV, MapCov, MapTop, LayerTy, LayerSem, CataSem, AnaSem)
--   Equations     Laws.Funs, Laws.Lets, Laws.LetAssoc, Laws.LetCase,
--                 Laws.Products, Laws.Sums, Laws.FoldRoll
--   toolkit       Laws.Tools, Laws.Views, Laws.Strengthen
------------------------------------------------------------------------

open import Data.Nat using (ℕ)
open import Once.Spec.Signature using (Signature; OneName)
open import Once.Spec.Numerics using (TargetNum)
open import Once.Spec.Core.Syntax using (Defs)

module Once.Metatheory.Laws (Σ : Signature) (u : OneName Σ) (fmt : TargetNum) {s : ℕ} (S : Defs s) where

open import Once.Spec.Metatheory using (Categorical; Equations)
import Once.Metatheory.Laws.Categorical Σ u fmt S as C
import Once.Metatheory.Laws.Assoc Σ u fmt S as A
import Once.Metatheory.Laws.Funs Σ u fmt S as F
import Once.Metatheory.Laws.Lets Σ u fmt S as L
import Once.Metatheory.Laws.LetAssoc Σ u fmt S as LA
import Once.Metatheory.Laws.LetCase Σ u fmt S as LC
import Once.Metatheory.Laws.Products Σ u fmt S as P
import Once.Metatheory.Laws.Sums Σ u fmt S as Su
import Once.Metatheory.Laws.MapFun Σ u fmt S as MF
import Once.Metatheory.Laws.CataLaws Σ u fmt S as CL
import Once.Metatheory.Laws.CataUnique Σ u fmt S as CU
import Once.Metatheory.Laws.AnaLaws Σ u fmt S as AL
import Once.Metatheory.Laws.FoldRoll Σ u fmt S as FR

categorical : Categorical Σ fmt S
categorical = record
  { compose-idˡ      = C.compose-idˡ
  ; compose-idʳ      = C.compose-idʳ
  ; compose-assoc    = A.compose-assoc
  ; fst-pairᶜ        = C.fst-pairᶜ
  ; snd-pairᶜ        = C.snd-pairᶜ
  ; pair-ηᶜ          = C.pair-ηᶜ
  ; terminal-uniqueᶜ = C.terminal-uniqueᶜ
  ; case-inlᶜ        = C.case-inlᶜ
  ; case-inrᶜ        = C.case-inrᶜ
  ; case-ηᶜ          = C.case-ηᶜ
  ; initial-uniqueᶜ  = C.initial-uniqueᶜ
  ; curry-βᶜ         = C.curry-βᶜ
  ; curry-ηᶜ         = C.curry-ηᶜ
  ; map-idᶜ          = MF.map-idᶜ
  ; map-composeᶜ     = MF.map-composeᶜ
  ; cata-βᶜ          = CL.cata-βᶜ
  ; cata-uniqueᶜ     = CU.cata-uniqueᶜ
  ; ana-βᶜ           = AL.ana-βᶜ
  ; ana-uniqueᶜ      = AL.ana-uniqueᶜ
  }

equations : Equations Σ fmt S
equations = record
  { app-lam   = F.app-lam
  ; lam-η     = F.lam-η
  ; let-unit  = L.let-unit
  ; let-assoc = LA.let-assoc
  ; let-drop  = L.let-drop
  ; fst-pair  = P.fst-pair
  ; snd-pair  = P.snd-pair
  ; pair-η    = P.pair-η
  ; unit-η    = P.unit-η
  ; case-inl  = Su.case-inl
  ; case-inr  = Su.case-inr
  ; case-η    = Su.case-η
  ; let-case  = LC.let-case
  ; absurd-η  = L.absurd-η
  ; fold-roll  = FR.fold-roll
  ; out-unfold = FR.out-unfold
  }
