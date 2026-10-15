{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Spec.Examples — the programs the claims are tested on
-- (`Spec.Metatheory`).
--
--   * a definition that names itself, and one that names a later
--     definition: there is no general recursion, so neither is a program;
--   * a stream that calls an operation in every layer, forever: the shape of
--     every effectful stream;
--   * an echo server: each round reads a value, then returns the call that
--     writes it back as the next request; it never finishes.
------------------------------------------------------------------------

module Once.Spec.Examples where

open import Data.Integer using (+_)
open import Data.List using (List; []; _∷_)
open import Once.Spec.Grade using (Many; mk-kind; pure; act; eff)
open import Once.Spec.Name using (CanonicalName; canonical)
open import Once.Spec.Type using (Ty; Unit; Void; Int; Id)
open import Once.Spec.Signature using (int; unit; arrow; _∶_; Signature)
open import Once.Spec.Surface.Syntax using (Module; mkModule; DTypeSig; DFunDef; PInt; RVar; RInt)
open import Once.Spec.Core.Syntax using (Defs; []; Tm; lam; app; unit; inr; lit; lit-int; unfold; sigop; request; anaEff)

------------------------------------------------------------------------
-- Structured recursion only
------------------------------------------------------------------------

-- `f : Int; f = f`
selfReference : Module
selfReference = mkModule (DTypeSig "f" PInt ∷ DFunDef "f" (RVar "f") ∷ [])

-- `g : Int; g = f; f : Int; f = 0`
forwardReference : Module
forwardReference =
  mkModule (DTypeSig "g" PInt ∷ DFunDef "g" (RVar "f") ∷ DTypeSig "f" PInt ∷ DFunDef "f" (RInt (+ 0)) ∷ [])

------------------------------------------------------------------------
-- A stream: `unfold tick 0 : ν Id eff`, over one operation `tick : Int → Int`
------------------------------------------------------------------------

tick : CanonicalName
tick = canonical ("tick" ∷ [])

tickΣ : Signature
tickΣ = (tick ∶ arrow int (mk-kind Many eff) int) ∷ []

ticker : Tm [] 0 0
ticker = unfold Id (sigop tick (arrow int (mk-kind Many eff) int)) (lit (lit-int (+ 0)))

------------------------------------------------------------------------
-- A server: echo, over `read : Act Unit Int` and `write : Act Int Unit`
------------------------------------------------------------------------

readN writeN : CanonicalName
readN  = canonical ("read" ∷ [])
writeN = canonical ("write" ∷ [])

echoΣ : Signature
echoΣ = (readN ∶ arrow unit (mk-kind Many act) int) ∷ (writeN ∶ arrow int (mk-kind Many act) unit) ∷ []

-- One round: read a value, and request writing it back; the state is `Unit`
-- and the loop never finishes (`Void`).
echoStep : Tm [] 0 0
echoStep =
  lam Unit Many act
    (inr Void (request writeN (arrow int (mk-kind Many act) unit)
                       (app (sigop readN (arrow unit (mk-kind Many act) int)) unit)
                       (lam Unit Many pure unit)))

echoServer : Tm [] 0 0
echoServer = app (anaEff echoStep) unit
