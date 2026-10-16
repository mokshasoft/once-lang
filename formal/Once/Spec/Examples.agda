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
--   * an echo server: a loop whose every round reads a value and writes it
--     back; it never finishes;
--   * a silent loop: a loop whose round calls nothing — a correct program
--     that is never observed doing anything (D317).
------------------------------------------------------------------------

module Once.Spec.Examples where

open import Data.Integer using (+_)
open import Data.List using (List; []; _∷_)
open import Once.Spec.Grade using (Many; mk-kind; pure; act; eff)
open import Once.Spec.Name using (CanonicalName; canonical)
open import Once.Spec.Type using (Ty; Unit; Void; Int; Id)
open import Once.Spec.Signature using (int; unit; operation; _∶_; Signature)
open import Once.Spec.Surface.Syntax using (Module; mkModule; DTypeSig; DFunDef; PInt; RVar; RInt)
open import Once.Spec.Core.Syntax using (Defs; []; Tm; lam; app; unit; inr; lit; lit-int; unfold; sigop; iter)

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
-- A stream: `unfold tick 0 : ν Id act`, over one operation `tick : Int → Int`
------------------------------------------------------------------------

tick : CanonicalName
tick = canonical ("tick" ∷ [])

tickΣ : Signature
tickΣ = (tick ∶ operation int Many int) ∷ []

ticker : Tm [] 0 0
ticker = unfold Id (sigop tick (operation int Many int)) (lit (lit-int (+ 0)))

------------------------------------------------------------------------
-- A server: echo, over `read : Unit → Int` and `write : Int → Unit`
------------------------------------------------------------------------

readN writeN : CanonicalName
readN  = canonical ("read" ∷ [])
writeN = canonical ("write" ∷ [])

echoΣ : Signature
echoΣ = (readN ∶ operation unit Many int) ∷ (writeN ∶ operation int Many unit) ∷ []

-- round = λ _ → inr (write (read ())): never the exit; each round reads,
-- writes and continues.
echoRound : Tm [] 0 0
echoRound =
  lam Unit Many act
    (inr Void (app (sigop writeN (operation int Many unit))
                   (app (sigop readN (operation unit Many int)) unit)))

-- The server: `iter round ()`.
echoServer : Tm [] 0 0
echoServer = iter echoRound unit

------------------------------------------------------------------------
-- A silent loop: `iter (λ _ → inr ()) ()`, over no operation
------------------------------------------------------------------------

silentRound : Tm [] 0 0
silentRound = lam Unit Many act (inr Void unit)

silentLoop : Tm [] 0 0
silentLoop = iter silentRound unit
