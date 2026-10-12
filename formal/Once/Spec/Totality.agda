-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Spec.Totality — what TOTAL and PRODUCTIVE mean (D311, plan 0.117 A).
--
-- SPEC. Once is a T+P language:
--   * TOTAL — a pure computation is a value (`M pure X = X`), so it has
--     nothing left to do;
--   * PRODUCTIVE — an effectful computation reaches each next event, or its
--     end, after finite work.
-- For a computation that RETURNS (grade `eff`, the free monad `T`), finite
-- work means: every path through its tree ends — in a result or a halt —
-- after finitely many events, whatever the world answers. `FiniteT` says so.
-- The answers may be infinitely many (a call into `Int` branches on every
-- integer), so this is well-foundedness of the tree, not a bound on it.
--
-- `Spec.Metatheory.Totality` claims it of every computation and of every
-- layer of every stream.
------------------------------------------------------------------------

module Once.Spec.Totality where

open import Data.Unit using (⊤)
open import Once.Spec.Type.Grade using (Purity; pure; eff)
open import Once.Spec.Meaning using (T; M)
open import Once.Denotation.TraceMonad using (ret; call; halt)

-- Every path ends: in a result, in a halt, or in a call whose every
-- continuation is again finite.
data FiniteT {X : Set} : T X → Set where
  fin-ret  : ∀ {x} → FiniteT (ret x)
  fin-call : ∀ {o a k} → (∀ b → FiniteT (k b)) → FiniteT (call o a k)
  fin-halt : ∀ {o a} → FiniteT (halt o a)

-- At a grade: a pure computation is a value, so nothing is left to check.
FiniteM : ∀ π {X : Set} → M π X → Set
FiniteM pure _ = ⊤
FiniteM eff  m = FiniteT m

------------------------------------------------------------------------
-- What the claims are tested on (`Spec.Metatheory.Totality`).
------------------------------------------------------------------------

open import Data.List using (List; []; _∷_)
open import Data.Maybe using (just)
open import Data.Bool using (false)
open import Data.Integer using (+_)
open import Data.Product using (_,_)
open import Once.Spec.Contract using (ISig)
open import Once.Spec.Type.Grade using (Many; mk-kind)
open import Once.Spec.Type using (Type; Int; _⇒[_]_; Id)
open import Once.Spec.Name using (CanonicalName; canonical)
open import Once.Spec.Syntax using (RVar; RInt)
open import Once.Spec.Core.PolyTy using (Sig; [])
import Once.Parser as Parser

-- STRUCTURED RECURSION ONLY: a definition that names itself, `f = f` …
selfRef : Parser.Entry
selfRef = Parser.e-fun (Parser.mkFunInfo "f" (just Int) (RVar "f") false)

-- … and one that names a later definition, `g = f` before `f = 0`.
forwardRef defF : Parser.Entry
forwardRef = Parser.e-fun (Parser.mkFunInfo "g" (just Int) (RVar "f") false)
defF       = Parser.e-fun (Parser.mkFunInfo "f" (just Int) (RInt (+ 0)) false)

-- AN EFFECTFUL STREAM: one operation `tick : Int → Int` (effectful) of the
-- interpretation, and the stream that calls it in every layer forever,
-- `unfold tick 0 : ν Id` at grade `eff` — the shape of every server.
tickTy : Type
tickTy = Int ⇒[ mk-kind Many eff ] Int

tickSig : ISig
tickSig = ("tick" , tickTy) ∷ []

tickDefs : Sig tickSig 0
tickDefs = []

tick : CanonicalName
tick = canonical ("tick" ∷ [])

open import Once.Spec.Core.Syntax tickDefs using (Tm; unfold; sigop; lit; lit-int)

ticker : Tm 0
ticker = unfold Id (sigop tick tickTy) (lit (lit-int (+ 0)))
