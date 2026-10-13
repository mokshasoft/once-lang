-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Spec.Totality — what TOTAL and PRODUCTIVE mean (D311, plan 0.117 A).
--
-- SPEC. Once is a T+P language:
--   * TOTAL — a pure computation is a value (`M pure X = X`), so it has
--     nothing left to do;
--   * PRODUCTIVE — an effectful computation reaches each next event, or its
--     end, after finite work; it need not stop (D312).
-- An effectful computation is a tree of the completely iterative monad `T∞`,
-- so finite work means: every node of its tree is an event or the end — there
-- is no silent step to wait on forever. `ProductiveT∞` says so,
-- coinductively; it is what a `Tau` would break.
--
-- `Spec.Metatheory.Totality` claims it of every computation and of every
-- layer of every stream.
------------------------------------------------------------------------

module Once.Spec.Totality where

open import Data.Unit using (⊤)
open import Once.Spec.Type.Grade using (Purity; pure; eff⁺; eff)
open import Once.Spec.Guarded using (forget⁺)
open import Once.Spec.Meaning using (M)
open import Once.Spec.Iterative using (T∞; T∞F; ret∞; call∞; halt∞)
open Once.Spec.Iterative.T∞ using (force)

-- Every node is an event or the end, forever.
data ProductiveNode {X R : Set} (P : R → Set) : T∞F X R → Set where
  prod-ret  : ∀ {x} → ProductiveNode P (ret∞ x)
  prod-call : ∀ {o a k} → (∀ b → P (k b)) → ProductiveNode P (call∞ o a k)
  prod-halt : ∀ {o a} → ProductiveNode P (halt∞ o a)

record ProductiveT∞ {X : Set} (m : T∞ X) : Set where
  coinductive
  field node : ProductiveNode ProductiveT∞ (force m)

-- At a grade: a pure computation is a value, so nothing is left to check.
ProductiveM : ∀ π {X : Set} → M π X → Set
ProductiveM pure _ = ⊤
ProductiveM eff  m = ProductiveT∞ m
ProductiveM eff⁺ m = ProductiveT∞ (forget⁺ m)

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

-- A SERVER (D311): an echo loop over two operations of the interpretation,
-- `read : Unit → Int` and `write : Int → Unit`, each a call (`eff⁺`: an event
-- first). One round reads a value and writes it back, then loops; it never
-- answers `inj₁` (`Void`), so the loop runs forever — `iter step () : Void`
-- at `eff`. Every round performs two events, so the run is never silent.
open import Once.Spec.Type using (Unit; Void)
open import Once.Spec.Type.Grade using (eff⁺)

readTy writeTy : Type
readTy  = Unit ⇒[ mk-kind Many eff⁺ ] Int
writeTy = Int ⇒[ mk-kind Many eff⁺ ] Unit

echoSig : ISig
echoSig = ("read" , readTy) ∷ ("write" , writeTy) ∷ []

echoDefs : Sig echoSig 0
echoDefs = []

readN writeN : CanonicalName
readN  = canonical ("read" ∷ [])
writeN = canonical ("write" ∷ [])

import Once.Spec.Core.Syntax
module EchoSyntax = Once.Spec.Core.Syntax echoDefs

-- step = λ _ → inr (write (read ()))
echoStep : EchoSyntax.Tm 0
echoStep = EchoSyntax.lam Unit Many eff⁺
             (EchoSyntax.inr Void (EchoSyntax.app (EchoSyntax.sigop writeN writeTy)
                                                   (EchoSyntax.app (EchoSyntax.sigop readN readTy) EchoSyntax.unit)))

-- the server = iter step ()
echoServer : EchoSyntax.Tm 0
echoServer = EchoSyntax.iter echoStep EchoSyntax.unit
