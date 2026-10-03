-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Arith.Backend.CallAnswer — plan 0.105 Phase 4 (decision (a)): WHAT
-- AN EXTERNAL CALL LEAVES IN THE RETURN REGISTER.
--
-- The concrete machine's external-call step (`RunTraceCore.ret-call`) writes
-- the world's answer where the calling convention says a callee leaves its
-- result: the arch's return register, which is the `Output` role on every
-- target (a0 / rax / eax). This module is the arch-neutral half: the word an
-- answer occupies, and the answer itself, read off the interpretation at the
-- binary's log.
--
-- The word is the flat machine's: a register-fitting codomain (`Int`,
-- `Float`) is its literal (`call-sigop-val … (just fit)`, and `lit-word` is
-- the identity); any other codomain gets the unit sentinel `0`
-- (`unit-storedvalue`), as the flat machine writes it.
--
-- A pure FFI call is answered from the interpretation's PURE half, which is
-- what the flat machine computes for it (`semM (fs-ffi FS)`); the two halves
-- of a world need not agree, so the resolver must say which half a label is.
--
-- WHICH call a label is, and its argument, is the per-arch label→SigOp
-- resolution boundary (`CallResolver`), the same trust class as each arch's
-- event extractor and arith environment: the symbol table and argument
-- decoding of the loaded binary.
------------------------------------------------------------------------

module Once.Arith.Backend.CallAnswer where

open import Data.Nat using (ℕ)
open import Data.List using (List)
open import Data.Maybe using (Maybe; maybe′)
open import Once.CanonicalName using (CanonicalName)
open import Data.String using (String)

open import Once.Type using (Type; Int; Float)
open import Once.Word using (Carrier)
import Once.Semantics.Value Carrier Carrier as M
open import Once.Denotation.Trace using (SigOpEvent)
open import Once.Denotation.TraceMonad using (Interp; CallOp; cdom; ccod; Key; key; kdom; kcod; callKey; calls; pures; answer; pure; _∈K?_)
open import Relation.Nullary using (Dec; yes; no)
open import Data.List.Membership.Propositional using (_∈_)

-- The register word of a value of `B`, as the flat machine places it.
answer-word : (B : Type) → M.⟦ B ⟧ → ℕ
answer-word Int   v = v
answer-word Float v = v
answer-word _     _ = 0

-- What an external call a label is at a state resolves to, with its argument:
-- an ANSWERING call (the world answers it, given the calls before it), or a
-- PURE FFI call (plan 0.105: the interpretation's pure half, a fixed function —
-- no history, no event). An emitting or halting call resolves to `nothing`.
data ResolvedCall : Set where
  answering : (o : CallOp) → M.⟦ cdom o ⟧ → ResolvedCall
  pure-ffi  : (nm : CanonicalName) (A B : Type) → M.⟦ A ⟧ → ResolvedCall

CallResolver : Set → Set
CallResolver State = String → State → Maybe ResolvedCall

-- The word a resolved call leaves in the return register: the implementation's
-- answer for a SigOp the interpretation declares; the sentinel for one it does
-- not (unreachable for a program linked against its signatures).
answering-word : (ι : Interp) → List SigOpEvent → (o : CallOp) → M.⟦ cdom o ⟧
               → Dec (callKey o ∈ calls ι) → ℕ
answering-word ι h o a (yes p) = answer-word (ccod o) (answer ι h o p a)
answering-word ι h o a (no _)  = 0

value-word : (ι : Interp) (k : Key) → M.⟦ kdom k ⟧ → Dec (k ∈ pures ι) → ℕ
value-word ι k a (yes p) = answer-word (kcod k) (pure ι k p a)
value-word ι k a (no _)  = 0

resolved-word : Interp → List SigOpEvent → ResolvedCall → ℕ
resolved-word ι h (answering o a)     = answering-word ι h o a (callKey o ∈K? calls ι)
resolved-word ι h (pure-ffi nm A B a) = value-word ι (key nm A B) a (key nm A B ∈K? pures ι)

-- What the world answers there, as the word the callee leaves behind; a label
-- that resolves to no value-returning call (an emitting or halting one) leaves
-- the sentinel.
answer-at : ∀ {State : Set} → Interp → CallResolver State
          → List SigOpEvent → String → State → ℕ
answer-at ι res h lbl s = maybe′ (resolved-word ι h) 0 (res lbl s)
