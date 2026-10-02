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
-- WHICH call a label is, and its argument, is the per-arch label→SigOp
-- resolution boundary (`CallResolver`), the same trust class as each arch's
-- event extractor and arith environment: the symbol table and argument
-- decoding of the loaded binary.
------------------------------------------------------------------------

module Once.Arith.Backend.CallAnswer where

open import Data.Nat using (ℕ)
open import Data.List using (List)
open import Data.Maybe using (Maybe; maybe′)
open import Data.Product using (Σ; _,_)
open import Data.String using (String)

open import Once.Type using (Type; Int; Float)
open import Once.Word using (Carrier)
import Once.Semantics.Value Carrier Carrier as M
open import Once.Denotation.Trace using (SigOpEvent)
open import Once.Denotation.TraceMonad using (Interp; CallOp; cdom; ccod)

-- The register word of a value of `B`, as the flat machine places it.
answer-word : (B : Type) → M.⟦ B ⟧ → ℕ
answer-word Int   v = v
answer-word Float v = v
answer-word _     _ = 0

-- The answering call a label is at a state, and its argument.
CallResolver : Set → Set
CallResolver State = String → State → Maybe (Σ CallOp λ o → M.⟦ cdom o ⟧)

-- What the world answers there, as the word the callee leaves behind; a label
-- that is no answering call (an emitting or halting one) leaves the sentinel.
answer-at : ∀ {State : Set} → Interp → CallResolver State
          → List SigOpEvent → String → State → ℕ
answer-at ι res h lbl s =
  maybe′ (λ { (o , a) → answer-word (ccod o) (Interp.answer ι h o a) }) 0 (res lbl s)
