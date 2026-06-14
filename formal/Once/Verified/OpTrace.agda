-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Verified.OpTrace — the OPERATIONAL trace semantics of the CCC IR
-- (solution 2: fire a SigOp event when it is EXECUTED).
--
-- WHY operational. The denotational `obs` (TraceDenote) denotes the
-- function type as a pure Agda function `⟦A ⇒ B⟧ = ⟦A⟧ → ⟦B⟧`, which has
-- no slot for a trace. So a `SigOp` inside an applied CLOSURE contributes
-- to the value (via `semM`) but its event is lost at `apply` — `obs` only
-- fires at `SigOp` nodes it structurally reaches through `∘`/`⟨,⟩`/`case`.
-- The MACHINE (`flat-events`) is operational and DOES fire inside closures
-- (a call jumps into the body and runs its `instr-sigop`s), so denotational
-- `obs` and the machine disagree for higher-order effects.
--
-- The fix: an operational interpreter over a value domain that
-- DEFUNCTIONALIZES arrows — a closure is `(IR body, captured env)` data
-- (like `SS.eval`'s `Vclos`), so `apply` can RUN the body and fire its
-- effects as they execute. Everything else is boxed as the denotational
-- `⟦_⟧` (no defunctionalization needed). This module defines the value
-- domain `OVal` and its forgetful coercion `ov→sem : OVal A → ⟦ A ⟧`; the
-- interpreter `otrace` follows.
--
-- This is the ground-truth observable the machine refines; the compositional
-- denotational layer (Plan 0.46) is proven ADEQUATE to it later.
------------------------------------------------------------------------

module Once.Verified.OpTrace where

open import Data.Unit using (⊤; tt)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)

open import Once.Type
  using (Type; Unit; Void; _*_; _+_; _⇒[_]_; μ-type; ν-type; Int; Float; Str; Buffer)
open import Once.CCC.IR using (IR)
open import Once.CCC.Eval using (eval; ⟦_⟧)

------------------------------------------------------------------------
-- The operational value domain.
--
-- DEFUNCTIONALIZE the arrow (`ovClos` carries the closure's IR body + the
-- captured environment, with the capture context `Γ` existential), be
-- STRUCTURAL on product/sum (so nested arrows are still defunctionalized),
-- and BOX every first-order / base type as its denotational value `⟦_⟧`.
--
-- `Void` has no constructor — `OVal Void` is the empty type (no values),
-- which is exactly right. (Boxed `μ`/`ν` assume first-order functors — no
-- arrows inside the data; faithful for Layer-0. A higher-order functor
-- would need a structural `μ`/`ν` value; deferred.)
------------------------------------------------------------------------

data OVal : Type → Set where
  ovUnit : OVal Unit
  ovPair : ∀ {A B} → OVal A → OVal B → OVal (A * B)
  ovInl  : ∀ {A B} → OVal A → OVal (A + B)
  ovInr  : ∀ {A B} → OVal B → OVal (A + B)
  -- defunctionalized closure: body `IR (Γ * A) B` + captured env `OVal Γ`.
  ovClos : ∀ {Γ A B k} → IR (Γ * A) B → OVal Γ → OVal (A ⇒[ k ] B)
  -- boxed base / first-order values.
  ovInt  : ⟦ Int ⟧    → OVal Int
  ovFlt  : ⟦ Float ⟧  → OVal Float
  ovStr  : ⟦ Str ⟧    → OVal Str
  ovBuf  : ⟦ Buffer ⟧ → OVal Buffer
  ovMu   : ∀ {F} → ⟦ μ-type F ⟧ → OVal (μ-type F)
  ovNu   : ∀ {F} → ⟦ ν-type F ⟧ → OVal (ν-type F)

------------------------------------------------------------------------
-- Forgetful coercion to the denotational value. A closure forgets to the
-- Agda function that RUNS its body via `eval` (the denotational value side;
-- the trace it would emit is exactly what `otrace` keeps and `ov→sem`
-- discards). The boxed cases are the identity; the structural cases recurse.
------------------------------------------------------------------------

ov→sem : ∀ {A} → OVal A → ⟦ A ⟧
ov→sem ovUnit        = tt
ov→sem (ovPair a b)  = (ov→sem a , ov→sem b)
ov→sem (ovInl a)     = inj₁ (ov→sem a)
ov→sem (ovInr b)     = inj₂ (ov→sem b)
ov→sem (ovClos h γ)  = λ a → eval h (ov→sem γ , a)
ov→sem (ovInt v)     = v
ov→sem (ovFlt v)     = v
ov→sem (ovStr v)     = v
ov→sem (ovBuf v)     = v
ov→sem (ovMu v)      = v
ov→sem (ovNu v)      = v
