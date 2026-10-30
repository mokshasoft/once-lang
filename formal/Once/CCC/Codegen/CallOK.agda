-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.CallOK — the per-instruction fact behind `CallsLinked`:
-- a direct call (`c-call-fn f`) satisfies `C` at some objects, and a SigOp
-- call (`instr-sigop si`) satisfies `Q`. Instantiated twice: a direct call
-- names an entry of the table (D245), and a compiler-owned SigOp names a block
-- of the file (plan 0.129 B5).
------------------------------------------------------------------------

module Once.CCC.Codegen.CallOK where

open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ)
open import Data.Unit using (⊤; tt)
open import Once.Spec.Name using (CanonicalName)
open import Once.IRTy using (IRTy)
open import Once.SigOp.Info using (SigOpInfo)
open import Once.Arith.CmpOp using (CmpOp)
open import Once.Arith.SigOp.Compare using (cmp-block-info)
open import Once.CCC.Machine.SMCore using (AbstractInstr; instr-ctrl; c-call-fn; instr-sigop)

-- CATCHALL: only a direct call and a SigOp call are constrained.
InstrOK : (CanonicalName → IRTy → IRTy → Set) → (∀ {A B} → SigOpInfo A B → Set) → AbstractInstr → Set
InstrOK C Q (instr-ctrl (c-call-fn f)) = Σ IRTy (λ A → Σ IRTy (λ B → C f A B))
InstrOK C Q (instr-sigop si)           = Q si
{-# CATCHALL #-}
InstrOK C Q _                          = ⊤

-- What a SigOp leaf's lowering calls: itself, or (a comparison, D264) its block.
Calls : (∀ {A B} → SigOpInfo A B → Set) → ∀ {A B} → SigOpInfo A B → Maybe CmpOp → Set
Calls Q si nothing  = Q si
Calls Q si (just o) = Q (cmp-block-info o)

-- With no SigOp obligation, every lowering meets it.
calls-⊤ : ∀ {A B} (si : SigOpInfo A B) (m : Maybe CmpOp) → Calls (λ _ → ⊤) si m
calls-⊤ si nothing  = tt
calls-⊤ si (just _) = tt
