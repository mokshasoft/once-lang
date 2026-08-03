-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.CCC.Target.X86-64.CodeGen.Primitives
--
-- Plan 0.30 cleanup: the per-SigOp and per-primitive-constant code
-- emitters used by the LIVE backend (`AbstractToX86` delegates to these
-- for `instr-sigop` / `instr-load-const`). Extracted out of the legacy
-- `CodeGen.Compile` (the dead `compile-ir` path) so the live path no
-- longer imports that module — a prerequisite for retiring `compile-ir`
-- once the correctness proofs are re-based onto `ir-to-trace`.
------------------------------------------------------------------------

module Once.CCC.Target.X86-64.CodeGen.Primitives where

open import Data.Nat using (ℕ)
open import Data.List using (List; []; _∷_; length)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Once.CCC.Target.X86-64.Syntax
  using (rax; reg; imm; mov; ud2; call-sym; Program)
open import Once.Target.Symbol using (once-symbol-path)
open import Once.CanonicalName using (CanonicalName)
open import Once.Type using (FitsInReg; fits-int; fits-float)
open import Once.Semantics.FloatBits using (float-bits)
import Once.Semantics.Value as SC
open import Once.Word using (Carrier)

------------------------------------------------------------------------
-- Plan 0.11: SigOp call by symbolic name.
------------------------------------------------------------------------
compile-sigOp : CanonicalName → Program
compile-sigOp name = call-sym (once-symbol-path name) ∷ []

compile-sigOp-size : CanonicalName → ℕ
compile-sigOp-size _ = 1

compile-sigOp-length : ∀ (name : CanonicalName) → length (compile-sigOp name) ≡ compile-sigOp-size name
compile-sigOp-length _ = refl

------------------------------------------------------------------------
-- Plan 0.11: const literal codegen. `FitsInReg` evidence dispatches;
-- each register-fittable primitive emits its immediate-load.
------------------------------------------------------------------------
compile-const : ∀ {A} → FitsInReg A → SC.⟦_⟧ Carrier A → Program
compile-const fits-int   n = mov (reg rax) (imm n) ∷ []
-- D079 (2026-08-03): a float CONSTANT is a 64-bit pattern, so it loads as
-- an ordinary immediate (gas promotes `movq $big` to `movabs`) — no FPU
-- needed. Was `ud2`, which made the machines diverge on this route.
compile-const fits-float v = mov (reg rax) (imm (float-bits v)) ∷ []

compile-const-size : ∀ {A} → FitsInReg A → ℕ
compile-const-size fits-int   = 1
compile-const-size fits-float = 1

compile-const-length : ∀ {A} (p : FitsInReg A) (v : SC.⟦_⟧ Carrier A) →
                        length (compile-const p v) ≡ compile-const-size p
compile-const-length fits-int   _ = refl
compile-const-length fits-float _ = refl
