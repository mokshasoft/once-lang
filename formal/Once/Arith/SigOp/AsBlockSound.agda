-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Arith.SigOp.AsBlockSound — AN OP AS ITS BLOCK MEANS WHAT IT MEANT
-- (D459): case for case `refl`, the block's evaluator being the primitive's
-- operation; and an op that was declared still is.
------------------------------------------------------------------------

module Once.Arith.SigOp.AsBlockSound where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Once.Spec.Numerics using (TargetNum)
open import Once.SigOp.Info using (SigOpInfo; SigOpSem; mk-info'; blockV; ffiV; callsV; emitsV; haltsV; primV; module SigOpInfo)
open import Once.Arith.Prim using (ArithPrim; p-add; p-sub; p-mul; p-div; p-mod; p-neg; p-fadd; p-fsub; p-fmul; p-fdiv; p-i2f; p-fneg; p-cmp; p-fcmp)
open import Once.Arith.SigOp.AsBlock using (as-block)
open import Once.Denotation.DenotTrace using (evalᴰ; CallEnv)
open import Once.Contract using (ISig)
open import Once.Denotation.Program using (Declared)
open import Once.IR using (SigOp)

------------------------------------------------------------------------
-- It means what it meant.
------------------------------------------------------------------------

private
  ev-prim : ∀ (fmt : TargetNum) (ρ : CallEnv) {A B} nm (p : ArithPrim A B) bA cB a
          → evalᴰ fmt ρ (SigOp (as-block (mk-info' nm (primV p) bA cB))) a ≡ evalᴰ fmt ρ (SigOp (mk-info' nm (primV p) bA cB)) a
  ev-prim fmt ρ nm p-add  bA cB a = refl
  ev-prim fmt ρ nm p-sub  bA cB a = refl
  ev-prim fmt ρ nm p-mul  bA cB a = refl
  ev-prim fmt ρ nm p-div  bA cB a = refl
  ev-prim fmt ρ nm p-mod  bA cB a = refl
  ev-prim fmt ρ nm p-neg  bA cB a = refl
  ev-prim fmt ρ nm p-fadd bA cB a = refl
  ev-prim fmt ρ nm p-fsub bA cB a = refl
  ev-prim fmt ρ nm p-fmul bA cB a = refl
  ev-prim fmt ρ nm p-fdiv bA cB a = refl
  ev-prim fmt ρ nm p-i2f  bA cB a = refl
  ev-prim fmt ρ nm p-fneg bA cB a = refl
  ev-prim fmt ρ nm (p-cmp o)    bA cB a = refl
  ev-prim fmt ρ nm (p-fcmp h o) bA cB a = refl

  ev-at : ∀ (fmt : TargetNum) (ρ : CallEnv) {A B} nm (s : SigOpSem A B) bA cB a
        → evalᴰ fmt ρ (SigOp (as-block (mk-info' nm s bA cB))) a ≡ evalᴰ fmt ρ (SigOp (mk-info' nm s bA cB)) a
  ev-at fmt ρ nm (primV p)        bA cB a = ev-prim fmt ρ nm p bA cB a
  ev-at fmt ρ nm (blockV e eA eB) bA cB a = refl
  ev-at fmt ρ nm ffiV             bA cB a = refl
  ev-at fmt ρ nm callsV           bA cB a = refl
  ev-at fmt ρ nm (emitsV e)       bA cB a = refl
  ev-at fmt ρ nm (haltsV e)       bA cB a = refl

-- ★ the op, as its block, runs as it did
as-block-ev : ∀ (fmt : TargetNum) (ρ : CallEnv) {A B} (si : SigOpInfo A B) a
            → evalᴰ fmt ρ (SigOp (as-block si)) a ≡ evalᴰ fmt ρ (SigOp si) a
as-block-ev fmt ρ si a = ev-at fmt ρ (SigOpInfo.name si) (SigOpInfo.sem si) (SigOpInfo.baseA si) (SigOpInfo.conB si) a

------------------------------------------------------------------------
-- A declared op stays declared (a block, as a primitive, needs nothing).
------------------------------------------------------------------------

private
  decl-prim : ∀ (Σ : ISig) {A B} nm (p : ArithPrim A B) bA cB
            → Declared Σ (mk-info' nm (primV p) bA cB) → Declared Σ (as-block (mk-info' nm (primV p) bA cB))
  decl-prim Σ nm p-add  bA cB d = d
  decl-prim Σ nm p-sub  bA cB d = d
  decl-prim Σ nm p-mul  bA cB d = d
  decl-prim Σ nm p-div  bA cB d = d
  decl-prim Σ nm p-mod  bA cB d = d
  decl-prim Σ nm p-neg  bA cB d = d
  decl-prim Σ nm p-fadd bA cB d = d
  decl-prim Σ nm p-fsub bA cB d = d
  decl-prim Σ nm p-fmul bA cB d = d
  decl-prim Σ nm p-fdiv bA cB d = d
  decl-prim Σ nm p-i2f  bA cB d = d
  decl-prim Σ nm p-fneg bA cB d = d
  decl-prim Σ nm (p-cmp o)    bA cB d = d
  decl-prim Σ nm (p-fcmp h o) bA cB d = d

  decl-at : ∀ (Σ : ISig) {A B} nm (s : SigOpSem A B) bA cB
          → Declared Σ (mk-info' nm s bA cB) → Declared Σ (as-block (mk-info' nm s bA cB))
  decl-at Σ nm (primV p)        bA cB d = decl-prim Σ nm p bA cB d
  decl-at Σ nm (blockV e eA eB) bA cB d = d
  decl-at Σ nm ffiV             bA cB d = d
  decl-at Σ nm callsV           bA cB d = d
  decl-at Σ nm (emitsV e)       bA cB d = d
  decl-at Σ nm (haltsV e)       bA cB d = d

as-block-declared : ∀ (Σ : ISig) {A B} (si : SigOpInfo A B) → Declared Σ si → Declared Σ (as-block si)
as-block-declared Σ si = decl-at Σ (SigOpInfo.name si) (SigOpInfo.sem si) (SigOpInfo.baseA si) (SigOpInfo.conB si)
