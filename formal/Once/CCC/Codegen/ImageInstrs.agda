-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.ImageInstrs   (plan 0.129 B5)
--
-- `CallsLinked` over the WHOLE program image: when `main` and every table
-- entry satisfy the leaf facts (`Leaves C i …`), every instruction of the image
-- satisfies `InstrOK (C i) Q`. The start and each entry's marker are neither
-- a call nor a SigOp.
------------------------------------------------------------------------

open import Once.Spec.Name using (CanonicalName)
open import Once.IRTy using (IRTy)
open import Once.SigOp.Info using (SigOpInfo)

module Once.CCC.Codegen.ImageInstrs {I : Set}
  (C : I → CanonicalName → IRTy → IRTy → Set) (i : I) (Q : ∀ {A B} → SigOpInfo A B → Set) where

open import Data.Nat using (ℕ; suc)
open import Data.Unit using (tt)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.All.Properties using (++⁺)

open import Once.Denotation.Program using (IRFun; IRProgram; module IRProgram; module IRFun; Leaves)
open IRProgram using (main; table)
open IRFun using (fname; fbody)
open import Once.CCC.Codegen.ProgramImage using (program-image; fns-image; fn-next)
open import Once.CCC.Codegen.CallOK using (InstrOK; Calls)
open import Once.IR using (IR)
open import Once.SigOp.Info using (module SigOpInfo)
open SigOpInfo using (sem)
open import Once.Arith.SigOp.Compare using (cmp-of)
import Once.CCC.Codegen.CallsLinked as CLk

-- the leaf facts: each call satisfies `C i`, each SigOp's lowering `Q`
LK : ∀ {A B} → IR A B → Set
LK = Leaves C i (λ si → Calls Q si (cmp-of (sem si)))

fns-ok : ∀ (l : ℕ) (es : List IRFun) → All (λ e → LK (fbody e)) es → All (InstrOK (C i) Q) (fns-image l es)
fns-ok l []       []         = []
fns-ok l (e ∷ es) (le ∷ les) =
  ++⁺ (tt ∷ CLk.ir-to-trace-lab-calls (fname e) C i Q (fbody e) l le) (fns-ok (fn-next l e) es les)

image-ok : ∀ (o : CanonicalName) (p : IRProgram) → LK (main p) → All (λ e → LK (fbody e)) (table p)
         → All (InstrOK (C i) Q) (program-image o p)
image-ok o p lm les = tt ∷ ++⁺ (CLk.ir-to-trace-top-calls o C i Q (main p) lm) (fns-ok _ (table p) les)
