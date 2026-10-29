-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.InitWindowImage   (Plan 0.123 A.4 step 4, part 1)
--
-- …and of the whole IMAGE: `main`'s unit and every function's, each by
-- `InitWindowTrace` at its own definition's identity, assembled as
-- `ProgramImageFacts.image-alloc-min` assembles theirs. Under the one named
-- exclusion (`AnaNoProd`, every term in the program).
------------------------------------------------------------------------

open import Once.Spec.Name using (CanonicalName)

module Once.CCC.Codegen.InitWindowImage (o : CanonicalName) where

open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Nat using (ℕ; suc)
open import Data.Unit using (tt)
open import Data.Product using (_×_; _,_)

open import Once.IR using (IR)
open import Once.IRTy using (Unit)
open import Once.CCC.Codegen.ProgramImage using (program-image; fns-image; fn-next)
open import Once.Denotation.Program using (IRFun; irProgram)
open Once.Denotation.Program.IRFun using (fbody; fname)
import Once.CCC.Codegen.IRToTrace as IT
import Once.CCC.Codegen.InitWindowTrace as IWT
open import Once.CCC.Codegen.InitWindow using (InitDisc; _∷_; []; init-++; AnaNoProd)

fns-init : ∀ (l : ℕ) (tbl : List IRFun) → All (λ e → AnaNoProd (fbody e)) tbl
         → InitDisc (fns-image l tbl)
fns-init l []       []       = []
fns-init l (e ∷ es) (p ∷ ps) =
  init-++ (tt ∷ IWT.ir-to-trace-lab-init (fname e) (fbody e) l p) (fns-init (fn-next l e) es ps)

image-init : ∀ (tbl : List IRFun) (ir : IR Unit Unit)
           → AnaNoProd ir → All (λ e → AnaNoProd (fbody e)) tbl
           → InitDisc (program-image o (irProgram tbl ir))
image-init tbl ir pm pf =
  tt ∷ init-++ (IWT.ir-to-trace-top-init o ir pm)
               (fns-init (suc (IT.ir-next-label o 0 ir)) tbl pf)
