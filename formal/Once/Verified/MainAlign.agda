-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Verified.MainAlign — the COMPILER-SIDE correspondence for
-- `main-exists-align` (Plan 0.45 #9): a compiled entry `main` traces back
-- to a `DFunDef "main"` in the source decls.
--
-- Two folds to bridge:
--   * `compileAllFuns-go`  : FunInfo list → CompiledFun list (name +
--     `isPrimitive` preserved positionally; this module).
--   * `extractFunctions`   : decls → FunInfo list (a non-primitive "main"
--     FunInfo comes from a `DFunDef "main"`).
------------------------------------------------------------------------

module Once.Verified.MainAlign where

open import Data.Bool using (Bool; true; false)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.List using (List; []; _∷_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

import Once.Compile as C
open import Once.TypeCheck.Elaborate using (PolyCtx)
open C using (CompiledFun; FunInfo; FunCtx; AllocMode;
              compileAllFuns-go; resolveFunType; compileFun; extendFunCtx;
              maybeWrapMain; mkCompiledFun)
open C.CompiledFun using (cfName; cfIsPrimitive)
open C.FunInfo using (funName; funIsPrimitive; funType; funBody)

private
  inj₁≢inj₂ : ∀ {ℓ} {A B : Set ℓ} {x : A} {y : B} → inj₁ x ≡ inj₂ y → ⊥
  inj₁≢inj₂ ()

  inj₂-inj : ∀ {ℓ} {A B : Set ℓ} {x y : B} → (inj₂ {A = A} x) ≡ inj₂ y → x ≡ y
  inj₂-inj refl = refl

MainCf : CompiledFun → Set
MainCf cf = cfName cf ≡ "main" × cfIsPrimitive cf ≡ false

MainFi : FunInfo → Set
MainFi fi = funName fi ≡ "main" × funIsPrimitive fi ≡ false

-- A non-primitive "main" in the COMPILED list traces back to a non-primitive
-- "main" `FunInfo` — `compileAllFuns-go` preserves name + `isPrimitive`
-- positionally (the head `CompiledFun` IS `mkCompiledFun (funName fi) … (funIsPrimitive fi)`).
compileAllFuns-go-main :
  ∀ (m : AllocMode) (doOpt : Bool) (polys : PolyCtx)
    (finfos : List FunInfo) (ctx : FunCtx) (funs : List CompiledFun)
  → compileAllFuns-go m doOpt polys finfos ctx ≡ inj₂ funs
  → Any MainCf funs
  → Any MainFi finfos
compileAllFuns-go-main m doOpt polys [] ctx _ refl ()
compileAllFuns-go-main m doOpt polys (fi ∷ rest) ctx funs eq anyCf
  with resolveFunType ctx polys (funType fi) (funBody fi)
... | inj₁ _  = ⊥-elim (inj₁≢inj₂ eq)
... | inj₂ ty with compileFun m doOpt ctx polys (funName fi) ty (funBody fi)
...   | inj₁ _  = ⊥-elim (inj₁≢inj₂ eq)
...   | inj₂ ir with compileAllFuns-go m doOpt polys rest (extendFunCtx ctx (funName fi) ty) in r3
...     | inj₁ _ = ⊥-elim (inj₁≢inj₂ eq)
...     | inj₂ compiled with inj₂-inj eq | anyCf
...       | refl | here mcf = here mcf
...       | refl | there a' =
              there (compileAllFuns-go-main m doOpt polys rest
                       (extendFunCtx ctx (funName fi) ty) compiled r3 a')
