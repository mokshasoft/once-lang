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
open import Data.Product using (_×_; _,_; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.String using (String; _≟_; _++_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Relation.Nullary using (yes; no)

import Once.Compile as C
open import Once.TypeCheck.Elaborate using (PolyCtx)
open import Once.Parser.Module.Core
  using (Module; mkModule; Decl; DFunDef; DTypeSig; DSignature; DTypeAlias; DImport)
open C using (CompiledFun; FunInfo; PolyFunInfo; FunCtx; AllocMode; PendingSig; TypeAliasEnv;
              compileAllFuns-go; resolveFunType; compileFun; extendFunCtx;
              maybeWrapMain; mkCompiledFun;
              extractFunctions-go; extractFunctions-consFun; extractFunctions-consPoly;
              extractFunctions; mkFunInfo; mkPolyFunInfo; isGround; projectSig;
              compileResolvedModule; extractAliases; buildPolyCtx; emptyFunCtx)
open Module using (decls)
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

------------------------------------------------------------------------
-- extractFunctions: a non-primitive "main" FunInfo comes from a DFunDef "main".
------------------------------------------------------------------------

-- "this decl is a `DFunDef` named main" (the witness `lookup-main-of-dfundef`
-- consumes on the source side).
DFunDefMain : Decl → Set
DFunDefMain d = ∃[ al ] ∃[ bd ] d ≡ DFunDef "main" al bd

-- A non-primitive "main" `FunInfo` produced by `extractFunctions-go` traces back
-- to a `DFunDef "main"` in the decls. The primitive (`DSignature`) branches make
-- `funIsPrimitive ≡ true`, so a `MainFi` (which demands `≡ false`) cannot land
-- there — the `here` case for a primitive is absurd (`true ≡ false`). This is
-- exactly what the `findMain`-skips-primitives fix buys.
extractFunctions-go-main :
  ∀ (aliases : TypeAliasEnv) (ds : List Decl) (pending : Maybe PendingSig)
    (finfos : List FunInfo) (polys : List PolyFunInfo)
  → extractFunctions-go aliases ds pending ≡ inj₂ (finfos , polys)
  → Any MainFi finfos
  → Any DFunDefMain ds
extractFunctions-go-main aliases [] pending _ _ refl ()
-- DTypeSig: sets pending, no FunInfo here ⇒ the main is in `rest`.
extractFunctions-go-main aliases (DTypeSig name ty ∷ rest) pending finfos polys eq anyFi
  with isGround ty
... | inj₁ _ = there (extractFunctions-go-main aliases rest _ finfos polys eq anyFi)
... | inj₂ _ = there (extractFunctions-go-main aliases rest _ finfos polys eq anyFi)
-- DFunDef with matching ground sig → non-primitive FunInfo (the entry case).
extractFunctions-go-main aliases (DFunDef name alloc body ∷ rest) (just (sigName , inj₁ gty)) finfos polys eq anyFi
  with sigName ≟ name
... | no  _ = there (extractFunctions-go-main aliases rest nothing finfos polys eq anyFi)
... | yes _ with extractFunctions-go aliases rest nothing in r
...   | inj₁ _ = ⊥-elim (inj₁≢inj₂ eq)
...   | inj₂ (gs , ps) with inj₂-inj eq | anyFi
...     | refl | here (pn , _) = here (alloc , body , cong (λ z → DFunDef z alloc body) pn)
...     | refl | there a'      = there (extractFunctions-go-main aliases rest nothing gs ps r a')
-- DFunDef with matching poly sig → PolyFunInfo (not in `finfos`) ⇒ main in `rest`.
extractFunctions-go-main aliases (DFunDef name alloc body ∷ rest) (just (sigName , inj₂ pty)) finfos polys eq anyFi
  with sigName ≟ name
... | no  _ = there (extractFunctions-go-main aliases rest nothing finfos polys eq anyFi)
... | yes _ with extractFunctions-go aliases rest nothing in r
...   | inj₁ _ = ⊥-elim (inj₁≢inj₂ eq)
...   | inj₂ (gs , ps) with inj₂-inj eq
...     | refl = there (extractFunctions-go-main aliases rest nothing gs ps r anyFi)
-- DFunDef, no sig → non-primitive FunInfo (the entry case).
extractFunctions-go-main aliases (DFunDef name alloc body ∷ rest) nothing finfos polys eq anyFi
  with extractFunctions-go aliases rest nothing in r
... | inj₁ _ = ⊥-elim (inj₁≢inj₂ eq)
... | inj₂ (gs , ps) with inj₂-inj eq | anyFi
...   | refl | here (pn , _) = here (alloc , body , cong (λ z → DFunDef z alloc body) pn)
...   | refl | there a'      = there (extractFunctions-go-main aliases rest nothing gs ps r a')
-- DSignature (primitive): funIsPrimitive ≡ true ⇒ the `here` MainFi is absurd.
extractFunctions-go-main aliases (DSignature name nothing ty ∷ rest) pending finfos polys eq anyFi
  with projectSig aliases name ty
... | inj₁ _ = ⊥-elim (inj₁≢inj₂ eq)
... | inj₂ gty with extractFunctions-go aliases rest nothing in r
...   | inj₁ _ = ⊥-elim (inj₁≢inj₂ eq)
...   | inj₂ (gs , ps) with inj₂-inj eq | anyFi
...     | refl | here (_ , ())
...     | refl | there a' = there (extractFunctions-go-main aliases rest nothing gs ps r a')
extractFunctions-go-main aliases (DSignature name (just owner) ty ∷ rest) pending finfos polys eq anyFi
  with projectSig aliases (owner ++ "." ++ name) ty
... | inj₁ _ = ⊥-elim (inj₁≢inj₂ eq)
... | inj₂ gty with extractFunctions-go aliases rest nothing in r
...   | inj₁ _ = ⊥-elim (inj₁≢inj₂ eq)
...   | inj₂ (gs , ps) with inj₂-inj eq | anyFi
...     | refl | here (_ , ())
...     | refl | there a' = there (extractFunctions-go-main aliases rest nothing gs ps r a')
-- DTypeAlias / DImport: not a DFunDef ⇒ main in `rest` (pending unchanged).
extractFunctions-go-main aliases (DTypeAlias _ _ _ ∷ rest) pending finfos polys eq anyFi =
  there (extractFunctions-go-main aliases rest pending finfos polys eq anyFi)
extractFunctions-go-main aliases (DImport _ ∷ rest) pending finfos polys eq anyFi =
  there (extractFunctions-go-main aliases rest pending finfos polys eq anyFi)

------------------------------------------------------------------------
-- Bridge through compileResolvedModule (case extractFunctions → compileAllFuns).
------------------------------------------------------------------------

compileResolvedModule-main :
  ∀ (m : Module) (mode : AllocMode) (doOpt : Bool) (funs : List CompiledFun)
  → compileResolvedModule mode doOpt m ≡ inj₂ funs
  → Any MainCf funs
  → Any DFunDefMain (decls m)
compileResolvedModule-main m mode doOpt funs crm anyCf
  with extractFunctions (extractAliases m) m in efEq
... | inj₁ _ = ⊥-elim (inj₁≢inj₂ crm)
... | inj₂ (finfos , polys) =
      extractFunctions-go-main (extractAliases m) (decls m) nothing finfos polys efEq
        (compileAllFuns-go-main mode doOpt (buildPolyCtx polys) finfos emptyFunCtx funs crm anyCf)
