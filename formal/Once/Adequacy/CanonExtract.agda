-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.CanonExtract — `extractFunctions` commutes with `canonDecl`.
--
-- `canonDecl` canonExpr's USER (`DFunDef`) bodies and leaves PRIMITIVE
-- (`DSignature`) bodies / signatures / aliases untouched, so `extractFunctions`
-- over the canonicalized decls yields the SAME funs/polys with user bodies
-- canonExpr'd (`canonFI`, skipping `isPrim`) and poly bodies canonExpr'd
-- (`canonPFI`). Proven by induction on `extractFunctions-go`.
------------------------------------------------------------------------

module Once.Adequacy.CanonExtract where

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.List using (List; []; _∷_; map)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_×_; _,_)
open import Data.String using (String; _++_) renaming (_≟_ to _≟s_)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Once.Type using (isGround; extractGround)
open import Once.Functor.Decide using (isConcrete?)
open import Once.TypeCheck.Raw using (RawExpr)
open import Once.Parser.Module.Core using (Decl; DTypeSig; DFunDef; DSignature; DImport; DTypeAlias)
open import Once.Parser
  using (FunInfo; mkFunInfo; PolyFunInfo; mkPolyFunInfo; projectSig; extractFunctions-go)
open Once.Parser.FunInfo using (funBody; funIsPrimitive)
open Once.Parser.PolyFunInfo using (pfunBody)
open import Once.Parser.Module.Resolve using (canonExpr; canonDecl)
-- D072 M3: the sig-less routing criterion and its canon-invariance.
open import Once.TypeCheck.Principal using (siglessSchema)
open import Once.Adequacy.CanonPrincipal using (siglessSchema-canon)

------------------------------------------------------------------------
-- Per-FunInfo / per-PolyFunInfo canonicalization (USER bodies only).
------------------------------------------------------------------------

canonBody : List String → FunInfo → FunInfo
canonBody b fi = record fi { funBody = canonExpr b [] [] (funBody fi) }

-- `if` only on the BODY (record-update keeps funName/funType DEFINITIONALLY), so
-- the AllFunsTyped transport's extendFunCtx (funName …) matches without casing.
canonFI : List String → FunInfo → FunInfo
canonFI b fi = record fi { funBody = if (funIsPrimitive fi) then funBody fi else canonExpr b [] [] (funBody fi) }

canonFuns : List String → List FunInfo → List FunInfo
canonFuns b = map (canonFI b)

canonPFI : List String → PolyFunInfo → PolyFunInfo
canonPFI b pfi = record pfi { pfunBody = canonExpr b [] [] (pfunBody pfi) }

canonPolys : List String → List PolyFunInfo → List PolyFunInfo
canonPolys b = map (canonPFI b)

------------------------------------------------------------------------
-- The commute.
------------------------------------------------------------------------

extract-commute : ∀ (b : List String) (al : _) (ds : List Decl) (pending : _) {funs polys}
  → extractFunctions-go al ds pending ≡ inj₂ (funs , polys)
  → extractFunctions-go al (map (canonDecl b [] []) ds) pending
      ≡ inj₂ (canonFuns b funs , canonPolys b polys)
extract-commute b al [] pending refl = refl
-- DTypeSig: unchanged by canonDecl; same isGround / isConcrete? classification
-- (Plan 0.58 / D071: ground-non-concrete sigs route to poly like non-ground).
extract-commute b al (DTypeSig name ty ∷ rest) pending eq with isGround ty
... | inj₂ _ = extract-commute b al rest _ eq
... | inj₁ g with isConcrete? (extractGround ty g)
...   | just _  = extract-commute b al rest _ eq
...   | nothing = extract-commute b al rest _ eq
-- DFunDef, GROUND pending (consFun) — body canonExpr'd.
extract-commute b al (DFunDef name alloc body ∷ rest) (just (sigName , inj₁ gty)) eq with sigName ≟s name
... | yes _ with extractFunctions-go al rest nothing in eq2
...   | inj₂ (gs , ps) with eq
...     | refl rewrite extract-commute b al rest nothing eq2 = refl
extract-commute b al (DFunDef name alloc body ∷ rest) (just (sigName , inj₁ gty)) eq | no _ =
      extract-commute b al rest nothing eq
-- DFunDef, NON-GROUND pending (consPoly) — body canonExpr'd.
extract-commute b al (DFunDef name alloc body ∷ rest) (just (sigName , inj₂ pty)) eq with sigName ≟s name
... | yes _ with extractFunctions-go al rest nothing in eq2
...   | inj₂ (gs , ps) with eq
...     | refl rewrite extract-commute b al rest nothing eq2 = refl
extract-commute b al (DFunDef name alloc body ∷ rest) (just (sigName , inj₂ pty)) eq | no _ =
      extract-commute b al rest nothing eq
-- DFunDef, NO pending (D007 consFun).
-- DFunDef, NO pending: D072 routes by `siglessSchema`; the criterion is
-- canon-invariant (CanonPrincipal.siglessSchema-canon), so both sides
-- classify identically.
extract-commute b al (DFunDef name alloc body ∷ rest) nothing eq
  with siglessSchema body in eqS
extract-commute b al (DFunDef name alloc body ∷ rest) nothing eq | just pty
  with extractFunctions-go al rest nothing in eq2
... | inj₂ (gs , ps) with eq
...   | refl rewrite siglessSchema-canon b body | eqS
                   | extract-commute b al rest nothing eq2 = refl
extract-commute b al (DFunDef name alloc body ∷ rest) nothing eq | nothing
  with extractFunctions-go al rest nothing in eq2
... | inj₂ (gs , ps) with eq
...   | refl rewrite siglessSchema-canon b body | eqS
                   | extract-commute b al rest nothing eq2 = refl
-- DSignature: primitive (consFun, body RVar name — unchanged by canonFI since isPrim).
extract-commute b al (DSignature name nothing ty se ∷ rest) pending eq with projectSig al name ty
... | inj₂ gty with extractFunctions-go al rest nothing in eq2
...   | inj₂ (gs , ps) with eq
...     | refl rewrite extract-commute b al rest nothing eq2 = refl
extract-commute b al (DSignature name (just owner) ty se ∷ rest) pending eq with projectSig al (owner ++ "." ++ name) ty
... | inj₂ gty with extractFunctions-go al rest nothing in eq2
...   | inj₂ (gs , ps) with eq
...     | refl rewrite extract-commute b al rest nothing eq2 = refl
-- DImport / DTypeAlias: pass through.
extract-commute b al (DImport imp ∷ rest) pending eq = extract-commute b al rest pending eq
extract-commute b al (DTypeAlias n ps t ∷ rest) pending eq = extract-commute b al rest pending eq
