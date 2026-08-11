-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.CanonReflectExtract — Plan 0.51 extraction-error preservation.
--
-- `extractFunctions-canon-inj₁`: canonicalization PRESERVES an extraction error.
-- `canonDecl` only rewrites function BODIES (canonExpr); the `inj₁` outcomes of
-- `extractFunctions-go` come from `DSignature`/`projectSig` (body-independent) and
-- `guardDistinct` (which reads `emittedNames`, preserved by `canonFuns`). So the
-- error rides — proven by mirroring `CanonExtract.extract-commute` for the `inj₁`
-- case + reusing `emittedNames-canon`. This is the inj₁ analogue of the forward
-- `CanonModuleTyped.extractFunctions-canon`.
------------------------------------------------------------------------

module Once.Adequacy.CanonReflectExtract where

open import Data.Bool using (Bool; true; false; _∧_)
open import Data.List using (List; []; _∷_; map)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_×_; _,_)
open import Data.String using (String; _++_) renaming (_≟_ to _≟s_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Once.Type using (isGround; extractGround)
open import Once.Functor.Decide using (isConcrete?)
open import Once.TypeCheck.Raw using (RawExpr)
open import Once.Parser.Module.Core using (Decl; DTypeSig; DFunDef; DSignature; DImport; DTypeAlias; mkModule)
open import Once.Parser
  using (FunInfo; mkFunInfo; PolyFunInfo; mkPolyFunInfo; projectSig; extractFunctions-go;
         guardDistinct; distinctOrErr; namesDistinct; allValidIdentB; emittedNames)
open import Once.Parser.Module.Resolve using (canonDecl; polyDefNames)
open import Once.TypeCheck.Principal using (siglessSchema)
open import Once.Adequacy.CanonPrincipal using (siglessSchema-canon)
import Once.Compile as C
open import Once.Adequacy.CanonExtract using (canonFuns; canonPolys; extract-commute)
open import Once.Adequacy.CanonModuleTyped using (canonModule; emittedNames-canon; extractAliases-canon)

------------------------------------------------------------------------
-- The inj₁ mirror of extract-commute (the error rides body-canonicalization).
------------------------------------------------------------------------

extract-commute-inj₁ : ∀ (b : List String) (al : _) (ds : List Decl) (pending : _) {err}
  → extractFunctions-go al ds pending ≡ inj₁ err
  → extractFunctions-go al (map (canonDecl b [] []) ds) pending ≡ inj₁ err
extract-commute-inj₁ b al [] pending ()
extract-commute-inj₁ b al (DTypeSig name ty ∷ rest) pending eq with isGround ty
... | inj₂ _ = extract-commute-inj₁ b al rest _ eq
... | inj₁ g with isConcrete? (extractGround ty g)
...   | just _  = extract-commute-inj₁ b al rest _ eq
...   | nothing = extract-commute-inj₁ b al rest _ eq
extract-commute-inj₁ b al (DFunDef name alloc body ∷ rest) (just (sigName , inj₁ gty)) eq with sigName ≟s name
... | yes _ with extractFunctions-go al rest nothing in eq2
...   | inj₁ e with eq
...     | refl rewrite extract-commute-inj₁ b al rest nothing eq2 = refl
extract-commute-inj₁ b al (DFunDef name alloc body ∷ rest) (just (sigName , inj₁ gty)) eq | no _ =
      extract-commute-inj₁ b al rest nothing eq
extract-commute-inj₁ b al (DFunDef name alloc body ∷ rest) (just (sigName , inj₂ pty)) eq with sigName ≟s name
... | yes _ with extractFunctions-go al rest nothing in eq2
...   | inj₁ e with eq
...     | refl rewrite extract-commute-inj₁ b al rest nothing eq2 = refl
extract-commute-inj₁ b al (DFunDef name alloc body ∷ rest) (just (sigName , inj₂ pty)) eq | no _ =
      extract-commute-inj₁ b al rest nothing eq
-- DFunDef, NO pending: D072 sig-less routing (canon-invariant criterion).
extract-commute-inj₁ b al (DFunDef name alloc body ∷ rest) nothing eq
  with siglessSchema body in eqS
extract-commute-inj₁ b al (DFunDef name alloc body ∷ rest) nothing eq | just pty
  with extractFunctions-go al rest nothing in eq2
... | inj₁ e with eq
...   | refl rewrite siglessSchema-canon b body | eqS
                   | extract-commute-inj₁ b al rest nothing eq2 = refl
extract-commute-inj₁ b al (DFunDef name alloc body ∷ rest) nothing eq | nothing
  with extractFunctions-go al rest nothing in eq2
... | inj₁ e with eq
...   | refl rewrite siglessSchema-canon b body | eqS
                   | extract-commute-inj₁ b al rest nothing eq2 = refl
extract-commute-inj₁ b al (DSignature name nothing ty se ∷ rest) pending eq with projectSig al name ty
... | inj₁ err = eq
... | inj₂ gty with extractFunctions-go al rest nothing in eq2
...   | inj₁ e with eq
...     | refl rewrite extract-commute-inj₁ b al rest nothing eq2 = refl
extract-commute-inj₁ b al (DSignature name (just owner) ty se ∷ rest) pending eq with projectSig al (owner ++ "." ++ name) ty
... | inj₁ err = eq
... | inj₂ gty with extractFunctions-go al rest nothing in eq2
...   | inj₁ e with eq
...     | refl rewrite extract-commute-inj₁ b al rest nothing eq2 = refl
extract-commute-inj₁ b al (DImport imp ∷ rest) pending eq = extract-commute-inj₁ b al rest pending eq
extract-commute-inj₁ b al (DTypeAlias n ps t ∷ rest) pending eq = extract-commute-inj₁ b al rest pending eq

------------------------------------------------------------------------
-- guardDistinct: a distinctness FAILURE rides (the error string is constant,
-- the check reads only emittedNames).
------------------------------------------------------------------------

distinctOrErr-inj₁-transfer-inj₂ : ∀ {c : Bool} {A B : List FunInfo × List PolyFunInfo} {x}
  → distinctOrErr c (inj₂ A) ≡ inj₁ x → distinctOrErr c (inj₂ B) ≡ inj₁ x
distinctOrErr-inj₁-transfer-inj₂ {false} eq = eq
distinctOrErr-inj₁-transfer-inj₂ {true}  ()

------------------------------------------------------------------------
-- The assembled lemma.
------------------------------------------------------------------------

extractFunctions-canon-inj₁ : ∀ (ds : List Decl) {x}
  → C.extractFunctions (C.extractAliases (mkModule ds)) (mkModule ds) ≡ inj₁ x
  → C.extractFunctions (C.extractAliases (canonModule ds)) (canonModule ds) ≡ inj₁ x
extractFunctions-canon-inj₁ ds {x} eq rewrite extractAliases-canon ds =
  aux (extractFunctions-go al ds nothing) refl eq
  where
    al = C.extractAliases (mkModule ds)
    b  = polyDefNames ds
    aux : ∀ r → extractFunctions-go al ds nothing ≡ r → C.guardDistinct r ≡ inj₁ x
        → C.guardDistinct (extractFunctions-go al (map (canonDecl b [] []) ds) nothing) ≡ inj₁ x
    aux (inj₁ e) egU eqg rewrite extract-commute-inj₁ b al ds nothing egU = eqg
    aux (inj₂ (funs , polys)) egU eqg
      rewrite extract-commute b al ds nothing egU | emittedNames-canon b funs =
        distinctOrErr-inj₁-transfer-inj₂ eqg
