-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Grammar.DeclBridge — the per-declaration relation `ParsesDecl` (a sum of
-- the six decl forms) + `sound-decl`/`complete-decl`, dispatching on `parseDeclB`
-- (the `pdb-kw1→kw2→kw3→fb` keyword chain + `tryOpDeclB`). Discharges the apex
-- `ParsesDecl`/`sound-decl`/`complete-decl` postulate, replacing it with
-- a proof.
------------------------------------------------------------------------

module Once.Grammar.DeclBridge where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; length)
open import Data.String using (String) renaming (_≟_ to _≟s_)
open import Data.Nat using (_<_)
open import Data.Maybe using (just; nothing)
open import Data.Product using (Σ; Σ-syntax; _,_)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Once.Type using (PolyType)
open import Once.Parser.Token
open import Once.Parser.Module.Core using (Decl; DTypeSig)
open import Once.Parser.Module using (parseDeclB; colonHead; colDrop1; eqHead)
open import Once.Parser.Module.Import using (parseImportB)
open import Once.Parser.Module.DeclTail using (parseTypeAliasB; parseSignatureB)
open import Once.Parser.Module.FunDef.Def using (parseFunDefB)
open import Once.Parser.Module.FunDef.OpDecl using (tryOpDeclB)
open import Once.Parser.PolyType using (parsePolyTypeB)
open import Once.Parser.Generic.PolyInst using (ParsesPolyType)
open import Once.Grammar.PolyTypeBridge using (parsePolyTypeB-sound; parsePolyTypeB-complete)
open import Once.Grammar.ImportBridge using (ParsesImport; sound-import; complete-import)
open import Once.Grammar.TypeAliasBridge using (ParsesTypeAliasDecl; sound-typealias; complete-typealias)
open import Once.Grammar.SignatureBridge using (ParsesSignature; sound-signature; complete-signature)
open import Once.Grammar.FunDefBridge using (ParsesFunDef; sound-fundef; complete-fundef)
open import Once.Grammar.OpDeclBridge using (ParsesOpDecl; sound-opDecl; complete-opDecl)

data ParsesDecl : List Token → Decl → List Token → Set where
  pd-import    : ∀ {rest d rest'} → ParsesImport rest d rest' →
                 ParsesDecl (TWord "import" ∷ rest) d rest'
  pd-typealias : ∀ {rest d rest'} → ParsesTypeAliasDecl rest d rest' →
                 ParsesDecl (TWord "type" ∷ rest) d rest'
  pd-signature : ∀ {rest d rest'} → ParsesSignature rest d rest' →
                 ParsesDecl (TWord "signature" ∷ rest) d rest'
  pd-typesig   : ∀ {w rest ty rest'} → ¬ (w ≡ "import") → ¬ (w ≡ "type") → ¬ (w ≡ "signature") →
                 colonHead rest ≡ true → ParsesPolyType (colDrop1 rest) ty rest' → eqHead rest' ≡ false →
                 ParsesDecl (TWord w ∷ rest) (DTypeSig w ty) rest'
  pd-fundef    : ∀ {w rest d rest'} → ¬ (w ≡ "import") → ¬ (w ≡ "type") → ¬ (w ≡ "signature") →
                 colonHead rest ≡ false → ParsesFunDef w rest d rest' →
                 ParsesDecl (TWord w ∷ rest) d rest'
  pd-opdecl    : ∀ {rest d rest'} → ParsesOpDecl (TLParen ∷ rest) d rest' →
                 ParsesDecl (TLParen ∷ rest) d rest'

------------------------------------------------------------------------
-- Soundness.
------------------------------------------------------------------------

sound-decl : ∀ {toks d rest bnd} → parseDeclB toks ≡ just (d , rest , bnd) → ParsesDecl toks d rest
sound-decl {TWord w ∷ rest} h with w ≟s "import"
... | yes refl with parseImportB rest in pi
...   | just _ with refl ← h = pd-import (sound-import pi)
sound-decl {TWord w ∷ rest} h | no ne1 with w ≟s "type"
... | yes refl with parseTypeAliasB rest in pt
...   | just _ with refl ← h = pd-typealias (sound-typealias pt)
sound-decl {TWord w ∷ rest} h | no ne1 | no ne2 with w ≟s "signature"
... | yes refl with parseSignatureB rest in ps
...   | just _ with refl ← h = pd-signature (sound-signature ps)
sound-decl {TWord w ∷ rest} h | no ne1 | no ne2 | no ne3 with colonHead rest in ch
... | true with parsePolyTypeB (colDrop1 rest) in pp
...   | just (ty , rest' , bnd) with eqHead rest' in eqf
...     | false with refl ← h = pd-typesig ne1 ne2 ne3 ch (parsePolyTypeB-sound pp) eqf
sound-decl {TWord w ∷ rest} h | no ne1 | no ne2 | no ne3 | false with parseFunDefB w rest in pf
... | just _ with refl ← h = pd-fundef ne1 ne2 ne3 ch (sound-fundef pf)
sound-decl {TLParen ∷ rest} h = pd-opdecl (sound-opDecl h)

------------------------------------------------------------------------
-- Completeness.
------------------------------------------------------------------------

complete-decl : ∀ {toks d rest} → ParsesDecl toks d rest →
  Σ[ bnd ∈ (length rest < length toks) ] parseDeclB toks ≡ just (d , rest , bnd)
complete-decl (pd-import di) with complete-import di
... | (_ , pi) rewrite pi = _ , refl
complete-decl (pd-typealias dt) with complete-typealias dt
... | (_ , pt) rewrite pt = _ , refl
complete-decl (pd-signature ds) with complete-signature ds
... | (_ , ps) rewrite ps = _ , refl
complete-decl (pd-typesig {w} ne1 ne2 ne3 ch dpt eqf) with w ≟s "import"
... | yes p = ⊥-elim (ne1 p)
... | no _ with w ≟s "type"
...   | yes p = ⊥-elim (ne2 p)
...   | no _ with w ≟s "signature"
...     | yes p = ⊥-elim (ne3 p)
...     | no _ rewrite ch with parsePolyTypeB-complete dpt
...       | (_ , pp) rewrite pp rewrite eqf = _ , refl
complete-decl (pd-fundef {w} ne1 ne2 ne3 ch dfd) with w ≟s "import"
... | yes p = ⊥-elim (ne1 p)
... | no _ with w ≟s "type"
...   | yes p = ⊥-elim (ne2 p)
...   | no _ with w ≟s "signature"
...     | yes p = ⊥-elim (ne3 p)
...     | no _ rewrite ch with complete-fundef dfd
...       | (_ , pf) rewrite pf = _ , refl
complete-decl (pd-opdecl dod) with complete-opDecl dod
... | (_ , td) rewrite td = _ , refl
