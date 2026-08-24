-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Grammar.ImportBridge — independent relational spec for the IMPORT
-- declaration parser + sound/complete bridge. First
-- proven leaf for `Once.Adequacy`'s `ParsesDecl`.
--
--   * `ParsesModulePath` (dotted module path) ↔ `parseModulePath-WFB`.
--   * `ParsesImportAlias` (optional `as Alias`) ↔ `parseImportAliasB`.
--   * `ParsesImport`      (path then alias)    ↔ `parseImportB`.
--
-- `wordHead := is-just ∘ anyWordB` relates definitionally to the executable, so
-- most inversions need no per-token enumeration; the only enumeration is
-- `anyWordB-inv` (a word-result forces a `TWord` head). The path parser never
-- fails on a word head (`pmp-dot ≢ nothing`).
------------------------------------------------------------------------

module Once.Grammar.ImportBridge where

open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ; suc; _<_; _≤_; s≤s; z≤n)
open import Data.Nat.Induction using (<-wellFounded)
open import Data.Nat.Properties using (≤-refl; <-trans; ≤-<-trans; <-≤-trans; <⇒≤; m≤n⇒m≤1+n)
open import Data.List using (List; []; _∷_; length)
open import Data.String using (String) renaming (_≟_ to _≟s_)
open import Data.Maybe using (Maybe; just; nothing; is-just)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Induction.WellFounded using (Acc; acc)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong)

open import Once.Parser.Token
open import Once.Parser.Module.Core using (ParseAtB; ParseAtB≤; anyWordB; Decl; DImport; Import; mkImport)
open import Once.Parser.Module.Import
  using (parseModulePath-WFB; pmp-aw; pmp-tail; pmp-dot; parseModulePathB;
         dropDot; dropDot-≤; dotHead;
         parseImportAliasB; pia-head; pia-as; pia-w; parseImportB; pib-path; pib-alias)

wordHead : List Token → Bool
wordHead toks = is-just (anyWordB toks)

------------------------------------------------------------------------
-- The parser never returns `nothing` on a word head; it fails only via
-- `anyWordB` failing.  (No token enumeration: `pmp-dot` is `just` in both
-- clauses, `pmp-tail false` likewise.)
------------------------------------------------------------------------

pmp-dot≢nothing : ∀ (toks : List Token) (rec : ∀ {y} → y < length toks → Acc _<_ y)
  (name : String) (tail : List Token) (bnd : length tail < length toks)
  (sub : ParseAtB {List String} (dropDot tail)) → ¬ (pmp-dot toks rec name tail bnd sub ≡ nothing)
pmp-dot≢nothing toks rec name tail bnd (just _) ()
pmp-dot≢nothing toks rec name tail bnd nothing  ()

pmp-tail≢nothing : ∀ (toks : List Token) (rec : ∀ {y} → y < length toks → Acc _<_ y)
  (name : String) (tail : List Token) (bnd : length tail < length toks)
  (cont : Bool) → ¬ (pmp-tail toks rec name tail bnd cont ≡ nothing)
pmp-tail≢nothing toks rec name tail bnd false ()
pmp-tail≢nothing toks rec name tail bnd true =
  pmp-dot≢nothing toks rec name tail bnd
    (parseModulePath-WFB (dropDot tail) (rec (≤-<-trans (dropDot-≤ tail) bnd)))

mp-nothing→aw : ∀ (toks : List Token) (a : Acc _<_ (length toks)) →
  parseModulePath-WFB toks a ≡ nothing → anyWordB toks ≡ nothing
mp-nothing→aw toks (acc rec) eq with anyWordB toks
... | nothing = refl
... | just (name , tail , bnd) = ⊥-elim (pmp-tail≢nothing toks rec name tail bnd (dotHead tail) eq)

mp-nothing→wh-false : ∀ (toks : List Token) (a : Acc _<_ (length toks)) →
  parseModulePath-WFB toks a ≡ nothing → wordHead toks ≡ false
mp-nothing→wh-false toks a eq = cong is-just (mp-nothing→aw toks a eq)

wh-false→nothing : ∀ (toks : List Token) (a : Acc _<_ (length toks)) →
  wordHead toks ≡ false → parseModulePath-WFB toks a ≡ nothing
wh-false→nothing toks (acc rec) wf with anyWordB toks
... | nothing = refl
... | just _ with () ← wf

------------------------------------------------------------------------
-- The relation.
------------------------------------------------------------------------

data ParsesModulePath : List Token → List String → List Token → Set where
  pmp-cons    : ∀ {name tail path rest'} → dotHead tail ≡ true →
                ParsesModulePath (dropDot tail) path rest' →
                ParsesModulePath (TWord name ∷ tail) (name ∷ path) rest'
  pmp-dotfail : ∀ {name tail} → dotHead tail ≡ true → wordHead (dropDot tail) ≡ false →
                ParsesModulePath (TWord name ∷ tail) (name ∷ []) tail
  pmp-nodot   : ∀ {name tail} → dotHead tail ≡ false →
                ParsesModulePath (TWord name ∷ tail) (name ∷ []) tail

------------------------------------------------------------------------
-- SOUNDNESS.
------------------------------------------------------------------------

sound-mpWF : ∀ (toks : List Token) (a : Acc _<_ (length toks)) {path rest bnd} →
  parseModulePath-WFB toks a ≡ just (path , rest , bnd) → ParsesModulePath toks path rest
sound-mpWF (TWord name ∷ tail) (acc rec) h with dotHead tail in dh
... | false with refl ← just-injective h = pmp-nodot dh
... | true with parseModulePath-WFB (dropDot tail) (rec (≤-<-trans (dropDot-≤ tail) (s≤s ≤-refl))) in subeq
...   | just (path , rest' , bnd') with refl ← just-injective h =
        pmp-cons dh (sound-mpWF (dropDot tail) (rec (≤-<-trans (dropDot-≤ tail) (s≤s ≤-refl))) subeq)
...   | nothing with refl ← just-injective h =
        pmp-dotfail dh (mp-nothing→wh-false (dropDot tail) (rec (≤-<-trans (dropDot-≤ tail) (s≤s ≤-refl))) subeq)
-- non-word heads: `anyWordB` fails, so the parser returns `nothing` (`h` absurd).
sound-mpWF [] (acc rec) ()
sound-mpWF (TInt _ _ ∷ _) (acc rec) ()
sound-mpWF (TString _ ∷ _) (acc rec) ()
sound-mpWF (TLParen ∷ _) (acc rec) ()
sound-mpWF (TRParen ∷ _) (acc rec) ()
sound-mpWF (TLBrace ∷ _) (acc rec) ()
sound-mpWF (TRBrace ∷ _) (acc rec) ()
sound-mpWF (TColon ∷ _) (acc rec) ()
sound-mpWF (TEquals ∷ _) (acc rec) ()
sound-mpWF (TArrow ∷ _) (acc rec) ()
sound-mpWF (TCaret1 ∷ _) (acc rec) ()
sound-mpWF (TCaret0 ∷ _) (acc rec) ()
sound-mpWF (TCaretW ∷ _) (acc rec) ()
sound-mpWF (TLambda ∷ _) (acc rec) ()
sound-mpWF (TComma ∷ _) (acc rec) ()
sound-mpWF (TSemicolon ∷ _) (acc rec) ()
sound-mpWF (TAt ∷ _) (acc rec) ()
sound-mpWF (TPipe ∷ _) (acc rec) ()
sound-mpWF (TDot ∷ _) (acc rec) ()
sound-mpWF (TPlus ∷ _) (acc rec) ()
sound-mpWF (TMinus ∷ _) (acc rec) ()
sound-mpWF (TStar ∷ _) (acc rec) ()
sound-mpWF (TSlash ∷ _) (acc rec) ()
sound-mpWF (TPercent ∷ _) (acc rec) ()
sound-mpWF (TAmpersand ∷ _) (acc rec) ()
sound-mpWF (TLt ∷ _) (acc rec) ()
sound-mpWF (TLe ∷ _) (acc rec) ()
sound-mpWF (TGt ∷ _) (acc rec) ()
sound-mpWF (TGe ∷ _) (acc rec) ()
sound-mpWF (TEqEq ∷ _) (acc rec) ()
sound-mpWF (TNeq ∷ _) (acc rec) ()
sound-mpWF (TBang ∷ _) (acc rec) ()
sound-mpWF (TNewline ∷ _) (acc rec) ()
sound-mpWF (TEOF ∷ _) (acc rec) ()

sound-mp : ∀ {toks path rest bnd} → parseModulePathB toks ≡ just (path , rest , bnd) →
  ParsesModulePath toks path rest
sound-mp {toks} h = sound-mpWF toks (<-wellFounded (length toks)) h

------------------------------------------------------------------------
-- COMPLETENESS.
------------------------------------------------------------------------

complete-mpWF : ∀ {toks path rest} (a : Acc _<_ (length toks)) → ParsesModulePath toks path rest →
  Σ[ bnd ∈ (length rest < length toks) ] parseModulePath-WFB toks a ≡ just (path , rest , bnd)
complete-mpWF (acc rec) (pmp-cons {name} {tail} dh sub) rewrite dh
  with complete-mpWF (rec (≤-<-trans (dropDot-≤ tail) (s≤s ≤-refl))) sub
... | (bnd' , eqr) rewrite eqr =
  <-trans bnd' (≤-<-trans (dropDot-≤ tail) (s≤s ≤-refl)) , refl
complete-mpWF (acc rec) (pmp-dotfail {name} {tail} dh wf) rewrite dh
  rewrite wh-false→nothing (dropDot tail) (rec (≤-<-trans (dropDot-≤ tail) (s≤s ≤-refl))) wf =
  s≤s ≤-refl , refl
complete-mpWF (acc rec) (pmp-nodot {name} {tail} dh) rewrite dh = s≤s ≤-refl , refl

complete-mp : ∀ {toks path rest} → ParsesModulePath toks path rest →
  Σ[ bnd ∈ (length rest < length toks) ] parseModulePathB toks ≡ just (path , rest , bnd)
complete-mp {toks} d = complete-mpWF (<-wellFounded (length toks)) d

------------------------------------------------------------------------
-- Stage 2: `ParsesImportAlias` (optional `as Alias`) + `ParsesImport`.
------------------------------------------------------------------------

-- A word-result forces a `TWord` head. The one unavoidable enumeration (33
-- non-word `Token` heads); reused by the alias soundness.
anyWordB-inv : ∀ {toks s rest bnd} → anyWordB toks ≡ just (s , rest , bnd) → toks ≡ TWord s ∷ rest
anyWordB-inv {TWord _ ∷ _} refl = refl
anyWordB-inv {[]} ()
anyWordB-inv {TInt _ _ ∷ _} ()
anyWordB-inv {TString _ ∷ _} ()
anyWordB-inv {TLParen ∷ _} ()
anyWordB-inv {TRParen ∷ _} ()
anyWordB-inv {TLBrace ∷ _} ()
anyWordB-inv {TRBrace ∷ _} ()
anyWordB-inv {TColon ∷ _} ()
anyWordB-inv {TEquals ∷ _} ()
anyWordB-inv {TArrow ∷ _} ()
anyWordB-inv {TCaret1 ∷ _} ()
anyWordB-inv {TCaret0 ∷ _} ()
anyWordB-inv {TCaretW ∷ _} ()
anyWordB-inv {TLambda ∷ _} ()
anyWordB-inv {TComma ∷ _} ()
anyWordB-inv {TSemicolon ∷ _} ()
anyWordB-inv {TAt ∷ _} ()
anyWordB-inv {TPipe ∷ _} ()
anyWordB-inv {TDot ∷ _} ()
anyWordB-inv {TPlus ∷ _} ()
anyWordB-inv {TMinus ∷ _} ()
anyWordB-inv {TStar ∷ _} ()
anyWordB-inv {TSlash ∷ _} ()
anyWordB-inv {TPercent ∷ _} ()
anyWordB-inv {TAmpersand ∷ _} ()
anyWordB-inv {TLt ∷ _} ()
anyWordB-inv {TLe ∷ _} ()
anyWordB-inv {TGt ∷ _} ()
anyWordB-inv {TGe ∷ _} ()
anyWordB-inv {TEqEq ∷ _} ()
anyWordB-inv {TNeq ∷ _} ()
anyWordB-inv {TBang ∷ _} ()
anyWordB-inv {TNewline ∷ _} ()
anyWordB-inv {TEOF ∷ _} ()

ij-false : ∀ {A : Set} {m : Maybe A} → is-just m ≡ false → m ≡ nothing
ij-false {m = just _} ()
ij-false {m = nothing} _ = refl

data ParsesImportAlias (path : List String) : List Token → Decl → List Token → Set where
  pia-alias-r   : ∀ {alias rest} →
    ParsesImportAlias path (TWord "as" ∷ TWord alias ∷ rest) (DImport (mkImport path (just alias))) rest
  pia-neq-r     : ∀ {s rest} → s ≢ "as" →
    ParsesImportAlias path (TWord s ∷ rest) (DImport (mkImport path nothing)) (TWord s ∷ rest)
  pia-nonword-r : ∀ {toks} → wordHead toks ≡ false →
    ParsesImportAlias path toks (DImport (mkImport path nothing)) toks

sound-alias : ∀ {path toks d rest bnd} → parseImportAliasB path toks ≡ just (d , rest , bnd) →
  ParsesImportAlias path toks d rest
sound-alias {path} {toks} h with anyWordB toks in aw
... | nothing with refl ← just-injective h = pia-nonword-r (cong is-just aw)
... | just (s , rest , bnd) with anyWordB-inv aw
...   | refl with s ≟s "as"
...     | no ¬p with refl ← just-injective h = pia-neq-r ¬p
...     | yes refl with anyWordB rest in aw2
...       | nothing with () ← h
...       | just (alias , rest' , bnd2) with anyWordB-inv aw2
...         | refl with refl ← just-injective h = pia-alias-r

complete-alias : ∀ {path toks d rest} → ParsesImportAlias path toks d rest →
  Σ[ bnd ∈ (length rest ≤ length toks) ] parseImportAliasB path toks ≡ just (d , rest , bnd)
complete-alias (pia-alias-r {alias} {rest}) = _ , refl
complete-alias (pia-neq-r {s} {rest} ¬p) with s ≟s "as"
... | yes p = ⊥-elim (¬p p)
... | no _ = ≤-refl , refl
complete-alias {path} (pia-nonword-r {toks} wf) rewrite ij-false wf = ≤-refl , refl

------------------------------------------------------------------------
-- `ParsesImport` = dotted path then optional alias.
------------------------------------------------------------------------

data ParsesImport : List Token → Decl → List Token → Set where
  pi-mk : ∀ {toks path rest d rest'} →
    ParsesModulePath toks path rest → ParsesImportAlias path rest d rest' →
    ParsesImport toks d rest'

sound-import : ∀ {toks d rest bnd} → parseImportB toks ≡ just (d , rest , bnd) → ParsesImport toks d rest
sound-import {toks} h with parseModulePathB toks in eq1
... | nothing with () ← h
... | just (path , rest , bnd) with parseImportAliasB path rest in eq2
...   | nothing with () ← h
...   | just (d , rest' , bnd') with refl ← just-injective h = pi-mk (sound-mp eq1) (sound-alias eq2)

complete-import : ∀ {toks d rest} → ParsesImport toks d rest →
  Σ[ bnd ∈ (length rest < length toks) ] parseImportB toks ≡ just (d , rest , bnd)
complete-import (pi-mk mp al) with complete-mp mp
... | (bnd , eq1) rewrite eq1 with complete-alias al
...   | (bnd' , eq2) rewrite eq2 = ≤-<-trans bnd' bnd , refl
