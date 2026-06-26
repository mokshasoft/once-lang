-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Grammar.ImportBridge — independent relational spec for the IMPORT
-- declaration parser + sound/complete bridge. No shim, no postulate. First
-- proven leaf for `Once.Adequacy`'s `ParsesDecl`.
--
-- Stage 1: `ParsesModulePath` (dotted module path) over the classifier-routed
-- `parseModulePath-WFB`. `wordHead := is-just ∘ anyWordB` relates definitionally
-- to the executable, so the inversions need no per-token enumeration; the parser
-- never fails on a word head (`pmp-dot ≢ nothing`).
------------------------------------------------------------------------

module Once.Grammar.ImportBridge where

open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ; suc; _<_; _≤_; s≤s; z≤n)
open import Data.Nat.Induction using (<-wellFounded)
open import Data.Nat.Properties using (≤-refl; <-trans; ≤-<-trans; <-≤-trans; <⇒≤; m≤n⇒m≤1+n)
open import Data.List using (List; []; _∷_; length)
open import Data.String using (String)
open import Data.Maybe using (Maybe; just; nothing; is-just)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Induction.WellFounded using (Acc; acc)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

open import Once.Parser.Token
open import Once.Parser.Module.Core using (ParseAtB; anyWordB)
open import Once.Parser.Module.Import
  using (parseModulePath-WFB; pmp-aw; pmp-tail; pmp-dot; parseModulePathB;
         dropDot; dropDot-≤; dotHead)

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
sound-mpWF (TInt _ ∷ _) (acc rec) ()
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
