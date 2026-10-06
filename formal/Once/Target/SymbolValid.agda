-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Target.SymbolValid — plan 0.107 §8 step 4 (D272, D275): EVERY SYMBOL
-- THE COMPILER RENDERS IS ONE `as` READS AS A SYMBOL NAME.
--
-- Since D275 the z-encoding is total: a char `as` accepts inside a symbol (a
-- letter, a digit, `_`) stands for itself and every other char is escaped. So
-- `once-symbol-path cn` is an `as` symbol for EVERY canonical name, not only
-- for lexer identifiers — the property needs no premise about where a name
-- came from. Label symbols add fixed prefixes, decimal numbers and `_`.
------------------------------------------------------------------------

module Once.Target.SymbolValid where

open import Data.Bool using (Bool; true; false; _∨_; T)
open import Data.Char using (Char; isAlpha; isDigit; toℕ)
open import Data.List using (List; []; _∷_; _++_; map; concatMap)
import Data.List
open import Data.List.Relation.Unary.All using (All; []; _∷_) renaming (map to All-map)
open import Data.List.Relation.Unary.All.Properties using (++⁺)
open import Data.Nat using (ℕ; _≡ᵇ_)
open import Data.Nat.Show using (charsInBase)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥-elim)
open import Data.String using (String; toList) renaming (_++_ to _++ˢ_)
open import Data.String.Unsafe using (toList-++; toList∘fromList)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)
open import Relation.Nullary using (Dec; yes; no)
open import Data.Char.Properties using (_≟_)

open import Once.CanonicalName using (CanonicalName; parts; canonical)
open import Once.Target.AsmSymbol using (AsmSym; AsmSymChars; sym-start; sym-continue; sym-punct)
open import Once.Target.Symbol
  using (z-encode-char; z-encode-char-aux; symbol-char?; showNat; once-symbol-path; once-symbol-own; once-prefix;
         mangle-component; join-us)
open import Once.Target.SymbolInjective
  using (zencL; mangL; joinUsL'; withSep; toList-mangle; toList-joinUs; body-rel; charsInBase-all-digits)
open import Once.CCC.Label using (LabelId; owner; path; idx; showLabelId; showPath; labelSym; thunkSym; entrySym;
                                  Label; once; callee; sigop; EntryId; e-thunk; e-fn)

------------------------------------------------------------------------
-- Chars that continue a symbol.
------------------------------------------------------------------------

SymCont : List Char → Set
SymCont = All (λ d → T (sym-continue d))

private
  ∨-true : ∀ (b : Bool) → T (b ∨ true)
  ∨-true true  = tt
  ∨-true false = tt

  -- `symbol-char?`'s three cases are each among `sym-continue`'s.
  bool-lem : ∀ (a d u x : Bool) → (a ∨ d ∨ u) ≡ true → T ((a ∨ (u ∨ x)) ∨ d)
  bool-lem true  d     u     x _ = tt
  bool-lem false true  u     x _ = ∨-true (u ∨ x)
  bool-lem false false true  x _ = tt
  bool-lem false false false x ()

digit-cont : ∀ {c} → isDigit c ≡ true → T (sym-continue c)
digit-cont {c} p = subst (λ d → T ((isAlpha c ∨ sym-punct c) ∨ d)) (sym p) (∨-true (isAlpha c ∨ sym-punct c))

digits-cont : ∀ (n : ℕ) → SymCont (charsInBase 10 n)
digits-cont n = All-map (λ {c} → digit-cont {c}) (charsInBase-all-digits n)

showNat-cont : ∀ (n : ℕ) → SymCont (toList (showNat n))
showNat-cont n = subst SymCont (sym (toList∘fromList (charsInBase 10 n))) (digits-cont n)

private
  zchar-cont-aux : ∀ (c : Char) d1 d2 d3 d4 d5 d6 d7 (b : Bool) → symbol-char? c ≡ b
                 → SymCont (z-encode-char-aux c d1 d2 d3 d4 d5 d6 d7 b)
  zchar-cont-aux c (yes _) _ _ _ _ _ _ _ _ = tt ∷ tt ∷ []
  zchar-cont-aux c (no _) (yes _) _ _ _ _ _ _ _ = tt ∷ tt ∷ []
  zchar-cont-aux c (no _) (no _) (yes _) _ _ _ _ _ _ = tt ∷ tt ∷ []
  zchar-cont-aux c (no _) (no _) (no _) (yes _) _ _ _ _ _ = tt ∷ tt ∷ []
  zchar-cont-aux c (no _) (no _) (no _) (no _) (yes _) _ _ _ _ = tt ∷ tt ∷ []
  zchar-cont-aux c (no _) (no _) (no _) (no _) (no _) (yes _) _ _ _ = tt ∷ tt ∷ []
  zchar-cont-aux c (no _) (no _) (no _) (no _) (no _) (no _) (yes _) _ _ = tt ∷ tt ∷ []
  zchar-cont-aux c (no _) (no _) (no _) (no _) (no _) (no _) (no _) true e =
    bool-lem (isAlpha c) (isDigit c) (toℕ c ≡ᵇ toℕ '_') _ e ∷ []
  zchar-cont-aux c (no _) (no _) (no _) (no _) (no _) (no _) (no _) false _ =
    tt ∷ tt ∷ ++⁺ (showNat-cont (toℕ c)) (tt ∷ [])

zchar-cont : ∀ (c : Char) → SymCont (z-encode-char c)
zchar-cont c = zchar-cont-aux c (c ≟ 'z') (c ≟ '\'') (c ≟ '+') (c ≟ '*')
                                (c ≟ '!') (c ≟ '?') (c ≟ '.') (symbol-char? c) refl

zencL-cont : ∀ (cs : List Char) → SymCont (zencL cs)
zencL-cont []       = []
zencL-cont (c ∷ cs) = ++⁺ (zchar-cont c) (zencL-cont cs)

mangL-cont : ∀ (cs : List Char) → SymCont (mangL cs)
mangL-cont cs = ++⁺ (digits-cont (Data.List.length (zencL cs))) (zencL-cont cs)

private
  withSep-cont : ∀ (xss : List (List Char)) → All SymCont xss → SymCont (withSep xss)
  withSep-cont []         []         = []
  withSep-cont (xs ∷ xss) (a ∷ as) = tt ∷ ++⁺ a (withSep-cont xss as)

  joinUs-cont : ∀ (xss : List (List Char)) → All SymCont xss → SymCont (joinUsL' xss)
  joinUs-cont []         []       = []
  joinUs-cont (xs ∷ xss) (a ∷ as) = ++⁺ a (withSep-cont xss as)

  mangs-cont : ∀ (ps : List (List Char)) → All SymCont (map mangL ps)
  mangs-cont []       = []
  mangs-cont (p ∷ ps) = mangL-cont p ∷ mangs-cont ps

------------------------------------------------------------------------
-- Strings
------------------------------------------------------------------------

-- An `as` symbol followed by symbol-continuing chars is an `as` symbol.
asm-chars-++ : ∀ (xs ys : List Char) → AsmSymChars xs → SymCont ys → AsmSymChars (xs ++ ys)
asm-chars-++ []       ys () c
asm-chars-++ (x ∷ xs) ys (h , a) c = h , ++⁺ a c

asm-++ : ∀ (s t : String) → AsmSym s → SymCont (toList t) → AsmSym (s ++ˢ t)
asm-++ s t a c = subst AsmSymChars (sym (toList-++ s t)) (asm-chars-++ (toList s) (toList t) a c)

-- …and an `as` symbol's chars all continue one.
private
  start⇒cont : ∀ {c} → T (sym-start c) → T (sym-continue c)
  start⇒cont {c} h with sym-start c
  ... | true = tt

asm-chars-cont : ∀ (xs : List Char) → AsmSymChars xs → SymCont xs
asm-chars-cont []       ()
asm-chars-cont (x ∷ xs) (h , a) = start⇒cont {x} h ∷ a

cont-++ : ∀ (s t : String) → SymCont (toList s) → SymCont (toList t) → SymCont (toList (s ++ˢ t))
cont-++ s t a b = subst SymCont (sym (toList-++ s t)) (++⁺ a b)

------------------------------------------------------------------------
-- THE SYMBOLS
------------------------------------------------------------------------

-- Every canonical name's symbol (D275: whatever its components).
once-symbol-path-asm : ∀ (cn : CanonicalName) → AsmSym (once-symbol-path cn)
once-symbol-path-asm cn =
  asm-++ once-prefix (join-us (map mangle-component (parts cn))) (tt , tt ∷ tt ∷ tt ∷ tt ∷ [])
    (subst SymCont (sym (trans (toList-joinUs (map mangle-component (parts cn)))
                               (cong joinUsL' (body-rel (parts cn)))))
           (joinUs-cont _ (mangs-cont (map toList (parts cn)))))

once-symbol-own-asm : ∀ (x : String) → AsmSym (once-symbol-own x)
once-symbol-own-asm x = once-symbol-path-asm (canonical (x ∷ []))

private
  showPath-cont : ∀ (ns : List ℕ) → SymCont (toList (showPath ns))
  showPath-cont []       = []
  showPath-cont (n ∷ ns) = cont-++ "_" (showNat n ++ˢ showPath ns) (tt ∷ []) (cont-++ (showNat n) (showPath ns) (showNat-cont n) (showPath-cont ns))

showLabelId-cont : ∀ (n : LabelId) → SymCont (toList (showLabelId n))
showLabelId-cont n =
  cont-++ (once-symbol-path (owner n)) (showPath (path n) ++ˢ "_" ++ˢ showNat (idx n))
    (asm-chars-cont (toList (once-symbol-path (owner n))) (once-symbol-path-asm (owner n)))
    (cont-++ (showPath (path n)) ("_" ++ˢ showNat (idx n)) (showPath-cont (path n))
      (cont-++ "_" (showNat (idx n)) (tt ∷ []) (showNat-cont (idx n))))

thunkSym-asm : ∀ (n : LabelId) → AsmSym (thunkSym n)
thunkSym-asm n = asm-++ ".L_thunk_" (showLabelId n) (tt , tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ []) (showLabelId-cont n)

entrySym-asm : ∀ (e : EntryId) → AsmSym (entrySym e)
entrySym-asm (e-thunk n) = thunkSym-asm n
entrySym-asm (e-fn f)    = once-symbol-path-asm f

-- The labels an image DEFINES (`once`, `callee`) — a SigOp label carries a
-- name of its own and is not one of them.
once-label-asm : ∀ (n : LabelId) → AsmSym (labelSym (once n))
once-label-asm n = asm-++ ".Lonce_" (showLabelId n) (tt , tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ []) (showLabelId-cont n)

callee-label-asm : ∀ (e : EntryId) → AsmSym (labelSym (callee e))
callee-label-asm = entrySym-asm
