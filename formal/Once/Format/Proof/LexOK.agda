-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Format.Proof.LexOK — what the Spec's lexer reads is printable
-- (plan 0.124 step 4.1).
--
-- Every token of a lexed text is printable, a line end, the end, or a string:
-- a word is an identifier, an integer non-negative, a float's fraction fits
-- its digits. The last needs a fact about the primitive `isDigit` (it
-- accepts the ten decimal digits only), which Agda's conversion cannot see:
-- tool hypothesis T3, `Once.Postulates.isDigit-value`.
--
-- Generated (the cases per lexing rule) by `scripts/gen-format-lexok.py`:
-- edit the generator, not this file.
------------------------------------------------------------------------

module Once.Format.Proof.LexOK where

open import Data.Char using (Char; isDigit)
import Data.Char as Ch
open import Data.List using (List; []; _∷_; length)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _^_; _<_; _≤_; s≤s; z≤n)
open import Data.Nat.Properties using (+-mono-≤; *-mono-≤; ≤-refl; ≤-trans; <-≤-trans; *-identityʳ; *-assoc; *-comm;
  +-comm; n<1+n; *-monoˡ-≤; +-monoʳ-<; ≤-reflexive)
open import Data.Product using (_×_; _,_; ∃-syntax)
open import Data.String using (String; fromList)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
import Relation.Binary.PropositionalEquality as Eq

open import Once.Postulates using (toList∘fromList; isDigit-value)
open import Once.Spec.Surface.Lexing
open import Once.Format.Proof.Lexing using (Printable; p-word; p-int; p-float; p-sym; s-lparen; s-rparen; s-lbrace;
  s-rbrace; s-colon; s-equals; s-arrow; s-caret1; s-caret0; s-caretw; s-lambda; s-comma; s-semicolon; s-at; s-pipe;
  s-dot; s-plus; s-minus; s-star; s-slash; s-percent; s-ampersand; s-lt; s-le; s-gt; s-ge; s-eqeq; s-neq; s-bang)

-- What else the lexer writes.
data Other : Token → Set where
  o-nl  : Other TNewline
  o-eof : Other TEOF
  o-str : ∀ {s} → Other (TString s)

LexOK : Token → Set
LexOK t = Printable t ⊎ Other t

open import Data.Bool using (true)

private
  identAll : ∀ {cs i r} → IdentRest cs i r → All (λ x → isIdentContinue x ≡ true) i
  identAll id-end         = []
  identAll (id-stop _)    = []
  identAll (id-more p ir) = p ∷ identAll ir

  digitsAll : ∀ {cs ds r} → Digits cs ds r → All (λ x → isDigit x ≡ true) ds
  digitsAll dg-end         = []
  digitsAll (dg-stop _)    = []
  digitsAll (dg-more p dg) = p ∷ digitsAll dg

  -- The value of digits after `a` is below `(a + 1) * 10 ^ (their number)`.
  below : ∀ a ds → All (λ x → isDigit x ≡ true) ds → digitsFrom a ds < suc a * 10 ^ length ds
  below a []       []       = subst (a <_) (sym (*-identityʳ (suc a))) (n<1+n a)
  below a (c ∷ cs) (p ∷ ps) =
    <-≤-trans (below (a * 10 + (Ch.toℕ c ∸ Ch.toℕ '0')) cs ps)
      (≤-trans (*-monoˡ-≤ (10 ^ length cs) step)
        (≤-reflexive (*-assoc (suc a) 10 (10 ^ length cs))))
    where
      step : suc (a * 10 + (Ch.toℕ c ∸ Ch.toℕ '0')) ≤ suc a * 10
      step = subst (_≤ 10 + a * 10) (cong suc (+-comm (Ch.toℕ c ∸ Ch.toℕ '0') (a * 10)))
               (+-mono-≤ (isDigit-value c p) (≤-refl {a * 10}))

  fraction-ok : ∀ {r f r′} → Fraction r f r′ → ∃[ l ] (length f ≡ suc l × digitsToNat f < 10 ^ suc l)
  fraction-ok (fraction {d} {ds = ds} p dg) =
    length ds , refl , subst (digitsToNat (d ∷ ds) <_) (+-comm (10 ^ suc (length ds)) 0)
                         (below 0 (d ∷ ds) (p ∷ digitsAll dg))

  float-ok : ∀ i {r f r′} → Fraction r f r′ → Printable (TFloat i (digitsToNat f) (length f))
  float-ok i fr with fraction-ok fr
  ... | l , eq , f< rewrite eq = p-float f<

-- | Every token of a lexed text is printable, or a line end, the end, a string.
lexed-ok : ∀ {cs ts} → LexesChars cs ts → All LexOK ts
lexed-ok lex-eof = inj₂ o-eof ∷ []
lexed-ok (lex-space l) = lexed-ok l
lexed-ok (lex-tab l) = lexed-ok l
lexed-ok (lex-cr l) = lexed-ok l
lexed-ok (lex-nl-cont _ _ l) = lexed-ok l
lexed-ok (lex-nl _ _ l) = inj₂ o-nl ∷ lexed-ok l
lexed-ok (lex-lparen l) = inj₁ (p-sym s-lparen) ∷ lexed-ok l
lexed-ok (lex-rparen l) = inj₁ (p-sym s-rparen) ∷ lexed-ok l
lexed-ok (lex-rbrace l) = inj₁ (p-sym s-rbrace) ∷ lexed-ok l
lexed-ok (lex-colon l) = inj₁ (p-sym s-colon) ∷ lexed-ok l
lexed-ok (lex-lambda l) = inj₁ (p-sym s-lambda) ∷ lexed-ok l
lexed-ok (lex-comma l) = inj₁ (p-sym s-comma) ∷ lexed-ok l
lexed-ok (lex-semi l) = inj₁ (p-sym s-semicolon) ∷ lexed-ok l
lexed-ok (lex-at l) = inj₁ (p-sym s-at) ∷ lexed-ok l
lexed-ok (lex-pipe l) = inj₁ (p-sym s-pipe) ∷ lexed-ok l
lexed-ok (lex-plus l) = inj₁ (p-sym s-plus) ∷ lexed-ok l
lexed-ok (lex-star l) = inj₁ (p-sym s-star) ∷ lexed-ok l
lexed-ok (lex-slash l) = inj₁ (p-sym s-slash) ∷ lexed-ok l
lexed-ok (lex-pct l) = inj₁ (p-sym s-percent) ∷ lexed-ok l
lexed-ok (lex-amp l) = inj₁ (p-sym s-ampersand) ∷ lexed-ok l
lexed-ok (lex-dot l) = inj₁ (p-sym s-dot) ∷ lexed-ok l
lexed-ok (lex-arrow l) = inj₁ (p-sym s-arrow) ∷ lexed-ok l
lexed-ok (lex-caret1 l) = inj₁ (p-sym s-caret1) ∷ lexed-ok l
lexed-ok (lex-caret0 l) = inj₁ (p-sym s-caret0) ∷ lexed-ok l
lexed-ok (lex-caretw l) = inj₁ (p-sym s-caretw) ∷ lexed-ok l
lexed-ok (lex-le l) = inj₁ (p-sym s-le) ∷ lexed-ok l
lexed-ok (lex-ge l) = inj₁ (p-sym s-ge) ∷ lexed-ok l
lexed-ok (lex-eqeq l) = inj₁ (p-sym s-eqeq) ∷ lexed-ok l
lexed-ok (lex-neq l) = inj₁ (p-sym s-neq) ∷ lexed-ok l
lexed-ok (lex-caret _ _ _ l) = lexed-ok l
lexed-ok (lex-comment _ l) = lexed-ok l
lexed-ok (lex-minus _ _ l) = inj₁ (p-sym s-minus) ∷ lexed-ok l
lexed-ok (lex-block _ l) = lexed-ok l
lexed-ok (lex-lbrace _ l) = inj₁ (p-sym s-lbrace) ∷ lexed-ok l
lexed-ok (lex-lt _ l) = inj₁ (p-sym s-lt) ∷ lexed-ok l
lexed-ok (lex-gt _ l) = inj₁ (p-sym s-gt) ∷ lexed-ok l
lexed-ok (lex-equal _ l) = inj₁ (p-sym s-equals) ∷ lexed-ok l
lexed-ok (lex-bang _ l) = inj₁ (p-sym s-bang) ∷ lexed-ok l
lexed-ok (lex-string _ l) = inj₂ o-str ∷ lexed-ok l
lexed-ok (lex-string-end _) = []
lexed-ok (lex-int _ _ _ l) = inj₁ p-int ∷ lexed-ok l
lexed-ok (lex-float {c} {ds = ds} _ _ fr l) = inj₁ (float-ok (digitsToNat (c ∷ ds)) fr) ∷ lexed-ok l
lexed-ok (lex-ident {c} {i = i} ¬s d st ir l) = inj₁ (p-word (toList∘fromList (c ∷ i)) ¬s d st (identAll ir)) ∷ lexed-ok l
lexed-ok (lex-skip _ _ _ l) = lexed-ok l
