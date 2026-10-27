# Generates formal/Once/Format/Proof/LexOK.agda (plan 0.124 step 4).
# Run from anywhere: python3 formal/scripts/gen-format-lexok.py
import os
PROOF=os.path.join(os.path.dirname(os.path.abspath(__file__)),'..','Once','Format','Proof')
SYM1={'lex-lparen':'s-lparen','lex-rparen':'s-rparen','lex-rbrace':'s-rbrace','lex-colon':'s-colon','lex-lambda':'s-lambda',
'lex-comma':'s-comma','lex-semi':'s-semicolon','lex-at':'s-at','lex-pipe':'s-pipe','lex-plus':'s-plus','lex-star':'s-star',
'lex-slash':'s-slash','lex-pct':'s-percent','lex-amp':'s-ampersand','lex-dot':'s-dot','lex-arrow':'s-arrow',
'lex-caret1':'s-caret1','lex-caret0':'s-caret0','lex-caretw':'s-caretw','lex-le':'s-le','lex-ge':'s-ge','lex-eqeq':'s-eqeq','lex-neq':'s-neq'}
SYM2={'lex-minus':'s-minus','lex-lbrace':'s-lbrace','lex-lt':'s-lt','lex-gt':'s-gt','lex-equal':'s-equals','lex-bang':'s-bang'}  # one premise before l
SYM3={'lex-minus':2}
o=[]; w=o.append
w(r'''-- SPDX-License-Identifier: AGPL-3.0-or-later
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
lexed-ok : ∀ {cs ts} → LexesChars cs ts → All LexOK ts''')
cases=[]
cases.append("lexed-ok lex-eof = inj₂ o-eof ∷ []")
for n in ['lex-space','lex-tab','lex-cr']: cases.append(f"lexed-ok ({n} l) = lexed-ok l")
cases.append("lexed-ok (lex-nl-cont _ _ l) = lexed-ok l")
cases.append("lexed-ok (lex-nl _ _ l) = inj₂ o-nl ∷ lexed-ok l")
for n,s in SYM1.items():
    cases.append(f"lexed-ok ({n} l) = inj₁ (p-sym {s}) ∷ lexed-ok l")
cases.append("lexed-ok (lex-comment _ l) = lexed-ok l")
cases.append("lexed-ok (lex-minus _ _ l) = inj₁ (p-sym s-minus) ∷ lexed-ok l")
cases.append("lexed-ok (lex-block _ l) = lexed-ok l")
for n,s in SYM2.items():
    if n=='lex-minus': continue
    cases.append(f"lexed-ok ({n} _ l) = inj₁ (p-sym {s}) ∷ lexed-ok l")
cases.append("lexed-ok (lex-string _ l) = inj₂ o-str ∷ lexed-ok l")
cases.append("lexed-ok (lex-int _ _ _ l) = inj₁ p-int ∷ lexed-ok l")
cases.append("lexed-ok (lex-float {c} {ds = ds} _ _ fr l) = inj₁ (float-ok (digitsToNat (c ∷ ds)) fr) ∷ lexed-ok l")
cases.append("lexed-ok (lex-ident {c} {i = i} ¬s d st ir l) = inj₁ (p-word (toList∘fromList (c ∷ i)) ¬s d st (identAll ir)) ∷ lexed-ok l")
for c in cases: w(c)
OUT=os.path.join(PROOF,'LexOK.agda')
open(OUT,'w').write('\n'.join(o)+'\n')
