-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Format.Proof.ExprBase — what the expression proof stands on (plan
-- 0.124 step 4.2): well-formed expressions, what does not continue an
-- expression at each level, and the printer's decisions read back.
--
-- Generated in part (the cases per constructor) by
-- `scripts/gen-format-expr.py`: edit the generator, not this file.
------------------------------------------------------------------------

module Once.Format.Proof.ExprBase where

open import Data.Bool using (Bool; true; false; T; _∧_; _∨_; if_then_else_)
open import Data.Char using (Char)
import Data.Char as Ch
import Data.Char.Properties as ChP
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
import Data.Nat.Properties as ℕP
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃-syntax)
open import Data.String using (String; toList; _==_)
import Data.String.Properties as StrP
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst)
open import Relation.Nullary using (¬_; does; yes; no)
open import Relation.Nullary.Decidable using (toWitness)

open import Once.Spec.Surface.Lexing using (Token; TWord; TInt; TFloat; TLParen; TRParen; TComma; TColon; TSemicolon;
  TRBrace; TDot; TAt; TNewline; isIdentStart; TLambda; TPlus; TMinus; TStar; TSlash; TPercent; TLt; TGt; TPipe;
  TAmpersand)
open import Once.Spec.Surface.Syntax using (Expr; RVar; RQualified; RResolved; RApp; RLam; RLet; RPair; RDestruct;
  RUnit; RInt; RFloat; RAnnot; RBinOp; RNeg)
open import Once.Spec.Surface.Grammar using (Starts; starts; ArgStart; as-paren; as-lambda; as-int; as-float; as-word;
  QualSuffix; qual-suffix; Reserved; r-in; r-of; r-let; r-destruct; r-Left; r-Right; MulToken; AddToken;
  CompareToken; OpChar; oc-dot; oc-plus; oc-minus; oc-star; oc-slash; oc-pct; oc-lt; oc-gt; oc-pipe; oc-amp; oc-at)
open import Once.Format.Print using (isCompose; headOf; opToken; isOpChar; allOp; isOperator)
open import Once.Format.Proof.TypeAlgs using (GroundOK)

------------------------------------------------------------------------
-- Well-formed expressions
------------------------------------------------------------------------

-- | An operator name: its characters are operator characters.
OpName : String → Set
OpName x = ∃[ c ] ∃[ cs ] (toList x ≡ c ∷ cs × All (λ d → ∃[ t ] OpChar t d) (c ∷ cs))

-- | A name: an operator, or a word that is not reserved and starts as an
-- identifier does.
NameOK : String → Set
NameOK x = OpName x ⊎ (¬ Reserved x × ∃[ c ] ∃[ cs ] (toList x ≡ c ∷ cs × isIdentStart c ≡ true))

WF : Expr → Set
WF (RVar x)                = NameOK x
WF (RQualified x a)        = ¬ Reserved x
WF (RResolved _)           = ⊥
WF (RApp f a)              = WF f × WF a
WF (RLam x e)              = WF e
WF (RLet x v b)            = WF v × WF b
WF (RPair a b)             = WF a × WF b
WF (RDestruct s x el y er) = WF s × WF el × WF er
WF RUnit                   = ⊤
WF (RInt _)                = ⊤
WF (RFloat _ _ _)          = ⊤
WF (RAnnot e T)            = WF e × GroundOK T
WF (RBinOp op a b)         = WF a × WF b
WF (RNeg e)                = WF e

------------------------------------------------------------------------
-- What does not continue an expression
------------------------------------------------------------------------

NoQual AppDone CompDone : List Token → Set
NoQual r   = ¬ QualSuffix r
AppDone r  = ¬ ArgStart r
CompDone r = ¬ Starts r TDot

MulDone AddDone CmpDone : List Token → Set
MulDone r = ∀ {t op} → Starts r t → ¬ MulToken t op
AddDone r = ∀ {t op} → Starts r t → ¬ AddToken t op
CmpDone r = ∀ {t op} → Starts r t → ¬ CompareToken t op

-- | Nothing of an expression follows.
record Stops (r : List Token) : Set where
  constructor stops
  field
    qual : NoQual r
    app  : AppDone r
    mul  : MulDone r
    add  : AddDone r
    cmp  : CmpDone r
    comp : CompDone r

-- `)`, `,`, `:`, `;`, `}`, a line end, `in`, `of` stop an expression.
stops-rparen : ∀ {r} → Stops (TRParen ∷ r)
stops-rparen = stops (λ ()) (λ ()) (λ { starts () }) (λ { starts () }) (λ { starts () }) (λ ())
stops-comma : ∀ {r} → Stops (TComma ∷ r)
stops-comma = stops (λ ()) (λ ()) (λ { starts () }) (λ { starts () }) (λ { starts () }) (λ ())
stops-colon : ∀ {r} → Stops (TColon ∷ r)
stops-colon = stops (λ ()) (λ ()) (λ { starts () }) (λ { starts () }) (λ { starts () }) (λ ())
stops-semi : ∀ {r} → Stops (TSemicolon ∷ r)
stops-semi = stops (λ ()) (λ ()) (λ { starts () }) (λ { starts () }) (λ { starts () }) (λ ())
stops-rbrace : ∀ {r} → Stops (TRBrace ∷ r)
stops-rbrace = stops (λ ()) (λ ()) (λ { starts () }) (λ { starts () }) (λ { starts () }) (λ ())
stops-newline : ∀ {r} → Stops (TNewline ∷ r)
stops-newline = stops (λ ()) (λ ()) (λ { starts () }) (λ { starts () }) (λ { starts () }) (λ ())

private
  reserved-word : ∀ {w r} → Reserved w → Stops (TWord w ∷ r)
  reserved-word rw = stops (λ ()) (λ { (as-word ¬r) → ¬r rw }) (λ { starts () }) (λ { starts () }) (λ { starts () }) (λ ())

stops-in : ∀ {r} → Stops (TWord "in" ∷ r)
stops-in = reserved-word r-in
stops-of : ∀ {r} → Stops (TWord "of" ∷ r)
stops-of = reserved-word r-of

------------------------------------------------------------------------
-- The printer's decisions
------------------------------------------------------------------------

private
  ==-true : ∀ {x y} → (x == y) ≡ true → x ≡ y
  ==-true {x} {y} eq with x Data.String.≟ y
  ... | yes p = p
  ==-true {x} {y} () | no _

-- | `compose g` at the head: the application is a composition.
compose-true : ∀ f → isCompose (headOf f) ≡ true → ∃[ g ] f ≡ RApp (RVar "compose") g
compose-true (RVar x) ()
compose-true (RQualified x a) ()
compose-true (RResolved n) ()
compose-true (RApp (RVar x) g) eq = g , cong (λ y → RApp (RVar y) g) (==-true eq)
compose-true (RApp (RQualified cx ca) g) ()
compose-true (RApp (RResolved cn) g) ()
compose-true (RApp (RApp cf ca) g) ()
compose-true (RApp (RLam cx ce) g) ()
compose-true (RApp (RLet cx cv cb) g) ()
compose-true (RApp (RPair ca cb) g) ()
compose-true (RApp (RDestruct cs cx cel cy cer) g) ()
compose-true (RApp RUnit g) ()
compose-true (RApp (RInt cz) g) ()
compose-true (RApp (RFloat ci cf cl) g) ()
compose-true (RApp (RAnnot ce cT) g) ()
compose-true (RApp (RBinOp cop ca cb) g) ()
compose-true (RApp (RNeg ce) g) ()
compose-true (RLam x e) ()
compose-true (RLet x v b) ()
compose-true (RPair a b) ()
compose-true (RDestruct s x el y er) ()
compose-true RUnit ()
compose-true (RInt z) ()
compose-true (RFloat i f l) ()
compose-true (RAnnot e T) ()
compose-true (RBinOp op a b) ()
compose-true (RNeg e) ()

private
  ≟-true : ∀ {c d} → does (c Ch.≟ d) ≡ true → c ≡ d
  ≟-true {c} {d} eq = ChP.toℕ-injective c d (ℕP.≡ᵇ⇒≡ (Ch.toℕ c) (Ch.toℕ d) (subst T (sym eq) tt))

  start-not : ∀ {c d} → does (c Ch.≟ d) ≡ true → isIdentStart c ≡ true → isIdentStart d ≡ false → ⊥
  start-not {c} {d} eq st sd with ≟-true {c} {d} eq
  ... | refl with () ← trans (sym st) sd

-- | A character that starts an identifier is no operator character.
ident-not-op : ∀ c → isIdentStart c ≡ true → opToken c ≡ nothing
ident-not-op c st with does (c Ch.≟ '.') in e0
ident-not-op c st | true  = ⊥-elim (start-not {c} {'.'} e0 st refl)
ident-not-op c st | false with does (c Ch.≟ '+') in e1
ident-not-op c st | false | true  = ⊥-elim (start-not {c} {'+'} e1 st refl)
ident-not-op c st | false | false with does (c Ch.≟ '-') in e2
ident-not-op c st | false | false | true  = ⊥-elim (start-not {c} {'-'} e2 st refl)
ident-not-op c st | false | false | false with does (c Ch.≟ '*') in e3
ident-not-op c st | false | false | false | true  = ⊥-elim (start-not {c} {'*'} e3 st refl)
ident-not-op c st | false | false | false | false with does (c Ch.≟ '/') in e4
ident-not-op c st | false | false | false | false | true  = ⊥-elim (start-not {c} {'/'} e4 st refl)
ident-not-op c st | false | false | false | false | false with does (c Ch.≟ '%') in e5
ident-not-op c st | false | false | false | false | false | true  = ⊥-elim (start-not {c} {'%'} e5 st refl)
ident-not-op c st | false | false | false | false | false | false with does (c Ch.≟ '<') in e6
ident-not-op c st | false | false | false | false | false | false | true  = ⊥-elim (start-not {c} {'<'} e6 st refl)
ident-not-op c st | false | false | false | false | false | false | false with does (c Ch.≟ '>') in e7
ident-not-op c st | false | false | false | false | false | false | false | true  = ⊥-elim (start-not {c} {'>'} e7 st refl)
ident-not-op c st | false | false | false | false | false | false | false | false with does (c Ch.≟ '|') in e8
ident-not-op c st | false | false | false | false | false | false | false | false | true  = ⊥-elim (start-not {c} {'|'} e8 st refl)
ident-not-op c st | false | false | false | false | false | false | false | false | false with does (c Ch.≟ '&') in e9
ident-not-op c st | false | false | false | false | false | false | false | false | false | true  = ⊥-elim (start-not {c} {'&'} e9 st refl)
ident-not-op c st | false | false | false | false | false | false | false | false | false | false with does (c Ch.≟ '@') in e10
ident-not-op c st | false | false | false | false | false | false | false | false | false | false | true  = ⊥-elim (start-not {c} {'@'} e10 st refl)
ident-not-op c st | false | false | false | false | false | false | false | false | false | false | false = refl

private
  op-isOp : ∀ {t d} → OpChar t d → isOpChar d ≡ true
  op-isOp oc-dot = refl
  op-isOp oc-plus = refl
  op-isOp oc-minus = refl
  op-isOp oc-star = refl
  op-isOp oc-slash = refl
  op-isOp oc-pct = refl
  op-isOp oc-lt = refl
  op-isOp oc-gt = refl
  op-isOp oc-pipe = refl
  op-isOp oc-amp = refl
  op-isOp oc-at = refl

  allOp-true : ∀ c cs → All (λ d → ∃[ t ] OpChar t d) (c ∷ cs) → allOp (c ∷ cs) ≡ true
  allOp-true c []       ((_ , o) ∷ []) = op-isOp o
  allOp-true c (d ∷ ds) ((_ , o) ∷ os) rewrite op-isOp o = allOp-true d ds os

  isOpChar-nothing : ∀ {c} → opToken c ≡ nothing → isOpChar c ≡ false
  isOpChar-nothing {c} eq with opToken c
  isOpChar-nothing {c} refl | nothing = refl

-- | The printer writes an operator name as an operator…
op-isOperator : ∀ x → OpName x → isOperator x ≡ true
op-isOperator x (c , cs , eq , os) rewrite eq = allOp-true c cs os

-- | …and a word as a word.
word-notOperator : ∀ x c cs → toList x ≡ c ∷ cs → isIdentStart c ≡ true → isOperator x ≡ false
word-notOperator x c cs eq st = trans (cong allOp eq) (allOp-start c cs (isOpChar-nothing {c} (ident-not-op c st)))
  where
    allOp-start : ∀ c cs → isOpChar c ≡ false → allOp (c ∷ cs) ≡ false
    allOp-start c []       e = e
    allOp-start c (d ∷ ds) e rewrite e = refl

-- | An operator character's token.
op-token : ∀ {t d} → OpChar t d → opToken d ≡ just t
op-token oc-dot = refl
op-token oc-plus = refl
op-token oc-minus = refl
op-token oc-star = refl
op-token oc-slash = refl
op-token oc-pct = refl
op-token oc-lt = refl
op-token oc-gt = refl
op-token oc-pipe = refl
op-token oc-amp = refl
op-token oc-at = refl
