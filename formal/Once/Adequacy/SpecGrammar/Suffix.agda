-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.SpecGrammar.Suffix — what a Spec parse leaves is a suffix
-- of what it read (plan 0.121 R13).
--
-- Every rule of `Once.Spec.Surface.Grammar` reads tokens off the front, so a
-- property of every token of a lexed text holds of every rest a parse
-- leaves (`All-⊒`).
------------------------------------------------------------------------

module Once.Adequacy.SpecGrammar.Suffix where

open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)

open import Once.Spec.Surface.Lexing using (Token; TWord; TColon; TEquals; TLParen; TRParen; TArrow; TDot; TAt)
open import Once.Spec.Surface.Grammar as G

------------------------------------------------------------------------
-- Suffixes
------------------------------------------------------------------------

infix 4 _⊒_
data _⊒_ : List Token → List Token → Set where
  ⊒-refl : ∀ {ts} → ts ⊒ ts
  ⊒-step : ∀ {t ts r} → ts ⊒ r → (t ∷ ts) ⊒ r

infixr 5 _⨾_
_⨾_ : ∀ {a b c} → a ⊒ b → b ⊒ c → a ⊒ c
⊒-refl   ⨾ q = q
⊒-step p ⨾ q = ⊒-step (p ⨾ q)

private
  s : ∀ {t ts r} → ts ⊒ r → (t ∷ ts) ⊒ r
  s = ⊒-step

  -- a rest that still starts with a token the rule then reads
  drop : ∀ {a t b} → a ⊒ (t ∷ b) → a ⊒ b
  drop p = p ⨾ s ⊒-refl

All-⊒ : ∀ {P : Token → Set} {ts r} → All P ts → ts ⊒ r → All P r
All-⊒ a          ⊒-refl     = a
All-⊒ (_ ∷ a)    (⊒-step p) = All-⊒ a p

------------------------------------------------------------------------
-- Types, over any algebra whose extra atoms read off the front
------------------------------------------------------------------------

module TypesSuffix {R RF : Set} {alg : TypeAlg R RF}
  (extra : ∀ {ts A r} → TypeAlg.Extra alg ts A r → ts ⊒ r) where
  open Types alg

  atom   : ∀ {ts A r} → ParsesAtom ts A r → ts ⊒ r
  prodT  : ∀ {l ts T r} → ParsesProdTail l ts T r → ts ⊒ r
  sumT   : ∀ {l ts T r} → ParsesSumTail l ts T r → ts ⊒ r
  prod′  : ∀ {ts A r} → ParsesProd ts A r → ts ⊒ r
  sum′   : ∀ {ts A r} → ParsesSum ts A r → ts ⊒ r
  type′  : ∀ {ts A r} → ParsesType ts A r → ts ⊒ r
  arrowT : ∀ {l ts T r} → ParsesArrowTail l ts T r → ts ⊒ r
  fatom  : ∀ {ts F r} → ParsesFunAtom ts F r → ts ⊒ r
  fprod′ : ∀ {ts F r} → ParsesFunProd ts F r → ts ⊒ r
  fprodT : ∀ {l ts F r} → ParsesFunProdTail l ts F r → ts ⊒ r
  fsum′  : ∀ {ts F r} → ParsesFunSum ts F r → ts ⊒ r
  fsumT  : ∀ {l ts F r} → ParsesFunSumTail l ts F r → ts ⊒ r

  atom a-unit         = s ⊒-refl
  atom a-void         = s ⊒-refl
  atom a-int          = s ⊒-refl
  atom a-float        = s ⊒-refl
  atom (a-eff p q)    = s (atom p ⨾ atom q)
  atom (a-act p q)    = s (atom p ⨾ atom q)
  atom (a-mu p)       = s (fsum′ p)
  atom (a-nu p)       = s (fsum′ p)
  atom (a-nu-act p)   = s (s (s (drop (fsum′ p))))
  atom (a-extra x)    = extra x
  atom (a-paren p)    = s (drop (type′ p))

  prodT (prod-done _)   = ⊒-refl
  prodT (prod-star p q) = s (atom p ⨾ prodT q)

  sumT (sum-done _)   = ⊒-refl
  sumT (sum-plus p q) = s (prod′ p ⨾ sumT q)

  prod′ (prod p q) = atom p ⨾ prodT q
  sum′ (sum p q)   = prod′ p ⨾ sumT q
  type′ (type p q) = sum′ p ⨾ arrowT q

  arrowT (arrow-done _ _ _ _) = ⊒-refl
  arrowT (arrow-grade _ p)    = s (s (type′ p))
  arrowT (arrow p)            = s (type′ p)

  fatom f-id        = s ⊒-refl
  fatom (f-k p)     = s (atom p)
  fatom (f-paren p) = s (drop (fsum′ p))

  fprod′ (fprod p q) = fatom p ⨾ fprodT q
  fprodT (fprod-done _)   = ⊒-refl
  fprodT (fprod-star p q) = s (fatom p ⨾ fprodT q)

  fsum′ (fsum p q) = fprod′ p ⨾ fsumT q
  fsumT (fsum-done _)   = ⊒-refl
  fsumT (fsum-plus p q) = s (fprod′ p ⨾ fsumT q)

private
  tvar-⊒ : ∀ {ts A r} → TypeVar ts A r → ts ⊒ r
  tvar-⊒ (tvar _) = s ⊒-refl

  none-⊒ : ∀ {R : Set} {ts} {A : R} {r} → NoExtra ts A r → ts ⊒ r
  none-⊒ ()

sigType : ∀ {ts A r} → SigType.ParsesType ts A r → ts ⊒ r
sigType = TypesSuffix.type′ tvar-⊒

aliasType : ∀ {ts A r} → AliasType.ParsesType ts A r → ts ⊒ r
aliasType = TypesSuffix.type′ none-⊒

annotType : ∀ {ts A r} → Annot.ParsesType ts A r → ts ⊒ r
annotType = TypesSuffix.type′ none-⊒

------------------------------------------------------------------------
-- Expressions
------------------------------------------------------------------------

opchars : ∀ {ts cs x r} → ParsesOpChars ts cs x r → ts ⊒ r
opchars op-close       = s ⊒-refl
opchars (op-char _ p)  = s (opchars p)

expr′   : ∀ {ts e r} → ParsesExpr ts e r → ts ⊒ r
compT   : ∀ {l ts e r} → ParsesCompTail l ts e r → ts ⊒ r
cmp′    : ∀ {ts e r} → ParsesCmp ts e r → ts ⊒ r
add′    : ∀ {ts e r} → ParsesAdd ts e r → ts ⊒ r
addT    : ∀ {l ts e r} → ParsesAddTail l ts e r → ts ⊒ r
mul′    : ∀ {ts e r} → ParsesMul ts e r → ts ⊒ r
mulT    : ∀ {l ts e r} → ParsesMulTail l ts e r → ts ⊒ r
unary′  : ∀ {ts e r} → ParsesUnary ts e r → ts ⊒ r
app′    : ∀ {ts e r} → ParsesApp ts e r → ts ⊒ r
appT    : ∀ {l ts e r} → ParsesAppTail l ts e r → ts ⊒ r
atomE   : ∀ {ts e r} → ParsesAtomExpr ts e r → ts ⊒ r
lam′    : ∀ {ts e r} → ParsesLamParams ts e r → ts ⊒ r
parenC  : ∀ {l ts e r} → ParsesParenCont l ts e r → ts ⊒ r

expr′ (expr p q) = cmp′ p ⨾ compT q
compT (comp-done _)  = ⊒-refl
compT (comp-dot p q) = s (cmp′ p ⨾ compT q)

cmp′ (cmp-none p _) = add′ p
cmp′ (cmp _ p q)    = drop (add′ p) ⨾ add′ q

add′ (add p q) = mul′ p ⨾ addT q
addT (add-done _)     = ⊒-refl
addT (add-op _ p q)   = s (mul′ p ⨾ addT q)

mul′ (mul p q) = unary′ p ⨾ mulT q
mulT (mul-done _)     = ⊒-refl
mulT (mul-op _ p q)   = s (unary′ p ⨾ mulT q)

unary′ (neg p)   = s (unary′ p)
unary′ (unary p) = app′ p

app′ (app p q) = atomE p ⨾ appT q
appT (app-done _)      = ⊒-refl
appT (app-arg _ p q)   = atomE p ⨾ appT q

atomE atom-unit             = s (s ⊒-refl)
atomE atom-int              = s ⊒-refl
atomE atom-float            = s ⊒-refl
atomE (atom-var _ _)        = s ⊒-refl
atomE (atom-qual _)         = s (s (s ⊒-refl))
atomE (atom-paren p q)      = s (expr′ p ⨾ parenC q)
atomE (atom-op p)           = s (opchars p)
atomE (atom-lambda p)       = s (lam′ p)
atomE (atom-let p q)        = s (s (s (drop (expr′ p) ⨾ expr′ q)))
atomE (atom-destruct p q r) =
  s (drop (drop (drop (drop (drop (expr′ p)))))
     ⨾ drop (drop (drop (drop (expr′ q))))
     ⨾ drop (expr′ r))

lam′ (lam-body p) = s (expr′ p)
lam′ (lam-arg p)  = s (lam′ p)

parenC paren-close      = s ⊒-refl
parenC (paren-pair p)   = s (drop (expr′ p))
parenC (paren-annot p)  = s (drop (annotType p))

------------------------------------------------------------------------
-- Declarations
------------------------------------------------------------------------

params : ∀ {ts ps r} → ParsesParams ts ps r → ts ⊒ r
params (params-eq _)     = s ⊒-refl
params (params-cons _ p) = s (params p)
params (params-stop _ _) = ⊒-refl
params (params-none _)   = ⊒-refl

fundef′ : ∀ {x ts d r} → ParsesFunDef x ts d r → ts ⊒ r
fundef′ (fundef p q) = drop (params p) ⨾ expr′ q

path : ∀ {ts p r} → ParsesModulePath ts p r → ts ⊒ r
path (path-cons p)    = s (s (path p))
path (path-dotstop _) = s ⊒-refl
path (path-end _)     = s ⊒-refl

import′ : ∀ {ts d r} → ParsesImport ts d r → ts ⊒ r
import′ (import-as p)      = drop (drop (path p))
import′ (import-plain p _) = path p

alias : ∀ {x ps ts d r} → ParsesTypeAlias x ps ts d r → ts ⊒ r
alias (alias-eq p)    = s (aliasType p)
alias (alias-param p) = s (alias p)

opAfter : ∀ {x ts d r} → ParsesOpAfter x ts d r → ts ⊒ r
opAfter (op-sig p)   = s (sigType p)
opAfter (op-def _ p) = fundef′ p

decl : ∀ {ts d r} → ParsesDecl ts d r → ts ⊒ r
decl (decl-import p)      = s (import′ p)
decl (decl-alias p)       = s (s (alias p))
decl (decl-signature p)   = s (s (s (sigType p)))
decl (decl-typesig _ p _) = s (s (sigType p))
decl (decl-fundef _ _ p)  = s (fundef′ p)
decl (decl-op p q)        = s (opchars p ⨾ opAfter q)

skip : ∀ {ts r} → SkipNewlines ts r → ts ⊒ r
skip (skip-nl p)   = s (skip p)
skip (skip-done _) = ⊒-refl

decls : ∀ {ts ds r} → ParsesDecls ts ds r → ts ⊒ r
decls (decls-stop k _)    = skip k
decls (decls-cons k p ps) = skip k ⨾ (decl p ⨾ decls ps)
