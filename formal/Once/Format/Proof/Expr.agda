-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Format.Proof.Expr — a printed expression reads back (plan 0.124
-- step 4.2).
--
-- At each level of the grammar (`Spec.Surface.Grammar`, loosest first:
-- composition, comparison, `+`/`-`, `*`/`/`/`%`, prefix `-`, application,
-- atom) the tokens of an expression printed for that level parse there as
-- the expression, when what follows does not continue it. A chain (an
-- application's arguments, `+`, `*`, `.`) is read left to right, so its left
-- operand is read with what follows it (the tail forms). A lambda, `let` or
-- `destruct` reads as far as it can: bare only where nothing follows it
-- (`whole`).
--
-- Generated (the cases per constructor and operator) by
-- `scripts/gen-format-expr.py`: edit the generator, not this file.
------------------------------------------------------------------------

module Once.Format.Proof.Expr where

open import Data.Bool using (Bool; true; false; if_then_else_; not; _∧_; _∨_)
open import Data.Char using (Char)
import Data.Char as Ch
open import Relation.Nullary using (does)
open import Data.List using (List; []; _∷_; reverse; reverseAcc)
open import Data.List.Properties using (reverse-involutive)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃-syntax)
open import Data.String using (String; toList; fromList)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Relation.Nullary using (¬_)
open import Agda.Builtin.String.Properties using (primStringToListInjective)

open import Once.Postulates using (toList∘fromList)
open import Once.Spec.Surface.Lexing using (Token; TWord; TInt; TFloat; TLParen; TRParen; TComma; TColon; TSemicolon;
  TLBrace; TRBrace; TDot; TAt; TLambda; TArrow; TEquals; TOpD)
open import Once.Adequacy.SpecTokNames
open import Once.Spec.Surface.Syntax using (Expr; RVar; RQualified; RResolved; RApp; RLam; RLet; RPair; RDestruct;
  RUnit; RInt; RFloat; RAnnot; RBinOp; RNeg)
open import Once.Surface.OpNames
import Once.Spec.Surface.Operator as Op
open import Once.Spec.Surface.Operator using (o+; o-; o*; o/; o<; o<=; o>; o>=; o==; o!=)
open import Once.Spec.Float.Value using (pos; neg)
import Data.Integer as ℤ
open import Once.Spec.Surface.Grammar
open import Once.Format.Doc using (toks)
open import Once.Format.Print
open import Once.Format.Proof.Tokens using (word-toks; anchor-toks)
open import Once.Format.Proof.ExprBase
open import Once.Format.Proof.TypeAlgs using (GroundOK; ground-id; ground-wf)
import Once.Format.Proof.TypeAlgs as TA

private
  E : ℕ → Expr → Trivia → ℕ → List Token → List Token
  E l e tv k r = toks (proj₁ (pex l false e tv k)) r

  -- From an atom, or an application, to any level, when nothing follows.
  atom→expr : ∀ {ts e r} → Stops r → ParsesAtomExpr ts e r → ParsesExpr ts e r
  atom→expr (stops q a m d c o) p =
    expr (cmp-none (add (mul (unary (app p (app-done a))) (mul-done m)) (add-done d)) c) (comp-done o)

  app→expr : ∀ {ts e r} → Stops r → ParsesApp ts e r → ParsesExpr ts e r
  app→expr (stops q a m d c o) p = expr (cmp-none (add (mul (unary p) (mul-done m)) (add-done d)) c) (comp-done o)

  argNoQual : ∀ {ts} → ArgStart ts → NoQual ts
  argNoQual as-paren ()
  argNoQual as-lambda ()
  argNoQual as-int ()
  argNoQual as-float ()
  argNoQual (as-word _) ()

  -- The blank between `-` and a `-` it would make a comment of.
  if-space : ∀ b r → toks (if b then Once.Format.Doc.sp else Once.Format.Doc.empty) r ≡ r
  if-space true  r = refl
  if-space false r = refl

  -- What the dot of a composition is followed by stops the left operand.
  dot-stops : ∀ {r} → NoQual (TDot ∷ r) × AppDone (TDot ∷ r) × MulDone (TDot ∷ r) × AddDone (TDot ∷ r) × CmpDone (TDot ∷ r)
  dot-stops = (λ ()) , (λ ()) , (λ { starts () }) , (λ { starts () }) , (λ { starts () })

  fromList∘toList : ∀ s → fromList (toList s) ≡ s
  fromList∘toList s = primStringToListInjective _ _ (toList∘fromList (toList s))

  -- An operator's characters, up to `)`: a glyph and `.` as its IEEE form.
  opchars : ∀ c cs acc tv k r → All (λ d → ∃[ t ] OpChar t d) (c ∷ cs)
          → ParsesOpChars (toks (proj₁ (opToks (c ∷ cs) tv k)) (TRParen ∷ r)) acc
                          (fromList (reverse (reverseAcc acc (c ∷ cs)))) r
  opcharsPair : ∀ c d ds acc tv k r → (∃[ t ] OpChar t c) → All (λ d → ∃[ t ] OpChar t d) (d ∷ ds)
              → ∀ m → dotToken c d ≡ m
              → ParsesOpChars (toks (proj₁ (opPair c d (d ∷ ds) ds m tv k)) (TRParen ∷ r)) acc
                              (fromList (reverse (reverseAcc acc (c ∷ d ∷ ds)))) r
  opchars c []       acc tv k r ((t , o) ∷ []) rewrite op-token o = op-char o op-close
  opchars c (d ∷ ds) acc tv k r (o₁ ∷ os) = opcharsPair c d ds acc tv k r o₁ os (dotToken c d) refl

  opcharsPair c d ds acc tv k r o₁ os (just x) e with dot-token c d e
  opcharsPair c .'.' [] acc tv k r o₁ os (just .(TOpD dd)) e | dd , refl , refl , g = op-dotted g op-close
  opcharsPair c .'.' (e′ ∷ es) acc tv k r o₁ (_ ∷ os) (just .(TOpD dd)) e | dd , refl , refl , g =
    op-dotted g (opchars e′ es ('.' ∷ c ∷ acc) tv _ r os)
  opcharsPair c d ds acc tv k r (t , o) os nothing e rewrite op-token o =
    subst (λ ts → ParsesOpChars (t ∷ ts) acc _ r)
      (sym (if-space (does (c Ch.≟ '-') ∧ (does (d Ch.≟ '-') ∨ does (d Ch.≟ '>'))) (toks (proj₁ (opToks (d ∷ ds) tv k)) (TRParen ∷ r))))
      (op-char o (opchars d ds (c ∷ acc) tv _ r os))

-- | An operator name's characters, up to `)`.
opName-parses : ∀ x tv k r → OpName x → ParsesOpChars (toks (proj₁ (opToks (toList x) tv k)) (TRParen ∷ r)) [] x r
opName-parses x tv k r (c , cs , eq , os) =
  subst (λ s → ParsesOpChars (toks (proj₁ (opToks (toList x) tv k)) (TRParen ∷ r)) [] s r)
    (trans (cong fromList (reverse-involutive (c ∷ cs))) (trans (cong fromList (sym eq)) (fromList∘toList x)))
    (subst (λ cs′ → ParsesOpChars (toks (proj₁ (opToks cs′ tv k)) (TRParen ∷ r)) [] (fromList (reverse (reverse (c ∷ cs)))) r)
       (sym eq) (opchars c cs [] tv k r os))

private
  -- A name.
  nameAtom : ∀ x tv k r → NameOK x → NoQual r → ParsesAtomExpr (toks (proj₁ (name x tv k)) r) (RVar x) r
  nameAtom x tv k r (inj₁ op) nq rewrite op-isOperator x op = atom-op (opName-parses x tv k r op)
  nameAtom x tv k r (inj₂ (¬res , c , cs , eq , st)) nq rewrite word-notOperator x c cs eq st =
    subst (λ ts → ParsesAtomExpr ts (RVar x) r) (sym (word-toks x tv k r)) (atom-var ¬res nq)

  nameArg : ∀ x tv k r → NameOK x → ArgStart (toks (proj₁ (name x tv k)) r)
  nameArg x tv k r (inj₁ op) rewrite op-isOperator x op = as-paren
  nameArg x tv k r (inj₂ (¬res , c , cs , eq , st)) rewrite word-notOperator x c cs eq st =
    subst ArgStart (sym (word-toks x tv k r)) (as-word ¬res)


private
  argApp : ∀ f a b tv k r → isCompose (headOf f) ≡ b → ArgStart (toks (proj₁ (pcomp 6 b f a tv k)) r)
  argApp f a true tv k r eq with compose-true f eq
  ... | g , refl = as-paren
  argApp f a false tv k r eq = as-paren

-- | A printed atom starts an argument.
argSt : ∀ e tv k r → WF e → ArgStart (E 6 e tv k r)
argSt (RVar x) tv k r w = nameArg x tv k r w
argSt (RQualified x q) tv k r w = subst ArgStart (sym (word-toks x tv k _)) (as-word w)
argSt (RResolved n) tv k r ()
argSt (RApp f a) tv k r w = argApp f a (isCompose (headOf f)) tv k r refl
argSt (RLam x e) tv k r w = as-paren
argSt (RLet x v b) tv k r w = as-paren
argSt (RPair a b) tv k r w = as-paren
argSt (RDestruct s x el y er) tv k r w = as-paren
argSt RUnit tv k r w = as-paren
argSt (RInt (ℤ.+ n)) tv k r w = subst ArgStart (sym (anchor-toks (TInt (ℤ.+ n)) tv k r)) as-int
argSt (RInt ℤ.-[1+ n ]) tv k r w = as-paren
argSt (RFloat pos i fr l) tv k r w = subst ArgStart (sym (anchor-toks (TFloat i fr l) tv k r)) as-float
argSt (RFloat neg i fr l) tv k r w = as-paren
argSt (RAnnot e T) tv k r w = as-paren
argSt (RBinOp OpAdd a b) tv k r w = as-paren
argSt (RBinOp OpSub a b) tv k r w = as-paren
argSt (RBinOp OpMul a b) tv k r w = as-paren
argSt (RBinOp OpDiv a b) tv k r w = as-paren
argSt (RBinOp OpMod a b) tv k r w = as-paren
argSt (RBinOp OpLt a b) tv k r w = as-paren
argSt (RBinOp OpLe a b) tv k r w = as-paren
argSt (RBinOp OpGt a b) tv k r w = as-paren
argSt (RBinOp OpGe a b) tv k r w = as-paren
argSt (RBinOp OpEq a b) tv k r w = as-paren
argSt (RBinOp OpNe a b) tv k r w = as-paren
argSt (RBinOp (Op.dotted o+) a b) tv k r w = as-paren
argSt (RBinOp (Op.dotted o-) a b) tv k r w = as-paren
argSt (RBinOp (Op.dotted o*) a b) tv k r w = as-paren
argSt (RBinOp (Op.dotted o/) a b) tv k r w = as-paren
argSt (RBinOp (Op.dotted o<) a b) tv k r w = as-paren
argSt (RBinOp (Op.dotted o<=) a b) tv k r w = as-paren
argSt (RBinOp (Op.dotted o>) a b) tv k r w = as-paren
argSt (RBinOp (Op.dotted o>=) a b) tv k r w = as-paren
argSt (RBinOp (Op.dotted o==) a b) tv k r w = as-paren
argSt (RBinOp (Op.dotted o!=) a b) tv k r w = as-paren
argSt (RNeg e) tv k r w = as-paren

private
  -- A prefix-level reading in parentheses, as an atom.
  unary→atom : ∀ {ts e r} → ParsesUnary ts e (TRParen ∷ r) → ParsesAtomExpr (TLParen ∷ ts) e r
  unary→atom u = atom-paren (expr (cmp-none (add (mul u (mul-done (λ { starts () }))) (add-done (λ { starts () })))
                   (λ { starts () })) (comp-done (λ ()))) paren-close

  -- A negative literal, at the prefix level.
  negIntU : ∀ n tv k r → AppDone r → ParsesUnary (E 4 (RInt ℤ.-[1+ n ]) tv k r) (RInt ℤ.-[1+ n ]) r
  negIntU n tv k r ad =
    subst (λ ts → ParsesUnary (TMinus ∷ ts) (RInt ℤ.-[1+ n ]) r) (sym (anchor-toks (TInt (ℤ.+ suc n)) tv k r))
      (neg-lit nn-int (app-done ad))

  negFloatU : ∀ i fr l tv k r → AppDone r → ParsesUnary (E 4 (RFloat neg i fr l) tv k r) (RFloat neg i fr l) r
  negFloatU i fr l tv k r ad =
    subst (λ ts → ParsesUnary (TMinus ∷ ts) (RFloat neg i fr l) r) (sym (anchor-toks (TFloat i fr l) tv k r))
      (neg-lit nn-float (app-done ad))

  nameNoNum : ∀ x tv k r → NameOK x → ¬ NumeralStart (toks (proj₁ (name x tv k)) r)
  nameNoNum x tv k r (inj₁ op) rewrite op-isOperator x op = λ ()
  nameNoNum x tv k r (inj₂ (¬res , c , cs , eq , st)) rewrite word-notOperator x c cs eq st =
    subst (λ ts → ¬ NumeralStart ts) (sym (word-toks x tv k r)) (λ ())

  -- Printed at level 6, at the head of an application, or at level 4, `e`
  -- starts with a numeral only when `startsNum e` (so a `-` before it is a
  -- prefix `-`, not a negative literal's).
  noNum6 : ∀ e tv k r → WF e → startsNum e ≡ false → ¬ NumeralStart (E 6 e tv k r)
  noNumApp6 : ∀ f a b tv k r → isCompose (headOf f) ≡ b → ¬ NumeralStart (toks (proj₁ (pcomp 6 b f a tv k)) r)
  noNumSpine : ∀ f tv k r → WF f → startsNum f ≡ false → ¬ NumeralStart (toks (proj₁ (pspine f tv k)) r)
  noNumSpine′ : ∀ f a b tv k r → isCompose (headOf f) ≡ b → WF f → (not b ∧ startsNum f) ≡ false
              → ¬ NumeralStart (toks (proj₁ (pspine′ b f a tv k)) r)
  noNum4 : ∀ e tv k r → WF e → startsNum e ≡ false → ¬ NumeralStart (E 4 e tv k r)
  noNumApp4 : ∀ f a b tv k r → isCompose (headOf f) ≡ b → WF f → (not b ∧ startsNum f) ≡ false
            → ¬ NumeralStart (toks (proj₁ (pcomp 4 b f a tv k)) r)

  noNumApp6 f a true tv k r eq with compose-true f eq
  ... | g , refl = λ ()
  noNumApp6 f a false tv k r eq = λ ()

  noNumSpine′ f a true tv k r eq wf h with compose-true f eq
  ... | g , refl = λ ()
  noNumSpine′ f a false tv k r eq wf h = noNumSpine f tv k _ wf h

  noNumApp4 f a true tv k r eq wf h with compose-true f eq
  ... | g , refl = λ ()
  noNumApp4 f a false tv k r eq wf h = noNumSpine f tv k _ wf h

  noNumSpine (RApp f a) tv k r (wf , wa) h = noNumSpine′ f a (isCompose (headOf f)) tv k r refl wf h
  noNumSpine (RVar x) tv k r w h = noNum6 (RVar x) tv k r w h
  noNumSpine (RQualified x q) tv k r w h = noNum6 (RQualified x q) tv k r w h
  noNumSpine (RResolved n) tv k r () h
  noNumSpine (RLam x e) tv k r w h = noNum6 (RLam x e) tv k r w h
  noNumSpine (RLet x v b) tv k r w h = noNum6 (RLet x v b) tv k r w h
  noNumSpine (RPair a b) tv k r w h = noNum6 (RPair a b) tv k r w h
  noNumSpine (RDestruct s x el y er) tv k r w h = noNum6 (RDestruct s x el y er) tv k r w h
  noNumSpine RUnit tv k r w h = noNum6 RUnit tv k r w h
  noNumSpine (RInt (ℤ.+ n)) tv k r w h = noNum6 (RInt (ℤ.+ n)) tv k r w h
  noNumSpine (RInt ℤ.-[1+ n ]) tv k r w h = noNum6 (RInt ℤ.-[1+ n ]) tv k r w h
  noNumSpine (RFloat pos i fr l) tv k r w h = noNum6 (RFloat pos i fr l) tv k r w h
  noNumSpine (RFloat neg i fr l) tv k r w h = noNum6 (RFloat neg i fr l) tv k r w h
  noNumSpine (RAnnot e T) tv k r w h = noNum6 (RAnnot e T) tv k r w h
  noNumSpine (RBinOp op a b) tv k r w h = noNum6 (RBinOp op a b) tv k r w h
  noNumSpine (RNeg e) tv k r w h = noNum6 (RNeg e) tv k r w h
  noNum6 (RVar x) tv k r w h = nameNoNum x tv k r w
  noNum6 (RQualified x q) tv k r w h = subst (λ ts → ¬ NumeralStart ts) (sym (word-toks x tv k _)) (λ ())
  noNum6 (RResolved n) tv k r () h
  noNum6 (RApp f a) tv k r w h = noNumApp6 f a (isCompose (headOf f)) tv k r refl
  noNum6 (RLam x e) tv k r w h = λ ()
  noNum6 (RLet x v b) tv k r w h = λ ()
  noNum6 (RPair a b) tv k r w h = λ ()
  noNum6 (RDestruct s x el y er) tv k r w h = λ ()
  noNum6 RUnit tv k r w h = λ ()
  noNum6 (RInt (ℤ.+ n)) tv k r w ()
  noNum6 (RInt ℤ.-[1+ n ]) tv k r w h = λ ()
  noNum6 (RFloat pos i fr l) tv k r w ()
  noNum6 (RFloat neg i fr l) tv k r w h = λ ()
  noNum6 (RAnnot e T) tv k r w h = λ ()
  noNum6 (RBinOp OpAdd a b) tv k r w h = λ ()
  noNum6 (RBinOp OpSub a b) tv k r w h = λ ()
  noNum6 (RBinOp OpMul a b) tv k r w h = λ ()
  noNum6 (RBinOp OpDiv a b) tv k r w h = λ ()
  noNum6 (RBinOp OpMod a b) tv k r w h = λ ()
  noNum6 (RBinOp OpLt a b) tv k r w h = λ ()
  noNum6 (RBinOp OpLe a b) tv k r w h = λ ()
  noNum6 (RBinOp OpGt a b) tv k r w h = λ ()
  noNum6 (RBinOp OpGe a b) tv k r w h = λ ()
  noNum6 (RBinOp OpEq a b) tv k r w h = λ ()
  noNum6 (RBinOp OpNe a b) tv k r w h = λ ()
  noNum6 (RBinOp (Op.dotted o+) a b) tv k r w h = λ ()
  noNum6 (RBinOp (Op.dotted o-) a b) tv k r w h = λ ()
  noNum6 (RBinOp (Op.dotted o*) a b) tv k r w h = λ ()
  noNum6 (RBinOp (Op.dotted o/) a b) tv k r w h = λ ()
  noNum6 (RBinOp (Op.dotted o<) a b) tv k r w h = λ ()
  noNum6 (RBinOp (Op.dotted o<=) a b) tv k r w h = λ ()
  noNum6 (RBinOp (Op.dotted o>) a b) tv k r w h = λ ()
  noNum6 (RBinOp (Op.dotted o>=) a b) tv k r w h = λ ()
  noNum6 (RBinOp (Op.dotted o==) a b) tv k r w h = λ ()
  noNum6 (RBinOp (Op.dotted o!=) a b) tv k r w h = λ ()
  noNum6 (RNeg e) tv k r w h = λ ()
  noNum4 (RVar x) tv k r w h = nameNoNum x tv k r w
  noNum4 (RQualified x q) tv k r w h = subst (λ ts → ¬ NumeralStart ts) (sym (word-toks x tv k _)) (λ ())
  noNum4 (RResolved n) tv k r () h
  noNum4 (RApp f a) tv k r (wf , wa) h = noNumApp4 f a (isCompose (headOf f)) tv k r refl wf h
  noNum4 (RLam x e) tv k r w h = λ ()
  noNum4 (RLet x v b) tv k r w h = λ ()
  noNum4 (RPair a b) tv k r w h = λ ()
  noNum4 (RDestruct s x el y er) tv k r w h = λ ()
  noNum4 RUnit tv k r w h = λ ()
  noNum4 (RInt (ℤ.+ n)) tv k r w ()
  noNum4 (RInt ℤ.-[1+ n ]) tv k r w h = λ ()
  noNum4 (RFloat pos i fr l) tv k r w ()
  noNum4 (RFloat neg i fr l) tv k r w h = λ ()
  noNum4 (RAnnot e T) tv k r w h = λ ()
  noNum4 (RBinOp OpAdd a b) tv k r w h = λ ()
  noNum4 (RBinOp OpSub a b) tv k r w h = λ ()
  noNum4 (RBinOp OpMul a b) tv k r w h = λ ()
  noNum4 (RBinOp OpDiv a b) tv k r w h = λ ()
  noNum4 (RBinOp OpMod a b) tv k r w h = λ ()
  noNum4 (RBinOp OpLt a b) tv k r w h = λ ()
  noNum4 (RBinOp OpLe a b) tv k r w h = λ ()
  noNum4 (RBinOp OpGt a b) tv k r w h = λ ()
  noNum4 (RBinOp OpGe a b) tv k r w h = λ ()
  noNum4 (RBinOp OpEq a b) tv k r w h = λ ()
  noNum4 (RBinOp OpNe a b) tv k r w h = λ ()
  noNum4 (RBinOp (Op.dotted o+) a b) tv k r w h = λ ()
  noNum4 (RBinOp (Op.dotted o-) a b) tv k r w h = λ ()
  noNum4 (RBinOp (Op.dotted o*) a b) tv k r w h = λ ()
  noNum4 (RBinOp (Op.dotted o/) a b) tv k r w h = λ ()
  noNum4 (RBinOp (Op.dotted o<) a b) tv k r w h = λ ()
  noNum4 (RBinOp (Op.dotted o<=) a b) tv k r w h = λ ()
  noNum4 (RBinOp (Op.dotted o>) a b) tv k r w h = λ ()
  noNum4 (RBinOp (Op.dotted o>=) a b) tv k r w h = λ ()
  noNum4 (RBinOp (Op.dotted o==) a b) tv k r w h = λ ()
  noNum4 (RBinOp (Op.dotted o!=) a b) tv k r w h = λ ()
  noNum4 (RNeg e) tv k r w h = λ ()

mutual
  -- | An atom (level 6).
  atomL : ∀ e tv k r → WF e → NoQual r → ParsesAtomExpr (E 6 e tv k r) e r
  atomL (RVar x) tv k r w nq = nameAtom x tv k r w nq
  atomL (RQualified x q) tv k r w nq =
    subst (λ ts → ParsesAtomExpr ts (RQualified x q) r) (sym (word-toks x tv k _))
      (subst (λ ts → ParsesAtomExpr (TWord x ∷ TAt ∷ ts) (RQualified x q) r) (sym (word-toks q tv _ r)) (atom-qual w))
  atomL (RResolved n) tv k r () nq
  atomL (RApp f a) tv k r (wf , wa) nq = atomApp f a (isCompose (headOf f)) tv k r refl wf wa nq
  atomL (RLam x e) tv k r w nq = atom-paren (atom→expr stops-rparen (lamA x e tv k (TRParen ∷ r) w stops-rparen)) paren-close
  atomL (RLet x v b) tv k r w nq = atom-paren (atom→expr stops-rparen (letA x v b tv k (TRParen ∷ r) w stops-rparen)) paren-close
  atomL (RDestruct s x el y er) tv k r w nq =
    atom-paren (atom→expr stops-rparen (desA s x el y er tv k (TRParen ∷ r) w stops-rparen)) paren-close
  atomL (RPair a b) tv k r (wa , wb) nq =
    atom-paren (wholeL a tv k _ wa stops-comma) (paren-pair (wholeL b tv _ (TRParen ∷ r) wb stops-rparen))
  atomL RUnit tv k r w nq = atom-unit
  atomL (RInt (ℤ.+ n)) tv k r w nq =
    subst (λ ts → ParsesAtomExpr ts (RInt (ℤ.+ n)) r) (sym (anchor-toks (TInt (ℤ.+ n)) tv k r)) atom-int
  atomL (RInt ℤ.-[1+ n ]) tv k r w nq = unary→atom (negIntU n tv k (TRParen ∷ r) (λ ()))
  atomL (RFloat pos i fr l) tv k r w nq =
    subst (λ ts → ParsesAtomExpr ts (RFloat pos i fr l) r) (sym (anchor-toks (TFloat i fr l) tv k r)) atom-float
  atomL (RFloat neg i fr l) tv k r w nq = unary→atom (negFloatU i fr l tv k (TRParen ∷ r) (λ ()))
  atomL (RAnnot e T) tv k r (we , wT) nq =
    atom-paren (wholeL e tv k _ we stops-colon)
      (paren-annot (subst (λ A → Annot.ParsesType (toks (proj₁ (pty 0 true (toPoly T) tv (proj₂ (pex 0 true e tv k)))) (TRParen ∷ r)) A (TRParen ∷ r))
        (ground-id T wT)
        (TA.Ground.type′ (toPoly T) true tv (proj₂ (pex 0 true e tv k)) (TRParen ∷ r) (ground-wf T) ((λ ()) , (λ ()))
          ((λ ()) , (λ ()) , (λ ()) , (λ ())) (λ ()) (λ ()))))
  atomL (RBinOp OpAdd a b) tv k r (wa , wb) nq =
    atom-paren (expr (cmp-none (leftAdd a tv k _ wa (λ ()) (λ ()) (λ { starts → otherLevel (ot-plain refl) (λ ()) }) (add-op (ot-plain refl) (mulL b tv _ (TRParen ∷ r) wb (λ ()) (λ ()) (mul-done (λ { starts () }))) (add-done (λ { starts () })))) (λ { starts () })) (comp-done (λ ()))) paren-close
  atomL (RBinOp OpSub a b) tv k r (wa , wb) nq =
    atom-paren (expr (cmp-none (leftAdd a tv k _ wa (λ ()) (λ ()) (λ { starts → otherLevel (ot-plain refl) (λ ()) }) (add-op (ot-plain refl) (mulL b tv _ (TRParen ∷ r) wb (λ ()) (λ ()) (mul-done (λ { starts () }))) (add-done (λ { starts () })))) (λ { starts () })) (comp-done (λ ()))) paren-close
  atomL (RBinOp OpMul a b) tv k r (wa , wb) nq =
    atom-paren (expr (cmp-none (add (leftMul a tv k _ wa (λ ()) (λ ()) (mul-op (ot-plain refl) (unaryL b tv _ (TRParen ∷ r) wb (λ ()) (λ ())) (mul-done (λ { starts () })))) (add-done (λ { starts () }))) (λ { starts () })) (comp-done (λ ()))) paren-close
  atomL (RBinOp OpDiv a b) tv k r (wa , wb) nq =
    atom-paren (expr (cmp-none (add (leftMul a tv k _ wa (λ ()) (λ ()) (mul-op (ot-plain refl) (unaryL b tv _ (TRParen ∷ r) wb (λ ()) (λ ())) (mul-done (λ { starts () })))) (add-done (λ { starts () }))) (λ { starts () })) (comp-done (λ ()))) paren-close
  atomL (RBinOp OpMod a b) tv k r (wa , wb) nq =
    atom-paren (expr (cmp-none (add (leftMul a tv k _ wa (λ ()) (λ ()) (mul-op (ot-plain refl) (unaryL b tv _ (TRParen ∷ r) wb (λ ()) (λ ())) (mul-done (λ { starts () })))) (add-done (λ { starts () }))) (λ { starts () })) (comp-done (λ ()))) paren-close
  atomL (RBinOp OpLt a b) tv k r (wa , wb) nq =
    atom-paren (expr (cmp (ot-plain refl) (leftCmp a tv k _ wa (λ ()) (λ ()) (λ { starts → otherLevel (ot-plain refl) (λ ()) }) (λ { starts → otherLevel (ot-plain refl) (λ ()) })) (addL b tv _ (TRParen ∷ r) wb (λ ()) (λ ()) (λ { starts () }) (add-done (λ { starts () })))) (comp-done (λ ()))) paren-close
  atomL (RBinOp OpLe a b) tv k r (wa , wb) nq =
    atom-paren (expr (cmp (ot-plain refl) (leftCmp a tv k _ wa (λ ()) (λ ()) (λ { starts → otherLevel (ot-plain refl) (λ ()) }) (λ { starts → otherLevel (ot-plain refl) (λ ()) })) (addL b tv _ (TRParen ∷ r) wb (λ ()) (λ ()) (λ { starts () }) (add-done (λ { starts () })))) (comp-done (λ ()))) paren-close
  atomL (RBinOp OpGt a b) tv k r (wa , wb) nq =
    atom-paren (expr (cmp (ot-plain refl) (leftCmp a tv k _ wa (λ ()) (λ ()) (λ { starts → otherLevel (ot-plain refl) (λ ()) }) (λ { starts → otherLevel (ot-plain refl) (λ ()) })) (addL b tv _ (TRParen ∷ r) wb (λ ()) (λ ()) (λ { starts () }) (add-done (λ { starts () })))) (comp-done (λ ()))) paren-close
  atomL (RBinOp OpGe a b) tv k r (wa , wb) nq =
    atom-paren (expr (cmp (ot-plain refl) (leftCmp a tv k _ wa (λ ()) (λ ()) (λ { starts → otherLevel (ot-plain refl) (λ ()) }) (λ { starts → otherLevel (ot-plain refl) (λ ()) })) (addL b tv _ (TRParen ∷ r) wb (λ ()) (λ ()) (λ { starts () }) (add-done (λ { starts () })))) (comp-done (λ ()))) paren-close
  atomL (RBinOp OpEq a b) tv k r (wa , wb) nq =
    atom-paren (expr (cmp (ot-plain refl) (leftCmp a tv k _ wa (λ ()) (λ ()) (λ { starts → otherLevel (ot-plain refl) (λ ()) }) (λ { starts → otherLevel (ot-plain refl) (λ ()) })) (addL b tv _ (TRParen ∷ r) wb (λ ()) (λ ()) (λ { starts () }) (add-done (λ { starts () })))) (comp-done (λ ()))) paren-close
  atomL (RBinOp OpNe a b) tv k r (wa , wb) nq =
    atom-paren (expr (cmp (ot-plain refl) (leftCmp a tv k _ wa (λ ()) (λ ()) (λ { starts → otherLevel (ot-plain refl) (λ ()) }) (λ { starts → otherLevel (ot-plain refl) (λ ()) })) (addL b tv _ (TRParen ∷ r) wb (λ ()) (λ ()) (λ { starts () }) (add-done (λ { starts () })))) (comp-done (λ ()))) paren-close
  atomL (RBinOp (Op.dotted o+) a b) tv k r (wa , wb) nq =
    atom-paren (expr (cmp-none (leftAdd a tv k _ wa (λ ()) (λ ()) (λ { starts → otherLevel (ot-dotted refl) (λ ()) }) (add-op (ot-dotted refl) (mulL b tv _ (TRParen ∷ r) wb (λ ()) (λ ()) (mul-done (λ { starts () }))) (add-done (λ { starts () })))) (λ { starts () })) (comp-done (λ ()))) paren-close
  atomL (RBinOp (Op.dotted o-) a b) tv k r (wa , wb) nq =
    atom-paren (expr (cmp-none (leftAdd a tv k _ wa (λ ()) (λ ()) (λ { starts → otherLevel (ot-dotted refl) (λ ()) }) (add-op (ot-dotted refl) (mulL b tv _ (TRParen ∷ r) wb (λ ()) (λ ()) (mul-done (λ { starts () }))) (add-done (λ { starts () })))) (λ { starts () })) (comp-done (λ ()))) paren-close
  atomL (RBinOp (Op.dotted o*) a b) tv k r (wa , wb) nq =
    atom-paren (expr (cmp-none (add (leftMul a tv k _ wa (λ ()) (λ ()) (mul-op (ot-dotted refl) (unaryL b tv _ (TRParen ∷ r) wb (λ ()) (λ ())) (mul-done (λ { starts () })))) (add-done (λ { starts () }))) (λ { starts () })) (comp-done (λ ()))) paren-close
  atomL (RBinOp (Op.dotted o/) a b) tv k r (wa , wb) nq =
    atom-paren (expr (cmp-none (add (leftMul a tv k _ wa (λ ()) (λ ()) (mul-op (ot-dotted refl) (unaryL b tv _ (TRParen ∷ r) wb (λ ()) (λ ())) (mul-done (λ { starts () })))) (add-done (λ { starts () }))) (λ { starts () })) (comp-done (λ ()))) paren-close
  atomL (RBinOp (Op.dotted o<) a b) tv k r (wa , wb) nq =
    atom-paren (expr (cmp (ot-dotted refl) (leftCmp a tv k _ wa (λ ()) (λ ()) (λ { starts → otherLevel (ot-dotted refl) (λ ()) }) (λ { starts → otherLevel (ot-dotted refl) (λ ()) })) (addL b tv _ (TRParen ∷ r) wb (λ ()) (λ ()) (λ { starts () }) (add-done (λ { starts () })))) (comp-done (λ ()))) paren-close
  atomL (RBinOp (Op.dotted o<=) a b) tv k r (wa , wb) nq =
    atom-paren (expr (cmp (ot-dotted refl) (leftCmp a tv k _ wa (λ ()) (λ ()) (λ { starts → otherLevel (ot-dotted refl) (λ ()) }) (λ { starts → otherLevel (ot-dotted refl) (λ ()) })) (addL b tv _ (TRParen ∷ r) wb (λ ()) (λ ()) (λ { starts () }) (add-done (λ { starts () })))) (comp-done (λ ()))) paren-close
  atomL (RBinOp (Op.dotted o>) a b) tv k r (wa , wb) nq =
    atom-paren (expr (cmp (ot-dotted refl) (leftCmp a tv k _ wa (λ ()) (λ ()) (λ { starts → otherLevel (ot-dotted refl) (λ ()) }) (λ { starts → otherLevel (ot-dotted refl) (λ ()) })) (addL b tv _ (TRParen ∷ r) wb (λ ()) (λ ()) (λ { starts () }) (add-done (λ { starts () })))) (comp-done (λ ()))) paren-close
  atomL (RBinOp (Op.dotted o>=) a b) tv k r (wa , wb) nq =
    atom-paren (expr (cmp (ot-dotted refl) (leftCmp a tv k _ wa (λ ()) (λ ()) (λ { starts → otherLevel (ot-dotted refl) (λ ()) }) (λ { starts → otherLevel (ot-dotted refl) (λ ()) })) (addL b tv _ (TRParen ∷ r) wb (λ ()) (λ ()) (λ { starts () }) (add-done (λ { starts () })))) (comp-done (λ ()))) paren-close
  atomL (RBinOp (Op.dotted o==) a b) tv k r (wa , wb) nq =
    atom-paren (expr (cmp (ot-dotted refl) (leftCmp a tv k _ wa (λ ()) (λ ()) (λ { starts → otherLevel (ot-dotted refl) (λ ()) }) (λ { starts → otherLevel (ot-dotted refl) (λ ()) })) (addL b tv _ (TRParen ∷ r) wb (λ ()) (λ ()) (λ { starts () }) (add-done (λ { starts () })))) (comp-done (λ ()))) paren-close
  atomL (RBinOp (Op.dotted o!=) a b) tv k r (wa , wb) nq =
    atom-paren (expr (cmp (ot-dotted refl) (leftCmp a tv k _ wa (λ ()) (λ ()) (λ { starts → otherLevel (ot-dotted refl) (λ ()) }) (λ { starts → otherLevel (ot-dotted refl) (λ ()) })) (addL b tv _ (TRParen ∷ r) wb (λ ()) (λ ()) (λ { starts () }) (add-done (λ { starts () })))) (comp-done (λ ()))) paren-close
  atomL (RNeg e) tv k r w nq = unary→atom (negL e (startsNum e) tv k (TRParen ∷ r) refl w (λ ()) (λ ()))

  -- An application at the atom level: parenthesized.
  atomApp : ∀ f a b tv k r → isCompose (headOf f) ≡ b → WF f → WF a → NoQual r
          → ParsesAtomExpr (toks (proj₁ (pcomp 6 b f a tv k)) r) (RApp f a) r
  atomApp f a true tv k r eq wf wa nq with compose-true f eq
  ... | g , refl = composeAtom g a 5 tv k r (proj₂ wf) wa
  atomApp f a false tv k r eq wf wa nq =
    atom-paren (app→expr stops-rparen (spineApp f a tv k (TRParen ∷ r) wf wa (λ ()) (app-done (λ ())))) paren-close

  -- A composition in parentheses.
  composeAtom : ∀ g h L tv k r → WF g → WF h
              → ParsesAtomExpr (toks (proj₁ (pcompose (suc L) g h tv k)) r) (RApp (RApp (RVar "compose") g) h) r
  composeAtom g h L tv k r wg wh =
    atom-paren (composeL g h tv k (TRParen ∷ r) wg wh (λ ()) (λ ()) (λ { starts () }) (λ { starts () }) (λ { starts () })
                  (comp-done (λ ()))) paren-close

  -- `g . h` at the level of a composition.
  composeL : ∀ g h tv k r {e′ r′} → WF g → WF h → NoQual r → AppDone r → MulDone r → AddDone r → CmpDone r
           → ParsesCompTail (RApp (RApp (RVar "compose") g) h) r e′ r′
           → ParsesExpr (toks (proj₁ (pcompose 0 g h tv k)) r) e′ r′
  composeL g h tv k r wg wh nq ad md dd cd tl =
    chainL g tv k _ wg (λ ()) (λ ()) (λ { starts () }) (λ { starts () }) (λ { starts () })
      (comp-dot (cmpL h tv _ r wh nq ad md dd cd) tl)

  -- The head and arguments of an application, with what continues it.
  spineApp : ∀ f a tv k r {e′ r′} → WF f → WF a → NoQual r → ParsesAppTail (RApp f a) r e′ r′
           → ParsesApp (toks (proj₁ ((pspine f ⊕ᵈ pure′ Once.Format.Doc.line ⊕ᵈ pex 6 false a) tv k)) r) e′ r′
  spineApp f a tv k r wf wa nq tl =
    spineL f tv k _ wf (argNoQual (argSt a tv _ r wa)) (app-arg (argSt a tv _ r wa) (atomL a tv _ r wa nq) tl)

  spineL : ∀ f tv k r {e′ r′} → WF f → NoQual r → ParsesAppTail f r e′ r′ → ParsesApp (toks (proj₁ (pspine f tv k)) r) e′ r′
  spineL (RApp f a) tv k r (wf , wa) nq tl = spineApp′ f a (isCompose (headOf f)) tv k r refl wf wa nq tl
  spineL (RVar x) tv k r wf nq tl = app (atomL (RVar x) tv k r wf nq) tl
  spineL (RQualified x q) tv k r wf nq tl = app (atomL (RQualified x q) tv k r wf nq) tl
  spineL (RResolved n) tv k r () nq tl
  spineL (RLam x e) tv k r wf nq tl = app (atomL (RLam x e) tv k r wf nq) tl
  spineL (RLet x v b) tv k r wf nq tl = app (atomL (RLet x v b) tv k r wf nq) tl
  spineL (RPair a b) tv k r wf nq tl = app (atomL (RPair a b) tv k r wf nq) tl
  spineL (RDestruct s x el y er) tv k r wf nq tl = app (atomL (RDestruct s x el y er) tv k r wf nq) tl
  spineL RUnit tv k r wf nq tl = app (atomL RUnit tv k r wf nq) tl
  spineL (RInt (ℤ.+ n)) tv k r wf nq tl = app (atomL (RInt (ℤ.+ n)) tv k r wf nq) tl
  spineL (RInt ℤ.-[1+ n ]) tv k r wf nq tl = app (atomL (RInt ℤ.-[1+ n ]) tv k r wf nq) tl
  spineL (RFloat pos i fr l) tv k r wf nq tl = app (atomL (RFloat pos i fr l) tv k r wf nq) tl
  spineL (RFloat neg i fr l) tv k r wf nq tl = app (atomL (RFloat neg i fr l) tv k r wf nq) tl
  spineL (RAnnot e T) tv k r wf nq tl = app (atomL (RAnnot e T) tv k r wf nq) tl
  spineL (RBinOp op a b) tv k r wf nq tl = app (atomL (RBinOp op a b) tv k r wf nq) tl
  spineL (RNeg e) tv k r wf nq tl = app (atomL (RNeg e) tv k r wf nq) tl

  spineApp′ : ∀ f a b tv k r {e′ r′} → isCompose (headOf f) ≡ b → WF f → WF a → NoQual r → ParsesAppTail (RApp f a) r e′ r′
            → ParsesApp (toks (proj₁ (pspine′ b f a tv k)) r) e′ r′
  spineApp′ f a true tv k r eq wf wa nq tl with compose-true f eq
  ... | g , refl = app (composeAtom g a 5 tv k r (proj₂ wf) wa) tl
  spineApp′ f a false tv k r eq wf wa nq tl = spineApp f a tv k r wf wa nq tl

  -- The left operand of `.`, while it is a composition.
  chainL : ∀ g tv k r {e′ r′} → WF g → NoQual r → AppDone r → MulDone r → AddDone r → CmpDone r → ParsesCompTail g r e′ r′
         → ParsesExpr (toks (proj₁ (pchainC g tv k)) r) e′ r′
  chainL (RApp f h) tv k r (wf , wh) nq ad md dd cd tl = chainApp f h (isCompose (headOf f)) tv k r refl wf wh nq ad md dd cd tl
  chainL (RVar x) tv k r wg nq ad md dd cd tl = expr (cmpL (RVar x) tv k r wg nq ad md dd cd) tl
  chainL (RQualified x q) tv k r wg nq ad md dd cd tl = expr (cmpL (RQualified x q) tv k r wg nq ad md dd cd) tl
  chainL (RResolved n) tv k r () nq ad md dd cd tl
  chainL (RLam x e) tv k r wg nq ad md dd cd tl = expr (cmpL (RLam x e) tv k r wg nq ad md dd cd) tl
  chainL (RLet x v b) tv k r wg nq ad md dd cd tl = expr (cmpL (RLet x v b) tv k r wg nq ad md dd cd) tl
  chainL (RPair a b) tv k r wg nq ad md dd cd tl = expr (cmpL (RPair a b) tv k r wg nq ad md dd cd) tl
  chainL (RDestruct s x el y er) tv k r wg nq ad md dd cd tl = expr (cmpL (RDestruct s x el y er) tv k r wg nq ad md dd cd) tl
  chainL RUnit tv k r wg nq ad md dd cd tl = expr (cmpL RUnit tv k r wg nq ad md dd cd) tl
  chainL (RInt (ℤ.+ n)) tv k r wg nq ad md dd cd tl = expr (cmpL (RInt (ℤ.+ n)) tv k r wg nq ad md dd cd) tl
  chainL (RInt ℤ.-[1+ n ]) tv k r wg nq ad md dd cd tl = expr (cmpL (RInt ℤ.-[1+ n ]) tv k r wg nq ad md dd cd) tl
  chainL (RFloat pos i fr l) tv k r wg nq ad md dd cd tl = expr (cmpL (RFloat pos i fr l) tv k r wg nq ad md dd cd) tl
  chainL (RFloat neg i fr l) tv k r wg nq ad md dd cd tl = expr (cmpL (RFloat neg i fr l) tv k r wg nq ad md dd cd) tl
  chainL (RAnnot e T) tv k r wg nq ad md dd cd tl = expr (cmpL (RAnnot e T) tv k r wg nq ad md dd cd) tl
  chainL (RBinOp op a b) tv k r wg nq ad md dd cd tl = expr (cmpL (RBinOp op a b) tv k r wg nq ad md dd cd) tl
  chainL (RNeg e) tv k r wg nq ad md dd cd tl = expr (cmpL (RNeg e) tv k r wg nq ad md dd cd) tl

  chainApp : ∀ f h b tv k r {e′ r′} → isCompose (headOf f) ≡ b → WF f → WF h → NoQual r → AppDone r → MulDone r → AddDone r
           → CmpDone r → ParsesCompTail (RApp f h) r e′ r′ → ParsesExpr (toks (proj₁ (pchainC′ b f h tv k)) r) e′ r′
  chainApp f h true tv k r eq wf wh nq ad md dd cd tl with compose-true f eq
  ... | g , refl =
    chainL g tv k _ (proj₂ wf) (λ ()) (λ ()) (λ { starts () }) (λ { starts () }) (λ { starts () })
      (comp-dot (cmpL h tv _ r wh nq ad md dd cd) tl)
  chainApp f h false tv k r eq wf wh nq ad md dd cd tl =
    expr (cmp-none (add (mul (unary (spineApp f h tv k r wf wh nq (app-done ad))) (mul-done md)) (add-done dd)) cd) tl

  -- | An application (level 5), with what continues it.
  appL : ∀ e tv k r {e′ r′} → WF e → NoQual r → ParsesAppTail e r e′ r′ → ParsesApp (E 5 e tv k r) e′ r′
  appL (RApp f a) tv k r (wf , wa) nq tl = appApp f a (isCompose (headOf f)) tv k r refl wf wa nq tl
  appL (RResolved n) tv k r () nq tl
  appL (RVar x) tv k r w nq tl = app (atomL (RVar x) tv k r w nq) tl
  appL (RQualified x q) tv k r w nq tl = app (atomL (RQualified x q) tv k r w nq) tl
  appL (RLam x e) tv k r w nq tl = app (atomL (RLam x e) tv k r w nq) tl
  appL (RLet x v b) tv k r w nq tl = app (atomL (RLet x v b) tv k r w nq) tl
  appL (RPair a b) tv k r w nq tl = app (atomL (RPair a b) tv k r w nq) tl
  appL (RDestruct s x el y er) tv k r w nq tl = app (atomL (RDestruct s x el y er) tv k r w nq) tl
  appL RUnit tv k r w nq tl = app (atomL RUnit tv k r w nq) tl
  appL (RInt (ℤ.+ n)) tv k r w nq tl = app (atomL (RInt (ℤ.+ n)) tv k r w nq) tl
  appL (RInt ℤ.-[1+ n ]) tv k r w nq tl = app (atomL (RInt ℤ.-[1+ n ]) tv k r w nq) tl
  appL (RFloat pos i fr l) tv k r w nq tl = app (atomL (RFloat pos i fr l) tv k r w nq) tl
  appL (RFloat neg i fr l) tv k r w nq tl = app (atomL (RFloat neg i fr l) tv k r w nq) tl
  appL (RAnnot e T) tv k r w nq tl = app (atomL (RAnnot e T) tv k r w nq) tl
  appL (RNeg e) tv k r w nq tl = app (atomL (RNeg e) tv k r w nq) tl
  appL (RBinOp OpAdd a b) tv k r w nq tl = app (atomL (RBinOp OpAdd a b) tv k r w nq) tl
  appL (RBinOp OpSub a b) tv k r w nq tl = app (atomL (RBinOp OpSub a b) tv k r w nq) tl
  appL (RBinOp OpMul a b) tv k r w nq tl = app (atomL (RBinOp OpMul a b) tv k r w nq) tl
  appL (RBinOp OpDiv a b) tv k r w nq tl = app (atomL (RBinOp OpDiv a b) tv k r w nq) tl
  appL (RBinOp OpMod a b) tv k r w nq tl = app (atomL (RBinOp OpMod a b) tv k r w nq) tl
  appL (RBinOp OpLt a b) tv k r w nq tl = app (atomL (RBinOp OpLt a b) tv k r w nq) tl
  appL (RBinOp OpLe a b) tv k r w nq tl = app (atomL (RBinOp OpLe a b) tv k r w nq) tl
  appL (RBinOp OpGt a b) tv k r w nq tl = app (atomL (RBinOp OpGt a b) tv k r w nq) tl
  appL (RBinOp OpGe a b) tv k r w nq tl = app (atomL (RBinOp OpGe a b) tv k r w nq) tl
  appL (RBinOp OpEq a b) tv k r w nq tl = app (atomL (RBinOp OpEq a b) tv k r w nq) tl
  appL (RBinOp OpNe a b) tv k r w nq tl = app (atomL (RBinOp OpNe a b) tv k r w nq) tl
  appL (RBinOp (Op.dotted o+) a b) tv k r w nq tl = app (atomL (RBinOp (Op.dotted o+) a b) tv k r w nq) tl
  appL (RBinOp (Op.dotted o-) a b) tv k r w nq tl = app (atomL (RBinOp (Op.dotted o-) a b) tv k r w nq) tl
  appL (RBinOp (Op.dotted o*) a b) tv k r w nq tl = app (atomL (RBinOp (Op.dotted o*) a b) tv k r w nq) tl
  appL (RBinOp (Op.dotted o/) a b) tv k r w nq tl = app (atomL (RBinOp (Op.dotted o/) a b) tv k r w nq) tl
  appL (RBinOp (Op.dotted o<) a b) tv k r w nq tl = app (atomL (RBinOp (Op.dotted o<) a b) tv k r w nq) tl
  appL (RBinOp (Op.dotted o<=) a b) tv k r w nq tl = app (atomL (RBinOp (Op.dotted o<=) a b) tv k r w nq) tl
  appL (RBinOp (Op.dotted o>) a b) tv k r w nq tl = app (atomL (RBinOp (Op.dotted o>) a b) tv k r w nq) tl
  appL (RBinOp (Op.dotted o>=) a b) tv k r w nq tl = app (atomL (RBinOp (Op.dotted o>=) a b) tv k r w nq) tl
  appL (RBinOp (Op.dotted o==) a b) tv k r w nq tl = app (atomL (RBinOp (Op.dotted o==) a b) tv k r w nq) tl
  appL (RBinOp (Op.dotted o!=) a b) tv k r w nq tl = app (atomL (RBinOp (Op.dotted o!=) a b) tv k r w nq) tl

  appApp : ∀ f a b tv k r {e′ r′} → isCompose (headOf f) ≡ b → WF f → WF a → NoQual r → ParsesAppTail (RApp f a) r e′ r′
         → ParsesApp (toks (proj₁ (pcomp 5 b f a tv k)) r) e′ r′
  appApp f a true tv k r eq wf wa nq tl with compose-true f eq
  ... | g , refl = app (composeAtom g a 4 tv k r (proj₂ wf) wa) tl
  appApp f a false tv k r eq wf wa nq tl = spineApp f a tv k r wf wa nq tl

  -- | A prefix `-` (level 4).
  unaryL : ∀ e tv k r → WF e → NoQual r → AppDone r → ParsesUnary (E 4 e tv k r) e r
  unaryL (RNeg e) tv k r w nq ad = negL e (startsNum e) tv k r refl w nq ad
  unaryL (RInt ℤ.-[1+ n ]) tv k r w nq ad = negIntU n tv k r ad
  unaryL (RFloat neg i fr l) tv k r w nq ad = negFloatU i fr l tv k r ad
  unaryL (RApp f a) tv k r (wf , wa) nq ad = unaryApp f a (isCompose (headOf f)) tv k r refl wf wa nq ad
  unaryL (RResolved n) tv k r () nq ad
  unaryL (RVar x) tv k r w nq ad = unary (appL (RVar x) tv k r w nq (app-done ad))
  unaryL (RQualified x q) tv k r w nq ad = unary (appL (RQualified x q) tv k r w nq (app-done ad))
  unaryL (RLam x e) tv k r w nq ad = unary (appL (RLam x e) tv k r w nq (app-done ad))
  unaryL (RLet x v b) tv k r w nq ad = unary (appL (RLet x v b) tv k r w nq (app-done ad))
  unaryL (RPair a b) tv k r w nq ad = unary (appL (RPair a b) tv k r w nq (app-done ad))
  unaryL (RDestruct s x el y er) tv k r w nq ad = unary (appL (RDestruct s x el y er) tv k r w nq (app-done ad))
  unaryL RUnit tv k r w nq ad = unary (appL RUnit tv k r w nq (app-done ad))
  unaryL (RInt (ℤ.+ n)) tv k r w nq ad = unary (appL (RInt (ℤ.+ n)) tv k r w nq (app-done ad))
  unaryL (RFloat pos i fr l) tv k r w nq ad = unary (appL (RFloat pos i fr l) tv k r w nq (app-done ad))
  unaryL (RAnnot e T) tv k r w nq ad = unary (appL (RAnnot e T) tv k r w nq (app-done ad))
  unaryL (RBinOp OpAdd a b) tv k r w nq ad = unary (appL (RBinOp OpAdd a b) tv k r w nq (app-done ad))
  unaryL (RBinOp OpSub a b) tv k r w nq ad = unary (appL (RBinOp OpSub a b) tv k r w nq (app-done ad))
  unaryL (RBinOp OpMul a b) tv k r w nq ad = unary (appL (RBinOp OpMul a b) tv k r w nq (app-done ad))
  unaryL (RBinOp OpDiv a b) tv k r w nq ad = unary (appL (RBinOp OpDiv a b) tv k r w nq (app-done ad))
  unaryL (RBinOp OpMod a b) tv k r w nq ad = unary (appL (RBinOp OpMod a b) tv k r w nq (app-done ad))
  unaryL (RBinOp OpLt a b) tv k r w nq ad = unary (appL (RBinOp OpLt a b) tv k r w nq (app-done ad))
  unaryL (RBinOp OpLe a b) tv k r w nq ad = unary (appL (RBinOp OpLe a b) tv k r w nq (app-done ad))
  unaryL (RBinOp OpGt a b) tv k r w nq ad = unary (appL (RBinOp OpGt a b) tv k r w nq (app-done ad))
  unaryL (RBinOp OpGe a b) tv k r w nq ad = unary (appL (RBinOp OpGe a b) tv k r w nq (app-done ad))
  unaryL (RBinOp OpEq a b) tv k r w nq ad = unary (appL (RBinOp OpEq a b) tv k r w nq (app-done ad))
  unaryL (RBinOp OpNe a b) tv k r w nq ad = unary (appL (RBinOp OpNe a b) tv k r w nq (app-done ad))
  unaryL (RBinOp (Op.dotted o+) a b) tv k r w nq ad = unary (appL (RBinOp (Op.dotted o+) a b) tv k r w nq (app-done ad))
  unaryL (RBinOp (Op.dotted o-) a b) tv k r w nq ad = unary (appL (RBinOp (Op.dotted o-) a b) tv k r w nq (app-done ad))
  unaryL (RBinOp (Op.dotted o*) a b) tv k r w nq ad = unary (appL (RBinOp (Op.dotted o*) a b) tv k r w nq (app-done ad))
  unaryL (RBinOp (Op.dotted o/) a b) tv k r w nq ad = unary (appL (RBinOp (Op.dotted o/) a b) tv k r w nq (app-done ad))
  unaryL (RBinOp (Op.dotted o<) a b) tv k r w nq ad = unary (appL (RBinOp (Op.dotted o<) a b) tv k r w nq (app-done ad))
  unaryL (RBinOp (Op.dotted o<=) a b) tv k r w nq ad = unary (appL (RBinOp (Op.dotted o<=) a b) tv k r w nq (app-done ad))
  unaryL (RBinOp (Op.dotted o>) a b) tv k r w nq ad = unary (appL (RBinOp (Op.dotted o>) a b) tv k r w nq (app-done ad))
  unaryL (RBinOp (Op.dotted o>=) a b) tv k r w nq ad = unary (appL (RBinOp (Op.dotted o>=) a b) tv k r w nq (app-done ad))
  unaryL (RBinOp (Op.dotted o==) a b) tv k r w nq ad = unary (appL (RBinOp (Op.dotted o==) a b) tv k r w nq (app-done ad))
  unaryL (RBinOp (Op.dotted o!=) a b) tv k r w nq ad = unary (appL (RBinOp (Op.dotted o!=) a b) tv k r w nq (app-done ad))

  -- `-e`: a prefix `-`, with `e` parenthesized when it would start a negative literal.
  negL : ∀ e b tv k r → startsNum e ≡ b → WF e → NoQual r → AppDone r
       → ParsesUnary (toks (proj₁ ((t TMinus ⊕ᵈ pure′ (if startsNeg e then Once.Format.Doc.sp else Once.Format.Doc.empty)
                                     ⊕ᵈ paren b (pex 4 false e)) tv k)) r) (RNeg e) r
  negL e false tv k r sn w nq ad =
    subst (λ ts → ParsesUnary (TMinus ∷ ts) (RNeg e) r) (sym (if-space (startsNeg e) (E 4 e tv k r)))
      (neg (noNum4 e tv k r w sn) (unaryL e tv k r w nq ad))
  negL e true tv k r sn w nq ad =
    subst (λ ts → ParsesUnary (TMinus ∷ ts) (RNeg e) r) (sym (if-space (startsNeg e) (TLParen ∷ E 4 e tv k (TRParen ∷ r))))
      (neg (λ ()) (unary (app (unary→atom (unaryL e tv k (TRParen ∷ r) w (λ ()) (λ ()))) (app-done ad))))

  unaryApp : ∀ f a b tv k r → isCompose (headOf f) ≡ b → WF f → WF a → NoQual r → AppDone r
           → ParsesUnary (toks (proj₁ (pcomp 4 b f a tv k)) r) (RApp f a) r
  unaryApp f a true tv k r eq wf wa nq ad with compose-true f eq
  ... | g , refl = unary (app (composeAtom g a 3 tv k r (proj₂ wf) wa) (app-done ad))
  unaryApp f a false tv k r eq wf wa nq ad = unary (spineApp f a tv k r wf wa nq (app-done ad))

  -- | `*`, `/`, `%` (level 3), with what continues them.
  mulL : ∀ e tv k r {e′ r′} → WF e → NoQual r → AppDone r → ParsesMulTail e r e′ r′ → ParsesMul (E 3 e tv k r) e′ r′
  mulL (RApp f a) tv k r (wf , wa) nq ad tl = mulApp f a (isCompose (headOf f)) tv k r refl wf wa nq ad tl
  mulL (RResolved n) tv k r () nq ad tl
  mulL (RVar x) tv k r w nq ad tl = mul (unaryL (RVar x) tv k r w nq ad) tl
  mulL (RQualified x q) tv k r w nq ad tl = mul (unaryL (RQualified x q) tv k r w nq ad) tl
  mulL (RLam x e) tv k r w nq ad tl = mul (unaryL (RLam x e) tv k r w nq ad) tl
  mulL (RLet x v b) tv k r w nq ad tl = mul (unaryL (RLet x v b) tv k r w nq ad) tl
  mulL (RPair a b) tv k r w nq ad tl = mul (unaryL (RPair a b) tv k r w nq ad) tl
  mulL (RDestruct s x el y er) tv k r w nq ad tl = mul (unaryL (RDestruct s x el y er) tv k r w nq ad) tl
  mulL RUnit tv k r w nq ad tl = mul (unaryL RUnit tv k r w nq ad) tl
  mulL (RInt (ℤ.+ n)) tv k r w nq ad tl = mul (unaryL (RInt (ℤ.+ n)) tv k r w nq ad) tl
  mulL (RInt ℤ.-[1+ n ]) tv k r w nq ad tl = mul (unaryL (RInt ℤ.-[1+ n ]) tv k r w nq ad) tl
  mulL (RFloat pos i fr l) tv k r w nq ad tl = mul (unaryL (RFloat pos i fr l) tv k r w nq ad) tl
  mulL (RFloat neg i fr l) tv k r w nq ad tl = mul (unaryL (RFloat neg i fr l) tv k r w nq ad) tl
  mulL (RAnnot e T) tv k r w nq ad tl = mul (unaryL (RAnnot e T) tv k r w nq ad) tl
  mulL (RNeg e) tv k r w nq ad tl = mul (unaryL (RNeg e) tv k r w nq ad) tl
  mulL (RBinOp OpAdd a b) tv k r w nq ad tl = mul (unaryL (RBinOp OpAdd a b) tv k r w nq ad) tl
  mulL (RBinOp OpSub a b) tv k r w nq ad tl = mul (unaryL (RBinOp OpSub a b) tv k r w nq ad) tl
  mulL (RBinOp OpMul a b) tv k r (wa , wb) nq ad tl =
    leftMul a tv k _ wa (λ ()) (λ ()) (mul-op (ot-plain refl) (unaryL b tv _ r wb nq ad) tl)
  mulL (RBinOp OpDiv a b) tv k r (wa , wb) nq ad tl =
    leftMul a tv k _ wa (λ ()) (λ ()) (mul-op (ot-plain refl) (unaryL b tv _ r wb nq ad) tl)
  mulL (RBinOp OpMod a b) tv k r (wa , wb) nq ad tl =
    leftMul a tv k _ wa (λ ()) (λ ()) (mul-op (ot-plain refl) (unaryL b tv _ r wb nq ad) tl)
  mulL (RBinOp OpLt a b) tv k r w nq ad tl = mul (unaryL (RBinOp OpLt a b) tv k r w nq ad) tl
  mulL (RBinOp OpLe a b) tv k r w nq ad tl = mul (unaryL (RBinOp OpLe a b) tv k r w nq ad) tl
  mulL (RBinOp OpGt a b) tv k r w nq ad tl = mul (unaryL (RBinOp OpGt a b) tv k r w nq ad) tl
  mulL (RBinOp OpGe a b) tv k r w nq ad tl = mul (unaryL (RBinOp OpGe a b) tv k r w nq ad) tl
  mulL (RBinOp OpEq a b) tv k r w nq ad tl = mul (unaryL (RBinOp OpEq a b) tv k r w nq ad) tl
  mulL (RBinOp OpNe a b) tv k r w nq ad tl = mul (unaryL (RBinOp OpNe a b) tv k r w nq ad) tl
  mulL (RBinOp (Op.dotted o+) a b) tv k r w nq ad tl = mul (unaryL (RBinOp (Op.dotted o+) a b) tv k r w nq ad) tl
  mulL (RBinOp (Op.dotted o-) a b) tv k r w nq ad tl = mul (unaryL (RBinOp (Op.dotted o-) a b) tv k r w nq ad) tl
  mulL (RBinOp (Op.dotted o*) a b) tv k r (wa , wb) nq ad tl =
    leftMul a tv k _ wa (λ ()) (λ ()) (mul-op (ot-dotted refl) (unaryL b tv _ r wb nq ad) tl)
  mulL (RBinOp (Op.dotted o/) a b) tv k r (wa , wb) nq ad tl =
    leftMul a tv k _ wa (λ ()) (λ ()) (mul-op (ot-dotted refl) (unaryL b tv _ r wb nq ad) tl)
  mulL (RBinOp (Op.dotted o<) a b) tv k r w nq ad tl = mul (unaryL (RBinOp (Op.dotted o<) a b) tv k r w nq ad) tl
  mulL (RBinOp (Op.dotted o<=) a b) tv k r w nq ad tl = mul (unaryL (RBinOp (Op.dotted o<=) a b) tv k r w nq ad) tl
  mulL (RBinOp (Op.dotted o>) a b) tv k r w nq ad tl = mul (unaryL (RBinOp (Op.dotted o>) a b) tv k r w nq ad) tl
  mulL (RBinOp (Op.dotted o>=) a b) tv k r w nq ad tl = mul (unaryL (RBinOp (Op.dotted o>=) a b) tv k r w nq ad) tl
  mulL (RBinOp (Op.dotted o==) a b) tv k r w nq ad tl = mul (unaryL (RBinOp (Op.dotted o==) a b) tv k r w nq ad) tl
  mulL (RBinOp (Op.dotted o!=) a b) tv k r w nq ad tl = mul (unaryL (RBinOp (Op.dotted o!=) a b) tv k r w nq ad) tl

  mulApp : ∀ f a b tv k r {e′ r′} → isCompose (headOf f) ≡ b → WF f → WF a → NoQual r → AppDone r → ParsesMulTail (RApp f a) r e′ r′
         → ParsesMul (toks (proj₁ (pcomp 3 b f a tv k)) r) e′ r′
  mulApp f a true tv k r eq wf wa nq ad tl with compose-true f eq
  ... | g , refl = mul (unary (app (composeAtom g a 2 tv k r (proj₂ wf) wa) (app-done ad))) tl
  mulApp f a false tv k r eq wf wa nq ad tl = mul (unary (spineApp f a tv k r wf wa nq (app-done ad))) tl

  leftMul : ∀ a tv k r {e′ r′} → WF a → NoQual r → AppDone r → ParsesMulTail a r e′ r′
          → ParsesMul (toks (proj₁ (pleft 3 a tv k)) r) e′ r′
  leftMul (RBinOp OpAdd x y) tv k r w nq ad tl = mulL (RBinOp OpAdd x y) tv k r w nq ad tl
  leftMul (RBinOp OpSub x y) tv k r w nq ad tl = mulL (RBinOp OpSub x y) tv k r w nq ad tl
  leftMul (RBinOp OpMul x y) tv k r (wx , wy) nq ad tl =
    leftMul x tv k _ wx (λ ()) (λ ()) (mul-op (ot-plain refl) (unaryL y tv _ r wy nq ad) tl)
  leftMul (RBinOp OpDiv x y) tv k r (wx , wy) nq ad tl =
    leftMul x tv k _ wx (λ ()) (λ ()) (mul-op (ot-plain refl) (unaryL y tv _ r wy nq ad) tl)
  leftMul (RBinOp OpMod x y) tv k r (wx , wy) nq ad tl =
    leftMul x tv k _ wx (λ ()) (λ ()) (mul-op (ot-plain refl) (unaryL y tv _ r wy nq ad) tl)
  leftMul (RBinOp OpLt x y) tv k r w nq ad tl = mulL (RBinOp OpLt x y) tv k r w nq ad tl
  leftMul (RBinOp OpLe x y) tv k r w nq ad tl = mulL (RBinOp OpLe x y) tv k r w nq ad tl
  leftMul (RBinOp OpGt x y) tv k r w nq ad tl = mulL (RBinOp OpGt x y) tv k r w nq ad tl
  leftMul (RBinOp OpGe x y) tv k r w nq ad tl = mulL (RBinOp OpGe x y) tv k r w nq ad tl
  leftMul (RBinOp OpEq x y) tv k r w nq ad tl = mulL (RBinOp OpEq x y) tv k r w nq ad tl
  leftMul (RBinOp OpNe x y) tv k r w nq ad tl = mulL (RBinOp OpNe x y) tv k r w nq ad tl
  leftMul (RBinOp (Op.dotted o+) x y) tv k r w nq ad tl = mulL (RBinOp (Op.dotted o+) x y) tv k r w nq ad tl
  leftMul (RBinOp (Op.dotted o-) x y) tv k r w nq ad tl = mulL (RBinOp (Op.dotted o-) x y) tv k r w nq ad tl
  leftMul (RBinOp (Op.dotted o*) x y) tv k r (wx , wy) nq ad tl =
    leftMul x tv k _ wx (λ ()) (λ ()) (mul-op (ot-dotted refl) (unaryL y tv _ r wy nq ad) tl)
  leftMul (RBinOp (Op.dotted o/) x y) tv k r (wx , wy) nq ad tl =
    leftMul x tv k _ wx (λ ()) (λ ()) (mul-op (ot-dotted refl) (unaryL y tv _ r wy nq ad) tl)
  leftMul (RBinOp (Op.dotted o<) x y) tv k r w nq ad tl = mulL (RBinOp (Op.dotted o<) x y) tv k r w nq ad tl
  leftMul (RBinOp (Op.dotted o<=) x y) tv k r w nq ad tl = mulL (RBinOp (Op.dotted o<=) x y) tv k r w nq ad tl
  leftMul (RBinOp (Op.dotted o>) x y) tv k r w nq ad tl = mulL (RBinOp (Op.dotted o>) x y) tv k r w nq ad tl
  leftMul (RBinOp (Op.dotted o>=) x y) tv k r w nq ad tl = mulL (RBinOp (Op.dotted o>=) x y) tv k r w nq ad tl
  leftMul (RBinOp (Op.dotted o==) x y) tv k r w nq ad tl = mulL (RBinOp (Op.dotted o==) x y) tv k r w nq ad tl
  leftMul (RBinOp (Op.dotted o!=) x y) tv k r w nq ad tl = mulL (RBinOp (Op.dotted o!=) x y) tv k r w nq ad tl
  leftMul (RVar x) tv k r w nq ad tl = mulL (RVar x) tv k r w nq ad tl
  leftMul (RQualified x q) tv k r w nq ad tl = mulL (RQualified x q) tv k r w nq ad tl
  leftMul (RResolved n) tv k r w nq ad tl = mulL (RResolved n) tv k r w nq ad tl
  leftMul (RApp f a) tv k r w nq ad tl = mulL (RApp f a) tv k r w nq ad tl
  leftMul (RLam x e) tv k r w nq ad tl = mulL (RLam x e) tv k r w nq ad tl
  leftMul (RLet x v b) tv k r w nq ad tl = mulL (RLet x v b) tv k r w nq ad tl
  leftMul (RPair a b) tv k r w nq ad tl = mulL (RPair a b) tv k r w nq ad tl
  leftMul (RDestruct s x el y er) tv k r w nq ad tl = mulL (RDestruct s x el y er) tv k r w nq ad tl
  leftMul RUnit tv k r w nq ad tl = mulL RUnit tv k r w nq ad tl
  leftMul (RInt (ℤ.+ n)) tv k r w nq ad tl = mulL (RInt (ℤ.+ n)) tv k r w nq ad tl
  leftMul (RInt ℤ.-[1+ n ]) tv k r w nq ad tl = mulL (RInt ℤ.-[1+ n ]) tv k r w nq ad tl
  leftMul (RFloat pos i fr l) tv k r w nq ad tl = mulL (RFloat pos i fr l) tv k r w nq ad tl
  leftMul (RFloat neg i fr l) tv k r w nq ad tl = mulL (RFloat neg i fr l) tv k r w nq ad tl
  leftMul (RAnnot e T) tv k r w nq ad tl = mulL (RAnnot e T) tv k r w nq ad tl
  leftMul (RNeg e) tv k r w nq ad tl = mulL (RNeg e) tv k r w nq ad tl

  -- | `+`, `-` (level 2), with what continues them.
  addL : ∀ e tv k r {e′ r′} → WF e → NoQual r → AppDone r → MulDone r → ParsesAddTail e r e′ r′ → ParsesAdd (E 2 e tv k r) e′ r′
  addL (RApp f a) tv k r (wf , wa) nq ad md tl = addApp f a (isCompose (headOf f)) tv k r refl wf wa nq ad md tl
  addL (RResolved n) tv k r () nq ad md tl
  addL (RVar x) tv k r w nq ad md tl = add (mulL (RVar x) tv k r w nq ad (mul-done md)) tl
  addL (RQualified x q) tv k r w nq ad md tl = add (mulL (RQualified x q) tv k r w nq ad (mul-done md)) tl
  addL (RLam x e) tv k r w nq ad md tl = add (mulL (RLam x e) tv k r w nq ad (mul-done md)) tl
  addL (RLet x v b) tv k r w nq ad md tl = add (mulL (RLet x v b) tv k r w nq ad (mul-done md)) tl
  addL (RPair a b) tv k r w nq ad md tl = add (mulL (RPair a b) tv k r w nq ad (mul-done md)) tl
  addL (RDestruct s x el y er) tv k r w nq ad md tl = add (mulL (RDestruct s x el y er) tv k r w nq ad (mul-done md)) tl
  addL RUnit tv k r w nq ad md tl = add (mulL RUnit tv k r w nq ad (mul-done md)) tl
  addL (RInt (ℤ.+ n)) tv k r w nq ad md tl = add (mulL (RInt (ℤ.+ n)) tv k r w nq ad (mul-done md)) tl
  addL (RInt ℤ.-[1+ n ]) tv k r w nq ad md tl = add (mulL (RInt ℤ.-[1+ n ]) tv k r w nq ad (mul-done md)) tl
  addL (RFloat pos i fr l) tv k r w nq ad md tl = add (mulL (RFloat pos i fr l) tv k r w nq ad (mul-done md)) tl
  addL (RFloat neg i fr l) tv k r w nq ad md tl = add (mulL (RFloat neg i fr l) tv k r w nq ad (mul-done md)) tl
  addL (RAnnot e T) tv k r w nq ad md tl = add (mulL (RAnnot e T) tv k r w nq ad (mul-done md)) tl
  addL (RNeg e) tv k r w nq ad md tl = add (mulL (RNeg e) tv k r w nq ad (mul-done md)) tl
  addL (RBinOp OpAdd a b) tv k r (wa , wb) nq ad md tl =
    leftAdd a tv k _ wa (λ ()) (λ ()) (λ { starts → otherLevel (ot-plain refl) (λ ()) }) (add-op (ot-plain refl) (mulL b tv _ r wb nq ad (mul-done md)) tl)
  addL (RBinOp OpSub a b) tv k r (wa , wb) nq ad md tl =
    leftAdd a tv k _ wa (λ ()) (λ ()) (λ { starts → otherLevel (ot-plain refl) (λ ()) }) (add-op (ot-plain refl) (mulL b tv _ r wb nq ad (mul-done md)) tl)
  addL (RBinOp OpMul a b) tv k r w nq ad md tl = add (mulL (RBinOp OpMul a b) tv k r w nq ad (mul-done md)) tl
  addL (RBinOp OpDiv a b) tv k r w nq ad md tl = add (mulL (RBinOp OpDiv a b) tv k r w nq ad (mul-done md)) tl
  addL (RBinOp OpMod a b) tv k r w nq ad md tl = add (mulL (RBinOp OpMod a b) tv k r w nq ad (mul-done md)) tl
  addL (RBinOp OpLt a b) tv k r w nq ad md tl = add (mulL (RBinOp OpLt a b) tv k r w nq ad (mul-done md)) tl
  addL (RBinOp OpLe a b) tv k r w nq ad md tl = add (mulL (RBinOp OpLe a b) tv k r w nq ad (mul-done md)) tl
  addL (RBinOp OpGt a b) tv k r w nq ad md tl = add (mulL (RBinOp OpGt a b) tv k r w nq ad (mul-done md)) tl
  addL (RBinOp OpGe a b) tv k r w nq ad md tl = add (mulL (RBinOp OpGe a b) tv k r w nq ad (mul-done md)) tl
  addL (RBinOp OpEq a b) tv k r w nq ad md tl = add (mulL (RBinOp OpEq a b) tv k r w nq ad (mul-done md)) tl
  addL (RBinOp OpNe a b) tv k r w nq ad md tl = add (mulL (RBinOp OpNe a b) tv k r w nq ad (mul-done md)) tl
  addL (RBinOp (Op.dotted o+) a b) tv k r (wa , wb) nq ad md tl =
    leftAdd a tv k _ wa (λ ()) (λ ()) (λ { starts → otherLevel (ot-dotted refl) (λ ()) }) (add-op (ot-dotted refl) (mulL b tv _ r wb nq ad (mul-done md)) tl)
  addL (RBinOp (Op.dotted o-) a b) tv k r (wa , wb) nq ad md tl =
    leftAdd a tv k _ wa (λ ()) (λ ()) (λ { starts → otherLevel (ot-dotted refl) (λ ()) }) (add-op (ot-dotted refl) (mulL b tv _ r wb nq ad (mul-done md)) tl)
  addL (RBinOp (Op.dotted o*) a b) tv k r w nq ad md tl = add (mulL (RBinOp (Op.dotted o*) a b) tv k r w nq ad (mul-done md)) tl
  addL (RBinOp (Op.dotted o/) a b) tv k r w nq ad md tl = add (mulL (RBinOp (Op.dotted o/) a b) tv k r w nq ad (mul-done md)) tl
  addL (RBinOp (Op.dotted o<) a b) tv k r w nq ad md tl = add (mulL (RBinOp (Op.dotted o<) a b) tv k r w nq ad (mul-done md)) tl
  addL (RBinOp (Op.dotted o<=) a b) tv k r w nq ad md tl = add (mulL (RBinOp (Op.dotted o<=) a b) tv k r w nq ad (mul-done md)) tl
  addL (RBinOp (Op.dotted o>) a b) tv k r w nq ad md tl = add (mulL (RBinOp (Op.dotted o>) a b) tv k r w nq ad (mul-done md)) tl
  addL (RBinOp (Op.dotted o>=) a b) tv k r w nq ad md tl = add (mulL (RBinOp (Op.dotted o>=) a b) tv k r w nq ad (mul-done md)) tl
  addL (RBinOp (Op.dotted o==) a b) tv k r w nq ad md tl = add (mulL (RBinOp (Op.dotted o==) a b) tv k r w nq ad (mul-done md)) tl
  addL (RBinOp (Op.dotted o!=) a b) tv k r w nq ad md tl = add (mulL (RBinOp (Op.dotted o!=) a b) tv k r w nq ad (mul-done md)) tl

  addApp : ∀ f a b tv k r {e′ r′} → isCompose (headOf f) ≡ b → WF f → WF a → NoQual r → AppDone r → MulDone r
         → ParsesAddTail (RApp f a) r e′ r′ → ParsesAdd (toks (proj₁ (pcomp 2 b f a tv k)) r) e′ r′
  addApp f a true tv k r eq wf wa nq ad md tl with compose-true f eq
  ... | g , refl = add (mul (unary (app (composeAtom g a 1 tv k r (proj₂ wf) wa) (app-done ad))) (mul-done md)) tl
  addApp f a false tv k r eq wf wa nq ad md tl = add (mul (unary (spineApp f a tv k r wf wa nq (app-done ad))) (mul-done md)) tl

  leftAdd : ∀ a tv k r {e′ r′} → WF a → NoQual r → AppDone r → MulDone r → ParsesAddTail a r e′ r′
          → ParsesAdd (toks (proj₁ (pleft 2 a tv k)) r) e′ r′
  leftAdd (RBinOp OpAdd x y) tv k r (wx , wy) nq ad md tl =
    leftAdd x tv k _ wx (λ ()) (λ ()) (λ { starts → otherLevel (ot-plain refl) (λ ()) }) (add-op (ot-plain refl) (mulL y tv _ r wy nq ad (mul-done md)) tl)
  leftAdd (RBinOp OpSub x y) tv k r (wx , wy) nq ad md tl =
    leftAdd x tv k _ wx (λ ()) (λ ()) (λ { starts → otherLevel (ot-plain refl) (λ ()) }) (add-op (ot-plain refl) (mulL y tv _ r wy nq ad (mul-done md)) tl)
  leftAdd (RBinOp OpMul x y) tv k r w nq ad md tl = addL (RBinOp OpMul x y) tv k r w nq ad md tl
  leftAdd (RBinOp OpDiv x y) tv k r w nq ad md tl = addL (RBinOp OpDiv x y) tv k r w nq ad md tl
  leftAdd (RBinOp OpMod x y) tv k r w nq ad md tl = addL (RBinOp OpMod x y) tv k r w nq ad md tl
  leftAdd (RBinOp OpLt x y) tv k r w nq ad md tl = addL (RBinOp OpLt x y) tv k r w nq ad md tl
  leftAdd (RBinOp OpLe x y) tv k r w nq ad md tl = addL (RBinOp OpLe x y) tv k r w nq ad md tl
  leftAdd (RBinOp OpGt x y) tv k r w nq ad md tl = addL (RBinOp OpGt x y) tv k r w nq ad md tl
  leftAdd (RBinOp OpGe x y) tv k r w nq ad md tl = addL (RBinOp OpGe x y) tv k r w nq ad md tl
  leftAdd (RBinOp OpEq x y) tv k r w nq ad md tl = addL (RBinOp OpEq x y) tv k r w nq ad md tl
  leftAdd (RBinOp OpNe x y) tv k r w nq ad md tl = addL (RBinOp OpNe x y) tv k r w nq ad md tl
  leftAdd (RBinOp (Op.dotted o+) x y) tv k r (wx , wy) nq ad md tl =
    leftAdd x tv k _ wx (λ ()) (λ ()) (λ { starts → otherLevel (ot-dotted refl) (λ ()) }) (add-op (ot-dotted refl) (mulL y tv _ r wy nq ad (mul-done md)) tl)
  leftAdd (RBinOp (Op.dotted o-) x y) tv k r (wx , wy) nq ad md tl =
    leftAdd x tv k _ wx (λ ()) (λ ()) (λ { starts → otherLevel (ot-dotted refl) (λ ()) }) (add-op (ot-dotted refl) (mulL y tv _ r wy nq ad (mul-done md)) tl)
  leftAdd (RBinOp (Op.dotted o*) x y) tv k r w nq ad md tl = addL (RBinOp (Op.dotted o*) x y) tv k r w nq ad md tl
  leftAdd (RBinOp (Op.dotted o/) x y) tv k r w nq ad md tl = addL (RBinOp (Op.dotted o/) x y) tv k r w nq ad md tl
  leftAdd (RBinOp (Op.dotted o<) x y) tv k r w nq ad md tl = addL (RBinOp (Op.dotted o<) x y) tv k r w nq ad md tl
  leftAdd (RBinOp (Op.dotted o<=) x y) tv k r w nq ad md tl = addL (RBinOp (Op.dotted o<=) x y) tv k r w nq ad md tl
  leftAdd (RBinOp (Op.dotted o>) x y) tv k r w nq ad md tl = addL (RBinOp (Op.dotted o>) x y) tv k r w nq ad md tl
  leftAdd (RBinOp (Op.dotted o>=) x y) tv k r w nq ad md tl = addL (RBinOp (Op.dotted o>=) x y) tv k r w nq ad md tl
  leftAdd (RBinOp (Op.dotted o==) x y) tv k r w nq ad md tl = addL (RBinOp (Op.dotted o==) x y) tv k r w nq ad md tl
  leftAdd (RBinOp (Op.dotted o!=) x y) tv k r w nq ad md tl = addL (RBinOp (Op.dotted o!=) x y) tv k r w nq ad md tl
  leftAdd (RVar x) tv k r w nq ad md tl = addL (RVar x) tv k r w nq ad md tl
  leftAdd (RQualified x q) tv k r w nq ad md tl = addL (RQualified x q) tv k r w nq ad md tl
  leftAdd (RResolved n) tv k r w nq ad md tl = addL (RResolved n) tv k r w nq ad md tl
  leftAdd (RApp f a) tv k r w nq ad md tl = addL (RApp f a) tv k r w nq ad md tl
  leftAdd (RLam x e) tv k r w nq ad md tl = addL (RLam x e) tv k r w nq ad md tl
  leftAdd (RLet x v b) tv k r w nq ad md tl = addL (RLet x v b) tv k r w nq ad md tl
  leftAdd (RPair a b) tv k r w nq ad md tl = addL (RPair a b) tv k r w nq ad md tl
  leftAdd (RDestruct s x el y er) tv k r w nq ad md tl = addL (RDestruct s x el y er) tv k r w nq ad md tl
  leftAdd RUnit tv k r w nq ad md tl = addL RUnit tv k r w nq ad md tl
  leftAdd (RInt (ℤ.+ n)) tv k r w nq ad md tl = addL (RInt (ℤ.+ n)) tv k r w nq ad md tl
  leftAdd (RInt ℤ.-[1+ n ]) tv k r w nq ad md tl = addL (RInt ℤ.-[1+ n ]) tv k r w nq ad md tl
  leftAdd (RFloat pos i fr l) tv k r w nq ad md tl = addL (RFloat pos i fr l) tv k r w nq ad md tl
  leftAdd (RFloat neg i fr l) tv k r w nq ad md tl = addL (RFloat neg i fr l) tv k r w nq ad md tl
  leftAdd (RAnnot e T) tv k r w nq ad md tl = addL (RAnnot e T) tv k r w nq ad md tl
  leftAdd (RNeg e) tv k r w nq ad md tl = addL (RNeg e) tv k r w nq ad md tl

  -- | A comparison (level 1).
  cmpL : ∀ e tv k r → WF e → NoQual r → AppDone r → MulDone r → AddDone r → CmpDone r → ParsesCmp (E 1 e tv k r) e r
  cmpL (RApp f a) tv k r (wf , wa) nq ad md dd cd = cmpApp f a (isCompose (headOf f)) tv k r refl wf wa nq ad md dd cd
  cmpL (RResolved n) tv k r () nq ad md dd cd
  cmpL (RVar x) tv k r w nq ad md dd cd = cmp-none (addL (RVar x) tv k r w nq ad md (add-done dd)) cd
  cmpL (RQualified x q) tv k r w nq ad md dd cd = cmp-none (addL (RQualified x q) tv k r w nq ad md (add-done dd)) cd
  cmpL (RLam x e) tv k r w nq ad md dd cd = cmp-none (addL (RLam x e) tv k r w nq ad md (add-done dd)) cd
  cmpL (RLet x v b) tv k r w nq ad md dd cd = cmp-none (addL (RLet x v b) tv k r w nq ad md (add-done dd)) cd
  cmpL (RPair a b) tv k r w nq ad md dd cd = cmp-none (addL (RPair a b) tv k r w nq ad md (add-done dd)) cd
  cmpL (RDestruct s x el y er) tv k r w nq ad md dd cd = cmp-none (addL (RDestruct s x el y er) tv k r w nq ad md (add-done dd)) cd
  cmpL RUnit tv k r w nq ad md dd cd = cmp-none (addL RUnit tv k r w nq ad md (add-done dd)) cd
  cmpL (RInt (ℤ.+ n)) tv k r w nq ad md dd cd = cmp-none (addL (RInt (ℤ.+ n)) tv k r w nq ad md (add-done dd)) cd
  cmpL (RInt ℤ.-[1+ n ]) tv k r w nq ad md dd cd = cmp-none (addL (RInt ℤ.-[1+ n ]) tv k r w nq ad md (add-done dd)) cd
  cmpL (RFloat pos i fr l) tv k r w nq ad md dd cd = cmp-none (addL (RFloat pos i fr l) tv k r w nq ad md (add-done dd)) cd
  cmpL (RFloat neg i fr l) tv k r w nq ad md dd cd = cmp-none (addL (RFloat neg i fr l) tv k r w nq ad md (add-done dd)) cd
  cmpL (RAnnot e T) tv k r w nq ad md dd cd = cmp-none (addL (RAnnot e T) tv k r w nq ad md (add-done dd)) cd
  cmpL (RNeg e) tv k r w nq ad md dd cd = cmp-none (addL (RNeg e) tv k r w nq ad md (add-done dd)) cd
  cmpL (RBinOp OpAdd a b) tv k r w nq ad md dd cd = cmp-none (addL (RBinOp OpAdd a b) tv k r w nq ad md (add-done dd)) cd
  cmpL (RBinOp OpSub a b) tv k r w nq ad md dd cd = cmp-none (addL (RBinOp OpSub a b) tv k r w nq ad md (add-done dd)) cd
  cmpL (RBinOp OpMul a b) tv k r w nq ad md dd cd = cmp-none (addL (RBinOp OpMul a b) tv k r w nq ad md (add-done dd)) cd
  cmpL (RBinOp OpDiv a b) tv k r w nq ad md dd cd = cmp-none (addL (RBinOp OpDiv a b) tv k r w nq ad md (add-done dd)) cd
  cmpL (RBinOp OpMod a b) tv k r w nq ad md dd cd = cmp-none (addL (RBinOp OpMod a b) tv k r w nq ad md (add-done dd)) cd
  cmpL (RBinOp OpLt a b) tv k r (wa , wb) nq ad md dd cd =
    cmp (ot-plain refl) (leftCmp a tv k _ wa (λ ()) (λ ()) (λ { starts → otherLevel (ot-plain refl) (λ ()) }) (λ { starts → otherLevel (ot-plain refl) (λ ()) })) (addL b tv _ r wb nq ad md (add-done dd))
  cmpL (RBinOp OpLe a b) tv k r (wa , wb) nq ad md dd cd =
    cmp (ot-plain refl) (leftCmp a tv k _ wa (λ ()) (λ ()) (λ { starts → otherLevel (ot-plain refl) (λ ()) }) (λ { starts → otherLevel (ot-plain refl) (λ ()) })) (addL b tv _ r wb nq ad md (add-done dd))
  cmpL (RBinOp OpGt a b) tv k r (wa , wb) nq ad md dd cd =
    cmp (ot-plain refl) (leftCmp a tv k _ wa (λ ()) (λ ()) (λ { starts → otherLevel (ot-plain refl) (λ ()) }) (λ { starts → otherLevel (ot-plain refl) (λ ()) })) (addL b tv _ r wb nq ad md (add-done dd))
  cmpL (RBinOp OpGe a b) tv k r (wa , wb) nq ad md dd cd =
    cmp (ot-plain refl) (leftCmp a tv k _ wa (λ ()) (λ ()) (λ { starts → otherLevel (ot-plain refl) (λ ()) }) (λ { starts → otherLevel (ot-plain refl) (λ ()) })) (addL b tv _ r wb nq ad md (add-done dd))
  cmpL (RBinOp OpEq a b) tv k r (wa , wb) nq ad md dd cd =
    cmp (ot-plain refl) (leftCmp a tv k _ wa (λ ()) (λ ()) (λ { starts → otherLevel (ot-plain refl) (λ ()) }) (λ { starts → otherLevel (ot-plain refl) (λ ()) })) (addL b tv _ r wb nq ad md (add-done dd))
  cmpL (RBinOp OpNe a b) tv k r (wa , wb) nq ad md dd cd =
    cmp (ot-plain refl) (leftCmp a tv k _ wa (λ ()) (λ ()) (λ { starts → otherLevel (ot-plain refl) (λ ()) }) (λ { starts → otherLevel (ot-plain refl) (λ ()) })) (addL b tv _ r wb nq ad md (add-done dd))
  cmpL (RBinOp (Op.dotted o+) a b) tv k r w nq ad md dd cd = cmp-none (addL (RBinOp (Op.dotted o+) a b) tv k r w nq ad md (add-done dd)) cd
  cmpL (RBinOp (Op.dotted o-) a b) tv k r w nq ad md dd cd = cmp-none (addL (RBinOp (Op.dotted o-) a b) tv k r w nq ad md (add-done dd)) cd
  cmpL (RBinOp (Op.dotted o*) a b) tv k r w nq ad md dd cd = cmp-none (addL (RBinOp (Op.dotted o*) a b) tv k r w nq ad md (add-done dd)) cd
  cmpL (RBinOp (Op.dotted o/) a b) tv k r w nq ad md dd cd = cmp-none (addL (RBinOp (Op.dotted o/) a b) tv k r w nq ad md (add-done dd)) cd
  cmpL (RBinOp (Op.dotted o<) a b) tv k r (wa , wb) nq ad md dd cd =
    cmp (ot-dotted refl) (leftCmp a tv k _ wa (λ ()) (λ ()) (λ { starts → otherLevel (ot-dotted refl) (λ ()) }) (λ { starts → otherLevel (ot-dotted refl) (λ ()) })) (addL b tv _ r wb nq ad md (add-done dd))
  cmpL (RBinOp (Op.dotted o<=) a b) tv k r (wa , wb) nq ad md dd cd =
    cmp (ot-dotted refl) (leftCmp a tv k _ wa (λ ()) (λ ()) (λ { starts → otherLevel (ot-dotted refl) (λ ()) }) (λ { starts → otherLevel (ot-dotted refl) (λ ()) })) (addL b tv _ r wb nq ad md (add-done dd))
  cmpL (RBinOp (Op.dotted o>) a b) tv k r (wa , wb) nq ad md dd cd =
    cmp (ot-dotted refl) (leftCmp a tv k _ wa (λ ()) (λ ()) (λ { starts → otherLevel (ot-dotted refl) (λ ()) }) (λ { starts → otherLevel (ot-dotted refl) (λ ()) })) (addL b tv _ r wb nq ad md (add-done dd))
  cmpL (RBinOp (Op.dotted o>=) a b) tv k r (wa , wb) nq ad md dd cd =
    cmp (ot-dotted refl) (leftCmp a tv k _ wa (λ ()) (λ ()) (λ { starts → otherLevel (ot-dotted refl) (λ ()) }) (λ { starts → otherLevel (ot-dotted refl) (λ ()) })) (addL b tv _ r wb nq ad md (add-done dd))
  cmpL (RBinOp (Op.dotted o==) a b) tv k r (wa , wb) nq ad md dd cd =
    cmp (ot-dotted refl) (leftCmp a tv k _ wa (λ ()) (λ ()) (λ { starts → otherLevel (ot-dotted refl) (λ ()) }) (λ { starts → otherLevel (ot-dotted refl) (λ ()) })) (addL b tv _ r wb nq ad md (add-done dd))
  cmpL (RBinOp (Op.dotted o!=) a b) tv k r (wa , wb) nq ad md dd cd =
    cmp (ot-dotted refl) (leftCmp a tv k _ wa (λ ()) (λ ()) (λ { starts → otherLevel (ot-dotted refl) (λ ()) }) (λ { starts → otherLevel (ot-dotted refl) (λ ()) })) (addL b tv _ r wb nq ad md (add-done dd))

  cmpApp : ∀ f a b tv k r → isCompose (headOf f) ≡ b → WF f → WF a → NoQual r → AppDone r → MulDone r → AddDone r → CmpDone r
         → ParsesCmp (toks (proj₁ (pcomp 1 b f a tv k)) r) (RApp f a) r
  cmpApp f a true tv k r eq wf wa nq ad md dd cd with compose-true f eq
  ... | g , refl = cmp-none (add (mul (unary (app (composeAtom g a 0 tv k r (proj₂ wf) wa) (app-done ad))) (mul-done md)) (add-done dd)) cd
  cmpApp f a false tv k r eq wf wa nq ad md dd cd =
    cmp-none (add (mul (unary (spineApp f a tv k r wf wa nq (app-done ad))) (mul-done md)) (add-done dd)) cd

  -- A comparison's left operand: a sum.
  leftCmp : ∀ a tv k r → WF a → NoQual r → AppDone r → MulDone r → AddDone r → ParsesAdd (toks (proj₁ (pleft 1 a tv k)) r) a r
  leftCmp (RBinOp OpAdd x y) tv k r w nq ad md dd = addL (RBinOp OpAdd x y) tv k r w nq ad md (add-done dd)
  leftCmp (RBinOp OpSub x y) tv k r w nq ad md dd = addL (RBinOp OpSub x y) tv k r w nq ad md (add-done dd)
  leftCmp (RBinOp OpMul x y) tv k r w nq ad md dd = addL (RBinOp OpMul x y) tv k r w nq ad md (add-done dd)
  leftCmp (RBinOp OpDiv x y) tv k r w nq ad md dd = addL (RBinOp OpDiv x y) tv k r w nq ad md (add-done dd)
  leftCmp (RBinOp OpMod x y) tv k r w nq ad md dd = addL (RBinOp OpMod x y) tv k r w nq ad md (add-done dd)
  leftCmp (RBinOp OpLt x y) tv k r w nq ad md dd = addL (RBinOp OpLt x y) tv k r w nq ad md (add-done dd)
  leftCmp (RBinOp OpLe x y) tv k r w nq ad md dd = addL (RBinOp OpLe x y) tv k r w nq ad md (add-done dd)
  leftCmp (RBinOp OpGt x y) tv k r w nq ad md dd = addL (RBinOp OpGt x y) tv k r w nq ad md (add-done dd)
  leftCmp (RBinOp OpGe x y) tv k r w nq ad md dd = addL (RBinOp OpGe x y) tv k r w nq ad md (add-done dd)
  leftCmp (RBinOp OpEq x y) tv k r w nq ad md dd = addL (RBinOp OpEq x y) tv k r w nq ad md (add-done dd)
  leftCmp (RBinOp OpNe x y) tv k r w nq ad md dd = addL (RBinOp OpNe x y) tv k r w nq ad md (add-done dd)
  leftCmp (RBinOp (Op.dotted o+) x y) tv k r w nq ad md dd = addL (RBinOp (Op.dotted o+) x y) tv k r w nq ad md (add-done dd)
  leftCmp (RBinOp (Op.dotted o-) x y) tv k r w nq ad md dd = addL (RBinOp (Op.dotted o-) x y) tv k r w nq ad md (add-done dd)
  leftCmp (RBinOp (Op.dotted o*) x y) tv k r w nq ad md dd = addL (RBinOp (Op.dotted o*) x y) tv k r w nq ad md (add-done dd)
  leftCmp (RBinOp (Op.dotted o/) x y) tv k r w nq ad md dd = addL (RBinOp (Op.dotted o/) x y) tv k r w nq ad md (add-done dd)
  leftCmp (RBinOp (Op.dotted o<) x y) tv k r w nq ad md dd = addL (RBinOp (Op.dotted o<) x y) tv k r w nq ad md (add-done dd)
  leftCmp (RBinOp (Op.dotted o<=) x y) tv k r w nq ad md dd = addL (RBinOp (Op.dotted o<=) x y) tv k r w nq ad md (add-done dd)
  leftCmp (RBinOp (Op.dotted o>) x y) tv k r w nq ad md dd = addL (RBinOp (Op.dotted o>) x y) tv k r w nq ad md (add-done dd)
  leftCmp (RBinOp (Op.dotted o>=) x y) tv k r w nq ad md dd = addL (RBinOp (Op.dotted o>=) x y) tv k r w nq ad md (add-done dd)
  leftCmp (RBinOp (Op.dotted o==) x y) tv k r w nq ad md dd = addL (RBinOp (Op.dotted o==) x y) tv k r w nq ad md (add-done dd)
  leftCmp (RBinOp (Op.dotted o!=) x y) tv k r w nq ad md dd = addL (RBinOp (Op.dotted o!=) x y) tv k r w nq ad md (add-done dd)
  leftCmp (RVar x) tv k r w nq ad md dd = addL (RVar x) tv k r w nq ad md (add-done dd)
  leftCmp (RQualified x q) tv k r w nq ad md dd = addL (RQualified x q) tv k r w nq ad md (add-done dd)
  leftCmp (RResolved n) tv k r w nq ad md dd = addL (RResolved n) tv k r w nq ad md (add-done dd)
  leftCmp (RApp f a) tv k r w nq ad md dd = addL (RApp f a) tv k r w nq ad md (add-done dd)
  leftCmp (RLam x e) tv k r w nq ad md dd = addL (RLam x e) tv k r w nq ad md (add-done dd)
  leftCmp (RLet x v b) tv k r w nq ad md dd = addL (RLet x v b) tv k r w nq ad md (add-done dd)
  leftCmp (RPair a b) tv k r w nq ad md dd = addL (RPair a b) tv k r w nq ad md (add-done dd)
  leftCmp (RDestruct s x el y er) tv k r w nq ad md dd = addL (RDestruct s x el y er) tv k r w nq ad md (add-done dd)
  leftCmp RUnit tv k r w nq ad md dd = addL RUnit tv k r w nq ad md (add-done dd)
  leftCmp (RInt (ℤ.+ n)) tv k r w nq ad md dd = addL (RInt (ℤ.+ n)) tv k r w nq ad md (add-done dd)
  leftCmp (RInt ℤ.-[1+ n ]) tv k r w nq ad md dd = addL (RInt ℤ.-[1+ n ]) tv k r w nq ad md (add-done dd)
  leftCmp (RFloat pos i fr l) tv k r w nq ad md dd = addL (RFloat pos i fr l) tv k r w nq ad md (add-done dd)
  leftCmp (RFloat neg i fr l) tv k r w nq ad md dd = addL (RFloat neg i fr l) tv k r w nq ad md (add-done dd)
  leftCmp (RAnnot e T) tv k r w nq ad md dd = addL (RAnnot e T) tv k r w nq ad md (add-done dd)
  leftCmp (RNeg e) tv k r w nq ad md dd = addL (RNeg e) tv k r w nq ad md (add-done dd)

  -- | A whole expression: nothing of it follows.
  wholeL : ∀ e tv k r → WF e → Stops r → ParsesExpr (toks (proj₁ (pex 0 true e tv k)) r) e r
  wholeL (RLam x e) tv k r w st = atom→expr st (lamA x e tv k r w st)
  wholeL (RLet x v b) tv k r w st = atom→expr st (letA x v b tv k r w st)
  wholeL (RDestruct s x el y er) tv k r w st = atom→expr st (desA s x el y er tv k r w st)
  wholeL (RApp f a) tv k r (wf , wa) st = wholeApp f a (isCompose (headOf f)) tv k r refl wf wa st
  wholeL (RResolved n) tv k r () st
  wholeL (RVar x) tv k r w (stops sq sa sm sd sc so) = expr (cmpL (RVar x) tv k r w sq sa sm sd sc) (comp-done so)
  wholeL (RQualified x q) tv k r w (stops sq sa sm sd sc so) = expr (cmpL (RQualified x q) tv k r w sq sa sm sd sc) (comp-done so)
  wholeL (RPair a b) tv k r w (stops sq sa sm sd sc so) = expr (cmpL (RPair a b) tv k r w sq sa sm sd sc) (comp-done so)
  wholeL RUnit tv k r w (stops sq sa sm sd sc so) = expr (cmpL RUnit tv k r w sq sa sm sd sc) (comp-done so)
  wholeL (RInt (ℤ.+ n)) tv k r w (stops sq sa sm sd sc so) = expr (cmpL (RInt (ℤ.+ n)) tv k r w sq sa sm sd sc) (comp-done so)
  wholeL (RInt ℤ.-[1+ n ]) tv k r w (stops sq sa sm sd sc so) = expr (cmpL (RInt ℤ.-[1+ n ]) tv k r w sq sa sm sd sc) (comp-done so)
  wholeL (RFloat pos i fr l) tv k r w (stops sq sa sm sd sc so) = expr (cmpL (RFloat pos i fr l) tv k r w sq sa sm sd sc) (comp-done so)
  wholeL (RFloat neg i fr l) tv k r w (stops sq sa sm sd sc so) = expr (cmpL (RFloat neg i fr l) tv k r w sq sa sm sd sc) (comp-done so)
  wholeL (RAnnot e T) tv k r w (stops sq sa sm sd sc so) = expr (cmpL (RAnnot e T) tv k r w sq sa sm sd sc) (comp-done so)
  wholeL (RNeg e) tv k r w (stops sq sa sm sd sc so) = expr (cmpL (RNeg e) tv k r w sq sa sm sd sc) (comp-done so)
  wholeL (RBinOp OpAdd x y) tv k r w (stops sq sa sm sd sc so) = expr (cmpL (RBinOp OpAdd x y) tv k r w sq sa sm sd sc) (comp-done so)
  wholeL (RBinOp OpSub x y) tv k r w (stops sq sa sm sd sc so) = expr (cmpL (RBinOp OpSub x y) tv k r w sq sa sm sd sc) (comp-done so)
  wholeL (RBinOp OpMul x y) tv k r w (stops sq sa sm sd sc so) = expr (cmpL (RBinOp OpMul x y) tv k r w sq sa sm sd sc) (comp-done so)
  wholeL (RBinOp OpDiv x y) tv k r w (stops sq sa sm sd sc so) = expr (cmpL (RBinOp OpDiv x y) tv k r w sq sa sm sd sc) (comp-done so)
  wholeL (RBinOp OpMod x y) tv k r w (stops sq sa sm sd sc so) = expr (cmpL (RBinOp OpMod x y) tv k r w sq sa sm sd sc) (comp-done so)
  wholeL (RBinOp OpLt x y) tv k r w (stops sq sa sm sd sc so) = expr (cmpL (RBinOp OpLt x y) tv k r w sq sa sm sd sc) (comp-done so)
  wholeL (RBinOp OpLe x y) tv k r w (stops sq sa sm sd sc so) = expr (cmpL (RBinOp OpLe x y) tv k r w sq sa sm sd sc) (comp-done so)
  wholeL (RBinOp OpGt x y) tv k r w (stops sq sa sm sd sc so) = expr (cmpL (RBinOp OpGt x y) tv k r w sq sa sm sd sc) (comp-done so)
  wholeL (RBinOp OpGe x y) tv k r w (stops sq sa sm sd sc so) = expr (cmpL (RBinOp OpGe x y) tv k r w sq sa sm sd sc) (comp-done so)
  wholeL (RBinOp OpEq x y) tv k r w (stops sq sa sm sd sc so) = expr (cmpL (RBinOp OpEq x y) tv k r w sq sa sm sd sc) (comp-done so)
  wholeL (RBinOp OpNe x y) tv k r w (stops sq sa sm sd sc so) = expr (cmpL (RBinOp OpNe x y) tv k r w sq sa sm sd sc) (comp-done so)
  wholeL (RBinOp (Op.dotted o+) x y) tv k r w (stops sq sa sm sd sc so) = expr (cmpL (RBinOp (Op.dotted o+) x y) tv k r w sq sa sm sd sc) (comp-done so)
  wholeL (RBinOp (Op.dotted o-) x y) tv k r w (stops sq sa sm sd sc so) = expr (cmpL (RBinOp (Op.dotted o-) x y) tv k r w sq sa sm sd sc) (comp-done so)
  wholeL (RBinOp (Op.dotted o*) x y) tv k r w (stops sq sa sm sd sc so) = expr (cmpL (RBinOp (Op.dotted o*) x y) tv k r w sq sa sm sd sc) (comp-done so)
  wholeL (RBinOp (Op.dotted o/) x y) tv k r w (stops sq sa sm sd sc so) = expr (cmpL (RBinOp (Op.dotted o/) x y) tv k r w sq sa sm sd sc) (comp-done so)
  wholeL (RBinOp (Op.dotted o<) x y) tv k r w (stops sq sa sm sd sc so) = expr (cmpL (RBinOp (Op.dotted o<) x y) tv k r w sq sa sm sd sc) (comp-done so)
  wholeL (RBinOp (Op.dotted o<=) x y) tv k r w (stops sq sa sm sd sc so) = expr (cmpL (RBinOp (Op.dotted o<=) x y) tv k r w sq sa sm sd sc) (comp-done so)
  wholeL (RBinOp (Op.dotted o>) x y) tv k r w (stops sq sa sm sd sc so) = expr (cmpL (RBinOp (Op.dotted o>) x y) tv k r w sq sa sm sd sc) (comp-done so)
  wholeL (RBinOp (Op.dotted o>=) x y) tv k r w (stops sq sa sm sd sc so) = expr (cmpL (RBinOp (Op.dotted o>=) x y) tv k r w sq sa sm sd sc) (comp-done so)
  wholeL (RBinOp (Op.dotted o==) x y) tv k r w (stops sq sa sm sd sc so) = expr (cmpL (RBinOp (Op.dotted o==) x y) tv k r w sq sa sm sd sc) (comp-done so)
  wholeL (RBinOp (Op.dotted o!=) x y) tv k r w (stops sq sa sm sd sc so) = expr (cmpL (RBinOp (Op.dotted o!=) x y) tv k r w sq sa sm sd sc) (comp-done so)

  wholeApp : ∀ f a b tv k r → isCompose (headOf f) ≡ b → WF f → WF a → Stops r
           → ParsesExpr (toks (proj₁ (pcomp 0 b f a tv k)) r) (RApp f a) r
  wholeApp f a true tv k r eq wf wa (stops q ad m d c o) with compose-true f eq
  ... | g , refl = composeL g a tv k r (proj₂ wf) wa q ad m d c (comp-done o)
  wholeApp f a false tv k r eq wf wa st@(stops q ad m d c o) = app→expr st (spineApp f a tv k r wf wa q (app-done ad))

  -- `\x y -> b`, `let`, `destruct`.
  lamA : ∀ x e tv k r → WF e → Stops r → ParsesAtomExpr (toks (proj₁ (plam x e tv k)) r) (RLam x e) r
  lamA x e tv k r w st =
    subst (λ ts → ParsesAtomExpr (TLambda ∷ ts) (RLam x e) r) (sym (word-toks x tv k _))
      (atom-lambda (lam-arg (paramsL e tv _ r w st)))

  paramsL : ∀ e tv k r → WF e → Stops r → ParsesLamParams (toks (proj₁ (plam′ e tv k)) r) e r
  paramsL (RLam y e) tv k r w st =
    subst (λ ts → ParsesLamParams ts (RLam y e) r) (sym (word-toks y tv k _)) (lam-arg (paramsL e tv _ r w st))
  paramsL (RVar x) tv k r w st = lam-body (wholeL (RVar x) tv k r w st)
  paramsL (RQualified x q) tv k r w st = lam-body (wholeL (RQualified x q) tv k r w st)
  paramsL (RResolved n) tv k r w st = lam-body (wholeL (RResolved n) tv k r w st)
  paramsL (RApp f a) tv k r w st = lam-body (wholeL (RApp f a) tv k r w st)
  paramsL (RLet x v b) tv k r w st = lam-body (wholeL (RLet x v b) tv k r w st)
  paramsL (RPair a b) tv k r w st = lam-body (wholeL (RPair a b) tv k r w st)
  paramsL (RDestruct s x el y er) tv k r w st = lam-body (wholeL (RDestruct s x el y er) tv k r w st)
  paramsL RUnit tv k r w st = lam-body (wholeL RUnit tv k r w st)
  paramsL (RInt (ℤ.+ n)) tv k r w st = lam-body (wholeL (RInt (ℤ.+ n)) tv k r w st)
  paramsL (RInt ℤ.-[1+ n ]) tv k r w st = lam-body (wholeL (RInt ℤ.-[1+ n ]) tv k r w st)
  paramsL (RFloat pos i fr l) tv k r w st = lam-body (wholeL (RFloat pos i fr l) tv k r w st)
  paramsL (RFloat neg i fr l) tv k r w st = lam-body (wholeL (RFloat neg i fr l) tv k r w st)
  paramsL (RAnnot e T) tv k r w st = lam-body (wholeL (RAnnot e T) tv k r w st)
  paramsL (RBinOp op a b) tv k r w st = lam-body (wholeL (RBinOp op a b) tv k r w st)
  paramsL (RNeg e) tv k r w st = lam-body (wholeL (RNeg e) tv k r w st)

  letA : ∀ x v b tv k r → WF (RLet x v b) → Stops r → ParsesAtomExpr (toks (proj₁ (plet′ x v b tv k)) r) (RLet x v b) r
  letA x v (RVar bx) tv k r (wv , wb) st =
    subst (λ ts → ParsesAtomExpr ts _ r) (sym (word-toks "let" tv k _))
      (subst (λ ts → ParsesAtomExpr (TWord "let" ∷ ts) _ r) (sym (word-toks x tv _ _))
        (subst (λ ts → ParsesAtomExpr (TWord "let" ∷ TWord x ∷ TEquals ∷ toks (proj₁ (pex 0 true v tv _)) ts) _ r)
          (sym (word-toks "in" tv _ _))
          (atom-let (wholeL v tv _ _ wv stops-in) (wholeL (RVar bx) tv _ r wb st))))
  letA x v (RQualified bx bq) tv k r (wv , wb) st =
    subst (λ ts → ParsesAtomExpr ts _ r) (sym (word-toks "let" tv k _))
      (subst (λ ts → ParsesAtomExpr (TWord "let" ∷ ts) _ r) (sym (word-toks x tv _ _))
        (subst (λ ts → ParsesAtomExpr (TWord "let" ∷ TWord x ∷ TEquals ∷ toks (proj₁ (pex 0 true v tv _)) ts) _ r)
          (sym (word-toks "in" tv _ _))
          (atom-let (wholeL v tv _ _ wv stops-in) (wholeL (RQualified bx bq) tv _ r wb st))))
  letA x v (RResolved bn) tv k r (wv , wb) st =
    subst (λ ts → ParsesAtomExpr ts _ r) (sym (word-toks "let" tv k _))
      (subst (λ ts → ParsesAtomExpr (TWord "let" ∷ ts) _ r) (sym (word-toks x tv _ _))
        (subst (λ ts → ParsesAtomExpr (TWord "let" ∷ TWord x ∷ TEquals ∷ toks (proj₁ (pex 0 true v tv _)) ts) _ r)
          (sym (word-toks "in" tv _ _))
          (atom-let (wholeL v tv _ _ wv stops-in) (wholeL (RResolved bn) tv _ r wb st))))
  letA x v (RApp bf ba) tv k r (wv , wb) st =
    subst (λ ts → ParsesAtomExpr ts _ r) (sym (word-toks "let" tv k _))
      (subst (λ ts → ParsesAtomExpr (TWord "let" ∷ ts) _ r) (sym (word-toks x tv _ _))
        (subst (λ ts → ParsesAtomExpr (TWord "let" ∷ TWord x ∷ TEquals ∷ toks (proj₁ (pex 0 true v tv _)) ts) _ r)
          (sym (word-toks "in" tv _ _))
          (atom-let (wholeL v tv _ _ wv stops-in) (wholeL (RApp bf ba) tv _ r wb st))))
  letA x v (RLam bx be) tv k r (wv , wb) st =
    subst (λ ts → ParsesAtomExpr ts _ r) (sym (word-toks "let" tv k _))
      (subst (λ ts → ParsesAtomExpr (TWord "let" ∷ ts) _ r) (sym (word-toks x tv _ _))
        (subst (λ ts → ParsesAtomExpr (TWord "let" ∷ TWord x ∷ TEquals ∷ toks (proj₁ (pex 0 true v tv _)) ts) _ r)
          (sym (word-toks "in" tv _ _))
          (atom-let (wholeL v tv _ _ wv stops-in) (wholeL (RLam bx be) tv _ r wb st))))
  letA x v (RLet y′ v′ c′) tv k r (wv , wb) st =
    subst (λ ts → ParsesAtomExpr ts _ r) (sym (word-toks "let" tv k _))
      (subst (λ ts → ParsesAtomExpr (TWord "let" ∷ ts) _ r) (sym (word-toks x tv _ _))
        (subst (λ ts → ParsesAtomExpr (TWord "let" ∷ TWord x ∷ TEquals ∷ toks (proj₁ (pex 0 true v tv _)) ts) _ r)
          (sym (word-toks "in" tv _ _))
          (atom-let (wholeL v tv _ _ wv stops-in) (atom→expr st (letA y′ v′ c′ tv _ r wb st)))))
  letA x v (RPair ba bb) tv k r (wv , wb) st =
    subst (λ ts → ParsesAtomExpr ts _ r) (sym (word-toks "let" tv k _))
      (subst (λ ts → ParsesAtomExpr (TWord "let" ∷ ts) _ r) (sym (word-toks x tv _ _))
        (subst (λ ts → ParsesAtomExpr (TWord "let" ∷ TWord x ∷ TEquals ∷ toks (proj₁ (pex 0 true v tv _)) ts) _ r)
          (sym (word-toks "in" tv _ _))
          (atom-let (wholeL v tv _ _ wv stops-in) (wholeL (RPair ba bb) tv _ r wb st))))
  letA x v (RDestruct bs bx bel by ber) tv k r (wv , wb) st =
    subst (λ ts → ParsesAtomExpr ts _ r) (sym (word-toks "let" tv k _))
      (subst (λ ts → ParsesAtomExpr (TWord "let" ∷ ts) _ r) (sym (word-toks x tv _ _))
        (subst (λ ts → ParsesAtomExpr (TWord "let" ∷ TWord x ∷ TEquals ∷ toks (proj₁ (pex 0 true v tv _)) ts) _ r)
          (sym (word-toks "in" tv _ _))
          (atom-let (wholeL v tv _ _ wv stops-in) (wholeL (RDestruct bs bx bel by ber) tv _ r wb st))))
  letA x v RUnit tv k r (wv , wb) st =
    subst (λ ts → ParsesAtomExpr ts _ r) (sym (word-toks "let" tv k _))
      (subst (λ ts → ParsesAtomExpr (TWord "let" ∷ ts) _ r) (sym (word-toks x tv _ _))
        (subst (λ ts → ParsesAtomExpr (TWord "let" ∷ TWord x ∷ TEquals ∷ toks (proj₁ (pex 0 true v tv _)) ts) _ r)
          (sym (word-toks "in" tv _ _))
          (atom-let (wholeL v tv _ _ wv stops-in) (wholeL RUnit tv 0 r wb st))))
  letA x v (RInt (ℤ.+ bn)) tv k r (wv , wb) st =
    subst (λ ts → ParsesAtomExpr ts _ r) (sym (word-toks "let" tv k _))
      (subst (λ ts → ParsesAtomExpr (TWord "let" ∷ ts) _ r) (sym (word-toks x tv _ _))
        (subst (λ ts → ParsesAtomExpr (TWord "let" ∷ TWord x ∷ TEquals ∷ toks (proj₁ (pex 0 true v tv _)) ts) _ r)
          (sym (word-toks "in" tv _ _))
          (atom-let (wholeL v tv _ _ wv stops-in) (wholeL (RInt (ℤ.+ bn)) tv _ r wb st))))
  letA x v (RInt ℤ.-[1+ bn ]) tv k r (wv , wb) st =
    subst (λ ts → ParsesAtomExpr ts _ r) (sym (word-toks "let" tv k _))
      (subst (λ ts → ParsesAtomExpr (TWord "let" ∷ ts) _ r) (sym (word-toks x tv _ _))
        (subst (λ ts → ParsesAtomExpr (TWord "let" ∷ TWord x ∷ TEquals ∷ toks (proj₁ (pex 0 true v tv _)) ts) _ r)
          (sym (word-toks "in" tv _ _))
          (atom-let (wholeL v tv _ _ wv stops-in) (wholeL (RInt ℤ.-[1+ bn ]) tv _ r wb st))))
  letA x v (RFloat pos bi bfr bl) tv k r (wv , wb) st =
    subst (λ ts → ParsesAtomExpr ts _ r) (sym (word-toks "let" tv k _))
      (subst (λ ts → ParsesAtomExpr (TWord "let" ∷ ts) _ r) (sym (word-toks x tv _ _))
        (subst (λ ts → ParsesAtomExpr (TWord "let" ∷ TWord x ∷ TEquals ∷ toks (proj₁ (pex 0 true v tv _)) ts) _ r)
          (sym (word-toks "in" tv _ _))
          (atom-let (wholeL v tv _ _ wv stops-in) (wholeL (RFloat pos bi bfr bl) tv _ r wb st))))
  letA x v (RFloat neg bi bfr bl) tv k r (wv , wb) st =
    subst (λ ts → ParsesAtomExpr ts _ r) (sym (word-toks "let" tv k _))
      (subst (λ ts → ParsesAtomExpr (TWord "let" ∷ ts) _ r) (sym (word-toks x tv _ _))
        (subst (λ ts → ParsesAtomExpr (TWord "let" ∷ TWord x ∷ TEquals ∷ toks (proj₁ (pex 0 true v tv _)) ts) _ r)
          (sym (word-toks "in" tv _ _))
          (atom-let (wholeL v tv _ _ wv stops-in) (wholeL (RFloat neg bi bfr bl) tv _ r wb st))))
  letA x v (RAnnot be bT) tv k r (wv , wb) st =
    subst (λ ts → ParsesAtomExpr ts _ r) (sym (word-toks "let" tv k _))
      (subst (λ ts → ParsesAtomExpr (TWord "let" ∷ ts) _ r) (sym (word-toks x tv _ _))
        (subst (λ ts → ParsesAtomExpr (TWord "let" ∷ TWord x ∷ TEquals ∷ toks (proj₁ (pex 0 true v tv _)) ts) _ r)
          (sym (word-toks "in" tv _ _))
          (atom-let (wholeL v tv _ _ wv stops-in) (wholeL (RAnnot be bT) tv _ r wb st))))
  letA x v (RBinOp bop ba bb) tv k r (wv , wb) st =
    subst (λ ts → ParsesAtomExpr ts _ r) (sym (word-toks "let" tv k _))
      (subst (λ ts → ParsesAtomExpr (TWord "let" ∷ ts) _ r) (sym (word-toks x tv _ _))
        (subst (λ ts → ParsesAtomExpr (TWord "let" ∷ TWord x ∷ TEquals ∷ toks (proj₁ (pex 0 true v tv _)) ts) _ r)
          (sym (word-toks "in" tv _ _))
          (atom-let (wholeL v tv _ _ wv stops-in) (wholeL (RBinOp bop ba bb) tv _ r wb st))))
  letA x v (RNeg be) tv k r (wv , wb) st =
    subst (λ ts → ParsesAtomExpr ts _ r) (sym (word-toks "let" tv k _))
      (subst (λ ts → ParsesAtomExpr (TWord "let" ∷ ts) _ r) (sym (word-toks x tv _ _))
        (subst (λ ts → ParsesAtomExpr (TWord "let" ∷ TWord x ∷ TEquals ∷ toks (proj₁ (pex 0 true v tv _)) ts) _ r)
          (sym (word-toks "in" tv _ _))
          (atom-let (wholeL v tv _ _ wv stops-in) (wholeL (RNeg be) tv _ r wb st))))

  desA : ∀ s x el y er tv k r → WF (RDestruct s x el y er) → Stops r
       → ParsesAtomExpr (toks (proj₁ (pdes s x el y er tv k)) r) (RDestruct s x el y er) r
  desA s x el y er tv k r (ws , wl , wr) st =
    subst (λ ts → ParsesAtomExpr ts _ r) (sym (word-toks "destruct" tv k _))
      (subst (λ ts → ParsesAtomExpr (TWord "destruct" ∷ toks (proj₁ (pex 0 true s tv _)) ts) _ r) (sym (word-toks "of" tv _ _))
        (subst (λ ts → ParsesAtomExpr (TWord "destruct" ∷ toks (proj₁ (pex 0 true s tv _)) (TWord "of" ∷ TLBrace ∷ ts)) _ r)
          (sym (word-toks "Left" tv _ _))
          (subst (λ ts → ParsesAtomExpr (TWord "destruct" ∷ toks (proj₁ (pex 0 true s tv _)) (TWord "of" ∷ TLBrace ∷ TWord "Left" ∷ ts)) _ r)
            (sym (word-toks x tv _ _))
            (subst (λ ts → ParsesAtomExpr (TWord "destruct" ∷ toks (proj₁ (pex 0 true s tv _))
                             (TWord "of" ∷ TLBrace ∷ TWord "Left" ∷ TWord x ∷ TArrow ∷ toks (proj₁ (pex 0 true el tv _)) (TSemicolon ∷ ts))) _ r)
              (sym (word-toks "Right" tv _ _))
              (subst (λ ts → ParsesAtomExpr (TWord "destruct" ∷ toks (proj₁ (pex 0 true s tv _))
                               (TWord "of" ∷ TLBrace ∷ TWord "Left" ∷ TWord x ∷ TArrow ∷ toks (proj₁ (pex 0 true el tv _))
                                 (TSemicolon ∷ TWord "Right" ∷ ts))) _ r)
                (sym (word-toks y tv _ _))
                (atom-destruct (wholeL s tv _ _ ws stops-of) (wholeL el tv _ _ wl stops-semi) (wholeL er tv _ _ wr stops-rbrace)))))))

