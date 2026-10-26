# Generates formal/Once/Format/Proof/ExprBase.agda and Expr.agda (plan 0.124
# step 4.2): the cases per expression constructor and operator.
# Run from anywhere: python3 formal/scripts/gen-format-expr.py
import os
PROOF=os.path.join(os.path.dirname(os.path.abspath(__file__)),'..','Once','Format','Proof')

# ---- ExprBase ----
CTORS=[('RVar','x'),('RQualified','x a'),('RResolved','n'),('RApp','f a'),('RLam','x e'),('RLet','x v b'),
 ('RPair','a b'),('RDestruct','s x el y er'),('RUnit',''),('RInt','z'),('RFloat','i f l'),('RAnnot','e T'),
 ('RBinOp','op a b'),('RNeg','e')]
def pat(c,args,prefix=''):
    if not args: return c
    a=' '.join(prefix+x for x in args.split())
    return f'({c} {a})'
OPCH=['.','+','-','*','/','%','<','>','|','&','@']
o=[]
w=o.append
w(r'''-- SPDX-License-Identifier: AGPL-3.0-or-later
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
compose-true : ∀ f → isCompose (headOf f) ≡ true → ∃[ g ] f ≡ RApp (RVar "compose") g''')
for c,args in CTORS:
    if c=='RApp':
        for c2,a2 in CTORS:
            if c2=='RVar':
                w(f'compose-true (RApp (RVar x) g) eq = g , cong (λ y → RApp (RVar y) g) (==-true eq)')
            else:
                w(f'compose-true (RApp {pat(c2,a2,"c")} g) ()')
    else:
        w(f'compose-true {pat(c,args)} ()')
# operator chars
w('''
private
  ≟-true : ∀ {c d} → does (c Ch.≟ d) ≡ true → c ≡ d
  ≟-true {c} {d} eq = ChP.toℕ-injective c d (ℕP.≡ᵇ⇒≡ (Ch.toℕ c) (Ch.toℕ d) (subst T (sym eq) tt))

  start-not : ∀ {c d} → does (c Ch.≟ d) ≡ true → isIdentStart c ≡ true → isIdentStart d ≡ false → ⊥
  start-not {c} {d} eq st sd with ≟-true {c} {d} eq
  ... | refl with () ← trans (sym st) sd

-- | A character that starts an identifier is no operator character.
ident-not-op : ∀ c → isIdentStart c ≡ true → opToken c ≡ nothing''')
# generate nested with chain
lines=[]
def chain(depth):
    pass
pref='ident-not-op c st'
pat_so_far=[]
for i,ch in enumerate(OPCH):
    pv=' | '.join(['false']*i)
    head=f'ident-not-op c st' + (' | '+pv if i>0 else '')
    w(f"{head} with does (c Ch.≟ '{ch}') in e{i}")
    w(f"{head} | true  = ⊥-elim (start-not {{c}} {{'{ch}'}} e{i} st refl)")
w(f"ident-not-op c st | {' | '.join(['false']*len(OPCH))} = refl")
w('''
private
  op-isOp : ∀ {t d} → OpChar t d → isOpChar d ≡ true''')
for oc in ['oc-dot','oc-plus','oc-minus','oc-star','oc-slash','oc-pct','oc-lt','oc-gt','oc-pipe','oc-amp','oc-at']:
    w(f'  op-isOp {oc} = refl')
w('''
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
op-token : ∀ {t d} → OpChar t d → opToken d ≡ just t''')
for oc in ['oc-dot','oc-plus','oc-minus','oc-star','oc-slash','oc-pct','oc-lt','oc-gt','oc-pipe','oc-amp','oc-at']:
    w(f'op-token {oc} = refl')
open(os.path.join(PROOF,'ExprBase.agda'),'w').write('\n'.join(o)+'\n')

# ---- Expr ----
CTORS=[('RVar','x'),('RQualified','x q'),('RResolved','n'),('RApp','f a'),('RLam','x e'),('RLet','x v b'),
 ('RPair','a b'),('RDestruct','s x el y er'),('RUnit',''),('RInt','z'),('RFloat','i fr l'),('RAnnot','e T'),
 ('RBinOp','op a b'),('RNeg','e')]
OPS={'OpAdd':2,'OpSub':2,'OpMul':3,'OpDiv':3,'OpMod':3,'OpLt':1,'OpLe':1,'OpGt':1,'OpGe':1,'OpEq':1,'OpNe':1}
MT={'OpMul':'mt-star','OpDiv':'mt-slash','OpMod':'mt-pct'}
AT={'OpAdd':'at-plus','OpSub':'at-minus'}
CT={'OpLt':'ct-lt','OpLe':'ct-le','OpGt':'ct-gt','OpGe':'ct-ge','OpEq':'ct-eq','OpNe':'ct-ne'}
def P(c,args,pre=''):
    if not args: return c
    return '('+c+' '+' '.join(pre+a for a in args.split())+')'
o=[]; w=o.append
w(r'''-- SPDX-License-Identifier: AGPL-3.0-or-later
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
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃-syntax)
open import Data.String using (String; toList; fromList)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Agda.Builtin.String.Properties using (primStringToListInjective)

open import Once.Postulates using (toList∘fromList)
open import Once.Spec.Surface.Lexing using (Token; TWord; TInt; TFloat; TLParen; TRParen; TComma; TColon; TSemicolon;
  TLBrace; TRBrace; TDot; TAt; TLambda; TArrow; TEquals; TMinus; TPlus; TStar; TSlash; TPercent; TLt; TLe; TGt; TGe;
  TEqEq; TNeq)
open import Once.Spec.Surface.Syntax using (Expr; RVar; RQualified; RResolved; RApp; RLam; RLet; RPair; RDestruct;
  RUnit; RInt; RFloat; RAnnot; RBinOp; RNeg; OpAdd; OpSub; OpMul; OpDiv; OpMod; OpLt; OpLe; OpGt; OpGe; OpEq; OpNe)
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

  -- An operator's characters, up to `)`.
  opchars : ∀ c cs acc tv k r → All (λ d → ∃[ t ] OpChar t d) (c ∷ cs)
          → ParsesOpChars (toks (proj₁ (opToks (c ∷ cs) tv k)) (TRParen ∷ r)) acc
                          (fromList (reverse (reverseAcc acc (c ∷ cs)))) r
  opchars c []       acc tv k r ((t , o) ∷ []) rewrite op-token o = op-char o op-close
  opchars c (d ∷ ds) acc tv k r ((t , o) ∷ os) rewrite op-token o =
    subst (λ ts → ParsesOpChars (t ∷ ts) acc _ r)
      (sym (if-space (does (c Ch.≟ '-') ∧ (does (d Ch.≟ '-') ∨ does (d Ch.≟ '>'))) (toks (proj₁ (opToks (d ∷ ds) tv k)) (TRParen ∷ r))))
      (op-char o (opchars d ds (c ∷ acc) tv _ r os))

  -- A name.
  nameAtom : ∀ x tv k r → NameOK x → NoQual r → ParsesAtomExpr (toks (proj₁ (name x tv k)) r) (RVar x) r
  nameAtom x tv k r (inj₁ op@(c , cs , eq , os)) nq rewrite op-isOperator x op =
    atom-op (subst (λ s → ParsesOpChars (toks (proj₁ (opToks (toList x) tv k)) (TRParen ∷ r)) [] s r)
               (trans (cong fromList (reverse-involutive (c ∷ cs))) (trans (cong fromList (sym eq)) (fromList∘toList x)))
               (subst (λ cs′ → ParsesOpChars (toks (proj₁ (opToks cs′ tv k)) (TRParen ∷ r)) [] (fromList (reverse (reverse (c ∷ cs)))) r)
                  (sym eq) (opchars c cs [] tv k r os)))
  nameAtom x tv k r (inj₂ (¬res , c , cs , eq , st)) nq rewrite word-notOperator x c cs eq st =
    subst (λ ts → ParsesAtomExpr ts (RVar x) r) (sym (word-toks x tv k r)) (atom-var ¬res nq)

  nameArg : ∀ x tv k r → NameOK x → ArgStart (toks (proj₁ (name x tv k)) r)
  nameArg x tv k r (inj₁ op) rewrite op-isOperator x op = as-paren
  nameArg x tv k r (inj₂ (¬res , c , cs , eq , st)) rewrite word-notOperator x c cs eq st =
    subst ArgStart (sym (word-toks x tv k r)) (as-word ¬res)
''')
open(os.path.join(PROOF,'Expr.agda'),'w').write('\n'.join(o)+'\n')
o=[]; w=o.append
LIFT_KINDS=['RVar','RQualified','RUnit','RInt','RFloat','RPair','RAnnot','RLam','RLet','RDestruct']
def lv(op): return OPS[op]
# ---------- argSt ----------
w('''
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
argSt (RInt z) tv k r w = subst ArgStart (sym (anchor-toks (TInt z) tv k r)) as-int
argSt (RFloat i fr l) tv k r w = subst ArgStart (sym (anchor-toks (TFloat i fr l) tv k r)) as-float
argSt (RAnnot e T) tv k r w = as-paren''')
for op in OPS: w(f'argSt (RBinOp {op} a b) tv k r w = as-paren')
w('argSt (RNeg e) tv k r w = as-paren')
# ---------- mutual ----------
w('''
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
  atomL (RInt z) tv k r w nq = subst (λ ts → ParsesAtomExpr ts (RInt z) r) (sym (anchor-toks (TInt z) tv k r)) atom-int
  atomL (RFloat i fr l) tv k r w nq =
    subst (λ ts → ParsesAtomExpr ts (RFloat i fr l) r) (sym (anchor-toks (TFloat i fr l) tv k r)) atom-float
  atomL (RAnnot e T) tv k r (we , wT) nq =
    atom-paren (wholeL e tv k _ we stops-colon)
      (paren-annot (subst (λ A → Annot.ParsesType (toks (proj₁ (pty 0 true (toPoly T) tv (proj₂ (pex 0 true e tv k)))) (TRParen ∷ r)) A (TRParen ∷ r))
        (ground-id T wT)
        (TA.Ground.type′ (toPoly T) true tv (proj₂ (pex 0 true e tv k)) (TRParen ∷ r) (ground-wf T) ((λ ()) , (λ ()))
          ((λ ()) , (λ ()) , (λ ()) , (λ ())) (λ ()) (λ ()))))''')
R = "(λ ()) (λ ())"
S = "(λ { starts () })"
for op in OPS:
    L=lv(op)
    if L==1:
        inner=f'expr (cmp {CT[op]} (leftCmp a tv k _ wa (λ ()) (λ ()) {S} {S}) (addL b tv _ (TRParen ∷ r) wb (λ ()) (λ ()) {S} (add-done {S}))) (comp-done (λ ()))'
    elif L==2:
        inner=f'expr (cmp-none (leftAdd a tv k _ wa (λ ()) (λ ()) {S} (add-op {AT[op]} (mulL b tv _ (TRParen ∷ r) wb (λ ()) (λ ()) (mul-done {S})) (add-done {S}))) {S}) (comp-done (λ ()))'
    else:
        inner=f'expr (cmp-none (add (leftMul a tv k _ wa (λ ()) (λ ()) (mul-op {MT[op]} (unaryL b tv _ (TRParen ∷ r) wb (λ ()) (λ ())) (mul-done {S}))) (add-done {S})) {S}) (comp-done (λ ()))'
    w(f'  atomL (RBinOp {op} a b) tv k r (wa , wb) nq =\n    atom-paren ({inner}) paren-close')
w('''  atomL (RNeg e) tv k r w nq =
    atom-paren (expr (cmp-none (add (mul
      (subst (λ ts → ParsesUnary (TMinus ∷ ts) (RNeg e) (TRParen ∷ r)) (sym (if-space (startsNeg e) (E 4 e tv k (TRParen ∷ r))))
        (neg (unaryL e tv k (TRParen ∷ r) w (λ ()) (λ ()))))
      (mul-done (λ { starts () }))) (add-done (λ { starts () }))) (λ { starts () })) (comp-done (λ ()))) paren-close

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
  spineL (RApp f a) tv k r (wf , wa) nq tl = spineApp′ f a (isCompose (headOf f)) tv k r refl wf wa nq tl''')
for c,args in CTORS:
    if c=='RApp': continue
    if c=='RResolved':
        w(f'  spineL {P(c,args)} tv k r () nq tl'); continue
    w(f'  spineL {P(c,args)} tv k r wf nq tl = app (atomL {P(c,args)} tv k r wf nq) tl')
w('''
  spineApp′ : ∀ f a b tv k r {e′ r′} → isCompose (headOf f) ≡ b → WF f → WF a → NoQual r → ParsesAppTail (RApp f a) r e′ r′
            → ParsesApp (toks (proj₁ (pspine′ b f a tv k)) r) e′ r′
  spineApp′ f a true tv k r eq wf wa nq tl with compose-true f eq
  ... | g , refl = app (composeAtom g a 5 tv k r (proj₂ wf) wa) tl
  spineApp′ f a false tv k r eq wf wa nq tl = spineApp f a tv k r wf wa nq tl

  -- The left operand of `.`, while it is a composition.
  chainL : ∀ g tv k r {e′ r′} → WF g → NoQual r → AppDone r → MulDone r → AddDone r → CmpDone r → ParsesCompTail g r e′ r′
         → ParsesExpr (toks (proj₁ (pchainC g tv k)) r) e′ r′
  chainL (RApp f h) tv k r (wf , wh) nq ad md dd cd tl = chainApp f h (isCompose (headOf f)) tv k r refl wf wh nq ad md dd cd tl''')
for c,args in CTORS:
    if c=='RApp': continue
    if c=='RResolved':
        w(f'  chainL {P(c,args)} tv k r () nq ad md dd cd tl'); continue
    w(f'  chainL {P(c,args)} tv k r wg nq ad md dd cd tl = expr (cmpL {P(c,args)} tv k r wg nq ad md dd cd) tl')
w('''
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
  appL (RResolved n) tv k r () nq tl''')
for c,args in CTORS:
    if c in ('RApp','RResolved','RBinOp'): continue
    w(f'  appL {P(c,args)} tv k r w nq tl = app (atomL {P(c,args)} tv k r w nq) tl')
for op in OPS:
    w(f'  appL (RBinOp {op} a b) tv k r w nq tl = app (atomL (RBinOp {op} a b) tv k r w nq) tl')
w('''
  appApp : ∀ f a b tv k r {e′ r′} → isCompose (headOf f) ≡ b → WF f → WF a → NoQual r → ParsesAppTail (RApp f a) r e′ r′
         → ParsesApp (toks (proj₁ (pcomp 5 b f a tv k)) r) e′ r′
  appApp f a true tv k r eq wf wa nq tl with compose-true f eq
  ... | g , refl = app (composeAtom g a 4 tv k r (proj₂ wf) wa) tl
  appApp f a false tv k r eq wf wa nq tl = spineApp f a tv k r wf wa nq tl

  -- | A prefix `-` (level 4).
  unaryL : ∀ e tv k r → WF e → NoQual r → AppDone r → ParsesUnary (E 4 e tv k r) e r
  unaryL (RNeg e) tv k r w nq ad =
    subst (λ ts → ParsesUnary (TMinus ∷ ts) (RNeg e) r) (sym (if-space (startsNeg e) (E 4 e tv k r)))
      (neg (unaryL e tv k r w nq ad))
  unaryL (RApp f a) tv k r (wf , wa) nq ad = unaryApp f a (isCompose (headOf f)) tv k r refl wf wa nq ad
  unaryL (RResolved n) tv k r () nq ad''')
for c,args in CTORS:
    if c in ('RApp','RResolved','RBinOp','RNeg'): continue
    w(f'  unaryL {P(c,args)} tv k r w nq ad = unary (appL {P(c,args)} tv k r w nq (app-done ad))')
for op in OPS:
    w(f'  unaryL (RBinOp {op} a b) tv k r w nq ad = unary (appL (RBinOp {op} a b) tv k r w nq (app-done ad))')
w('''
  unaryApp : ∀ f a b tv k r → isCompose (headOf f) ≡ b → WF f → WF a → NoQual r → AppDone r
           → ParsesUnary (toks (proj₁ (pcomp 4 b f a tv k)) r) (RApp f a) r
  unaryApp f a true tv k r eq wf wa nq ad with compose-true f eq
  ... | g , refl = unary (app (composeAtom g a 3 tv k r (proj₂ wf) wa) (app-done ad))
  unaryApp f a false tv k r eq wf wa nq ad = unary (spineApp f a tv k r wf wa nq (app-done ad))

  -- | `*`, `/`, `%` (level 3), with what continues them.
  mulL : ∀ e tv k r {e′ r′} → WF e → NoQual r → AppDone r → ParsesMulTail e r e′ r′ → ParsesMul (E 3 e tv k r) e′ r′
  mulL (RApp f a) tv k r (wf , wa) nq ad tl = mulApp f a (isCompose (headOf f)) tv k r refl wf wa nq ad tl
  mulL (RResolved n) tv k r () nq ad tl''')
for c,args in CTORS:
    if c in ('RApp','RResolved','RBinOp'): continue
    w(f'  mulL {P(c,args)} tv k r w nq ad tl = mul (unaryL {P(c,args)} tv k r w nq ad) tl')
for op in OPS:
    if lv(op)==3:
        w(f'  mulL (RBinOp {op} a b) tv k r (wa , wb) nq ad tl =\n    leftMul a tv k _ wa (λ ()) (λ ()) (mul-op {MT[op]} (unaryL b tv _ r wb nq ad) tl)')
    else:
        w(f'  mulL (RBinOp {op} a b) tv k r w nq ad tl = mul (unaryL (RBinOp {op} a b) tv k r w nq ad) tl')
w('''
  mulApp : ∀ f a b tv k r {e′ r′} → isCompose (headOf f) ≡ b → WF f → WF a → NoQual r → AppDone r → ParsesMulTail (RApp f a) r e′ r′
         → ParsesMul (toks (proj₁ (pcomp 3 b f a tv k)) r) e′ r′
  mulApp f a true tv k r eq wf wa nq ad tl with compose-true f eq
  ... | g , refl = mul (unary (app (composeAtom g a 2 tv k r (proj₂ wf) wa) (app-done ad))) tl
  mulApp f a false tv k r eq wf wa nq ad tl = mul (unary (spineApp f a tv k r wf wa nq (app-done ad))) tl

  leftMul : ∀ a tv k r {e′ r′} → WF a → NoQual r → AppDone r → ParsesMulTail a r e′ r′
          → ParsesMul (toks (proj₁ (pleft 3 a tv k)) r) e′ r′''')
for op in OPS:
    if lv(op)==3:
        w(f'  leftMul (RBinOp {op} x y) tv k r (wx , wy) nq ad tl =\n    leftMul x tv k _ wx (λ ()) (λ ()) (mul-op {MT[op]} (unaryL y tv _ r wy nq ad) tl)')
    else:
        w(f'  leftMul (RBinOp {op} x y) tv k r w nq ad tl = mulL (RBinOp {op} x y) tv k r w nq ad tl')
for c,args in CTORS:
    if c=='RBinOp': continue
    w(f'  leftMul {P(c,args)} tv k r w nq ad tl = mulL {P(c,args)} tv k r w nq ad tl')
w('''
  -- | `+`, `-` (level 2), with what continues them.
  addL : ∀ e tv k r {e′ r′} → WF e → NoQual r → AppDone r → MulDone r → ParsesAddTail e r e′ r′ → ParsesAdd (E 2 e tv k r) e′ r′
  addL (RApp f a) tv k r (wf , wa) nq ad md tl = addApp f a (isCompose (headOf f)) tv k r refl wf wa nq ad md tl
  addL (RResolved n) tv k r () nq ad md tl''')
for c,args in CTORS:
    if c in ('RApp','RResolved','RBinOp'): continue
    w(f'  addL {P(c,args)} tv k r w nq ad md tl = add (mulL {P(c,args)} tv k r w nq ad (mul-done md)) tl')
for op in OPS:
    if lv(op)==2:
        w(f'  addL (RBinOp {op} a b) tv k r (wa , wb) nq ad md tl =\n    leftAdd a tv k _ wa (λ ()) (λ ()) (λ {{ starts () }}) (add-op {AT[op]} (mulL b tv _ r wb nq ad (mul-done md)) tl)')
    else:
        w(f'  addL (RBinOp {op} a b) tv k r w nq ad md tl = add (mulL (RBinOp {op} a b) tv k r w nq ad (mul-done md)) tl')
w('''
  addApp : ∀ f a b tv k r {e′ r′} → isCompose (headOf f) ≡ b → WF f → WF a → NoQual r → AppDone r → MulDone r
         → ParsesAddTail (RApp f a) r e′ r′ → ParsesAdd (toks (proj₁ (pcomp 2 b f a tv k)) r) e′ r′
  addApp f a true tv k r eq wf wa nq ad md tl with compose-true f eq
  ... | g , refl = add (mul (unary (app (composeAtom g a 1 tv k r (proj₂ wf) wa) (app-done ad))) (mul-done md)) tl
  addApp f a false tv k r eq wf wa nq ad md tl = add (mul (unary (spineApp f a tv k r wf wa nq (app-done ad))) (mul-done md)) tl

  leftAdd : ∀ a tv k r {e′ r′} → WF a → NoQual r → AppDone r → MulDone r → ParsesAddTail a r e′ r′
          → ParsesAdd (toks (proj₁ (pleft 2 a tv k)) r) e′ r′''')
for op in OPS:
    if lv(op)==2:
        w(f'  leftAdd (RBinOp {op} x y) tv k r (wx , wy) nq ad md tl =\n    leftAdd x tv k _ wx (λ ()) (λ ()) (λ {{ starts () }}) (add-op {AT[op]} (mulL y tv _ r wy nq ad (mul-done md)) tl)')
    else:
        w(f'  leftAdd (RBinOp {op} x y) tv k r w nq ad md tl = addL (RBinOp {op} x y) tv k r w nq ad md tl')
for c,args in CTORS:
    if c=='RBinOp': continue
    w(f'  leftAdd {P(c,args)} tv k r w nq ad md tl = addL {P(c,args)} tv k r w nq ad md tl')
w('''
  -- | A comparison (level 1).
  cmpL : ∀ e tv k r → WF e → NoQual r → AppDone r → MulDone r → AddDone r → CmpDone r → ParsesCmp (E 1 e tv k r) e r
  cmpL (RApp f a) tv k r (wf , wa) nq ad md dd cd = cmpApp f a (isCompose (headOf f)) tv k r refl wf wa nq ad md dd cd
  cmpL (RResolved n) tv k r () nq ad md dd cd''')
for c,args in CTORS:
    if c in ('RApp','RResolved','RBinOp'): continue
    w(f'  cmpL {P(c,args)} tv k r w nq ad md dd cd = cmp-none (addL {P(c,args)} tv k r w nq ad md (add-done dd)) cd')
for op in OPS:
    if lv(op)==1:
        w(f'  cmpL (RBinOp {op} a b) tv k r (wa , wb) nq ad md dd cd =\n    cmp {CT[op]} (leftCmp a tv k _ wa (λ ()) (λ ()) (λ {{ starts () }}) (λ {{ starts () }})) (addL b tv _ r wb nq ad md (add-done dd))')
    else:
        w(f'  cmpL (RBinOp {op} a b) tv k r w nq ad md dd cd = cmp-none (addL (RBinOp {op} a b) tv k r w nq ad md (add-done dd)) cd')
w('''
  cmpApp : ∀ f a b tv k r → isCompose (headOf f) ≡ b → WF f → WF a → NoQual r → AppDone r → MulDone r → AddDone r → CmpDone r
         → ParsesCmp (toks (proj₁ (pcomp 1 b f a tv k)) r) (RApp f a) r
  cmpApp f a true tv k r eq wf wa nq ad md dd cd with compose-true f eq
  ... | g , refl = cmp-none (add (mul (unary (app (composeAtom g a 0 tv k r (proj₂ wf) wa) (app-done ad))) (mul-done md)) (add-done dd)) cd
  cmpApp f a false tv k r eq wf wa nq ad md dd cd =
    cmp-none (add (mul (unary (spineApp f a tv k r wf wa nq (app-done ad))) (mul-done md)) (add-done dd)) cd

  -- A comparison's left operand: a sum.
  leftCmp : ∀ a tv k r → WF a → NoQual r → AppDone r → MulDone r → AddDone r → ParsesAdd (toks (proj₁ (pleft 1 a tv k)) r) a r''')
for op in OPS:
    w(f'  leftCmp (RBinOp {op} x y) tv k r w nq ad md dd = addL (RBinOp {op} x y) tv k r w nq ad md (add-done dd)')
for c,args in CTORS:
    if c=='RBinOp': continue
    w(f'  leftCmp {P(c,args)} tv k r w nq ad md dd = addL {P(c,args)} tv k r w nq ad md (add-done dd)')
w('''
  -- | A whole expression: nothing of it follows.
  wholeL : ∀ e tv k r → WF e → Stops r → ParsesExpr (toks (proj₁ (pex 0 true e tv k)) r) e r
  wholeL (RLam x e) tv k r w st = atom→expr st (lamA x e tv k r w st)
  wholeL (RLet x v b) tv k r w st = atom→expr st (letA x v b tv k r w st)
  wholeL (RDestruct s x el y er) tv k r w st = atom→expr st (desA s x el y er tv k r w st)
  wholeL (RApp f a) tv k r (wf , wa) st = wholeApp f a (isCompose (headOf f)) tv k r refl wf wa st
  wholeL (RResolved n) tv k r () st''')
for c,args in CTORS:
    if c in ('RLam','RLet','RDestruct','RApp','RResolved','RBinOp'): continue
    w(f'  wholeL {P(c,args)} tv k r w (stops sq sa sm sd sc so) = expr (cmpL {P(c,args)} tv k r w sq sa sm sd sc) (comp-done so)')
for op in OPS:
    w(f'  wholeL (RBinOp {op} x y) tv k r w (stops sq sa sm sd sc so) = expr (cmpL (RBinOp {op} x y) tv k r w sq sa sm sd sc) (comp-done so)')
w('''
  wholeApp : ∀ f a b tv k r → isCompose (headOf f) ≡ b → WF f → WF a → Stops r
           → ParsesExpr (toks (proj₁ (pcomp 0 b f a tv k)) r) (RApp f a) r
  wholeApp f a true tv k r eq wf wa (stops q ad m d c o) with compose-true f eq
  ... | g , refl = composeL g a tv k r (proj₂ wf) wa q ad m d c (comp-done o)
  wholeApp f a false tv k r eq wf wa st@(stops q ad m d c o) = app→expr st (spineApp f a tv k r wf wa q (app-done ad))

  -- `\\x y -> b`, `let`, `destruct`.
  lamA : ∀ x e tv k r → WF e → Stops r → ParsesAtomExpr (toks (proj₁ (plam x e tv k)) r) (RLam x e) r
  lamA x e tv k r w st =
    subst (λ ts → ParsesAtomExpr (TLambda ∷ ts) (RLam x e) r) (sym (word-toks x tv k _))
      (atom-lambda (lam-arg (paramsL e tv _ r w st)))

  paramsL : ∀ e tv k r → WF e → Stops r → ParsesLamParams (toks (proj₁ (plam′ e tv k)) r) e r
  paramsL (RLam y e) tv k r w st =
    subst (λ ts → ParsesLamParams ts (RLam y e) r) (sym (word-toks y tv k _)) (lam-arg (paramsL e tv _ r w st))''')
for c,args in CTORS:
    if c=='RLam': continue
    w(f'  paramsL {P(c,args)} tv k r w st = lam-body (wholeL {P(c,args)} tv k r w st)')
w('''
  letA : ∀ x v b tv k r → WF (RLet x v b) → Stops r → ParsesAtomExpr (toks (proj₁ (plet′ x v b tv k)) r) (RLet x v b) r''')
for c,args in CTORS:
    body = P(c,args,'b')
    if c=='RLet':
        rest = f'(atom→expr st (letA y′ v′ c′ tv _ r wb st))'
        bpat = '(RLet y′ v′ c′)'
    else:
        rest = f'(wholeL {body} tv {"0" if c=="RUnit" else "_"} r wb st)'
        bpat = body
    w(f'''  letA x v {bpat} tv k r (wv , wb) st =
    subst (λ ts → ParsesAtomExpr ts _ r) (sym (word-toks "let" tv k _))
      (subst (λ ts → ParsesAtomExpr (TWord "let" ∷ ts) _ r) (sym (word-toks x tv _ _))
        (subst (λ ts → ParsesAtomExpr (TWord "let" ∷ TWord x ∷ TEquals ∷ toks (proj₁ (pex 0 true v tv _)) ts) _ r)
          (sym (word-toks "in" tv _ _))
          (atom-let (wholeL v tv _ _ wv stops-in) {rest})))''')
w('''
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
''')
open(os.path.join(PROOF,'Expr.agda'),'a').write('\n'.join(o)+'\n')
