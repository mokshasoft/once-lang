-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.SpecGrammar.Expr — the compiler's expression grammar
-- (`Once.Parser.ExprRelation`) against the Spec's.
--
-- Both grammars build the Spec's expressions (plan 0.122: the compiler's
-- are the Spec's), so a derivation of one is a derivation of the other at
-- the same tree. The Spec's derivation comes back only where what follows
-- is not a string literal (`¬ StrHead`) — the compiler may not end an
-- application before one. A whole program has none
-- (`Once.Adequacy.SpecGrammar.Decl`).
------------------------------------------------------------------------

module Once.Adequacy.SpecGrammar.Expr where

open import Data.Char using (Char)
open import Data.Empty using (⊥-elim)
open import Data.List using (List; []; _∷_; map)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import Relation.Nullary using (¬_)

open import Once.Spec.Surface.Syntax as O using (RVar; RQualified; RResolved; RApp; RLam; RLet; RPair; RDestruct; RUnit; RInt; RFloat; RAnnot; RBinOp; RNeg; OpAdd; OpSub; OpMul; OpDiv; OpMod; OpLt; OpLe; OpGt; OpGe; OpEq; OpNe)
open import Once.Internal.Syntax as O using (RawExpr)
import Once.Spec.Surface.Syntax as S
open import Once.Spec.Surface.Lexing using (Token; TWord; TInt; TFloat; TLParen; TRParen; TLBrace; TRBrace; TColon; TEquals;
  TArrow; TLambda; TComma; TSemicolon; TAt; TPipe; TDot; TPlus; TMinus; TStar; TSlash; TPercent; TAmpersand; TLt; TLe;
  TGt; TGe; TEqEq; TNeq)
open import Once.Spec.Surface.Grammar as G
  hiding (ParsesExpr; ParsesCompTail; ParsesCmp; ParsesAdd; ParsesAddTail; ParsesMul; ParsesMulTail; ParsesUnary;
          ParsesApp; ParsesAppTail; ParsesAtomExpr; ParsesLamParams; ParsesParenCont; ParsesOpChars)
import Once.Parser.Token as P
open import Once.Parser.ExprRelation as E
  hiding (ParsesExpr; ParsesCompTail; ParsesCmp; ParsesAdd; ParsesAddTail; ParsesMul; ParsesMulTail; ParsesUnary;
          ParsesApp; ParsesAppTail; ParsesAtomExpr; ParsesLamParams; ParsesParenCont)
open import Once.Adequacy.SpecLexing using (forget)
open import Once.Adequacy.SpecGrammar.Tokens using (back; isLit; step; peel; peels; NonLits; []; _∷_; stepInt; stepFloat)
open import Data.Bool using (false)
import Once.Parser.TypeRelation
open import Once.Adequacy.SpecGrammar.ExprHeads
open import Once.Adequacy.SpecGrammar.Conv using (toTy)
open import Once.Adequacy.SpecGrammar.GroundTypes using (annot→; annot←)

private
  F : List P.Token → List Token
  F = map forget

  N : List Token → Set
  N r = ¬ StrHead r

------------------------------------------------------------------------
-- The compiler's derivation gives the Spec's
------------------------------------------------------------------------

-- (the compiler's operators are the Spec's: plan 0.122)
opS : O.BinOp → S.BinOp
opS op = op

expr→   : ∀ {toks e rest} → E.ParsesExpr toks e rest → G.ParsesExpr (F toks) e (F rest)
comp→   : ∀ {toks e rest} → E.ParsesComp toks e rest → G.ParsesExpr (F toks) e (F rest)
ctail→  : ∀ {l toks e rest} → E.ParsesCompTail l toks e rest → G.ParsesCompTail l (F toks) e (F rest)
cmp→    : ∀ {toks e rest} → E.ParsesCmp toks e rest → G.ParsesCmp (F toks) e (F rest)
add→    : ∀ {toks e rest} → E.ParsesAdd toks e rest → G.ParsesAdd (F toks) e (F rest)
atail→  : ∀ {l toks e rest} → E.ParsesAddTail l toks e rest → G.ParsesAddTail l (F toks) e (F rest)
mul→    : ∀ {toks e rest} → E.ParsesMul toks e rest → G.ParsesMul (F toks) e (F rest)
mtail→  : ∀ {l toks e rest} → E.ParsesMulTail l toks e rest → G.ParsesMulTail l (F toks) e (F rest)
unary→  : ∀ {toks e rest} → E.ParsesUnary toks e rest → G.ParsesUnary (F toks) e (F rest)
app→    : ∀ {toks e rest} → E.ParsesApp toks e rest → G.ParsesApp (F toks) e (F rest)
aptail→ : ∀ {l toks e rest} → E.ParsesAppTail l toks e rest → G.ParsesAppTail l (F toks) e (F rest)
atom→   : ∀ {toks e rest} → E.ParsesAtomExpr toks e rest → G.ParsesAtomExpr (F toks) e (F rest)
lam→    : ∀ {toks e rest} → E.ParsesLamParams toks e rest → G.ParsesLamParams (F toks) e (F rest)
pcont→  : ∀ {e toks eo rest} → E.ParsesParenCont e toks eo rest → G.ParsesParenCont e (F toks) eo (F rest)
op→     : ∀ {acc toks e rest} → ParsesOpExpr acc toks e rest
        → Σ[ s ∈ String ] (e ≡ RVar s × G.ParsesOpChars (F toks) acc s (F rest))

private
  argStart : ∀ {toks a toks₂} → AppArgOk toks → E.ParsesAtomExpr toks a toks₂ → ArgStart (F toks)
  argStart aao-TLParen _ = as-paren
  argStart aao-TLambda _ = as-lambda
  argStart aao-TInt _ = as-int
  argStart aao-TFloat _ = as-float
  argStart (aao-word nr) _ = as-word (reserved-false→ nr)

  opatom : ∀ {toks e rest} → Σ[ s ∈ String ] (e ≡ RVar s × G.ParsesOpChars (F toks) [] s (F rest))
         → G.ParsesAtomExpr (TLParen ∷ F toks) e (F rest)
  opatom (s , refl , sop) = atom-op sop

  opc : ∀ {t ch acc toks e rest} → OpChar (forget t) ch → Σ[ s ∈ String ] (e ≡ RVar s × G.ParsesOpChars (F toks) (ch ∷ acc) s (F rest))
      → Σ[ s ∈ String ] (e ≡ RVar s × G.ParsesOpChars (F (t ∷ toks)) acc s (F rest))
  opc oc (s , eq , sd) = s , eq , op-char oc sd

expr→ (pe-mk d) = comp→ d

comp→ (pc-mk dc dt) = expr (cmp→ dc) (ctail→ dt)

ctail→ {toks = toks} (pct-done n) = comp-done (notDot→TDot toks n)
ctail→ (pct-dot dc dt) = comp-dot (cmp→ dc) (ctail→ dt)

cmp→ {rest = rest} (pcm-noop da n) = cmp-none (add→ da) (notCmp→ rest n)
cmp→ (pcm-lt dl dr) = cmp ct-lt (add→ dl) (add→ dr)
cmp→ (pcm-le dl dr) = cmp ct-le (add→ dl) (add→ dr)
cmp→ (pcm-gt dl dr) = cmp ct-gt (add→ dl) (add→ dr)
cmp→ (pcm-ge dl dr) = cmp ct-ge (add→ dl) (add→ dr)
cmp→ (pcm-eq dl dr) = cmp ct-eq (add→ dl) (add→ dr)
cmp→ (pcm-ne dl dr) = cmp ct-ne (add→ dl) (add→ dr)

add→ (pa-mk dm dt) = add (mul→ dm) (atail→ dt)

atail→ {toks = toks} (pat-done n) = add-done (notAdd→ toks n)
atail→ (pat-plus dm dt) = add-op at-plus (mul→ dm) (atail→ dt)
atail→ (pat-minus dm dt) = add-op at-minus (mul→ dm) (atail→ dt)

mul→ (pm-mk du dt) = mul (unary→ du) (mtail→ dt)

mtail→ {toks = toks} (pmt-done n) = mul-done (notMul→ toks n)
mtail→ (pmt-star du dt) = mul-op mt-star (unary→ du) (mtail→ dt)
mtail→ (pmt-slash du dt) = mul-op mt-slash (unary→ du) (mtail→ dt)
mtail→ (pmt-percent du dt) = mul-op mt-pct (unary→ du) (mtail→ dt)

unary→ (pu-neg du) = neg (unary→ du)
unary→ (pu-app da) = unary (app→ da)

app→ (papp-mk da dt) = app (atom→ da) (aptail→ dt)

aptail→ (papp-done n) = app-done (notAtom→ n)
aptail→ (papp-arg ok da dt) = app-arg (argStart ok da) (atom→ da) (aptail→ dt)

atom→ pae-unit = atom-unit
atom→ pae-int = atom-int
atom→ pae-float = atom-float
atom→ (pae-var nr nq) = atom-var (reserved-false→ nr) (notQual→ nq)
atom→ (pae-qual nr) = atom-qual (reserved-false→ nr)
atom→ (pae-paren de dc) = atom-paren (expr→ de) (pcont→ dc)
atom→ (pae-lambda dl) = atom-lambda (lam→ dl)
atom→ (pae-let (plet-single dv (plin db))) = atom-let (expr→ dv) (expr→ db)
atom→ (pae-destruct (pd-mk ds (pdof (pdb dl (prb dr))))) = atom-destruct (expr→ ds) (expr→ dl) (expr→ dr)
atom→ (pae-paren-op dop) = opatom (op→ dop)

lam→ (plp-body de) = lam-body (expr→ de)
lam→ (plp-arg dl) = lam-arg (lam→ dl)

pcont→ ppc-close = paren-close
pcont→ (ppc-pair de ppt-close) = paren-pair (expr→ de)
pcont→ (ppc-annot dT) = paren-annot (annot→ dT)

op→ poe-close = _ , refl , op-close
op→ (poe-dot d) = opc oc-dot (op→ d)
op→ (poe-plus d) = opc oc-plus (op→ d)
op→ (poe-minus d) = opc oc-minus (op→ d)
op→ (poe-star d) = opc oc-star (op→ d)
op→ (poe-slash d) = opc oc-slash (op→ d)
op→ (poe-percent d) = opc oc-pct (op→ d)
op→ (poe-lt d) = opc oc-lt (op→ d)
op→ (poe-gt d) = opc oc-gt (op→ d)
op→ (poe-pipe d) = opc oc-pipe (op→ d)
op→ (poe-amp d) = opc oc-amp (op→ d)
op→ (poe-at d) = opc oc-at (op→ d)

------------------------------------------------------------------------
-- The Spec's derivation comes from the compiler's
------------------------------------------------------------------------

-- What follows a part is not a string literal when what follows the whole is not.
ctail-ns : ∀ {l ts e r} → G.ParsesCompTail l ts e r → N r → N ts
ctail-ns (comp-done _) n = n
ctail-ns (comp-dot _ _) n ()

atail-ns : ∀ {l ts e r} → G.ParsesAddTail l ts e r → N r → N ts
atail-ns (add-done _) n = n
atail-ns (add-op at-plus _ _) n ()
atail-ns (add-op at-minus _ _) n ()

mtail-ns : ∀ {l ts e r} → G.ParsesMulTail l ts e r → N r → N ts
mtail-ns (mul-done _) n = n
mtail-ns (mul-op mt-star _ _) n ()
mtail-ns (mul-op mt-slash _ _) n ()
mtail-ns (mul-op mt-pct _ _) n ()

aptail-ns : ∀ {l ts e r} → G.ParsesAppTail l ts e r → N r → N ts
aptail-ns (app-done _) n = n
aptail-ns (app-arg as-paren _ _) n ()
aptail-ns (app-arg as-lambda _ _) n ()
aptail-ns (app-arg as-int _ _) n ()
aptail-ns (app-arg as-float _ _) n ()
aptail-ns (app-arg (as-word _) _ _) n ()

pcont-ns : ∀ {e ts e′ r} → G.ParsesParenCont e ts e′ r → N ts
pcont-ns paren-close ()
pcont-ns (paren-pair _) ()
pcont-ns (paren-annot _) ()

ct-ns : ∀ {t op ts} → CompareToken t op → N (t ∷ ts)
ct-ns ct-lt ()
ct-ns ct-le ()
ct-ns ct-gt ()
ct-ns ct-ge ()
ct-ns ct-eq ()
ct-ns ct-ne ()

-- A compiler derivation over `toks` of the tree.
BackE : (List P.Token → RawExpr → List P.Token → Set) → List P.Token → S.Expr → List Token → Set
BackE Rel toks e r = Σ[ rest ∈ List P.Token ] (Rel toks e rest × F rest ≡ r)

BackET : (RawExpr → List P.Token → RawExpr → List P.Token → Set) → RawExpr → List P.Token → S.Expr → List Token → Set
BackET Rel l toks e r = Σ[ rest ∈ List P.Token ] (Rel l toks e rest × F rest ≡ r)

expr←   : ∀ {ts e r} → G.ParsesExpr ts e r → ∀ toks → F toks ≡ ts → N r → BackE E.ParsesExpr toks e r
ctail←  : ∀ {l ts e r} → G.ParsesCompTail l ts e r → ∀ toks → F toks ≡ ts → N r → BackET E.ParsesCompTail l toks e r
cmp←    : ∀ {ts e r} → G.ParsesCmp ts e r → ∀ toks → F toks ≡ ts → N r → BackE E.ParsesCmp toks e r
add←    : ∀ {ts e r} → G.ParsesAdd ts e r → ∀ toks → F toks ≡ ts → N r → BackE E.ParsesAdd toks e r
atail←  : ∀ {l ts e r} → G.ParsesAddTail l ts e r → ∀ toks → F toks ≡ ts → N r → BackET E.ParsesAddTail l toks e r
mul←    : ∀ {ts e r} → G.ParsesMul ts e r → ∀ toks → F toks ≡ ts → N r → BackE E.ParsesMul toks e r
mtail←  : ∀ {l ts e r} → G.ParsesMulTail l ts e r → ∀ toks → F toks ≡ ts → N r → BackET E.ParsesMulTail l toks e r
unary←  : ∀ {ts e r} → G.ParsesUnary ts e r → ∀ toks → F toks ≡ ts → N r → BackE E.ParsesUnary toks e r
app←    : ∀ {ts e r} → G.ParsesApp ts e r → ∀ toks → F toks ≡ ts → N r → BackE E.ParsesApp toks e r
aptail← : ∀ {l ts e r} → G.ParsesAppTail l ts e r → ∀ toks → F toks ≡ ts → N r → BackET E.ParsesAppTail l toks e r
atom←   : ∀ {ts e r} → G.ParsesAtomExpr ts e r → ∀ toks → F toks ≡ ts → N r → BackE E.ParsesAtomExpr toks e r
lam←    : ∀ {ts e r} → G.ParsesLamParams ts e r → ∀ toks → F toks ≡ ts → N r → BackE E.ParsesLamParams toks e r
pcont←  : ∀ {e ts e″ r} → G.ParsesParenCont e ts e″ r → ∀ toks → F toks ≡ ts → BackET E.ParsesParenCont e toks e″ r
op←     : ∀ {ts acc s r} → G.ParsesOpChars ts acc s r → ∀ toks → F toks ≡ ts
        → Σ[ rest ∈ List P.Token ] (ParsesOpExpr acc toks (RVar s) rest × F rest ≡ r)

private
  comp← : ∀ {toks e₁ ts₁ e r} → BackE E.ParsesCmp toks e₁ ts₁ → G.ParsesCompTail e₁ ts₁ e r → N r
        → BackE E.ParsesExpr toks e r
  comp←₂ : ∀ {toks e₁ toks₁ e r} → E.ParsesCmp toks e₁ toks₁ → BackET E.ParsesCompTail e₁ toks₁ e r
         → BackE E.ParsesExpr toks e r
  comp← (toks₁ , dc , eq) dt n = comp←₂ dc (ctail← dt toks₁ eq n)
  comp←₂ dc (rest , dt , er) = rest , pe-mk (pc-mk dc dt) , er

  ctdot← : ∀ {l toks₁ e₂ ts₂ e r} → BackE E.ParsesCmp toks₁ e₂ ts₂
         → G.ParsesCompTail (RApp (RApp (RVar "compose") l) e₂) ts₂ e r → N r
         → BackET E.ParsesCompTail l (P.TDot ∷ toks₁) e r
  ctdot←₂ : ∀ {l toks₁ e₂ toks₂ e r} → E.ParsesCmp toks₁ e₂ toks₂
          → BackET E.ParsesCompTail (RApp (RApp (RVar "compose") l) e₂) toks₂ e r
          → BackET E.ParsesCompTail l (P.TDot ∷ toks₁) e r
  ctdot← (toks₂ , dc , eq) dt n = ctdot←₂ dc (ctail← dt toks₂ eq n)
  ctdot←₂ dc (rest , dt , er) = rest , pct-dot dc dt , er

  cmpn← : ∀ {toks e r} → BackE E.ParsesAdd toks e r → (∀ {t op} → Starts r t → ¬ CompareToken t op)
        → BackE E.ParsesCmp toks e r
  cmpn← (rest , da , refl) nc = rest , pcm-noop da (notCmp← rest nc) , refl

  -- `l op e`, for the operator `oop` written `u`
  cmp-fin  : ∀ {toks l ts₁ e r} (u : Token) (oop : O.BinOp)
           → (∀ {a b c x y} → E.ParsesAdd a x (back u ∷ b) → E.ParsesAdd b y c → E.ParsesCmp a (RBinOp oop x y) c)
           → isLit u ≡ false
           → BackE E.ParsesAdd toks l (u ∷ ts₁) → G.ParsesAdd ts₁ e r → N r
           → BackE E.ParsesCmp toks (RBinOp oop l e) r
  cmp-fin₁ : ∀ {toks l rest₁ ts₁ e r} {tok : P.Token} (oop : O.BinOp)
           → (∀ {a b c x y} → E.ParsesAdd a x (tok ∷ b) → E.ParsesAdd b y c → E.ParsesCmp a (RBinOp oop x y) c)
           → E.ParsesAdd toks l rest₁
           → Σ[ toks₁ ∈ List P.Token ] (rest₁ ≡ tok ∷ toks₁ × F toks₁ ≡ ts₁)
           → G.ParsesAdd ts₁ e r → N r → BackE E.ParsesCmp toks (RBinOp oop l e) r
  cmp-fin₂ : ∀ {toks l toks₁ e r} {tok : P.Token} (oop : O.BinOp)
           → (∀ {a b c x y} → E.ParsesAdd a x (tok ∷ b) → E.ParsesAdd b y c → E.ParsesCmp a (RBinOp oop x y) c)
           → E.ParsesAdd toks l (tok ∷ toks₁) → BackE E.ParsesAdd toks₁ e r
           → BackE E.ParsesCmp toks (RBinOp oop l e) r
  cmp-fin u oop mk nl (rest₁ , dl , e₁) dr n = cmp-fin₁ oop mk dl (peel nl e₁) dr n
  cmp-fin₁ oop mk dl (toks₁ , refl , e₂) dr n = cmp-fin₂ oop mk dl (add← dr toks₁ e₂ n)
  cmp-fin₂ oop mk dl (rest , dr , e₃) = rest , mk dl dr , e₃

  add←₁ : ∀ {toks e₁ ts₁ e r} → BackE E.ParsesMul toks e₁ ts₁ → G.ParsesAddTail e₁ ts₁ e r → N r
        → BackE E.ParsesAdd toks e r
  add←₂ : ∀ {toks e₁ toks₁ e r} → E.ParsesMul toks e₁ toks₁ → BackET E.ParsesAddTail e₁ toks₁ e r
        → BackE E.ParsesAdd toks e r
  add←₁ (toks₁ , dm , eq) dt n = add←₂ dm (atail← dt toks₁ eq n)
  add←₂ dm (rest , dt , er) = rest , pa-mk dm dt , er

  aop← : ∀ {l toks₁ e₂ ts₂ e r} (tok : P.Token) (oop : O.BinOp)
       → (∀ {lft t1 t2 rt e rst} → E.ParsesMul t1 rt t2 → E.ParsesAddTail (RBinOp oop lft rt) t2 e rst
          → E.ParsesAddTail lft (tok ∷ t1) e rst)
       → BackE E.ParsesMul toks₁ e₂ ts₂ → G.ParsesAddTail (RBinOp oop l e₂) ts₂ e r → N r
       → BackET E.ParsesAddTail l (tok ∷ toks₁) e r
  aop←₂ : ∀ {l toks₁ e₂ toks₂ e r} {tok : P.Token} {oop : O.BinOp}
        → (∀ {lft t1 t2 rt e rst} → E.ParsesMul t1 rt t2 → E.ParsesAddTail (RBinOp oop lft rt) t2 e rst
           → E.ParsesAddTail lft (tok ∷ t1) e rst)
        → E.ParsesMul toks₁ e₂ toks₂ → BackET E.ParsesAddTail (RBinOp oop l e₂) toks₂ e r
        → BackET E.ParsesAddTail l (tok ∷ toks₁) e r
  aop← tok oop mk (toks₂ , dm , eq) dt n = aop←₂ mk dm (atail← dt toks₂ eq n)
  aop←₂ mk dm (rest , dt , er) = rest , mk dm dt , er

  mul←₁ : ∀ {toks e₁ ts₁ e r} → BackE E.ParsesUnary toks e₁ ts₁ → G.ParsesMulTail e₁ ts₁ e r → N r
        → BackE E.ParsesMul toks e r
  mul←₂ : ∀ {toks e₁ toks₁ e r} → E.ParsesUnary toks e₁ toks₁ → BackET E.ParsesMulTail e₁ toks₁ e r
        → BackE E.ParsesMul toks e r
  mul←₁ (toks₁ , du , eq) dt n = mul←₂ du (mtail← dt toks₁ eq n)
  mul←₂ du (rest , dt , er) = rest , pm-mk du dt , er

  mop← : ∀ {l toks₁ e₂ ts₂ e r} (tok : P.Token) (oop : O.BinOp)
       → (∀ {lft t1 t2 rt e rst} → E.ParsesUnary t1 rt t2 → E.ParsesMulTail (RBinOp oop lft rt) t2 e rst
          → E.ParsesMulTail lft (tok ∷ t1) e rst)
       → BackE E.ParsesUnary toks₁ e₂ ts₂ → G.ParsesMulTail (RBinOp oop l e₂) ts₂ e r → N r
       → BackET E.ParsesMulTail l (tok ∷ toks₁) e r
  mop←₂ : ∀ {l toks₁ e₂ toks₂ e r} {tok : P.Token} {oop : O.BinOp}
        → (∀ {lft t1 t2 rt e rst} → E.ParsesUnary t1 rt t2 → E.ParsesMulTail (RBinOp oop lft rt) t2 e rst
           → E.ParsesMulTail lft (tok ∷ t1) e rst)
        → E.ParsesUnary toks₁ e₂ toks₂ → BackET E.ParsesMulTail (RBinOp oop l e₂) toks₂ e r
        → BackET E.ParsesMulTail l (tok ∷ toks₁) e r
  mop← tok oop mk (toks₂ , du , eq) dt n = mop←₂ mk du (mtail← dt toks₂ eq n)
  mop←₂ mk du (rest , dt , er) = rest , mk du dt , er

  neg←₁ : ∀ {toks e r} → BackE E.ParsesUnary toks e r → BackE E.ParsesUnary (P.TMinus ∷ toks) (RNeg e) r
  neg←₁ (rest , du , er) = rest , pu-neg du , er

  un←₁ : ∀ {toks e r} → BackE E.ParsesApp toks e r → BackE E.ParsesUnary toks e r
  un←₁ (rest , da , er) = rest , pu-app da , er

  app←₁ : ∀ {toks f ts₁ e r} → BackE E.ParsesAtomExpr toks f ts₁ → G.ParsesAppTail f ts₁ e r → N r
        → BackE E.ParsesApp toks e r
  app←₂ : ∀ {toks f toks₁ e r} → E.ParsesAtomExpr toks f toks₁ → BackET E.ParsesAppTail f toks₁ e r
        → BackE E.ParsesApp toks e r
  app←₁ (toks₁ , da , eq) dt n = app←₂ da (aptail← dt toks₁ eq n)
  app←₂ da (rest , dt , er) = rest , papp-mk da dt , er

  aparg← : ∀ {l toks a ts₂ e r} → AppArgOk toks → BackE E.ParsesAtomExpr toks a ts₂
         → G.ParsesAppTail (RApp l a) ts₂ e r → N r → BackET E.ParsesAppTail l toks e r
  aparg←₂ : ∀ {l toks a toks₂ e r} → AppArgOk toks → E.ParsesAtomExpr toks a toks₂
          → BackET E.ParsesAppTail (RApp l a) toks₂ e r → BackET E.ParsesAppTail l toks e r
  aparg← ok (toks₂ , da , eq) dt n = aparg←₂ ok da (aptail← dt toks₂ eq n)
  aparg←₂ ok da (rest , dt , er) = rest , papp-arg ok da dt , er

  paren← : ∀ {toks e ts₁ e″ r} → BackE E.ParsesExpr toks e ts₁ → G.ParsesParenCont e ts₁ e″ r
         → BackE E.ParsesAtomExpr (P.TLParen ∷ toks) e″ r
  paren←₂ : ∀ {toks e toks₁ e″ r} → E.ParsesExpr toks e toks₁ → BackET E.ParsesParenCont e toks₁ e″ r
          → BackE E.ParsesAtomExpr (P.TLParen ∷ toks) e″ r
  paren← (toks₁ , de , eq) dc = paren←₂ de (pcont← dc toks₁ eq)
  paren←₂ de (rest , dc , er) = rest , pae-paren de dc , er

  op←₁ : ∀ {toks s r} → Σ[ rest ∈ List P.Token ] (ParsesOpExpr [] toks (RVar s) rest × F rest ≡ r)
       → BackE E.ParsesAtomExpr (P.TLParen ∷ toks) (RVar s) r
  op←₁ (rest , d , er) = rest , pae-paren-op d , er

  lam←₁ : ∀ {toks e r} → BackE E.ParsesLamParams toks e r → BackE E.ParsesAtomExpr (P.TLambda ∷ toks) e r
  lam←₁ (rest , dl , er) = rest , pae-lambda dl , er

  let←₁ : ∀ {x toks v ts₁ b r} → BackE E.ParsesExpr toks v (TWord "in" ∷ ts₁) → G.ParsesExpr ts₁ b r → N r
        → BackE E.ParsesAtomExpr (P.TWord "let" ∷ P.TWord x ∷ P.TEquals ∷ toks) (RLet x v b) r
  let←₂ : ∀ {x toks v rest₁ ts₁ b r} → E.ParsesExpr toks v rest₁
        → Σ[ toks₁ ∈ List P.Token ] (rest₁ ≡ P.TWord "in" ∷ toks₁ × F toks₁ ≡ ts₁) → G.ParsesExpr ts₁ b r → N r
        → BackE E.ParsesAtomExpr (P.TWord "let" ∷ P.TWord x ∷ P.TEquals ∷ toks) (RLet x v b) r
  let←₃ : ∀ {x toks v toks₁ b r} → E.ParsesExpr toks v (P.TWord "in" ∷ toks₁) → BackE E.ParsesExpr toks₁ b r
        → BackE E.ParsesAtomExpr (P.TWord "let" ∷ P.TWord x ∷ P.TEquals ∷ toks) (RLet x v b) r
  let←₁ (rest₁ , dv , e₁) db n = let←₂ dv (peel refl e₁) db n
  let←₂ dv (toks₁ , refl , e₂) db n = let←₃ dv (expr← db toks₁ e₂ n)
  let←₃ dv (rest , db , er) = rest , pae-let (plet-single dv (plin db)) , er

  de←₁ : ∀ {toks s x ts₁ l y ts₂ rv r}
       → BackE E.ParsesExpr toks s (TWord "of" ∷ TLBrace ∷ TWord "Left" ∷ TWord x ∷ TArrow ∷ ts₁)
       → G.ParsesExpr ts₁ l (TSemicolon ∷ TWord "Right" ∷ TWord y ∷ TArrow ∷ ts₂) → G.ParsesExpr ts₂ rv (TRBrace ∷ r)
       → BackE E.ParsesAtomExpr (P.TWord "destruct" ∷ toks) (RDestruct s x l y rv) r
  de←₂ : ∀ {toks s rest₁ x ts₁ l y ts₂ rv r} → E.ParsesExpr toks s rest₁
       → Σ[ toks₁ ∈ List P.Token ] (rest₁ ≡ P.TWord "of" ∷ P.TLBrace ∷ P.TWord "Left" ∷ P.TWord x ∷ P.TArrow ∷ toks₁ × F toks₁ ≡ ts₁)
       → G.ParsesExpr ts₁ l (TSemicolon ∷ TWord "Right" ∷ TWord y ∷ TArrow ∷ ts₂) → G.ParsesExpr ts₂ rv (TRBrace ∷ r)
       → BackE E.ParsesAtomExpr (P.TWord "destruct" ∷ toks) (RDestruct s x l y rv) r
  de←₃ : ∀ {toks s x toks₁ l rest₂ y ts₂ rv r}
       → E.ParsesExpr toks s (P.TWord "of" ∷ P.TLBrace ∷ P.TWord "Left" ∷ P.TWord x ∷ P.TArrow ∷ toks₁)
       → E.ParsesExpr toks₁ l rest₂
       → Σ[ toks₂ ∈ List P.Token ] (rest₂ ≡ P.TSemicolon ∷ P.TWord "Right" ∷ P.TWord y ∷ P.TArrow ∷ toks₂ × F toks₂ ≡ ts₂)
       → G.ParsesExpr ts₂ rv (TRBrace ∷ r)
       → BackE E.ParsesAtomExpr (P.TWord "destruct" ∷ toks) (RDestruct s x l y rv) r
  de←₄ : ∀ {toks s x toks₁ l y toks₂ rv rest₃ r}
       → E.ParsesExpr toks s (P.TWord "of" ∷ P.TLBrace ∷ P.TWord "Left" ∷ P.TWord x ∷ P.TArrow ∷ toks₁)
       → E.ParsesExpr toks₁ l (P.TSemicolon ∷ P.TWord "Right" ∷ P.TWord y ∷ P.TArrow ∷ toks₂)
       → E.ParsesExpr toks₂ rv rest₃
       → Σ[ rest ∈ List P.Token ] (rest₃ ≡ P.TRBrace ∷ rest × F rest ≡ r)
       → BackE E.ParsesAtomExpr (P.TWord "destruct" ∷ toks) (RDestruct s x l y rv) r
  de←₂b : ∀ {toks s x toks₁ l y ts₂ rv r}
        → E.ParsesExpr toks s (P.TWord "of" ∷ P.TLBrace ∷ P.TWord "Left" ∷ P.TWord x ∷ P.TArrow ∷ toks₁)
        → BackE E.ParsesExpr toks₁ l (TSemicolon ∷ TWord "Right" ∷ TWord y ∷ TArrow ∷ ts₂) → G.ParsesExpr ts₂ rv (TRBrace ∷ r)
        → BackE E.ParsesAtomExpr (P.TWord "destruct" ∷ toks) (RDestruct s x l y rv) r
  de←₃b : ∀ {toks s x toks₁ l y toks₂ rv r}
        → E.ParsesExpr toks s (P.TWord "of" ∷ P.TLBrace ∷ P.TWord "Left" ∷ P.TWord x ∷ P.TArrow ∷ toks₁)
        → E.ParsesExpr toks₁ l (P.TSemicolon ∷ P.TWord "Right" ∷ P.TWord y ∷ P.TArrow ∷ toks₂)
        → BackE E.ParsesExpr toks₂ rv (TRBrace ∷ r)
        → BackE E.ParsesAtomExpr (P.TWord "destruct" ∷ toks) (RDestruct s x l y rv) r
  de←₁ (rest₁ , ds , e₁) dl dr =
    de←₂ ds (peels (TWord "of" ∷ TLBrace ∷ TWord "Left" ∷ TWord _ ∷ TArrow ∷ []) (refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ []) e₁) dl dr
  de←₂ ds (toks₁ , refl , e₂) dl dr = de←₂b ds (expr← dl toks₁ e₂ (λ ())) dr
  de←₂b ds (rest₂ , dl , e₃) dr =
    de←₃ ds dl (peels (TSemicolon ∷ TWord "Right" ∷ TWord _ ∷ TArrow ∷ []) (refl ∷ refl ∷ refl ∷ refl ∷ []) e₃) dr
  de←₃ ds dl (toks₂ , refl , e₄) dr = de←₃b ds dl (expr← dr toks₂ e₄ (λ ()))
  de←₃b ds dl (rest₃ , dr , e₅) = de←₄ ds dl dr (peel refl e₅)
  de←₄ ds dl dr (rest , refl , e₆) = rest , pae-destruct (pd-mk ds (pdof (pdb dl (prb dr)))) , e₆

  lamb←₁ : ∀ {toks e r} → BackE E.ParsesExpr toks e r → BackE E.ParsesLamParams (P.TArrow ∷ toks) e r
  lamb←₁ (rest , de , er) = rest , plp-body de , er

  lama←₁ : ∀ {x toks e r} → BackE E.ParsesLamParams toks e r → BackE E.ParsesLamParams (P.TWord x ∷ toks) (RLam x e) r
  lama←₁ (rest , dl , er) = rest , plp-arg dl , er

  pair←₁ : ∀ {e toks b r} → BackE E.ParsesExpr toks b (TRParen ∷ r)
         → BackET E.ParsesParenCont e (P.TComma ∷ toks) (RPair e b) r
  pair←₂ : ∀ {e toks b rest₁ r} → E.ParsesExpr toks b rest₁
         → Σ[ rest ∈ List P.Token ] (rest₁ ≡ P.TRParen ∷ rest × F rest ≡ r)
         → BackET E.ParsesParenCont e (P.TComma ∷ toks) (RPair e b) r
  pair←₁ (rest₁ , db , e₁) = pair←₂ db (peel refl e₁)
  pair←₂ db (rest , refl , e₂) = rest , ppc-pair db ppt-close , e₂

  annot←₁ : ∀ {e toks A r}
          → Σ[ T ∈ _ ] Σ[ rest₁ ∈ List P.Token ] (Once.Parser.TypeRelation.ParsesType toks T rest₁ × toTy T ≡ A × F rest₁ ≡ TRParen ∷ r)
          → BackET E.ParsesParenCont e (P.TColon ∷ toks) (RAnnot e A) r
  annot←₂ : ∀ {e toks T rest₁ r} → Once.Parser.TypeRelation.ParsesType toks T rest₁
          → Σ[ rest ∈ List P.Token ] (rest₁ ≡ P.TRParen ∷ rest × F rest ≡ r)
          → BackET E.ParsesParenCont e (P.TColon ∷ toks) (RAnnot e (toTy T)) r
  annot←₁ (T , rest₁ , dT , refl , e₁) = annot←₂ dT (peel refl e₁)
  annot←₂ dT (rest , refl , e₂) = rest , ppc-annot dT , e₂

  opc← : ∀ {toks acc ch s r} (t : P.Token)
       → (∀ {acc toks e rest} → ParsesOpExpr (ch ∷ acc) toks e rest → ParsesOpExpr acc (t ∷ toks) e rest)
       → Σ[ rest ∈ List P.Token ] (ParsesOpExpr (ch ∷ acc) toks (RVar s) rest × F rest ≡ r)
       → Σ[ rest ∈ List P.Token ] (ParsesOpExpr acc (t ∷ toks) (RVar s) rest × F rest ≡ r)
  opc← t mk (rest , d , er) = rest , mk d , er

expr← (expr dc dt) toks e n = comp← (cmp← dc toks e (ctail-ns dt n)) dt n

ctail← (comp-done x) toks refl n = toks , pct-done (notDot← toks x) , refl
ctail← {l = l} (comp-dot dc dt) toks e n =
  step (λ z → BackET E.ParsesCompTail l z _ _) refl e (λ {toks′} e′ → ctdot← (cmp← dc toks′ e′ (ctail-ns dt n)) dt n)

cmp← (cmp-none da nc) toks e n = cmpn← (add← da toks e n) nc
cmp← (cmp ct-lt dl dr) toks e n = cmp-fin TLt OpLt pcm-lt refl (add← dl toks e (ct-ns ct-lt)) dr n
cmp← (cmp ct-le dl dr) toks e n = cmp-fin TLe OpLe pcm-le refl (add← dl toks e (ct-ns ct-le)) dr n
cmp← (cmp ct-gt dl dr) toks e n = cmp-fin TGt OpGt pcm-gt refl (add← dl toks e (ct-ns ct-gt)) dr n
cmp← (cmp ct-ge dl dr) toks e n = cmp-fin TGe OpGe pcm-ge refl (add← dl toks e (ct-ns ct-ge)) dr n
cmp← (cmp ct-eq dl dr) toks e n = cmp-fin TEqEq OpEq pcm-eq refl (add← dl toks e (ct-ns ct-eq)) dr n
cmp← (cmp ct-ne dl dr) toks e n = cmp-fin TNeq OpNe pcm-ne refl (add← dl toks e (ct-ns ct-ne)) dr n

add← (add dm dt) toks e n = add←₁ (mul← dm toks e (atail-ns dt n)) dt n

atail← (add-done x) toks refl n = toks , pat-done (notAdd← toks x) , refl
atail← {l = l} (add-op at-plus dm dt) toks e n =
  step (λ z → BackET E.ParsesAddTail l z _ _) refl e (λ {toks′} e′ →
    aop← P.TPlus OpAdd pat-plus (mul← dm toks′ e′ (atail-ns dt n)) dt n)
atail← {l = l} (add-op at-minus dm dt) toks e n =
  step (λ z → BackET E.ParsesAddTail l z _ _) refl e (λ {toks′} e′ →
    aop← P.TMinus OpSub pat-minus (mul← dm toks′ e′ (atail-ns dt n)) dt n)

mul← (mul du dt) toks e n = mul←₁ (unary← du toks e (mtail-ns dt n)) dt n

mtail← (mul-done x) toks refl n = toks , pmt-done (notMul← toks x) , refl
mtail← {l = l} (mul-op mt-star du dt) toks e n =
  step (λ z → BackET E.ParsesMulTail l z _ _) refl e (λ {toks′} e′ →
    mop← P.TStar OpMul pmt-star (unary← du toks′ e′ (mtail-ns dt n)) dt n)
mtail← {l = l} (mul-op mt-slash du dt) toks e n =
  step (λ z → BackET E.ParsesMulTail l z _ _) refl e (λ {toks′} e′ →
    mop← P.TSlash OpDiv pmt-slash (unary← du toks′ e′ (mtail-ns dt n)) dt n)
mtail← {l = l} (mul-op mt-pct du dt) toks e n =
  step (λ z → BackET E.ParsesMulTail l z _ _) refl e (λ {toks′} e′ →
    mop← P.TPercent OpMod pmt-percent (unary← du toks′ e′ (mtail-ns dt n)) dt n)

unary← (neg du) toks e n = step (λ z → BackE E.ParsesUnary z _ _) refl e (λ {toks′} e′ → neg←₁ (unary← du toks′ e′ n))
unary← (unary da) toks e n = un←₁ (app← da toks e n)

app← (app da dt) toks e n = app←₁ (atom← da toks e (aptail-ns dt n)) dt n

aptail← (app-done x) toks refl n = toks , papp-done (notAtom← toks x n) , refl
aptail← (app-arg as da dt) toks e n =
  aparg← (argOk← toks (subst ArgStart (sym e) as)) (atom← da toks e (aptail-ns dt n)) dt n

atom← atom-unit toks e n =
  step (λ z → BackE E.ParsesAtomExpr z _ _) refl e (λ e₁ →
  step (λ z → BackE E.ParsesAtomExpr (P.TLParen ∷ z) _ _) refl e₁ (λ {toks′} e₂ →
  toks′ , pae-unit , e₂))
atom← atom-int toks e n = stepInt (λ z → BackE E.ParsesAtomExpr z _ _) e (λ p {toks′} e′ → toks′ , pae-int , e′)
atom← atom-float toks e n = stepFloat (λ z → BackE E.ParsesAtomExpr z _ _) e (λ p {toks′} e′ → toks′ , pae-float , e′)
atom← (atom-var nr nq) toks e n =
  step (λ z → BackE E.ParsesAtomExpr z _ _) refl e (λ {toks′} e′ →
  toks′ , pae-var (reserved-false nr) (notQual← toks′ (subst (λ z → ¬ QualSuffix z) (sym e′) nq)) , e′)
atom← (atom-qual nr) toks e n =
  step (λ z → BackE E.ParsesAtomExpr z _ _) refl e (λ e₁ →
  step (λ z → BackE E.ParsesAtomExpr (P.TWord _ ∷ z) _ _) refl e₁ (λ e₂ →
  step (λ z → BackE E.ParsesAtomExpr (P.TWord _ ∷ P.TAt ∷ z) _ _) refl e₂ (λ {toks′} e₃ →
  toks′ , pae-qual (reserved-false nr) , e₃)))
atom← (atom-paren de dc) toks e n =
  step (λ z → BackE E.ParsesAtomExpr z _ _) refl e (λ {toks′} e′ → paren← (expr← de toks′ e′ (pcont-ns dc)) dc)
atom← (atom-op dop) toks e n =
  step (λ z → BackE E.ParsesAtomExpr z _ _) refl e (λ {toks′} e′ → op←₁ (op← dop toks′ e′))
atom← (atom-lambda dl) toks e n =
  step (λ z → BackE E.ParsesAtomExpr z _ _) refl e (λ {toks′} e′ → lam←₁ (lam← dl toks′ e′ n))
atom← (atom-let dv db) toks e n =
  step (λ z → BackE E.ParsesAtomExpr z _ _) refl e (λ e₁ →
  step (λ z → BackE E.ParsesAtomExpr (P.TWord "let" ∷ z) _ _) refl e₁ (λ e₂ →
  step (λ z → BackE E.ParsesAtomExpr (P.TWord "let" ∷ P.TWord _ ∷ z) _ _) refl e₂ (λ {toks′} e₃ →
  let←₁ (expr← dv toks′ e₃ (λ ())) db n)))
atom← (atom-destruct ds dl dr) toks e n =
  step (λ z → BackE E.ParsesAtomExpr z _ _) refl e (λ {toks′} e′ → de←₁ (expr← ds toks′ e′ (λ ())) dl dr)

lam← (lam-body de) toks e n = step (λ z → BackE E.ParsesLamParams z _ _) refl e (λ {toks′} e′ → lamb←₁ (expr← de toks′ e′ n))
lam← (lam-arg dl) toks e n = step (λ z → BackE E.ParsesLamParams z _ _) refl e (λ {toks′} e′ → lama←₁ (lam← dl toks′ e′ n))

pcont← {e = e} paren-close toks eq = step (λ z → BackET E.ParsesParenCont e z _ _) refl eq (λ {toks′} e′ → toks′ , ppc-close , e′)
pcont← {e = e} (paren-pair de) toks eq =
  step (λ z → BackET E.ParsesParenCont e z _ _) refl eq (λ {toks′} e′ → pair←₁ (expr← de toks′ e′ (λ ())))
pcont← {e = e} (paren-annot dT) toks eq =
  step (λ z → BackET E.ParsesParenCont e z _ _) refl eq (λ {toks′} e′ → annot←₁ (annot← dT toks′ e′))

op← op-close toks e = step (λ z → Σ[ rest ∈ List P.Token ] (ParsesOpExpr (_ ∷ _) z (RVar _) rest × F rest ≡ _)) refl e
  (λ {toks′} e′ → toks′ , poe-close , e′)
op← (op-char oc-dot d) toks e = step (λ z → Σ[ rest ∈ List P.Token ] (ParsesOpExpr _ z (RVar _) rest × F rest ≡ _)) refl e
  (λ {toks′} e′ → opc← P.TDot poe-dot (op← d toks′ e′))
op← (op-char oc-plus d) toks e = step (λ z → Σ[ rest ∈ List P.Token ] (ParsesOpExpr _ z (RVar _) rest × F rest ≡ _)) refl e
  (λ {toks′} e′ → opc← P.TPlus poe-plus (op← d toks′ e′))
op← (op-char oc-minus d) toks e = step (λ z → Σ[ rest ∈ List P.Token ] (ParsesOpExpr _ z (RVar _) rest × F rest ≡ _)) refl e
  (λ {toks′} e′ → opc← P.TMinus poe-minus (op← d toks′ e′))
op← (op-char oc-star d) toks e = step (λ z → Σ[ rest ∈ List P.Token ] (ParsesOpExpr _ z (RVar _) rest × F rest ≡ _)) refl e
  (λ {toks′} e′ → opc← P.TStar poe-star (op← d toks′ e′))
op← (op-char oc-slash d) toks e = step (λ z → Σ[ rest ∈ List P.Token ] (ParsesOpExpr _ z (RVar _) rest × F rest ≡ _)) refl e
  (λ {toks′} e′ → opc← P.TSlash poe-slash (op← d toks′ e′))
op← (op-char oc-pct d) toks e = step (λ z → Σ[ rest ∈ List P.Token ] (ParsesOpExpr _ z (RVar _) rest × F rest ≡ _)) refl e
  (λ {toks′} e′ → opc← P.TPercent poe-percent (op← d toks′ e′))
op← (op-char oc-lt d) toks e = step (λ z → Σ[ rest ∈ List P.Token ] (ParsesOpExpr _ z (RVar _) rest × F rest ≡ _)) refl e
  (λ {toks′} e′ → opc← P.TLt poe-lt (op← d toks′ e′))
op← (op-char oc-gt d) toks e = step (λ z → Σ[ rest ∈ List P.Token ] (ParsesOpExpr _ z (RVar _) rest × F rest ≡ _)) refl e
  (λ {toks′} e′ → opc← P.TGt poe-gt (op← d toks′ e′))
op← (op-char oc-pipe d) toks e = step (λ z → Σ[ rest ∈ List P.Token ] (ParsesOpExpr _ z (RVar _) rest × F rest ≡ _)) refl e
  (λ {toks′} e′ → opc← P.TPipe poe-pipe (op← d toks′ e′))
op← (op-char oc-amp d) toks e = step (λ z → Σ[ rest ∈ List P.Token ] (ParsesOpExpr _ z (RVar _) rest × F rest ≡ _)) refl e
  (λ {toks′} e′ → opc← P.TAmpersand poe-amp (op← d toks′ e′))
op← (op-char oc-at d) toks e = step (λ z → Σ[ rest ∈ List P.Token ] (ParsesOpExpr _ z (RVar _) rest × F rest ≡ _)) refl e
  (λ {toks′} e′ → opc← P.TAt poe-at (op← d toks′ e′))
