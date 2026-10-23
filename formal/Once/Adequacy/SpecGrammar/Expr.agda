-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.SpecGrammar.Expr — the compiler's expression grammar
-- (`Once.Parser.ExprRelation`) against the Spec's.
--
-- The compiler reads more than the Spec: a string literal is an atom to
-- it (the type checker then rejects it), and to the Spec no rule reads one.
-- So the two meet on the trees that embed (`Emb`: every node but a string
-- literal, `ana` and a resolved name has its Spec counterpart), and the
-- Spec's derivation comes back only where what follows is not a string
-- literal (`¬ StrHead`) — the compiler may not end an application before
-- one. A whole program has neither (`Once.Adequacy.SpecGrammar.Decl`).
------------------------------------------------------------------------

module Once.Adequacy.SpecGrammar.Expr where

open import Data.Char using (Char)
open import Data.Empty using (⊥-elim)
open import Data.List using (List; []; _∷_; map)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import Relation.Nullary using (¬_)

open import Once.Internal.Syntax as O
  using (RawExpr; RVar; RQualified; RResolved; RApp; RLam; RLet; RPair; RDestruct; RUnit; RInt; RFloat;
         RAnnot; RBinOp; RUnaryOp; OpNeg; OpAdd; OpSub; OpMul; OpDiv; OpMod; OpLt; OpLe; OpGt; OpGe; OpEq; OpNe)
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
open import Once.Adequacy.SpecGrammar.TypeRF using (type-rf)
open import Once.Internal.Type.WellFormed using (RigidFree)

private
  F : List P.Token → List Token
  F = map forget

  N : List Token → Set
  N r = ¬ StrHead r

------------------------------------------------------------------------
-- The trees that embed
------------------------------------------------------------------------

opS : O.BinOp → S.BinOp
opS OpAdd = S.OpAdd
opS OpSub = S.OpSub
opS OpMul = S.OpMul
opS OpDiv = S.OpDiv
opS OpMod = S.OpMod
opS OpLt  = S.OpLt
opS OpLe  = S.OpLe
opS OpGt  = S.OpGt
opS OpGe  = S.OpGe
opS OpEq  = S.OpEq
opS OpNe  = S.OpNe

data Emb : RawExpr → S.Expr → Set where
  e-var      : ∀ {x} → Emb (RVar x) (S.RVar x)
  e-qual     : ∀ {x a} → Emb (RQualified x a) (S.RQualified x a)
  e-res      : ∀ {c} → Emb (RResolved c) (S.RResolved c)
  e-app      : ∀ {f a f′ a′} → Emb f f′ → Emb a a′ → Emb (RApp f a) (S.RApp f′ a′)
  e-lam      : ∀ {x b b′} → Emb b b′ → Emb (RLam x b) (S.RLam x b′)
  e-let      : ∀ {x v b v′ b′} → Emb v v′ → Emb b b′ → Emb (RLet x v b) (S.RLet x v′ b′)
  e-pair     : ∀ {a b a′ b′} → Emb a a′ → Emb b b′ → Emb (RPair a b) (S.RPair a′ b′)
  e-destruct : ∀ {s x l y r s′ l′ r′} → Emb s s′ → Emb l l′ → Emb r r′ → Emb (RDestruct s x l y r) (S.RDestruct s′ x l′ y r′)
  e-unit     : Emb RUnit S.RUnit
  e-int      : ∀ {n} → Emb (RInt n) (S.RInt n)
  e-float    : ∀ {i f l} → Emb (RFloat i f l) (S.RFloat i f l)
  -- (a parsed annotation is a surface type: no rigid parameter)
  e-annot    : ∀ {e e′ T} → RigidFree T → Emb e e′ → Emb (RAnnot e T) (S.RAnnot e′ (toTy T))
  e-binop    : ∀ {op a b a′ b′} → Emb a a′ → Emb b b′ → Emb (RBinOp op a b) (S.RBinOp (opS op) a′ b′)
  e-neg      : ∀ {e e′} → Emb e e′ → Emb (RUnaryOp OpNeg e) (S.RNeg e′)

------------------------------------------------------------------------
-- The compiler's derivation gives the Spec's
------------------------------------------------------------------------

expr→   : ∀ {toks e rest e′} → E.ParsesExpr toks e rest → Emb e e′ → G.ParsesExpr (F toks) e′ (F rest)
comp→   : ∀ {toks e rest e′} → E.ParsesComp toks e rest → Emb e e′ → G.ParsesExpr (F toks) e′ (F rest)
ctail→  : ∀ {l toks e rest e′} → E.ParsesCompTail l toks e rest → Emb e e′
        → Σ[ l′ ∈ S.Expr ] (Emb l l′ × G.ParsesCompTail l′ (F toks) e′ (F rest))
cmp→    : ∀ {toks e rest e′} → E.ParsesCmp toks e rest → Emb e e′ → G.ParsesCmp (F toks) e′ (F rest)
add→    : ∀ {toks e rest e′} → E.ParsesAdd toks e rest → Emb e e′ → G.ParsesAdd (F toks) e′ (F rest)
atail→  : ∀ {l toks e rest e′} → E.ParsesAddTail l toks e rest → Emb e e′
        → Σ[ l′ ∈ S.Expr ] (Emb l l′ × G.ParsesAddTail l′ (F toks) e′ (F rest))
mul→    : ∀ {toks e rest e′} → E.ParsesMul toks e rest → Emb e e′ → G.ParsesMul (F toks) e′ (F rest)
mtail→  : ∀ {l toks e rest e′} → E.ParsesMulTail l toks e rest → Emb e e′
        → Σ[ l′ ∈ S.Expr ] (Emb l l′ × G.ParsesMulTail l′ (F toks) e′ (F rest))
unary→  : ∀ {toks e rest e′} → E.ParsesUnary toks e rest → Emb e e′ → G.ParsesUnary (F toks) e′ (F rest)
app→    : ∀ {toks e rest e′} → E.ParsesApp toks e rest → Emb e e′ → G.ParsesApp (F toks) e′ (F rest)
aptail→ : ∀ {l toks e rest e′} → E.ParsesAppTail l toks e rest → Emb e e′
        → Σ[ l′ ∈ S.Expr ] (Emb l l′ × G.ParsesAppTail l′ (F toks) e′ (F rest))
atom→   : ∀ {toks e rest e′} → E.ParsesAtomExpr toks e rest → Emb e e′ → G.ParsesAtomExpr (F toks) e′ (F rest)
lam→    : ∀ {toks e rest e′} → E.ParsesLamParams toks e rest → Emb e e′ → G.ParsesLamParams (F toks) e′ (F rest)
pcont→  : ∀ {e toks eo rest e″} → E.ParsesParenCont e toks eo rest → Emb eo e″
        → Σ[ e′ ∈ S.Expr ] (Emb e e′ × G.ParsesParenCont e′ (F toks) e″ (F rest))
op→     : ∀ {acc toks e rest} → ParsesOpExpr acc toks e rest
        → Σ[ s ∈ String ] (e ≡ RVar s × G.ParsesOpChars (F toks) acc s (F rest))

private
  comp₁ : ∀ {toks e₁ toks₁ e′ rest} → E.ParsesCmp toks e₁ toks₁ → Σ[ l′ ∈ S.Expr ] (Emb e₁ l′ × G.ParsesCompTail l′ (F toks₁) e′ (F rest))
        → G.ParsesExpr (F toks) e′ (F rest)
  comp₁ dc (l′ , el , st) = expr (cmp→ dc el) st

  ctdot₁ : ∀ {left toks₁ right toks₂ e′ rest} → E.ParsesCmp toks₁ right toks₂
         → Σ[ l″ ∈ S.Expr ] (Emb (RApp (RApp (RVar "compose") left) right) l″ × G.ParsesCompTail l″ (F toks₂) e′ (F rest))
         → Σ[ l′ ∈ S.Expr ] (Emb left l′ × G.ParsesCompTail l′ (TDot ∷ F toks₁) e′ (F rest))
  ctdot₁ dc (_ , e-app (e-app e-var el) er , st) = _ , el , comp-dot (cmp→ dc er) st

  add₁ : ∀ {toks e₁ toks₁ e′ rest} → E.ParsesMul toks e₁ toks₁ → Σ[ l′ ∈ S.Expr ] (Emb e₁ l′ × G.ParsesAddTail l′ (F toks₁) e′ (F rest))
       → G.ParsesAdd (F toks) e′ (F rest)
  add₁ dm (l′ , el , st) = add (mul→ dm el) st

  aop₁ : ∀ {op t left toks₁ right toks₂ e′ rest} → AddToken t (opS op) → E.ParsesMul toks₁ right toks₂
       → Σ[ l″ ∈ S.Expr ] (Emb (RBinOp op left right) l″ × G.ParsesAddTail l″ (F toks₂) e′ (F rest))
       → Σ[ l′ ∈ S.Expr ] (Emb left l′ × G.ParsesAddTail l′ (t ∷ F toks₁) e′ (F rest))
  aop₁ at dm (_ , e-binop el er , st) = _ , el , add-op at (mul→ dm er) st

  mul₁ : ∀ {toks e₁ toks₁ e′ rest} → E.ParsesUnary toks e₁ toks₁ → Σ[ l′ ∈ S.Expr ] (Emb e₁ l′ × G.ParsesMulTail l′ (F toks₁) e′ (F rest))
       → G.ParsesMul (F toks) e′ (F rest)
  mul₁ du (l′ , el , st) = mul (unary→ du el) st

  mop₁ : ∀ {op t left toks₁ right toks₂ e′ rest} → MulToken t (opS op) → E.ParsesUnary toks₁ right toks₂
       → Σ[ l″ ∈ S.Expr ] (Emb (RBinOp op left right) l″ × G.ParsesMulTail l″ (F toks₂) e′ (F rest))
       → Σ[ l′ ∈ S.Expr ] (Emb left l′ × G.ParsesMulTail l′ (t ∷ F toks₁) e′ (F rest))
  mop₁ mt du (_ , e-binop el er , st) = _ , el , mul-op mt (unary→ du er) st

  app₁ : ∀ {toks f toks₁ e′ rest} → E.ParsesAtomExpr toks f toks₁ → Σ[ l′ ∈ S.Expr ] (Emb f l′ × G.ParsesAppTail l′ (F toks₁) e′ (F rest))
       → G.ParsesApp (F toks) e′ (F rest)
  app₁ da (f′ , ef , st) = app (atom→ da ef) st

  argStart : ∀ {toks a toks₂ a′} → AppArgOk toks → E.ParsesAtomExpr toks a toks₂ → Emb a a′ → ArgStart (F toks)
  argStart aao-TLParen _ _ = as-paren
  argStart aao-TLambda _ _ = as-lambda
  argStart aao-TInt _ _ = as-int
  argStart aao-TFloat _ _ = as-float
  argStart (aao-word nr) _ _ = as-word (reserved-false→ nr)

  aparg₁ : ∀ {left toks₁ arg toks₂ e′ rest} → AppArgOk toks₁ → E.ParsesAtomExpr toks₁ arg toks₂
         → Σ[ l″ ∈ S.Expr ] (Emb (RApp left arg) l″ × G.ParsesAppTail l″ (F toks₂) e′ (F rest))
         → Σ[ l′ ∈ S.Expr ] (Emb left l′ × G.ParsesAppTail l′ (F toks₁) e′ (F rest))
  aparg₁ ok da (_ , e-app el ea , st) = _ , el , app-arg (argStart ok da ea) (atom→ da ea) st

  paren₁ : ∀ {toks e toks₁ eo rest} → E.ParsesExpr toks e toks₁
         → Σ[ e′ ∈ S.Expr ] (Emb e e′ × G.ParsesParenCont e′ (F toks₁) eo (F rest))
         → G.ParsesAtomExpr (TLParen ∷ F toks) eo (F rest)
  paren₁ de (e′ , ee , sc) = atom-paren (expr→ de ee) sc

  opatom : ∀ {toks e rest e′} → Σ[ s ∈ String ] (e ≡ RVar s × G.ParsesOpChars (F toks) [] s (F rest)) → Emb e e′
         → G.ParsesAtomExpr (TLParen ∷ F toks) e′ (F rest)
  opatom (s , refl , sop) e-var = atom-op sop

  opc : ∀ {t ch acc toks e rest} → OpChar (forget t) ch → Σ[ s ∈ String ] (e ≡ RVar s × G.ParsesOpChars (F toks) (ch ∷ acc) s (F rest))
      → Σ[ s ∈ String ] (e ≡ RVar s × G.ParsesOpChars (F (t ∷ toks)) acc s (F rest))
  opc oc (s , eq , sd) = s , eq , op-char oc sd

expr→ (pe-mk d) em = comp→ d em

comp→ (pc-mk dc dt) em = comp₁ dc (ctail→ dt em)

ctail→ {toks = toks} (pct-done n) em = _ , em , comp-done (notDot→TDot toks n)
ctail→ (pct-dot dc dt) em = ctdot₁ dc (ctail→ dt em)

cmp→ {rest = rest} (pcm-noop da n) em = cmp-none (add→ da em) (notCmp→ rest n)
cmp→ (pcm-lt dl dr) (e-binop el er) = cmp ct-lt (add→ dl el) (add→ dr er)
cmp→ (pcm-le dl dr) (e-binop el er) = cmp ct-le (add→ dl el) (add→ dr er)
cmp→ (pcm-gt dl dr) (e-binop el er) = cmp ct-gt (add→ dl el) (add→ dr er)
cmp→ (pcm-ge dl dr) (e-binop el er) = cmp ct-ge (add→ dl el) (add→ dr er)
cmp→ (pcm-eq dl dr) (e-binop el er) = cmp ct-eq (add→ dl el) (add→ dr er)
cmp→ (pcm-ne dl dr) (e-binop el er) = cmp ct-ne (add→ dl el) (add→ dr er)

add→ (pa-mk dm dt) em = add₁ dm (atail→ dt em)

atail→ {toks = toks} (pat-done n) em = _ , em , add-done (notAdd→ toks n)
atail→ (pat-plus dm dt) em = aop₁ at-plus dm (atail→ dt em)
atail→ (pat-minus dm dt) em = aop₁ at-minus dm (atail→ dt em)

mul→ (pm-mk du dt) em = mul₁ du (mtail→ dt em)

mtail→ {toks = toks} (pmt-done n) em = _ , em , mul-done (notMul→ toks n)
mtail→ (pmt-star du dt) em = mop₁ mt-star du (mtail→ dt em)
mtail→ (pmt-slash du dt) em = mop₁ mt-slash du (mtail→ dt em)
mtail→ (pmt-percent du dt) em = mop₁ mt-pct du (mtail→ dt em)

unary→ (pu-neg du) (e-neg em) = neg (unary→ du em)
unary→ (pu-app da) em = unary (app→ da em)

app→ (papp-mk da dt) em = app₁ da (aptail→ dt em)

aptail→ (papp-done n) em = _ , em , app-done (notAtom→ n)
aptail→ (papp-arg ok da dt) em = aparg₁ ok da (aptail→ dt em)

atom→ pae-unit e-unit = atom-unit
atom→ pae-int e-int = atom-int
atom→ pae-float e-float = atom-float
atom→ (pae-var nr nq) e-var = atom-var (reserved-false→ nr) (notQual→ nq)
atom→ (pae-qual nr) e-qual = atom-qual (reserved-false→ nr)
atom→ (pae-paren de dc) em = paren₁ de (pcont→ dc em)
atom→ (pae-lambda dl) em = atom-lambda (lam→ dl em)
atom→ (pae-let (plet-single dv (plin db))) (e-let ev eb) = atom-let (expr→ dv ev) (expr→ db eb)
atom→ (pae-destruct (pd-mk ds (pdof (pdb dl (prb dr))))) (e-destruct es el er) =
  atom-destruct (expr→ ds es) (expr→ dl el) (expr→ dr er)
atom→ (pae-paren-op dop) em = opatom (op→ dop) em

lam→ (plp-body de) em = lam-body (expr→ de em)
lam→ (plp-arg dl) (e-lam eb) = lam-arg (lam→ dl eb)

pcont→ ppc-close em = _ , em , paren-close
pcont→ (ppc-pair de ppt-close) (e-pair ea eb) = _ , ea , paren-pair (expr→ de eb)
pcont→ (ppc-annot dT) (e-annot _ ee) = _ , ee , paren-annot (annot→ dT)

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

-- A compiler derivation over `toks` of a tree that embeds as `e′`.
BackE : (List P.Token → RawExpr → List P.Token → Set) → List P.Token → S.Expr → List Token → Set
BackE Rel toks e′ r = Σ[ e ∈ RawExpr ] Σ[ rest ∈ List P.Token ] (Rel toks e rest × Emb e e′ × F rest ≡ r)

BackET : (RawExpr → List P.Token → RawExpr → List P.Token → Set) → RawExpr → List P.Token → S.Expr → List Token → Set
BackET Rel l toks e′ r = Σ[ e ∈ RawExpr ] Σ[ rest ∈ List P.Token ] (Rel l toks e rest × Emb e e′ × F rest ≡ r)

expr←   : ∀ {ts e′ r} → G.ParsesExpr ts e′ r → ∀ toks → F toks ≡ ts → N r → BackE E.ParsesExpr toks e′ r
ctail←  : ∀ {l′ ts e′ r} → G.ParsesCompTail l′ ts e′ r → ∀ l toks → Emb l l′ → F toks ≡ ts → N r → BackET E.ParsesCompTail l toks e′ r
cmp←    : ∀ {ts e′ r} → G.ParsesCmp ts e′ r → ∀ toks → F toks ≡ ts → N r → BackE E.ParsesCmp toks e′ r
add←    : ∀ {ts e′ r} → G.ParsesAdd ts e′ r → ∀ toks → F toks ≡ ts → N r → BackE E.ParsesAdd toks e′ r
atail←  : ∀ {l′ ts e′ r} → G.ParsesAddTail l′ ts e′ r → ∀ l toks → Emb l l′ → F toks ≡ ts → N r → BackET E.ParsesAddTail l toks e′ r
mul←    : ∀ {ts e′ r} → G.ParsesMul ts e′ r → ∀ toks → F toks ≡ ts → N r → BackE E.ParsesMul toks e′ r
mtail←  : ∀ {l′ ts e′ r} → G.ParsesMulTail l′ ts e′ r → ∀ l toks → Emb l l′ → F toks ≡ ts → N r → BackET E.ParsesMulTail l toks e′ r
unary←  : ∀ {ts e′ r} → G.ParsesUnary ts e′ r → ∀ toks → F toks ≡ ts → N r → BackE E.ParsesUnary toks e′ r
app←    : ∀ {ts e′ r} → G.ParsesApp ts e′ r → ∀ toks → F toks ≡ ts → N r → BackE E.ParsesApp toks e′ r
aptail← : ∀ {l′ ts e′ r} → G.ParsesAppTail l′ ts e′ r → ∀ l toks → Emb l l′ → F toks ≡ ts → N r → BackET E.ParsesAppTail l toks e′ r
atom←   : ∀ {ts e′ r} → G.ParsesAtomExpr ts e′ r → ∀ toks → F toks ≡ ts → N r → BackE E.ParsesAtomExpr toks e′ r
lam←    : ∀ {ts e′ r} → G.ParsesLamParams ts e′ r → ∀ toks → F toks ≡ ts → N r → BackE E.ParsesLamParams toks e′ r
pcont←  : ∀ {e′ ts e″ r} → G.ParsesParenCont e′ ts e″ r → ∀ e toks → Emb e e′ → F toks ≡ ts → BackET E.ParsesParenCont e toks e″ r
op←     : ∀ {ts acc s r} → G.ParsesOpChars ts acc s r → ∀ toks → F toks ≡ ts
        → Σ[ rest ∈ List P.Token ] (ParsesOpExpr acc toks (RVar s) rest × F rest ≡ r)

private
  comp← : ∀ {toks e₁′ ts₁ e′ r} → BackE E.ParsesCmp toks e₁′ ts₁ → G.ParsesCompTail e₁′ ts₁ e′ r → N r
        → BackE E.ParsesExpr toks e′ r
  comp←₂ : ∀ {toks e₁ toks₁ e′ r} → E.ParsesCmp toks e₁ toks₁ → BackET E.ParsesCompTail e₁ toks₁ e′ r
         → BackE E.ParsesExpr toks e′ r
  comp← (e₁ , toks₁ , dc , em , eq) dt n = comp←₂ dc (ctail← dt e₁ toks₁ em eq n)
  comp←₂ dc (e , rest , dt , em , er) = e , rest , pe-mk (pc-mk dc dt) , em , er

  ctdot← : ∀ {l l′ toks₁ e₂′ ts₂ e′ r} → Emb l l′ → BackE E.ParsesCmp toks₁ e₂′ ts₂
         → G.ParsesCompTail (S.RApp (S.RApp (S.RVar "compose") l′) e₂′) ts₂ e′ r → N r
         → BackET E.ParsesCompTail l (P.TDot ∷ toks₁) e′ r
  ctdot←₂ : ∀ {l toks₁ e₂ toks₂ e′ r} → E.ParsesCmp toks₁ e₂ toks₂
          → BackET E.ParsesCompTail (RApp (RApp (RVar "compose") l) e₂) toks₂ e′ r
          → BackET E.ParsesCompTail l (P.TDot ∷ toks₁) e′ r
  ctdot← {l = l} el (e₂ , toks₂ , dc , ee₂ , eq) dt n =
    ctdot←₂ dc (ctail← dt (RApp (RApp (RVar "compose") l) e₂) toks₂ (e-app (e-app e-var el) ee₂) eq n)
  ctdot←₂ dc (e , rest , dt , em , er) = e , rest , pct-dot dc dt , em , er

  cmpn← : ∀ {toks e′ r} → BackE E.ParsesAdd toks e′ r → (∀ {t op} → Starts r t → ¬ CompareToken t op)
        → BackE E.ParsesCmp toks e′ r
  cmpn← (e , rest , da , em , refl) nc = e , rest , pcm-noop da (notCmp← rest nc) , em , refl

  -- `l op e`, for the compiler's operator `oop` written `u`
  cmp-fin  : ∀ {toks l′ ts₁ e′ r} (u : Token) (oop : O.BinOp)
           → (∀ {a b c x y} → E.ParsesAdd a x (back u ∷ b) → E.ParsesAdd b y c → E.ParsesCmp a (RBinOp oop x y) c)
           → isLit u ≡ false
           → BackE E.ParsesAdd toks l′ (u ∷ ts₁) → G.ParsesAdd ts₁ e′ r → N r
           → BackE E.ParsesCmp toks (S.RBinOp (opS oop) l′ e′) r
  cmp-fin₁ : ∀ {toks l l′ rest₁ ts₁ e′ r} {tok : P.Token} (oop : O.BinOp)
           → (∀ {a b c x y} → E.ParsesAdd a x (tok ∷ b) → E.ParsesAdd b y c → E.ParsesCmp a (RBinOp oop x y) c)
           → E.ParsesAdd toks l rest₁ → Emb l l′
           → Σ[ toks₁ ∈ List P.Token ] (rest₁ ≡ tok ∷ toks₁ × F toks₁ ≡ ts₁)
           → G.ParsesAdd ts₁ e′ r → N r → BackE E.ParsesCmp toks (S.RBinOp (opS oop) l′ e′) r
  cmp-fin₂ : ∀ {toks l l′ toks₁ e′ r} {tok : P.Token} (oop : O.BinOp)
           → (∀ {a b c x y} → E.ParsesAdd a x (tok ∷ b) → E.ParsesAdd b y c → E.ParsesCmp a (RBinOp oop x y) c)
           → E.ParsesAdd toks l (tok ∷ toks₁) → Emb l l′ → BackE E.ParsesAdd toks₁ e′ r
           → BackE E.ParsesCmp toks (S.RBinOp (opS oop) l′ e′) r
  cmp-fin u oop mk nl (l , rest₁ , dl , el , e₁) dr n = cmp-fin₁ oop mk dl el (peel nl e₁) dr n
  cmp-fin₁ oop mk dl el (toks₁ , refl , e₂) dr n = cmp-fin₂ oop mk dl el (add← dr toks₁ e₂ n)
  cmp-fin₂ oop mk dl el (r , rest , dr , er , e₃) = RBinOp oop _ r , rest , mk dl dr , e-binop el er , e₃

  add←₁ : ∀ {toks e₁′ ts₁ e′ r} → BackE E.ParsesMul toks e₁′ ts₁ → G.ParsesAddTail e₁′ ts₁ e′ r → N r
        → BackE E.ParsesAdd toks e′ r
  add←₂ : ∀ {toks e₁ toks₁ e′ r} → E.ParsesMul toks e₁ toks₁ → BackET E.ParsesAddTail e₁ toks₁ e′ r
        → BackE E.ParsesAdd toks e′ r
  add←₁ (e₁ , toks₁ , dm , em , eq) dt n = add←₂ dm (atail← dt e₁ toks₁ em eq n)
  add←₂ dm (e , rest , dt , em , er) = e , rest , pa-mk dm dt , em , er

  aop← : ∀ {l l′ toks₁ e₂′ ts₂ e′ r} (tok : P.Token) (oop : O.BinOp)
       → (∀ {lft t1 t2 rt e rst} → E.ParsesMul t1 rt t2 → E.ParsesAddTail (RBinOp oop lft rt) t2 e rst
          → E.ParsesAddTail lft (tok ∷ t1) e rst)
       → Emb l l′ → BackE E.ParsesMul toks₁ e₂′ ts₂ → G.ParsesAddTail (S.RBinOp (opS oop) l′ e₂′) ts₂ e′ r → N r
       → BackET E.ParsesAddTail l (tok ∷ toks₁) e′ r
  aop←₂ : ∀ {l toks₁ e₂ toks₂ e′ r} {tok : P.Token} {oop : O.BinOp}
        → (∀ {lft t1 t2 rt e rst} → E.ParsesMul t1 rt t2 → E.ParsesAddTail (RBinOp oop lft rt) t2 e rst
           → E.ParsesAddTail lft (tok ∷ t1) e rst)
        → E.ParsesMul toks₁ e₂ toks₂ → BackET E.ParsesAddTail (RBinOp oop l e₂) toks₂ e′ r
        → BackET E.ParsesAddTail l (tok ∷ toks₁) e′ r
  aop← {l = l} tok oop mk el (e₂ , toks₂ , dm , ee₂ , eq) dt n = aop←₂ mk dm (atail← dt (RBinOp oop l e₂) toks₂ (e-binop el ee₂) eq n)
  aop←₂ mk dm (e , rest , dt , em , er) = e , rest , mk dm dt , em , er

  mul←₁ : ∀ {toks e₁′ ts₁ e′ r} → BackE E.ParsesUnary toks e₁′ ts₁ → G.ParsesMulTail e₁′ ts₁ e′ r → N r
        → BackE E.ParsesMul toks e′ r
  mul←₂ : ∀ {toks e₁ toks₁ e′ r} → E.ParsesUnary toks e₁ toks₁ → BackET E.ParsesMulTail e₁ toks₁ e′ r
        → BackE E.ParsesMul toks e′ r
  mul←₁ (e₁ , toks₁ , du , em , eq) dt n = mul←₂ du (mtail← dt e₁ toks₁ em eq n)
  mul←₂ du (e , rest , dt , em , er) = e , rest , pm-mk du dt , em , er

  mop← : ∀ {l l′ toks₁ e₂′ ts₂ e′ r} (tok : P.Token) (oop : O.BinOp)
       → (∀ {lft t1 t2 rt e rst} → E.ParsesUnary t1 rt t2 → E.ParsesMulTail (RBinOp oop lft rt) t2 e rst
          → E.ParsesMulTail lft (tok ∷ t1) e rst)
       → Emb l l′ → BackE E.ParsesUnary toks₁ e₂′ ts₂ → G.ParsesMulTail (S.RBinOp (opS oop) l′ e₂′) ts₂ e′ r → N r
       → BackET E.ParsesMulTail l (tok ∷ toks₁) e′ r
  mop←₂ : ∀ {l toks₁ e₂ toks₂ e′ r} {tok : P.Token} {oop : O.BinOp}
        → (∀ {lft t1 t2 rt e rst} → E.ParsesUnary t1 rt t2 → E.ParsesMulTail (RBinOp oop lft rt) t2 e rst
           → E.ParsesMulTail lft (tok ∷ t1) e rst)
        → E.ParsesUnary toks₁ e₂ toks₂ → BackET E.ParsesMulTail (RBinOp oop l e₂) toks₂ e′ r
        → BackET E.ParsesMulTail l (tok ∷ toks₁) e′ r
  mop← {l = l} tok oop mk el (e₂ , toks₂ , du , ee₂ , eq) dt n = mop←₂ mk du (mtail← dt (RBinOp oop l e₂) toks₂ (e-binop el ee₂) eq n)
  mop←₂ mk du (e , rest , dt , em , er) = e , rest , mk du dt , em , er

  neg←₁ : ∀ {toks e′ r} → BackE E.ParsesUnary toks e′ r → BackE E.ParsesUnary (P.TMinus ∷ toks) (S.RNeg e′) r
  neg←₁ (e , rest , du , em , er) = RUnaryOp OpNeg e , rest , pu-neg du , e-neg em , er

  un←₁ : ∀ {toks e′ r} → BackE E.ParsesApp toks e′ r → BackE E.ParsesUnary toks e′ r
  un←₁ (e , rest , da , em , er) = e , rest , pu-app da , em , er

  app←₁ : ∀ {toks f′ ts₁ e′ r} → BackE E.ParsesAtomExpr toks f′ ts₁ → G.ParsesAppTail f′ ts₁ e′ r → N r
        → BackE E.ParsesApp toks e′ r
  app←₂ : ∀ {toks f toks₁ e′ r} → E.ParsesAtomExpr toks f toks₁ → BackET E.ParsesAppTail f toks₁ e′ r
        → BackE E.ParsesApp toks e′ r
  app←₁ (f , toks₁ , da , ef , eq) dt n = app←₂ da (aptail← dt f toks₁ ef eq n)
  app←₂ da (e , rest , dt , em , er) = e , rest , papp-mk da dt , em , er

  aparg← : ∀ {l l′ toks a′ ts₂ e′ r} → AppArgOk toks → Emb l l′ → BackE E.ParsesAtomExpr toks a′ ts₂
         → G.ParsesAppTail (S.RApp l′ a′) ts₂ e′ r → N r → BackET E.ParsesAppTail l toks e′ r
  aparg←₂ : ∀ {l toks a toks₂ e′ r} → AppArgOk toks → E.ParsesAtomExpr toks a toks₂
          → BackET E.ParsesAppTail (RApp l a) toks₂ e′ r → BackET E.ParsesAppTail l toks e′ r
  aparg← {l = l} ok el (a , toks₂ , da , ea , eq) dt n = aparg←₂ ok da (aptail← dt (RApp l a) toks₂ (e-app el ea) eq n)
  aparg←₂ ok da (e , rest , dt , em , er) = e , rest , papp-arg ok da dt , em , er

  paren← : ∀ {toks e′ ts₁ e″ r} → BackE E.ParsesExpr toks e′ ts₁ → G.ParsesParenCont e′ ts₁ e″ r
         → BackE E.ParsesAtomExpr (P.TLParen ∷ toks) e″ r
  paren←₂ : ∀ {toks e toks₁ e″ r} → E.ParsesExpr toks e toks₁ → BackET E.ParsesParenCont e toks₁ e″ r
          → BackE E.ParsesAtomExpr (P.TLParen ∷ toks) e″ r
  paren← (e , toks₁ , de , ee , eq) dc = paren←₂ de (pcont← dc e toks₁ ee eq)
  paren←₂ de (eo , rest , dc , em , er) = eo , rest , pae-paren de dc , em , er

  op←₁ : ∀ {toks s r} → Σ[ rest ∈ List P.Token ] (ParsesOpExpr [] toks (RVar s) rest × F rest ≡ r)
       → BackE E.ParsesAtomExpr (P.TLParen ∷ toks) (S.RVar s) r
  op←₁ (rest , d , er) = _ , rest , pae-paren-op d , e-var , er

  lam←₁ : ∀ {toks e′ r} → BackE E.ParsesLamParams toks e′ r → BackE E.ParsesAtomExpr (P.TLambda ∷ toks) e′ r
  lam←₁ (e , rest , dl , em , er) = e , rest , pae-lambda dl , em , er

  let←₁ : ∀ {x toks v′ ts₁ b′ r} → BackE E.ParsesExpr toks v′ (TWord "in" ∷ ts₁) → G.ParsesExpr ts₁ b′ r → N r
        → BackE E.ParsesAtomExpr (P.TWord "let" ∷ P.TWord x ∷ P.TEquals ∷ toks) (S.RLet x v′ b′) r
  let←₂ : ∀ {x toks v v′ rest₁ ts₁ b′ r} → E.ParsesExpr toks v rest₁ → Emb v v′
        → Σ[ toks₁ ∈ List P.Token ] (rest₁ ≡ P.TWord "in" ∷ toks₁ × F toks₁ ≡ ts₁) → G.ParsesExpr ts₁ b′ r → N r
        → BackE E.ParsesAtomExpr (P.TWord "let" ∷ P.TWord x ∷ P.TEquals ∷ toks) (S.RLet x v′ b′) r
  let←₃ : ∀ {x toks v v′ toks₁ b′ r} → E.ParsesExpr toks v (P.TWord "in" ∷ toks₁) → Emb v v′ → BackE E.ParsesExpr toks₁ b′ r
        → BackE E.ParsesAtomExpr (P.TWord "let" ∷ P.TWord x ∷ P.TEquals ∷ toks) (S.RLet x v′ b′) r
  let←₁ (v , rest₁ , dv , ev , e₁) db n = let←₂ dv ev (peel refl e₁) db n
  let←₂ dv ev (toks₁ , refl , e₂) db n = let←₃ dv ev (expr← db toks₁ e₂ n)
  let←₃ dv ev (b , rest , db , eb , er) = _ , rest , pae-let (plet-single dv (plin db)) , e-let ev eb , er

  de←₁ : ∀ {toks s′ x ts₁ l′ y ts₂ r′ r}
       → BackE E.ParsesExpr toks s′ (TWord "of" ∷ TLBrace ∷ TWord "Left" ∷ TWord x ∷ TArrow ∷ ts₁)
       → G.ParsesExpr ts₁ l′ (TSemicolon ∷ TWord "Right" ∷ TWord y ∷ TArrow ∷ ts₂) → G.ParsesExpr ts₂ r′ (TRBrace ∷ r)
       → BackE E.ParsesAtomExpr (P.TWord "destruct" ∷ toks) (S.RDestruct s′ x l′ y r′) r
  de←₂ : ∀ {toks s s′ rest₁ x ts₁ l′ y ts₂ r′ r} → E.ParsesExpr toks s rest₁ → Emb s s′
       → Σ[ toks₁ ∈ List P.Token ] (rest₁ ≡ P.TWord "of" ∷ P.TLBrace ∷ P.TWord "Left" ∷ P.TWord x ∷ P.TArrow ∷ toks₁ × F toks₁ ≡ ts₁)
       → G.ParsesExpr ts₁ l′ (TSemicolon ∷ TWord "Right" ∷ TWord y ∷ TArrow ∷ ts₂) → G.ParsesExpr ts₂ r′ (TRBrace ∷ r)
       → BackE E.ParsesAtomExpr (P.TWord "destruct" ∷ toks) (S.RDestruct s′ x l′ y r′) r
  de←₃ : ∀ {toks s s′ x toks₁ l l′ rest₂ y ts₂ r′ r}
       → E.ParsesExpr toks s (P.TWord "of" ∷ P.TLBrace ∷ P.TWord "Left" ∷ P.TWord x ∷ P.TArrow ∷ toks₁) → Emb s s′
       → E.ParsesExpr toks₁ l rest₂ → Emb l l′
       → Σ[ toks₂ ∈ List P.Token ] (rest₂ ≡ P.TSemicolon ∷ P.TWord "Right" ∷ P.TWord y ∷ P.TArrow ∷ toks₂ × F toks₂ ≡ ts₂)
       → G.ParsesExpr ts₂ r′ (TRBrace ∷ r)
       → BackE E.ParsesAtomExpr (P.TWord "destruct" ∷ toks) (S.RDestruct s′ x l′ y r′) r
  de←₄ : ∀ {toks s s′ x toks₁ l l′ y toks₂ rv r′ rest₃ r}
       → E.ParsesExpr toks s (P.TWord "of" ∷ P.TLBrace ∷ P.TWord "Left" ∷ P.TWord x ∷ P.TArrow ∷ toks₁) → Emb s s′
       → E.ParsesExpr toks₁ l (P.TSemicolon ∷ P.TWord "Right" ∷ P.TWord y ∷ P.TArrow ∷ toks₂) → Emb l l′
       → E.ParsesExpr toks₂ rv rest₃ → Emb rv r′
       → Σ[ rest ∈ List P.Token ] (rest₃ ≡ P.TRBrace ∷ rest × F rest ≡ r)
       → BackE E.ParsesAtomExpr (P.TWord "destruct" ∷ toks) (S.RDestruct s′ x l′ y r′) r
  de←₂b : ∀ {toks s s′ x toks₁ l′ y ts₂ r′ r}
        → E.ParsesExpr toks s (P.TWord "of" ∷ P.TLBrace ∷ P.TWord "Left" ∷ P.TWord x ∷ P.TArrow ∷ toks₁) → Emb s s′
        → BackE E.ParsesExpr toks₁ l′ (TSemicolon ∷ TWord "Right" ∷ TWord y ∷ TArrow ∷ ts₂) → G.ParsesExpr ts₂ r′ (TRBrace ∷ r)
        → BackE E.ParsesAtomExpr (P.TWord "destruct" ∷ toks) (S.RDestruct s′ x l′ y r′) r
  de←₃b : ∀ {toks s s′ x toks₁ l l′ y toks₂ r′ r}
        → E.ParsesExpr toks s (P.TWord "of" ∷ P.TLBrace ∷ P.TWord "Left" ∷ P.TWord x ∷ P.TArrow ∷ toks₁) → Emb s s′
        → E.ParsesExpr toks₁ l (P.TSemicolon ∷ P.TWord "Right" ∷ P.TWord y ∷ P.TArrow ∷ toks₂) → Emb l l′
        → BackE E.ParsesExpr toks₂ r′ (TRBrace ∷ r)
        → BackE E.ParsesAtomExpr (P.TWord "destruct" ∷ toks) (S.RDestruct s′ x l′ y r′) r
  de←₁ (s , rest₁ , ds , es , e₁) dl dr =
    de←₂ ds es (peels (TWord "of" ∷ TLBrace ∷ TWord "Left" ∷ TWord _ ∷ TArrow ∷ []) (refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ []) e₁) dl dr
  de←₂ ds es (toks₁ , refl , e₂) dl dr = de←₂b ds es (expr← dl toks₁ e₂ (λ ())) dr
  de←₂b ds es (l , rest₂ , dl , el , e₃) dr =
    de←₃ ds es dl el (peels (TSemicolon ∷ TWord "Right" ∷ TWord _ ∷ TArrow ∷ []) (refl ∷ refl ∷ refl ∷ refl ∷ []) e₃) dr
  de←₃ ds es dl el (toks₂ , refl , e₄) dr = de←₃b ds es dl el (expr← dr toks₂ e₄ (λ ()))
  de←₃b ds es dl el (rv , rest₃ , dr , er , e₅) = de←₄ ds es dl el dr er (peel refl e₅)
  de←₄ ds es dl el dr er (rest , refl , e₆) =
    _ , rest , pae-destruct (pd-mk ds (pdof (pdb dl (prb dr)))) , e-destruct es el er , e₆

  lamb←₁ : ∀ {toks e′ r} → BackE E.ParsesExpr toks e′ r → BackE E.ParsesLamParams (P.TArrow ∷ toks) e′ r
  lamb←₁ (e , rest , de , em , er) = e , rest , plp-body de , em , er

  lama←₁ : ∀ {x toks e′ r} → BackE E.ParsesLamParams toks e′ r → BackE E.ParsesLamParams (P.TWord x ∷ toks) (S.RLam x e′) r
  lama←₁ (e , rest , dl , em , er) = RLam _ e , rest , plp-arg dl , e-lam em , er

  pair←₁ : ∀ {e e′ toks b′ r} → Emb e e′ → BackE E.ParsesExpr toks b′ (TRParen ∷ r)
         → BackET E.ParsesParenCont e (P.TComma ∷ toks) (S.RPair e′ b′) r
  pair←₂ : ∀ {e e′ toks b b′ rest₁ r} → Emb e e′ → E.ParsesExpr toks b rest₁ → Emb b b′
         → Σ[ rest ∈ List P.Token ] (rest₁ ≡ P.TRParen ∷ rest × F rest ≡ r)
         → BackET E.ParsesParenCont e (P.TComma ∷ toks) (S.RPair e′ b′) r
  pair←₁ em (b , rest₁ , db , eb , e₁) = pair←₂ em db eb (peel refl e₁)
  pair←₂ em db eb (rest , refl , e₂) = _ , rest , ppc-pair db ppt-close , e-pair em eb , e₂

  annot←₁ : ∀ {e e′ toks A′ r} → Emb e e′
          → Σ[ T ∈ _ ] Σ[ rest₁ ∈ List P.Token ] (Once.Parser.TypeRelation.ParsesType toks T rest₁ × toTy T ≡ A′ × F rest₁ ≡ TRParen ∷ r)
          → BackET E.ParsesParenCont e (P.TColon ∷ toks) (S.RAnnot e′ A′) r
  annot←₂ : ∀ {e e′ toks T rest₁ r} → Emb e e′ → Once.Parser.TypeRelation.ParsesType toks T rest₁
          → Σ[ rest ∈ List P.Token ] (rest₁ ≡ P.TRParen ∷ rest × F rest ≡ r)
          → BackET E.ParsesParenCont e (P.TColon ∷ toks) (S.RAnnot e′ (toTy T)) r
  annot←₁ em (T , rest₁ , dT , refl , e₁) = annot←₂ em dT (peel refl e₁)
  annot←₂ em dT (rest , refl , e₂) = _ , rest , ppc-annot dT , e-annot (type-rf dT) em , e₂

  opc← : ∀ {toks acc ch s r} (t : P.Token)
       → (∀ {acc toks e rest} → ParsesOpExpr (ch ∷ acc) toks e rest → ParsesOpExpr acc (t ∷ toks) e rest)
       → Σ[ rest ∈ List P.Token ] (ParsesOpExpr (ch ∷ acc) toks (RVar s) rest × F rest ≡ r)
       → Σ[ rest ∈ List P.Token ] (ParsesOpExpr acc (t ∷ toks) (RVar s) rest × F rest ≡ r)
  opc← t mk (rest , d , er) = rest , mk d , er

expr← (expr dc dt) toks e n = comp← (cmp← dc toks e (ctail-ns dt n)) dt n

ctail← (comp-done x) l toks em refl n = l , toks , pct-done (notDot← toks x) , em , refl
ctail← (comp-dot dc dt) l toks em e n =
  step (λ z → BackET E.ParsesCompTail l z _ _) refl e (λ {toks′} e′ → ctdot← em (cmp← dc toks′ e′ (ctail-ns dt n)) dt n)

cmp← (cmp-none da nc) toks e n = cmpn← (add← da toks e n) nc
cmp← (cmp ct-lt dl dr) toks e n = cmp-fin TLt OpLt pcm-lt refl (add← dl toks e (ct-ns ct-lt)) dr n
cmp← (cmp ct-le dl dr) toks e n = cmp-fin TLe OpLe pcm-le refl (add← dl toks e (ct-ns ct-le)) dr n
cmp← (cmp ct-gt dl dr) toks e n = cmp-fin TGt OpGt pcm-gt refl (add← dl toks e (ct-ns ct-gt)) dr n
cmp← (cmp ct-ge dl dr) toks e n = cmp-fin TGe OpGe pcm-ge refl (add← dl toks e (ct-ns ct-ge)) dr n
cmp← (cmp ct-eq dl dr) toks e n = cmp-fin TEqEq OpEq pcm-eq refl (add← dl toks e (ct-ns ct-eq)) dr n
cmp← (cmp ct-ne dl dr) toks e n = cmp-fin TNeq OpNe pcm-ne refl (add← dl toks e (ct-ns ct-ne)) dr n

add← (add dm dt) toks e n = add←₁ (mul← dm toks e (atail-ns dt n)) dt n

atail← (add-done x) l toks em refl n = l , toks , pat-done (notAdd← toks x) , em , refl
atail← (add-op at-plus dm dt) l toks em e n =
  step (λ z → BackET E.ParsesAddTail l z _ _) refl e (λ {toks′} e′ →
    aop← P.TPlus OpAdd pat-plus em (mul← dm toks′ e′ (atail-ns dt n)) dt n)
atail← (add-op at-minus dm dt) l toks em e n =
  step (λ z → BackET E.ParsesAddTail l z _ _) refl e (λ {toks′} e′ →
    aop← P.TMinus OpSub pat-minus em (mul← dm toks′ e′ (atail-ns dt n)) dt n)

mul← (mul du dt) toks e n = mul←₁ (unary← du toks e (mtail-ns dt n)) dt n

mtail← (mul-done x) l toks em refl n = l , toks , pmt-done (notMul← toks x) , em , refl
mtail← (mul-op mt-star du dt) l toks em e n =
  step (λ z → BackET E.ParsesMulTail l z _ _) refl e (λ {toks′} e′ →
    mop← P.TStar OpMul pmt-star em (unary← du toks′ e′ (mtail-ns dt n)) dt n)
mtail← (mul-op mt-slash du dt) l toks em e n =
  step (λ z → BackET E.ParsesMulTail l z _ _) refl e (λ {toks′} e′ →
    mop← P.TSlash OpDiv pmt-slash em (unary← du toks′ e′ (mtail-ns dt n)) dt n)
mtail← (mul-op mt-pct du dt) l toks em e n =
  step (λ z → BackET E.ParsesMulTail l z _ _) refl e (λ {toks′} e′ →
    mop← P.TPercent OpMod pmt-percent em (unary← du toks′ e′ (mtail-ns dt n)) dt n)

unary← (neg du) toks e n = step (λ z → BackE E.ParsesUnary z _ _) refl e (λ {toks′} e′ → neg←₁ (unary← du toks′ e′ n))
unary← (unary da) toks e n = un←₁ (app← da toks e n)

app← (app da dt) toks e n = app←₁ (atom← da toks e (aptail-ns dt n)) dt n

aptail← (app-done x) l toks em refl n = l , toks , papp-done (notAtom← toks x n) , em , refl
aptail← (app-arg as da dt) l toks em e n =
  aparg← (argOk← toks (subst ArgStart (sym e) as)) em (atom← da toks e (aptail-ns dt n)) dt n

atom← atom-unit toks e n =
  step (λ z → BackE E.ParsesAtomExpr z _ _) refl e (λ e₁ →
  step (λ z → BackE E.ParsesAtomExpr (P.TLParen ∷ z) _ _) refl e₁ (λ {toks′} e₂ →
  RUnit , toks′ , pae-unit , e-unit , e₂))
atom← atom-int toks e n = stepInt (λ z → BackE E.ParsesAtomExpr z _ _) e (λ p {toks′} e′ → _ , toks′ , pae-int , e-int , e′)
atom← atom-float toks e n = stepFloat (λ z → BackE E.ParsesAtomExpr z _ _) e (λ p {toks′} e′ → _ , toks′ , pae-float , e-float , e′)
atom← (atom-var nr nq) toks e n =
  step (λ z → BackE E.ParsesAtomExpr z _ _) refl e (λ {toks′} e′ →
  _ , toks′ , pae-var (reserved-false nr) (notQual← toks′ (subst (λ z → ¬ QualSuffix z) (sym e′) nq)) , e-var , e′)
atom← (atom-qual nr) toks e n =
  step (λ z → BackE E.ParsesAtomExpr z _ _) refl e (λ e₁ →
  step (λ z → BackE E.ParsesAtomExpr (P.TWord _ ∷ z) _ _) refl e₁ (λ e₂ →
  step (λ z → BackE E.ParsesAtomExpr (P.TWord _ ∷ P.TAt ∷ z) _ _) refl e₂ (λ {toks′} e₃ →
  _ , toks′ , pae-qual (reserved-false nr) , e-qual , e₃)))
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

pcont← paren-close e toks em eq = step (λ z → BackET E.ParsesParenCont e z _ _) refl eq (λ {toks′} e′ → e , toks′ , ppc-close , em , e′)
pcont← (paren-pair de) e toks em eq =
  step (λ z → BackET E.ParsesParenCont e z _ _) refl eq (λ {toks′} e′ → pair←₁ em (expr← de toks′ e′ (λ ())))
pcont← (paren-annot dT) e toks em eq =
  step (λ z → BackET E.ParsesParenCont e z _ _) refl eq (λ {toks′} e′ → annot←₁ em (annot← dT toks′ e′))

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
