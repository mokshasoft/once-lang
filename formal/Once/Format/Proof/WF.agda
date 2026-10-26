-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Format.Proof.WF — a parsed module is well formed (plan 0.124 step
-- 4.1).
--
-- What the grammar reads from lexed tokens (`LexOK`) is what the printer's
-- proofs ask for: names that are words or operators, words that are
-- identifiers, non-negative integers, floats whose fraction fits its digits,
-- type variables in signatures only, ground annotations whose effectful
-- arrows are as read. By induction on the derivations, each reading the
-- tokens it consumes and handing on the rest.
------------------------------------------------------------------------

module Once.Format.Proof.WF where

open import Data.Bool using (Bool; true; false)
open import Data.Char using (Char)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; _++_; reverse; reverseAcc; [_])
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃-syntax)
open import Data.String using (String; toList; fromList)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Relation.Nullary using (¬_)

open import Once.Postulates using (toList∘fromList)
open import Once.Spec.Grade using (Many; pureᶠ; actᶠ; fin; eff; mk-kind)
open import Once.Spec.Type using (Type; Fun)
open import Once.Spec.Surface.Lexing using (Token; TWord; TInt; TFloat; TLParen; TRParen; TAt; TNewline; TEOF)
open import Once.Spec.Surface.Syntax
open import Once.Spec.Surface.Grammar
open import Once.Format.Print using (isOperator)
open import Once.Format.Proof.Lexing using (Printable; p-word; p-int; p-float; p-sym)
open import Once.Format.Proof.LexOK using (DigitBound; LexOK; Other; o-nl; o-eof; o-str; lexed-ok)
open import Once.Format.Proof.ExprBase using (WF; NameOK; OpName; op-isOperator)
open import Once.Format.Proof.TypeAlgs using (GroundOK; GroundOKF; written; ground)
import Once.Format.Proof.TypeAlgs as TA
open import Once.Format.Proof.Printable using (PE; PT; PF; PD; Pw; kw)
open import Once.Format.Proof.Decl using (WFD; DeclName)

AL : List Token → Set
AL = All LexOK

private
  word : ∀ {x} → LexOK (TWord x) → Pw x
  word (inj₁ p) = p
  word (inj₂ ())

  int : ∀ {z} → LexOK (TInt z) → PE (RInt z)
  int (inj₁ (p-int {n})) = n , refl
  int (inj₁ (p-sym ()))
  int (inj₂ ())

  float : ∀ {i f l} → LexOK (TFloat i f l) → PE (RFloat i f l)
  float (inj₁ (p-float {l = l} f<)) = l , refl , f<
  float (inj₁ (p-sym ()))
  float (inj₂ ())

  tl : ∀ {t ts} → AL (t ∷ ts) → AL ts
  tl (_ ∷ a) = a

-- What the grammar asks of an expression (a record: its index is matched).
record Good (e : Expr) : Set where
  constructor good
  field
    wf : WF e
    pe : PE e

private

  wordName : ∀ {x} → ¬ Reserved x → LexOK (TWord x) → Good (RVar x)
  wordName ¬r l with word l
  ... | p@(p-word {c = c} {i} eq ¬s ¬d st ps) = good (inj₂ (¬r , c , i , eq , st)) (λ _ → p)

  composeName : Good (RVar "compose")
  composeName = good (inj₂ ((λ ()) , 'c' , toList "ompose" , refl , refl)) (λ _ → kw "compose" refl)

  allRev : ∀ {A : Set} {P : A → Set} {acc xs} → All P acc → All P xs → All P (reverseAcc acc xs)
  allRev pa []       = pa
  allRev pa (p ∷ ps) = allRev (p ∷ pa) ps

  revCons : ∀ {A : Set} (c : A) cs → ∃[ d ] ∃[ ds ] reverse (c ∷ cs) ≡ d ∷ ds
  revCons c cs = go [ c ] cs (c , [] , refl)
    where
      go : ∀ acc xs → ∃[ a ] ∃[ as ] acc ≡ a ∷ as → ∃[ d ] ∃[ ds ] reverseAcc acc xs ≡ d ∷ ds
      go acc []       (a , as , eq) = a , as , eq
      go acc (x ∷ xs) _             = go (x ∷ acc) xs (x , acc , refl)

  OC : Char → Set
  OC d = ∃[ t ] OpChar t d

  -- An operator name, up to `)`.
  opName : ∀ {ts cs s r} → ParsesOpChars ts cs s r → All OC cs → AL ts → OpName s × AL r
  opName (op-close {c} {cs}) os a with revCons c cs
  ... | d , ds , eq =
    (d , ds , trans (toList∘fromList (reverse (c ∷ cs))) eq , subst (All OC) eq (allRev [] os)) , tl a
  opName (op-char {t} oc p) os a = opName p ((t , oc) ∷ os) (tl a)

  opGood : ∀ {ts s r} → ParsesOpChars ts [] s r → AL ts → Good (RVar s) × AL r
  opGood {s = s} p a with opName p [] a
  ... | on , a′ = good (inj₁ on) (λ e → ⊥-elim (t≢f (trans (sym (op-isOperator s on)) e))) , a′
    where
      t≢f : true ≡ false → ⊥
      t≢f ()

------------------------------------------------------------------------
-- Types
------------------------------------------------------------------------

-- | What a reading of types keeps.
record Closed {R RF : Set} (alg : TypeAlg R RF) (Q : R → Set) (QF : RF → Set) : Set where
  open TypeAlg alg
  field
    qUnit : Q aUnit
    qVoid : Q aVoid
    qInt  : Q aInt
    qFloat : Q aFloat
    qProd : ∀ {A B} → Q A → Q B → Q (aProd A B)
    qSum  : ∀ {A B} → Q A → Q B → Q (aSum A B)
    qEff  : ∀ {A B} → Q A → Q B → Q (aEff A B)
    qAct  : ∀ {A B} → Q A → Q B → Q (aAct A B)
    qArrow : ∀ {q A B} → Q A → Q B → Q (aArrow q A B)
    qMu   : ∀ {F} → QF F → Q (aMu F)
    qNu   : ∀ {φ F} → QF F → Q (aNu φ F)
    qK    : ∀ {A} → Q A → QF (fK A)
    qId   : QF fId
    qFSum  : ∀ {F G} → QF F → QF G → QF (fSum F G)
    qFProd : ∀ {F G} → QF F → QF G → QF (fProd F G)
    qExtra : ∀ {ts A r} → Extra ts A r → AL ts → Q A × AL r

module ReadTypes {R RF : Set} (alg : TypeAlg R RF) (Q : R → Set) (QF : RF → Set) (cl : Closed alg Q QF) where
  open TypeAlg alg
  open Types alg
  open Closed cl

  mutual
    atom : ∀ {ts A r} → ParsesAtom ts A r → AL ts → Q A × AL r
    atom a-unit a = qUnit , tl a
    atom a-void a = qVoid , tl a
    atom a-int a = qInt , tl a
    atom a-float a = qFloat , tl a
    atom (a-eff p q) a with atom p (tl a)
    ... | qa , a′ with atom q a′
    ...   | qb , a″ = qEff qa qb , a″
    atom (a-act p q) a with atom p (tl a)
    ... | qa , a′ with atom q a′
    ...   | qb , a″ = qAct qa qb , a″
    atom (a-mu f) a with fsumR f (tl a)
    ... | qf , a′ = qMu qf , a′
    atom (a-nu f) a with fsumR f (tl a)
    ... | qf , a′ = qNu qf , a′
    atom (a-nu-act f) a with fsumR f (tl (tl (tl a)))
    ... | qf , a′ = qNu qf , tl a′
    atom (a-extra x) a = qExtra x a
    atom (a-paren p) a with typ p (tl a)
    ... | qa , a′ = qa , tl a′

    prodT : ∀ {l ts T r} → ParsesProdTail l ts T r → Q l → AL ts → Q T × AL r
    prodT (prod-done _) ql a = ql , a
    prodT (prod-star p t) ql a with atom p (tl a)
    ... | qb , a′ = prodT t (qProd ql qb) a′

    prod′ : ∀ {ts T r} → ParsesProd ts T r → AL ts → Q T × AL r
    prod′ (prod p t) a with atom p a
    ... | qa , a′ = prodT t qa a′

    sumT : ∀ {l ts T r} → ParsesSumTail l ts T r → Q l → AL ts → Q T × AL r
    sumT (sum-done _) ql a = ql , a
    sumT (sum-plus p t) ql a with prod′ p (tl a)
    ... | qb , a′ = sumT t (qSum ql qb) a′

    sum′ : ∀ {ts T r} → ParsesSum ts T r → AL ts → Q T × AL r
    sum′ (sum p t) a with prod′ p a
    ... | qa , a′ = sumT t qa a′

    arrowT : ∀ {l ts T r} → ParsesArrowTail l ts T r → Q l → AL ts → Q T × AL r
    arrowT (arrow-done _ _ _ _) ql a = ql , a
    arrowT (arrow-grade _ p) ql a with typ p (tl (tl a))
    ... | qb , a′ = qArrow ql qb , a′
    arrowT (arrow p) ql a with typ p (tl a)
    ... | qb , a′ = qArrow ql qb , a′

    typ : ∀ {ts T r} → ParsesType ts T r → AL ts → Q T × AL r
    typ (Types.type p t) a with sum′ p a
    ... | qa , a′ = arrowT t qa a′

    fatom : ∀ {ts F r} → ParsesFunAtom ts F r → AL ts → QF F × AL r
    fatom f-id a = qId , tl a
    fatom (f-k p) a with atom p (tl a)
    ... | qa , a′ = qK qa , a′
    fatom (f-paren p) a with fsumR p (tl a)
    ... | qf , a′ = qf , tl a′

    fprodT : ∀ {l ts F r} → ParsesFunProdTail l ts F r → QF l → AL ts → QF F × AL r
    fprodT (fprod-done _) ql a = ql , a
    fprodT (fprod-star p t) ql a with fatom p (tl a)
    ... | qb , a′ = fprodT t (qFProd ql qb) a′

    fprod′ : ∀ {ts F r} → ParsesFunProd ts F r → AL ts → QF F × AL r
    fprod′ (fprod p t) a with fatom p a
    ... | qa , a′ = fprodT t qa a′

    fsumT : ∀ {l ts F r} → ParsesFunSumTail l ts F r → QF l → AL ts → QF F × AL r
    fsumT (fsum-done _) ql a = ql , a
    fsumT (fsum-plus p t) ql a with fprod′ p (tl a)
    ... | qb , a′ = fsumT t (qFSum ql qb) a′

    fsumR : ∀ {ts F r} → ParsesFunSum ts F r → AL ts → QF F × AL r
    fsumR (Types.fsum p t) a with fprod′ p a
    ... | qa , a′ = fsumT t qa a′

private
  pair : ∀ {A B C D : Set} → A × B → C × D → (A × C) × (B × D)
  pair (a , b) (c , d) = (a , c) , (b , d)

  sigClosed : Closed (written TypeVar) (λ P → TA.Sig.WF P × PT P) (λ F → TA.Sig.WFF F × PF F)
  sigClosed = record
    { qUnit = tt , tt ; qVoid = tt , tt ; qInt = tt , tt ; qFloat = tt , tt
    ; qProd = pair ; qSum = pair ; qEff = pair ; qAct = pair ; qArrow = pair
    ; qMu = λ p → p ; qNu = λ p → p ; qK = λ p → p ; qId = tt , tt ; qFSum = pair ; qFProd = pair
    ; qExtra = λ { (tvar lw) (l ∷ a) → (lw , word l) , a } }

  aliasClosed : Closed (written NoExtra) (λ P → TA.Alias.WF P × PT P) (λ F → TA.Alias.WFF F × PF F)
  aliasClosed = record
    { qUnit = tt , tt ; qVoid = tt , tt ; qInt = tt , tt ; qFloat = tt , tt
    ; qProd = pair ; qSum = pair ; qEff = pair ; qAct = pair ; qArrow = pair
    ; qMu = λ p → p ; qNu = λ p → p ; qK = λ p → p ; qId = tt , tt ; qFSum = pair ; qFProd = pair
    ; qExtra = λ () }

  groundClosed : Closed ground GroundOK GroundOKF
  groundClosed = record
    { qUnit = tt ; qVoid = tt ; qInt = tt ; qFloat = tt
    ; qProd = _,_ ; qSum = _,_ ; qEff = λ a b → refl , a , b ; qAct = λ a b → refl , a , b ; qArrow = _,_
    ; qMu = λ p → p ; qNu = λ p → p ; qK = λ p → p ; qId = tt ; qFSum = _,_ ; qFProd = _,_
    ; qExtra = λ () }

module SigR    = ReadTypes (written TypeVar) _ _ sigClosed
module AliasR  = ReadTypes (written NoExtra) _ _ aliasClosed
module GroundR = ReadTypes ground _ _ groundClosed

------------------------------------------------------------------------
-- Expressions
------------------------------------------------------------------------

private
  bin : ∀ {op a b} → Good a → Good b → Good (RBinOp op a b)
  bin (good wa pa) (good wb pb) = good (wa , wb) (pa , pb)

  appG : ∀ {f a} → Good f → Good a → Good (RApp f a)
  appG (good wf pf) (good wa pa) = good (wf , wa) (pf , pa)

mutual
  expr′ : ∀ {ts e r} → ParsesExpr ts e r → AL ts → Good e × AL r
  expr′ (expr c t) a with cmp′ c a
  ... | g , a′ = compT t g a′

  compT : ∀ {l ts e r} → ParsesCompTail l ts e r → Good l → AL ts → Good e × AL r
  compT (comp-done _) g a = g , a
  compT (comp-dot c t) g a with cmp′ c (tl a)
  ... | g₂ , a′ = compT t (appG (appG composeName g) g₂) a′

  cmp′ : ∀ {ts e r} → ParsesCmp ts e r → AL ts → Good e × AL r
  cmp′ (cmp-none p _) a = add′ p a
  cmp′ (cmp _ p q) a with add′ p a
  ... | g₁ , a′ with add′ q (tl a′)
  ...   | g₂ , a″ = bin g₁ g₂ , a″

  add′ : ∀ {ts e r} → ParsesAdd ts e r → AL ts → Good e × AL r
  add′ (add p t) a with mul′ p a
  ... | g , a′ = addT t g a′

  addT : ∀ {l ts e r} → ParsesAddTail l ts e r → Good l → AL ts → Good e × AL r
  addT (add-done _) g a = g , a
  addT (add-op _ p t) g a with mul′ p (tl a)
  ... | g₂ , a′ = addT t (bin g g₂) a′

  mul′ : ∀ {ts e r} → ParsesMul ts e r → AL ts → Good e × AL r
  mul′ (mul p t) a with unary′ p a
  ... | g , a′ = mulT t g a′

  mulT : ∀ {l ts e r} → ParsesMulTail l ts e r → Good l → AL ts → Good e × AL r
  mulT (mul-done _) g a = g , a
  mulT (mul-op _ p t) g a with unary′ p (tl a)
  ... | g₂ , a′ = mulT t (bin g g₂) a′

  unary′ : ∀ {ts e r} → ParsesUnary ts e r → AL ts → Good e × AL r
  unary′ (neg p) a with unary′ p (tl a)
  ... | good w q , a′ = good w q , a′
  unary′ (unary p) a = app′ p a

  app′ : ∀ {ts e r} → ParsesApp ts e r → AL ts → Good e × AL r
  app′ (app p t) a with atom′ p a
  ... | g , a′ = appT t g a′

  appT : ∀ {l ts e r} → ParsesAppTail l ts e r → Good l → AL ts → Good e × AL r
  appT (app-done _) g a = g , a
  appT (app-arg _ p t) g a with atom′ p a
  ... | g₂ , a′ = appT t (appG g g₂) a′

  atom′ : ∀ {ts e r} → ParsesAtomExpr ts e r → AL ts → Good e × AL r
  atom′ atom-unit a = good tt tt , tl (tl a)
  atom′ atom-int (l ∷ a) = good tt (int l) , a
  atom′ atom-float (l ∷ a) = good tt (float l) , a
  atom′ (atom-var ¬r _) (l ∷ a) = wordName ¬r l , a
  atom′ (atom-qual ¬r) (l ∷ _ ∷ l′ ∷ a) = good ¬r (word l , word l′) , a
  atom′ (atom-paren p c) a with expr′ p (tl a)
  ... | g , a′ = paren′ c g a′
  atom′ (atom-op p) a = opGood p (tl a)
  atom′ (atom-lambda p) a = lam′ p (tl a)
  atom′ (atom-let p q) (_ ∷ lx ∷ _ ∷ a) with expr′ p a
  ... | good wv pv , a′ with expr′ q (tl a′)
  ...   | good wb pb , a″ = good (wv , wb) (word lx , pv , pb) , a″
  atom′ (atom-destruct p q s) a with expr′ p (tl a)
  ... | good ws ps , (_ ∷ _ ∷ _ ∷ lx ∷ _ ∷ a′) with expr′ q a′
  ...   | good wl pl , (_ ∷ _ ∷ ly ∷ _ ∷ a″) with expr′ s a″
  ...     | good wr pr , a‴ = good (ws , wl , wr) (ps , word lx , pl , word ly , pr) , tl a‴

  lam′ : ∀ {ts e r} → ParsesLamParams ts e r → AL ts → Good e × AL r
  lam′ (lam-body p) a = expr′ p (tl a)
  lam′ (lam-arg p) (lx ∷ a) with lam′ p a
  ... | good we pe , a′ = good we (word lx , pe) , a′

  paren′ : ∀ {e ts e′ r} → ParsesParenCont e ts e′ r → Good e → AL ts → Good e′ × AL r
  paren′ paren-close g a = g , tl a
  paren′ (paren-pair p) (good w₁ p₁) a with expr′ p (tl a)
  ... | good w₂ p₂ , a′ = good (w₁ , w₂) (p₁ , p₂) , tl a′
  paren′ (paren-annot p) (good w₁ p₁) a with GroundR.typ p (tl a)
  ... | gk , a′ = good (w₁ , gk) p₁ , tl a′

------------------------------------------------------------------------
-- Declarations
------------------------------------------------------------------------

private
  wrapGood : ∀ {ps e} → All Pw ps → Good e → Good (wrapLams ps e)
  wrapGood []       g = g
  wrapGood (p ∷ ps) g with wrapGood ps g
  ... | good w q = good w (p , q)

  params′ : ∀ {ts ps r} → ParsesParams ts ps r → AL ts → All Pw ps × AL r
  params′ (params-eq _) (l ∷ a) = word l ∷ [] , a
  params′ (params-cons _ p) (l ∷ a) with params′ p a
  ... | ps , a′ = word l ∷ ps , a′
  params′ (params-stop _ _) a = [] , a
  params′ (params-none _) a = [] , a

  funDef′ : ∀ {x ts d r} → ParsesFunDef x ts d r → AL ts → (∃[ e ] (d ≡ DFunDef x e × Good e)) × AL r
  funDef′ (fundef p q) a with params′ p a
  ... | ps , a′ with expr′ q (tl a′)
  ...   | g , a″ = (_ , refl , wrapGood ps g) , a″

  path′ : ∀ {ts p r} → ParsesModulePath ts p r → AL ts → (∃[ x ] ∃[ xs ] (p ≡ x ∷ xs × All Pw (x ∷ xs))) × AL r
  path′ (path-cons p) (l ∷ _ ∷ a) with path′ p a
  ... | (y , ys , refl , ps) , a′ = (_ , _ , refl , word l ∷ ps) , a′
  path′ (path-dotstop _) (l ∷ a) = (_ , _ , refl , word l ∷ []) , a
  path′ (path-end _) (l ∷ a) = (_ , _ , refl , word l ∷ []) , a

  alias′ : ∀ {x acc ts d r} → ParsesTypeAlias x acc ts d r → All Pw acc → AL ts
         → (∃[ ps ] ∃[ A ] (d ≡ DTypeAlias x ps A × All Pw ps × TA.Alias.WF A × PT A)) × AL r
  alias′ (alias-eq p) pa a with AliasR.typ p (tl a)
  ... | (w , q) , a′ = (_ , _ , refl , allRev [] pa , w , q) , a′
  alias′ (alias-param p) pa (l ∷ a) = alias′ p (word l ∷ pa) a

  -- A declaration's name, read as a word.
  wordDecl : ∀ {x} → NotKeyword x → LexOK (TWord x) → DeclName x × (isOperator x ≡ false → Pw x)
  wordDecl nk l with word l
  ... | p@(p-word {c = c} {i} eq ¬s ¬d st ps) = inj₂ (nk , c , i , eq , st) , (λ _ → p)

  opDecl : ∀ {ts x r} → ParsesOpChars ts [] x r → AL ts → (DeclName x × (isOperator x ≡ false → Pw x)) × AL r
  opDecl {x = x} p a with opName p [] a
  ... | on , a′ = (inj₁ on , λ e → ⊥-elim (t≢f (trans (sym (op-isOperator x on)) e))) , a′
    where
      t≢f : true ≡ false → ⊥
      t≢f ()

  sig′ : ∀ {ts A r} → SigType.ParsesType ts A r → AL ts → (TA.Sig.WF A × PT A) × AL r
  sig′ p a = SigR.typ p a

  fromDef : ∀ {x d} → DeclName x × (isOperator x ≡ false → Pw x) → ∃[ e ] (d ≡ DFunDef x e × Good e) → WFD d × PD d
  fromDef (dn , pw) (e , refl , good w p) = (dn , w) , (pw , p)

-- | A declaration read from lexed tokens is well formed and printable.
decl′ : ∀ {ts d r} → ParsesDecl ts d r → AL ts → (WFD d × PD d) × AL r
decl′ (decl-import (import-as p)) (_ ∷ a) with path′ p a
... | (x , xs , refl , ps) , (_ ∷ la ∷ a′) = (tt , (ps , word la)) , a′
decl′ (decl-import (import-plain p _)) (_ ∷ a) with path′ p a
... | (x , xs , refl , ps) , a′ = (tt , (ps , tt)) , a′
decl′ (decl-alias p) (_ ∷ lx ∷ a) with alias′ p [] a
... | (ps , A , refl , pps , w , q) , a′ = (w , (word lx , pps , q)) , a′
decl′ (decl-signature p) (_ ∷ lx ∷ _ ∷ a) with sig′ p a
... | (w , q) , a′ = (w , (word lx , q)) , a′
decl′ (decl-typesig nk p _) (lx ∷ _ ∷ a) with wordDecl nk lx | sig′ p a
... | (dn , pw) | (w , q) , a′ = ((dn , w) , (pw , q)) , a′
decl′ (decl-fundef nk _ f) (lx ∷ a) with funDef′ f a
... | ef , a′ = fromDef (wordDecl nk lx) ef , a′
decl′ (decl-op p (op-sig q)) (_ ∷ a) with opDecl p a
... | (dn , pw) , a′ with sig′ q (tl a′)
...   | (w , t) , a″ = ((dn , w) , (pw , t)) , a″
decl′ (decl-op p (op-def _ f)) (_ ∷ a) with opDecl p a
... | n , a′ with funDef′ f a′
...   | ef , a″ = fromDef n ef , a″

private
  skip′ : ∀ {ts r} → SkipNewlines ts r → AL ts → AL r
  skip′ (skip-nl s)   a = skip′ s (tl a)
  skip′ (skip-done _) a = a

decls′ : ∀ {ts ds r} → ParsesDecls ts ds r → AL ts → All WFD ds × All PD ds
decls′ (decls-stop _ _) a = [] , []
decls′ (decls-cons s p q) a with decl′ p (skip′ s a)
... | (w , pd) , a′ with decls′ q a′
...   | ws , pds = w ∷ ws , pd ∷ pds

-- | A text's module is well formed and printable.
parsed-wf : DigitBound → ∀ {text m} → Parses text m → All WFD (Module.decls m) × All PD (Module.decls m)
parsed-wf bound (ts , r , lx , pd , _) = decls′ pd (lexed-ok bound lx)
