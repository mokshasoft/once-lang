{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Spec.Surface.Grammar — which module a text is.
--
-- `Parses text m`: `text` lexes (`Spec.Surface.Lexing`) to tokens that read as
-- the declarations of `m`, followed by nothing but newlines and the end.
--
-- Types: `->` (with an optional grade `^0`/`^1`/`^w` before it) binds
-- loosest and to the right, then `+`, then `*`; atoms are `Unit`, `Void`,
-- `Int`, `Float`, `Eff A B`, `Act A B`, `Mu F`, `Nu F`, `Nu (Eff F)`,
-- `Nu (Act F)` and parentheses; a functor is built from `Id`, `K A`, `+`, `*`.
-- In a signature a lowercase word is a type variable.
--
-- Expressions, loosest first: composition `.` (left), one comparison,
-- `+`/`-` (left), `*`/`/`/`%` (left), prefix `-`, application (left). Atoms:
-- `()`, numbers, names, `name@alias`, parentheses (a pair, an annotation),
-- `\x y -> e`, `let x = e in e`, `destruct e of { Left x -> e; Right y -> e }`
-- and an operator in parentheses.
--
-- Declarations: `import a.b [as c]`, `type T p … = A`, `signature f : A`,
-- `f : A`, `f x … = e`, and the same two for an operator `(op)`.
------------------------------------------------------------------------

module Once.Spec.Surface.Grammar where

open import Data.Bool using (Bool; true; false)
open import Data.Char using (Char; isLower)
open import Data.List using (List; []; _∷_; reverse)
open import Data.Product using (_×_; Σ-syntax; ∃-syntax)
open import Data.String using (String; toList; fromList)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)
open import Relation.Nullary using (¬_)
open import Data.Maybe using (just; nothing)
open import Once.Spec.Grade using (Quantity; Zero; One; Many; Purity; pure; act; eff; mk-kind)
open import Once.Spec.Type using (Ty; Fun; Type; Unit; Void; Int; Float; _*_; _+_; _⇒[_]_; μ; ν; K; Id; _⊕_; _⊗_)
open import Once.Spec.Surface.Lexing
  using (Token; TWord; TInt; TFloat; TLParen; TRParen; TLBrace; TRBrace; TColon; TEquals; TArrow;
         TCaret1; TCaret0; TCaretW; TLambda; TComma; TSemicolon; TAt; TPipe; TDot; TPlus; TMinus;
         TStar; TSlash; TPercent; TAmpersand; TLt; TLe; TGt; TGe; TEqEq; TNeq; TNewline; TEOF; Lexes)
open import Once.Spec.Surface.Syntax
  using (PolyType; PolyFunctor; PUnit; PVoid; PInt; PFloat; _P*_; _P+_; _P⇒[_]_; PAct; PEff; Pμ; Pν; PTVar;
         PK; PId; _P⊕_; _P⊗_; BinOp; OpAdd; OpSub; OpMul; OpDiv; OpMod; OpLt; OpLe; OpGt; OpGe; OpEq; OpNe;
         Expr; RVar; RQualified; RApp; RLam; RLet; RPair; RDestruct; RUnit; RInt; RFloat; RAnnot; RBinOp; RNeg;
         Decl; DTypeSig; DFunDef; DSignature; DTypeAlias; DImport; mkImport; Module)

------------------------------------------------------------------------
-- Looking ahead
------------------------------------------------------------------------

-- The token stream starts with `t`.
data Starts : List Token → Token → Set where
  starts : ∀ {t ts} → Starts (t ∷ ts) t

data StartsWord : List Token → Set where
  starts-word : ∀ {s ts} → StartsWord (TWord s ∷ ts)

-- The grade written before an arrow.
data GradeToken : Token → Quantity → Set where
  g0 : GradeToken TCaret0 Zero
  g1 : GradeToken TCaret1 One
  gw : GradeToken TCaretW Many

------------------------------------------------------------------------
-- Types, read into any algebra of type formers
------------------------------------------------------------------------

record TypeAlg (R RF : Set) : Set₁ where
  field
    aUnit aVoid aInt aFloat : R
    aProd aSum aEff aAct    : R → R → R
    aArrow                  : Quantity → R → R → R
    aMu                     : RF → R
    aNu                     : Purity → RF → R
    fK                      : R → RF
    fId                     : RF
    fSum fProd              : RF → RF → RF
    -- what else may stand as an atom (a type variable, in a signature)
    Extra                   : List Token → R → List Token → Set

module Types {R RF : Set} (alg : TypeAlg R RF) where
  open TypeAlg alg

  data ParsesAtom      : List Token → R → List Token → Set
  data ParsesProdTail  : R → List Token → R → List Token → Set
  data ParsesSumTail   : R → List Token → R → List Token → Set
  data ParsesProd      : List Token → R → List Token → Set
  data ParsesSum       : List Token → R → List Token → Set
  data ParsesType      : List Token → R → List Token → Set
  data ParsesArrowTail : R → List Token → R → List Token → Set
  data ParsesFunAtom   : List Token → RF → List Token → Set
  data ParsesFunProd   : List Token → RF → List Token → Set
  data ParsesFunProdTail : RF → List Token → RF → List Token → Set
  data ParsesFunSum    : List Token → RF → List Token → Set
  data ParsesFunSumTail : RF → List Token → RF → List Token → Set

  data ParsesAtom where
    a-unit  : ∀ {r} → ParsesAtom (TWord "Unit" ∷ r) aUnit r
    a-void  : ∀ {r} → ParsesAtom (TWord "Void" ∷ r) aVoid r
    a-int   : ∀ {r} → ParsesAtom (TWord "Int" ∷ r) aInt r
    a-float : ∀ {r} → ParsesAtom (TWord "Float" ∷ r) aFloat r
    a-eff   : ∀ {ts₁ ts₂ r A B} → ParsesAtom ts₁ A ts₂ → ParsesAtom ts₂ B r → ParsesAtom (TWord "Eff" ∷ ts₁) (aEff A B) r
    a-act   : ∀ {ts₁ ts₂ r A B} → ParsesAtom ts₁ A ts₂ → ParsesAtom ts₂ B r → ParsesAtom (TWord "Act" ∷ ts₁) (aAct A B) r
    a-mu    : ∀ {ts r F} → ParsesFunSum ts F r → ParsesAtom (TWord "Mu" ∷ ts) (aMu F) r
    a-nu    : ∀ {ts r F} → ParsesFunSum ts F r → ParsesAtom (TWord "Nu" ∷ ts) (aNu pure F) r
    a-nu-eff : ∀ {ts r F} → ParsesFunSum ts F (TRParen ∷ r)
             → ParsesAtom (TWord "Nu" ∷ TLParen ∷ TWord "Eff" ∷ ts) (aNu eff F) r
    a-nu-act : ∀ {ts r F} → ParsesFunSum ts F (TRParen ∷ r)
             → ParsesAtom (TWord "Nu" ∷ TLParen ∷ TWord "Act" ∷ ts) (aNu act F) r
    a-extra : ∀ {ts A r} → Extra ts A r → ParsesAtom ts A r
    a-paren : ∀ {ts A r} → ParsesType ts A (TRParen ∷ r) → ParsesAtom (TLParen ∷ ts) A r

  data ParsesProd where
    prod : ∀ {ts ts₁ r A T} → ParsesAtom ts A ts₁ → ParsesProdTail A ts₁ T r → ParsesProd ts T r
  data ParsesProdTail where
    prod-done : ∀ {l ts} → ¬ Starts ts TStar → ParsesProdTail l ts l ts
    prod-star : ∀ {l ts ts₂ r B T} → ParsesAtom ts B ts₂ → ParsesProdTail (aProd l B) ts₂ T r
              → ParsesProdTail l (TStar ∷ ts) T r

  data ParsesSum where
    sum : ∀ {ts ts₁ r A T} → ParsesProd ts A ts₁ → ParsesSumTail A ts₁ T r → ParsesSum ts T r
  data ParsesSumTail where
    sum-done : ∀ {l ts} → ¬ Starts ts TPlus → ParsesSumTail l ts l ts
    sum-plus : ∀ {l ts ts₂ r B T} → ParsesProd ts B ts₂ → ParsesSumTail (aSum l B) ts₂ T r
             → ParsesSumTail l (TPlus ∷ ts) T r

  data ParsesType where
    type : ∀ {ts ts₁ r A T} → ParsesSum ts A ts₁ → ParsesArrowTail A ts₁ T r → ParsesType ts T r
  data ParsesArrowTail where
    arrow-done  : ∀ {l ts} → ¬ Starts ts TArrow → ¬ Starts ts TCaret0 → ¬ Starts ts TCaret1 → ¬ Starts ts TCaretW
                → ParsesArrowTail l ts l ts
    arrow-grade : ∀ {l t q ts r B} → GradeToken t q → ParsesType ts B r
                → ParsesArrowTail l (t ∷ TArrow ∷ ts) (aArrow q l B) r
    arrow       : ∀ {l ts r B} → ParsesType ts B r → ParsesArrowTail l (TArrow ∷ ts) (aArrow Many l B) r

  data ParsesFunAtom where
    f-id    : ∀ {r} → ParsesFunAtom (TWord "Id" ∷ r) fId r
    f-k     : ∀ {ts r A} → ParsesAtom ts A r → ParsesFunAtom (TWord "K" ∷ ts) (fK A) r
    f-paren : ∀ {ts r F} → ParsesFunSum ts F (TRParen ∷ r) → ParsesFunAtom (TLParen ∷ ts) F r
  data ParsesFunProd where
    fprod : ∀ {ts ts₁ r A F} → ParsesFunAtom ts A ts₁ → ParsesFunProdTail A ts₁ F r → ParsesFunProd ts F r
  data ParsesFunProdTail where
    fprod-done : ∀ {l ts} → ¬ Starts ts TStar → ParsesFunProdTail l ts l ts
    fprod-star : ∀ {l ts ts₂ r B F} → ParsesFunAtom ts B ts₂ → ParsesFunProdTail (fProd l B) ts₂ F r
               → ParsesFunProdTail l (TStar ∷ ts) F r
  data ParsesFunSum where
    fsum : ∀ {ts ts₁ r A F} → ParsesFunProd ts A ts₁ → ParsesFunSumTail A ts₁ F r → ParsesFunSum ts F r
  data ParsesFunSumTail where
    fsum-done : ∀ {l ts} → ¬ Starts ts TPlus → ParsesFunSumTail l ts l ts
    fsum-plus : ∀ {l ts ts₂ r B F} → ParsesFunProd ts B ts₂ → ParsesFunSumTail (fSum l B) ts₂ F r
              → ParsesFunSumTail l (TPlus ∷ ts) F r

-- Nothing else is an atom.
data NoExtra {R : Set} : List Token → R → List Token → Set where

-- A word starting with a lowercase letter.
lowerWord : String → Bool
lowerWord s = go (toList s)
  where
    go : List Char → Bool
    go []      = false
    go (c ∷ _) = isLower c

data TypeVar : List Token → PolyType → List Token → Set where
  tvar : ∀ {x r} → lowerWord x ≡ true → TypeVar (TWord x ∷ r) (PTVar x) r

private
  written : (Extra : List Token → PolyType → List Token → Set) → TypeAlg PolyType PolyFunctor
  written X = record
    { aUnit = PUnit ; aVoid = PVoid ; aInt = PInt ; aFloat = PFloat
    ; aProd = _P*_ ; aSum = _P+_ ; aEff = PEff ; aAct = PAct
    ; aArrow = λ q A B → A P⇒[ q ] B ; aMu = Pμ ; aNu = λ π F → Pν F π
    ; fK = PK ; fId = PId ; fSum = _P⊕_ ; fProd = _P⊗_
    ; Extra = X }

  ground : TypeAlg Type (Fun 0)
  ground = record
    { aUnit = Unit ; aVoid = Void ; aInt = Int ; aFloat = Float
    ; aProd = _*_ ; aSum = _+_
    ; aEff = λ A B → A ⇒[ mk-kind Many eff ] B ; aAct = λ A B → A ⇒[ mk-kind Many act ] B
    ; aArrow = λ q A B → A ⇒[ mk-kind q pure ] B ; aMu = μ ; aNu = λ π F → ν F π
    ; fK = K ; fId = Id ; fSum = _⊕_ ; fProd = _⊗_
    ; Extra = NoExtra }

-- A type in a signature (it may have type variables), in a type alias (it
-- may not), and in an annotation (a ground type).
module SigType   = Types (written TypeVar)
module AliasType = Types (written NoExtra)
module Annot     = Types ground

------------------------------------------------------------------------
-- Expressions
------------------------------------------------------------------------

data Reserved : String → Set where
  r-in : Reserved "in"
  r-of : Reserved "of"
  r-let : Reserved "let"
  r-destruct : Reserved "destruct"
  r-Left : Reserved "Left"
  r-Right : Reserved "Right"

-- What may start an argument of an application.
data ArgStart : List Token → Set where
  as-paren  : ∀ {ts} → ArgStart (TLParen ∷ ts)
  as-lambda : ∀ {ts} → ArgStart (TLambda ∷ ts)
  as-int    : ∀ {n ts} → ArgStart (TInt n ∷ ts)
  as-float  : ∀ {i f l ts} → ArgStart (TFloat i f l ∷ ts)
  as-word   : ∀ {x ts} → ¬ Reserved x → ArgStart (TWord x ∷ ts)

-- `@alias` follows.
data QualSuffix : List Token → Set where
  qual-suffix : ∀ {a ts} → QualSuffix (TAt ∷ TWord a ∷ ts)

-- The operator characters a parenthesized operator is made of.
data OpChar : Token → Char → Set where
  oc-dot   : OpChar TDot '.'
  oc-plus  : OpChar TPlus '+'
  oc-minus : OpChar TMinus '-'
  oc-star  : OpChar TStar '*'
  oc-slash : OpChar TSlash '/'
  oc-pct   : OpChar TPercent '%'
  oc-lt    : OpChar TLt '<'
  oc-gt    : OpChar TGt '>'
  oc-pipe  : OpChar TPipe '|'
  oc-amp   : OpChar TAmpersand '&'
  oc-at    : OpChar TAt '@'

-- An operator name up to its closing parenthesis (`cs`: read so far, reversed).
data ParsesOpChars : List Token → List Char → String → List Token → Set where
  op-close : ∀ {c cs r} → ParsesOpChars (TRParen ∷ r) (c ∷ cs) (fromList (reverse (c ∷ cs))) r
  op-char  : ∀ {t ch cs s r ts} → OpChar t ch → ParsesOpChars ts (ch ∷ cs) s r → ParsesOpChars (t ∷ ts) cs s r

data CompareToken : Token → BinOp → Set where
  ct-lt : CompareToken TLt OpLt
  ct-le : CompareToken TLe OpLe
  ct-gt : CompareToken TGt OpGt
  ct-ge : CompareToken TGe OpGe
  ct-eq : CompareToken TEqEq OpEq
  ct-ne : CompareToken TNeq OpNe

data AddToken : Token → BinOp → Set where
  at-plus  : AddToken TPlus OpAdd
  at-minus : AddToken TMinus OpSub

data MulToken : Token → BinOp → Set where
  mt-star  : MulToken TStar OpMul
  mt-slash : MulToken TSlash OpDiv
  mt-pct   : MulToken TPercent OpMod

data ParsesExpr     : List Token → Expr → List Token → Set
data ParsesCompTail : Expr → List Token → Expr → List Token → Set
data ParsesCmp      : List Token → Expr → List Token → Set
data ParsesAdd      : List Token → Expr → List Token → Set
data ParsesAddTail  : Expr → List Token → Expr → List Token → Set
data ParsesMul      : List Token → Expr → List Token → Set
data ParsesMulTail  : Expr → List Token → Expr → List Token → Set
data ParsesUnary    : List Token → Expr → List Token → Set
data ParsesApp      : List Token → Expr → List Token → Set
data ParsesAppTail  : Expr → List Token → Expr → List Token → Set
data ParsesAtomExpr : List Token → Expr → List Token → Set
data ParsesLamParams : List Token → Expr → List Token → Set
data ParsesParenCont : Expr → List Token → Expr → List Token → Set

-- `f . g` is `compose f g`.
data ParsesExpr where
  expr : ∀ {ts ts₁ r e₁ e} → ParsesCmp ts e₁ ts₁ → ParsesCompTail e₁ ts₁ e r → ParsesExpr ts e r
data ParsesCompTail where
  comp-done : ∀ {l ts} → ¬ Starts ts TDot → ParsesCompTail l ts l ts
  comp-dot  : ∀ {l ts ts₂ r e₂ e} → ParsesCmp ts e₂ ts₂
            → ParsesCompTail (RApp (RApp (RVar "compose") l) e₂) ts₂ e r
            → ParsesCompTail l (TDot ∷ ts) e r

-- At most one comparison.
data ParsesCmp where
  cmp-none : ∀ {ts e r} → ParsesAdd ts e r → (∀ {t op} → Starts r t → ¬ CompareToken t op) → ParsesCmp ts e r
  cmp      : ∀ {ts t op ts₁ r l e} → CompareToken t op → ParsesAdd ts l (t ∷ ts₁) → ParsesAdd ts₁ e r
           → ParsesCmp ts (RBinOp op l e) r

data ParsesAdd where
  add : ∀ {ts ts₁ r e₁ e} → ParsesMul ts e₁ ts₁ → ParsesAddTail e₁ ts₁ e r → ParsesAdd ts e r
data ParsesAddTail where
  add-done : ∀ {l ts} → (∀ {t op} → Starts ts t → ¬ AddToken t op) → ParsesAddTail l ts l ts
  add-op   : ∀ {l t op ts ts₂ r e₂ e} → AddToken t op → ParsesMul ts e₂ ts₂ → ParsesAddTail (RBinOp op l e₂) ts₂ e r
           → ParsesAddTail l (t ∷ ts) e r

data ParsesMul where
  mul : ∀ {ts ts₁ r e₁ e} → ParsesUnary ts e₁ ts₁ → ParsesMulTail e₁ ts₁ e r → ParsesMul ts e r
data ParsesMulTail where
  mul-done : ∀ {l ts} → (∀ {t op} → Starts ts t → ¬ MulToken t op) → ParsesMulTail l ts l ts
  mul-op   : ∀ {l t op ts ts₂ r e₂ e} → MulToken t op → ParsesUnary ts e₂ ts₂ → ParsesMulTail (RBinOp op l e₂) ts₂ e r
           → ParsesMulTail l (t ∷ ts) e r

data ParsesUnary where
  neg   : ∀ {ts r e} → ParsesUnary ts e r → ParsesUnary (TMinus ∷ ts) (RNeg e) r
  unary : ∀ {ts r e} → ParsesApp ts e r → ParsesUnary ts e r

data ParsesApp where
  app : ∀ {ts ts₁ r f e} → ParsesAtomExpr ts f ts₁ → ParsesAppTail f ts₁ e r → ParsesApp ts e r
data ParsesAppTail where
  app-done : ∀ {l ts} → ¬ ArgStart ts → ParsesAppTail l ts l ts
  app-arg  : ∀ {l ts ts₂ r a e} → ArgStart ts → ParsesAtomExpr ts a ts₂ → ParsesAppTail (RApp l a) ts₂ e r
           → ParsesAppTail l ts e r

data ParsesAtomExpr where
  atom-unit   : ∀ {r} → ParsesAtomExpr (TLParen ∷ TRParen ∷ r) RUnit r
  atom-int    : ∀ {n r} → ParsesAtomExpr (TInt n ∷ r) (RInt n) r
  atom-float  : ∀ {i f l r} → ParsesAtomExpr (TFloat i f l ∷ r) (RFloat i f l) r
  atom-var    : ∀ {x r} → ¬ Reserved x → ¬ QualSuffix r → ParsesAtomExpr (TWord x ∷ r) (RVar x) r
  atom-qual   : ∀ {x a r} → ¬ Reserved x → ParsesAtomExpr (TWord x ∷ TAt ∷ TWord a ∷ r) (RQualified x a) r
  atom-paren  : ∀ {ts ts₁ r e e′} → ParsesExpr ts e ts₁ → ParsesParenCont e ts₁ e′ r → ParsesAtomExpr (TLParen ∷ ts) e′ r
  atom-op     : ∀ {ts s r} → ParsesOpChars ts [] s r → ParsesAtomExpr (TLParen ∷ ts) (RVar s) r
  atom-lambda : ∀ {ts e r} → ParsesLamParams ts e r → ParsesAtomExpr (TLambda ∷ ts) e r
  atom-let    : ∀ {x ts ts₁ r v b} → ParsesExpr ts v (TWord "in" ∷ ts₁) → ParsesExpr ts₁ b r
              → ParsesAtomExpr (TWord "let" ∷ TWord x ∷ TEquals ∷ ts) (RLet x v b) r
  atom-destruct : ∀ {ts ts₁ ts₂ r s x y el er}
                → ParsesExpr ts s (TWord "of" ∷ TLBrace ∷ TWord "Left" ∷ TWord x ∷ TArrow ∷ ts₁)
                → ParsesExpr ts₁ el (TSemicolon ∷ TWord "Right" ∷ TWord y ∷ TArrow ∷ ts₂)
                → ParsesExpr ts₂ er (TRBrace ∷ r)
                → ParsesAtomExpr (TWord "destruct" ∷ ts) (RDestruct s x el y er) r

-- `\x y -> e` is `\x -> \y -> e`.
data ParsesLamParams where
  lam-body : ∀ {ts e r} → ParsesExpr ts e r → ParsesLamParams (TArrow ∷ ts) e r
  lam-arg  : ∀ {x ts e r} → ParsesLamParams ts e r → ParsesLamParams (TWord x ∷ ts) (RLam x e) r

-- After a parenthesized expression: `)`, `, e)` (a pair) or `: A)`.
data ParsesParenCont where
  paren-close : ∀ {e r} → ParsesParenCont e (TRParen ∷ r) e r
  paren-pair  : ∀ {e ts e₂ r} → ParsesExpr ts e₂ (TRParen ∷ r) → ParsesParenCont e (TComma ∷ ts) (RPair e e₂) r
  paren-annot : ∀ {e ts A r} → Annot.ParsesType ts A (TRParen ∷ r) → ParsesParenCont e (TColon ∷ ts) (RAnnot e A) r

------------------------------------------------------------------------
-- Declarations
------------------------------------------------------------------------

-- `f x y = e` is `f = \x y -> e`.
wrapLams : List String → Expr → Expr
wrapLams []       e = e
wrapLams (x ∷ xs) e = RLam x (wrapLams xs e)

-- The parameters of a definition, up to `=`.
data ParsesParams : List Token → List String → List Token → Set where
  params-eq     : ∀ {x ts} → Starts ts TEquals → ParsesParams (TWord x ∷ ts) (x ∷ []) ts
  params-cons   : ∀ {x ts ps r} → StartsWord ts → ParsesParams ts ps r → ParsesParams (TWord x ∷ ts) (x ∷ ps) r
  params-stop   : ∀ {x ts} → ¬ Starts ts TEquals → ¬ StartsWord ts → ParsesParams (TWord x ∷ ts) [] (TWord x ∷ ts)
  params-none   : ∀ {ts} → ¬ StartsWord ts → ParsesParams ts [] ts

data ParsesFunDef (x : String) : List Token → Decl → List Token → Set where
  fundef : ∀ {ts ps ts₁ e r} → ParsesParams ts ps (TEquals ∷ ts₁) → ParsesExpr ts₁ e r
         → ParsesFunDef x ts (DFunDef x (wrapLams ps e)) r

-- `a.b.c`
data ParsesModulePath : List Token → List String → List Token → Set where
  path-cons    : ∀ {x ts p r} → ParsesModulePath ts p r → ParsesModulePath (TWord x ∷ TDot ∷ ts) (x ∷ p) r
  path-dotstop : ∀ {x ts} → ¬ StartsWord ts → ParsesModulePath (TWord x ∷ TDot ∷ ts) (x ∷ []) (TDot ∷ ts)
  path-end     : ∀ {x ts} → ¬ Starts ts TDot → ParsesModulePath (TWord x ∷ ts) (x ∷ []) ts

data ParsesImport : List Token → Decl → List Token → Set where
  import-as : ∀ {ts p a r} → ParsesModulePath ts p (TWord "as" ∷ TWord a ∷ r)
            → ParsesImport ts (DImport (mkImport p (just a))) r
  import-plain : ∀ {ts p r} → ParsesModulePath ts p r → ¬ Starts r (TWord "as")
            → ParsesImport ts (DImport (mkImport p nothing)) r

-- `T p … = A` (the parameters collected in reverse).
data ParsesTypeAlias (x : String) : List String → List Token → Decl → List Token → Set where
  alias-eq    : ∀ {ps ts A r} → AliasType.ParsesType ts A r
              → ParsesTypeAlias x ps (TEquals ∷ ts) (DTypeAlias x (reverse ps) A) r
  alias-param : ∀ {ps p ts d r} → ParsesTypeAlias x (p ∷ ps) ts d r → ParsesTypeAlias x ps (TWord p ∷ ts) d r

data ParsesOpAfter (x : String) : List Token → Decl → List Token → Set where
  op-sig : ∀ {ts A r} → SigType.ParsesType ts A r → ParsesOpAfter x (TColon ∷ ts) (DTypeSig x A) r
  op-def : ∀ {ts d r} → ¬ Starts ts TColon → ParsesFunDef x ts d r → ParsesOpAfter x ts d r

data NotKeyword : String → Set where
  not-keyword : ∀ {w} → w ≢ "import" → w ≢ "type" → w ≢ "signature" → NotKeyword w

data ParsesDecl : List Token → Decl → List Token → Set where
  decl-import    : ∀ {ts d r} → ParsesImport ts d r → ParsesDecl (TWord "import" ∷ ts) d r
  decl-alias     : ∀ {x ts d r} → ParsesTypeAlias x [] ts d r → ParsesDecl (TWord "type" ∷ TWord x ∷ ts) d r
  decl-signature : ∀ {x ts A r} → SigType.ParsesType ts A r
                 → ParsesDecl (TWord "signature" ∷ TWord x ∷ TColon ∷ ts) (DSignature x A) r
  decl-typesig   : ∀ {x ts A r} → NotKeyword x → SigType.ParsesType ts A r → ¬ Starts r TEquals
                 → ParsesDecl (TWord x ∷ TColon ∷ ts) (DTypeSig x A) r
  decl-fundef    : ∀ {x ts d r} → NotKeyword x → ¬ Starts ts TColon → ParsesFunDef x ts d r
                 → ParsesDecl (TWord x ∷ ts) d r
  decl-op        : ∀ {ts x ts₁ d r} → ParsesOpChars ts [] x ts₁ → ParsesOpAfter x ts₁ d r
                 → ParsesDecl (TLParen ∷ ts) d r

-- Leading newlines dropped.
data SkipNewlines : List Token → List Token → Set where
  skip-nl   : ∀ {ts r} → SkipNewlines ts r → SkipNewlines (TNewline ∷ ts) r
  skip-done : ∀ {ts} → ¬ Starts ts TNewline → SkipNewlines ts ts

-- Declarations, as long as one parses.
data ParsesDecls : List Token → List Decl → List Token → Set where
  decls-stop : ∀ {ts ts₁} → SkipNewlines ts ts₁ → (∀ {d r} → ¬ ParsesDecl ts₁ d r) → ParsesDecls ts [] ts₁
  decls-cons : ∀ {ts ts₁ d r ds r′} → SkipNewlines ts ts₁ → ParsesDecl ts₁ d r → ParsesDecls r ds r′
             → ParsesDecls ts (d ∷ ds) r′

-- Only newlines and the end.
data Trailing : List Token → Set where
  trail-end : Trailing []
  trail-nl  : ∀ {ts} → Trailing ts → Trailing (TNewline ∷ ts)
  trail-eof : ∀ {ts} → Trailing ts → Trailing (TEOF ∷ ts)

Parses : String → Module → Set
Parses text m = Σ[ ts ∈ List Token ] Σ[ r ∈ List Token ]
                  Lexes text ts × ParsesDecls ts (Module.decls m) r × Trailing r
