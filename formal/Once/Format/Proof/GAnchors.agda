-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Format.Proof.GAnchors — what a declaration's tokens hold, by the
-- grammar (plan 0.124 step 4.5).
--
-- Whatever its spelling, a declaration's tokens (`Spec.Surface.Grammar`)
-- hold as many anchors (words but `compose`, literals) as its syntax tree
-- says (`cE`, `cT`, `cD`: the words and literals every spelling keeps;
-- parentheses, operators, `compose` written `.` and grades are no anchors),
-- and no line end. So the anchors the comment walker counts in a source,
-- declaration by declaration, are the anchors the printer numbers.
------------------------------------------------------------------------

module Once.Format.Proof.GAnchors where

open import Data.Bool using (Bool; true; false; not; if_then_else_; T)
open import Data.List using (List; []; _∷_; _++_; reverse; foldr)
open import Data.List.Properties using (++-assoc)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
import Data.List.Relation.Unary.All.Properties as AllP
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-assoc; +-comm; +-identityʳ)
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ; ∃-syntax)
open import Data.String using (String)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst)

open import Once.Spec.Grade using (Quantity; Finite; pureᶠ; actᶠ)
open import Once.Spec.Surface.Lexing using (Token; TWord; TInt; TFloat; TNewline; TLParen; TRParen; TStar; TPlus;
  TArrow; TCaret0; TCaret1; TCaretW)
open import Once.Spec.Surface.Syntax using (PolyType; PolyFunctor; PUnit; PVoid; PInt; PFloat; _P*_; _P+_;
  _P⇒[_]_; PAct; PEff; Pμ; Pν; PTVar; PK; PId; _P⊕_; _P⊗_)
open import Once.Spec.Surface.Grammar using (TypeAlg; module Types; GradeToken; g0; g1; gw)
open import Once.Format.Proof.Counts using (anchors)
open import Once.Format.Proof.Skeleton using (anchorTok)

------------------------------------------------------------------------
-- Segments
------------------------------------------------------------------------

-- | No line end among tokens.
NoNl : List Token → Set
NoNl = All (_≢ TNewline)

-- | `ts` is a segment holding `n` anchors and no line end, then `r`.
Seg : ℕ → List Token → List Token → Set
Seg n ts r = Σ (List Token) λ seg → ts ≡ seg ++ r × anchors seg ≡ n × NoNl seg

anchors-++ : ∀ xs ys → anchors (xs ++ ys) ≡ anchors xs + anchors ys
anchors-++ []       ys = refl
anchors-++ (x ∷ xs) ys = trans (cong ((if anchorTok x then 1 else 0) +_) (anchors-++ xs ys))
                               (sym (+-assoc (if anchorTok x then 1 else 0) (anchors xs) (anchors ys)))

-- | A token, then a segment.
seg-cons : ∀ {n ts r} t → t ≢ TNewline → Seg n ts r → Seg ((if anchorTok t then 1 else 0) + n) (t ∷ ts) r
seg-cons t nt (seg , refl , ea , nn) = t ∷ seg , refl , cong ((if anchorTok t then 1 else 0) +_) ea , nt ∷ nn

-- | Two segments, one after the other.
seg-++ : ∀ {m n ts ts₁ r} → Seg m ts ts₁ → Seg n ts₁ r → Seg (m + n) ts r
seg-++ (s₁ , refl , e₁ , n₁) (s₂ , refl , e₂ , n₂) =
  s₁ ++ s₂ , sym (++-assoc s₁ s₂ _) , trans (anchors-++ s₁ s₂) (cong₂ _+_ e₁ e₂) , AllP.++⁺ n₁ n₂

seg-nil : ∀ {r} → Seg 0 r r
seg-nil = [] , refl , refl , []

seg-cast : ∀ {m n ts r} → m ≡ n → Seg m ts r → Seg n ts r
seg-cast refl s = s

-- | After an operand holding `base` anchors, a segment that makes it hold `n`.
TSeg : ℕ → ℕ → List Token → List Token → Set
TSeg base n ts r = Σ (List Token) λ seg → ts ≡ seg ++ r × base + anchors seg ≡ n × NoNl seg

tseg-nil : ∀ {base r} → TSeg base base r r
tseg-nil {base} = [] , refl , +-identityʳ base , []

-- | An operator that is no anchor, an operand, the rest.
tseg-step : ∀ {base m mid n ts ts₂ r} t → t ≢ TNewline → (if anchorTok t then 1 else 0) ≡ 0 → mid ≡ base + m
          → Seg m ts ts₂ → TSeg mid n ts₂ r → TSeg base n (t ∷ ts) r
tseg-step {base} {m} t nt na em (s₁ , refl , e₁ , n₁) (s₂ , refl , e₂ , n₂) =
  t ∷ s₁ ++ s₂ , cong (t ∷_) (sym (++-assoc s₁ s₂ _)) ,
  trans (cong (base +_) (trans (cong (_+ anchors (s₁ ++ s₂)) na) (anchors-++ s₁ s₂)))
    (trans (sym (+-assoc base (anchors s₁) (anchors s₂)))
      (trans (cong (λ x → base + x + anchors s₂) e₁) (trans (cong (_+ anchors s₂) (sym em)) e₂))) ,
  nt ∷ AllP.++⁺ n₁ n₂

-- | An operand, then what follows it.
head-tail : ∀ {m n ts ts₁ r} → Seg m ts ts₁ → TSeg m n ts₁ r → Seg n ts r
head-tail (s₁ , refl , e₁ , n₁) (s₂ , refl , e₂ , n₂) =
  s₁ ++ s₂ , sym (++-assoc s₁ s₂ _) , trans (anchors-++ s₁ s₂) (trans (cong (_+ anchors s₂) e₁) e₂) , AllP.++⁺ n₁ n₂

------------------------------------------------------------------------
-- Types
------------------------------------------------------------------------

-- | A word's anchors.
wc : String → ℕ
wc x = if anchorTok (TWord x) then 1 else 0

-- | The anchors of a type, as written (`Print.pty`).
mutual
  cT : PolyType → ℕ
  cT PUnit         = 1
  cT PVoid         = 1
  cT PInt          = 1
  cT PFloat        = 1
  cT (A P* B)      = cT A + cT B
  cT (A P+ B)      = cT A + cT B
  cT (A P⇒[ q ] B) = cT A + cT B
  cT (PAct A B)    = 1 + (cT A + cT B)
  cT (PEff A B)    = 1 + (cT A + cT B)
  cT (Pμ F)        = 1 + cF F
  cT (Pν F pureᶠ)  = 1 + cF F
  cT (Pν F actᶠ)   = 2 + cF F
  cT (PTVar x)     = wc x

  cF : PolyFunctor → ℕ
  cF PId      = 1
  cF (PK A)   = 1 + cT A
  cF (F P⊕ G) = cF F + cF G
  cF (F P⊗ G) = cF F + cF G

-- | The types of any algebra, with a count that agrees with the formers.
module TypeAnchors {R RF : Set} (alg : TypeAlg R RF) (cR : R → ℕ) (cRF : RF → ℕ)
  (l-unit : cR (TypeAlg.aUnit alg) ≡ 1) (l-void : cR (TypeAlg.aVoid alg) ≡ 1)
  (l-int : cR (TypeAlg.aInt alg) ≡ 1) (l-float : cR (TypeAlg.aFloat alg) ≡ 1)
  (l-prod : ∀ a b → cR (TypeAlg.aProd alg a b) ≡ cR a + cR b)
  (l-sum : ∀ a b → cR (TypeAlg.aSum alg a b) ≡ cR a + cR b)
  (l-eff : ∀ a b → cR (TypeAlg.aEff alg a b) ≡ 1 + (cR a + cR b))
  (l-act : ∀ a b → cR (TypeAlg.aAct alg a b) ≡ 1 + (cR a + cR b))
  (l-arrow : ∀ q a b → cR (TypeAlg.aArrow alg q a b) ≡ cR a + cR b)
  (l-mu : ∀ f → cR (TypeAlg.aMu alg f) ≡ 1 + cRF f)
  (l-nu : ∀ f → cR (TypeAlg.aNu alg pureᶠ f) ≡ 1 + cRF f)
  (l-nu-act : ∀ f → cR (TypeAlg.aNu alg actᶠ f) ≡ 2 + cRF f)
  (l-k : ∀ a → cRF (TypeAlg.fK alg a) ≡ 1 + cR a) (l-id : cRF (TypeAlg.fId alg) ≡ 1)
  (l-fsum : ∀ f g → cRF (TypeAlg.fSum alg f g) ≡ cRF f + cRF g)
  (l-fprod : ∀ f g → cRF (TypeAlg.fProd alg f g) ≡ cRF f + cRF g)
  (l-extra : ∀ {ts A r} → TypeAlg.Extra alg ts A r → Seg (cR A) ts r)
  where

  open Types alg

  -- (the tails: what they add to the left operand's anchors)
  mutual
    atom : ∀ {ts A r} → ParsesAtom ts A r → Seg (cR A) ts r
    atom a-unit  = seg-cast (sym l-unit) (seg-cons _ (λ ()) seg-nil)
    atom a-void  = seg-cast (sym l-void) (seg-cons _ (λ ()) seg-nil)
    atom a-int   = seg-cast (sym l-int) (seg-cons _ (λ ()) seg-nil)
    atom a-float = seg-cast (sym l-float) (seg-cons _ (λ ()) seg-nil)
    atom (a-eff p q) = seg-cast (sym (l-eff _ _)) (seg-cons _ (λ ()) (seg-++ (atom p) (atom q)))
    atom (a-act p q) = seg-cast (sym (l-act _ _)) (seg-cons _ (λ ()) (seg-++ (atom p) (atom q)))
    atom (a-mu p)    = seg-cast (sym (l-mu _)) (seg-cons _ (λ ()) (fsum′ p))
    atom (a-nu p)    = seg-cast (sym (l-nu _)) (seg-cons _ (λ ()) (fsum′ p))
    atom (a-nu-act p) =
      seg-cast (sym (l-nu-act _)) (seg-cons _ (λ ()) (seg-cons TLParen (λ ()) (seg-cons _ (λ ())
        (seg-cast (+-identityʳ _) (seg-++ (fsum′ p) (seg-cons TRParen (λ ()) seg-nil))))))
    atom (a-extra x) = l-extra x
    atom (a-paren p) = seg-cons TLParen (λ ()) (seg-cast (+-identityʳ _) (seg-++ (ty p) (seg-cons TRParen (λ ()) seg-nil)))

    prodT : ∀ {l ts A r} → ParsesProdTail l ts A r → TSeg (cR l) (cR A) ts r
    prodT (prod-done _)  = tseg-nil
    prodT (prod-star p t) = tseg-step TStar (λ ()) refl (l-prod _ _) (atom p) (prodT t)

    prod′ : ∀ {ts A r} → ParsesProd ts A r → Seg (cR A) ts r
    prod′ (prod a t) = head-tail (atom a) (prodT t)

    sumT : ∀ {l ts A r} → ParsesSumTail l ts A r → TSeg (cR l) (cR A) ts r
    sumT (sum-done _)  = tseg-nil
    sumT (sum-plus p t) = tseg-step TPlus (λ ()) refl (l-sum _ _) (prod′ p) (sumT t)

    sum′ : ∀ {ts A r} → ParsesSum ts A r → Seg (cR A) ts r
    sum′ (sum p t) = head-tail (prod′ p) (sumT t)

    arrowT : ∀ {l ts A r} → ParsesArrowTail l ts A r → TSeg (cR l) (cR A) ts r
    arrowT (arrow-done _ _ _ _) = tseg-nil
    arrowT (arrow-grade g p)    = grade-step g (ty p)
    arrowT (arrow p)            = tseg-step TArrow (λ ()) refl (l-arrow _ _ _) (ty p) tseg-nil

    grade-step : ∀ {l t q ts r B} → GradeToken t q → Seg (cR B) ts r → TSeg (cR l) (cR (TypeAlg.aArrow alg q l B)) (t ∷ TArrow ∷ ts) r
    grade-step g0 sB = tseg-step TCaret0 (λ ()) refl (l-arrow _ _ _) (seg-cons TArrow (λ ()) sB) tseg-nil
    grade-step g1 sB = tseg-step TCaret1 (λ ()) refl (l-arrow _ _ _) (seg-cons TArrow (λ ()) sB) tseg-nil
    grade-step gw sB = tseg-step TCaretW (λ ()) refl (l-arrow _ _ _) (seg-cons TArrow (λ ()) sB) tseg-nil

    ty : ∀ {ts A r} → ParsesType ts A r → Seg (cR A) ts r
    ty (type p t) = head-tail (sum′ p) (arrowT t)

    fatom : ∀ {ts F r} → ParsesFunAtom ts F r → Seg (cRF F) ts r
    fatom f-id        = seg-cast (sym l-id) (seg-cons _ (λ ()) seg-nil)
    fatom (f-k p)     = seg-cast (sym (l-k _)) (seg-cons _ (λ ()) (atom p))
    fatom (f-paren p) = seg-cons TLParen (λ ()) (seg-cast (+-identityʳ _) (seg-++ (fsum′ p) (seg-cons TRParen (λ ()) seg-nil)))

    fprodT : ∀ {l ts F r} → ParsesFunProdTail l ts F r → TSeg (cRF l) (cRF F) ts r
    fprodT (fprod-done _)  = tseg-nil
    fprodT (fprod-star p t) = tseg-step TStar (λ ()) refl (l-fprod _ _) (fatom p) (fprodT t)

    fprod′ : ∀ {ts F r} → ParsesFunProd ts F r → Seg (cRF F) ts r
    fprod′ (fprod a t) = head-tail (fatom a) (fprodT t)

    fsumT : ∀ {l ts F r} → ParsesFunSumTail l ts F r → TSeg (cRF l) (cRF F) ts r
    fsumT (fsum-done _)  = tseg-nil
    fsumT (fsum-plus p t) = tseg-step TPlus (λ ()) refl (l-fsum _ _) (fprod′ p) (fsumT t)

    fsum′ : ∀ {ts F r} → ParsesFunSum ts F r → Seg (cRF F) ts r
    fsum′ (fsum p t) = head-tail (fprod′ p) (fsumT t)

-- The three type grammars (their algebras, as `Spec.Surface.Grammar` writes them).
open import Once.Spec.Type using (Ty; Fun; Type; Unit; Void; Int; Float; _⇒[_]_; μ; ν; K; Id; _⊕_; _⊗_)
import Once.Spec.Type as Ty
open import Once.Spec.Grade using (Many; mk-kind; eff; act; pure)
open import Once.Spec.Surface.Grammar using (module SigType; module AliasType; module Annot; TypeVar; tvar; NoExtra)
open import Once.Format.Print using (toPoly; toPolyF)

private
  written : (Extra : List Token → PolyType → List Token → Set) → TypeAlg PolyType PolyFunctor
  written X = record
    { aUnit = PUnit ; aVoid = PVoid ; aInt = PInt ; aFloat = PFloat
    ; aProd = _P*_ ; aSum = _P+_ ; aEff = PEff ; aAct = PAct
    ; aArrow = λ q A B → A P⇒[ q ] B ; aMu = Pμ ; aNu = λ f F → Pν F f
    ; fK = PK ; fId = PId ; fSum = _P⊕_ ; fProd = _P⊗_
    ; Extra = X }

  ground : TypeAlg Type (Fun 0)
  ground = record
    { aUnit = Unit ; aVoid = Void ; aInt = Int ; aFloat = Float
    ; aProd = Ty._*_ ; aSum = Ty._+_
    ; aEff = λ A B → A ⇒[ mk-kind Many eff ] B ; aAct = λ A B → A ⇒[ mk-kind Many act ] B
    ; aArrow = λ q A B → A ⇒[ mk-kind q pure ] B ; aMu = μ ; aNu = λ f F → ν F f
    ; fK = K ; fId = Id ; fSum = _⊕_ ; fProd = _⊗_
    ; Extra = NoExtra }

module SigA = TypeAnchors (written TypeVar) cT cF refl refl refl refl (λ _ _ → refl) (λ _ _ → refl) (λ _ _ → refl) (λ _ _ → refl)
  (λ _ _ _ → refl) (λ _ → refl) (λ _ → refl) (λ _ → refl) (λ _ → refl) refl (λ _ _ → refl) (λ _ _ → refl)
  (λ { (tvar {x} _) → seg-cast (+-identityʳ (wc x)) (seg-cons (TWord x) (λ ()) seg-nil) })

module AliasA = TypeAnchors (written NoExtra) cT cF refl refl refl refl (λ _ _ → refl) (λ _ _ → refl) (λ _ _ → refl) (λ _ _ → refl)
  (λ _ _ _ → refl) (λ _ → refl) (λ _ → refl) (λ _ → refl) (λ _ → refl) refl (λ _ _ → refl) (λ _ _ → refl)
  (λ ())

module AnnotA = TypeAnchors ground (λ A → cT (toPoly A)) (λ F → cF (toPolyF F)) refl refl refl refl
  (λ _ _ → refl) (λ _ _ → refl) (λ _ _ → refl) (λ _ _ → refl)
  (λ _ _ _ → refl) (λ _ → refl) (λ _ → refl) (λ _ → refl) (λ _ → refl) refl (λ _ _ → refl) (λ _ _ → refl)
  (λ ())

private
  -- the grammar's own type parsers are these
  sig-ty : ∀ {ts A r} → SigType.ParsesType ts A r → Seg (cT A) ts r
  sig-ty = SigA.ty

  alias-ty : ∀ {ts A r} → AliasType.ParsesType ts A r → Seg (cT A) ts r
  alias-ty = AliasA.ty

  annot-ty : ∀ {ts A r} → Annot.ParsesType ts A r → Seg (cT (toPoly A)) ts r
  annot-ty = AnnotA.ty

------------------------------------------------------------------------
-- Expressions
------------------------------------------------------------------------

open import Once.Spec.Surface.Lexing using (TAt; TDot; TComma; TColon; TLambda; TEquals; TLBrace; TRBrace;
  TSemicolon; TMinus; TPlus; TStar; TSlash; TPercent; TLt; TLe; TGt; TGe; TEqEq; TNeq; TBang)
open import Once.Spec.Surface.Syntax using (Expr; RVar; RQualified; RResolved; RApp; RLam; RLet; RPair; RDestruct;
  RUnit; RInt; RFloat; RAnnot; RBinOp; RNeg)
open import Once.Spec.Name using (canonical)
open import Once.Spec.Surface.Grammar using (ParsesExpr; ParsesCompTail; ParsesCmp; ParsesAdd; ParsesAddTail;
  ParsesMul; ParsesMulTail; ParsesUnary; ParsesApp; ParsesAppTail; ParsesAtomExpr; ParsesLamParams; ParsesParenCont;
  expr; comp-done; comp-dot; cmp-none; cmp; add; add-done; add-op; mul; mul-done; mul-op; neg; unary; app;
  app-done; app-arg; atom-unit; atom-int; atom-float; atom-var; atom-qual; atom-paren; atom-op; atom-lambda;
  atom-let; atom-destruct; lam-body; lam-arg; paren-close; paren-pair; paren-annot;
  CompareToken; ct-lt; ct-le; ct-gt; ct-ge; ct-eq; ct-ne; AddToken; at-plus; at-minus; MulToken; mt-star;
  mt-slash; mt-pct; ParsesOpChars; op-close; op-char; OpChar; oc-dot; oc-plus; oc-minus; oc-star; oc-slash;
  oc-pct; oc-lt; oc-gt; oc-pipe; oc-amp; oc-at)
open import Once.Format.Print using (isOperator)

-- | The anchors of an expression, as written.
cE : Expr → ℕ
cE (RVar x)                 = if isOperator x then 0 else wc x
cE (RQualified x a)         = wc x + wc a
cE (RResolved (canonical xs)) = foldr (λ x n → wc x + n) 0 xs
cE (RApp f a)               = cE f + cE a
cE (RLam x e)               = wc x + cE e
cE (RLet x v b)             = 2 + (wc x + (cE v + cE b))
cE (RPair a b)              = cE a + cE b
cE (RDestruct s x el y er)  = 4 + (wc x + (wc y + (cE s + (cE el + cE er))))
cE RUnit                    = 0
cE (RInt _)                 = 1
cE (RFloat _ _ _)           = 1
cE (RAnnot e T)             = cE e + cT (toPoly T)
cE (RBinOp op a b)          = cE a + cE b
cE (RNeg e)                 = cE e

-- | Words that are no operator names (what the lexer reads as words).
Good : Token → Set
Good (TWord x) = isOperator x ≡ false
{-# CATCHALL #-}
Good _         = ⊤

private
  good-rest : ∀ {n ts r} → All Good ts → Seg n ts r → All Good r
  good-rest g (seg , refl , _ , _) = AllP.++⁻ʳ seg g

  gtail : ∀ {t ts} → All Good (t ∷ ts) → All Good ts
  gtail (_ ∷ g) = g

  -- an operand with no operator before it
  tseg-arg : ∀ {base m n ts ts₂ r} → Seg m ts ts₂ → TSeg (base + m) n ts₂ r → TSeg base n ts r
  tseg-arg {base} {m} (s₁ , refl , e₁ , n₁) (s₂ , refl , e₂ , n₂) =
    s₁ ++ s₂ , sym (++-assoc s₁ s₂ _) ,
    trans (cong (base +_) (anchors-++ s₁ s₂))
      (trans (sym (+-assoc base (anchors s₁) (anchors s₂))) (trans (cong (λ x → base + x + anchors s₂) e₁) e₂)) ,
    AllP.++⁺ n₁ n₂

  ct-nl : ∀ {t op} → CompareToken t op → t ≢ TNewline
  ct-nl ct-lt () ; ct-nl ct-le () ; ct-nl ct-gt () ; ct-nl ct-ge () ; ct-nl ct-eq () ; ct-nl ct-ne ()
  ct-na : ∀ {t op} → CompareToken t op → (if anchorTok t then 1 else 0) ≡ 0
  ct-na ct-lt = refl ; ct-na ct-le = refl ; ct-na ct-gt = refl ; ct-na ct-ge = refl ; ct-na ct-eq = refl ; ct-na ct-ne = refl
  at-nl : ∀ {t op} → AddToken t op → t ≢ TNewline
  at-nl at-plus () ; at-nl at-minus ()
  at-na : ∀ {t op} → AddToken t op → (if anchorTok t then 1 else 0) ≡ 0
  at-na at-plus = refl ; at-na at-minus = refl
  mt-nl : ∀ {t op} → MulToken t op → t ≢ TNewline
  mt-nl mt-star () ; mt-nl mt-slash () ; mt-nl mt-pct ()
  mt-na : ∀ {t op} → MulToken t op → (if anchorTok t then 1 else 0) ≡ 0
  mt-na mt-star = refl ; mt-na mt-slash = refl ; mt-na mt-pct = refl

  -- an operator in parentheses: no anchor, and an operator name
  oc-nl : ∀ {t ch} → OpChar t ch → t ≢ TNewline
  oc-nl oc-dot () ; oc-nl oc-plus () ; oc-nl oc-minus () ; oc-nl oc-star () ; oc-nl oc-slash () ; oc-nl oc-pct ()
  oc-nl oc-lt () ; oc-nl oc-gt () ; oc-nl oc-pipe () ; oc-nl oc-amp () ; oc-nl oc-at ()
  oc-na : ∀ {t ch} → OpChar t ch → (if anchorTok t then 1 else 0) ≡ 0
  oc-na oc-dot = refl ; oc-na oc-plus = refl ; oc-na oc-minus = refl ; oc-na oc-star = refl ; oc-na oc-slash = refl
  oc-na oc-pct = refl ; oc-na oc-lt = refl ; oc-na oc-gt = refl ; oc-na oc-pipe = refl ; oc-na oc-amp = refl
  oc-na oc-at = refl

  opchars-seg : ∀ {ts cs s r} → ParsesOpChars ts cs s r → Seg 0 ts r
  opchars-seg op-close        = seg-cons TRParen (λ ()) seg-nil
  opchars-seg (op-char {t = t} oc p) = seg-cast (cong (_+ 0) (oc-na oc)) (seg-cons t (oc-nl oc) (opchars-seg p))

open import Data.Char using (Char)
open import Data.List using (_∷ʳ_)
open import Data.List.Properties using (unfold-reverse)
open import Data.Nat.Properties using (+-suc)
open import Data.String using (fromList; toList)
open import Once.Postulates using (toList∘fromList)
open import Once.Format.Proof.ExprBase using (OpName; op-isOperator)

private
  all-rev : ∀ {P : Char → Set} xs → All P xs → All P (reverse xs)
  all-rev []       []       = []
  all-rev (x ∷ xs) (p ∷ ps) = subst (All _) (sym (unfold-reverse x xs)) (AllP.++⁺ (all-rev xs ps) (p ∷ []))

  snoc-ne : ∀ {P : Char → Set} xs c → All P xs → P c → ∃[ d ] ∃[ ds ] (xs ∷ʳ c ≡ d ∷ ds × All P (d ∷ ds))
  snoc-ne []       c []       p = c , [] , refl , p ∷ []
  snoc-ne (x ∷ xs) c (q ∷ qs) p = x , xs ∷ʳ c , refl , q ∷ AllP.++⁺ qs (p ∷ [])

  -- the characters of a parenthesized operator make an operator name
  opchars-name : ∀ {ts cs s r} → ParsesOpChars ts cs s r → All (λ d → ∃[ t ] OpChar t d) cs → OpName s
  opchars-name (op-close {c} {cs}) (o ∷ os) =
    let (d , ds , eq , all) = snoc-ne (reverse cs) c (all-rev cs os) o
    in d , ds , trans (toList∘fromList _) (trans (unfold-reverse c cs) eq) , all
  opchars-name (op-char {t = t} oc p) os = opchars-name p ((t , oc) ∷ os)

  seg-tseg : ∀ {m n ts ts₁ r} → Seg m ts ts₁ → TSeg m n ts₁ r → Seg n ts r
  seg-tseg s t = tseg-arg {base = 0} s t

  -- a token that is no anchor between two segments
  seg-op : ∀ {m n t ts ts₁ r} → t ≢ TNewline → (if anchorTok t then 1 else 0) ≡ 0
         → Seg m ts (t ∷ ts₁) → Seg n ts₁ r → Seg (m + n) ts r
  seg-op {m} {n} nt na s₁ s₂ = seg-cast (cong (m +_) (cong (_+ n) na)) (seg-++ s₁ (seg-cons _ nt s₂))

  tseg-close : ∀ {base r} → TSeg base base (TRParen ∷ r) r
  tseg-close {base} = TRParen ∷ [] , refl , +-identityʳ base , (λ ()) ∷ []

  if-false : ∀ {b} (x : ℕ) → b ≡ false → x ≡ (if b then 0 else x)
  if-false x refl = refl

  if-true : ∀ {b} (x : ℕ) → b ≡ true → 0 ≡ (if b then 0 else x)
  if-true x refl = refl

  destruct-count : ∀ S X L Y R → suc (S + suc (suc (X + (L + suc (Y + (R + 0))))))
                                 ≡ 4 + (X + (Y + (S + (L + R))))
  destruct-count S X L Y R =
    cong suc (trans (+-suc S _) (cong suc (trans (+-suc S _) (cong suc
      (trans (cong (S +_) (trans (cong (X +_) (+-suc L _)) (+-suc X _))) (trans (+-suc S _) (cong suc
        (trans (cong (λ z → S + (X + (L + (Y + z)))) (+-identityʳ R))
          (trans (lc S X (L + (Y + R))) (cong (X +_) (trans (cong (S +_) (lc L Y R)) (lc S Y (L + R)))))))))))))
    where
      lc : ∀ a b c → a + (b + c) ≡ b + (a + c)
      lc a b c = trans (sym (+-assoc a b c)) (trans (cong (_+ c) (+-comm a b)) (+-assoc b a c))

  let-count : ∀ a b c → suc (a + (b + suc c)) ≡ 2 + (a + (b + c))
  let-count a b c = cong suc (trans (cong (a +_) (+-suc b c)) (+-suc a (b + c)))

mutual
  e-expr : ∀ {ts e r} → All Good ts → ParsesExpr ts e r → Seg (cE e) ts r
  e-expr g (expr c t) = let s = e-cmp g c in seg-tseg s (e-comp (good-rest g s) t)

  e-comp : ∀ {l ts e r} → All Good ts → ParsesCompTail l ts e r → TSeg (cE l) (cE e) ts r
  e-comp g (comp-done _)     = tseg-nil
  e-comp g₀ (comp-dot c t) =
    let g = gtail g₀ ; s = e-cmp g c in tseg-step TDot (λ ()) refl refl s (e-comp (good-rest g s) t)

  e-cmp : ∀ {ts e r} → All Good ts → ParsesCmp ts e r → Seg (cE e) ts r
  e-cmp g (cmp-none a _) = e-add g a
  e-cmp g (cmp ct a b)   = let s = e-add g a in seg-op (ct-nl ct) (ct-na ct) s (e-add (gtail (good-rest g s)) b)

  e-add : ∀ {ts e r} → All Good ts → ParsesAdd ts e r → Seg (cE e) ts r
  e-add g (add m t) = let s = e-mul g m in seg-tseg s (e-addT (good-rest g s) t)

  e-addT : ∀ {l ts e r} → All Good ts → ParsesAddTail l ts e r → TSeg (cE l) (cE e) ts r
  e-addT g (add-done _)        = tseg-nil
  e-addT g₀ (add-op at m t) =
    let g = gtail g₀ ; s = e-mul g m in tseg-step _ (at-nl at) (at-na at) refl s (e-addT (good-rest g s) t)

  e-mul : ∀ {ts e r} → All Good ts → ParsesMul ts e r → Seg (cE e) ts r
  e-mul g (mul u t) = let s = e-unary g u in seg-tseg s (e-mulT (good-rest g s) t)

  e-mulT : ∀ {l ts e r} → All Good ts → ParsesMulTail l ts e r → TSeg (cE l) (cE e) ts r
  e-mulT g (mul-done _)        = tseg-nil
  e-mulT g₀ (mul-op mt u t) =
    let g = gtail g₀ ; s = e-unary g u in tseg-step _ (mt-nl mt) (mt-na mt) refl s (e-mulT (good-rest g s) t)

  e-unary : ∀ {ts e r} → All Good ts → ParsesUnary ts e r → Seg (cE e) ts r
  e-unary g (neg u) = seg-cons TMinus (λ ()) (e-unary (gtail g) u)
  e-unary g (unary a)     = e-app g a

  e-app : ∀ {ts e r} → All Good ts → ParsesApp ts e r → Seg (cE e) ts r
  e-app g (app a t) = let s = e-atom g a in seg-tseg s (e-appT (good-rest g s) t)

  e-appT : ∀ {l ts e r} → All Good ts → ParsesAppTail l ts e r → TSeg (cE l) (cE e) ts r
  e-appT g (app-done _)    = tseg-nil
  e-appT g (app-arg _ a t) = let s = e-atom g a in tseg-arg s (e-appT (good-rest g s) t)

  e-atom : ∀ {ts e r} → All Good ts → ParsesAtomExpr ts e r → Seg (cE e) ts r
  e-atom g atom-unit = seg-cons TLParen (λ ()) (seg-cons TRParen (λ ()) seg-nil)
  e-atom g (atom-int {n}) = seg-cons (TInt n) (λ ()) seg-nil
  e-atom g (atom-float {i} {f} {l}) = seg-cons (TFloat i f l) (λ ()) seg-nil
  e-atom (gx ∷ _) (atom-var {x} _ _) =
    seg-cast (trans (+-identityʳ (wc x)) (if-false (wc x) gx)) (seg-cons (TWord x) (λ ()) seg-nil)
  e-atom g (atom-qual {x} {a} _) =
    seg-cast (cong (wc x +_) (+-identityʳ (wc a)))
      (seg-cons (TWord x) (λ ()) (seg-cons TAt (λ ()) (seg-cons (TWord a) (λ ()) seg-nil)))
  e-atom g₀ (atom-paren e p) =
    let g = gtail g₀ ; s = e-expr g e in seg-cons TLParen (λ ()) (seg-tseg s (e-paren (good-rest g s) p))
  e-atom g (atom-op {s = s} p) =
    seg-cast (if-true (wc s) (op-isOperator s (opchars-name p []))) (seg-cons TLParen (λ ()) (opchars-seg p))
  e-atom g (atom-lambda p) = seg-cons TLambda (λ ()) (e-lam (gtail g) p)
  e-atom g₀ (atom-let {x} {v = v} {b} pv pb) =
    let g = gtail (gtail (gtail g₀)) ; s = e-expr g pv
    in seg-cast (let-count (wc x) (cE v) (cE b))
         (seg-cons (TWord "let") (λ ()) (seg-cons (TWord x) (λ ()) (seg-cons TEquals (λ ())
           (seg-++ s (seg-cons (TWord "in") (λ ()) (e-expr (gtail (good-rest g s)) pb))))))
  e-atom g₀ (atom-destruct {s = sc} {x = x} {y = y} {el = el} {er = er} ps pl pr) =
    let g  = gtail g₀
        ss = e-expr g ps
        g₁ = gtail (gtail (gtail (gtail (gtail (good-rest g ss)))))
        sl = e-expr g₁ pl
        g₂ = gtail (gtail (gtail (gtail (good-rest g₁ sl))))
        sr = e-expr g₂ pr
    in seg-cast (destruct-count (cE sc) (wc x) (cE el) (wc y) (cE er))
         (seg-cons (TWord "destruct") (λ ()) (seg-++ ss
           (seg-cons (TWord "of") (λ ()) (seg-cons TLBrace (λ ()) (seg-cons (TWord "Left") (λ ())
             (seg-cons (TWord x) (λ ()) (seg-cons TArrow (λ ()) (seg-++ sl
               (seg-cons TSemicolon (λ ()) (seg-cons (TWord "Right") (λ ()) (seg-cons (TWord y) (λ ())
                 (seg-cons TArrow (λ ()) (seg-++ sr (seg-cons TRBrace (λ ()) seg-nil))))))))))))))

  e-lam : ∀ {ts e r} → All Good ts → ParsesLamParams ts e r → Seg (cE e) ts r
  e-lam (_ ∷ g) (lam-body e)    = seg-cons TArrow (λ ()) (e-expr g e)
  e-lam (_ ∷ g) (lam-arg {x} p) = seg-cons (TWord x) (λ ()) (e-lam g p)

  e-paren : ∀ {e ts e′ r} → All Good ts → ParsesParenCont e ts e′ r → TSeg (cE e) (cE e′) ts r
  e-paren g paren-close        = tseg-close
  e-paren g (paren-pair p)  = tseg-step TComma (λ ()) refl refl (e-expr (gtail g) p) tseg-close
  e-paren g (paren-annot A) = tseg-step TColon (λ ()) refl refl (annot-ty A) tseg-close

------------------------------------------------------------------------
-- Declarations
------------------------------------------------------------------------

open import Data.Maybe using (Maybe; just; nothing)
open import Once.Spec.Surface.Syntax using (Decl; DTypeSig; DFunDef; DSignature; DTypeAlias; DImport; Import; mkImport)
open import Once.Spec.Surface.Grammar using (ParsesDecl; ParsesDecls; SkipNewlines; ParsesOpAfter; ParsesFunDef;
  ParsesParams; ParsesTypeAlias; ParsesImport; ParsesModulePath; wrapLams;
  decl-import; decl-alias; decl-signature; decl-typesig; decl-fundef; decl-op; skip-nl; skip-done;
  decls-stop; decls-cons; op-sig; op-def; fundef; params-eq; params-cons; params-stop; params-none;
  alias-eq; alias-param; import-as; import-plain; path-cons; path-dotstop; path-end)

-- | The anchors of words.
sw : List String → ℕ
sw = foldr (λ x n → wc x + n) 0

-- | A name's anchors: a word is one, an operator in parentheses none.
nameC : String → ℕ
nameC x = if isOperator x then 0 else wc x

asC : Maybe String → ℕ
asC (just a) = 1 + wc a
asC nothing  = 0

-- | The anchors of a declaration, as written.
cD : Decl → ℕ
cD (DTypeSig x A)          = nameC x + cT A
cD (DFunDef x e)           = nameC x + cE e
cD (DSignature x A)        = 1 + (nameC x + cT A)
cD (DTypeAlias x ps A)     = 1 + (nameC x + (sw ps + cT A))
cD (DImport (mkImport p a)) = 1 + (sw p + asC a)

private
  sw-++ : ∀ xs ys → sw (xs ++ ys) ≡ sw xs + sw ys
  sw-++ []       ys = refl
  sw-++ (x ∷ xs) ys = trans (cong (wc x +_) (sw-++ xs ys)) (sym (+-assoc (wc x) (sw xs) (sw ys)))

  sw-rev : ∀ xs → sw (reverse xs) ≡ sw xs
  sw-rev []       = refl
  sw-rev (x ∷ xs) = trans (cong sw (unfold-reverse x xs))
    (trans (sw-++ (reverse xs) (x ∷ []))
      (trans (cong₂ _+_ (sw-rev xs) (+-identityʳ (wc x))) (+-comm (sw xs) (wc x))))

  cE-wrap : ∀ ps e → cE (wrapLams ps e) ≡ sw ps + cE e
  cE-wrap []       e = refl
  cE-wrap (x ∷ xs) e = trans (cong (wc x +_) (cE-wrap xs e)) (sym (+-assoc (wc x) (sw xs) (cE e)))

  tseg-cast : ∀ {base m n ts r} → m ≡ n → TSeg base m ts r → TSeg base n ts r
  tseg-cast refl t = t

  -- a token before a tail: its anchors join the base
  tseg-pre : ∀ {base n ts r} t → t ≢ TNewline → TSeg ((if anchorTok t then 1 else 0) + base) n ts r
           → TSeg base n (t ∷ ts) r
  tseg-pre {base} t nt (s , refl , e , nn) =
    t ∷ s , refl , trans (lc base (if anchorTok t then 1 else 0) (anchors s))
                     (trans (sym (+-assoc (if anchorTok t then 1 else 0) base (anchors s))) e) , nt ∷ nn
    where
      lc : ∀ a b c → a + (b + c) ≡ b + (a + c)
      lc a b c = trans (sym (+-assoc a b c)) (trans (cong (_+ c) (+-comm a b)) (+-assoc b a c))

  -- a name's anchors, as the grammar reads it
  Named : String → Decl → List Token → List Token → Set
  Named x d ts r = Σ ℕ λ m → cD d ≡ nameC x + m × Seg m ts r

  d-params : ∀ {ts ps r} → ParsesParams ts ps r → Seg (sw ps) ts r
  d-params (params-eq {x} _)  = seg-cons (TWord x) (λ ()) seg-nil
  d-params (params-cons {x} _ p) = seg-cons (TWord x) (λ ()) (d-params p)
  d-params (params-stop _ _)  = seg-nil
  d-params (params-none _)    = seg-nil

  d-fun : ∀ {x ts d r} → All Good ts → ParsesFunDef x ts d r → Named x d ts r
  d-fun g (fundef {ps = ps} {e = e} p pe) =
    let s = d-params p
    in cE (wrapLams ps e) , refl ,
       seg-cast (sym (cE-wrap ps e)) (seg-op (λ ()) refl s (e-expr (gtail (good-rest g s)) pe))

  d-after : ∀ {x ts d r} → All Good ts → ParsesOpAfter x ts d r → Named x d ts r
  d-after g (op-sig {A = A} p) = cT A , refl , seg-cons TColon (λ ()) (sig-ty p)
  d-after g (op-def _ p)       = d-fun g p

  d-alias : ∀ {x ps ts d r} → ParsesTypeAlias x ps ts d r
          → Σ (List String) λ qs → Σ PolyType λ A → d ≡ DTypeAlias x qs A × TSeg (sw ps) (sw qs + cT A) ts r
  d-alias (alias-eq {ps} {A = A} p) =
    reverse ps , A , refl , tseg-cast (cong (_+ cT A) (sym (sw-rev ps))) (tseg-step TEquals (λ ()) refl refl (alias-ty p) tseg-nil)
  d-alias (alias-param {p = p} q) with d-alias q
  ... | qs , A , eq , t = qs , A , eq , tseg-pre (TWord p) (λ ()) t

  d-path : ∀ {ts p r} → ParsesModulePath ts p r → Seg (sw p) ts r
  d-path (path-cons {x} q)    = seg-cons (TWord x) (λ ()) (seg-cons TDot (λ ()) (d-path q))
  d-path (path-dotstop {x} _) = seg-cons (TWord x) (λ ()) seg-nil
  d-path (path-end {x} _)     = seg-cons (TWord x) (λ ()) seg-nil

  d-import : ∀ {ts d r} → ParsesImport ts d r → Σ ℕ λ m → cD d ≡ 1 + m × Seg m ts r
  d-import (import-as {p = p} {a} q) =
    sw p + (1 + wc a) , refl ,
    seg-cast (cong (λ z → sw p + suc z) (+-identityʳ (wc a)))
      (seg-++ (d-path q) (seg-cons (TWord "as") (λ ()) (seg-cons (TWord a) (λ ()) seg-nil)))
  d-import (import-plain {p = p} q _) = sw p + 0 , refl , seg-cast (sym (+-identityʳ (sw p))) (d-path q)

-- | A declaration's tokens hold its anchors, and no line end.
decl-seg : ∀ {ts d r} → All Good ts → ParsesDecl ts d r → Seg (cD d) ts r
decl-seg g (decl-import p) with d-import p
... | m , eq , s = seg-cast (sym eq) (seg-cons (TWord "import") (λ ()) s)
decl-seg (_ ∷ gx ∷ _) (decl-alias {x} p) with d-alias p
... | qs , A , refl , t =
  seg-cast (cong (λ z → 1 + (z + (sw qs + cT A))) (if-false (wc x) gx))
    (seg-cons (TWord "type") (λ ()) (seg-cons (TWord x) (λ ()) t))
decl-seg (_ ∷ gx ∷ _) (decl-signature {x} {A = A} p) =
  seg-cast (cong (λ z → 1 + (z + cT A)) (if-false (wc x) gx))
    (seg-cons (TWord "signature") (λ ()) (seg-cons (TWord x) (λ ()) (seg-cons TColon (λ ()) (sig-ty p))))
decl-seg (gx ∷ _) (decl-typesig {x} {A = A} _ p _) =
  seg-cast (cong (_+ cT A) (if-false (wc x) gx)) (seg-cons (TWord x) (λ ()) (seg-cons TColon (λ ()) (sig-ty p)))
decl-seg (gx ∷ g) (decl-fundef {x} _ _ p) with d-fun g p
... | m , eq , s = seg-cast (trans (cong (_+ m) (if-false (wc x) gx)) (sym eq)) (seg-cons (TWord x) (λ ()) s)
decl-seg (_ ∷ g) (decl-op {x = x} p q) with d-after (good-rest g (opchars-seg p)) q
... | m , eq , s =
  seg-cast (trans (cong (_+ m) (if-true (wc x) (op-isOperator x (opchars-name p [])))) (sym eq))
    (seg-cons TLParen (λ ()) (seg-++ (opchars-seg p) s))

-- | Line ends only.
Nls : List Token → Set
Nls = All (_≡ TNewline)

-- | Declarations, one after the other: line ends, then a declaration's
-- tokens holding its anchors; at the end, line ends before the rest.
DeclSegs : List Decl → List Token → List Token → Set
DeclSegs []       ts r = Σ (List Token) λ nls → ts ≡ nls ++ r × Nls nls
DeclSegs (d ∷ ds) ts r = Σ (List Token) λ nls → Σ (List Token) λ mid → ts ≡ nls ++ mid × Nls nls ×
                           Σ (List Token) λ rest → Seg (cD d) mid rest × DeclSegs ds rest r

private
  skip-nls : ∀ {ts r} → SkipNewlines ts r → Σ (List Token) λ nls → ts ≡ nls ++ r × Nls nls
  skip-nls (skip-nl s) with skip-nls s
  ... | nls , refl , n = TNewline ∷ nls , refl , refl ∷ n
  skip-nls (skip-done _) = [] , refl , []

decls-segs : ∀ {ts ds r} → All Good ts → ParsesDecls ts ds r → DeclSegs ds ts r
decls-segs g (decls-stop s _) = skip-nls s
decls-segs g (decls-cons s p ps) with skip-nls s
... | nls , refl , n =
  let g₁ = AllP.++⁻ʳ nls g ; sd = decl-seg g₁ p
  in nls , _ , refl , n , _ , sd , decls-segs (good-rest g₁ sd) ps
