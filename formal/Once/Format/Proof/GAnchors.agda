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
