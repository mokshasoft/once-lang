-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Format.Proof.Types — a printed type reads back (plan 0.124 step 4.2).
--
-- For any algebra the Spec reads types into (`TypeAlg`): the tokens of a
-- type printed at a level parse, at that level, as the type's reading, when
-- what follows does not continue it. A sum and a product are read left to
-- right, so their left operand is read with what follows it (the tail
-- forms). `Mu`/`Nu` read their functor as far as it goes: bare only when no
-- `+`/`*` follows (`Greedy`).
------------------------------------------------------------------------

module Once.Format.Proof.Types where

open import Data.Bool using (Bool; true; false; _∨_; not)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.String using (String)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import Relation.Nullary using (¬_)

open import Once.Spec.Grade using (Quantity; Zero; One; Many; Finite; pureᶠ; actᶠ)
open import Once.Spec.Surface.Lexing using (Token; TWord; TLParen; TRParen; TArrow; TCaret0; TCaret1; TCaretW;
  TPlus; TStar)
open import Once.Spec.Surface.Syntax using (PolyType; PolyFunctor; PUnit; PVoid; PInt; PFloat; _P*_; _P+_; _P⇒[_]_;
  PAct; PEff; Pμ; Pν; PTVar; PK; PId; _P⊕_; _P⊗_)
open import Once.Spec.Surface.Grammar using (Starts; starts; GradeToken; g0; g1; gw; TypeAlg; module Types)
open import Once.Format.Doc using (toks)
open import Once.Format.Print using (pty; pfun; pfunArg)
open import Once.Format.Proof.Tokens using (word-toks)

-- What does not continue a product, a sum, an arrow.
ProdDone SumDone ArrowDone : List Token → Set
ProdDone r  = ¬ Starts r TStar
SumDone r   = ¬ Starts r TPlus
ArrowDone r = ¬ Starts r TArrow × ¬ Starts r TCaret0 × ¬ Starts r TCaret1 × ¬ Starts r TCaretW

-- A bare `Mu`/`Nu` (`b`) is followed by neither `+` nor `*`.
Greedy : Bool → List Token → Set
Greedy true  r = SumDone r × ProdDone r
Greedy false r = ⊤

greedy-paren : ∀ b {r} → Greedy b (TRParen ∷ r)
greedy-paren true  = (λ ()) , (λ ())
greedy-paren false = tt

greedy-∨f : ∀ b {r} → Greedy b r → Greedy (b ∨ false) r
greedy-∨f true  g = g
greedy-∨f false g = g

module Read {R RF : Set} (alg : TypeAlg R RF) (Var : String → Set) (var : String → R)
            (var-ok : ∀ {x r} → Var x → TypeAlg.Extra alg (TWord x ∷ r) (var x) r) where
  open TypeAlg alg
  open Types alg

  mutual
    -- | A type's reading in the algebra.
    ⟦_⟧ : PolyType → R
    ⟦ PUnit ⟧         = aUnit
    ⟦ PVoid ⟧         = aVoid
    ⟦ PInt ⟧          = aInt
    ⟦ PFloat ⟧        = aFloat
    ⟦ A P* B ⟧        = aProd ⟦ A ⟧ ⟦ B ⟧
    ⟦ A P+ B ⟧        = aSum ⟦ A ⟧ ⟦ B ⟧
    ⟦ A P⇒[ q ] B ⟧   = aArrow q ⟦ A ⟧ ⟦ B ⟧
    ⟦ PAct A B ⟧      = aAct ⟦ A ⟧ ⟦ B ⟧
    ⟦ PEff A B ⟧      = aEff ⟦ A ⟧ ⟦ B ⟧
    ⟦ Pμ F ⟧          = aMu ⟦ F ⟧F
    ⟦ Pν F φ ⟧        = aNu φ ⟦ F ⟧F
    ⟦ PTVar x ⟧       = var x

    ⟦_⟧F : PolyFunctor → RF
    ⟦ PK A ⟧F    = fK ⟦ A ⟧
    ⟦ PId ⟧F     = fId
    ⟦ F P⊕ G ⟧F  = fSum ⟦ F ⟧F ⟦ G ⟧F
    ⟦ F P⊗ G ⟧F  = fProd ⟦ F ⟧F ⟦ G ⟧F

  mutual
    -- | A type whose variables the algebra reads.
    WF : PolyType → Set
    WF PUnit         = ⊤
    WF PVoid         = ⊤
    WF PInt          = ⊤
    WF PFloat        = ⊤
    WF (A P* B)      = WF A × WF B
    WF (A P+ B)      = WF A × WF B
    WF (A P⇒[ q ] B) = WF A × WF B
    WF (PAct A B)    = WF A × WF B
    WF (PEff A B)    = WF A × WF B
    WF (Pμ F)        = WFF F
    WF (Pν F φ)      = WFF F
    WF (PTVar x)     = Var x

    WFF : PolyFunctor → Set
    WFF (PK A)   = WF A
    WFF PId      = ⊤
    WFF (F P⊕ G) = WFF F × WFF G
    WFF (F P⊗ G) = WFF F × WFF G

  private
    word-atom : ∀ s tv k {A r} → ParsesAtom (TWord s ∷ r) A r → ParsesAtom (toks (proj₁ (Once.Format.Print.word s tv k)) r) A r
    word-atom s tv k {A} {r} p = subst (λ ts → ParsesAtom ts A r) (sym (word-toks s tv k r)) p

    grade-tail : ∀ q {tv k l ts B r} → ParsesType ts B r
               → ParsesArrowTail l (toks (proj₁ (Once.Format.Print.grade q tv k)) ts) (aArrow q l B) r
    grade-tail Zero p = arrow-grade g0 p
    grade-tail One  p = arrow-grade g1 p
    grade-tail Many p = arrow p

    grade-stops : ∀ q {tv k ts} → let g = toks (proj₁ (Once.Format.Print.grade q tv k)) ts in SumDone g × ProdDone g
    grade-stops Zero = (λ ()) , (λ ())
    grade-stops One  = (λ ()) , (λ ())
    grade-stops Many = (λ ()) , (λ ())

  mutual
    -- | An atom (level 3).
    atom : ∀ P b tv k r → WF P → Greedy b r → ParsesAtom (toks (proj₁ (pty 3 b P tv k)) r) ⟦ P ⟧ r
    atom PUnit  b tv k r w g = word-atom "Unit" tv k a-unit
    atom PVoid  b tv k r w g = word-atom "Void" tv k a-void
    atom PInt   b tv k r w g = word-atom "Int" tv k a-int
    atom PFloat b tv k r w g = word-atom "Float" tv k a-float
    atom (PTVar x) b tv k r w g = word-atom x tv k (a-extra (var-ok w))
    atom (A P⇒[ q ] B) b tv k r (wa , wb) g =
      a-paren (arrowBody A q B (b ∨ true) tv k (TRParen ∷ r) wa wb (greedy-paren (b ∨ true)) ((λ ()) , (λ ()) , (λ ()) , (λ ())) (λ ()) (λ ()))
    atom (A P+ B) b tv k r (wa , wb) g =
      a-paren (type (sumBody A B (b ∨ true) tv k (TRParen ∷ r) wa wb (greedy-paren (b ∨ true)) (λ ()) (sum-done (λ ())))
                    (arrow-done (λ ()) (λ ()) (λ ()) (λ ())))
    atom (A P* B) b tv k r (wa , wb) g =
      a-paren (type (sum (prodBody A B (b ∨ true) tv k (TRParen ∷ r) wa wb (greedy-paren (b ∨ true)) (prod-done (λ ())))
                         (sum-done (λ ())))
                    (arrow-done (λ ()) (λ ()) (λ ()) (λ ())))
    atom (PEff A B) b tv k r (wa , wb) g =
      subst (λ ts → ParsesAtom ts _ r) (sym (word-toks "Eff" tv k _))
        (a-eff (atom A false tv _ _ wa tt) (atom B false tv _ r wb tt))
    atom (PAct A B) b tv k r (wa , wb) g =
      subst (λ ts → ParsesAtom ts _ r) (sym (word-toks "Act" tv k _))
        (a-act (atom A false tv _ _ wa tt) (atom B false tv _ r wb tt))
    atom (Pμ F) true  tv k r w (sd , pd) = muBody F tv k r w sd pd
    atom (Pμ F) false tv k r w g =
      a-paren (type (sum (prod (muBody F tv k (TRParen ∷ r) w (λ ()) (λ ())) (prod-done (λ ()))) (sum-done (λ ())))
                    (arrow-done (λ ()) (λ ()) (λ ()) (λ ())))
    atom (Pν F pureᶠ) true  tv k r w (sd , pd) = nuBody F tv k r w sd pd
    atom (Pν F pureᶠ) false tv k r w g =
      a-paren (type (sum (prod (nuBody F tv k (TRParen ∷ r) w (λ ()) (λ ())) (prod-done (λ ()))) (sum-done (λ ())))
                    (arrow-done (λ ()) (λ ()) (λ ()) (λ ())))
    atom (Pν F actᶠ) true  tv k r w g = nuActBody F tv k r w
    atom (Pν F actᶠ) false tv k r w g =
      a-paren (type (sum (prod (nuActBody F tv k (TRParen ∷ r) w) (prod-done (λ ()))) (sum-done (λ ())))
                    (arrow-done (λ ()) (λ ()) (λ ()) (λ ())))

    -- | A product (level 2), with what continues it.
    prod′ : ∀ P b tv k r {T r′} → WF P → Greedy b r → ParsesProdTail ⟦ P ⟧ r T r′
          → ParsesProd (toks (proj₁ (pty 2 b P tv k)) r) T r′
    prod′ (A P* B) b tv k r (wa , wb) g tl = prodBody A B (b ∨ false) tv k r wa wb (greedy-∨f b g) tl
    prod′ PUnit         b tv k r w g tl = prod (atom PUnit b tv k r w g) tl
    prod′ PVoid         b tv k r w g tl = prod (atom PVoid b tv k r w g) tl
    prod′ PInt          b tv k r w g tl = prod (atom PInt b tv k r w g) tl
    prod′ PFloat        b tv k r w g tl = prod (atom PFloat b tv k r w g) tl
    prod′ (PTVar x)     b tv k r w g tl = prod (atom (PTVar x) b tv k r w g) tl
    prod′ (A P⇒[ q ] B) b tv k r w g tl = prod (atom (A P⇒[ q ] B) b tv k r w g) tl
    prod′ (A P+ B)      b tv k r w g tl = prod (atom (A P+ B) b tv k r w g) tl
    prod′ (PEff A B)    b tv k r w g tl = prod (atom (PEff A B) b tv k r w g) tl
    prod′ (PAct A B)    b tv k r w g tl = prod (atom (PAct A B) b tv k r w g) tl
    prod′ (Pμ F)        b tv k r w g tl = prod (atom (Pμ F) b tv k r w g) tl
    prod′ (Pν F pureᶠ)      b tv k r w g tl = prod (atom (Pν F pureᶠ) b tv k r w g) tl
    prod′ (Pν F actᶠ)      b tv k r w g tl = prod (atom (Pν F actᶠ) b tv k r w g) tl

    -- | A sum (level 1), with what continues it.
    sum′ : ∀ P b tv k r {T r′} → WF P → Greedy b r → ProdDone r → ParsesSumTail ⟦ P ⟧ r T r′
         → ParsesSum (toks (proj₁ (pty 1 b P tv k)) r) T r′
    sum′ (A P+ B) b tv k r (wa , wb) g pd tl = sumBody A B (b ∨ false) tv k r wa wb (greedy-∨f b g) pd tl
    sum′ (A P* B)      b tv k r w g pd tl = sum (prod′ (A P* B) b tv k r w g (prod-done pd)) tl
    sum′ PUnit         b tv k r w g pd tl = sum (prod′ PUnit b tv k r w g (prod-done pd)) tl
    sum′ PVoid         b tv k r w g pd tl = sum (prod′ PVoid b tv k r w g (prod-done pd)) tl
    sum′ PInt          b tv k r w g pd tl = sum (prod′ PInt b tv k r w g (prod-done pd)) tl
    sum′ PFloat        b tv k r w g pd tl = sum (prod′ PFloat b tv k r w g (prod-done pd)) tl
    sum′ (PTVar x)     b tv k r w g pd tl = sum (prod′ (PTVar x) b tv k r w g (prod-done pd)) tl
    sum′ (A P⇒[ q ] B) b tv k r w g pd tl = sum (prod′ (A P⇒[ q ] B) b tv k r w g (prod-done pd)) tl
    sum′ (PEff A B)    b tv k r w g pd tl = sum (prod′ (PEff A B) b tv k r w g (prod-done pd)) tl
    sum′ (PAct A B)    b tv k r w g pd tl = sum (prod′ (PAct A B) b tv k r w g (prod-done pd)) tl
    sum′ (Pμ F)        b tv k r w g pd tl = sum (prod′ (Pμ F) b tv k r w g (prod-done pd)) tl
    sum′ (Pν F pureᶠ)      b tv k r w g pd tl = sum (prod′ (Pν F pureᶠ) b tv k r w g (prod-done pd)) tl
    sum′ (Pν F actᶠ)      b tv k r w g pd tl = sum (prod′ (Pν F actᶠ) b tv k r w g (prod-done pd)) tl

    -- | A type (level 0).
    type′ : ∀ P b tv k r → WF P → Greedy b r → ArrowDone r → SumDone r → ProdDone r
          → ParsesType (toks (proj₁ (pty 0 b P tv k)) r) ⟦ P ⟧ r
    type′ (A P⇒[ q ] B) b tv k r (wa , wb) g ad sd pd = arrowBody A q B (b ∨ false) tv k r wa wb (greedy-∨f b g) ad sd pd
    type′ (A P+ B)  b tv k r w g (a₁ , a₂ , a₃ , a₄) sd pd = type (sum′ (A P+ B) b tv k r w g pd (sum-done sd)) (arrow-done a₁ a₂ a₃ a₄)
    type′ (A P* B)  b tv k r w g (a₁ , a₂ , a₃ , a₄) sd pd = type (sum′ (A P* B) b tv k r w g pd (sum-done sd)) (arrow-done a₁ a₂ a₃ a₄)
    type′ PUnit     b tv k r w g (a₁ , a₂ , a₃ , a₄) sd pd = type (sum′ PUnit b tv k r w g pd (sum-done sd)) (arrow-done a₁ a₂ a₃ a₄)
    type′ PVoid     b tv k r w g (a₁ , a₂ , a₃ , a₄) sd pd = type (sum′ PVoid b tv k r w g pd (sum-done sd)) (arrow-done a₁ a₂ a₃ a₄)
    type′ PInt      b tv k r w g (a₁ , a₂ , a₃ , a₄) sd pd = type (sum′ PInt b tv k r w g pd (sum-done sd)) (arrow-done a₁ a₂ a₃ a₄)
    type′ PFloat    b tv k r w g (a₁ , a₂ , a₃ , a₄) sd pd = type (sum′ PFloat b tv k r w g pd (sum-done sd)) (arrow-done a₁ a₂ a₃ a₄)
    type′ (PTVar x) b tv k r w g (a₁ , a₂ , a₃ , a₄) sd pd = type (sum′ (PTVar x) b tv k r w g pd (sum-done sd)) (arrow-done a₁ a₂ a₃ a₄)
    type′ (PEff A B) b tv k r w g (a₁ , a₂ , a₃ , a₄) sd pd = type (sum′ (PEff A B) b tv k r w g pd (sum-done sd)) (arrow-done a₁ a₂ a₃ a₄)
    type′ (PAct A B) b tv k r w g (a₁ , a₂ , a₃ , a₄) sd pd = type (sum′ (PAct A B) b tv k r w g pd (sum-done sd)) (arrow-done a₁ a₂ a₃ a₄)
    type′ (Pμ F)    b tv k r w g (a₁ , a₂ , a₃ , a₄) sd pd = type (sum′ (Pμ F) b tv k r w g pd (sum-done sd)) (arrow-done a₁ a₂ a₃ a₄)
    type′ (Pν F pureᶠ)  b tv k r w g (a₁ , a₂ , a₃ , a₄) sd pd = type (sum′ (Pν F pureᶠ) b tv k r w g pd (sum-done sd)) (arrow-done a₁ a₂ a₃ a₄)
    type′ (Pν F actᶠ)  b tv k r w g (a₁ , a₂ , a₃ , a₄) sd pd = type (sum′ (Pν F actᶠ) b tv k r w g pd (sum-done sd)) (arrow-done a₁ a₂ a₃ a₄)

    -- The bodies, at their own level.
    arrowBody : ∀ A q B b′ tv k r → WF A → WF B → Greedy b′ r → ArrowDone r → SumDone r → ProdDone r
              → ParsesType (toks (proj₁ ((Once.Format.Print._⊕ᵈ_ (pty 1 true A)
                                          (Once.Format.Print._⊕ᵈ_ (Once.Format.Print.grade q)
                                            (Once.Format.Print._⊕ᵈ_ Once.Format.Print.␣ (pty 0 b′ B)))) tv k)) r)
                           (aArrow q ⟦ A ⟧ ⟦ B ⟧) r
    arrowBody A q B b′ tv k r wa wb g ad sd pd =
      type (sum′ A true tv k _ wa (grade-stops q) (proj₂ (grade-stops q)) (sum-done (proj₁ (grade-stops q))))
           (grade-tail q (type′ B b′ tv _ r wb g ad sd pd))

    sumBody : ∀ A B b′ tv k r {T r′} → WF A → WF B → Greedy b′ r → ProdDone r → ParsesSumTail (aSum ⟦ A ⟧ ⟦ B ⟧) r T r′
            → ParsesSum (toks (proj₁ ((Once.Format.Print._⊕ᵈ_ (pty 1 false A)
                                        (Once.Format.Print._⊕ᵈ_ (Once.Format.Print.infixOp TPlus) (pty 2 b′ B))) tv k)) r) T r′
    sumBody A B b′ tv k r wa wb g pd tl =
      sum′ A false tv k _ wa tt (λ ()) (sum-plus (prod′ B b′ tv _ r wb g (prod-done pd)) tl)

    prodBody : ∀ A B b′ tv k r {T r′} → WF A → WF B → Greedy b′ r → ParsesProdTail (aProd ⟦ A ⟧ ⟦ B ⟧) r T r′
             → ParsesProd (toks (proj₁ ((Once.Format.Print._⊕ᵈ_ (pty 2 false A)
                                         (Once.Format.Print._⊕ᵈ_ (Once.Format.Print.infixOp TStar) (pty 3 b′ B))) tv k)) r) T r′
    prodBody A B b′ tv k r wa wb g tl =
      prod′ A false tv k _ wa tt (prod-star (atom B b′ tv _ r wb g) tl)

    muBody : ∀ F tv k r → WFF F → SumDone r → ProdDone r
           → ParsesAtom (toks (proj₁ ((Once.Format.Print._⊕ᵈ_ (Once.Format.Print.word "Mu")
                                        (Once.Format.Print._⊕ᵈ_ Once.Format.Print.␣ (pfunArg F))) tv k)) r) (aMu ⟦ F ⟧F) r
    muBody F tv k r w sd pd = subst (λ ts → ParsesAtom ts _ r) (sym (word-toks "Mu" tv k _)) (a-mu (farg F tv _ r w sd pd))

    nuBody : ∀ F tv k r → WFF F → SumDone r → ProdDone r
           → ParsesAtom (toks (proj₁ ((Once.Format.Print._⊕ᵈ_ (Once.Format.Print.word "Nu")
                                        (Once.Format.Print._⊕ᵈ_ Once.Format.Print.␣ (pfunArg F))) tv k)) r) (aNu pureᶠ ⟦ F ⟧F) r
    nuBody F tv k r w sd pd = subst (λ ts → ParsesAtom ts _ r) (sym (word-toks "Nu" tv k _)) (a-nu (farg F tv _ r w sd pd))

    nuActBody : ∀ F tv k r → WFF F
              → ParsesAtom (toks (proj₁ (pty 3 true (Pν F actᶠ) tv k)) r) (aNu actᶠ ⟦ F ⟧F) r
    nuActBody F tv k r w =
      subst (λ ts → ParsesAtom ts _ r) (sym (word-toks "Nu" tv k _))
        (subst (λ ts → ParsesAtom (TWord "Nu" ∷ TLParen ∷ ts) _ r) (sym (word-toks "Act" tv _ _))
          (a-nu-act (fsum′ F tv _ (TRParen ∷ r) w (λ ()) (fsum-done (λ ())))))

    -- | A functor: an atom (level 2), a product (1), a sum (0); the
    -- argument of `Mu`/`Nu`.
    fatom : ∀ F tv k r → WFF F → ParsesFunAtom (toks (proj₁ (pfun 2 F tv k)) r) ⟦ F ⟧F r
    fatom PId tv k r w = subst (λ ts → ParsesFunAtom ts _ r) (sym (word-toks "Id" tv k r)) f-id
    fatom (PK A) tv k r w =
      f-paren (fsum (fprod (kBody A tv k (TRParen ∷ r) w) (fprod-done (λ ()))) (fsum-done (λ ())))
    fatom (F P⊕ G) tv k r (wf , wg) = f-paren (fsumBody F G tv k (TRParen ∷ r) wf wg (λ ()) (fsum-done (λ ())))
    fatom (F P⊗ G) tv k r (wf , wg) =
      f-paren (fsum (fprodBody F G tv k (TRParen ∷ r) wf wg (fprod-done (λ ()))) (fsum-done (λ ())))

    fprod′ : ∀ F tv k r {G r′} → WFF F → ParsesFunProdTail ⟦ F ⟧F r G r′ → ParsesFunProd (toks (proj₁ (pfun 1 F tv k)) r) G r′
    fprod′ PId      tv k r w tl = fprod (fatom PId tv k r w) tl
    fprod′ (PK A)   tv k r w tl = fprod (kBody A tv k r w) tl
    fprod′ (F P⊕ G) tv k r w tl = fprod (fatom (F P⊕ G) tv k r w) tl
    fprod′ (F P⊗ G) tv k r (wf , wg) tl = fprodBody F G tv k r wf wg tl

    fsum′ : ∀ F tv k r {G r′} → WFF F → ProdDone r → ParsesFunSumTail ⟦ F ⟧F r G r′
          → ParsesFunSum (toks (proj₁ (pfun 0 F tv k)) r) G r′
    fsum′ PId      tv k r w pd tl = fsum (fprod′ PId tv k r w (fprod-done pd)) tl
    fsum′ (PK A)   tv k r w pd tl = fsum (fprod′ (PK A) tv k r w (fprod-done pd)) tl
    fsum′ (F P⊕ G) tv k r (wf , wg) pd tl = fsumBody F G tv k r wf wg pd tl
    fsum′ (F P⊗ G) tv k r w pd tl = fsum (fprod′ (F P⊗ G) tv k r w (fprod-done pd)) tl

    farg : ∀ F tv k r → WFF F → SumDone r → ProdDone r → ParsesFunSum (toks (proj₁ (pfunArg F tv k)) r) ⟦ F ⟧F r
    farg PId tv k r w sd pd = fsum (fprod′ PId tv k r w (fprod-done pd)) (fsum-done sd)
    farg (PK A) tv k r w sd pd =
      fsum (fprod (f-paren (fsum′ (PK A) tv k (TRParen ∷ r) w (λ ()) (fsum-done (λ ())))) (fprod-done pd)) (fsum-done sd)
    farg (F P⊕ G) tv k r w sd pd =
      fsum (fprod (f-paren (fsum′ (F P⊕ G) tv k (TRParen ∷ r) w (λ ()) (fsum-done (λ ())))) (fprod-done pd)) (fsum-done sd)
    farg (F P⊗ G) tv k r w sd pd =
      fsum (fprod (f-paren (fsum′ (F P⊗ G) tv k (TRParen ∷ r) w (λ ()) (fsum-done (λ ())))) (fprod-done pd)) (fsum-done sd)

    kBody : ∀ A tv k r → WF A
          → ParsesFunAtom (toks (proj₁ ((Once.Format.Print._⊕ᵈ_ (Once.Format.Print.word "K")
                                          (Once.Format.Print._⊕ᵈ_ Once.Format.Print.␣ (pty 3 false A))) tv k)) r) (fK ⟦ A ⟧) r
    kBody A tv k r w = subst (λ ts → ParsesFunAtom ts _ r) (sym (word-toks "K" tv k _)) (f-k (atom A false tv _ r w tt))

    fsumBody : ∀ F G tv k r {H r′} → WFF F → WFF G → ProdDone r → ParsesFunSumTail (fSum ⟦ F ⟧F ⟦ G ⟧F) r H r′
             → ParsesFunSum (toks (proj₁ ((Once.Format.Print._⊕ᵈ_ (pfun 0 F)
                                           (Once.Format.Print._⊕ᵈ_ (Once.Format.Print.infixOp TPlus) (pfun 1 G))) tv k)) r) H r′
    fsumBody F G tv k r wf wg pd tl = fsum′ F tv k _ wf (λ ()) (fsum-plus (fprod′ G tv _ r wg (fprod-done pd)) tl)

    fprodBody : ∀ F G tv k r {H r′} → WFF F → WFF G → ParsesFunProdTail (fProd ⟦ F ⟧F ⟦ G ⟧F) r H r′
              → ParsesFunProd (toks (proj₁ ((Once.Format.Print._⊕ᵈ_ (pfun 1 F)
                                            (Once.Format.Print._⊕ᵈ_ (Once.Format.Print.infixOp TStar) (pfun 2 G))) tv k)) r) H r′
    fprodBody F G tv k r wf wg tl = fprod′ F tv k _ wf (fprod-star (fatom G tv _ r wg) tl)
