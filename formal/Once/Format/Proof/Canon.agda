-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Format.Proof.Canon — without comments, the layout is the module's
-- alone (plan 0.124 step 4.5, canonicity).
--
-- The printer reads the trivia only at its anchors (their comments) and
-- before a declaration (the notes that stand there). A text without comments
-- leaves only blank lines in its trivia (`Quiet`): no anchor has a comment,
-- and blank lines alone print as nothing. So two texts without comments that
-- parse as the same module are formatted alike, whatever their whitespace and
-- blank lines (`format-canonical`).
--
-- Generated in part by `scripts/gen-format-canon.py`: edit the generator, not
-- this file.
------------------------------------------------------------------------

module Once.Format.Proof.Canon where

open import Data.Bool using (Bool; true; false; not; _∧_; _∨_; if_then_else_)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
import Data.List.Relation.Unary.All.Properties as AllP
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _<ᵇ_; _≡ᵇ_; _∸_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.String using (String; toList)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)

open import Once.Spec.Grade using (Quantity; Zero; One; Many; pureᶠ; actᶠ)
open import Once.Spec.Surface.Syntax
open import Once.Spec.Name using (canonical)
open import Once.Spec.Surface.Lexing using (Token; TWord; TInt; TFloat; TNewline; TEOF)
open import Once.Parser using (parseStrict)
open import Once.Format using (formatSource; formatParsed)
open import Once.Format.Doc using (Doc; empty; indent; render)
open import Once.Format.Lex using (Item; tok; comment; cont; lexItems)
open import Once.Format.Print
import Once.Format.Proof.Walk

------------------------------------------------------------------------
-- Quiet trivia: no comments
------------------------------------------------------------------------

-- | No anchor has a comment; what stands before a declaration is blank lines.
Quiet : Trivia → Set
Quiet tv = ∀ k → Notes.inner (lookupNotes k tv) ≡ [] × Notes.after (lookupNotes k tv) ≡ []
             × All (_≡ note-blank) (Notes.top (lookupNotes k tv))

module Same (tv : Trivia) (q : Quiet tv) where

  -- | A printer that prints alike with the trivia and without.
  record Ind (m : P Doc) : Set where
    constructor ind
    field
      same : ∀ k → m tv k ≡ m [] k

  ind-bind : ∀ {A B : Set} {m : P A} {f : A → P B} → (∀ k → m tv k ≡ m [] k) → (∀ x k → f x tv k ≡ f x [] k)
           → ∀ k → (m >>=′ f) tv k ≡ (m >>=′ f) [] k
  ind-bind {f = f} em ef k = trans (cong (λ p → f (proj₁ p) tv (proj₂ p)) (em k)) (ef _ _)

  ind-⊕ : ∀ {a b} → Ind a → Ind b → Ind (a ⊕ᵈ b)
  ind-⊕ {a} {b} (ind ea) (ind eb) =
    ind (ind-bind {m = a} {f = λ x → b >>=′ λ y → pure′ (x Doc.<> y)} ea
          (λ x → ind-bind {m = b} {f = λ y → pure′ (x Doc.<> y)} eb (λ y k → refl)))

  infixr 6 _⊕ⁱ_
  _⊕ⁱ_ : ∀ {a b} → Ind a → Ind b → Ind (a ⊕ᵈ b)
  _⊕ⁱ_ = ind-⊕

  ind-pure : ∀ {d} → Ind (pure′ d)
  ind-pure = ind (λ k → refl)

  ind-gn : ∀ {m} → Ind m → Ind (m >>=′ λ d → pure′ (Doc.group (Doc.nest indent d)))
  ind-gn {m} (ind e) = ind (ind-bind {m = m} {f = λ d → pure′ (Doc.group (Doc.nest indent d))} e (λ x k → refl))

  ind-g : ∀ {m} → Ind m → Ind (m >>=′ λ d → pure′ (Doc.group d))
  ind-g {m} (ind e) = ind (ind-bind {m = m} {f = λ d → pure′ (Doc.group d)} e (λ x k → refl))

  ind-n : ∀ {m} → Ind m → Ind (m >>=′ λ d → pure′ (Doc.nest indent d))
  ind-n {m} (ind e) = ind (ind-bind {m = m} {f = λ d → pure′ (Doc.nest indent d)} e (λ x k → refl))

  ind-paren : ∀ b {d} → Ind d → Ind (paren b d)
  ind-paren true  i = ind-pure ⊕ⁱ i ⊕ⁱ ind-pure
  ind-paren false i = i

  ind-if : ∀ b {x y} → Ind x → Ind y → Ind (if b then x else y)
  ind-if true  ix iy = ix
  ind-if false ix iy = iy

  ind-anchor : ∀ x → Ind (anchor x)
  ind-anchor x = ind λ k →
    cong₂ (λ i a → (inners i Doc.<> Doc.tk x Doc.<> eols a) , suc k) (proj₁ (q k)) (proj₁ (proj₂ (q k)))

  ind-word : ∀ s → Ind (word s)
  ind-word s with s Data.String.== "compose"
  ... | true  = ind-pure
  ... | false = ind-anchor (TWord s)

  ind-opToks : ∀ cs → Ind (opToks cs)
  ind-opToks []           = ind-pure
  ind-opToks (c ∷ [])     = opTok1′ (opToken c)
    where
      opTok1′ : ∀ m → Ind (opTok1 m)
      opTok1′ (just x) = ind-pure
      opTok1′ nothing  = ind-pure
  ind-opToks (c ∷ d ∷ cs) = opTok1′ (opToken c) ⊕ⁱ ind-pure ⊕ⁱ ind-opToks (d ∷ cs)
    where
      opTok1′ : ∀ m → Ind (opTok1 m)
      opTok1′ (just x) = ind-pure
      opTok1′ nothing  = ind-pure

  ind-name : ∀ x → Ind (name x)
  ind-name x = ind-if (isOperator x) (ind-pure ⊕ⁱ ind-opToks (toList x) ⊕ⁱ ind-pure) (ind-word x)

  ind-grade : ∀ q → Ind (grade q)
  ind-grade Zero = ind-pure ⊕ⁱ ind-pure ⊕ⁱ ind-pure ⊕ⁱ ind-pure
  ind-grade One  = ind-pure ⊕ⁱ ind-pure ⊕ⁱ ind-pure ⊕ⁱ ind-pure
  ind-grade Many = ind-pure ⊕ⁱ ind-pure

  ind-infix : ∀ x → Ind (infixOp x)
  ind-infix x = ind-pure ⊕ⁱ ind-pure ⊕ⁱ ind-pure

  mutual
    ind-ty : ∀ l b P → Ind (pty l b P)
    ind-ty l b PUnit = ind-word "Unit"
    ind-ty l b PVoid = ind-word "Void"
    ind-ty l b PInt = ind-word "Int"
    ind-ty l b PFloat = ind-word "Float"
    ind-ty l b (PTVar x) = ind-word x
    ind-ty l b (A P⇒[ q ] B) = ind-paren (0 <ᵇ l) (ind-ty 1 true A ⊕ⁱ ind-grade q ⊕ⁱ ind-pure ⊕ⁱ ind-ty 0 (b ∨ (0 <ᵇ l)) B)
    ind-ty l b (A P+ B) = ind-paren (1 <ᵇ l) (ind-ty 1 false A ⊕ⁱ ind-infix _ ⊕ⁱ ind-ty 2 (b ∨ (1 <ᵇ l)) B)
    ind-ty l b (A P* B) = ind-paren (2 <ᵇ l) (ind-ty 2 false A ⊕ⁱ ind-infix _ ⊕ⁱ ind-ty 3 (b ∨ (2 <ᵇ l)) B)
    ind-ty l b (PEff A B) = ind-paren (3 <ᵇ l) (ind-word "Eff" ⊕ⁱ ind-pure ⊕ⁱ ind-ty 3 false A ⊕ⁱ ind-pure ⊕ⁱ ind-ty 3 false B)
    ind-ty l b (PAct A B) = ind-paren (3 <ᵇ l) (ind-word "Act" ⊕ⁱ ind-pure ⊕ⁱ ind-ty 3 false A ⊕ⁱ ind-pure ⊕ⁱ ind-ty 3 false B)
    ind-ty l b (Pμ F) = ind-paren (not b) (ind-word "Mu" ⊕ⁱ ind-pure ⊕ⁱ ind-arg F)
    ind-ty l b (Pν F pureᶠ) = ind-paren (not b) (ind-word "Nu" ⊕ⁱ ind-pure ⊕ⁱ ind-arg F)
    ind-ty l b (Pν F actᶠ) =
      ind-paren (not b) (ind-word "Nu" ⊕ⁱ ind-pure ⊕ⁱ ind-pure ⊕ⁱ ind-word "Act" ⊕ⁱ ind-pure ⊕ⁱ ind-fun 0 F ⊕ⁱ ind-pure)

    ind-arg : ∀ F → Ind (pfunArg F)
    ind-arg PId = ind-word "Id"
    ind-arg (PK A) = ind-pure ⊕ⁱ ind-fun 0 (PK A) ⊕ⁱ ind-pure
    ind-arg (F P⊕ G) = ind-pure ⊕ⁱ ind-fun 0 (F P⊕ G) ⊕ⁱ ind-pure
    ind-arg (F P⊗ G) = ind-pure ⊕ⁱ ind-fun 0 (F P⊗ G) ⊕ⁱ ind-pure

    ind-fun : ∀ l F → Ind (pfun l F)
    ind-fun l PId = ind-word "Id"
    ind-fun l (PK A) = ind-paren (1 <ᵇ l) (ind-word "K" ⊕ⁱ ind-pure ⊕ⁱ ind-ty 3 false A)
    ind-fun l (F P⊕ G) = ind-paren (0 <ᵇ l) (ind-fun 0 F ⊕ⁱ ind-infix _ ⊕ⁱ ind-fun 1 G)
    ind-fun l (F P⊗ G) = ind-paren (1 <ᵇ l) (ind-fun 1 F ⊕ⁱ ind-infix _ ⊕ⁱ ind-fun 2 G)

  mutual
    ind-ex : ∀ l wh e → Ind (pex l wh e)
    ind-ex l wh (RVar x) = ind-name x
    ind-ex l wh (RQualified x q) = ind-word x ⊕ⁱ ind-pure ⊕ⁱ ind-word q
    ind-ex l wh (RResolved (canonical xs)) = ind-dotted xs
    ind-ex l wh (RApp f a) = ind-comp l (isCompose (headOf f)) f a
    ind-ex l wh (RLam x e) = ind-paren (not wh) (ind-g (ind-pure ⊕ⁱ ind-word x ⊕ⁱ ind-lam e))
    ind-ex l wh (RLet x v b) = ind-paren (not wh) (ind-g (ind-let x v b))
    ind-ex l wh (RPair a b) =
      ind-gn (ind-pure ⊕ⁱ ind-ex 0 true a ⊕ⁱ ind-pure ⊕ⁱ ind-pure ⊕ⁱ ind-ex 0 true b ⊕ⁱ ind-pure)
    ind-ex l wh (RDestruct s x el y er) =
      ind-paren (not wh) (ind-g (ind-word "destruct" ⊕ⁱ ind-pure ⊕ⁱ ind-ex 0 true s ⊕ⁱ ind-pure ⊕ⁱ ind-word "of"
        ⊕ⁱ ind-n (ind-pure ⊕ⁱ ind-pure ⊕ⁱ ind-pure ⊕ⁱ ind-word "Left" ⊕ⁱ ind-pure ⊕ⁱ ind-word x ⊕ⁱ ind-infix _
            ⊕ⁱ ind-ex 0 true el ⊕ⁱ ind-pure ⊕ⁱ ind-pure ⊕ⁱ ind-pure ⊕ⁱ ind-word "Right" ⊕ⁱ ind-pure ⊕ⁱ ind-word y
            ⊕ⁱ ind-infix _ ⊕ⁱ ind-ex 0 true er ⊕ⁱ ind-pure ⊕ⁱ ind-pure)))
    ind-ex l wh RUnit = ind-pure ⊕ⁱ ind-pure
    ind-ex l wh (RInt z) = ind-anchor (TInt z)
    ind-ex l wh (RFloat i f n) = ind-anchor (TFloat i f n)
    ind-ex l wh (RAnnot e T) = ind-pure ⊕ⁱ ind-ex 0 true e ⊕ⁱ ind-infix _ ⊕ⁱ ind-ty 0 true (toPoly T) ⊕ⁱ ind-pure
    ind-ex l wh (RBinOp op a b) = ind-gn (ind-paren (opLevel op <ᵇ l) (ind-bin (opLevel op) op a b))
    ind-ex l wh (RNeg e) = ind-paren (4 <ᵇ l) (ind-pure ⊕ⁱ ind-pure ⊕ⁱ ind-ex 4 false e)

    ind-dotted : ∀ xs → Ind (dotted xs)
    ind-dotted [] = ind-pure
    ind-dotted (x ∷ []) = ind-word x
    ind-dotted (x ∷ y ∷ ys) = ind-word x ⊕ⁱ ind-pure ⊕ⁱ ind-dotted (y ∷ ys)

    ind-comp : ∀ l b f a → Ind (pcomp l b f a)
    ind-comp l true (RVar ux) a = ind-gn (ind-paren (5 <ᵇ l) (ind-spine (RVar ux) ⊕ⁱ ind-pure ⊕ⁱ ind-ex 6 false a))
    ind-comp l true (RQualified ux uq) a = ind-gn (ind-paren (5 <ᵇ l) (ind-spine (RQualified ux uq) ⊕ⁱ ind-pure ⊕ⁱ ind-ex 6 false a))
    ind-comp l true (RResolved un) a = ind-gn (ind-paren (5 <ᵇ l) (ind-spine (RResolved un) ⊕ⁱ ind-pure ⊕ⁱ ind-ex 6 false a))
    ind-comp l true (RApp c g) h = ind-compose l g h
    ind-comp l true (RLam ux ue) a = ind-gn (ind-paren (5 <ᵇ l) (ind-spine (RLam ux ue) ⊕ⁱ ind-pure ⊕ⁱ ind-ex 6 false a))
    ind-comp l true (RLet ux uv ub) a = ind-gn (ind-paren (5 <ᵇ l) (ind-spine (RLet ux uv ub) ⊕ⁱ ind-pure ⊕ⁱ ind-ex 6 false a))
    ind-comp l true (RPair ua ub) a = ind-gn (ind-paren (5 <ᵇ l) (ind-spine (RPair ua ub) ⊕ⁱ ind-pure ⊕ⁱ ind-ex 6 false a))
    ind-comp l true (RDestruct us ux uel uy uer) a = ind-gn (ind-paren (5 <ᵇ l) (ind-spine (RDestruct us ux uel uy uer) ⊕ⁱ ind-pure ⊕ⁱ ind-ex 6 false a))
    ind-comp l true RUnit a = ind-gn (ind-paren (5 <ᵇ l) (ind-spine RUnit ⊕ⁱ ind-pure ⊕ⁱ ind-ex 6 false a))
    ind-comp l true (RInt uz) a = ind-gn (ind-paren (5 <ᵇ l) (ind-spine (RInt uz) ⊕ⁱ ind-pure ⊕ⁱ ind-ex 6 false a))
    ind-comp l true (RFloat ui ufr ul) a = ind-gn (ind-paren (5 <ᵇ l) (ind-spine (RFloat ui ufr ul) ⊕ⁱ ind-pure ⊕ⁱ ind-ex 6 false a))
    ind-comp l true (RAnnot ue uT) a = ind-gn (ind-paren (5 <ᵇ l) (ind-spine (RAnnot ue uT) ⊕ⁱ ind-pure ⊕ⁱ ind-ex 6 false a))
    ind-comp l true (RBinOp uop ua ub) a = ind-gn (ind-paren (5 <ᵇ l) (ind-spine (RBinOp uop ua ub) ⊕ⁱ ind-pure ⊕ⁱ ind-ex 6 false a))
    ind-comp l true (RNeg ue) a = ind-gn (ind-paren (5 <ᵇ l) (ind-spine (RNeg ue) ⊕ⁱ ind-pure ⊕ⁱ ind-ex 6 false a))
    ind-comp l false f a = ind-gn (ind-paren (5 <ᵇ l) (ind-spine f ⊕ⁱ ind-pure ⊕ⁱ ind-ex 6 false a))

    ind-compose : ∀ l g h → Ind (pcompose l g h)
    ind-compose l g h = ind-gn (ind-paren (0 <ᵇ l) (ind-chain g ⊕ⁱ (ind-pure ⊕ⁱ ind-pure ⊕ⁱ ind-pure) ⊕ⁱ ind-ex 1 false h))

    ind-chain : ∀ g → Ind (pchainC g)
    ind-chain (RApp f h) = ind-chain′ (isCompose (headOf f)) f h
    ind-chain (RVar x) = ind-ex 1 false (RVar x)
    ind-chain (RQualified x q) = ind-ex 1 false (RQualified x q)
    ind-chain (RResolved n) = ind-ex 1 false (RResolved n)
    ind-chain (RLam x e) = ind-ex 1 false (RLam x e)
    ind-chain (RLet x v b) = ind-ex 1 false (RLet x v b)
    ind-chain (RPair a b) = ind-ex 1 false (RPair a b)
    ind-chain (RDestruct s x el y er) = ind-ex 1 false (RDestruct s x el y er)
    ind-chain RUnit = ind-ex 1 false RUnit
    ind-chain (RInt z) = ind-ex 1 false (RInt z)
    ind-chain (RFloat i fr l) = ind-ex 1 false (RFloat i fr l)
    ind-chain (RAnnot e T) = ind-ex 1 false (RAnnot e T)
    ind-chain (RBinOp op a b) = ind-ex 1 false (RBinOp op a b)
    ind-chain (RNeg e) = ind-ex 1 false (RNeg e)

    ind-chain′ : ∀ b f h → Ind (pchainC′ b f h)
    ind-chain′ true (RVar ux) h = ind-comp 0 false (RVar ux) h
    ind-chain′ true (RQualified ux uq) h = ind-comp 0 false (RQualified ux uq) h
    ind-chain′ true (RResolved un) h = ind-comp 0 false (RResolved un) h
    ind-chain′ true (RApp c g) h = ind-chain g ⊕ⁱ (ind-pure ⊕ⁱ ind-pure ⊕ⁱ ind-pure) ⊕ⁱ ind-ex 1 false h
    ind-chain′ true (RLam ux ue) h = ind-comp 0 false (RLam ux ue) h
    ind-chain′ true (RLet ux uv ub) h = ind-comp 0 false (RLet ux uv ub) h
    ind-chain′ true (RPair ua ub) h = ind-comp 0 false (RPair ua ub) h
    ind-chain′ true (RDestruct us ux uel uy uer) h = ind-comp 0 false (RDestruct us ux uel uy uer) h
    ind-chain′ true RUnit h = ind-comp 0 false RUnit h
    ind-chain′ true (RInt uz) h = ind-comp 0 false (RInt uz) h
    ind-chain′ true (RFloat ui ufr ul) h = ind-comp 0 false (RFloat ui ufr ul) h
    ind-chain′ true (RAnnot ue uT) h = ind-comp 0 false (RAnnot ue uT) h
    ind-chain′ true (RBinOp uop ua ub) h = ind-comp 0 false (RBinOp uop ua ub) h
    ind-chain′ true (RNeg ue) h = ind-comp 0 false (RNeg ue) h
    ind-chain′ false f h = ind-comp 0 false f h

    ind-bin : ∀ lv op a b → Ind (pbin lv op a b)
    ind-bin lv op a b = ind-left lv a ⊕ⁱ ind-pure ⊕ⁱ ind-pure ⊕ⁱ ind-pure ⊕ⁱ ind-ex (suc lv) false b

    ind-left : ∀ lv a → Ind (pleft lv a)
    ind-left lv (RBinOp op x y) = ind-if ((lv ≡ᵇ opLevel op) ∧ (1 <ᵇ lv)) (ind-bin lv op x y) (ind-ex (leftLevel lv) false (RBinOp op x y))
    ind-left lv (RVar x) = ind-ex (leftLevel lv) false (RVar x)
    ind-left lv (RQualified x q) = ind-ex (leftLevel lv) false (RQualified x q)
    ind-left lv (RResolved n) = ind-ex (leftLevel lv) false (RResolved n)
    ind-left lv (RApp f a) = ind-ex (leftLevel lv) false (RApp f a)
    ind-left lv (RLam x e) = ind-ex (leftLevel lv) false (RLam x e)
    ind-left lv (RLet x v b) = ind-ex (leftLevel lv) false (RLet x v b)
    ind-left lv (RPair a b) = ind-ex (leftLevel lv) false (RPair a b)
    ind-left lv (RDestruct s x el y er) = ind-ex (leftLevel lv) false (RDestruct s x el y er)
    ind-left lv RUnit = ind-ex (leftLevel lv) false RUnit
    ind-left lv (RInt z) = ind-ex (leftLevel lv) false (RInt z)
    ind-left lv (RFloat i fr l) = ind-ex (leftLevel lv) false (RFloat i fr l)
    ind-left lv (RAnnot e T) = ind-ex (leftLevel lv) false (RAnnot e T)
    ind-left lv (RNeg e) = ind-ex (leftLevel lv) false (RNeg e)

    ind-spine : ∀ f → Ind (pspine f)
    ind-spine (RApp f a) = ind-spine′ (isCompose (headOf f)) f a
    ind-spine (RVar x) = ind-ex 6 false (RVar x)
    ind-spine (RQualified x q) = ind-ex 6 false (RQualified x q)
    ind-spine (RResolved n) = ind-ex 6 false (RResolved n)
    ind-spine (RLam x e) = ind-ex 6 false (RLam x e)
    ind-spine (RLet x v b) = ind-ex 6 false (RLet x v b)
    ind-spine (RPair a b) = ind-ex 6 false (RPair a b)
    ind-spine (RDestruct s x el y er) = ind-ex 6 false (RDestruct s x el y er)
    ind-spine RUnit = ind-ex 6 false RUnit
    ind-spine (RInt z) = ind-ex 6 false (RInt z)
    ind-spine (RFloat i fr l) = ind-ex 6 false (RFloat i fr l)
    ind-spine (RAnnot e T) = ind-ex 6 false (RAnnot e T)
    ind-spine (RBinOp op a b) = ind-ex 6 false (RBinOp op a b)
    ind-spine (RNeg e) = ind-ex 6 false (RNeg e)

    ind-spine′ : ∀ b f a → Ind (pspine′ b f a)
    ind-spine′ true (RVar ux) a = ind-spine (RVar ux) ⊕ⁱ ind-pure ⊕ⁱ ind-ex 6 false a
    ind-spine′ true (RQualified ux uq) a = ind-spine (RQualified ux uq) ⊕ⁱ ind-pure ⊕ⁱ ind-ex 6 false a
    ind-spine′ true (RResolved un) a = ind-spine (RResolved un) ⊕ⁱ ind-pure ⊕ⁱ ind-ex 6 false a
    ind-spine′ true (RApp c g) h = ind-compose 6 g h
    ind-spine′ true (RLam ux ue) a = ind-spine (RLam ux ue) ⊕ⁱ ind-pure ⊕ⁱ ind-ex 6 false a
    ind-spine′ true (RLet ux uv ub) a = ind-spine (RLet ux uv ub) ⊕ⁱ ind-pure ⊕ⁱ ind-ex 6 false a
    ind-spine′ true (RPair ua ub) a = ind-spine (RPair ua ub) ⊕ⁱ ind-pure ⊕ⁱ ind-ex 6 false a
    ind-spine′ true (RDestruct us ux uel uy uer) a = ind-spine (RDestruct us ux uel uy uer) ⊕ⁱ ind-pure ⊕ⁱ ind-ex 6 false a
    ind-spine′ true RUnit a = ind-spine RUnit ⊕ⁱ ind-pure ⊕ⁱ ind-ex 6 false a
    ind-spine′ true (RInt uz) a = ind-spine (RInt uz) ⊕ⁱ ind-pure ⊕ⁱ ind-ex 6 false a
    ind-spine′ true (RFloat ui ufr ul) a = ind-spine (RFloat ui ufr ul) ⊕ⁱ ind-pure ⊕ⁱ ind-ex 6 false a
    ind-spine′ true (RAnnot ue uT) a = ind-spine (RAnnot ue uT) ⊕ⁱ ind-pure ⊕ⁱ ind-ex 6 false a
    ind-spine′ true (RBinOp uop ua ub) a = ind-spine (RBinOp uop ua ub) ⊕ⁱ ind-pure ⊕ⁱ ind-ex 6 false a
    ind-spine′ true (RNeg ue) a = ind-spine (RNeg ue) ⊕ⁱ ind-pure ⊕ⁱ ind-ex 6 false a
    ind-spine′ false f a = ind-spine f ⊕ⁱ ind-pure ⊕ⁱ ind-ex 6 false a

    ind-lam : ∀ e → Ind (plam′ e)
    ind-lam (RLam y e) = ind-pure ⊕ⁱ ind-word y ⊕ⁱ ind-lam e
    ind-lam (RVar x) = ind-pure ⊕ⁱ ind-pure ⊕ⁱ ind-n (ind-pure ⊕ⁱ ind-ex 0 true (RVar x))
    ind-lam (RQualified x q) = ind-pure ⊕ⁱ ind-pure ⊕ⁱ ind-n (ind-pure ⊕ⁱ ind-ex 0 true (RQualified x q))
    ind-lam (RResolved n) = ind-pure ⊕ⁱ ind-pure ⊕ⁱ ind-n (ind-pure ⊕ⁱ ind-ex 0 true (RResolved n))
    ind-lam (RApp f a) = ind-pure ⊕ⁱ ind-pure ⊕ⁱ ind-n (ind-pure ⊕ⁱ ind-ex 0 true (RApp f a))
    ind-lam (RLet x v b) = ind-pure ⊕ⁱ ind-pure ⊕ⁱ ind-n (ind-pure ⊕ⁱ ind-ex 0 true (RLet x v b))
    ind-lam (RPair a b) = ind-pure ⊕ⁱ ind-pure ⊕ⁱ ind-n (ind-pure ⊕ⁱ ind-ex 0 true (RPair a b))
    ind-lam (RDestruct s x el y er) = ind-pure ⊕ⁱ ind-pure ⊕ⁱ ind-n (ind-pure ⊕ⁱ ind-ex 0 true (RDestruct s x el y er))
    ind-lam RUnit = ind-pure ⊕ⁱ ind-pure ⊕ⁱ ind-n (ind-pure ⊕ⁱ ind-ex 0 true RUnit)
    ind-lam (RInt z) = ind-pure ⊕ⁱ ind-pure ⊕ⁱ ind-n (ind-pure ⊕ⁱ ind-ex 0 true (RInt z))
    ind-lam (RFloat i fr l) = ind-pure ⊕ⁱ ind-pure ⊕ⁱ ind-n (ind-pure ⊕ⁱ ind-ex 0 true (RFloat i fr l))
    ind-lam (RAnnot e T) = ind-pure ⊕ⁱ ind-pure ⊕ⁱ ind-n (ind-pure ⊕ⁱ ind-ex 0 true (RAnnot e T))
    ind-lam (RBinOp op a b) = ind-pure ⊕ⁱ ind-pure ⊕ⁱ ind-n (ind-pure ⊕ⁱ ind-ex 0 true (RBinOp op a b))
    ind-lam (RNeg e) = ind-pure ⊕ⁱ ind-pure ⊕ⁱ ind-n (ind-pure ⊕ⁱ ind-ex 0 true (RNeg e))

    ind-lhead : ∀ x v → Ind (lhead x v)
    ind-lhead x v = ind-word "let" ⊕ⁱ ind-pure ⊕ⁱ ind-word x ⊕ⁱ ind-pure ⊕ⁱ ind-pure ⊕ⁱ ind-gn (ind-pure ⊕ⁱ ind-ex 0 true v)

    ind-let : ∀ x v b → Ind (plet′ x v b)
    ind-let x v (RLet y v′ c) = ind-lhead x v ⊕ⁱ ind-pure ⊕ⁱ ind-word "in" ⊕ⁱ ind-pure ⊕ⁱ ind-let y v′ c
    ind-let x v (RVar bx) = ind-lhead x v ⊕ⁱ ind-pure ⊕ⁱ ind-word "in" ⊕ⁱ ind-pure ⊕ⁱ ind-ex 0 true (RVar bx)
    ind-let x v (RQualified bx bq) = ind-lhead x v ⊕ⁱ ind-pure ⊕ⁱ ind-word "in" ⊕ⁱ ind-pure ⊕ⁱ ind-ex 0 true (RQualified bx bq)
    ind-let x v (RResolved bn) = ind-lhead x v ⊕ⁱ ind-pure ⊕ⁱ ind-word "in" ⊕ⁱ ind-pure ⊕ⁱ ind-ex 0 true (RResolved bn)
    ind-let x v (RApp bf ba) = ind-lhead x v ⊕ⁱ ind-pure ⊕ⁱ ind-word "in" ⊕ⁱ ind-pure ⊕ⁱ ind-ex 0 true (RApp bf ba)
    ind-let x v (RLam bx be) = ind-lhead x v ⊕ⁱ ind-pure ⊕ⁱ ind-word "in" ⊕ⁱ ind-pure ⊕ⁱ ind-ex 0 true (RLam bx be)
    ind-let x v (RPair ba bb) = ind-lhead x v ⊕ⁱ ind-pure ⊕ⁱ ind-word "in" ⊕ⁱ ind-pure ⊕ⁱ ind-ex 0 true (RPair ba bb)
    ind-let x v (RDestruct bs bx bel by ber) = ind-lhead x v ⊕ⁱ ind-pure ⊕ⁱ ind-word "in" ⊕ⁱ ind-pure ⊕ⁱ ind-ex 0 true (RDestruct bs bx bel by ber)
    ind-let x v RUnit = ind-lhead x v ⊕ⁱ ind-pure ⊕ⁱ ind-word "in" ⊕ⁱ ind-pure ⊕ⁱ ind-ex 0 true RUnit
    ind-let x v (RInt bz) = ind-lhead x v ⊕ⁱ ind-pure ⊕ⁱ ind-word "in" ⊕ⁱ ind-pure ⊕ⁱ ind-ex 0 true (RInt bz)
    ind-let x v (RFloat bi bfr bl) = ind-lhead x v ⊕ⁱ ind-pure ⊕ⁱ ind-word "in" ⊕ⁱ ind-pure ⊕ⁱ ind-ex 0 true (RFloat bi bfr bl)
    ind-let x v (RAnnot be bT) = ind-lhead x v ⊕ⁱ ind-pure ⊕ⁱ ind-word "in" ⊕ⁱ ind-pure ⊕ⁱ ind-ex 0 true (RAnnot be bT)
    ind-let x v (RBinOp bop ba bb) = ind-lhead x v ⊕ⁱ ind-pure ⊕ⁱ ind-word "in" ⊕ⁱ ind-pure ⊕ⁱ ind-ex 0 true (RBinOp bop ba bb)
    ind-let x v (RNeg be) = ind-lhead x v ⊕ⁱ ind-pure ⊕ⁱ ind-word "in" ⊕ⁱ ind-pure ⊕ⁱ ind-ex 0 true (RNeg be)

  private
    ind-path : ∀ p → Ind (path p)
    ind-path [] = ind-pure
    ind-path (x ∷ []) = ind-word x
    ind-path (x ∷ y ∷ ys) = ind-word x ⊕ⁱ ind-pure ⊕ⁱ ind-path (y ∷ ys)

    ind-spaced : ∀ ps → Ind (spaced ps)
    ind-spaced [] = ind-pure
    ind-spaced (x ∷ xs) = ind-pure ⊕ⁱ ind-word x ⊕ⁱ ind-spaced xs

  -- | A declaration prints alike.
  ind-body : ∀ d → Ind (pbody d)
  ind-body (DImport (mkImport p nothing)) = ind-word "import" ⊕ⁱ ind-pure ⊕ⁱ ind-path p
  ind-body (DImport (mkImport p (just a))) =
    ind-word "import" ⊕ⁱ ind-pure ⊕ⁱ ind-path p ⊕ⁱ ind-pure ⊕ⁱ ind-word "as" ⊕ⁱ ind-pure ⊕ⁱ ind-word a
  ind-body (DTypeAlias x ps A) =
    ind-word "type" ⊕ⁱ ind-pure ⊕ⁱ ind-word x ⊕ⁱ ind-spaced ps ⊕ⁱ ind-pure ⊕ⁱ ind-pure ⊕ⁱ ind-pure ⊕ⁱ ind-ty 0 true A
  ind-body (DSignature x A) =
    ind-word "signature" ⊕ⁱ ind-pure ⊕ⁱ ind-word x ⊕ⁱ ind-pure ⊕ⁱ ind-pure ⊕ⁱ ind-pure ⊕ⁱ ind-ty 0 true A
  ind-body (DTypeSig x A) = ind-name x ⊕ⁱ ind-pure ⊕ⁱ ind-pure ⊕ⁱ ind-pure ⊕ⁱ ind-ty 0 true A
  ind-body (DFunDef x e) =
    ind-name x ⊕ⁱ ind-spaced (proj₁ (lams e)) ⊕ⁱ ind-pure ⊕ⁱ ind-pure ⊕ⁱ ind-pure ⊕ⁱ ind-ex 0 true (proj₂ (lams e))


------------------------------------------------------------------------
-- The module prints alike
------------------------------------------------------------------------

private
  Blank : Note → Set
  Blank n = n ≡ note-blank

  QN : Notes → Set
  QN n = Notes.inner n ≡ [] × Notes.after n ≡ [] × All Blank (Notes.top n)

-- | Each anchor's notes are quiet.
QuietT : Trivia → Set
QuietT = All (λ e → QN (proj₂ e))

private
  lookup-quiet : ∀ tv → QuietT tv → Quiet tv
  lookup-quiet []             []       k = refl , refl , []
  lookup-quiet ((j , n) ∷ ts) (qn ∷ qs) k = pick (k ≡ᵇ j)
    where
      pick : ∀ b → QN (if b then n else lookupNotes k ts)
      pick true  = qn
      pick false = lookup-quiet ts qs k

  hoist-quietT : ∀ k tv → QuietT tv → QuietT (hoist k tv)
  hoist-quietT k []                         []        = []
  hoist-quietT k ((j , notes t .[] .[]) ∷ ts) ((refl , refl , bs) ∷ qs) = pick (k ≡ᵇ j)
    where
      pick : ∀ b → QuietT (if b then (j , notes (t ++ []) [] []) ∷ ts else (j , notes t [] []) ∷ hoist k ts)
      pick true  = (refl , refl , AllP.++⁺ bs []) ∷ qs
      pick false = (refl , refl , bs) ∷ hoist-quietT k ts qs

  hasComment-blank : ∀ ns → All Blank ns → hasComment ns ≡ false
  hasComment-blank []       []          = refl
  hasComment-blank (_ ∷ ns) (refl ∷ bs) = hasComment-blank ns bs

  runs-blank : ∀ ns b → All Blank ns → runs ns [] b ≡ empty
  runs-blank []       b []          = refl
  runs-blank (_ ∷ ns) b (refl ∷ bs) = runs-blank ns true bs

  lead-blank : ∀ prev ns → All Blank ns → lead prev ns ≡ lead prev []
  lead-blank nothing  ns bs rewrite hasComment-blank ns bs = refl
  lead-blank (just _) ns bs = runs-blank ns false bs

  ending-blank : ∀ prev ns → All Blank ns → ending prev ns ≡ ending prev []
  ending-blank prev ns bs rewrite hasComment-blank ns bs = refl

  tops-blank : ∀ tv → Quiet tv → ∀ j n → All Blank (tops tv j n)
  tops-blank tv q j zero    = []
  tops-blank tv q j (suc n) = AllP.++⁺ (proj₂ (proj₂ (q j))) (tops-blank tv q (suc j) n)

  tops-[] : ∀ j n → tops [] j n ≡ []
  tops-[] j zero    = refl
  tops-[] j (suc n) = tops-[] (suc j) n

  lead-same : ∀ prev k k′ tv → Quiet tv → lead prev (topList k k′ tv) ≡ lead prev (topList k k′ [])
  lead-same prev k k′ tv q =
    trans (lead-blank prev _ (tops-blank tv q k (k′ ∸ k))) (cong (lead prev) (sym (tops-[] k (k′ ∸ k))))

-- | Quiet trivia print the declarations as no trivia does.
pdecls-same : ∀ prev ds tv k → QuietT tv → pdecls prev ds tv k ≡ pdecls prev ds [] k
pdecls-same prev [] tv k qt =
  cong (_, k) (trans (ending-blank prev _ (tops-blank (hoist k tv) (lookup-quiet _ (hoist-quietT k tv qt)) k (suc k ∸ k)))
                     (cong (ending prev) (sym (tops-[] k (suc k ∸ k)))))
pdecls-same prev (d ∷ ds) tv k qt =
  trans (cong F (Same.Ind.same (Same.ind-gn tv′ q′ (Same.ind-body tv′ q′ d)) k)) (F-same (pdecl d [] k))
  where
    tv′ = hoist k tv
    qt′ = hoist-quietT k tv qt
    q′  = lookup-quiet tv′ qt′
    F : Doc × ℕ → Doc × ℕ
    F p = (gap prev d Doc.<> lead prev (topList k (proj₂ p) tv′) Doc.<> proj₁ p Doc.<> Doc.newline
             Doc.<> proj₁ (pdecls (just d) ds tv′ (proj₂ p))) , proj₂ (pdecls (just d) ds tv′ (proj₂ p))
    F-same : ∀ p → F p ≡ ((gap prev d Doc.<> lead prev (topList k (proj₂ p) []) Doc.<> proj₁ p Doc.<> Doc.newline
                           Doc.<> proj₁ (pdecls (just d) ds [] (proj₂ p))) , proj₂ (pdecls (just d) ds [] (proj₂ p)))
    F-same p = cong₂ (λ L R → (gap prev d Doc.<> L Doc.<> proj₁ p Doc.<> Doc.newline Doc.<> proj₁ R) , proj₂ R)
                 (lead-same prev k (proj₂ p) tv′ q′) (pdecls-same (just d) ds tv′ (proj₂ p) qt′)

------------------------------------------------------------------------
-- The walk over a text without comments
------------------------------------------------------------------------

-- | Tokens and swallowed line ends, no comment.
data NoComment : Item → Set where
  nc-tok  : ∀ {t} → NoComment (tok t)
  nc-cont : NoComment cont

private
  data NoText : Line → Set where
    nt-empty : NoText line-empty
    nt-code  : NoText line-code

  HB : Held → Set
  HB h = h ≡ held-blank

  record InvW (σ : W) : Set where
    constructor inv
    field
      text  : NoText (W.ln σ)
      held  : All HB (W.held σ)
      quiet : QuietT (W.acc σ)

  addTo-quiet : ∀ k f t → (∀ n → QN n → QN (f n)) → QuietT t → QuietT (addTo k f t)
  addTo-quiet k f []             pf []        = pf noNotes (refl , refl , []) ∷ []
  addTo-quiet k f ((j , n) ∷ ts) pf (qn ∷ qs) = pick (k ≡ᵇ j)
    where
      pick : ∀ b → QuietT (if b then (j , f n) ∷ ts else (j , n) ∷ addTo k f ts)
      pick true  = pf n qn ∷ qs
      pick false = qn ∷ addTo-quiet k f ts pf qs

  blankTop : ∀ n → QN n → QN (addTop note-blank n)
  blankTop (notes t i a) (ei , ea , bs) = ei , ea , AllP.++⁺ bs (refl ∷ [])

  settle-quiet : ∀ k f hs t → All HB hs → QuietT t → QuietT (settleAt k f hs t)
  settle-quiet k _     []                t []          qt = qt
  settle-quiet k true  (held-blank ∷ hs) t (refl ∷ bs) qt = settle-quiet k true hs _ bs (addTo-quiet k _ t blankTop qt)
  settle-quiet k false (held-blank ∷ hs) t (refl ∷ bs) qt = settle-quiet k false hs t bs qt

  blankBefore-blank : ∀ b hs → All HB hs → All HB (blankBefore b hs)
  blankBefore-blank b hs bs with 2 <ᵇ suc b
  ... | true  = AllP.++⁺ bs (refl ∷ [])
  ... | false = bs

  pending-blank : ∀ ln hs → NoText ln → All HB hs → All HB (pending ln hs)
  pending-blank line-empty hs nt-empty bs = bs
  pending-blank line-code  hs nt-code  bs = bs

  lineEnd-inv : ∀ top σ → InvW σ → InvW (lineEnd top σ)
  lineEnd-inv top (walker k h′ line-empty hs b fr t) (inv nt-empty h q) = inv nt-empty h q
  lineEnd-inv top (walker k h′ line-code hs b fr t)  (inv nt-code h q)  = inv nt-empty h q

  settle-inv : ∀ σ → InvW σ → All HB (W.held σ) → QuietT (W.acc (settle σ))
  settle-inv (walker k h′ ln hs b fr t) (inv _ _ q) h = settle-quiet k fr _ t h q

  stepTok-inv : ∀ σ a b → InvW σ → InvW (stepTok σ a b)
  stepTok-inv σ a true i = hoist-inv (lineEnd true σ) (lineEnd-inv true σ i)
    where
      hoist-inv : ∀ τ → InvW τ → InvW (Once.Format.Print.hoistW τ)
      hoist-inv (walker k h′ ln hs b fr t) (inv nt h q) =
        inv nt h (Once.Format.Proof.Walk.hoistAt-cases k t QuietT q (hoist-quietT k t q))
  stepTok-inv (walker k h′ ln hs b fr t) a false (inv nt h q) =
    inv nt-code [] (settle-quiet k fr _ t (pending-blank ln _ nt (blankBefore-blank b hs h)) q)

  step-inv : ∀ σ i → NoComment i → InvW σ → InvW (step σ i)
  step-inv σ (tok x) nc-tok  iv = stepTok-inv σ (isAnchor x) (isLineEnd x) iv
  step-inv σ cont    nc-cont iv = lineEnd-inv false σ iv

  walk-inv : ∀ σ is → All NoComment is → InvW σ → InvW (walkItems σ is)
  walk-inv σ []       []        iv = iv
  walk-inv σ (i ∷ is) (n ∷ ns)  iv = walk-inv (step σ i) is ns (step-inv σ i n iv)

-- | A text without comments leaves quiet trivia.
trivia-quiet : ∀ is → All NoComment is → QuietT (trivia is)
trivia-quiet is ns with walk-inv (walker 0 false line-empty [] 0 true []) is ns (inv nt-empty [] [])
... | iv = settle-inv (lineEnd true (walkItems _ is)) (lineEnd-inv true _ iv) (InvW.held (lineEnd-inv true _ iv))

------------------------------------------------------------------------
-- Canonicity
------------------------------------------------------------------------

-- | Without comments, the layout is the module's alone.
format-quiet : ∀ m is → All NoComment is → format m is ≡ format m []
format-quiet (mkModule ds) is ns = cong (λ p → render (proj₁ p)) (pdecls-same nothing ds (trivia is) 0 (trivia-quiet is ns))

-- | Two texts without comments that parse as the same module are formatted
-- alike, whatever their whitespace and blank lines.
format-canonical : ∀ t₁ t₂ m → parseStrict t₁ ≡ inj₂ m → parseStrict t₂ ≡ inj₂ m
          → All NoComment (lexItems (toList t₁)) → All NoComment (lexItems (toList t₂))
          → formatSource t₁ ≡ formatSource t₂
format-canonical t₁ t₂ m e₁ e₂ n₁ n₂ =
  trans (cong (formatParsed t₁) e₁)
    (trans (cong inj₂ (trans (format-quiet m _ n₁) (sym (format-quiet m _ n₂)))) (sym (cong (formatParsed t₂) e₂)))

------------------------------------------------------------------------
-- Without trivia, the printer writes no comment
------------------------------------------------------------------------

-- | A document with no comment in it.
data NoNotes : Doc → Set where
  nn-empty   : NoNotes empty
  nn-tk      : ∀ {t} → NoNotes (Doc.tk t)
  nn-sp      : NoNotes Doc.sp
  nn-line    : NoNotes Doc.line
  nn-newline : NoNotes Doc.newline
  nn-blank   : NoNotes Doc.blank
  nn-<>      : ∀ {a b} → NoNotes a → NoNotes b → NoNotes (a Doc.<> b)
  nn-nest    : ∀ {n d} → NoNotes d → NoNotes (Doc.nest n d)
  nn-group   : ∀ {d} → NoNotes d → NoNotes (Doc.group d)

module Bare where
  instance
    i-empty : NoNotes empty
    i-empty = nn-empty
    i-tk : ∀ {t} → NoNotes (Doc.tk t)
    i-tk = nn-tk
    i-sp : NoNotes Doc.sp
    i-sp = nn-sp
    i-line : NoNotes Doc.line
    i-line = nn-line
    i-if : ∀ {b} → NoNotes (if b then Doc.sp else empty)
    i-if {true}  = nn-sp
    i-if {false} = nn-empty

  -- | A printer that, without trivia, writes no comment.
  record NN (m : P Doc) : Set where
    constructor nn
    field
      quiet : ∀ k → NoNotes (proj₁ (m [] k))

  nn-⊕ : ∀ {a b} → NN a → NN b → NN (a ⊕ᵈ b)
  nn-⊕ (nn qa) (nn qb) = nn λ k → nn-<> (qa k) (qb _)

  infixr 6 _⊕ⁿ_
  _⊕ⁿ_ : ∀ {a b} → NN a → NN b → NN (a ⊕ᵈ b)
  _⊕ⁿ_ = nn-⊕

  nn-pure : ∀ {d} → ⦃ NoNotes d ⦄ → NN (pure′ d)
  nn-pure ⦃ q ⦄ = nn λ k → q

  nn-gn : ∀ {m} → NN m → NN (m >>=′ λ d → pure′ (Doc.group (Doc.nest indent d)))
  nn-gn (nn q) = nn λ k → nn-group (nn-nest (q k))

  nn-g : ∀ {m} → NN m → NN (m >>=′ λ d → pure′ (Doc.group d))
  nn-g (nn q) = nn λ k → nn-group (q k)

  nn-n : ∀ {m} → NN m → NN (m >>=′ λ d → pure′ (Doc.nest indent d))
  nn-n (nn q) = nn λ k → nn-nest (q k)

  nn-paren : ∀ b {d} → NN d → NN (paren b d)
  nn-paren true  i = nn-pure ⊕ⁿ i ⊕ⁿ nn-pure
  nn-paren false i = i

  nn-if : ∀ b {x y} → NN x → NN y → NN (if b then x else y)
  nn-if true  ix iy = ix
  nn-if false ix iy = iy

  nn-anchor : ∀ x → NN (anchor x)
  nn-anchor x = nn λ k → nn-<> nn-empty (nn-<> nn-tk nn-empty)

  nn-word : ∀ s → NN (word s)
  nn-word s with s Data.String.== "compose"
  ... | true  = nn-pure
  ... | false = nn-anchor (TWord s)

  nn-opToks : ∀ cs → NN (opToks cs)
  nn-opToks []           = nn-pure
  nn-opToks (c ∷ [])     = opTok1′ (opToken c)
    where
      opTok1′ : ∀ m → NN (opTok1 m)
      opTok1′ (just x) = nn-pure
      opTok1′ nothing  = nn-pure
  nn-opToks (c ∷ d ∷ cs) = opTok1′ (opToken c) ⊕ⁿ nn-pure ⊕ⁿ nn-opToks (d ∷ cs)
    where
      opTok1′ : ∀ m → NN (opTok1 m)
      opTok1′ (just x) = nn-pure
      opTok1′ nothing  = nn-pure

  nn-name : ∀ x → NN (name x)
  nn-name x = nn-if (isOperator x) (nn-pure ⊕ⁿ nn-opToks (toList x) ⊕ⁿ nn-pure) (nn-word x)

  nn-grade : ∀ q → NN (grade q)
  nn-grade Zero = nn-pure ⊕ⁿ nn-pure ⊕ⁿ nn-pure ⊕ⁿ nn-pure
  nn-grade One  = nn-pure ⊕ⁿ nn-pure ⊕ⁿ nn-pure ⊕ⁿ nn-pure
  nn-grade Many = nn-pure ⊕ⁿ nn-pure

  nn-infix : ∀ x → NN (infixOp x)
  nn-infix x = nn-pure ⊕ⁿ nn-pure ⊕ⁿ nn-pure

  mutual
    nn-ty : ∀ l b P → NN (pty l b P)
    nn-ty l b PUnit = nn-word "Unit"
    nn-ty l b PVoid = nn-word "Void"
    nn-ty l b PInt = nn-word "Int"
    nn-ty l b PFloat = nn-word "Float"
    nn-ty l b (PTVar x) = nn-word x
    nn-ty l b (A P⇒[ q ] B) = nn-paren (0 <ᵇ l) (nn-ty 1 true A ⊕ⁿ nn-grade q ⊕ⁿ nn-pure ⊕ⁿ nn-ty 0 (b ∨ (0 <ᵇ l)) B)
    nn-ty l b (A P+ B) = nn-paren (1 <ᵇ l) (nn-ty 1 false A ⊕ⁿ nn-infix _ ⊕ⁿ nn-ty 2 (b ∨ (1 <ᵇ l)) B)
    nn-ty l b (A P* B) = nn-paren (2 <ᵇ l) (nn-ty 2 false A ⊕ⁿ nn-infix _ ⊕ⁿ nn-ty 3 (b ∨ (2 <ᵇ l)) B)
    nn-ty l b (PEff A B) = nn-paren (3 <ᵇ l) (nn-word "Eff" ⊕ⁿ nn-pure ⊕ⁿ nn-ty 3 false A ⊕ⁿ nn-pure ⊕ⁿ nn-ty 3 false B)
    nn-ty l b (PAct A B) = nn-paren (3 <ᵇ l) (nn-word "Act" ⊕ⁿ nn-pure ⊕ⁿ nn-ty 3 false A ⊕ⁿ nn-pure ⊕ⁿ nn-ty 3 false B)
    nn-ty l b (Pμ F) = nn-paren (not b) (nn-word "Mu" ⊕ⁿ nn-pure ⊕ⁿ nn-arg F)
    nn-ty l b (Pν F pureᶠ) = nn-paren (not b) (nn-word "Nu" ⊕ⁿ nn-pure ⊕ⁿ nn-arg F)
    nn-ty l b (Pν F actᶠ) =
      nn-paren (not b) (nn-word "Nu" ⊕ⁿ nn-pure ⊕ⁿ nn-pure ⊕ⁿ nn-word "Act" ⊕ⁿ nn-pure ⊕ⁿ nn-fun 0 F ⊕ⁿ nn-pure)

    nn-arg : ∀ F → NN (pfunArg F)
    nn-arg PId = nn-word "Id"
    nn-arg (PK A) = nn-pure ⊕ⁿ nn-fun 0 (PK A) ⊕ⁿ nn-pure
    nn-arg (F P⊕ G) = nn-pure ⊕ⁿ nn-fun 0 (F P⊕ G) ⊕ⁿ nn-pure
    nn-arg (F P⊗ G) = nn-pure ⊕ⁿ nn-fun 0 (F P⊗ G) ⊕ⁿ nn-pure

    nn-fun : ∀ l F → NN (pfun l F)
    nn-fun l PId = nn-word "Id"
    nn-fun l (PK A) = nn-paren (1 <ᵇ l) (nn-word "K" ⊕ⁿ nn-pure ⊕ⁿ nn-ty 3 false A)
    nn-fun l (F P⊕ G) = nn-paren (0 <ᵇ l) (nn-fun 0 F ⊕ⁿ nn-infix _ ⊕ⁿ nn-fun 1 G)
    nn-fun l (F P⊗ G) = nn-paren (1 <ᵇ l) (nn-fun 1 F ⊕ⁿ nn-infix _ ⊕ⁿ nn-fun 2 G)

  mutual
    nn-ex : ∀ l wh e → NN (pex l wh e)
    nn-ex l wh (RVar x) = nn-name x
    nn-ex l wh (RQualified x q) = nn-word x ⊕ⁿ nn-pure ⊕ⁿ nn-word q
    nn-ex l wh (RResolved (canonical xs)) = nn-dotted xs
    nn-ex l wh (RApp f a) = nn-comp l (isCompose (headOf f)) f a
    nn-ex l wh (RLam x e) = nn-paren (not wh) (nn-g (nn-pure ⊕ⁿ nn-word x ⊕ⁿ nn-lam e))
    nn-ex l wh (RLet x v b) = nn-paren (not wh) (nn-g (nn-let x v b))
    nn-ex l wh (RPair a b) =
      nn-gn (nn-pure ⊕ⁿ nn-ex 0 true a ⊕ⁿ nn-pure ⊕ⁿ nn-pure ⊕ⁿ nn-ex 0 true b ⊕ⁿ nn-pure)
    nn-ex l wh (RDestruct s x el y er) =
      nn-paren (not wh) (nn-g (nn-word "destruct" ⊕ⁿ nn-pure ⊕ⁿ nn-ex 0 true s ⊕ⁿ nn-pure ⊕ⁿ nn-word "of"
        ⊕ⁿ nn-n (nn-pure ⊕ⁿ nn-pure ⊕ⁿ nn-pure ⊕ⁿ nn-word "Left" ⊕ⁿ nn-pure ⊕ⁿ nn-word x ⊕ⁿ nn-infix _
            ⊕ⁿ nn-ex 0 true el ⊕ⁿ nn-pure ⊕ⁿ nn-pure ⊕ⁿ nn-pure ⊕ⁿ nn-word "Right" ⊕ⁿ nn-pure ⊕ⁿ nn-word y
            ⊕ⁿ nn-infix _ ⊕ⁿ nn-ex 0 true er ⊕ⁿ nn-pure ⊕ⁿ nn-pure)))
    nn-ex l wh RUnit = nn-pure ⊕ⁿ nn-pure
    nn-ex l wh (RInt z) = nn-anchor (TInt z)
    nn-ex l wh (RFloat i f n) = nn-anchor (TFloat i f n)
    nn-ex l wh (RAnnot e T) = nn-pure ⊕ⁿ nn-ex 0 true e ⊕ⁿ nn-infix _ ⊕ⁿ nn-ty 0 true (toPoly T) ⊕ⁿ nn-pure
    nn-ex l wh (RBinOp op a b) = nn-gn (nn-paren (opLevel op <ᵇ l) (nn-bin (opLevel op) op a b))
    nn-ex l wh (RNeg e) = nn-paren (4 <ᵇ l) (nn-pure ⊕ⁿ nn-pure ⊕ⁿ nn-ex 4 false e)

    nn-dotted : ∀ xs → NN (dotted xs)
    nn-dotted [] = nn-pure
    nn-dotted (x ∷ []) = nn-word x
    nn-dotted (x ∷ y ∷ ys) = nn-word x ⊕ⁿ nn-pure ⊕ⁿ nn-dotted (y ∷ ys)

    nn-comp : ∀ l b f a → NN (pcomp l b f a)
    nn-comp l true (RVar ux) a = nn-gn (nn-paren (5 <ᵇ l) (nn-spine (RVar ux) ⊕ⁿ nn-pure ⊕ⁿ nn-ex 6 false a))
    nn-comp l true (RQualified ux uq) a = nn-gn (nn-paren (5 <ᵇ l) (nn-spine (RQualified ux uq) ⊕ⁿ nn-pure ⊕ⁿ nn-ex 6 false a))
    nn-comp l true (RResolved un) a = nn-gn (nn-paren (5 <ᵇ l) (nn-spine (RResolved un) ⊕ⁿ nn-pure ⊕ⁿ nn-ex 6 false a))
    nn-comp l true (RApp c g) h = nn-compose l g h
    nn-comp l true (RLam ux ue) a = nn-gn (nn-paren (5 <ᵇ l) (nn-spine (RLam ux ue) ⊕ⁿ nn-pure ⊕ⁿ nn-ex 6 false a))
    nn-comp l true (RLet ux uv ub) a = nn-gn (nn-paren (5 <ᵇ l) (nn-spine (RLet ux uv ub) ⊕ⁿ nn-pure ⊕ⁿ nn-ex 6 false a))
    nn-comp l true (RPair ua ub) a = nn-gn (nn-paren (5 <ᵇ l) (nn-spine (RPair ua ub) ⊕ⁿ nn-pure ⊕ⁿ nn-ex 6 false a))
    nn-comp l true (RDestruct us ux uel uy uer) a = nn-gn (nn-paren (5 <ᵇ l) (nn-spine (RDestruct us ux uel uy uer) ⊕ⁿ nn-pure ⊕ⁿ nn-ex 6 false a))
    nn-comp l true RUnit a = nn-gn (nn-paren (5 <ᵇ l) (nn-spine RUnit ⊕ⁿ nn-pure ⊕ⁿ nn-ex 6 false a))
    nn-comp l true (RInt uz) a = nn-gn (nn-paren (5 <ᵇ l) (nn-spine (RInt uz) ⊕ⁿ nn-pure ⊕ⁿ nn-ex 6 false a))
    nn-comp l true (RFloat ui ufr ul) a = nn-gn (nn-paren (5 <ᵇ l) (nn-spine (RFloat ui ufr ul) ⊕ⁿ nn-pure ⊕ⁿ nn-ex 6 false a))
    nn-comp l true (RAnnot ue uT) a = nn-gn (nn-paren (5 <ᵇ l) (nn-spine (RAnnot ue uT) ⊕ⁿ nn-pure ⊕ⁿ nn-ex 6 false a))
    nn-comp l true (RBinOp uop ua ub) a = nn-gn (nn-paren (5 <ᵇ l) (nn-spine (RBinOp uop ua ub) ⊕ⁿ nn-pure ⊕ⁿ nn-ex 6 false a))
    nn-comp l true (RNeg ue) a = nn-gn (nn-paren (5 <ᵇ l) (nn-spine (RNeg ue) ⊕ⁿ nn-pure ⊕ⁿ nn-ex 6 false a))
    nn-comp l false f a = nn-gn (nn-paren (5 <ᵇ l) (nn-spine f ⊕ⁿ nn-pure ⊕ⁿ nn-ex 6 false a))

    nn-compose : ∀ l g h → NN (pcompose l g h)
    nn-compose l g h = nn-gn (nn-paren (0 <ᵇ l) (nn-chain g ⊕ⁿ (nn-pure ⊕ⁿ nn-pure ⊕ⁿ nn-pure) ⊕ⁿ nn-ex 1 false h))

    nn-chain : ∀ g → NN (pchainC g)
    nn-chain (RApp f h) = nn-chain′ (isCompose (headOf f)) f h
    nn-chain (RVar x) = nn-ex 1 false (RVar x)
    nn-chain (RQualified x q) = nn-ex 1 false (RQualified x q)
    nn-chain (RResolved n) = nn-ex 1 false (RResolved n)
    nn-chain (RLam x e) = nn-ex 1 false (RLam x e)
    nn-chain (RLet x v b) = nn-ex 1 false (RLet x v b)
    nn-chain (RPair a b) = nn-ex 1 false (RPair a b)
    nn-chain (RDestruct s x el y er) = nn-ex 1 false (RDestruct s x el y er)
    nn-chain RUnit = nn-ex 1 false RUnit
    nn-chain (RInt z) = nn-ex 1 false (RInt z)
    nn-chain (RFloat i fr l) = nn-ex 1 false (RFloat i fr l)
    nn-chain (RAnnot e T) = nn-ex 1 false (RAnnot e T)
    nn-chain (RBinOp op a b) = nn-ex 1 false (RBinOp op a b)
    nn-chain (RNeg e) = nn-ex 1 false (RNeg e)

    nn-chain′ : ∀ b f h → NN (pchainC′ b f h)
    nn-chain′ true (RVar ux) h = nn-comp 0 false (RVar ux) h
    nn-chain′ true (RQualified ux uq) h = nn-comp 0 false (RQualified ux uq) h
    nn-chain′ true (RResolved un) h = nn-comp 0 false (RResolved un) h
    nn-chain′ true (RApp c g) h = nn-chain g ⊕ⁿ (nn-pure ⊕ⁿ nn-pure ⊕ⁿ nn-pure) ⊕ⁿ nn-ex 1 false h
    nn-chain′ true (RLam ux ue) h = nn-comp 0 false (RLam ux ue) h
    nn-chain′ true (RLet ux uv ub) h = nn-comp 0 false (RLet ux uv ub) h
    nn-chain′ true (RPair ua ub) h = nn-comp 0 false (RPair ua ub) h
    nn-chain′ true (RDestruct us ux uel uy uer) h = nn-comp 0 false (RDestruct us ux uel uy uer) h
    nn-chain′ true RUnit h = nn-comp 0 false RUnit h
    nn-chain′ true (RInt uz) h = nn-comp 0 false (RInt uz) h
    nn-chain′ true (RFloat ui ufr ul) h = nn-comp 0 false (RFloat ui ufr ul) h
    nn-chain′ true (RAnnot ue uT) h = nn-comp 0 false (RAnnot ue uT) h
    nn-chain′ true (RBinOp uop ua ub) h = nn-comp 0 false (RBinOp uop ua ub) h
    nn-chain′ true (RNeg ue) h = nn-comp 0 false (RNeg ue) h
    nn-chain′ false f h = nn-comp 0 false f h

    nn-bin : ∀ lv op a b → NN (pbin lv op a b)
    nn-bin lv op a b = nn-left lv a ⊕ⁿ nn-pure ⊕ⁿ nn-pure ⊕ⁿ nn-pure ⊕ⁿ nn-ex (suc lv) false b

    nn-left : ∀ lv a → NN (pleft lv a)
    nn-left lv (RBinOp op x y) = nn-if ((lv ≡ᵇ opLevel op) ∧ (1 <ᵇ lv)) (nn-bin lv op x y) (nn-ex (leftLevel lv) false (RBinOp op x y))
    nn-left lv (RVar x) = nn-ex (leftLevel lv) false (RVar x)
    nn-left lv (RQualified x q) = nn-ex (leftLevel lv) false (RQualified x q)
    nn-left lv (RResolved n) = nn-ex (leftLevel lv) false (RResolved n)
    nn-left lv (RApp f a) = nn-ex (leftLevel lv) false (RApp f a)
    nn-left lv (RLam x e) = nn-ex (leftLevel lv) false (RLam x e)
    nn-left lv (RLet x v b) = nn-ex (leftLevel lv) false (RLet x v b)
    nn-left lv (RPair a b) = nn-ex (leftLevel lv) false (RPair a b)
    nn-left lv (RDestruct s x el y er) = nn-ex (leftLevel lv) false (RDestruct s x el y er)
    nn-left lv RUnit = nn-ex (leftLevel lv) false RUnit
    nn-left lv (RInt z) = nn-ex (leftLevel lv) false (RInt z)
    nn-left lv (RFloat i fr l) = nn-ex (leftLevel lv) false (RFloat i fr l)
    nn-left lv (RAnnot e T) = nn-ex (leftLevel lv) false (RAnnot e T)
    nn-left lv (RNeg e) = nn-ex (leftLevel lv) false (RNeg e)

    nn-spine : ∀ f → NN (pspine f)
    nn-spine (RApp f a) = nn-spine′ (isCompose (headOf f)) f a
    nn-spine (RVar x) = nn-ex 6 false (RVar x)
    nn-spine (RQualified x q) = nn-ex 6 false (RQualified x q)
    nn-spine (RResolved n) = nn-ex 6 false (RResolved n)
    nn-spine (RLam x e) = nn-ex 6 false (RLam x e)
    nn-spine (RLet x v b) = nn-ex 6 false (RLet x v b)
    nn-spine (RPair a b) = nn-ex 6 false (RPair a b)
    nn-spine (RDestruct s x el y er) = nn-ex 6 false (RDestruct s x el y er)
    nn-spine RUnit = nn-ex 6 false RUnit
    nn-spine (RInt z) = nn-ex 6 false (RInt z)
    nn-spine (RFloat i fr l) = nn-ex 6 false (RFloat i fr l)
    nn-spine (RAnnot e T) = nn-ex 6 false (RAnnot e T)
    nn-spine (RBinOp op a b) = nn-ex 6 false (RBinOp op a b)
    nn-spine (RNeg e) = nn-ex 6 false (RNeg e)

    nn-spine′ : ∀ b f a → NN (pspine′ b f a)
    nn-spine′ true (RVar ux) a = nn-spine (RVar ux) ⊕ⁿ nn-pure ⊕ⁿ nn-ex 6 false a
    nn-spine′ true (RQualified ux uq) a = nn-spine (RQualified ux uq) ⊕ⁿ nn-pure ⊕ⁿ nn-ex 6 false a
    nn-spine′ true (RResolved un) a = nn-spine (RResolved un) ⊕ⁿ nn-pure ⊕ⁿ nn-ex 6 false a
    nn-spine′ true (RApp c g) h = nn-compose 6 g h
    nn-spine′ true (RLam ux ue) a = nn-spine (RLam ux ue) ⊕ⁿ nn-pure ⊕ⁿ nn-ex 6 false a
    nn-spine′ true (RLet ux uv ub) a = nn-spine (RLet ux uv ub) ⊕ⁿ nn-pure ⊕ⁿ nn-ex 6 false a
    nn-spine′ true (RPair ua ub) a = nn-spine (RPair ua ub) ⊕ⁿ nn-pure ⊕ⁿ nn-ex 6 false a
    nn-spine′ true (RDestruct us ux uel uy uer) a = nn-spine (RDestruct us ux uel uy uer) ⊕ⁿ nn-pure ⊕ⁿ nn-ex 6 false a
    nn-spine′ true RUnit a = nn-spine RUnit ⊕ⁿ nn-pure ⊕ⁿ nn-ex 6 false a
    nn-spine′ true (RInt uz) a = nn-spine (RInt uz) ⊕ⁿ nn-pure ⊕ⁿ nn-ex 6 false a
    nn-spine′ true (RFloat ui ufr ul) a = nn-spine (RFloat ui ufr ul) ⊕ⁿ nn-pure ⊕ⁿ nn-ex 6 false a
    nn-spine′ true (RAnnot ue uT) a = nn-spine (RAnnot ue uT) ⊕ⁿ nn-pure ⊕ⁿ nn-ex 6 false a
    nn-spine′ true (RBinOp uop ua ub) a = nn-spine (RBinOp uop ua ub) ⊕ⁿ nn-pure ⊕ⁿ nn-ex 6 false a
    nn-spine′ true (RNeg ue) a = nn-spine (RNeg ue) ⊕ⁿ nn-pure ⊕ⁿ nn-ex 6 false a
    nn-spine′ false f a = nn-spine f ⊕ⁿ nn-pure ⊕ⁿ nn-ex 6 false a

    nn-lam : ∀ e → NN (plam′ e)
    nn-lam (RLam y e) = nn-pure ⊕ⁿ nn-word y ⊕ⁿ nn-lam e
    nn-lam (RVar x) = nn-pure ⊕ⁿ nn-pure ⊕ⁿ nn-n (nn-pure ⊕ⁿ nn-ex 0 true (RVar x))
    nn-lam (RQualified x q) = nn-pure ⊕ⁿ nn-pure ⊕ⁿ nn-n (nn-pure ⊕ⁿ nn-ex 0 true (RQualified x q))
    nn-lam (RResolved n) = nn-pure ⊕ⁿ nn-pure ⊕ⁿ nn-n (nn-pure ⊕ⁿ nn-ex 0 true (RResolved n))
    nn-lam (RApp f a) = nn-pure ⊕ⁿ nn-pure ⊕ⁿ nn-n (nn-pure ⊕ⁿ nn-ex 0 true (RApp f a))
    nn-lam (RLet x v b) = nn-pure ⊕ⁿ nn-pure ⊕ⁿ nn-n (nn-pure ⊕ⁿ nn-ex 0 true (RLet x v b))
    nn-lam (RPair a b) = nn-pure ⊕ⁿ nn-pure ⊕ⁿ nn-n (nn-pure ⊕ⁿ nn-ex 0 true (RPair a b))
    nn-lam (RDestruct s x el y er) = nn-pure ⊕ⁿ nn-pure ⊕ⁿ nn-n (nn-pure ⊕ⁿ nn-ex 0 true (RDestruct s x el y er))
    nn-lam RUnit = nn-pure ⊕ⁿ nn-pure ⊕ⁿ nn-n (nn-pure ⊕ⁿ nn-ex 0 true RUnit)
    nn-lam (RInt z) = nn-pure ⊕ⁿ nn-pure ⊕ⁿ nn-n (nn-pure ⊕ⁿ nn-ex 0 true (RInt z))
    nn-lam (RFloat i fr l) = nn-pure ⊕ⁿ nn-pure ⊕ⁿ nn-n (nn-pure ⊕ⁿ nn-ex 0 true (RFloat i fr l))
    nn-lam (RAnnot e T) = nn-pure ⊕ⁿ nn-pure ⊕ⁿ nn-n (nn-pure ⊕ⁿ nn-ex 0 true (RAnnot e T))
    nn-lam (RBinOp op a b) = nn-pure ⊕ⁿ nn-pure ⊕ⁿ nn-n (nn-pure ⊕ⁿ nn-ex 0 true (RBinOp op a b))
    nn-lam (RNeg e) = nn-pure ⊕ⁿ nn-pure ⊕ⁿ nn-n (nn-pure ⊕ⁿ nn-ex 0 true (RNeg e))

    nn-lhead : ∀ x v → NN (lhead x v)
    nn-lhead x v = nn-word "let" ⊕ⁿ nn-pure ⊕ⁿ nn-word x ⊕ⁿ nn-pure ⊕ⁿ nn-pure ⊕ⁿ nn-gn (nn-pure ⊕ⁿ nn-ex 0 true v)

    nn-let : ∀ x v b → NN (plet′ x v b)
    nn-let x v (RLet y v′ c) = nn-lhead x v ⊕ⁿ nn-pure ⊕ⁿ nn-word "in" ⊕ⁿ nn-pure ⊕ⁿ nn-let y v′ c
    nn-let x v (RVar bx) = nn-lhead x v ⊕ⁿ nn-pure ⊕ⁿ nn-word "in" ⊕ⁿ nn-pure ⊕ⁿ nn-ex 0 true (RVar bx)
    nn-let x v (RQualified bx bq) = nn-lhead x v ⊕ⁿ nn-pure ⊕ⁿ nn-word "in" ⊕ⁿ nn-pure ⊕ⁿ nn-ex 0 true (RQualified bx bq)
    nn-let x v (RResolved bn) = nn-lhead x v ⊕ⁿ nn-pure ⊕ⁿ nn-word "in" ⊕ⁿ nn-pure ⊕ⁿ nn-ex 0 true (RResolved bn)
    nn-let x v (RApp bf ba) = nn-lhead x v ⊕ⁿ nn-pure ⊕ⁿ nn-word "in" ⊕ⁿ nn-pure ⊕ⁿ nn-ex 0 true (RApp bf ba)
    nn-let x v (RLam bx be) = nn-lhead x v ⊕ⁿ nn-pure ⊕ⁿ nn-word "in" ⊕ⁿ nn-pure ⊕ⁿ nn-ex 0 true (RLam bx be)
    nn-let x v (RPair ba bb) = nn-lhead x v ⊕ⁿ nn-pure ⊕ⁿ nn-word "in" ⊕ⁿ nn-pure ⊕ⁿ nn-ex 0 true (RPair ba bb)
    nn-let x v (RDestruct bs bx bel by ber) = nn-lhead x v ⊕ⁿ nn-pure ⊕ⁿ nn-word "in" ⊕ⁿ nn-pure ⊕ⁿ nn-ex 0 true (RDestruct bs bx bel by ber)
    nn-let x v RUnit = nn-lhead x v ⊕ⁿ nn-pure ⊕ⁿ nn-word "in" ⊕ⁿ nn-pure ⊕ⁿ nn-ex 0 true RUnit
    nn-let x v (RInt bz) = nn-lhead x v ⊕ⁿ nn-pure ⊕ⁿ nn-word "in" ⊕ⁿ nn-pure ⊕ⁿ nn-ex 0 true (RInt bz)
    nn-let x v (RFloat bi bfr bl) = nn-lhead x v ⊕ⁿ nn-pure ⊕ⁿ nn-word "in" ⊕ⁿ nn-pure ⊕ⁿ nn-ex 0 true (RFloat bi bfr bl)
    nn-let x v (RAnnot be bT) = nn-lhead x v ⊕ⁿ nn-pure ⊕ⁿ nn-word "in" ⊕ⁿ nn-pure ⊕ⁿ nn-ex 0 true (RAnnot be bT)
    nn-let x v (RBinOp bop ba bb) = nn-lhead x v ⊕ⁿ nn-pure ⊕ⁿ nn-word "in" ⊕ⁿ nn-pure ⊕ⁿ nn-ex 0 true (RBinOp bop ba bb)
    nn-let x v (RNeg be) = nn-lhead x v ⊕ⁿ nn-pure ⊕ⁿ nn-word "in" ⊕ⁿ nn-pure ⊕ⁿ nn-ex 0 true (RNeg be)

  private
    nn-path : ∀ p → NN (path p)
    nn-path [] = nn-pure
    nn-path (x ∷ []) = nn-word x
    nn-path (x ∷ y ∷ ys) = nn-word x ⊕ⁿ nn-pure ⊕ⁿ nn-path (y ∷ ys)

    nn-spaced : ∀ ps → NN (spaced ps)
    nn-spaced [] = nn-pure
    nn-spaced (x ∷ xs) = nn-pure ⊕ⁿ nn-word x ⊕ⁿ nn-spaced xs

  -- | A declaration prints alike.
  nn-body : ∀ d → NN (pbody d)
  nn-body (DImport (mkImport p nothing)) = nn-word "import" ⊕ⁿ nn-pure ⊕ⁿ nn-path p
  nn-body (DImport (mkImport p (just a))) =
    nn-word "import" ⊕ⁿ nn-pure ⊕ⁿ nn-path p ⊕ⁿ nn-pure ⊕ⁿ nn-word "as" ⊕ⁿ nn-pure ⊕ⁿ nn-word a
  nn-body (DTypeAlias x ps A) =
    nn-word "type" ⊕ⁿ nn-pure ⊕ⁿ nn-word x ⊕ⁿ nn-spaced ps ⊕ⁿ nn-pure ⊕ⁿ nn-pure ⊕ⁿ nn-pure ⊕ⁿ nn-ty 0 true A
  nn-body (DSignature x A) =
    nn-word "signature" ⊕ⁿ nn-pure ⊕ⁿ nn-word x ⊕ⁿ nn-pure ⊕ⁿ nn-pure ⊕ⁿ nn-pure ⊕ⁿ nn-ty 0 true A
  nn-body (DTypeSig x A) = nn-name x ⊕ⁿ nn-pure ⊕ⁿ nn-pure ⊕ⁿ nn-pure ⊕ⁿ nn-ty 0 true A
  nn-body (DFunDef x e) =
    nn-name x ⊕ⁿ nn-spaced (proj₁ (lams e)) ⊕ⁿ nn-pure ⊕ⁿ nn-pure ⊕ⁿ nn-pure ⊕ⁿ nn-ex 0 true (proj₂ (lams e))

  private
    lead-nn : ∀ prev → NoNotes (lead prev [])
    lead-nn nothing  = nn-empty
    lead-nn (just _) = nn-empty

    ending-nn : ∀ prev → NoNotes (ending prev [])
    ending-nn prev = nn-empty

    gap-nn : ∀ prev d → NoNotes (gap prev d)
    gap-nn nothing  d = nn-empty
    gap-nn (just p) d with together p d
    ... | true  = nn-empty
    ... | false = nn-blank

  -- | The module, printed without trivia, has no comment.
  pdecls-nn : ∀ prev ds k → NoNotes (proj₁ (pdecls prev ds [] k))
  pdecls-nn prev []       k = subst (λ ns → NoNotes (ending prev ns)) (sym (tops-[] k (suc k ∸ k))) (ending-nn prev)
  pdecls-nn prev (d ∷ ds) k =
    nn-<> (gap-nn prev d)
      (nn-<> (subst (λ ns → NoNotes (lead prev ns)) (sym (tops-[] k (proj₂ (pdecl d [] k) ∸ k))) (lead-nn prev))
        (nn-<> (NN.quiet (nn-gn (nn-body d)) k) (nn-<> nn-newline (pdecls-nn (just d) ds (proj₂ (pdecl d [] k))))))
