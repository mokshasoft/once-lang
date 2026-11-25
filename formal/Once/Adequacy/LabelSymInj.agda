-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.LabelSymInj — plan 0.146 B1.7 step 3 (D466): ★ A DEFINED
-- LABEL'S SYMBOL IS THE LABEL, when its owner reads back.
--
-- `LabelSymbols` reads a counter label's index off its symbol (the decimal
-- after the last `_`), which is all master's image needs: its counter labels
-- are numbered apart image-wide. The linear core's image numbers its jump
-- labels per block, apart by their OWNER (`Lower.jl j k`, owner `nameOf j`),
-- so here the whole label is read back: the index as before, then the rest
-- of the rendering — `.Lonce_` / `.L_thunk_`, the owner's symbol, its path —
-- whose owner symbol `once-symbol-path` gives back when each part leads with
-- a non-digit (`SymbolInjective.once-symbol-path-injective-peel`).
------------------------------------------------------------------------

module Once.Adequacy.LabelSymInj where

open import Data.Char using (Char)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.List.Properties using (++-cancelˡ; ++-cancelʳ; ++-identityʳ; ∷-injective)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.AllPairs using (AllPairs; []; _∷_)
import Data.List.Relation.Unary.All
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.String using (String; toList) renaming (_++_ to _++ˢ_)
open import Data.String.Properties using (toList-injective)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst)
open import Once.Postulates using (toList-++)
open import Once.Spec.Name using (CanonicalName; module CanonicalName)
open import Once.CCC.Label using (Label; once; callee; sigop; LabelId; mkLabelId; e-thunk; e-fn; labelSym; showLabelId; module LabelId)
open import Once.Target.Symbol using (once-symbol-path)
open import Once.Target.SymbolInjective using (PeelS; once-symbol-path-injective-peel)
open import Once.Adequacy.LabelSymbols using (DefL; d-once; d-callee; lid-shape; idx-of-once; idx-of-thunk; showNat-inj; once-head; thunk-head; cnt≢fn)

------------------------------------------------------------------------
-- Labels whose owner reads back
------------------------------------------------------------------------

-- a label id with no path, each part of its owner led by a non-digit
GoodId : LabelId → Set
GoodId n = (LabelId.path n ≡ []) × All PeelS (CanonicalName.parts (LabelId.owner n))

GoodL : Label → Set
GoodL (once n)             = GoodId n
GoodL (callee (e-thunk n)) = GoodId n
GoodL (callee (e-fn f))    = All PeelS (CanonicalName.parts f)
GoodL (sigop _ _)          = ⊥

------------------------------------------------------------------------
-- A label id read back from its rendering behind a fixed prefix
------------------------------------------------------------------------

private
  ∷-tail : ∀ {a b : Char} {as bs : List Char} → a ∷ as ≡ b ∷ bs → as ≡ bs
  ∷-tail refl = refl

  ∷-head : ∀ {a b : Char} {as bs : List Char} → a ∷ as ≡ b ∷ bs → a ≡ b
  ∷-head refl = refl

lid-inj : ∀ (pre : String) (n m : LabelId) → GoodId n → GoodId m
        → toList (pre ++ˢ showLabelId n) ≡ toList (pre ++ˢ showLabelId m)
        → (last-eq : LabelId.idx n ≡ LabelId.idx m) → n ≡ m
lid-inj pre (mkLabelId o .[] i) (mkLabelId o′ .[] .i) (refl , po) (refl , po′) e refl =
  cong (λ x → mkLabelId x [] i)
    (once-symbol-path-injective-peel o o′ po po′
      (toList-injective _ _
        (trans (sym (++-identityʳ (toList (once-symbol-path o))))
          (trans (++-cancelˡ (toList pre) _ _
                   (++-cancelʳ ('_' ∷ toList (Once.Target.Symbol.showNat i)) _ _
                     (trans (sym (lid-shape pre (mkLabelId o [] i))) (trans e (lid-shape pre (mkLabelId o′ [] i))))))
                 (++-identityʳ (toList (once-symbol-path o′)))))))

private
  -- the index, from the last segment
  idx-once : ∀ n m → labelSym (once n) ≡ labelSym (once m) → LabelId.idx n ≡ LabelId.idx m
  idx-once n m e = showNat-inj (trans (sym (idx-of-once n)) (trans (cong (λ z → Once.Adequacy.LabelSymbols.last-seg (toList z)) e) (idx-of-once m)))

  idx-thunk : ∀ n m → labelSym (callee (e-thunk n)) ≡ labelSym (callee (e-thunk m)) → LabelId.idx n ≡ LabelId.idx m
  idx-thunk n m e = showNat-inj (trans (sym (idx-of-thunk n)) (trans (cong (λ z → Once.Adequacy.LabelSymbols.last-seg (toList z)) e) (idx-of-thunk m)))

  -- `.Lonce_…` is no `.L_thunk_…` (their third characters)
  once≢thunk : ∀ n m → labelSym (once n) ≢ labelSym (callee (e-thunk m))
  once≢thunk n m e =
    case′ (∷-head (∷-tail (∷-tail (trans (sym (toList-++ ".Lonce_" (showLabelId n))) (trans (cong toList e) (toList-++ ".L_thunk_" (showLabelId m)))))))
    where case′ : 'o' ≡ '_' → ⊥
          case′ ()

-- ★ two defined labels whose owners read back, with one symbol, are one label
sym-inj : ∀ {x y} → DefL x → DefL y → GoodL x → GoodL y → labelSym x ≡ labelSym y → x ≡ y
sym-inj {once n} {once m} d-once d-once gx gy e =
  cong once (lid-inj ".Lonce_" n m gx gy (cong toList e) (idx-once n m e))
sym-inj {once n} {callee (e-thunk m)} d-once d-callee gx gy e = ⊥-elim (once≢thunk n m e)
sym-inj {once n} {callee (e-fn f)} d-once d-callee gx gy e = ⊥-elim (cnt≢fn f (once-head n) e)
sym-inj {callee (e-thunk n)} {once m} d-callee d-once gx gy e = ⊥-elim (once≢thunk m n (sym e))
sym-inj {callee (e-thunk n)} {callee (e-thunk m)} d-callee d-callee gx gy e =
  cong (λ z → callee (e-thunk z)) (lid-inj ".L_thunk_" n m gx gy (cong toList e) (idx-thunk n m e))
sym-inj {callee (e-thunk n)} {callee (e-fn f)} d-callee d-callee gx gy e = ⊥-elim (cnt≢fn f (thunk-head n) e)
sym-inj {callee (e-fn f)} {once m} d-callee d-once gx gy e = ⊥-elim (cnt≢fn f (once-head m) (sym e))
sym-inj {callee (e-fn f)} {callee (e-thunk m)} d-callee d-callee gx gy e = ⊥-elim (cnt≢fn f (thunk-head m) (sym e))
sym-inj {callee (e-fn f)} {callee (e-fn g)} d-callee d-callee gx gy e =
  cong (λ z → callee (e-fn z)) (once-symbol-path-injective-peel f g gx gy e)

-- …so distinct such labels have distinct symbols
syms-dst : ∀ {xs : List Label} → All DefL xs → All GoodL xs → AllPairs _≢_ xs → AllPairs _≢_ (map labelSym xs)
syms-dst []         []         []         = []
syms-dst (d ∷ ds) (g ∷ gs) (px ∷ pxs) = go d g ds gs px ∷ syms-dst ds gs pxs
  where
    go : ∀ {x ys} → DefL x → GoodL x → All DefL ys → All GoodL ys → All (x ≢_) ys → All (labelSym x ≢_) (map labelSym ys)
    go dx gx []         []         []         = []
    go dx gx (dy ∷ dys) (gy ∷ gys) (p ∷ ps) = (λ e → p (sym-inj dx dy gx gy e)) ∷ go dx gx dys gys ps
