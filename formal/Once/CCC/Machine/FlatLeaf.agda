-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Machine.FlatLeaf  (plan 0.123 α′ (f3c))
--
-- A DECODED BLOCK INPUT IS ITS LEAVES, IN PLACE. When the flat reader
-- (`readTyped`, D375) reads an arith block's input shape at `loc`, each typed
-- leaf `p` of the value it returns is the literal in the cell `flat-off p`
-- words past `loc` — the cell the block's code loads (D385's `Xmov-arg … k`).
-- This is the abstract half of the block's `R-input`; the concrete half is
-- the correspondence of those cells (`FlatCorr.heap-eq` / `stack-eq`).
------------------------------------------------------------------------

open import Once.CCC.FrameSemantics using (FrameSemantics)

module Once.CCC.Machine.FlatLeaf (FS : FrameSemantics) where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-assoc; +-identityʳ)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)

open import Once.Semantics.Machine using (⟦_⟧)
open import Once.Type using (FitsInReg; fits-int; fits-float)
open import Once.CCC.Machine.Locations using (ValueLocation; AtStack; AtDynamic)
open import Once.Memory.HeapAddress using (heap-loc)
open import Once.CCC.Machine.SMCore
open MemOps {FS} using (readLoc)
open AbstractExec {FS} using (readTyped; tsize; combine-typed; readTyped-int; readTyped-float)
open import Once.Arith.Machine.Shape
  using (InputShape; shape-unit; shape-int; shape-float; shape-pair; Path; here-int; here-flt; go-fst; go-snd; flat-off; shape-size)
open import Once.Arith.Machine.IR using (shape-as-type; numtype-as-type)
open import Once.Arith.Type using (NumType; NInt; NFloat)

-- the leaf a typed path names, in the machine's value
leafM : ∀ {sh n} → Path sh n → ⟦ shape-as-type sh ⟧ → ⟦ numtype-as-type n ⟧
leafM here-int   v       = v
leafM here-flt   v       = v
leafM (go-fst p) (x , _) = leafM p x
leafM (go-snd p) (_ , y) = leafM p y

-- the literal kind of a leaf
fitsN : (n : NumType) → FitsInReg (numtype-as-type n)
fitsN NInt   = fits-int
fitsN NFloat = fits-float

-- a shape's words are its type's
tsize-shape : ∀ sh → tsize (shape-as-type sh) ≡ shape-size sh
tsize-shape shape-unit       = refl
tsize-shape shape-int        = refl
tsize-shape shape-float      = refl
tsize-shape (shape-pair l r) = cong₂ _+_ (tsize-shape l) (tsize-shape r)

offset-0 : ∀ (loc : ValueLocation FS) → offsetLoc loc 0 ≡ loc
offset-0 (AtStack f k)              = refl
offset-0 (AtDynamic (heap-loc r o)) = refl

offset-+ : ∀ (loc : ValueLocation FS) a b → offsetLoc (offsetLoc loc a) b ≡ offsetLoc loc (a + b)
offset-+ (AtStack f k)              a b = cong (AtStack f) (trans (sym (+-assoc b a k)) (cong (_+ k) (+-comm′ b a)))
  where +-comm′ = Data.Nat.Properties.+-comm
        import Data.Nat.Properties
offset-+ (AtDynamic (heap-loc r o)) a b = cong (λ x → AtDynamic (heap-loc r x)) (trans (sym (+-assoc b a o)) (cong (_+ o) (Data.Nat.Properties.+-comm b a)))
  where import Data.Nat.Properties

private
  int-inv : ∀ (m : Maybe (StoredValue FS)) {v} → readTyped-int m ≡ just v → m ≡ just (SV-Lit fits-int v)
  int-inv (just (SV-Lit fits-int w)) eq = cong (λ x → just (SV-Lit fits-int x)) (just-injective eq)
  int-inv (just (SV-Lit fits-float _)) ()
  int-inv (just (SV-Ptr _)) ()
  int-inv (just (SV-Tag _)) ()
  int-inv (just (SV-Code _)) ()
  int-inv nothing ()

  flt-inv : ∀ (m : Maybe (StoredValue FS)) {v} → readTyped-float m ≡ just v → m ≡ just (SV-Lit fits-float v)
  flt-inv (just (SV-Lit fits-float w)) eq = cong (λ x → just (SV-Lit fits-float x)) (just-injective eq)
  flt-inv (just (SV-Lit fits-int _)) ()
  flt-inv (just (SV-Ptr _)) ()
  flt-inv (just (SV-Tag _)) ()
  flt-inv (just (SV-Code _)) ()
  flt-inv nothing ()

  pair-inv : ∀ {A B : _} (ma : Maybe ⟦ A ⟧) (mb : Maybe ⟦ B ⟧) {a b} → combine-typed ma mb ≡ just (a , b)
           → (ma ≡ just a) × (mb ≡ just b)
  pair-inv (just x) (just y) refl = refl , refl
  pair-inv (just x) nothing  ()
  pair-inv nothing  _        ()

-- THE LEMMA
leaf-at : ∀ {sh n} (p : Path sh n) (loc : ValueLocation FS) (ls : LocState FS) (a : ⟦ shape-as-type sh ⟧)
        → readTyped (shape-as-type sh) loc ls ≡ just a
        → readLoc ls (offsetLoc loc (flat-off p)) ≡ just (SV-Lit (fitsN n) (leafM p a))
leaf-at here-int loc ls a eq = trans (cong (readLoc ls) (offset-0 loc)) (int-inv (readLoc ls loc) eq)
leaf-at here-flt loc ls a eq = trans (cong (readLoc ls) (offset-0 loc)) (flt-inv (readLoc ls loc) eq)
leaf-at {shape-pair l r} (go-fst p) loc ls (x , y) eq =
  leaf-at p loc ls x (proj₁′ (pair-inv (readTyped (shape-as-type l) loc ls) _ eq))
  where proj₁′ = Data.Product.proj₁
        import Data.Product
leaf-at {shape-pair l r} (go-snd p) loc ls (x , y) eq =
  trans (cong (readLoc ls) (sym (trans (offset-+ loc (tsize (shape-as-type l)) (flat-off p))
                                        (cong (λ t → offsetLoc loc (t + flat-off p)) (tsize-shape l)))))
        (leaf-at p (offsetLoc loc (tsize (shape-as-type l))) ls y
                 (Data.Product.proj₂ (pair-inv (readTyped (shape-as-type l) loc ls) _ eq)))
  where import Data.Product
