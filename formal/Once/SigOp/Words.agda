-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.SigOp.Words  (plan 0.123 α′ (f3c, A))
--
-- A SIGOP'S VALUE IS A WORD. `Int` is the target's word (D054): every
-- operation `norm`s, every literal is `fromℤ`, and since D397 the world's
-- answers are read at the target (`atTarget`). So whatever a Pure or answering
-- SigOp returns at an `Int` is below the target's modulus, given that its
-- `Int` inputs are (a block's `/ −1`, `%` read their dividend as a word).
--
-- `Words m A v`: the `Int` leaves of `v` (through products) are below `m`.
-- This is what the abstract machine's store keeps (`FlatStoreWF.sv-below`), and
-- what an arith block's input needs (`Shape.IntsBelow`, `normalize-preserves`).
------------------------------------------------------------------------

module Once.SigOp.Words where

open import Data.Nat using (ℕ; suc; pred; _<_; _^_; >-nonZero)
open import Data.Nat.DivMod using (m%n<n)
open import Data.Nat.Properties using (suc-pred)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)

open import Once.Spec.Type using (Type; var; Unit; Void; _*_; _+_; _⇒[_]_; μ; ν; Int; Float)
open import Once.Spec.Word using (Carrier)
import Once.Spec.Word as SW
import Once.IR.Semantics.Value Carrier Carrier as M
open import Once.Spec.Numerics using (TargetNum; module TargetNum)
open TargetNum using (int-bits; float-format; int-bits-pos)
open import Once.Type using (FitsInReg; fits-int; fits-float; fits-in-reg?)
open import Data.Sum using (inj₁; inj₂)
open import Data.Maybe using (nothing)
open import Once.Res using (Res; returns; stopped; mapRes)
open import Once.IR.Semantics.Boundary using (atTarget)
open import Once.SigOp.Info using (SigOpSem; blockV; ffiV; callsV; emitsV; haltsV; primV; semM-of)
open import Once.Arith.Prim using (primSem; p-add; p-sub; p-mul; p-div; p-mod; p-neg; p-fadd; p-fsub; p-fmul; p-fdiv; p-i2f; p-cmp; p-fneg; p-fcmp)
open import Once.Arith.Type using (NInt; NFloat)
open import Once.Arith.Machine.IR using (MArithIR; shape-as-type)
open import Once.Arith.Machine.Shape using (InputShape; shape-unit; shape-int; shape-float; shape-pair; ⟦_⟧S; IntsBelow)
open import Once.Arith.SigOp.BlockSem using (block-semM)
open import Once.Arith.SigOp.BlockSemBridge using (toWord; eval≡semM)
import Once.Arith.Machine.CompileCorrect as CC
open import Once.Word using (module WidthLaws)

------------------------------------------------------------------------
-- The predicates.
------------------------------------------------------------------------

-- the `Int` leaves of a value, through products, are below `m`
Words : ℕ → (A : Type) → M.⟦ A ⟧ → Set
Words m Int           v = v < m
Words m (A * B)       p = Words m A (proj₁ p) × Words m B (proj₂ p)
Words m (var _)       _ = ⊤
Words m Unit          _ = ⊤
Words m Void          _ = ⊤
Words m (A + B)       _ = ⊤
Words m (A ⇒[ _ ] B)  _ = ⊤
Words m (μ _)         _ = ⊤
Words m (ν _ _)       _ = ⊤
Words m Float         _ = ⊤

-- a register-fittable value: an `Int` is below `m`, a float pattern is free
LitWord : ℕ → ∀ {A} → FitsInReg A → M.⟦ A ⟧ → Set
LitWord m fits-int   v = v < m
LitWord m fits-float _ = ⊤

ResWord : ℕ → ∀ {B} → FitsInReg B → Res M.⟦ B ⟧ → Set
ResWord m f (returns v) = LitWord m f v
ResWord m f stopped     = ⊤

-- D451: a base value's EVERY `Int` leaf is below `m` — a sum's by its
-- alternative (`Words` leaves a sum free). What a value written in place
-- (`writeTyped`) needs of its words.
Leaves : ℕ → (A : Type) → M.⟦ A ⟧ → Set
Leaves m Int           v        = v < m
Leaves m (A * B)       p        = Leaves m A (proj₁ p) × Leaves m B (proj₂ p)
Leaves m (A + B)       (inj₁ a) = Leaves m A a
Leaves m (A + B)       (inj₂ b) = Leaves m B b
Leaves m (var _)       _        = ⊤
Leaves m Unit          _        = ⊤
Leaves m Void          _        = ⊤
Leaves m (A ⇒[ _ ] B)  _        = ⊤
Leaves m (μ _)         _        = ⊤
Leaves m (ν _ _)       _        = ⊤
Leaves m Float         _        = ⊤

ResLeaves : ℕ → (B : Type) → Res M.⟦ B ⟧ → Set
ResLeaves m B (returns v) = Leaves m B v
ResLeaves m B stopped     = ⊤

UnitSum : Type
UnitSum = Unit + Unit

unit-sum-leaves : ∀ m (v : M.⟦ UnitSum ⟧) → Leaves m UnitSum v
unit-sum-leaves m (inj₁ _) = tt
unit-sum-leaves m (inj₂ _) = tt

------------------------------------------------------------------------
-- At a target.
------------------------------------------------------------------------

module _ (tn : TargetNum) where

  private
    bits = int-bits tn
    module W  = SW.Width bits
    module WL = WidthLaws bits
      using (%ˢ-in-range; /ˢ-in-range)
    b : ℕ
    b = pred bits
    eqb : bits ≡ suc b
    eqb = sym (suc-pred bits {{>-nonZero (int-bits-pos tn)}})

  IM : ℕ
  IM = 2 ^ bits

  -- the world's value, read at the target, is a word (D397)
  atTarget-word : ∀ {B} (f : FitsInReg B) (v : M.⟦ B ⟧) → LitWord IM f (atTarget tn B v)
  atTarget-word fits-int   v = m%n<n v IM
  atTarget-word fits-float v = tt

  -- a shape's machine value as the block's input tree (the same words)
  fromM : ∀ (sh : InputShape) → M.⟦ shape-as-type sh ⟧ → ⟦ sh ⟧S
  fromM shape-unit       x = x
  fromM shape-int        x = x
  fromM shape-float      x = x
  fromM (shape-pair l r) p = fromM l (proj₁ p) , fromM r (proj₂ p)

  toWord-fromM : ∀ sh x → toWord tn sh (fromM sh x) ≡ x
  toWord-fromM shape-unit       x = refl
  toWord-fromM shape-int        x = refl
  toWord-fromM shape-float      x = refl
  toWord-fromM (shape-pair l r) p
    rewrite toWord-fromM l (proj₁ p) | toWord-fromM r (proj₂ p) = refl

  words-below : ∀ sh x → Words IM (shape-as-type sh) x → IntsBelow IM sh (fromM sh x)
  words-below shape-unit       x _       = tt
  words-below shape-int        x w       = w
  words-below shape-float      x _       = tt
  words-below (shape-pair l r) p (wl , wr) = words-below l (proj₁ p) wl , words-below r (proj₂ p) wr

  -- an `Int` block's value is a word, given word inputs
  block-word : ∀ {sh} (e : MArithIR sh NInt) (x : M.⟦ shape-as-type sh ⟧)
             → Words IM (shape-as-type sh) x → block-semM e tn x < IM
  block-word {sh} e x w =
    subst (_< IM)
      (trans (eval≡semM tn e (fromM sh x)) (Relation.Binary.PropositionalEquality.cong (block-semM e tn) (toWord-fromM sh x)))
      (CC.eval-in-range bits (float-format tn) b eqb e (fromM sh x) (words-below sh x w))
    where import Relation.Binary.PropositionalEquality

  -- THE LEMMA: a SigOp's value at a register-fittable codomain is a word
  semM-of-word : ∀ {A B} ans n (s : SigOpSem A B) (f : FitsInReg B) (x : M.⟦ A ⟧)
               → Words IM A x → ResWord IM f (semM-of ans n s tn x)
  semM-of-word ans n (blockV {n = NInt}   e refl refl) fits-int   x w = block-word e x w
  semM-of-word ans n (blockV {n = NFloat} e refl refl) fits-float x w = tt
  semM-of-word ans n (emitsV refl) () x w
  semM-of-word ans n (haltsV refl) () x w
  semM-of-word ans n (primV p-add)  fits-int   x w = m%n<n _ IM
  semM-of-word ans n (primV p-sub)  fits-int   x w = m%n<n _ IM
  semM-of-word ans n (primV p-mul)  fits-int   x w = m%n<n _ IM
  semM-of-word ans n (primV p-neg)  fits-int   x w = m%n<n _ IM
  semM-of-word ans n (primV p-div)  fits-int   x w = WL./ˢ-in-range b eqb (proj₁ x) (proj₂ x)
  semM-of-word ans n (primV p-mod)  fits-int   x w = WL.%ˢ-in-range b eqb (proj₁ x) (proj₂ x) (proj₁ w)
  semM-of-word ans n (primV p-fadd) fits-float x w = tt
  semM-of-word ans n (primV p-fsub) fits-float x w = tt
  semM-of-word ans n (primV p-fmul) fits-float x w = tt
  semM-of-word ans n (primV p-fdiv) fits-float x w = tt
  semM-of-word ans n (primV p-i2f)  fits-float x w = tt
  semM-of-word ans n (primV (p-cmp _)) () x w
  semM-of-word ans n (primV p-fneg)  fits-float x w = tt
  semM-of-word ans n (primV (p-fcmp _ _)) () x w
  semM-of-word {A} {B} ans n ffiV f x w with ans n A B x
  ... | returns v = atTarget-word f v
  ... | stopped   = tt
  semM-of-word {A} {B} ans n callsV f x w with ans n A B x
  ... | returns v = atTarget-word f v
  ... | stopped   = tt

  -- D451: the world's value, read at the target, has every leaf a word
  atTarget-leaves : ∀ (B : Type) (v : M.⟦ B ⟧) → Leaves IM B (atTarget tn B v)
  atTarget-leaves Int          v        = m%n<n v IM
  atTarget-leaves Float        v        = tt
  atTarget-leaves (A * B)      (x , y)  = atTarget-leaves A x , atTarget-leaves B y
  atTarget-leaves (A + B)      (inj₁ x) = atTarget-leaves A x
  atTarget-leaves (A + B)      (inj₂ y) = atTarget-leaves B y
  atTarget-leaves (var _)      v        = tt
  atTarget-leaves Unit         v        = tt
  atTarget-leaves Void         v        = tt
  atTarget-leaves (A ⇒[ _ ] B) v        = tt
  atTarget-leaves (μ _)        v        = tt
  atTarget-leaves (ν _ _)      v        = tt

  map-leaves : ∀ (B : Type) (r : Res M.⟦ B ⟧) → ResLeaves IM B (mapRes (atTarget tn B) r)
  map-leaves B (returns v) = atTarget-leaves B v
  map-leaves B stopped     = tt

  -- D451: a SigOp's value at a codomain that is not a register value has every leaf a word
  semM-of-leaves : ∀ {A B} ans n (s : SigOpSem A B) (x : M.⟦ A ⟧)
                 → fits-in-reg? B ≡ nothing → ResLeaves IM B (semM-of ans n s tn x)
  semM-of-leaves ans n (blockV {n = NInt}   e refl refl) x ()
  semM-of-leaves ans n (blockV {n = NFloat} e refl refl) x ()
  semM-of-leaves ans n (emitsV refl) x _ = tt
  semM-of-leaves ans n (haltsV refl) x _ = tt
  semM-of-leaves ans n (primV p-add)  x ()
  semM-of-leaves ans n (primV p-sub)  x ()
  semM-of-leaves ans n (primV p-mul)  x ()
  semM-of-leaves ans n (primV p-div)  x ()
  semM-of-leaves ans n (primV p-mod)  x ()
  semM-of-leaves ans n (primV p-neg)  x ()
  semM-of-leaves ans n (primV p-fadd) x ()
  semM-of-leaves ans n (primV p-fsub) x ()
  semM-of-leaves ans n (primV p-fmul) x ()
  semM-of-leaves ans n (primV p-fdiv) x ()
  semM-of-leaves ans n (primV p-i2f)  x ()
  semM-of-leaves ans n (primV (p-cmp o)) x _ = unit-sum-leaves IM (M.eraseᵍ (primSem (p-cmp o) tn x))
  semM-of-leaves ans n (primV p-fneg) x ()
  semM-of-leaves ans n (primV (p-fcmp h o)) x _ = unit-sum-leaves IM (M.eraseᵍ (primSem (p-fcmp h o) tn x))
  semM-of-leaves {A} {B} ans n ffiV   x _ = map-leaves B (ans n A B x)
  semM-of-leaves {A} {B} ans n callsV x _ = map-leaves B (ans n A B x)
