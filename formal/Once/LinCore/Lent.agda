-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.LinCore.Lent — plan 0.157 S2, D498 (decided by the user): THE
-- LENT-CALLED TYPES of a program. A many-use closure's LENT entry is needed
-- only where a lent call through a code word (`bev`, the image's `icallω`)
-- at its type is reachable: in the table's bodies, in the main term, in a
-- closure's owned entry, in a fold's algebra or an observation, and in the
-- lent body of a closure whose own type is lent-called — a least fixpoint.
--
-- The facts follow the image's blocks (`Image.compᴵ`): a block's own lent
-- calls are those of its term INLINE (`shallow`: a closure's body, a fold's
-- algebra and an observation are blocks of their own); the blocks a term
-- names (`inner`) add theirs, unconditionally except a many-use closure's
-- lent body, which counts only if its closure's type is lent-called.
--
-- The set is computed by iteration and CHECKED closed; were the check to
-- fail, every target type is taken instead (closed by construction). So
-- `closed` needs no bound on the iteration.
------------------------------------------------------------------------

open import Once.Spec.Numerics using (TargetNum)

module Once.LinCore.Lent (fmt : TargetNum) where

open import Data.Bool using (Bool; true; false; _∨_; _∧_; not; if_then_else_; T)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁻; ∈-++⁺ˡ; ∈-++⁺ʳ)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; trans)

open import Once.LinCore.Core fmt
open import Once.LinCore.TyEq fmt using (eqT; eqT-refl)

------------------------------------------------------------------------
-- 1. THE FACTS: a lent call at a type, unconditionally or under a closure's type.
------------------------------------------------------------------------

Fact : Set
Fact = Maybe LTy × LTy

uncond : List LTy → List Fact
uncond []       = []
uncond (t ∷ ts) = (nothing , t) ∷ uncond ts

under : LTy → List LTy → List Fact
under C []       = []
under C (t ∷ ts) = (just C , t) ∷ under C ts

-- a block's own lent calls: its term's, inline
shallow : ∀ {Γ E A B} → Tm Γ E A B → List LTy
shallow (f ∘l g)      = shallow f ++ shallow g
shallow (f ⊗l g)      = shallow f ++ shallow g
shallow (lcase f g)   = shallow f ++ shallow g
shallow (liter f _)   = shallow f
shallow (lend f)      = shallow f
shallow (blift f)     = shallow f
shallow (bfst f)      = shallow f
shallow (bsnd f)      = shallow f
shallow (bcaseE f g)  = shallow f ++ shallow g
shallow (bout f)      = shallow f
shallow (bev {g = g} {A} {B}) = Fn many g A B ∷ []
{-# CATCHALL #-}
shallow _             = []

-- an owned entry's own lent calls, by its certificate (`o-ev` applies owned: none)
shallowO : ∀ {Γ X A B} (b : Tm Γ X A B) → Own b → List LTy
shallowO b o-bg                           = shallow b
shallowO _ o-ev                           = []
shallowO (bfst f) (o-fst o)               = shallowO f o
shallowO (bsnd f) (o-snd o)               = shallowO f o
shallowO (bfst f ∘l bsnd g) (o-split p q) = shallowO f p ++ shallowO g q
shallowO (lcase f g) (o-case p q)         = shallowO f p ++ shallowO g q
shallowO ((bfst f ⊗l bsnd g) ∘l s) (o-fork p q) = shallowO f p ++ shallowO g q ++ shallow s
shallowO (blift g ∘l t) (o-lift p)        = shallow g ++ shallowO t p
shallowO (t ∘l blift f) (o-pre p)         = shallowO t p ++ shallow f

------------------------------------------------------------------------
-- 2. THE LEAST SET, computed and checked.
------------------------------------------------------------------------

elemT : LTy → List LTy → Bool
elemT t []       = false
elemT t (u ∷ us) = eqT t u ∨ elemT t us

-- a fact's condition holds in a set
holds : Maybe LTy → List LTy → Bool
holds nothing  l = true
holds (just c) l = elemT c l

private
  add : List LTy → Fact → List LTy → List LTy
  add l (c , t) acc = if holds c l ∧ not (elemT t acc) then t ∷ acc else acc

  stepL : List Fact → List LTy → List LTy
  stepL []       l = l
  stepL (x ∷ fs) l = add l x (stepL fs l)

  iter : ℕ → List Fact → List LTy → List LTy
  iter zero    fs l = l
  iter (suc k) fs l = iter k fs (stepL fs l)

  targets : List Fact → List LTy
  targets []             = []
  targets ((_ , t) ∷ fs) = t ∷ targets fs

-- the set is closed when every fact whose condition holds has its type in it
closed? : List Fact → List LTy → Bool
closed? []             l = true
closed? ((c , t) ∷ fs) l = (not (holds c l) ∨ elemT t l) ∧ closed? fs l

lentTys : List Fact → List LTy
lentTys fs = let l = iter (suc (length fs)) fs [] in if closed? fs l then l else targets fs

------------------------------------------------------------------------
-- 3. ★ CLOSED: a fact whose condition holds names a lent-called type.
------------------------------------------------------------------------

private
  ∧-l : ∀ {a b} → (a ∧ b) ≡ true → a ≡ true
  ∧-l {true} e = refl

  ∧-r : ∀ {a b} → (a ∧ b) ≡ true → b ≡ true
  ∧-r {true} e = e

  ∨-r : ∀ {a b} → (not a ∨ b) ≡ true → a ≡ true → b ≡ true
  ∨-r {true} e refl = e

  ∨-l′ : ∀ a {b} → a ≡ true → (a ∨ b) ≡ true
  ∨-l′ true e = refl

  ∨-r′ : ∀ a {b} → b ≡ true → (a ∨ b) ≡ true
  ∨-r′ true  e = refl
  ∨-r′ false e = e

  closed-∈ : ∀ fs l {c t} → closed? fs l ≡ true → (c , t) ∈ fs → holds c l ≡ true → elemT t l ≡ true
  closed-∈ ((c , t) ∷ fs) l e (here refl) h = ∨-r (∧-l {not (holds c l) ∨ elemT t l} e) h
  closed-∈ ((c′ , t′) ∷ fs) l e (there m) h = closed-∈ fs l (∧-r {not (holds c′ l) ∨ elemT t′ l} e) m h

  elem-self : ∀ t us → elemT t (t ∷ us) ≡ true
  elem-self t us = ∨-l′ (eqT t t) (eqT-refl t)

  targets-∈ : ∀ fs {c t} → (c , t) ∈ fs → elemT t (targets fs) ≡ true
  targets-∈ ((c , t) ∷ fs) (here refl) = elem-self t (targets fs)
  targets-∈ ((c′ , t′) ∷ fs) {t = t} (there m) = ∨-r′ (eqT t t′) (targets-∈ fs m)

  by-check : ∀ fs l (b : Bool) → closed? fs l ≡ b → ∀ {c t} → (c , t) ∈ fs
           → holds c (if b then l else targets fs) ≡ true → elemT t (if b then l else targets fs) ≡ true
  by-check fs l true  e m h = closed-∈ fs l e m h
  by-check fs l false e m h = targets-∈ fs m

lent-closed : ∀ fs {c t} → (c , t) ∈ fs → holds c (lentTys fs) ≡ true → elemT t (lentTys fs) ≡ true
lent-closed fs m h = by-check fs l (closed? fs l) refl m h
  where l = iter (suc (length fs)) fs []

