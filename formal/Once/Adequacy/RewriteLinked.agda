-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.RewriteLinked — plan 0.103: THE ARITH PASS ADDS NO CALL.
--
-- `rewrite-ir` lifts maximal closed arithmetic subtrees into one block SigOp
-- and otherwise rebuilds the IR node for node. A lifted subtree becomes a
-- SigOp, which calls nothing; every other node keeps its calls. So a program
-- whose calls all resolve still does after the pass (`rewrite-ir-linked`,
-- formerly a postulate of `SourceTrace`).
------------------------------------------------------------------------

module Once.Adequacy.RewriteLinked where

import Once.Type.Core

import Once.Spec.Type
import Once.SigOp.Info

open import Data.Bool using (true; false)
open import Data.List using (List)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)

open import Once.IR
import Once.IRTy as II
open import Once.Denotation.Program using (IRFun; Linked; Declared)
open import Once.Contract using (ISig)
open import Once.Arith.Type using (NInt; NFloat)

private variable σ : ISig
open import Once.Arith.Machine.Rewrite using (rewrite-ir; try-lift; shape-of; block-as-ir; has-op; bare-at; prefix-at)
open import Once.Arith.Machine.Recognise using (recognise-body; recognise-body-float)
open import Once.Arith.Machine.IR using (ArithBlock; MArithIR; shape-as-type)
open import Once.Arith.SigOp.Block using (block-info)

private
  block-linked : ∀ (tbl : List IRFun) {A sh n} (eq : A ≡ II.⌊ shape-as-type sh ⌋) (body : MArithIR sh n)
               → Linked σ tbl (block-as-ir eq body)
  block-linked {σ = σ} tbl eq body =
    subst′ eq (block-info body) (block-decl body)
    where
      subst′ : ∀ {A : II.IRTy} {T B : Once.Spec.Type.Type} (e : A ≡ II.⌊ T ⌋) (si : Once.SigOp.Info.SigOpInfo T B)
             → Declared σ si → Linked σ tbl (subst (λ U → IR U II.⌊ B ⌋) (Relation.Binary.PropositionalEquality.sym e) (SigOp si))
      subst′ refl si d = d
      -- an arith block is the compiler's: it owes no declaration
      block-decl : ∀ {sh n} (b : MArithIR sh n) → Declared σ (block-info b)
      block-decl {n = NInt}   b = tt
      block-decl {n = NFloat} b = tt

private
  linked-subst : ∀ (tbl : List IRFun) {T T′ B : II.IRTy} (eq : T ≡ T′) (x : IR T B)
               → Linked σ tbl x → Linked σ tbl (subst (λ U → IR U B) eq x)
  linked-subst tbl refl x l = l

  JustLinked : ISig → ∀ (tbl : List IRFun) {A B} → Maybe (IR A B × ArithBlock) → Set
  JustLinked σ tbl nothing          = ⊤
  JustLinked σ tbl (just (ir′ , _)) = Linked σ tbl ir′

-- A lifted subtree is a block SigOp: it calls nothing.
try-lift-linked : ∀ (tbl : List IRFun) {A B} (ir : IR A B) → JustLinked σ tbl (try-lift ir)
try-lift-linked tbl {A} {II.Int} ir with shape-of A
... | nothing = tt
... | just (sh , eq) with recognise-body sh ir
...   | nothing = tt
...   | just body with has-op body
...     | false = tt
...     | true  = block-linked tbl eq body
try-lift-linked tbl {A} {II.Float} ir with shape-of A
... | nothing = tt
... | just (sh , eq) with recognise-body-float sh ir
...   | nothing = tt
...   | just body with has-op body
...     | false = tt
...     | true  = block-linked tbl eq body
try-lift-linked tbl {A} {II.Unit}       ir = tt
try-lift-linked tbl {A} {II.Void}       ir = tt
try-lift-linked tbl {A} {_ II.* _}      ir = tt
try-lift-linked tbl {A} {_ II.+ _}      ir = tt
try-lift-linked tbl {A} {_ II.⇛ _}      ir = tt
try-lift-linked tbl {A} {II.μ-type _}   ir = tt
try-lift-linked tbl {A} {II.ν-type _}   ir = tt

-- Plan 0.108: a bare primitive is lifted to a block (which owes no
-- declaration), or stays the declared SigOp it was.
bare-linked : ∀ (tbl : List IRFun) {X Y} (si : Once.SigOp.Info.SigOpInfo X Y) → Linked σ tbl (SigOp si)
            → ∀ (d : Maybe (IR II.⌊ X ⌋ II.⌊ Y ⌋ × ArithBlock)) → JustLinked σ tbl d
            → Linked σ tbl (proj₁ (bare-at si d))
bare-linked tbl si l (just _) lk = lk
bare-linked tbl si l nothing  _  = l

-- THE PASS KEEPS A PROGRAM LINKED.
-- (a chain's head lifted as a block, plan 0.129 B4)
prefix-linked : ∀ (tbl : List IRFun) {A X B C} (g : IR B C) (f₁ : IR X B) (f₂ : IR A X) (f : IR A B) → f ≡ f₁ ∘ f₂
              → Linked σ tbl g → Linked σ tbl f
              → ∀ (d : Maybe (IR X C × ArithBlock)) → JustLinked σ tbl d
              → Linked σ tbl (proj₁ (prefix-at g f₁ f₂ f d))
-- THE PASS KEEPS A PROGRAM LINKED.
rewrite-ir-linked : ∀ (tbl : List IRFun) {A B} (ir : IR A B) → Linked σ tbl ir → Linked σ tbl (proj₁ (rewrite-ir ir))
rewrite-ir-linked tbl ir l with try-lift ir | try-lift-linked tbl ir
... | just (ir′ , blk) | lk = lk
rewrite-ir-linked tbl id           l        | nothing | _ = tt
rewrite-ir-linked tbl (g ∘ f@(f₁ ∘ f₂)) (lg , lf) | nothing | _ =
  prefix-linked tbl g f₁ f₂ f refl lg lf (try-lift (g ∘ f₁)) (try-lift-linked tbl (g ∘ f₁))
rewrite-ir-linked tbl (g ∘ f@id) (lg , lf) | nothing | _ = rewrite-ir-linked tbl g lg , rewrite-ir-linked tbl f lf
rewrite-ir-linked tbl (g ∘ f@(⟨ _ , _ ⟩)) (lg , lf) | nothing | _ = rewrite-ir-linked tbl g lg , rewrite-ir-linked tbl f lf
rewrite-ir-linked tbl (g ∘ f@fst) (lg , lf) | nothing | _ = rewrite-ir-linked tbl g lg , rewrite-ir-linked tbl f lf
rewrite-ir-linked tbl (g ∘ f@snd) (lg , lf) | nothing | _ = rewrite-ir-linked tbl g lg , rewrite-ir-linked tbl f lf
rewrite-ir-linked tbl (g ∘ f@(inl {P} {Q})) (lg , lf) | nothing | _ = rewrite-ir-linked tbl g lg , tt
rewrite-ir-linked tbl (g ∘ f@(inr {P} {Q})) (lg , lf) | nothing | _ = rewrite-ir-linked tbl g lg , tt
rewrite-ir-linked tbl (g ∘ f@(case _ _)) (lg , lf) | nothing | _ = rewrite-ir-linked tbl g lg , rewrite-ir-linked tbl f lf
rewrite-ir-linked tbl (g ∘ f@(terminal {P})) (lg , lf) | nothing | _ = rewrite-ir-linked tbl g lg , tt
rewrite-ir-linked tbl (g ∘ f@initial) (lg , lf) | nothing | _ = rewrite-ir-linked tbl g lg , rewrite-ir-linked tbl f lf
rewrite-ir-linked tbl (g ∘ f@(curry _)) (lg , lf) | nothing | _ = rewrite-ir-linked tbl g lg , rewrite-ir-linked tbl f lf
rewrite-ir-linked tbl (g ∘ f@(apply {P} {Q})) (lg , lf) | nothing | _ = rewrite-ir-linked tbl g lg , rewrite-ir-linked tbl f lf
rewrite-ir-linked tbl (g ∘ f@(In _)) (lg , lf) | nothing | _ = rewrite-ir-linked tbl g lg , tt
rewrite-ir-linked tbl (g ∘ f@(out-μ _)) (lg , lf) | nothing | _ = rewrite-ir-linked tbl g lg , rewrite-ir-linked tbl f lf
rewrite-ir-linked tbl (g ∘ f@(Cata _ _)) (lg , lf) | nothing | _ = rewrite-ir-linked tbl g lg , rewrite-ir-linked tbl f lf
rewrite-ir-linked tbl (g ∘ f@(Out _)) (lg , lf) | nothing | _ = rewrite-ir-linked tbl g lg , rewrite-ir-linked tbl f lf
rewrite-ir-linked tbl (g ∘ f@(in-ν _)) (lg , lf) | nothing | _ = rewrite-ir-linked tbl g lg , tt
rewrite-ir-linked tbl (g ∘ f@(Ana _ _)) (lg , lf) | nothing | _ = rewrite-ir-linked tbl g lg , rewrite-ir-linked tbl f lf
rewrite-ir-linked tbl (g ∘ f@(Iter _)) (lg , lf) | nothing | _ = rewrite-ir-linked tbl g lg , rewrite-ir-linked tbl f lf
rewrite-ir-linked tbl (g ∘ f@(SigOp _)) (lg , lf) | nothing | _ = rewrite-ir-linked tbl g lg , rewrite-ir-linked tbl f lf
rewrite-ir-linked tbl (g ∘ f@(Call _)) (lg , lf) | nothing | _ = rewrite-ir-linked tbl g lg , rewrite-ir-linked tbl f lf
rewrite-ir-linked tbl (g ∘ f@(const _ _)) (lg , lf) | nothing | _ = rewrite-ir-linked tbl g lg , rewrite-ir-linked tbl f lf
rewrite-ir-linked tbl fst          l        | nothing | _ = tt
rewrite-ir-linked tbl snd          l        | nothing | _ = tt
rewrite-ir-linked tbl ⟨ f , g ⟩    (lf , lg) | nothing | _ = rewrite-ir-linked tbl f lf , rewrite-ir-linked tbl g lg
rewrite-ir-linked tbl inl          l        | nothing | _ = tt
rewrite-ir-linked tbl inr          l        | nothing | _ = tt
rewrite-ir-linked tbl (case f g)   (lf , lg) | nothing | _ = rewrite-ir-linked tbl f lf , rewrite-ir-linked tbl g lg
rewrite-ir-linked tbl terminal     l        | nothing | _ = tt
rewrite-ir-linked tbl initial      l        | nothing | _ = tt
rewrite-ir-linked tbl (curry f)    l        | nothing | _ = rewrite-ir-linked tbl f l
rewrite-ir-linked tbl apply        l        | nothing | _ = tt
rewrite-ir-linked tbl (In w)       l        | nothing | _ = tt
rewrite-ir-linked tbl (out-μ w)    l        | nothing | _ = tt
rewrite-ir-linked tbl (Cata w f)   l        | nothing | _ = rewrite-ir-linked tbl f l
rewrite-ir-linked tbl (Out w)      l        | nothing | _ = tt
rewrite-ir-linked tbl (in-ν w)     l        | nothing | _ = tt
rewrite-ir-linked tbl (Ana w f)    l        | nothing | _ = rewrite-ir-linked tbl f l
rewrite-ir-linked tbl (Iter f)     l        | nothing | _ = rewrite-ir-linked tbl f l
rewrite-ir-linked tbl (const p v)  l        | nothing | _ = tt
rewrite-ir-linked tbl (SigOp si)   l        | nothing | _ = bare-linked tbl si l (try-lift (SigOp si ∘ id)) (try-lift-linked tbl (SigOp si ∘ id))
rewrite-ir-linked tbl (Call f)     l        | nothing | _ = l

prefix-linked tbl g f₁ f₂ f e lg lf nothing _ = rewrite-ir-linked tbl g lg , rewrite-ir-linked tbl f lf
prefix-linked tbl g f₁ f₂ .(f₁ ∘ f₂) refl lg (l₁ , l₂) (just _) lk = lk , rewrite-ir-linked tbl f₂ l₂
