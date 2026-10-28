-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.OptimizeLinked — THE OPTIMIZER CALLS NOTHING NEW
-- (plan 0.39 C).
--
-- A term is linked when each call it makes names a table entry at its
-- types and each FFI operation it uses is declared (`Program.Linked`). Every
-- rule of `optimize` builds its result from parts of its input and from
-- formers that call nothing (`id`, `terminal`, `initial`), so an optimized
-- linked term is linked, against the same table and signatures.
------------------------------------------------------------------------

module Once.Adequacy.OptimizeLinked where

open import Data.Bool using (true; false)
open import Data.List using (List)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (refl)
open import Relation.Nullary using (yes; no)

open import Once.IR
open import Once.IRTy using (_≟IRTy_; fits-int; fits-float)
import Once.IRTy as II
open import Once.Type.DecEq using (_≟T_)
open import Once.Spec.Type using () renaming (Void to VoidT)
open import Once.Denotation.Program using (IRFun; Linked)
open import Once.Contract using (ISig)
open import Once.Optimize

module _ (Σ : ISig) (tbl : List IRFun) where
  private
    L : ∀ {A B} → IR A B → Set
    L = Linked Σ tbl

    fst-linked : ∀ {A B C} (f : IR A (B II.* C)) → L f → L (optimize-fst f)
    fst-linked f lf with pairView f
    ... | is-pair p h = proj₁ lf
    ... | is-other-pair .f = tt , lf

    snd-linked : ∀ {A B C} (f : IR A (B II.* C)) → L f → L (optimize-snd f)
    snd-linked f lf with pairView f
    ... | is-pair p h = proj₂ lf
    ... | is-other-pair .f = tt , lf

    post-case-linked : ∀ {A B C D} (h : IR A C) (k : IR B C) (f : IR D (A II.+ B)) → L (case h k) → L f
                     → L (optimize-post-case h k f)
    post-case-linked h k f lg lf with coprodView f
    ... | is-inl = proj₁ lg
    ... | is-inr = proj₂ lg
    ... | is-other-coprod .f = lg , lf

    compose-second-linked : ∀ {A B C} (g : IR B C) (f : IR A B) → L g → L f → L (optimize-compose-second g f)
    compose-second-linked g f lg lf with composeSecondView f
    ... | cs-id = lg
    ... | cs-initial = tt
    ... | cs-other .f = lg , lf

  compose-linked : ∀ {A B C} (g : IR B C) (f : IR A B) → L g → L f → L (optimize-compose g f)
  compose-linked g f lg lf with has-effect? f
  ... | true = lg , lf
  ... | false with composeFirstView g
  ...   | cf-id = lf
  ...   | cf-terminal = tt
  ...   | cf-fst = fst-linked f lf
  ...   | cf-snd = snd-linked f lf
  ...   | cf-case h k = post-case-linked h k f lg lf
  ...   | cf-other .g = compose-second-linked g f lg lf

  pair-linked : ∀ {A B C} (f : IR C A) (g : IR C B) → L f → L g → L (optimize-pair f g)
  pair-linked f g lf lg with fstSndView f | fstSndView g
  ... | fsv-fst      | fsv-snd      = tt
  ... | fsv-fst      | fsv-fst      = lf , lg
  ... | fsv-fst      | fsv-other .g = lf , lg
  ... | fsv-snd      | fsv-fst      = lf , lg
  ... | fsv-snd      | fsv-snd      = lf , lg
  ... | fsv-snd      | fsv-other .g = lf , lg
  ... | fsv-other .f | fsv-fst      = lf , lg
  ... | fsv-other .f | fsv-snd      = lf , lg
  ... | fsv-other .f | fsv-other .g = lf , lg

  case-linked : ∀ {A B C} (f : IR A C) (g : IR B C) → L f → L g → L (optimize-case f g)
  case-linked f g lf lg with inlInrView f | inlInrView g
  ... | iiv-inl      | iiv-inr      = tt
  ... | iiv-inl      | iiv-inl      = lf , lg
  ... | iiv-inl      | iiv-other .g = lf , lg
  ... | iiv-inr      | iiv-inl      = lf , lg
  ... | iiv-inr      | iiv-inr      = lf , lg
  ... | iiv-inr      | iiv-other .g = lf , lg
  ... | iiv-other .f | iiv-inl      = lf , lg
  ... | iiv-other .f | iiv-inr      = lf , lg
  ... | iiv-other .f | iiv-other .g = lf , lg

  -- | One pass keeps a term linked.
  opt-once-linked : ∀ {A B} (ir : IR A B) → L ir → L (optimize-once ir)
  struct-linked   : ∀ {A B} (ir : IR A B) → L ir → L (optimize-once-structural ir)

  opt-once-linked {A} {B} ir l with B ≟IRTy II.Unit
  ... | yes refl with has-effect? ir
  ...   | false = tt
  ...   | true  = struct-linked ir l
  opt-once-linked {A} {B} ir l | no _ with A ≟IRTy II.Void
  ...   | yes refl = tt
  ...   | no _     = struct-linked ir l

  struct-linked id         l = tt
  struct-linked (g ∘ f)    (lg , lf) = compose-linked (optimize-once g) (optimize-once f) (opt-once-linked g lg) (opt-once-linked f lf)
  struct-linked fst        l = tt
  struct-linked snd        l = tt
  struct-linked ⟨ f , g ⟩  (lf , lg) = pair-linked (optimize-once f) (optimize-once g) (opt-once-linked f lf) (opt-once-linked g lg)
  struct-linked (inl {A} {B}) l with A ≟IRTy II.Void
  ... | yes refl = tt
  ... | no _     = tt
  struct-linked (inr {A} {B}) l with B ≟IRTy II.Void
  ... | yes refl = tt
  ... | no _     = tt
  struct-linked (case f g) (lf , lg) = case-linked (optimize-once f) (optimize-once g) (opt-once-linked f lf) (opt-once-linked g lg)
  struct-linked terminal   l = tt
  struct-linked initial    l = tt
  struct-linked (curry f)  l = opt-once-linked f l
  struct-linked apply      l = tt
  struct-linked (SigOp {A} si) l with A ≟T VoidT
  ... | yes refl = tt
  ... | no _     = l
  struct-linked (const fits-int v)   l = tt
  struct-linked (const fits-float v) l = tt
  struct-linked (Call f)   l = l
  struct-linked (In _)     l = tt
  struct-linked (out-μ _)  l = tt
  struct-linked (Cata w alg)  l = opt-once-linked alg l
  struct-linked (Out _)    l = tt
  struct-linked (in-ν _)   l = tt
  struct-linked (Ana w c)  l = opt-once-linked c l
  struct-linked (Iter b)   l = opt-once-linked b l

  opt-n-linked : ∀ n {A B} (ir : IR A B) → L ir → L (optimize-n n ir)
  opt-n-linked zero    ir l = l
  opt-n-linked (suc n) ir l = opt-n-linked n (optimize-once ir) (opt-once-linked ir l)

  -- | The optimizer keeps a term linked.
  optimize-linked : ∀ {A B} (ir : IR A B) → L ir → L (optimize ir)
  optimize-linked = opt-n-linked 10
