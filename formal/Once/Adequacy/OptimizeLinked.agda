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
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (Dec; yes; no)

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

    compose-second-linked : ∀ {A B C} (g : IR B C) (f : IR A B) → L g → L f → (v : ComposeSecondView f)
                          → L (compose-second-aux g f v)
    compose-second-linked g _ lg lf cs-id        = lg
    compose-second-linked g _ lg lf cs-initial   = tt
    compose-second-linked g _ lg lf (cs-other f) = lg , lf

    fst-pair-linked : ∀ {A B C} (a : IR A B) (b : IR A C) → L a × L b → ∀ q → L (fst-pair a b q)
    fst-pair-linked a b l true  = tt , l
    fst-pair-linked a b l false = proj₁ l

    fst-chain-pair-linked : ∀ {A X B C} (a : IR X B) (b : IR X C) (k : IR A X) → (L a × L b) × L k
                          → ∀ q → L (fst-chain-pair a b k q)
    fst-chain-pair-linked a b k l true  = tt , l
    fst-chain-pair-linked a b k l false = proj₁ (proj₁ l) , proj₂ l

    fst-chain-aux-linked : ∀ {A X B C} (p : IR X (B II.* C)) (k : IR A X) → L p × L k → (v : PairView p) → L (fst-chain-aux p k v)
    fst-chain-aux-linked _ k l (is-pair a b)     = fst-chain-pair-linked a b k l (has-effect? b)
    fst-chain-aux-linked _ k l (is-other-pair p) = tt , l

    fst-chain-linked : ∀ {A B C} (f : IR A (B II.* C)) → L f → (w : ChainView f) → L (fst-chain f w)
    fst-chain-linked _ l (is-comp p k) = fst-chain-aux-linked p k l (pairView p)
    fst-chain-linked _ l (not-comp f)  = compose-second-linked fst f tt l (composeSecondView f)

    fst-linked : ∀ {A B C} (f : IR A (B II.* C)) → L f → (v : PairView f) → L (fst-aux f v)
    fst-linked _ l (is-pair a b)     = fst-pair-linked a b l (has-effect? b)
    fst-linked _ l (is-other-pair f) = fst-chain-linked f l (chainView f)

    snd-pair-linked : ∀ {A B C} (a : IR A B) (b : IR A C) → L a × L b → ∀ q → L (snd-pair a b q)
    snd-pair-linked a b l true  = tt , l
    snd-pair-linked a b l false = proj₂ l

    snd-chain-pair-linked : ∀ {A X B C} (a : IR X B) (b : IR X C) (k : IR A X) → (L a × L b) × L k
                          → ∀ q → L (snd-chain-pair a b k q)
    snd-chain-pair-linked a b k l true  = tt , l
    snd-chain-pair-linked a b k l false = proj₂ (proj₁ l) , proj₂ l

    snd-chain-aux-linked : ∀ {A X B C} (p : IR X (B II.* C)) (k : IR A X) → L p × L k → (v : PairView p) → L (snd-chain-aux p k v)
    snd-chain-aux-linked _ k l (is-pair a b)     = snd-chain-pair-linked a b k l (has-effect? a)
    snd-chain-aux-linked _ k l (is-other-pair p) = tt , l

    snd-chain-linked : ∀ {A B C} (f : IR A (B II.* C)) → L f → (w : ChainView f) → L (snd-chain f w)
    snd-chain-linked _ l (is-comp p k) = snd-chain-aux-linked p k l (pairView p)
    snd-chain-linked _ l (not-comp f)  = compose-second-linked snd f tt l (composeSecondView f)

    snd-linked : ∀ {A B C} (f : IR A (B II.* C)) → L f → (v : PairView f) → L (snd-aux f v)
    snd-linked _ l (is-pair a b)     = snd-pair-linked a b l (has-effect? a)
    snd-linked _ l (is-other-pair f) = snd-chain-linked f l (chainView f)

    post-case-chain-aux-linked : ∀ {A B C D X} (h : IR A C) (k : IR B C) (p : IR X (A II.+ B)) (m : IR D X)
                               → L (case h k) → L p × L m → (v : CoprodView p) → L (post-case-chain-aux h k p m v)
    post-case-chain-aux-linked h k _ m lg l is-inl              = proj₁ lg , proj₂ l
    post-case-chain-aux-linked h k _ m lg l is-inr              = proj₂ lg , proj₂ l
    post-case-chain-aux-linked h k _ m lg l (is-other-coprod p) = lg , l

    post-case-chain-linked : ∀ {A B C D} (h : IR A C) (k : IR B C) (f : IR D (A II.+ B)) → L (case h k) → L f
                           → (w : ChainView f) → L (post-case-chain h k f w)
    post-case-chain-linked h k _ lg l (is-comp p m) = post-case-chain-aux-linked h k p m lg l (coprodView p)
    post-case-chain-linked h k _ lg l (not-comp f)  = compose-second-linked (case h k) f lg l (composeSecondView f)

    post-case-linked : ∀ {A B C D} (h : IR A C) (k : IR B C) (f : IR D (A II.+ B)) → L (case h k) → L f
                     → (v : CoprodView f) → L (post-case-aux h k f v)
    post-case-linked h k _ lg lf is-inl              = proj₁ lg
    post-case-linked h k _ lg lf is-inr              = proj₂ lg
    post-case-linked h k _ lg lf (is-other-coprod f) = post-case-chain-linked h k f lg lf (chainView f)

    terminal-linked : ∀ {A B} (f : IR A B) → L f → ∀ q → L (terminal-drop f q)
    terminal-linked f lf true  = tt , lf
    terminal-linked f lf false = tt

    compose-aux-linked : ∀ {A B C} (g : IR B C) (f : IR A B) → L g → L f → (v : ComposeFirstView g) → L (compose-aux g f v)
    compose-aux-linked _ f lg lf cf-id         = lf
    compose-aux-linked _ f lg lf cf-terminal   = terminal-linked f lf (has-effect? f)
    compose-aux-linked _ f lg lf cf-fst        = fst-linked f lf (pairView f)
    compose-aux-linked _ f lg lf cf-snd        = snd-linked f lf (pairView f)
    compose-aux-linked _ f lg lf (cf-case h k) = post-case-linked h k f lg lf (coprodView f)
    compose-aux-linked _ f lg lf (cf-comp h k) = proj₁ lg , (proj₂ lg , lf)
    compose-aux-linked _ f lg lf (cf-other g)  = compose-second-linked g f lg lf (composeSecondView f)

  compose-linked : ∀ {A B C} (g : IR B C) (f : IR A B) → L g → L f → L (optimize-compose g f)
  compose-linked g f lg lf = compose-aux-linked g f lg lf (composeFirstView g)

  private
    eta-pair-linked : ∀ {A B} (f : IR (A II.* B) A) (g : IR (A II.* B) B) → L f → L g → ∀ x y → L (eta-pair f g x y)
    eta-pair-linked f g lf lg true  true  = tt
    eta-pair-linked f g lf lg true  false = lf , lg
    eta-pair-linked f g lf lg false _     = lf , lg

    pair-aux-linked : ∀ {A B C} (f : IR C A) (g : IR C B) → L f → L g → (d : Dec (C ≡ A II.* B)) → L (pair-aux f g d)
    pair-aux-linked f g lf lg (yes refl) = eta-pair-linked f g lf lg (fst-like-aux f (fstSndView f)) (snd-like-aux g (fstSndView g))
    pair-aux-linked f g lf lg (no _)     = lf , lg

    eta-case-linked : ∀ {A B} (f : IR A (A II.+ B)) (g : IR B (A II.+ B)) → L f → L g → ∀ x y → L (eta-case f g x y)
    eta-case-linked f g lf lg true  true  = tt
    eta-case-linked f g lf lg true  false = lf , lg
    eta-case-linked f g lf lg false _     = lf , lg

    case-aux-linked : ∀ {A B C} (f : IR A C) (g : IR B C) → L f → L g → (d : Dec (C ≡ A II.+ B)) → L (case-aux f g d)
    case-aux-linked f g lf lg (yes refl) = eta-case-linked f g lf lg (inl-like-aux f (inlInrView f)) (inr-like-aux g (inlInrView g))
    case-aux-linked f g lf lg (no _)     = lf , lg

  pair-linked : ∀ {A B C} (f : IR C A) (g : IR C B) → L f → L g → L (optimize-pair f g)
  pair-linked {A} {B} {C} f g lf lg = pair-aux-linked f g lf lg (C ≟IRTy (A II.* B))

  case-linked : ∀ {A B C} (f : IR A C) (g : IR B C) → L f → L g → L (optimize-case f g)
  case-linked {A} {B} {C} f g lf lg = case-aux-linked f g lf lg (C ≟IRTy (A II.+ B))

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
  struct-linked inl        l = tt
  struct-linked inr        l = tt
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
