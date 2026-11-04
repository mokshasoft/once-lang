-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Machine.ValueRelocate — A COPIED VALUE IS VALID WHERE IT WAS COPIED
-- (plan 0.123 B.4 α).
--
-- Embedding a compound component copies its words (`FlatCopy`); this says the
-- copy is the value. A value of a flat type is its words in place (D375), so it
-- is valid at the destination when the destination's words are the source's,
-- word for word over its size. Its NODE components (μ, ν, closures) are pointer
-- words, copied too; the nodes they point to do not move, and stay valid by
-- the same-location `Transport`, given the copy wrote only into a block the old
-- allocator did not hold (every live cell is unchanged).
------------------------------------------------------------------------

open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.SMCore using (AbstractTrace)

module Once.CCC.Machine.ValueRelocate {FS : FrameSemantics} {prog : AbstractTrace} where

open import Data.Nat using (ℕ; zero; suc; _+_; _<_; _≤_; _⊔_; _∸_; z≤n; s≤s)
open import Data.Nat.Properties using (+-assoc; +-suc; m≤m+n; m≤n⊔m; m≤m⊔n; ≤-trans; +-monoˡ-≤; +-monoʳ-≤; +-comm; +-monoʳ-<; m+[n∸m]≡n)
open import Data.Maybe using (just)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Once.Memory.HeapAddress using (HeapRef; heap-loc)
import Once.Memory.HeapAddress
open import Once.CCC.Machine.LocMatchesMode using (LocMatchesMode)
open import Once.CCC.Machine.Locations using (ValueLocation; AtStack; AtDynamic)
open import Once.CCC.Machine.SMCore hiding (AllocMode; Stack; Heap; AbstractTrace)
open MemOps {FS}
open import Once.IR using (AllocMode; Stack; Heap)
open import Once.IRTy using (IRTy; Unit; Void; _*_; _⇛_; μ-type; ν-type; Int; Float; FitsInRegI; fits-int; fits-float) renaming (_+_ to _+ᵀ_)
open import Once.CCC.Codegen.Size using (size)
open import Once.CCC.Machine.ValueRel
open ClosureWellFormedBase {FS}
open ClosureWellFormedDef {FS} {prog} using (ValidAtWF; CellAt; module Transport; fo→valid; valid→fo)
open import Once.IRTy using (IRFunctor; WellFormedFI; ⟦_⟧TI; wf-K; wf-Id; wf-Sum; wf-Prod; base-Unit; base-Void; base-Int; base-Float; base-Prod; base-Sum)
open import Once.CCC.Machine.FlatWords {FS} {prog} using (offset-+; offset-0; offset-1)
open import Data.Unit using (tt)

private
  -- a node and a scalar are one word
  node-size : ∀ {C : IRTy} → IsNode C → size C ≡ 1
  node-size {μ-type _} _ = refl
  node-size {ν-type _} _ = refl
  node-size {_ ⇛ _}    _ = refl

  scalar-size : ∀ {C : IRTy} → FitsInRegI C → size C ≡ 1
  scalar-size fits-int   = refl
  scalar-size fits-float = refl

  -- a tag moves with its word (into a heap block: the copy's mode is Heap)
  tag-move : ∀ {m t} {s₁ s₂ : LocState FS} {l₁ l₂ : ValueLocation FS}
           → readLoc s₂ l₂ ≡ readLoc s₁ l₁ → SumTag m t s₁ l₁ → SumTag Heap t s₂ l₂
  tag-move {Heap}  e tg = trans e tg
  tag-move {Stack} e tg = trans e tg

  -- the source's words after a tag
  shift : ∀ (l : ValueLocation FS) j → offsetLoc (sucLoc l) j ≡ offsetLoc l (suc j)
  shift l j = trans (cong (λ z → offsetLoc z j) (sym (offset-1 l))) (offset-+ l 1 j)

-- The source is ANY location (a heap block's cell, or a frame slot: D374);
-- the destination a heap block, so the copy is a Heap-mode value.
module Relocate {a₁ a₂ : AllocState {FS}} {s₁ s₂ : LocState FS}
  -- the destination's block
  (rd : HeapRef)
  -- the destination is held in the new allocator …
  (dst-live : ∀ o → Live a₂ (AtDynamic (heap-loc rd o)))
  -- … and every cell the old one held is unchanged (the copy wrote a fresh block)
  (keep : ∀ l → Live a₁ l → readLoc s₂ l ≡ readLoc s₁ l)
  (bft : ∀ l → Live a₁ l → Live a₂ l)
  (ibt : BlocksKept a₁ a₂)
  -- D381: the destination block has `N` words, each a cell of it
  (N : ℕ)
  (dst-in : ∀ o → o < N → InBlk a₂ (AtDynamic (heap-loc rd o))) where

  open Transport (Live a₁) (λ _ b → b) keep bft ibt using (v-tr)

  private
    -- a value of `c > 0` words fitting from `od` starts inside
    starts-in : ∀ {od c} → 0 < c → od + c ≤ N → od < N
    starts-in {od} {c} p f = ≤-trans (subst (_≤ od + c) (+-comm od 1) (+-monoʳ-≤ od p)) f

    -- a pair's parts fit where it does
    fits-fst : ∀ {od a b} → od + (a + b) ≤ N → od + a ≤ N
    fits-fst {od} {a} {b} f = ≤-trans (+-monoʳ-≤ od (m≤m+n a b)) f

    fits-snd : ∀ {od a b} → od + (a + b) ≤ N → (a + od) + b ≤ N
    fits-snd {od} {a} {b} f =
      subst (_≤ N) (trans (sym (+-assoc od a b)) (cong (_+ b) (+-comm od a))) f

    -- a payload after its tag fits where the sum does
    fits-pay-l : ∀ {od a b} → od + suc (a ⊔ b) ≤ N → suc od + a ≤ N
    fits-pay-l {od} {a} {b} f =
      ≤-trans (s≤s (+-monoʳ-≤ od (m≤m⊔n a b))) (subst (_≤ N) (+-suc od (a ⊔ b)) f)

    fits-pay-r : ∀ {od a b} → od + suc (a ⊔ b) ≤ N → suc od + b ≤ N
    fits-pay-r {od} {a} {b} f =
      ≤-trans (s≤s (+-monoʳ-≤ od (m≤n⊔m a b))) (subst (_≤ N) (+-suc od (a ⊔ b)) f)

  -- word `j` of the destination is word `j` of the source, over `n` words
  -- (a record, so that the source location is recoverable from its type)
  record Agree (n : ℕ) (sl : ValueLocation FS) (od : ℕ) : Set where
    constructor mk-agree
    field at : ∀ j → j < n → readLoc s₂ (AtDynamic (heap-loc rd (j + od))) ≡ readLoc s₁ (offsetLoc sl j)
  open Agree using (at)

  private
    -- the first `n` words of an agreement over `n + m`, and the rest
    agree-fst : ∀ {n m sl od} → Agree (n + m) sl od → Agree n sl od
    agree-fst {n} {m} ag = mk-agree λ j j<n → at ag j (≤-trans j<n (m≤m+n n m))

    agree-snd : ∀ {n m sl od} → Agree (n + m) sl od → Agree m (offsetLoc sl n) (n + od)
    agree-snd {n} {m} {sl} {od} ag = mk-agree λ j j<m →
      trans (cong (λ z → readLoc s₂ (AtDynamic (heap-loc rd z))) (sym (+-assoc j n od)))
        (trans (at ag (j + n) (subst (_< n + m) (+-comm n j) (+-monoʳ-< n j<m)))
               (cong (readLoc s₁) (trans (cong (offsetLoc sl) (+-comm j n)) (sym (offset-+ sl n j)))))

    -- a payload after its tag: the words from the second on
    agree-tail : ∀ {n sl od} → Agree (suc n) sl od → Agree n (sucLoc sl) (suc od)
    agree-tail {n} {sl} {od} ag = mk-agree λ j j<n →
      trans (cong (λ z → readLoc s₂ (AtDynamic (heap-loc rd z))) (+-suc j od))
        (trans (at ag (suc j) (s≤s j<n)) (cong (readLoc s₁) (sym (shift sl j))))

    -- the payload's words fit in the larger alternative
    agree-max-l : ∀ {a b sl od} → Agree (a ⊔ b) sl od → Agree a sl od
    agree-max-l {a} {b} ag = mk-agree λ j j<a → at ag j (≤-trans j<a (m≤m⊔n a b))
    agree-max-r : ∀ {a b sl od} → Agree (a ⊔ b) sl od → Agree b sl od
    agree-max-r {a} {b} ag = mk-agree λ j j<b → at ag j (≤-trans j<b (m≤n⊔m a b))

  private
    -- D382: padding word `j` after an `m`-word payload is a word of the sum
    pad-bound : ∀ m n j → m ≤ n → j < n ∸ m → suc m + j < suc n
    pad-bound m n j m≤n p = s≤s (subst (m + j <_) (m+[n∸m]≡n m≤n) (+-monoʳ-< m p))

    -- …so it moves with the copy
    pad-move : ∀ {m n sl od} → m ≤ n → Agree (suc n) sl od
             → Pad s₁ sl (suc m) (n ∸ m)
             → Pad s₂ (AtDynamic (heap-loc rd od)) (suc m) (n ∸ m)
    pad-move {m} {n} m≤n ag pd j j<c =
      proj₁ (pd j j<c) , trans (at ag (suc m + j) (pad-bound m n j m≤n j<c)) (proj₂ (pd j j<c))

    -- the source's first word, and its second
    w0 : ∀ {n sl od} → 0 < n → Agree n sl od → readLoc s₂ (AtDynamic (heap-loc rd od)) ≡ readLoc s₁ sl
    w0 {sl = sl} p ag = trans (at ag 0 p) (cong (readLoc s₁) (offset-0 sl))

    w1 : ∀ {n sl od} → 1 < n → Agree n sl od → readLoc s₂ (AtDynamic (heap-loc rd (suc od))) ≡ readLoc s₁ (sucLoc sl)
    w1 {sl = sl} p ag = trans (at ag 1 p) (cong (readLoc s₁) (offset-1 sl))

    -- a sum's tag, copied
    tag-at : ∀ {m t n sl od} → 0 < n → Agree n sl od → SumTag m t s₁ sl → SumTag Heap t s₂ (AtDynamic (heap-loc rd od))
    tag-at {m} {od = od} p ag tg = tag-move {m} {s₂ = s₂} {l₂ = AtDynamic (heap-loc rd od)} (w0 p ag) tg

  mutual
    -- a flat value, relocated
    reloc-v : ∀ (C : IRTy) {m v} (sl : ValueLocation FS) (od : ℕ) → Agree (size C) sl od → IsFlat C → od + size C ≤ N
            → ValidAtWF m a₁ {C} v sl s₁
            → ValidAtWF Heap a₂ {C} v (AtDynamic (heap-loc rd od)) s₂
    reloc-v Unit sl od ag _ _ valid-unit-wf = valid-unit-wf
    reloc-v (A * B) sl od ag _ f (valid-pair-wf lmm slb c₁ c₂) =
      valid-pair-wf tt (dst-live _)
        (reloc-cell A sl od (agree-fst {size A} {size B} ag) (fits-fst {od} {size A} {size B} f) c₁)
        (reloc-cell B (offsetLoc sl (size A)) (size A + od) (agree-snd {size A} {size B} ag) (fits-snd {od} {size A} {size B} f) c₂)
    reloc-v (A +ᵀ B) sl od ag _ _ (valid-inl-wf nd lmm tg pp pb slb pd pv) =
      valid-inl-wf nd tt (tag-at (s≤s z≤n) ag tg) (trans (w1 (s≤s (s≤s′ nd)) ag) pp) (bft _ pb) (dst-live _)
        (pad-move (m≤m⊔n (size A) (size B)) ag pd)
        (v-tr A pb pv)
      where s≤s′ : IsNode A → 0 < size A ⊔ size B
            s≤s′ nd′ = ≤-trans (subst (0 <_) (sym (node-size nd′)) (s≤s z≤n)) (m≤m⊔n (size A) (size B))
    reloc-v (A +ᵀ B) sl od ag _ _ (valid-inr-wf nd lmm tg pp pb slb pd pv) =
      valid-inr-wf nd tt (tag-at (s≤s z≤n) ag tg) (trans (w1 (s≤s (s≤s′ nd)) ag) pp) (bft _ pb) (dst-live _)
        (pad-move (m≤n⊔m (size A) (size B)) ag pd)
        (v-tr B pb pv)
      where s≤s′ : IsNode B → 0 < size A ⊔ size B
            s≤s′ nd′ = ≤-trans (subst (0 <_) (sym (node-size nd′)) (s≤s z≤n)) (m≤n⊔m (size A) (size B))
    reloc-v (A +ᵀ B) sl od ag _ _ (valid-inl-reg-wf lmm tg (rep-prim fit) rl slb pd) =
      valid-inl-reg-wf tt (tag-at (s≤s z≤n) ag tg) (rep-prim fit)
        (trans (w1 (s≤s (≤-trans (subst (0 <_) (sym (scalar-size fit)) (s≤s z≤n)) (m≤m⊔n (size A) (size B)))) ag) rl)
        (dst-live _) (pad-move (m≤m⊔n (size A) (size B)) ag pd)
    reloc-v (A +ᵀ B) sl od ag _ _ (valid-inr-reg-wf lmm tg (rep-prim fit) rl slb pd) =
      valid-inr-reg-wf tt (tag-at (s≤s z≤n) ag tg) (rep-prim fit)
        (trans (w1 (s≤s (≤-trans (subst (0 <_) (sym (scalar-size fit)) (s≤s z≤n)) (m≤n⊔m (size A) (size B)))) ag) rl)
        (dst-live _) (pad-move (m≤n⊔m (size A) (size B)) ag pd)
    reloc-v (A +ᵀ B) sl od ag _ f (valid-inl-flat-wf fl lmm tg slb ib pd pv) =
      valid-inl-flat-wf fl tt (tag-at (s≤s z≤n) ag tg) (dst-live _)
        (λ p → dst-in (suc od) (starts-in p (fits-pay-l {od} {size A} {size B} f)))
        (pad-move (m≤m⊔n (size A) (size B)) ag pd)
        (reloc-v A (sucLoc sl) (suc od) (agree-max-l {size A} {size B} (agree-tail ag)) fl
                 (fits-pay-l {od} {size A} {size B} f) pv)
    reloc-v (A +ᵀ B) sl od ag _ f (valid-inr-flat-wf fl lmm tg slb ib pd pv) =
      valid-inr-flat-wf fl tt (tag-at (s≤s z≤n) ag tg) (dst-live _)
        (λ p → dst-in (suc od) (starts-in p (fits-pay-r {od} {size A} {size B} f)))
        (pad-move (m≤n⊔m (size A) (size B)) ag pd)
        (reloc-v B (sucLoc sl) (suc od) (agree-max-r {size A} {size B} (agree-tail ag)) fl
                 (fits-pay-r {od} {size A} {size B} f) pv)

    -- a component's cell, relocated: a node's pointer and a scalar are their
    -- word, a compound its words
    reloc-cell : ∀ (C : IRTy) {c} (sl : ValueLocation FS) (od : ℕ) → Agree (size C) sl od → od + size C ≤ N
               → CellAt a₁ C c sl s₁
               → CellAt a₂ C c (AtDynamic (heap-loc rd od)) s₂
    reloc-cell C sl od ag f (cell-ptr nd r bf v) =
      cell-ptr nd (trans (w0 (subst (0 <_) (sym (node-size nd)) (s≤s z≤n)) ag) r) (bft _ bf) (v-tr C bf v)
    reloc-cell C sl od ag f (cell-inline (rep-prim fit) r) =
      cell-inline (rep-prim fit) (trans (w0 (subst (0 <_) (sym (scalar-size fit)) (s≤s z≤n)) ag) r)
    reloc-cell C sl od ag f (cell-flat fl hr v) =
      cell-flat fl (λ p → dst-live _ , dst-in od (starts-in p f)) (reloc-v C sl od ag fl f v)

  ----------------------------------------------------------------------
  -- plan 0.123 α2: A FORCED LAYER, relocated (the re-suspension's puts,
  -- `Resusp`). `LayerV G R` has the case datas `ValidAtWF` has, at a
  -- functor: a constant position is first-order (`reloc-v`), a recursive
  -- one is a node — its pointer word is copied, and what it points to is
  -- `R`, which moves with the live cells (`R-tr`).
  ----------------------------------------------------------------------
  module Lay {F : IRFunctor} (R : VTy (ν-type F))
             (R-tr : ∀ {m v l} → Live a₁ l → R m a₁ v l s₁ → R m a₂ v l s₂) where

    private
      X = ν-type F

    -- a node position stays where it is
    lay-tr : ∀ {G} (wG : WellFormedFI G) → IsNode (⟦ G ⟧TI X)
           → ∀ {m v l} → Live a₁ l → LayerV G {X} R m a₁ v l s₁ → LayerV G {X} R m a₂ v l s₂
    lay-tr wf-Id _ lv r = R-tr lv r
    lay-tr (wf-K base-Unit) ()
    lay-tr (wf-K base-Void) ()
    lay-tr (wf-K base-Int) ()
    lay-tr (wf-K base-Float) ()
    lay-tr (wf-K (base-Prod _ _)) ()
    lay-tr (wf-K (base-Sum _ _)) ()
    lay-tr (wf-Sum _ _) ()
    lay-tr (wf-Prod _ _) ()

    mutual
      reloc-lay : ∀ {G} (wG : WellFormedFI G) {m v} (sl : ValueLocation FS) (od : ℕ)
                → Agree (size (⟦ G ⟧TI X)) sl od → IsFlat (⟦ G ⟧TI X) → od + size (⟦ G ⟧TI X) ≤ N
                → LayerV G {X} R m a₁ v sl s₁
                → LayerV G {X} R Heap a₂ v (AtDynamic (heap-loc rd od)) s₂
      reloc-lay (wf-K ib) sl od ag fl f v = valid→fo (fo-base ib) (reloc-v _ sl od ag fl f (fo→valid v))
      reloc-lay wf-Id sl od ag () f v
      reloc-lay (wf-Prod {G₁} {G₂} w₁ w₂) sl od ag _ f (pair-wf lmm slb c₁ c₂) =
        pair-wf tt (dst-live _)
          (reloc-lay-cell w₁ sl od (agree-fst {size (⟦ G₁ ⟧TI X)} {size (⟦ G₂ ⟧TI X)} ag)
             (fits-fst {od} {size (⟦ G₁ ⟧TI X)} {size (⟦ G₂ ⟧TI X)} f) c₁)
          (reloc-lay-cell w₂ (offsetLoc sl (size (⟦ G₁ ⟧TI X))) (size (⟦ G₁ ⟧TI X) + od)
             (agree-snd {size (⟦ G₁ ⟧TI X)} {size (⟦ G₂ ⟧TI X)} ag)
             (fits-snd {od} {size (⟦ G₁ ⟧TI X)} {size (⟦ G₂ ⟧TI X)} f) c₂)
      reloc-lay (wf-Sum {G₁} {G₂} w₁ w₂) sl od ag _ _ (inl-wf nd lmm tg pp pb slb pd pv) =
        inl-wf nd tt (tag-at (s≤s z≤n) ag tg)
          (trans (w1 (s≤s (≤-trans (subst (0 <_) (sym (node-size nd)) (s≤s z≤n)) (m≤m⊔n (size (⟦ G₁ ⟧TI X)) (size (⟦ G₂ ⟧TI X))))) ag) pp)
          (bft _ pb) (dst-live _)
          (pad-move (m≤m⊔n (size (⟦ G₁ ⟧TI X)) (size (⟦ G₂ ⟧TI X))) ag pd)
          (lay-tr w₁ nd pb pv)
      reloc-lay (wf-Sum {G₁} {G₂} w₁ w₂) sl od ag _ _ (inr-wf nd lmm tg pp pb slb pd pv) =
        inr-wf nd tt (tag-at (s≤s z≤n) ag tg)
          (trans (w1 (s≤s (≤-trans (subst (0 <_) (sym (node-size nd)) (s≤s z≤n)) (m≤n⊔m (size (⟦ G₁ ⟧TI X)) (size (⟦ G₂ ⟧TI X))))) ag) pp)
          (bft _ pb) (dst-live _)
          (pad-move (m≤n⊔m (size (⟦ G₁ ⟧TI X)) (size (⟦ G₂ ⟧TI X))) ag pd)
          (lay-tr w₂ nd pb pv)
      reloc-lay (wf-Sum {G₁} {G₂} w₁ w₂) sl od ag _ _ (inl-reg-wf lmm tg (rep-prim fit) rl slb pd) =
        inl-reg-wf tt (tag-at (s≤s z≤n) ag tg) (rep-prim fit)
          (trans (w1 (s≤s (≤-trans (subst (0 <_) (sym (scalar-size fit)) (s≤s z≤n)) (m≤m⊔n (size (⟦ G₁ ⟧TI X)) (size (⟦ G₂ ⟧TI X))))) ag) rl)
          (dst-live _) (pad-move (m≤m⊔n (size (⟦ G₁ ⟧TI X)) (size (⟦ G₂ ⟧TI X))) ag pd)
      reloc-lay (wf-Sum {G₁} {G₂} w₁ w₂) sl od ag _ _ (inr-reg-wf lmm tg (rep-prim fit) rl slb pd) =
        inr-reg-wf tt (tag-at (s≤s z≤n) ag tg) (rep-prim fit)
          (trans (w1 (s≤s (≤-trans (subst (0 <_) (sym (scalar-size fit)) (s≤s z≤n)) (m≤n⊔m (size (⟦ G₁ ⟧TI X)) (size (⟦ G₂ ⟧TI X))))) ag) rl)
          (dst-live _) (pad-move (m≤n⊔m (size (⟦ G₁ ⟧TI X)) (size (⟦ G₂ ⟧TI X))) ag pd)
      reloc-lay (wf-Sum {G₁} {G₂} w₁ w₂) sl od ag _ f (inl-flat-wf fl lmm tg slb ib pd pv) =
        inl-flat-wf fl tt (tag-at (s≤s z≤n) ag tg) (dst-live _)
          (λ p → dst-in (suc od) (starts-in p (fits-pay-l {od} {size (⟦ G₁ ⟧TI X)} {size (⟦ G₂ ⟧TI X)} f)))
          (pad-move (m≤m⊔n (size (⟦ G₁ ⟧TI X)) (size (⟦ G₂ ⟧TI X))) ag pd)
          (reloc-lay w₁ (sucLoc sl) (suc od) (agree-max-l {size (⟦ G₁ ⟧TI X)} {size (⟦ G₂ ⟧TI X)} (agree-tail ag)) fl
                     (fits-pay-l {od} {size (⟦ G₁ ⟧TI X)} {size (⟦ G₂ ⟧TI X)} f) pv)
      reloc-lay (wf-Sum {G₁} {G₂} w₁ w₂) sl od ag _ f (inr-flat-wf fl lmm tg slb ib pd pv) =
        inr-flat-wf fl tt (tag-at (s≤s z≤n) ag tg) (dst-live _)
          (λ p → dst-in (suc od) (starts-in p (fits-pay-r {od} {size (⟦ G₁ ⟧TI X)} {size (⟦ G₂ ⟧TI X)} f)))
          (pad-move (m≤n⊔m (size (⟦ G₁ ⟧TI X)) (size (⟦ G₂ ⟧TI X))) ag pd)
          (reloc-lay w₂ (sucLoc sl) (suc od) (agree-max-r {size (⟦ G₁ ⟧TI X)} {size (⟦ G₂ ⟧TI X)} (agree-tail ag)) fl
                     (fits-pay-r {od} {size (⟦ G₁ ⟧TI X)} {size (⟦ G₂ ⟧TI X)} f) pv)

      -- a layer component's cell, relocated
      reloc-lay-cell : ∀ {G} (wG : WellFormedFI G) {c} (sl : ValueLocation FS) (od : ℕ)
                     → Agree (size (⟦ G ⟧TI X)) sl od → od + size (⟦ G ⟧TI X) ≤ N
                     → CellAtP {⟦ G ⟧TI X} (LayerV G {X} R) a₁ c sl s₁
                     → CellAtP {⟦ G ⟧TI X} (LayerV G {X} R) a₂ c (AtDynamic (heap-loc rd od)) s₂
      reloc-lay-cell wG sl od ag f (cell-ptr nd r bf v) =
        cell-ptr nd (trans (w0 (subst (0 <_) (sym (node-size nd)) (s≤s z≤n)) ag) r) (bft _ bf) (lay-tr wG nd bf v)
      reloc-lay-cell wG sl od ag f (cell-inline (rep-prim fit) r) =
        cell-inline (rep-prim fit) (trans (w0 (subst (0 <_) (sym (scalar-size fit)) (s≤s z≤n)) ag) r)
      reloc-lay-cell wG sl od ag f (cell-flat fl hr v) =
        cell-flat fl (λ p → dst-live _ , dst-in od (starts-in p f)) (reloc-lay wG sl od ag fl f v)
