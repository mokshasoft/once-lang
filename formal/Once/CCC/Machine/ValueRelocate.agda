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

open import Data.Nat using (ℕ; zero; suc; _+_; _<_; _≤_; _⊔_; z≤n; s≤s)
open import Data.Nat.Properties using (+-assoc; +-suc; m≤m+n; m≤n⊔m; m≤m⊔n; ≤-trans; +-monoˡ-≤; +-monoʳ-≤; +-comm)
open import Data.Maybe using (just)
open import Data.Product using (_,_)
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
open ClosureWellFormedDef {FS} {prog} using (ValidAtWF; CellAt; module Transport)

private
  -- a node and a scalar are one word
  node-size : ∀ {C : IRTy} → IsNode C → size C ≡ 1
  node-size {μ-type _} _ = refl
  node-size {ν-type _} _ = refl
  node-size {_ ⇛ _}    _ = refl

  scalar-size : ∀ {C : IRTy} → FitsInRegI C → size C ≡ 1
  scalar-size fits-int   = refl
  scalar-size fits-float = refl

  -- a tag moves with its word
  tag-move : ∀ {m t} {s₁ s₂ : LocState FS} {l₁ l₂ : ValueLocation FS}
           → readLoc s₂ l₂ ≡ readLoc s₁ l₁ → SumTag m t s₁ l₁ → SumTag m t s₂ l₂
  tag-move {Heap}  e tg = trans e tg
  tag-move {Stack} e tg = trans e tg

  -- a mode fact about one heap cell is one about any
  lmm-move : ∀ {m} {h h′ : Once.Memory.HeapAddress.HeapLocation}
           → LocMatchesMode m (AtDynamic {FS} h) → LocMatchesMode m (AtDynamic {FS} h′)
  lmm-move {Heap}  l = l
  lmm-move {Stack} ()

module Relocate {a₁ a₂ : AllocState {FS}} {s₁ s₂ : LocState FS}
  -- the source's block and the destination's
  (rs rd : HeapRef)
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
  Agree : ℕ → ℕ → ℕ → Set
  Agree n os od = ∀ j → j < n → readLoc s₂ (AtDynamic (heap-loc rd (j + od))) ≡ readLoc s₁ (AtDynamic (heap-loc rs (j + os)))

  private
    -- the first `n` words of an agreement over `n + m`, and the rest
    agree-fst : ∀ {n m os od} → Agree (n + m) os od → Agree n os od
    agree-fst {n} {m} ag j j<n = ag j (≤-trans j<n (m≤m+n n m))

    agree-snd : ∀ {n m os od} → Agree (n + m) os od → Agree m (n + os) (n + od)
    agree-snd {n} {m} {os} {od} ag j j<m =
      subst₂′ (+-assoc j n od) (+-assoc j n os)
        (ag (j + n) (subst (_< n + m) (+-comm′ n j) (+-monoʳ-< n j<m)))
      where
        open import Data.Nat.Properties using (+-comm; +-monoʳ-<)
        +-comm′ : ∀ a b → a + b ≡ b + a
        +-comm′ = +-comm
        subst₂′ : ∀ {x y x′ y′} → x ≡ x′ → y ≡ y′
                → readLoc s₂ (AtDynamic (heap-loc rd x)) ≡ readLoc s₁ (AtDynamic (heap-loc rs y))
                → readLoc s₂ (AtDynamic (heap-loc rd x′)) ≡ readLoc s₁ (AtDynamic (heap-loc rs y′))
        subst₂′ refl refl e = e

    -- a payload after its tag: the words from the second on
    agree-tail : ∀ {n os od} → Agree (suc n) os od → Agree n (suc os) (suc od)
    agree-tail {n} {os} {od} ag j j<n =
      subst₂′ (sym (+-suc j od)) (sym (+-suc j os)) (ag (suc j) (s≤s j<n))
      where
        subst₂′ : ∀ {x y x′ y′} → x ≡ x′ → y ≡ y′
                → readLoc s₂ (AtDynamic (heap-loc rd x)) ≡ readLoc s₁ (AtDynamic (heap-loc rs y))
                → readLoc s₂ (AtDynamic (heap-loc rd x′)) ≡ readLoc s₁ (AtDynamic (heap-loc rs y′))
        subst₂′ refl refl e = sym-sym e
          where sym-sym : ∀ {A : Set} {a b : A} → a ≡ b → a ≡ b
                sym-sym e = e

    -- the payload's words fit in the larger alternative
    agree-max-l : ∀ {a b os od} → Agree (a ⊔ b) os od → Agree a os od
    agree-max-l {a} {b} ag j j<a = ag j (≤-trans j<a (m≤m⊔n a b))
    agree-max-r : ∀ {a b os od} → Agree (a ⊔ b) os od → Agree b os od
    agree-max-r {a} {b} ag j j<b = ag j (≤-trans j<b (m≤n⊔m a b))

  mutual
    -- a flat value, relocated
    reloc-v : ∀ (C : IRTy) {m v} (os od : ℕ) → Agree (size C) os od → IsFlat C → od + size C ≤ N
            → ValidAtWF m a₁ {C} v (AtDynamic (heap-loc rs os)) s₁
            → ValidAtWF m a₂ {C} v (AtDynamic (heap-loc rd od)) s₂
    reloc-v Unit os od ag _ _ valid-unit-wf = valid-unit-wf
    reloc-v (A * B) os od ag _ f (valid-pair-wf lmm slb c₁ c₂) =
      valid-pair-wf (lmm-move lmm) (dst-live _)
        (reloc-cell A os od (agree-fst {size A} {size B} ag) (fits-fst {od} {size A} {size B} f) c₁)
        (reloc-cell B (size A + os) (size A + od) (agree-snd {size A} {size B} ag) (fits-snd {od} {size A} {size B} f) c₂)
    reloc-v (A +ᵀ B) os od ag _ _ (valid-inl-wf nd lmm tg pp pb slb pv) =
      valid-inl-wf nd (lmm-move lmm) (tag-move (ag 0 (s≤s z≤n)) tg) (trans (ag 1 (s≤s (s≤s′ nd))) pp) (bft _ pb) (dst-live _)
        (v-tr A pb pv)
      where s≤s′ : IsNode A → 0 < size A ⊔ size B
            s≤s′ nd′ = ≤-trans (subst (0 <_) (sym (node-size nd′)) (s≤s z≤n)) (m≤m⊔n (size A) (size B))
    reloc-v (A +ᵀ B) os od ag _ _ (valid-inr-wf nd lmm tg pp pb slb pv) =
      valid-inr-wf nd (lmm-move lmm) (tag-move (ag 0 (s≤s z≤n)) tg) (trans (ag 1 (s≤s (s≤s′ nd))) pp) (bft _ pb) (dst-live _)
        (v-tr B pb pv)
      where s≤s′ : IsNode B → 0 < size A ⊔ size B
            s≤s′ nd′ = ≤-trans (subst (0 <_) (sym (node-size nd′)) (s≤s z≤n)) (m≤n⊔m (size A) (size B))
    reloc-v (A +ᵀ B) os od ag _ _ (valid-inl-reg-wf lmm tg (rep-prim fit) rl slb) =
      valid-inl-reg-wf (lmm-move lmm) (tag-move (ag 0 (s≤s z≤n)) tg) (rep-prim fit)
        (trans (ag 1 (s≤s (≤-trans (subst (0 <_) (sym (scalar-size fit)) (s≤s z≤n)) (m≤m⊔n (size A) (size B))))) rl)
        (dst-live _)
    reloc-v (A +ᵀ B) os od ag _ _ (valid-inr-reg-wf lmm tg (rep-prim fit) rl slb) =
      valid-inr-reg-wf (lmm-move lmm) (tag-move (ag 0 (s≤s z≤n)) tg) (rep-prim fit)
        (trans (ag 1 (s≤s (≤-trans (subst (0 <_) (sym (scalar-size fit)) (s≤s z≤n)) (m≤n⊔m (size A) (size B))))) rl)
        (dst-live _)
    reloc-v (A +ᵀ B) os od ag _ f (valid-inl-flat-wf fl lmm tg slb ib pv) =
      valid-inl-flat-wf fl (lmm-move lmm) (tag-move (ag 0 (s≤s z≤n)) tg) (dst-live _)
        (λ p → dst-in (suc od) (starts-in p (fits-pay-l {od} {size A} {size B} f)))
        (reloc-v A (suc os) (suc od) (agree-max-l {size A} {size B} (agree-tail ag)) fl
                 (fits-pay-l {od} {size A} {size B} f) pv)
    reloc-v (A +ᵀ B) os od ag _ f (valid-inr-flat-wf fl lmm tg slb ib pv) =
      valid-inr-flat-wf fl (lmm-move lmm) (tag-move (ag 0 (s≤s z≤n)) tg) (dst-live _)
        (λ p → dst-in (suc od) (starts-in p (fits-pay-r {od} {size A} {size B} f)))
        (reloc-v B (suc os) (suc od) (agree-max-r {size A} {size B} (agree-tail ag)) fl
                 (fits-pay-r {od} {size A} {size B} f) pv)

    -- a component's cell, relocated: a node's pointer and a scalar are their
    -- word, a compound its words
    reloc-cell : ∀ (C : IRTy) {c} (os od : ℕ) → Agree (size C) os od → od + size C ≤ N
               → CellAt a₁ C c (AtDynamic (heap-loc rs os)) s₁
               → CellAt a₂ C c (AtDynamic (heap-loc rd od)) s₂
    reloc-cell C os od ag f (cell-ptr nd r bf v) =
      cell-ptr nd (trans (ag 0 (subst (0 <_) (sym (node-size nd)) (s≤s z≤n))) r) (bft _ bf) (v-tr C bf v)
    reloc-cell C os od ag f (cell-inline (rep-prim fit) r) =
      cell-inline (rep-prim fit) (trans (ag 0 (subst (0 <_) (sym (scalar-size fit)) (s≤s z≤n))) r)
    reloc-cell C os od ag f (cell-flat fl hr v) =
      cell-flat fl (λ p → dst-live _ , dst-in od (starts-in p f)) (reloc-v C os od ag fl f v)
