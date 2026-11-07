-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Machine.FlatWords
--
-- plan 0.123 B.4 α (D388): EVERY WORD OF A VALID FLAT VALUE IS WRITTEN.
--
-- A pair's words are its components'; a sum's are its tag, its payload's and
-- its padding (written when the sum was built, D388); a node or a scalar is
-- one written word. So a copy of a flat value (`FlatCopy.copy-run`) reads no
-- unwritten cell, which in the abstract machine would fault (D367).
------------------------------------------------------------------------

open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.SMCore using (AbstractTrace)

module Once.CCC.Machine.FlatWords {FS : FrameSemantics} {prog : AbstractTrace} where

open import Data.Nat using (ℕ; zero; suc; _+_; _<_; _≤_; _⊔_; _∸_; z≤n; s≤s; _<?_)
open import Data.Nat.Properties using (+-assoc; +-comm; m≤m⊔n; m≤n⊔m; m+[n∸m]≡n; ≮⇒≥; ∸-monoˡ-<)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Once.Memory.HeapAddress using (heap-loc)
open import Once.CCC.Machine.Locations using (ValueLocation; AtStack; AtDynamic)
open import Once.CCC.Machine.SMCore hiding (AllocMode; Stack; Heap; AbstractTrace)
open import Once.IR using (AllocMode; Stack; Heap)
open import Once.IRTy using (IRTy; Unit; Void; _*_; _⇛_; μ-type; ν-type; Int; Float; FitsInRegI; fits-int; fits-float)
  renaming (_+_ to _+ᵀ_)
open import Once.CCC.Codegen.Size using (size)
open import Once.CCC.Machine.ValueRel
open ClosureWellFormedBase {FS}
open ClosureWellFormedDef {FS} {prog} using (ValidAtWF; CellAt; fo→valid)
open import Once.IRTy using (IRFunctor; WellFormedFI; ⟦_⟧TI; wf-K; wf-Id; wf-Sum; wf-Prod)
open MemOps {FS} using (readLoc)

------------------------------------------------------------------------
-- Offsets.
------------------------------------------------------------------------
offset-+ : ∀ (l : ValueLocation FS) n m → offsetLoc (offsetLoc l n) m ≡ offsetLoc l (n + m)
offset-+ (AtStack f k) n m = cong (AtStack f) (trans (sym (+-assoc m n k)) (cong (_+ k) (+-comm m n)))
offset-+ (AtDynamic (heap-loc r o)) n m =
  cong (λ z → AtDynamic (heap-loc r z)) (trans (sym (+-assoc m n o)) (cong (_+ o) (+-comm m n)))

offset-0 : ∀ (l : ValueLocation FS) → offsetLoc l 0 ≡ l
offset-0 (AtStack f k)              = refl
offset-0 (AtDynamic (heap-loc r o)) = refl

offset-1 : ∀ (l : ValueLocation FS) → offsetLoc l 1 ≡ sucLoc l
offset-1 (AtStack f k)              = refl
offset-1 (AtDynamic (heap-loc r o)) = refl

private
  node-size : ∀ {C : IRTy} → IsNode C → size C ≡ 1
  node-size {μ-type _} _ = refl
  node-size {ν-type _} _ = refl
  node-size {_ ⇛ _}    _ = refl

  scalar-size : ∀ {C : IRTy} → FitsInRegI C → size C ≡ 1
  scalar-size fits-int   = refl
  scalar-size fits-float = refl

  below-one : ∀ {j} → j < 1 → j ≡ 0
  below-one (s≤s z≤n) = refl

  tag-written : ∀ {m t s l} → SumTag m t s l → Written s l
  tag-written {Heap}  tg = _ , tg
  tag-written {Stack} tg = _ , tg

  -- a one-word thing at `l`
  one-word : ∀ {s : LocState FS} {l} {n} → Written s l → n ≡ 1 → ∀ j → j < n → Written s (offsetLoc l j)
  one-word {l = l} w refl j j<1 rewrite below-one j<1 = subst (Written _) (sym (offset-0 l)) w

  -- the words after a sum's tag: a payload of `p` words, then its padding
  sum-tail : ∀ {s : LocState FS} {l} (p n : ℕ) → p ≤ n
           → (∀ i → i < p → Written s (offsetLoc l (suc i)))
           → Pad s l (suc p) (n ∸ p)
           → ∀ j → j < n → Written s (offsetLoc l (suc j))
  sum-tail {s} {l} p n p≤n pay pd j j<n with j <? p
  ... | yes j<p = pay j j<p
  ... | no ¬j<p =
    subst (λ z → Written s (offsetLoc l (suc z))) (m+[n∸m]≡n (≮⇒≥ ¬j<p))
          (pd (j ∸ p) (∸-monoˡ-< j<n (≮⇒≥ ¬j<p)))

  -- a payload at `sucLoc l` is at `l`'s words from the second
  shift-1 : ∀ {s : LocState FS} {l} {n} → (∀ i → i < n → Written s (offsetLoc (sucLoc l) i))
          → ∀ i → i < n → Written s (offsetLoc l (suc i))
  shift-1 {s} {l} w i i<n =
    subst (Written s) (trans (cong (λ z → offsetLoc z i) (sym (offset-1 l))) (offset-+ l 1 i)) (w i i<n)

mutual
  words : ∀ (C : IRTy) {m alloc c} {l : ValueLocation FS} {s} → IsFlat C → ValidAtWF m alloc {C} c l s
        → ∀ j → j < size C → Written s (offsetLoc l j)
  words Unit _ valid-unit-wf j ()
  words (A * B) {l = l} {s} _ (valid-pair-wf lmm slb c₁ c₂) j j< with j <? size A
  ... | yes j<A = cell-words A c₁ j j<A
  ... | no ¬j<A =
    subst (Written s) (trans (offset-+ l (size A) (j ∸ size A)) (cong (offsetLoc l) (m+[n∸m]≡n (≮⇒≥ ¬j<A))))
          (cell-words B c₂ (j ∸ size A)
             (subst (j ∸ size A <_) (m+[n∸m]≡n′ (size A) (size B)) (∸-monoˡ-< j< (≮⇒≥ ¬j<A))))
    where
      m+[n∸m]≡n′ : ∀ a b → a + b ∸ a ≡ b
      m+[n∸m]≡n′ zero    b = refl
      m+[n∸m]≡n′ (suc a) b = m+[n∸m]≡n′ a b
  words (A +ᵀ B) {l = l} _ (valid-inl-wf nd lmm tg pp pb slb pd pv) zero    _ = subst (Written _) (sym (offset-0 l)) (tag-written tg)
  words (A +ᵀ B) {l = l} {s} _ (valid-inl-wf nd lmm tg pp pb slb pd pv) (suc j) (s≤s j<) =
    sum-tail {s = s} {l = l} (size A) _ (m≤m⊔n (size A) (size B))
      (λ i i< → shift-1 {l = l} (one-word {l = sucLoc l} (_ , pp) (node-size nd)) i i<) pd j j<
  words (A +ᵀ B) {l = l} _ (valid-inr-wf nd lmm tg pp pb slb pd pv) zero    _ = subst (Written _) (sym (offset-0 l)) (tag-written tg)
  words (A +ᵀ B) {l = l} {s} _ (valid-inr-wf nd lmm tg pp pb slb pd pv) (suc j) (s≤s j<) =
    sum-tail {s = s} {l = l} (size B) _ (m≤n⊔m (size A) (size B))
      (λ i i< → shift-1 {l = l} (one-word {l = sucLoc l} (_ , pp) (node-size nd)) i i<) pd j j<
  words (A +ᵀ B) {l = l} _ (valid-inl-reg-wf lmm tg (rep-prim fit) pp slb pd) zero _ = subst (Written _) (sym (offset-0 l)) (tag-written tg)
  words (A +ᵀ B) {l = l} {s} _ (valid-inl-reg-wf lmm tg (rep-prim fit) pp slb pd) (suc j) (s≤s j<) =
    sum-tail {s = s} {l = l} (size A) _ (m≤m⊔n (size A) (size B))
      (λ i i< → shift-1 {l = l} (one-word {l = sucLoc l} (_ , pp) (scalar-size fit)) i i<) pd j j<
  words (A +ᵀ B) {l = l} _ (valid-inr-reg-wf lmm tg (rep-prim fit) pp slb pd) zero _ = subst (Written _) (sym (offset-0 l)) (tag-written tg)
  words (A +ᵀ B) {l = l} {s} _ (valid-inr-reg-wf lmm tg (rep-prim fit) pp slb pd) (suc j) (s≤s j<) =
    sum-tail {s = s} {l = l} (size B) _ (m≤n⊔m (size A) (size B))
      (λ i i< → shift-1 {l = l} (one-word {l = sucLoc l} (_ , pp) (scalar-size fit)) i i<) pd j j<
  words (A +ᵀ B) {l = l} _ (valid-inl-flat-wf fl lmm tg slb ib pd pv) zero _ = subst (Written _) (sym (offset-0 l)) (tag-written tg)
  words (A +ᵀ B) {l = l} {s} _ (valid-inl-flat-wf fl lmm tg slb ib pd pv) (suc j) (s≤s j<) =
    sum-tail {s = s} {l = l} (size A) _ (m≤m⊔n (size A) (size B)) (shift-1 {l = l} (words A fl pv)) pd j j<
  words (A +ᵀ B) {l = l} _ (valid-inr-flat-wf fl lmm tg slb ib pd pv) zero _ = subst (Written _) (sym (offset-0 l)) (tag-written tg)
  words (A +ᵀ B) {l = l} {s} _ (valid-inr-flat-wf fl lmm tg slb ib pd pv) (suc j) (s≤s j<) =
    sum-tail {s = s} {l = l} (size B) _ (m≤n⊔m (size A) (size B)) (shift-1 {l = l} (words B fl pv)) pd j j<
  words Void       () _
  words (A ⇛ B)    () _
  words (μ-type F) () _
  words (ν-type F) () _
  words Int        () _
  words Float      () _

  cell-words : ∀ (C : IRTy) {alloc c} {cl : ValueLocation FS} {s}
             → CellAt alloc C c cl s → ∀ j → j < size C → Written s (offsetLoc cl j)
  cell-words C {cl = cl} {s} (cell-ptr nd r _ _) = one-word {s = s} {l = cl} (_ , r) (node-size nd)
  cell-words C {cl = cl} {s} (cell-inline (rep-prim fit) r) = one-word {s = s} {l = cl} (_ , r) (scalar-size fit)
  cell-words C (cell-flat fl _ v)             = words C fl v

------------------------------------------------------------------------
-- plan 0.123 α2: …and so is every word of a FORCED LAYER (`LayerV`), whose
-- constant positions are first-order values and whose recursive positions
-- are pointer words.
------------------------------------------------------------------------
module LayWords {F : IRFunctor} (R : VTy (ν-type F)) where
  private
    X = ν-type F

  mutual
    lay-words : ∀ {G} (wG : WellFormedFI G) {m alloc c} {l : ValueLocation FS} {s} → IsFlat (⟦ G ⟧TI X)
              → LayerV G {X} R m alloc c l s
              → ∀ j → j < size (⟦ G ⟧TI X) → Written s (offsetLoc l j)
    lay-words (wf-K ib) fl v = words _ fl (fo→valid v)
    lay-words wf-Id () v
    lay-words (wf-Prod {G₁} {G₂} w₁ w₂) {l = l} {s} _ (pair-wf lmm slb c₁ c₂) j j< with j <? size (⟦ G₁ ⟧TI X)
    ... | yes j<A = lay-cell-words w₁ c₁ j j<A
    ... | no ¬j<A =
      subst (Written s) (trans (offset-+ l (size (⟦ G₁ ⟧TI X)) (j ∸ size (⟦ G₁ ⟧TI X)))
                               (cong (offsetLoc l) (m+[n∸m]≡n (≮⇒≥ ¬j<A))))
            (lay-cell-words w₂ c₂ (j ∸ size (⟦ G₁ ⟧TI X))
               (subst (j ∸ size (⟦ G₁ ⟧TI X) <_) (m+[n∸m]≡n′ (size (⟦ G₁ ⟧TI X)) (size (⟦ G₂ ⟧TI X)))
                      (∸-monoˡ-< j< (≮⇒≥ ¬j<A))))
      where
        m+[n∸m]≡n′ : ∀ a b → a + b ∸ a ≡ b
        m+[n∸m]≡n′ zero    b = refl
        m+[n∸m]≡n′ (suc a) b = m+[n∸m]≡n′ a b
    lay-words (wf-Sum w₁ w₂) {l = l} _ (inl-wf nd lmm tg pp pb slb pd pv) zero _ = subst (Written _) (sym (offset-0 l)) (tag-written tg)
    lay-words (wf-Sum {G₁} {G₂} w₁ w₂) {l = l} {s} _ (inl-wf nd lmm tg pp pb slb pd pv) (suc j) (s≤s j<) =
      sum-tail {s = s} {l = l} (size (⟦ G₁ ⟧TI X)) _ (m≤m⊔n (size (⟦ G₁ ⟧TI X)) (size (⟦ G₂ ⟧TI X)))
        (λ i i< → shift-1 {l = l} (one-word {l = sucLoc l} (_ , pp) (node-size nd)) i i<) pd j j<
    lay-words (wf-Sum w₁ w₂) {l = l} _ (inr-wf nd lmm tg pp pb slb pd pv) zero _ = subst (Written _) (sym (offset-0 l)) (tag-written tg)
    lay-words (wf-Sum {G₁} {G₂} w₁ w₂) {l = l} {s} _ (inr-wf nd lmm tg pp pb slb pd pv) (suc j) (s≤s j<) =
      sum-tail {s = s} {l = l} (size (⟦ G₂ ⟧TI X)) _ (m≤n⊔m (size (⟦ G₁ ⟧TI X)) (size (⟦ G₂ ⟧TI X)))
        (λ i i< → shift-1 {l = l} (one-word {l = sucLoc l} (_ , pp) (node-size nd)) i i<) pd j j<
    lay-words (wf-Sum w₁ w₂) {l = l} _ (inl-reg-wf lmm tg (rep-prim fit) pp slb pd) zero _ = subst (Written _) (sym (offset-0 l)) (tag-written tg)
    lay-words (wf-Sum {G₁} {G₂} w₁ w₂) {l = l} {s} _ (inl-reg-wf lmm tg (rep-prim fit) pp slb pd) (suc j) (s≤s j<) =
      sum-tail {s = s} {l = l} (size (⟦ G₁ ⟧TI X)) _ (m≤m⊔n (size (⟦ G₁ ⟧TI X)) (size (⟦ G₂ ⟧TI X)))
        (λ i i< → shift-1 {l = l} (one-word {l = sucLoc l} (_ , pp) (scalar-size fit)) i i<) pd j j<
    lay-words (wf-Sum w₁ w₂) {l = l} _ (inr-reg-wf lmm tg (rep-prim fit) pp slb pd) zero _ = subst (Written _) (sym (offset-0 l)) (tag-written tg)
    lay-words (wf-Sum {G₁} {G₂} w₁ w₂) {l = l} {s} _ (inr-reg-wf lmm tg (rep-prim fit) pp slb pd) (suc j) (s≤s j<) =
      sum-tail {s = s} {l = l} (size (⟦ G₂ ⟧TI X)) _ (m≤n⊔m (size (⟦ G₁ ⟧TI X)) (size (⟦ G₂ ⟧TI X)))
        (λ i i< → shift-1 {l = l} (one-word {l = sucLoc l} (_ , pp) (scalar-size fit)) i i<) pd j j<
    lay-words (wf-Sum w₁ w₂) {l = l} _ (inl-flat-wf fl lmm tg slb ib pd pv) zero _ = subst (Written _) (sym (offset-0 l)) (tag-written tg)
    lay-words (wf-Sum {G₁} {G₂} w₁ w₂) {l = l} {s} _ (inl-flat-wf fl lmm tg slb ib pd pv) (suc j) (s≤s j<) =
      sum-tail {s = s} {l = l} (size (⟦ G₁ ⟧TI X)) _ (m≤m⊔n (size (⟦ G₁ ⟧TI X)) (size (⟦ G₂ ⟧TI X)))
        (shift-1 {l = l} (lay-words w₁ fl pv)) pd j j<
    lay-words (wf-Sum w₁ w₂) {l = l} _ (inr-flat-wf fl lmm tg slb ib pd pv) zero _ = subst (Written _) (sym (offset-0 l)) (tag-written tg)
    lay-words (wf-Sum {G₁} {G₂} w₁ w₂) {l = l} {s} _ (inr-flat-wf fl lmm tg slb ib pd pv) (suc j) (s≤s j<) =
      sum-tail {s = s} {l = l} (size (⟦ G₂ ⟧TI X)) _ (m≤n⊔m (size (⟦ G₁ ⟧TI X)) (size (⟦ G₂ ⟧TI X)))
        (shift-1 {l = l} (lay-words w₂ fl pv)) pd j j<

    lay-cell-words : ∀ {G} (wG : WellFormedFI G) {alloc c} {cl : ValueLocation FS} {s}
                   → CellAtP {⟦ G ⟧TI X} (LayerV G {X} R) alloc c cl s
                   → ∀ j → j < size (⟦ G ⟧TI X) → Written s (offsetLoc cl j)
    lay-cell-words wG {cl = cl} {s} (cell-ptr nd r _ _) = one-word {s = s} {l = cl} (_ , r) (node-size nd)
    lay-cell-words wG {cl = cl} {s} (cell-inline (rep-prim fit) r) = one-word {s = s} {l = cl} (_ , r) (scalar-size fit)
    lay-cell-words wG (cell-flat fl _ v) = lay-words wG fl v
