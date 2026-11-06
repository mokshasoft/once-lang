-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.LayoutAll
--
-- plan 0.123 B.4 α: THE LAYOUT SEGMENTS, ONCE PER PREDICATE.
--
-- The flat emitter's straight segments (`put`, `get`, the injection, the
-- cata call and setup, a closure body's entry, `apply`'s setup) have a length
-- that depends on a type, so a structural fact about emitted code can no
-- longer be read off by reduction. Each fact is a predicate on instructions
-- (`P`); given it at the handful of instruction forms those segments are made
-- of, this module gives it at every segment.
------------------------------------------------------------------------

open import Once.Spec.Name using (CanonicalName)

module Once.CCC.Codegen.LayoutAll (o : CanonicalName) where

open import Data.Nat using (ℕ; suc; _∸_)
open import Data.List using ([]; _∷_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.All.Properties using (++⁺)
open import Data.Product using (proj₂)
open import Once.IRTy using (IRTy)
open import Once.CCC.Machine.SMCore
  using (AbstractInstr; restore-input; load-from-slot; store-at-slot; load-at; store-at; addr-at;
         instr-alloc-heap; mov-to-input; mov-to-output; instr-load-tag-lit; instr-load-code-addr;
         instr-save-closure-reg; instr-call-closure)
open import Once.CCC.Codegen.FlatLayout using (Kind; word; flat; put; put-k; get; get-k; lkind; lsz;
  put-All; put-k-All; get-All; get-k-All; fill; fill-All)
open import Once.CCC.Codegen.Size using (size)
open import Once.CCC.Codegen.IRToTrace o using (wrap-sum; inj-trace; cata-call-from; cata-call-setup; env-entry; getμ; in-trace; node-copy-trace; with-copy; two-cell)
open import Once.CCC.Machine.MuRep using (MuRep; mu-box; mu-unit; mu-ptr)

module Seg {P : AbstractInstr → Set}
  (p-ri    : ∀ k → P (restore-input k))
  (p-lfs   : ∀ k → P (load-from-slot k))
  (p-sas   : ∀ k → P (store-at-slot k))
  (p-la    : ∀ j → P (load-at j))
  (p-sa    : ∀ j → P (store-at j))
  (p-aa    : ∀ j → P (addr-at j))
  (p-alloc : ∀ n → P (instr-alloc-heap n))
  (p-mi    : P mov-to-input)
  (p-mo    : P mov-to-output)
  (p-tag   : ∀ t → P (instr-load-tag-lit t))
  (p-code  : ∀ c → P (instr-load-code-addr c))
  (p-save  : P instr-save-closure-reg)
  (p-call  : P instr-call-closure)
  where

  put-P : ∀ X s b o′ → All P (put X s b o′)
  put-P X s b o′ = put-All X s b o′ (p-ri s) (p-ri b) (p-lfs s) p-la p-sa

  put-k-P : ∀ kd n s b o′ → All P (put-k kd n s b o′)
  put-k-P kd n s b o′ = put-k-All kd n s b o′ (p-ri s) (p-ri b) (p-lfs s) p-la p-sa

  fill-P : ∀ from c → All P (fill from c)
  fill-P from c = fill-All from c (p-tag 0) p-sa

  get-P : ∀ X k → All P (get X k)
  get-P X k = get-All X k p-la p-aa p-mo

  get-k-P : ∀ kd n k → All P (get-k kd n k)
  get-k-P kd n k = get-k-All kd n k p-la p-aa p-mo

  getμ-P : ∀ G k → All P (getμ G k)
  getμ-P G k = get-k-P (lkind G word) (lsz G 1) k

  wrap-P : ∀ tag pk ps ss s → All P (wrap-sum tag pk ps ss s)
  wrap-P tag pk ps ss s =
    p-sas s ∷ p-alloc _ ∷ p-sas (suc s) ∷ p-mi ∷ p-tag tag ∷ p-sa 0 ∷
    ++⁺ (fill-P (suc ps) (ss ∸ suc ps)) (++⁺ (put-k-P pk ps s (suc s) 1) (p-lfs (suc s) ∷ []))

  inj-P : ∀ t Q S n → All P (inj-trace t Q S n)
  inj-P t Q S n =
    p-mo ∷ p-sas n ∷ p-alloc _ ∷ p-sas (suc n) ∷ p-mi ∷ p-tag t ∷ p-sa 0 ∷
    ++⁺ (fill-P (suc (size Q)) (size S ∸ suc (size Q))) (++⁺ (put-P Q n (suc n) 1) (p-lfs (suc n) ∷ []))

  -- D398 (β1): a flat layer's copy into a fresh node
  node-copy-P : ∀ L n → All P (node-copy-trace L n)
  node-copy-P L n = p-mo ∷ p-sas n ∷ p-alloc _ ∷ p-sas (suc n) ∷ ++⁺ (put-P L n (suc n) 0) (p-lfs (suc n) ∷ [])

  -- the two-cell build (D190)
  two-cell-P : ∀ m c → All P (two-cell m c)
  two-cell-P m c = p-mo ∷ p-sas m ∷ p-alloc 2 ∷ p-sas (suc m) ∷ p-mi ∷ p-lfs m ∷ p-sa 0 ∷ p-code c ∷ p-sa 1 ∷ p-lfs (suc m) ∷ []

  -- D398: a kept value's copy, then the rest
  with-copy-P : ∀ kd E n (k : ℕ → _) → (∀ m → All P (k m)) → All P (with-copy kd E n k)
  with-copy-P word E n k pk = pk n
  with-copy-P flat E n k pk = ++⁺ (node-copy-P E n) (p-mi ∷ pk (suc (suc n)))

  wc2-P : ∀ kd E n c → All P (with-copy kd E n (λ m → two-cell m c))
  wc2-P kd E n c = with-copy-P kd E n (λ m → two-cell m c) (λ m → two-cell-P m c)

  -- `In`'s shapes (D366, D398)
  in-P : ∀ r kd L n → All P (in-trace r kd L n)
  in-P mu-box  kd   L n = p-mo ∷ p-sas n ∷ p-alloc 2 ∷ p-mi ∷ p-lfs n ∷ p-sa 0 ∷ p-mo ∷ []
  in-P mu-unit kd   L n = p-alloc 2 ∷ []
  in-P mu-ptr  word L n = p-mo ∷ []
  in-P mu-ptr  flat L n = node-copy-P L n

  call-P : ∀ i0 → P i0 → ∀ E lk ls cl k ev pr → All P (cata-call-from i0 E lk ls cl k ev pr)
  call-P i0 p0 E lk ls cl k ev pr =
    p0 ∷ p-sas k ∷ p-alloc _ ∷ p-sas pr ∷
    ++⁺ (put-P E ev pr 0)
        (++⁺ (put-k-P lk ls k pr (size E))
             (p-lfs cl ∷ p-mi ∷ p-save ∷ p-lfs pr ∷ p-mi ∷ p-call ∷ []))

  setup-P : ∀ E cl k ev bl → All P (cata-call-setup E cl k ev bl)
  setup-P E cl k ev bl =
    ++⁺ (get-P E 0)
        (p-sas ev ∷ p-la _ ∷ p-sas k ∷ p-alloc 2 ∷ p-sas cl ∷ p-mi ∷ p-tag 0 ∷ p-sa 0 ∷
         p-code _ ∷ p-sa 1 ∷ p-lfs k ∷ p-mi ∷ [])

  entry-P : ∀ kd (E A : IRTy) → All P (proj₂ (env-entry kd E A))
  entry-P word E A = []
  entry-P flat E A =
    p-mo ∷ p-sas 0 ∷ p-la 0 ∷ p-sas 1 ∷ p-ri 0 ∷
    ++⁺ (get-P A 1)
        (p-sas 2 ∷ p-alloc _ ∷ p-sas 3 ∷
         ++⁺ (put-P E 1 3 0) (++⁺ (put-P A 2 3 (size E)) (p-lfs 3 ∷ p-mi ∷ [])))
