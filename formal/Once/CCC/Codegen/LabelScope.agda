-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.CCC.Codegen.LabelScope   (Plan 0.63, obligation (iii))
--
-- CONTAINMENT: every `once`-namespace label an emitted fragment MENTIONS —
-- defines (`c-label`) or targets (`c-jmp`, the two branches) — lies inside the
-- counter range `[l, l')` that fragment was given.
--
-- This is the third and last brick of label scoping (`label-mono` is the
-- first, `Machine.Flat.find-label-lands` the second). With it, a jump emitted
-- inside a closure body cannot name a label outside the body: the body's range
-- is disjoint from everything around it, by monotonicity.
--
-- SHAPE: `slots-below`'s, exactly — one clause per `ir-to-trace'` clause, with
-- the cata skeletons and the two compile-time functor walks as sub-lemmas.
-- Unlike the slot development there is no `seg-idle?`-style decider shortcut:
-- the labels are ARITHMETIC ON THE COUNTER (`l1`, `suc l1`, `lb + lsize F`),
-- so nothing reduces on a variable and every bound is a real `≤` proof.
--
-- THE THUNK NAMESPACE IS NOT HERE, and does not need to be: D082 made
-- `c-thunk`/`instr-load-code-addr` a separate provenance, so they can never be
-- the target of a `find-label` scan and cannot break a jump's segment.
------------------------------------------------------------------------

module Once.CCC.Codegen.LabelScope where

open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; _<_; z≤n; s≤s; _*_)
open import Data.Nat.Properties using
  (≤-refl; ≤-trans; ≤-reflexive; n≤1+n; m≤m+n; m≤n+m; +-monoʳ-≤; +-monoˡ-≤
  ; +-comm; +-assoc; +-identityʳ; ≤-step; m<n⇒m<1+n; <-transˡ; <-transʳ; +-suc)
open import Data.Bool using (Bool; true; false)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.All.Properties using (++⁺)
open import Data.List.Properties using (++-assoc; ++-identityʳ)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; subst₂; cong)

open import Once.IR using (IR; AllocMode; Stack; Heap;
  id; _∘_; ⟨_,_⟩; fst; snd; inl; inr; case; terminal; initial;
  curry; apply;
  In; out-μ; Cata; Para; Out; in-ν; Ana; Hylo; Fuse;
  free-heap; SigOp; const)
open import Once.IRTy using (fits-int; fits-float; ⌈_⌉F)
open import Once.Type using (Functor; K; Id; _⊕_; _⊗_)
open import Once.CCC.Machine.SMCore
open import Once.CCC.Codegen.IRToTrace using
  (ir-to-trace'; ir-to-trace; CataStrategy; strat-const; strat-nat; strat-linear
  ; strat-branching; cata-strategy; cata-dispatch; lsize
  ; push2; pop2; wrap-sum; visit-walk; rebuild-walk
  ; cata-nat-I₁; cata-nat-I₂; cata-nat-I₃; cata-nat-layer; cata-nat-descend
  ; cata-br-I₁; cata-br-I₂; cata-lin-I₁; cata-lin-I₂; cata-lin-I₃)
open import Once.CCC.Codegen.LabelRange using (label-of; cata-label-of; label-mono; cata-label-mono)
open import Once.CCC.Codegen.SlotBudget using
  (fetch-at; seg-at; SegState; seg-idle?; idle-seg-at
  ; seg-at-++ˡ; seg-at-++ʳ; fetch-++ˡ; fetch-++ʳ; split-pos; seg-fold
  ; idle-neutral; seg-fold-++; idle-++; visit-idle; rebuild-idle
  ; ok-neu; slots-below; budget-of)

------------------------------------------------------------------------
-- The `once`-namespace label an instruction mentions.
------------------------------------------------------------------------
once-label-of : AbstractInstr → Maybe ℕ
once-label-of (instr-ctrl (c-label m))               = just m
once-label-of (instr-ctrl (c-jmp m))                 = just m
once-label-of (instr-ctrl (c-branch-scratch-zero m)) = just m
once-label-of (instr-ctrl (c-branch-tag-zero m))     = just m
{-# CATCHALL #-}
once-label-of _                                      = nothing

-- A RECORD, for `SlotBelow`'s reason: at a use site the goal must keep the
-- INSTRUCTION rigid, which a reducing function would not.
record LabelIn (lo hi : ℕ) (i : AbstractInstr) : Set where
  constructor mkLabelIn
  field in-range : ∀ (m : ℕ) → once-label-of i ≡ just m → (lo ≤ m) × (m < hi)
open LabelIn public

cata-trace-of : ℕ × ℕ × AbstractTrace → AbstractTrace
cata-trace-of (_ , _ , t) = t

trace-of : ℕ × ℕ × AbstractTrace × List (ℕ × ℕ × AbstractTrace) → AbstractTrace
trace-of (_ , _ , t , _) = t

LabelsIn : ℕ → ℕ → AbstractTrace → Set
LabelsIn lo hi = All (LabelIn lo hi)

li-none : ∀ {lo hi} {i} → once-label-of i ≡ nothing → LabelIn lo hi i
li-none eq = mkLabelIn (λ m eq' → go (trans (sym eq) eq'))
  where go : ∀ {A : Set} {m : ℕ} → nothing ≡ just m → A
        go ()

li-lab : ∀ {lo hi} {k} {i} → once-label-of i ≡ just k → lo ≤ k → k < hi → LabelIn lo hi i
li-lab {lo} {hi} eq lo≤ <hi =
  mkLabelIn (λ m eq' → let p = just-inj (trans (sym eq) eq')
                       in subst (lo ≤_) p lo≤ , subst (_< hi) p <hi)
  where just-inj : ∀ {a b : ℕ} → just a ≡ just b → a ≡ b
        just-inj refl = refl

-- widening the window preserves membership
li-weaken : ∀ {lo lo' hi hi'} {i} → lo' ≤ lo → hi ≤ hi' → LabelIn lo hi i → LabelIn lo' hi' i
li-weaken lo' hi' p =
  mkLabelIn (λ m eq → ≤-trans lo' (proj₁ (in-range p m eq))
                    , ≤-trans (proj₂ (in-range p m eq)) hi')

ls-weaken : ∀ {lo lo' hi hi'} {t} → lo' ≤ lo → hi ≤ hi' → LabelsIn lo hi t → LabelsIn lo' hi' t
ls-weaken lo' hi' []       = []
ls-weaken lo' hi' (p ∷ ps) = li-weaken lo' hi' p ∷ ls-weaken lo' hi' ps

-- two arithmetic shapes every `⊕` level needs (`lsize (F ⊕ G)` is a double
-- successor, so both bounds are `+-suc` shifts of `m≤m+n`)
a<a+suc : ∀ (a k : ℕ) → a < a + suc k
a<a+suc a k = subst (suc a ≤_) (sym (+-suc a k)) (s≤s (m≤m+n a k))

sa<a+ss : ∀ (a k : ℕ) → suc a < a + suc (suc k)
sa<a+ss a k = subst (suc (suc a) ≤_) (sym (+-suc a (suc k))) (s≤s (a<a+suc a k))

+ss : ∀ (a k : ℕ) → a + suc (suc k) ≡ suc (suc (a + k))
+ss a k = trans (+-suc a (suc k)) (cong suc (+-suc a k))

-- `a + k < a + j` from `suc k ≤ j` (the branching loop's four labels are
-- `l1 + 0..3` against `lv = l1 + 4`)
+lt : ∀ (a k j : ℕ) → suc k ≤ j → a + k < a + j
+lt a k j p = subst (_≤ a + j) (+-suc a k) (+-monoʳ-≤ a p)

------------------------------------------------------------------------
-- The slot-only fragments mention no label at all.
------------------------------------------------------------------------
push2-ls : ∀ (lo hi topSlot tv tb : ℕ) → LabelsIn lo hi (push2 topSlot tv tb)
push2-ls lo hi topSlot tv tb =
  li-none refl ∷ li-none refl ∷ li-none refl ∷ li-none refl ∷ li-none refl ∷
  li-none refl ∷ li-none refl ∷ li-none refl ∷ li-none refl ∷ li-none refl ∷ []

pop2-ls : ∀ (lo hi topSlot : ℕ) → LabelsIn lo hi (pop2 topSlot)
pop2-ls lo hi topSlot =
  li-none refl ∷ li-none refl ∷ li-none refl ∷ li-none refl ∷ li-none refl ∷ []

wrap-sum-ls : ∀ (lo hi tag s : ℕ) → LabelsIn lo hi (wrap-sum tag s)
wrap-sum-ls lo hi tag s =
  li-none refl ∷ li-none refl ∷ li-none refl ∷ li-none refl ∷ li-none refl ∷
  li-none refl ∷ li-none refl ∷ li-none refl ∷ li-none refl ∷ []

------------------------------------------------------------------------
-- THE TWO COMPILE-TIME WALKS. A `⊕` level owns `[lb, lb+1]` and recurses at
-- `lb+2` (F) and `lb+2+lsize F` (G); a `⊗` level owns nothing and recurses at
-- `lb` (F) and `lb + lsize F` (G). Hence `lsize (F ⊕ G) = 2 + lsize F + lsize G`
-- and `lsize (F ⊗ G) = lsize F + lsize G` — the windows are exactly disjoint.
------------------------------------------------------------------------
visit-ls : ∀ (F : Functor) (todo tv tb s lb : ℕ)
         → LabelsIn lb (lb + lsize F) (visit-walk todo tv tb F s lb)
visit-ls (K _) todo tv tb s lb = []
visit-ls Id    todo tv tb s lb =
  li-none refl ∷ push2-ls _ _ todo tv tb
visit-ls (F ⊕ G) todo tv tb s lb =
  ++⁺ (li-lab refl ≤-refl lb<hi ∷ li-none refl ∷ li-none refl ∷ [])
      (++⁺ (ls-weaken loG hiG (visit-ls G todo tv tb (s + 4) (suc (suc lb) + lsize F)))
           (++⁺ (li-lab refl (n≤1+n lb) slb<hi ∷ li-lab refl ≤-refl lb<hi ∷
                 li-none refl ∷ li-none refl ∷ [])
                (++⁺ (ls-weaken loF hiF (visit-ls F todo tv tb (s + 4) (suc (suc lb))))
                     (li-lab refl (n≤1+n lb) slb<hi ∷ []))))
  where
    hi = lb + lsize (F ⊕ G)
    lb<hi : lb < hi
    lb<hi = a<a+suc lb (suc (lsize F + lsize G))
    slb<hi : suc lb < hi
    slb<hi = sa<a+ss lb (lsize F + lsize G)
    loF : lb ≤ suc (suc lb)
    loF = ≤-trans (n≤1+n lb) (n≤1+n (suc lb))
    hiF : suc (suc lb) + lsize F ≤ hi
    hiF = subst (suc (suc (lb + lsize F)) ≤_) (sym (+ss lb (lsize F + lsize G)))
                (s≤s (s≤s (+-monoʳ-≤ lb (m≤m+n (lsize F) (lsize G)))))
    loG : lb ≤ suc (suc lb) + lsize F
    loG = ≤-step (≤-step (m≤m+n lb (lsize F)))
    hiG : suc (suc lb) + lsize F + lsize G ≤ hi
    hiG = subst (suc (suc (lb + lsize F + lsize G)) ≤_) (sym (+ss lb (lsize F + lsize G)))
                (s≤s (s≤s (≤-reflexive (+-assoc lb (lsize F) (lsize G)))))
visit-ls (F ⊗ G) todo tv tb s lb =
  ++⁺ (li-none refl ∷ li-none refl ∷ li-none refl ∷ li-none refl ∷ [])
      (++⁺ (ls-weaken (m≤m+n lb (lsize F)) hiG (visit-ls G todo tv tb (s + 4) (lb + lsize F)))
           (++⁺ (li-none refl ∷ li-none refl ∷ li-none refl ∷ [])
                (ls-weaken ≤-refl hiF (visit-ls F todo tv tb (s + 4) lb))))
  where
    hiF : lb + lsize F ≤ lb + lsize (F ⊗ G)
    hiF = +-monoʳ-≤ lb (m≤m+n (lsize F) (lsize G))
    hiG : lb + lsize F + lsize G ≤ lb + lsize (F ⊗ G)
    hiG = ≤-reflexive (+-assoc lb (lsize F) (lsize G))

rebuild-ls : ∀ (F : Functor) (val tv tb s lb : ℕ)
           → LabelsIn lb (lb + lsize F) (rebuild-walk val tv tb F s lb)
rebuild-ls (K _) val tv tb s lb = li-none refl ∷ []
rebuild-ls Id    val tv tb s lb = pop2-ls _ _ val
rebuild-ls (F ⊕ G) val tv tb s lb =
  ++⁺ (li-lab refl ≤-refl lb<hi ∷ li-none refl ∷ li-none refl ∷ [])
      (++⁺ (ls-weaken loG hiG (rebuild-ls G val tv tb (s + 4) (suc (suc lb) + lsize F)))
           (++⁺ (wrap-sum-ls _ _ 1 s)
                (++⁺ (li-lab refl (n≤1+n lb) slb<hi ∷ li-lab refl ≤-refl lb<hi ∷
                      li-none refl ∷ li-none refl ∷ [])
                     (++⁺ (ls-weaken loF hiF (rebuild-ls F val tv tb (s + 4) (suc (suc lb))))
                          (++⁺ (wrap-sum-ls _ _ 0 s)
                               (li-lab refl (n≤1+n lb) slb<hi ∷ []))))))
  where
    hi = lb + lsize (F ⊕ G)
    lb<hi : lb < hi
    lb<hi = a<a+suc lb (suc (lsize F + lsize G))
    slb<hi : suc lb < hi
    slb<hi = sa<a+ss lb (lsize F + lsize G)
    loF : lb ≤ suc (suc lb)
    loF = ≤-trans (n≤1+n lb) (n≤1+n (suc lb))
    hiF : suc (suc lb) + lsize F ≤ hi
    hiF = subst (suc (suc (lb + lsize F)) ≤_) (sym (+ss lb (lsize F + lsize G)))
                (s≤s (s≤s (+-monoʳ-≤ lb (m≤m+n (lsize F) (lsize G)))))
    loG : lb ≤ suc (suc lb) + lsize F
    loG = ≤-step (≤-step (m≤m+n lb (lsize F)))
    hiG : suc (suc lb) + lsize F + lsize G ≤ hi
    hiG = subst (suc (suc (lb + lsize F + lsize G)) ≤_) (sym (+ss lb (lsize F + lsize G)))
                (s≤s (s≤s (≤-reflexive (+-assoc lb (lsize F) (lsize G)))))
rebuild-ls (F ⊗ G) val tv tb s lb =
  ++⁺ (li-none refl ∷ li-none refl ∷ li-none refl ∷ li-none refl ∷ [])
      (++⁺ (ls-weaken ≤-refl hiF (rebuild-ls F val tv tb (s + 4) lb))
           (++⁺ (li-none refl ∷ li-none refl ∷ li-none refl ∷ li-none refl ∷ [])
                (++⁺ (ls-weaken (m≤m+n lb (lsize F)) hiG (rebuild-ls G val tv tb (s + 4) (lb + lsize F)))
                     (li-none refl ∷ li-none refl ∷ li-none refl ∷ li-none refl ∷
                      li-none refl ∷ li-none refl ∷ li-none refl ∷ li-none refl ∷
                      li-none refl ∷ []))))
  where
    hiF : lb + lsize F ≤ lb + lsize (F ⊗ G)
    hiF = +-monoʳ-≤ lb (m≤m+n (lsize F) (lsize G))
    hiG : lb + lsize F + lsize G ≤ lb + lsize (F ⊗ G)
    hiG = ≤-reflexive (+-assoc lb (lsize F) (lsize G))

------------------------------------------------------------------------
-- THE CATA SKELETONS. Each owns a fixed block of labels immediately above
-- the algebra's outgoing counter `l1`, and splices the algebra trace `at`
-- (whose own labels are below `l1`) unchanged — so everything lands in
-- `[lo, l2)` given `lo ≤ l1`.
------------------------------------------------------------------------
-- `lo ≤ l1 + k`, and `l1 + k < l1 + n` for the fixed towers. Spelled as
-- `≤-step` chains rather than arithmetic: the towers are literal `suc`s.
lo≤ : ∀ {lo l1 : ℕ} → lo ≤ l1 → lo ≤ l1
lo≤ p = p

cata-nat-ls : ∀ (lo n1 l1 : ℕ) (at : AbstractTrace) → lo ≤ l1 → LabelsIn lo l1 at
            → LabelsIn lo (cata-label-of (cata-dispatch strat-nat n1 l1 at))
                       (cata-trace-of (cata-dispatch strat-nat n1 l1 at))
cata-nat-ls lo n1 l1 at lo≤l1 atls =
  -- Plan 0.63 (iii): `I₁ ++ at ++ (I₂ ++ at ++ I₃)`
  li-none refl ∷ li-none refl ∷
  ++⁺ descend
      (li-none refl ∷ li-none refl ∷ li-none refl ∷
       ++⁺ (layer 0)
           (li-none refl ∷ ++⁺ at'
             (li-lab refl L4 H4 ∷ li-lab refl L5 H5 ∷ li-none refl ∷
              ++⁺ (layer 1)
                  (li-none refl ∷ ++⁺ at'
                    (li-none refl ∷ li-lab refl L4 H4 ∷ li-lab refl L5 H5 ∷ [])))))
  where
    hi = suc (suc (suc (suc (suc (suc l1)))))
    L0 : lo ≤ l1
    L0 = lo≤l1
    L1 : lo ≤ suc l1
    L1 = ≤-step L0
    L2 : lo ≤ suc (suc l1)
    L2 = ≤-step L1
    L3 : lo ≤ suc (suc (suc l1))
    L3 = ≤-step L2
    L4 : lo ≤ suc (suc (suc (suc l1)))
    L4 = ≤-step L3
    L5 : lo ≤ suc (suc (suc (suc (suc l1))))
    L5 = ≤-step L4
    H0 : l1 < hi
    H0 = ≤-step (≤-step (≤-step (≤-step (≤-step ≤-refl))))
    H1 : suc l1 < hi
    H1 = ≤-step (≤-step (≤-step (≤-step ≤-refl)))
    H2 : suc (suc l1) < hi
    H2 = ≤-step (≤-step (≤-step ≤-refl))
    H3 : suc (suc (suc l1)) < hi
    H3 = ≤-step (≤-step ≤-refl)
    H4 : suc (suc (suc (suc l1))) < hi
    H4 = ≤-step ≤-refl
    H5 : suc (suc (suc (suc (suc l1)))) < hi
    H5 = ≤-refl
    at' : LabelsIn lo hi at
    at' = ls-weaken ≤-refl (≤-step (≤-step (≤-step (≤-step (≤-step (≤-step ≤-refl)))))) atls
    -- `build-layer tag` is ten slot/heap instructions: no label anywhere.
    -- Indexed by the tag because the skeleton uses it at BOTH 0 and 1, and a
    -- `_`-inferred trace would unify with whichever came first.
    layer : ∀ (tag : ℕ) → LabelsIn lo hi
              (mov-to-output ∷ store-at-slot n1 ∷ instr-alloc-heap 2 ∷
               store-at-slot (suc n1) ∷ mov-to-input ∷ instr-load-tag-lit tag ∷
               store-indirect ∷ load-from-slot n1 ∷ store-indirect-suc ∷
               load-from-slot (suc n1) ∷ [])
    layer tag = li-none refl ∷ li-none refl ∷ li-none refl ∷ li-none refl ∷ li-none refl ∷
                li-none refl ∷ li-none refl ∷ li-none refl ∷ li-none refl ∷ li-none refl ∷ []
    descend : LabelsIn lo hi _
    descend =
      li-lab refl L0 H0 ∷ li-lab refl L1 H1 ∷ li-lab refl L2 H2 ∷
      li-none refl ∷ li-none refl ∷ li-none refl ∷
      li-lab refl L3 H3 ∷
      li-lab refl L2 H2 ∷ li-none refl ∷
      li-lab refl L3 H3 ∷ li-lab refl L0 H0 ∷
      li-lab refl L1 H1 ∷ []


-- The Tier-1 LINEAR skeleton: four labels above `l1` (`ld-top`, `ld-end`,
-- `la-top`, `la-end`), the algebra spliced twice.
cata-linear-ls : ∀ (lo n1 l1 : ℕ) (at : AbstractTrace) → lo ≤ l1 → LabelsIn lo l1 at
               → LabelsIn lo (cata-label-of (cata-dispatch strat-linear n1 l1 at))
                          (cata-trace-of (cata-dispatch strat-linear n1 l1 at))
cata-linear-ls lo n1 l1 at lo≤l1 atls =
  ++⁺ descend (li-none refl ∷ ++⁺ at' ascend)
  where
    hi = suc (suc (suc (suc l1)))
    L0 : lo ≤ l1
    L0 = lo≤l1
    L1 : lo ≤ suc l1
    L1 = ≤-step L0
    L2 : lo ≤ suc (suc l1)
    L2 = ≤-step L1
    L3 : lo ≤ suc (suc (suc l1))
    L3 = ≤-step L2
    H0 : l1 < hi
    H0 = ≤-step (≤-step (≤-step ≤-refl))
    H1 : suc l1 < hi
    H1 = ≤-step (≤-step ≤-refl)
    H2 : suc (suc l1) < hi
    H2 = ≤-step ≤-refl
    H3 : suc (suc (suc l1)) < hi
    H3 = ≤-refl
    at' : LabelsIn lo hi at
    at' = ls-weaken ≤-refl (≤-step (≤-step (≤-step (≤-step ≤-refl)))) atls
    descend : LabelsIn lo hi _
    descend =
      li-none refl ∷ li-none refl ∷ li-none refl ∷
      li-lab refl L0 H0 ∷ li-lab refl L1 H1 ∷
      li-none refl ∷ li-none refl ∷ li-none refl ∷ li-none refl ∷ li-none refl ∷
      li-none refl ∷ li-none refl ∷ li-none refl ∷ li-none refl ∷ li-none refl ∷
      li-none refl ∷ li-none refl ∷ li-none refl ∷ li-none refl ∷ li-none refl ∷
      li-none refl ∷ li-none refl ∷ li-none refl ∷
      li-lab refl L0 H0 ∷ li-lab refl L1 H1 ∷ []
    ascend : LabelsIn lo hi _
    ascend =
      li-lab refl L2 H2 ∷ li-lab refl L3 H3 ∷
      li-none refl ∷ li-none refl ∷ li-none refl ∷ li-none refl ∷ li-none refl ∷
      li-none refl ∷ li-none refl ∷ li-none refl ∷ li-none refl ∷ li-none refl ∷
      li-none refl ∷ li-none refl ∷ li-none refl ∷ li-none refl ∷ li-none refl ∷
      li-none refl ∷ li-none refl ∷ li-none refl ∷ li-none refl ∷ li-none refl ∷
      li-none refl ∷ li-none refl ∷ li-none refl ∷
      ++⁺ at' (li-none refl ∷ li-lab refl L2 H2 ∷ li-lab refl L3 H3 ∷ [])

-- The Tier-2 BRANCHING skeleton. Four loop labels at `l1..l1+3`, then the two
-- functor walks in DISJOINT windows: visit at `lv = l1+4`, rebuild at
-- `lr = lv + lsize F`, and `l2 = lr + lsize F`. That the windows are disjoint
-- is exactly what the two `ls-weaken`s below check.
cata-branching-ls : ∀ (F : Functor) (lo n1 l1 : ℕ) (at : AbstractTrace) → lo ≤ l1 → LabelsIn lo l1 at
                  → LabelsIn lo (cata-label-of (cata-dispatch (strat-branching F) n1 l1 at))
                             (cata-trace-of (cata-dispatch (strat-branching F) n1 l1 at))
-- Plan 0.63 (iii): `I₁ ++ at ++ I₂`.
cata-branching-ls F lo n1 l1 at lo≤l1 atls =
  ++⁺ I₁-ls (++⁺ at' I₂-ls)
  where
    lv = l1 + 4
    lr = lv + lsize F
    hi = lr + lsize F
    lv≤lr : lv ≤ lr
    lv≤lr = m≤m+n lv (lsize F)
    top : lv ≤ hi
    top = ≤-trans lv≤lr (m≤m+n lr (lsize F))
    L0 : lo ≤ l1
    L0 = lo≤l1
    L1 : lo ≤ suc l1
    L1 = ≤-step L0
    L2 : lo ≤ l1 + 2
    L2 = ≤-trans L0 (m≤m+n l1 2)
    L3 : lo ≤ l1 + 3
    L3 = ≤-trans L0 (m≤m+n l1 3)
    H0 : l1 < hi
    H0 = <-transˡ (a<a+suc l1 3) top
    H1 : suc l1 < hi
    H1 = <-transˡ (sa<a+ss l1 2) top
    H2 : l1 + 2 < hi
    H2 = <-transˡ (+lt l1 2 4 (s≤s (s≤s (s≤s z≤n)))) top
    H3 : l1 + 3 < hi
    H3 = <-transˡ (+lt l1 3 4 (s≤s (s≤s (s≤s (s≤s z≤n))))) top
    at' : LabelsIn lo hi at
    at' = ls-weaken ≤-refl (≤-trans (m≤m+n l1 4) top) atls
    I₁-ls : LabelsIn lo hi (cata-br-I₁ F n1 l1)
    I₁-ls =
      ++⁺ (li-none refl ∷ li-none refl ∷ li-none refl ∷ li-none refl ∷ li-none refl ∷
           li-none refl ∷ li-none refl ∷ li-none refl ∷ li-none refl ∷ li-none refl ∷
           li-none refl ∷ li-none refl ∷ li-none refl ∷ li-none refl ∷ [])
      (++⁺ (push2-ls lo hi n1 (n1 + 4) (n1 + 5))
      (++⁺ (li-lab refl L0 H0 ∷ li-none refl ∷ li-none refl ∷
            li-lab refl L1 H1 ∷ li-none refl ∷ li-none refl ∷
            li-none refl ∷ li-none refl ∷ li-none refl ∷ li-none refl ∷ [])
      (++⁺ (push2-ls lo hi (suc n1) (n1 + 4) (n1 + 5))
      (++⁺ (li-none refl ∷ li-none refl ∷ [])
      (++⁺ (ls-weaken (≤-trans L0 (m≤m+n l1 4)) (m≤m+n lr (lsize F))
                      (visit-ls F n1 (n1 + 4) (n1 + 5) (n1 + 7) lv))
      (++⁺ (li-lab refl L0 H0 ∷ li-lab refl L1 H1 ∷ [])
      (++⁺ (li-lab refl L2 H2 ∷ li-none refl ∷ li-none refl ∷
            li-lab refl L3 H3 ∷ li-none refl ∷ li-none refl ∷
            li-none refl ∷ li-none refl ∷ [])
      (++⁺ (ls-weaken (≤-trans L0 (≤-trans (m≤m+n l1 4) lv≤lr)) ≤-refl
                      (rebuild-ls F (n1 + 2) (n1 + 4) (n1 + 5) (n1 + 7) lr))
           (li-none refl ∷ [])))))))))
    I₂-ls : LabelsIn lo hi (cata-br-I₂ n1 l1)
    I₂-ls =
      ++⁺ (push2-ls lo hi (n1 + 2) (n1 + 4) (n1 + 5))
          (li-lab refl L2 H2 ∷ li-lab refl L3 H3 ∷
           li-none refl ∷ li-none refl ∷ li-none refl ∷ [])

cata-ls : ∀ (st : CataStrategy) (lo n1 l1 : ℕ) (at : AbstractTrace) → lo ≤ l1 → LabelsIn lo l1 at
        → LabelsIn lo (cata-label-of (cata-dispatch st n1 l1 at))
                   (cata-trace-of (cata-dispatch st n1 l1 at))
cata-ls strat-const         lo n1 l1 at le atls = atls
cata-ls strat-nat           lo n1 l1 at le atls = cata-nat-ls lo n1 l1 at le atls
cata-ls strat-linear        lo n1 l1 at le atls = cata-linear-ls lo n1 l1 at le atls
cata-ls (strat-branching F) lo n1 l1 at le atls = cata-branching-ls F lo n1 l1 at le atls

------------------------------------------------------------------------
-- THE INDUCTION: every label an emitted fragment mentions lies in the range
-- its counter was handed. `slots-below`'s shape — each splice weakens the
-- sub-IR's window through `label-mono`.
------------------------------------------------------------------------
labels-in : ∀ {A B} (ir : IR A B) (n l : ℕ)
          → LabelsIn l (label-of (ir-to-trace' n l ir)) (trace-of (ir-to-trace' n l ir))
labels-in id       n l = li-none refl ∷ []
labels-in fst      n l = li-none refl ∷ []
labels-in snd      n l = li-none refl ∷ []
labels-in terminal n l = []
labels-in initial  n l = li-none refl ∷ []
labels-in (g ∘ f)  n l =
  ++⁺ (ls-weaken ≤-refl (label-mono g _ _) (labels-in f n l))
      (li-none refl ∷ ls-weaken (label-mono f n l) ≤-refl (labels-in g _ _))
labels-in (⟨ f , g ⟩ Stack) n l =
  li-none refl ∷ li-none refl ∷
  ++⁺ (ls-weaken ≤-refl (label-mono g _ _) (labels-in f _ l))
      (li-none refl ∷ li-none refl ∷
       ++⁺ (ls-weaken (label-mono f _ l) ≤-refl (labels-in g _ _))
           (li-none refl ∷ li-none refl ∷ []))
labels-in (⟨ f , g ⟩ Heap) n l =
  li-none refl ∷ li-none refl ∷
  ++⁺ (ls-weaken ≤-refl (label-mono g _ _) (labels-in f _ l))
      (li-none refl ∷ li-none refl ∷
       ++⁺ (ls-weaken (label-mono f _ l) ≤-refl (labels-in g _ _))
           (li-none refl ∷ li-none refl ∷ li-none refl ∷ li-none refl ∷
            li-none refl ∷ li-none refl ∷ li-none refl ∷ li-none refl ∷
            li-none refl ∷ []))
-- the closure clauses mention no ONCE label (the body marker and the code
-- address are `thunk`-provenance — D082 — and the body's own trace is
-- reachable only through `ir-to-bodies` until the flip)
labels-in (curry b Stack) n l =
  li-none refl ∷ li-none refl ∷ li-none refl ∷ li-none refl ∷ li-none refl ∷ []
labels-in (curry b Heap) n l =
  li-none refl ∷ li-none refl ∷ li-none refl ∷ li-none refl ∷ li-none refl ∷
  li-none refl ∷ li-none refl ∷ li-none refl ∷ li-none refl ∷ li-none refl ∷ []
labels-in apply n l =
  li-none refl ∷ li-none refl ∷ li-none refl ∷ li-none refl ∷ li-none refl ∷
  li-none refl ∷ li-none refl ∷ li-none refl ∷ li-none refl ∷ li-none refl ∷
  li-none refl ∷ li-none refl ∷ li-none refl ∷ li-none refl ∷ li-none refl ∷
  li-none refl ∷ li-none refl ∷ []
labels-in (inl Stack) n l =
  li-none refl ∷ li-none refl ∷ li-none refl ∷ li-none refl ∷ li-none refl ∷ []
labels-in (inr Stack) n l =
  li-none refl ∷ li-none refl ∷ li-none refl ∷ li-none refl ∷ li-none refl ∷ []
labels-in (inl Heap) n l =
  li-none refl ∷ li-none refl ∷ li-none refl ∷ li-none refl ∷ li-none refl ∷
  li-none refl ∷ li-none refl ∷ li-none refl ∷ li-none refl ∷ li-none refl ∷ []
labels-in (inr Heap) n l =
  li-none refl ∷ li-none refl ∷ li-none refl ∷ li-none refl ∷ li-none refl ∷
  li-none refl ∷ li-none refl ∷ li-none refl ∷ li-none refl ∷ li-none refl ∷ []
-- `case` owns `l` (the inl entry) and `suc l` (the join); both branches are
-- compiled above them, so all four mentions sit at the bottom of the range.
labels-in (case f g) n l =
  ++⁺ (li-lab refl ≤-refl case-l<hi ∷ li-none refl ∷ li-none refl ∷ [])
      (++⁺ (ls-weaken (≤-trans (≤-step (≤-step ≤-refl)) (label-mono f n (suc (suc l)))) ≤-refl
                      (labels-in g _ _))
           (++⁺ (li-lab refl (n≤1+n l) case-sl<hi ∷ li-lab refl ≤-refl case-l<hi ∷
                 li-none refl ∷ li-none refl ∷ [])
                (++⁺ (ls-weaken (≤-step (≤-step ≤-refl)) (label-mono g _ _)
                                (labels-in f n (suc (suc l))))
                     (li-lab refl (n≤1+n l) case-sl<hi ∷ []))))
  where
    up : suc (suc l) ≤ label-of (ir-to-trace' n l (case f g))
    up = ≤-trans (label-mono f n (suc (suc l))) (label-mono g _ _)
    case-l<hi : l < label-of (ir-to-trace' n l (case f g))
    case-l<hi = ≤-trans (≤-step ≤-refl) up
    case-sl<hi : suc l < label-of (ir-to-trace' n l (case f g))
    case-sl<hi = up
labels-in (In _ _)   n l = li-none refl ∷ []
labels-in (out-μ _)  n l = li-none refl ∷ []
labels-in (Cata {F} _ alg) n l =
  cata-ls (cata-strategy ⌈ F ⌉F) l _ _ _ (label-mono alg n l) (labels-in alg n l)
labels-in (Para _ _)     n l = []
labels-in (Out _)        n l = li-none refl ∷ []
labels-in (in-ν _ _)     n l = []
labels-in (Ana _ _)      n l = []
labels-in (Hylo _ _ _ _) n l = []
labels-in (Fuse _ _ _ _) n l = []
labels-in (free-heap _)  n l = li-none refl ∷ []
labels-in (SigOp _)      n l = li-none refl ∷ []
labels-in (const fits-int _)   n l = li-none refl ∷ []
labels-in (const fits-float _) n l = li-none refl ∷ []

------------------------------------------------------------------------
-- THE SEGMENT LEMMA (Plan 0.63, obligation (iii) — the assembly).
--
-- "A jump and its target sit in the same segment." Stated over POSITIONS
-- rather than over label ranges, because that is what the runtime invariant
-- consumes and it is insensitive to how labels are allocated:
--
--   p mentions m, q defines m  ⟹  seg-at t q st ≡ seg-at t p st
--
-- Note it quantifies over ALL positions `q` holding `c-label m`, not "the"
-- one — which is what makes label UNIQUENESS unnecessary. `find-label-lands`
-- delivers some such `q`, and any of them will do.
------------------------------------------------------------------------
-- Factored through the fetch (NOT a `with`): the `Pieces` development below
-- transports a position between a trace and an embedded copy by an equation
-- on `fetch-at`, and `cong` needs mention to be a function of it.
mention-of : Maybe AbstractInstr → Maybe ℕ
mention-of (just i) = once-label-of i
mention-of nothing  = nothing

mention-at : AbstractTrace → ℕ → Maybe ℕ
mention-at t p = mention-of (fetch-at t p)

SegAgree : AbstractTrace → Set
SegAgree t = ∀ (p q m : ℕ) (st : SegState)
           → mention-at t p ≡ just m
           → fetch-at t q ≡ just (instr-ctrl (c-label m))
           → seg-at t q st ≡ seg-at t p st

-- AN EMPTY RANGE MEANS NO LABELS, so the property is vacuous. This is the
-- workhorse: `label-mono` gives `l ≤ l'`, and for every leaf clause of
-- `ir-to-trace'` the counter does not move at all, so `labels-in` hands back a
-- window `[l, l)` that nothing can inhabit.
segagree-empty : ∀ (lo : ℕ) (t : AbstractTrace) → LabelsIn lo lo t → SegAgree t
segagree-empty lo t ls p q m st mq _ = ⊥-elim (no-mention p mq)
  where
    no-mention : ∀ (p' : ℕ) → mention-at t p' ≡ just m → ⊥
    no-mention p' eq = go t p' ls eq
      where
        go : ∀ (t' : AbstractTrace) (r : ℕ) → LabelsIn lo lo t' → mention-at t' r ≡ just m → ⊥
        go []       r       _         ()
        go (i ∷ is) zero    (x ∷ _)  e = absurd (in-range x m e)
          where absurd : (lo ≤ m) × (m < lo) → ⊥
                absurd (le , lt) = <-irrefl-aux (≤-trans lt le)
                  where <-irrefl-aux : ∀ {a} → suc a ≤ a → ⊥
                        <-irrefl-aux {suc a} (s≤s p) = <-irrefl-aux p
        go (i ∷ is) (suc r) (_ ∷ xs) e = go is r xs e

-- AN IDLE TRACE has a constant fold, so any two positions agree outright.
segagree-idle : ∀ (t : AbstractTrace) → seg-idle? t ≡ true → SegAgree t
segagree-idle t idle p q m st _ _ =
  trans (idle-seg-at t idle q st) (sym (idle-seg-at t idle p st))

-- THE COMPOSITION, and the only place containment is actually spent: a jump
-- in one part and a label in the other would put the SAME `m` in two DISJOINT
-- windows. Everything else is the two splice lemmas plus the induction
-- hypotheses.
<-asym : ∀ {a b : ℕ} → a < b → b ≤ a → ⊥
<-asym {suc a} {suc b} (s≤s p) (s≤s q) = <-asym p q

segagree-++ : ∀ (t1 t2 : AbstractTrace) (lo mid hi : ℕ)
            → LabelsIn lo mid t1 → LabelsIn mid hi t2
            → SegAgree t1 → SegAgree t2
            → SegAgree (t1 ++ t2)
segagree-++ t1 t2 lo mid hi ls1 ls2 sa1 sa2 p q m st mq lq =
  go (split-pos t1 p) (split-pos t1 q)
  where
    -- read a mention/definition back on whichever side it landed
    mentions₁ : ∀ (r : ℕ) → r < length t1 → mention-at (t1 ++ t2) r ≡ just m → mention-at t1 r ≡ just m
    mentions₁ r lt e rewrite fetch-++ˡ t1 t2 r lt = e
    mentions₂ : ∀ (k : ℕ) → mention-at (t1 ++ t2) (length t1 + k) ≡ just m → mention-at t2 k ≡ just m
    mentions₂ k e rewrite fetch-++ʳ t1 t2 k = e
    defines₁ : ∀ (r : ℕ) → r < length t1
             → fetch-at (t1 ++ t2) r ≡ just (instr-ctrl (c-label m))
             → fetch-at t1 r ≡ just (instr-ctrl (c-label m))
    defines₁ r lt e = trans (sym (fetch-++ˡ t1 t2 r lt)) e
    defines₂ : ∀ (k : ℕ) → fetch-at (t1 ++ t2) (length t1 + k) ≡ just (instr-ctrl (c-label m))
             → fetch-at t2 k ≡ just (instr-ctrl (c-label m))
    defines₂ k e = trans (sym (fetch-++ʳ t1 t2 k)) e
    -- a mention in `t1` puts `m` below `mid`; a definition in `t2` puts it at
    -- or above `mid`. That is the contradiction.
    inʟ : ∀ (r : ℕ) → r < length t1 → mention-at t1 r ≡ just m → m < mid
    inʟ r lt e = proj₂ (walk t1 r ls1 e)
      where walk : ∀ (t : AbstractTrace) (r' : ℕ) → LabelsIn lo mid t
                 → mention-at t r' ≡ just m → (lo ≤ m) × (m < mid)
            walk []       _       _        ()
            walk (i ∷ is) zero    (x ∷ _)  e' = in-range x m e'
            walk (i ∷ is) (suc r') (_ ∷ xs) e' = walk is r' xs e'
    inʀ : ∀ (k : ℕ) → mention-at t2 k ≡ just m → mid ≤ m
    inʀ k e = proj₁ (walk t2 k ls2 e)
      where walk : ∀ (t : AbstractTrace) (k' : ℕ) → LabelsIn mid hi t
                 → mention-at t k' ≡ just m → (mid ≤ m) × (m < hi)
            walk []       _        _        ()
            walk (i ∷ is) zero     (x ∷ _)  e' = in-range x m e'
            walk (i ∷ is) (suc k') (_ ∷ xs) e' = walk is k' xs e'
    -- a DEFINITION is also a mention (`c-label m` has `once-label-of ≡ just m`)
    def→men : ∀ (t : AbstractTrace) (r : ℕ)
            → fetch-at t r ≡ just (instr-ctrl (c-label m)) → mention-at t r ≡ just m
    def→men t r e rewrite e = refl
    go : (p < length t1) ⊎ (Σ ℕ (λ k → p ≡ length t1 + k))
       → (q < length t1) ⊎ (Σ ℕ (λ k → q ≡ length t1 + k))
       → seg-at (t1 ++ t2) q st ≡ seg-at (t1 ++ t2) p st
    go (inj₁ pl) (inj₁ ql) =
      trans (seg-at-++ˡ t1 t2 q st ql)
            (trans (sa1 p q m st (mentions₁ p pl mq) (defines₁ q ql lq))
                   (sym (seg-at-++ˡ t1 t2 p st pl)))
    -- (no `rewrite`: it would move the GOAL off `p`/`q` while `mq`/`lq` still
    -- mention them. Both sides are transported explicitly instead.)
    go (inj₂ (pk , peq)) (inj₂ (qk , qeq)) =
      subst₂ (λ a b → seg-at (t1 ++ t2) b st ≡ seg-at (t1 ++ t2) a st) (sym peq) (sym qeq)
        (trans (seg-at-++ʳ t1 t2 qk st)
               (trans (sa2 pk qk m (seg-fold t1 st)
                           (mentions₂ pk (subst (λ z → mention-at (t1 ++ t2) z ≡ just m) peq mq))
                           (defines₂ qk (subst (λ z → fetch-at (t1 ++ t2) z ≡ just (instr-ctrl (c-label m))) qeq lq)))
                      (sym (seg-at-++ʳ t1 t2 pk st))))
    go (inj₁ pl) (inj₂ (qk , qeq)) =
      ⊥-elim (<-asym (inʟ p pl (mentions₁ p pl mq))
                     (inʀ qk (def→men t2 qk
                       (defines₂ qk (subst (λ z → fetch-at (t1 ++ t2) z ≡ just (instr-ctrl (c-label m))) qeq lq)))))
    go (inj₂ (pk , peq)) (inj₁ ql) =
      ⊥-elim (<-asym (inʟ q ql (def→men t1 q (defines₁ q ql lq)))
                     (inʀ pk (mentions₂ pk (subst (λ z → mention-at (t1 ++ t2) z ≡ just m) peq mq))))

-- THE COMPOSITION, GENERALIZED (needed by the cata skeletons). Along a trace
-- the label windows are NOT in increasing order: `cata-trace-nat` emits its
-- own `descend` labels `[l1, l1+6)` BEFORE splicing the algebra, whose labels
-- are `[l, l1)` — below, not above. So the two parts only have to be
-- DISJOINT, in either order.
segagree-++' : ∀ (t1 t2 : AbstractTrace) (a b c d : ℕ)
             → LabelsIn a b t1 → LabelsIn c d t2
             → (b ≤ c) ⊎ (d ≤ a)
             → SegAgree t1 → SegAgree t2
             → SegAgree (t1 ++ t2)
segagree-++' t1 t2 a b c d ls1 ls2 disj sa1 sa2 p q m st mq lq =
  go (split-pos t1 p) (split-pos t1 q)
  where
    mentions₁ : ∀ (r : ℕ) → r < length t1 → mention-at (t1 ++ t2) r ≡ just m → mention-at t1 r ≡ just m
    mentions₁ r lt e rewrite fetch-++ˡ t1 t2 r lt = e
    mentions₂ : ∀ (k : ℕ) → mention-at (t1 ++ t2) (length t1 + k) ≡ just m → mention-at t2 k ≡ just m
    mentions₂ k e rewrite fetch-++ʳ t1 t2 k = e
    defines₁ : ∀ (r : ℕ) → r < length t1
             → fetch-at (t1 ++ t2) r ≡ just (instr-ctrl (c-label m))
             → fetch-at t1 r ≡ just (instr-ctrl (c-label m))
    defines₁ r lt e = trans (sym (fetch-++ˡ t1 t2 r lt)) e
    defines₂ : ∀ (k : ℕ) → fetch-at (t1 ++ t2) (length t1 + k) ≡ just (instr-ctrl (c-label m))
             → fetch-at t2 k ≡ just (instr-ctrl (c-label m))
    defines₂ k e = trans (sym (fetch-++ʳ t1 t2 k)) e
    win : ∀ (t : AbstractTrace) (lo hi r : ℕ) → LabelsIn lo hi t
        → mention-at t r ≡ just m → (lo ≤ m) × (m < hi)
    win []       lo hi _        _        ()
    win (i ∷ is) lo hi zero     (x ∷ _)  e = in-range x m e
    win (i ∷ is) lo hi (suc r') (_ ∷ xs) e = win is lo hi r' xs e
    def→men : ∀ (t : AbstractTrace) (r : ℕ)
            → fetch-at t r ≡ just (instr-ctrl (c-label m)) → mention-at t r ≡ just m
    def→men t r e rewrite e = refl
    -- `m` in both windows is impossible, whichever way round they sit
    clash : (a ≤ m) × (m < b) → (c ≤ m) × (m < d) → ⊥
    clash (a≤ , <b) (c≤ , <d) = dis disj
      where dis : (b ≤ c) ⊎ (d ≤ a) → ⊥
            dis (inj₁ b≤c) = <-asym <b (≤-trans b≤c c≤)
            dis (inj₂ d≤a) = <-asym <d (≤-trans d≤a a≤)
    go : (p < length t1) ⊎ (Σ ℕ (λ k → p ≡ length t1 + k))
       → (q < length t1) ⊎ (Σ ℕ (λ k → q ≡ length t1 + k))
       → seg-at (t1 ++ t2) q st ≡ seg-at (t1 ++ t2) p st
    go (inj₁ pl) (inj₁ ql) =
      trans (seg-at-++ˡ t1 t2 q st ql)
            (trans (sa1 p q m st (mentions₁ p pl mq) (defines₁ q ql lq))
                   (sym (seg-at-++ˡ t1 t2 p st pl)))
    go (inj₂ (pk , peq)) (inj₂ (qk , qeq)) =
      subst₂ (λ x y → seg-at (t1 ++ t2) y st ≡ seg-at (t1 ++ t2) x st) (sym peq) (sym qeq)
        (trans (seg-at-++ʳ t1 t2 qk st)
               (trans (sa2 pk qk m (seg-fold t1 st)
                           (mentions₂ pk (subst (λ z → mention-at (t1 ++ t2) z ≡ just m) peq mq))
                           (defines₂ qk (subst (λ z → fetch-at (t1 ++ t2) z ≡ just (instr-ctrl (c-label m))) qeq lq)))
                      (sym (seg-at-++ʳ t1 t2 pk st))))
    go (inj₁ pl) (inj₂ (qk , qeq)) =
      ⊥-elim (clash (win t1 a b p ls1 (mentions₁ p pl mq))
                    (win t2 c d qk ls2 (def→men t2 qk
                      (defines₂ qk (subst (λ z → fetch-at (t1 ++ t2) z ≡ just (instr-ctrl (c-label m))) qeq lq)))))
    go (inj₂ (pk , peq)) (inj₁ ql) =
      ⊥-elim (clash (win t1 a b q ls1 (def→men t1 q (defines₁ q ql lq)))
                    (win t2 c d pk ls2 (mentions₂ pk (subst (λ z → mention-at (t1 ++ t2) z ≡ just m) peq mq))))

-- …and the no-label discharge, for fragments that mention nothing at all
-- regardless of how wide their range is (every closure clause, `apply`, the
-- four injections). `segagree-empty` covers only the empty-range case.
NoLab : AbstractTrace → Set
NoLab = All (λ i → once-label-of i ≡ nothing)

segagree-nolab : ∀ (t : AbstractTrace) → NoLab t → SegAgree t
segagree-nolab t nl p q m st mq _ = ⊥-elim (go t p nl mq)
  where go : ∀ (t' : AbstractTrace) (r : ℕ) → NoLab t' → mention-at t' r ≡ just m → ⊥
        go []       r       _        ()
        go (i ∷ is) zero    (e ∷ _)  eq rewrite e = absurd eq
          where absurd : ∀ {A : Set} → nothing ≡ just m → A
                absurd ()
        go (i ∷ is) (suc r) (_ ∷ xs) eq = go is r xs eq

------------------------------------------------------------------------
-- PIECES: a skeleton with embedded copies of ONE sub-trace.
--
-- Every cata skeleton has this shape — an alternation of idle skeleton
-- fragments and copies of the ALGEBRA trace — and the copy count differs per
-- strategy: `strat-const` 0 (the trace IS the algebra), `strat-branching` 1,
-- and **`strat-nat` and `strat-linear` 2** (base path plus the ascend body).
-- So Nat is not a bystander here: it is one of the two cases that `Pieces`
-- exists for. The `pnil`/`pcons` structure covers 0, 1, 2, … uniformly, so all
-- four strategies land on the same lemma.
--
-- Why a datatype rather than repeated `segagree-++'`: two copies of the SAME
-- trace carry the SAME label window, so the disjointness premise is
-- unsatisfiable against itself — a jump in one copy and its label in the other
-- mention the same `m` LEGITIMATELY. What closes that case is not disjointness
-- but the fact that both copies START FROM THE SAME STATE, which is what this
-- induction makes available.
------------------------------------------------------------------------
data Pieces (at : AbstractTrace) (a b : ℕ) : AbstractTrace → Set where
  pnil  : ∀ {I} → seg-idle? I ≡ true → LabelsIn a b I → Pieces at a b I
  pcons : ∀ {I t} → seg-idle? I ≡ true → LabelsIn a b I → Pieces at a b t
        → Pieces at a b (I ++ at ++ t)

-- THE WHOLE IS NEUTRAL: idle pieces are, and the algebra is (`SegOK.ok-neu`).
-- This is what makes every copy start where the last one left off, i.e. at
-- `st`.
pieces-neutral : ∀ (at : AbstractTrace) (a b : ℕ) (t : AbstractTrace) → Pieces at a b t
               → (∀ st → seg-fold at st ≡ st)
               → ∀ (st : SegState) → seg-fold t st ≡ st
pieces-neutral at a b .I (pnil {I} idle _) natl st = idle-neutral I idle st
pieces-neutral at a b .(I ++ at ++ t) (pcons {I} {t} idle _ ps) natl st =
  trans (seg-fold-++ I (at ++ t) st)
        (trans (cong (seg-fold (at ++ t)) (idle-neutral I idle st))
               (trans (seg-fold-++ at t st)
                      (trans (cong (seg-fold t) (natl st))
                             (pieces-neutral at a b t ps natl st))))

-- EVERY POSITION IS ONE OF TWO KINDS: a skeleton position, whose segment is
-- the starting state and whose mention (if any) is in the skeleton window; or
-- a position INSIDE some copy, which fetches exactly what the algebra fetches
-- at the corresponding offset and has the algebra's segment there.
data PosView (at : AbstractTrace) (a b : ℕ) (t : AbstractTrace)
             (st : SegState) (p : ℕ) : Set where
  pv-skel : seg-at t p st ≡ st
          → (∀ (m : ℕ) → mention-at t p ≡ just m → (a ≤ m) × (m < b))
          → PosView at a b t st p
  pv-at   : ∀ (k : ℕ) → seg-at t p st ≡ seg-at at k st
          → fetch-at t p ≡ fetch-at at k
          → PosView at a b t st p

-- the skeleton window fact, read off a `LabelsIn` at a position
win-at : ∀ (a b : ℕ) (t : AbstractTrace) → LabelsIn a b t
       → ∀ (p m : ℕ) → mention-at t p ≡ just m → (a ≤ m) × (m < b)
win-at a b []       _        p       m ()
win-at a b (i ∷ is) (x ∷ _)  zero    m e = in-range x m e
win-at a b (i ∷ is) (_ ∷ xs) (suc p) m e = win-at a b is xs p m e

pieces-pos : ∀ (at : AbstractTrace) (a b : ℕ) (t : AbstractTrace) → Pieces at a b t
           → (∀ st → seg-fold at st ≡ st)
           → ∀ (p : ℕ) (st : SegState) → PosView at a b t st p
pieces-pos at a b .I (pnil {I} idle ls) natl p st =
  pv-skel (idle-seg-at I idle p st) (win-at a b I ls p)
pieces-pos at a b .(I ++ at ++ t) (pcons {I} {t} idle ls ps) natl p st =
  go (split-pos I p)
  where
    go : (p < length I) ⊎ (Σ ℕ (λ k → p ≡ length I + k))
       → PosView at a b (I ++ at ++ t) st p
    -- inside the skeleton piece
    go (inj₁ lt) =
      pv-skel (trans (seg-at-++ˡ I (at ++ t) p st lt) (idle-seg-at I idle p st))
              (λ m e → win-at a b I ls p m (trans (sym (cong mention-of (fetch-++ˡ I (at ++ t) p lt))) e))
    go (inj₂ (k , peq)) = go2 (split-pos at k)
      where
        -- the piece is idle, so the copy starts exactly at `st`
        at-st : seg-at (I ++ at ++ t) p st ≡ seg-at (at ++ t) k st
        at-st = trans (cong (λ z → seg-at (I ++ at ++ t) z st) peq)
                      (trans (seg-at-++ʳ I (at ++ t) k st)
                             (cong (seg-at (at ++ t) k) (idle-neutral I idle st)))
        ft-eq : fetch-at (I ++ at ++ t) p ≡ fetch-at (at ++ t) k
        ft-eq = trans (cong (fetch-at (I ++ at ++ t)) peq) (fetch-++ʳ I (at ++ t) k)
        go2 : (k < length at) ⊎ (Σ ℕ (λ j → k ≡ length at + j))
            → PosView at a b (I ++ at ++ t) st p
        -- inside THIS copy of the algebra
        go2 (inj₁ klt) =
          pv-at k (trans at-st (seg-at-++ˡ at t k st klt))
                  (trans ft-eq (fetch-++ˡ at t k klt))
        -- past it: recurse, and lift whichever kind the tail reports
        go2 (inj₂ (j , keq)) = lift (pieces-pos at a b t ps natl j st)
          where
            tail-st : seg-at (I ++ at ++ t) p st ≡ seg-at t j st
            tail-st = trans at-st
                        (trans (cong (λ z → seg-at (at ++ t) z st) keq)
                               (trans (seg-at-++ʳ at t j st)
                                      (cong (seg-at t j) (natl st))))
            tail-ft : fetch-at (I ++ at ++ t) p ≡ fetch-at t j
            tail-ft = trans ft-eq (trans (cong (fetch-at (at ++ t)) keq) (fetch-++ʳ at t j))
            lift : PosView at a b t st j → PosView at a b (I ++ at ++ t) st p
            lift (pv-skel seq wf) =
              pv-skel (trans tail-st seq)
                      (λ m e → wf m (trans (sym (cong mention-of tail-ft)) e))
            lift (pv-at k' seq feq) =
              pv-at k' (trans tail-st seq) (trans tail-ft feq)

-- THE PAYOFF. Four cases, and the one that defeated `segagree-++'` — a
-- mention in one copy with its label in ANOTHER copy — is now closed by
-- `SegAgree at` applied at the two offsets, because both copies fetch from the
-- same trace at the same starting state.
pieces-agree : ∀ (at : AbstractTrace) (a b c d : ℕ) (t : AbstractTrace)
             → Pieces at a b t
             → (∀ st → seg-fold at st ≡ st)
             → SegAgree at → LabelsIn c d at
             → (b ≤ c) ⊎ (d ≤ a)
             → SegAgree t
pieces-agree at a b c d t ps natl saAt lsAt disj p q m st mq lq =
  go (pieces-pos at a b t ps natl p st) (pieces-pos at a b t ps natl q st)
  where
    lq-men : mention-at t q ≡ just m
    lq-men rewrite lq = refl
    clash : (a ≤ m) × (m < b) → (c ≤ m) × (m < d) → ⊥
    clash (a≤ , <b) (c≤ , <d) = dis disj
      where dis : (b ≤ c) ⊎ (d ≤ a) → ⊥
            dis (inj₁ b≤c) = <-asym <b (≤-trans b≤c c≤)
            dis (inj₂ d≤a) = <-asym <d (≤-trans d≤a a≤)
    go : PosView at a b t st p → PosView at a b t st q → seg-at t q st ≡ seg-at t p st
    -- both on the skeleton: both segments are the starting state
    go (pv-skel sp _) (pv-skel sq _) = trans sq (sym sp)
    -- one on the skeleton, one inside a copy: the same `m` would have to sit
    -- in both windows
    go (pv-skel _ wp) (pv-at kq _ fq) =
      ⊥-elim (clash (wp m mq)
                    (win-at c d at lsAt kq m (trans (sym (cong mention-of fq)) lq-men)))
    go (pv-at kp _ fp) (pv-skel _ wq) =
      ⊥-elim (clash (wq m lq-men)
                    (win-at c d at lsAt kp m (trans (sym (cong mention-of fp)) mq)))
    -- BOTH INSIDE COPIES (possibly different ones): reduce to the algebra
    go (pv-at kp sp fp) (pv-at kq sq fq) =
      trans sq (trans (saAt kp kq m st
                        (trans (sym (cong mention-of fp)) mq)
                        (trans (sym fq) lq))
                      (sym sp))

-- The skeletons nest their splices as `(at ++ X) ++ Y` rather than associating
-- to the right, so a witness needs one transport per nested copy. `Pieces` is
-- a datatype, so this is `refl`-matching.
pieces-≡ : ∀ {at : AbstractTrace} {a b : ℕ} {t t' : AbstractTrace}
         → t ≡ t' → Pieces at a b t → Pieces at a b t'
pieces-≡ refl ps = ps

------------------------------------------------------------------------
-- THE `cata-nat` WITNESS. This is what the `IRToTrace` refactor bought: the
-- skeleton decomposes DEFINITIONALLY, so the witness is two `pcons` and a
-- `pnil` with no transcription and no `++-assoc` transport.
------------------------------------------------------------------------
cata-nat-pieces : ∀ (n1 l1 : ℕ) (at : AbstractTrace)
                → Pieces at l1 (suc (suc (suc (suc (suc (suc l1))))))
                         (cata-trace-of (cata-dispatch strat-nat n1 l1 at))
cata-nat-pieces n1 l1 at =
  pcons refl I₁-ls (pcons refl I₂-ls (pnil refl I₃-ls))
  where
    hi = suc (suc (suc (suc (suc (suc l1)))))
    L0 : l1 ≤ l1
    L0 = ≤-refl
    L1 : l1 ≤ suc l1
    L1 = ≤-step L0
    L2 : l1 ≤ suc (suc l1)
    L2 = ≤-step L1
    L3 : l1 ≤ suc (suc (suc l1))
    L3 = ≤-step L2
    L4 : l1 ≤ suc (suc (suc (suc l1)))
    L4 = ≤-step L3
    L5 : l1 ≤ suc (suc (suc (suc (suc l1))))
    L5 = ≤-step L4
    H0 : l1 < hi
    H0 = ≤-step (≤-step (≤-step (≤-step (≤-step ≤-refl))))
    H1 : suc l1 < hi
    H1 = ≤-step (≤-step (≤-step (≤-step ≤-refl)))
    H2 : suc (suc l1) < hi
    H2 = ≤-step (≤-step (≤-step ≤-refl))
    H3 : suc (suc (suc l1)) < hi
    H3 = ≤-step (≤-step ≤-refl)
    H4 : suc (suc (suc (suc l1))) < hi
    H4 = ≤-step ≤-refl
    H5 : suc (suc (suc (suc (suc l1)))) < hi
    H5 = ≤-refl
    I₁-ls : LabelsIn l1 hi (cata-nat-I₁ n1 l1)
    I₁-ls =
      li-none refl ∷ li-none refl ∷
      li-lab refl L0 H0 ∷ li-lab refl L1 H1 ∷ li-lab refl L2 H2 ∷
      li-none refl ∷ li-none refl ∷ li-none refl ∷
      li-lab refl L3 H3 ∷ li-lab refl L2 H2 ∷ li-none refl ∷
      li-lab refl L3 H3 ∷ li-lab refl L0 H0 ∷ li-lab refl L1 H1 ∷
      li-none refl ∷ li-none refl ∷ li-none refl ∷
      li-none refl ∷ li-none refl ∷ li-none refl ∷ li-none refl ∷ li-none refl ∷
      li-none refl ∷ li-none refl ∷ li-none refl ∷ li-none refl ∷ li-none refl ∷
      li-none refl ∷ []
    I₂-ls : LabelsIn l1 hi (cata-nat-I₂ n1 l1)
    I₂-ls =
      li-lab refl L4 H4 ∷ li-lab refl L5 H5 ∷ li-none refl ∷
      li-none refl ∷ li-none refl ∷ li-none refl ∷ li-none refl ∷ li-none refl ∷
      li-none refl ∷ li-none refl ∷ li-none refl ∷ li-none refl ∷ li-none refl ∷
      li-none refl ∷ []
    I₃-ls : LabelsIn l1 hi (cata-nat-I₃ l1)
    I₃-ls = li-none refl ∷ li-lab refl L4 H4 ∷ li-lab refl L5 H5 ∷ []

-- …and the other two skeletons. `linear` has two copies like `nat`;
-- `branching` has ONE, so its witness is a single `pcons`.
cata-lin-pieces : ∀ (n1 l1 : ℕ) (at : AbstractTrace)
                → Pieces at l1 (suc (suc (suc (suc l1))))
                         (cata-trace-of (cata-dispatch strat-linear n1 l1 at))
cata-lin-pieces n1 l1 at =
  pcons refl I₁-ls (pcons refl I₂-ls (pnil refl I₃-ls))
  where
    hi = suc (suc (suc (suc l1)))
    L0 : l1 ≤ l1
    L0 = ≤-refl
    L1 : l1 ≤ suc l1
    L1 = ≤-step L0
    L2 : l1 ≤ suc (suc l1)
    L2 = ≤-step L1
    L3 : l1 ≤ suc (suc (suc l1))
    L3 = ≤-step L2
    H0 : l1 < hi
    H0 = ≤-step (≤-step (≤-step ≤-refl))
    H1 : suc l1 < hi
    H1 = ≤-step (≤-step ≤-refl)
    H2 : suc (suc l1) < hi
    H2 = ≤-step ≤-refl
    H3 : suc (suc (suc l1)) < hi
    H3 = ≤-refl
    I₁-ls : LabelsIn l1 hi (cata-lin-I₁ n1 l1)
    I₁-ls =
      li-none refl ∷ li-none refl ∷ li-none refl ∷
      li-lab refl L0 H0 ∷ li-lab refl L1 H1 ∷
      li-none refl ∷ li-none refl ∷ li-none refl ∷ li-none refl ∷ li-none refl ∷
      li-none refl ∷ li-none refl ∷ li-none refl ∷ li-none refl ∷ li-none refl ∷
      li-none refl ∷ li-none refl ∷ li-none refl ∷ li-none refl ∷ li-none refl ∷
      li-none refl ∷ li-none refl ∷ li-none refl ∷
      li-lab refl L0 H0 ∷ li-lab refl L1 H1 ∷ li-none refl ∷ []
    I₂-ls : LabelsIn l1 hi (cata-lin-I₂ n1 l1)
    I₂-ls =
      li-lab refl L2 H2 ∷ li-lab refl L3 H3 ∷
      li-none refl ∷ li-none refl ∷ li-none refl ∷ li-none refl ∷ li-none refl ∷
      li-none refl ∷ li-none refl ∷ li-none refl ∷ li-none refl ∷ li-none refl ∷
      li-none refl ∷ li-none refl ∷ li-none refl ∷ li-none refl ∷ li-none refl ∷
      li-none refl ∷ li-none refl ∷ li-none refl ∷ li-none refl ∷ li-none refl ∷
      li-none refl ∷ li-none refl ∷ li-none refl ∷ []
    I₃-ls : LabelsIn l1 hi (cata-lin-I₃ l1)
    I₃-ls = li-none refl ∷ li-lab refl L2 H2 ∷ li-lab refl L3 H3 ∷ []

cata-br-pieces : ∀ (F : Functor) (n1 l1 : ℕ) (at : AbstractTrace)
               → Pieces at l1 (l1 + 4 + lsize F + lsize F)
                        (cata-trace-of (cata-dispatch (strat-branching F) n1 l1 at))
cata-br-pieces F n1 l1 at = pcons I₁-idle I₁-ls (pnil refl I₂-ls)
  where
    lv = l1 + 4
    lr = lv + lsize F
    hi = lr + lsize F
    lv≤lr : lv ≤ lr
    lv≤lr = m≤m+n lv (lsize F)
    top : lv ≤ hi
    top = ≤-trans lv≤lr (m≤m+n lr (lsize F))
    L0 : l1 ≤ l1
    L0 = ≤-refl
    L1 : l1 ≤ suc l1
    L1 = ≤-step L0
    L2 : l1 ≤ l1 + 2
    L2 = m≤m+n l1 2
    L3 : l1 ≤ l1 + 3
    L3 = m≤m+n l1 3
    H0 : l1 < hi
    H0 = <-transˡ (a<a+suc l1 3) top
    H1 : suc l1 < hi
    H1 = <-transˡ (sa<a+ss l1 2) top
    H2 : l1 + 2 < hi
    H2 = <-transˡ (+lt l1 2 4 (s≤s (s≤s (s≤s z≤n)))) top
    H3 : l1 + 3 < hi
    H3 = <-transˡ (+lt l1 3 4 (s≤s (s≤s (s≤s (s≤s z≤n))))) top
    I₁-idle : seg-idle? (cata-br-I₁ F n1 l1) ≡ true
    I₁-idle = idle-++ (visit-walk n1 (n1 + 4) (n1 + 5) F (n1 + 7) lv) _
                (visit-idle F n1 (n1 + 4) (n1 + 5) (n1 + 7) lv)
                (idle-++ (rebuild-walk (n1 + 2) (n1 + 4) (n1 + 5) F (n1 + 7) lr) _
                  (rebuild-idle F (n1 + 2) (n1 + 4) (n1 + 5) (n1 + 7) lr) refl)
    I₁-ls : LabelsIn l1 hi (cata-br-I₁ F n1 l1)
    I₁-ls =
      ++⁺ (li-none refl ∷ li-none refl ∷ li-none refl ∷ li-none refl ∷ li-none refl ∷
           li-none refl ∷ li-none refl ∷ li-none refl ∷ li-none refl ∷ li-none refl ∷
           li-none refl ∷ li-none refl ∷ li-none refl ∷ li-none refl ∷ [])
      (++⁺ (push2-ls l1 hi n1 (n1 + 4) (n1 + 5))
      (++⁺ (li-lab refl L0 H0 ∷ li-none refl ∷ li-none refl ∷
            li-lab refl L1 H1 ∷ li-none refl ∷ li-none refl ∷
            li-none refl ∷ li-none refl ∷ li-none refl ∷ li-none refl ∷ [])
      (++⁺ (push2-ls l1 hi (suc n1) (n1 + 4) (n1 + 5))
      (++⁺ (li-none refl ∷ li-none refl ∷ [])
      (++⁺ (ls-weaken (m≤m+n l1 4) (m≤m+n lr (lsize F))
                      (visit-ls F n1 (n1 + 4) (n1 + 5) (n1 + 7) lv))
      (++⁺ (li-lab refl L0 H0 ∷ li-lab refl L1 H1 ∷ [])
      (++⁺ (li-lab refl L2 H2 ∷ li-none refl ∷ li-none refl ∷
            li-lab refl L3 H3 ∷ li-none refl ∷ li-none refl ∷
            li-none refl ∷ li-none refl ∷ [])
      (++⁺ (ls-weaken (≤-trans (m≤m+n l1 4) lv≤lr) ≤-refl
                      (rebuild-ls F (n1 + 2) (n1 + 4) (n1 + 5) (n1 + 7) lr))
           (li-none refl ∷ [])))))))))
    I₂-ls : LabelsIn l1 hi (cata-br-I₂ n1 l1)
    I₂-ls =
      ++⁺ (push2-ls l1 hi (n1 + 2) (n1 + 4) (n1 + 5))
          (li-lab refl L2 H2 ∷ li-lab refl L3 H3 ∷
           li-none refl ∷ li-none refl ∷ li-none refl ∷ [])

-- (superseded note) WHY THE CATA WITNESSES WERE NOT HERE (2026-08-04, measured by attempting
-- them): a `Pieces` witness has to name the skeleton fragments, and in
-- `cata-trace-nat` / `-linear` / `-branching` they are `let`-bound INSIDE the
-- function (`descend-flat`, `build-layer`, `ascend-body`, `ascend-flat`, …) —
-- none is exported, so the witness would have to transcribe ~28 + ~15 + 3
-- instructions for the nat skeleton alone, and again for the other two. That
-- is duplication of the emitter's own definition, and it would rot silently
-- the moment the codegen is touched.
--
-- THE FIX IS IN `IRToTrace`, not here: lift those `let`s to top level, so
-- `cata-trace-nat n1 l1 at` reads `I₁ n1 l1 ++ at ++ (I₂ n1 l1 ++ at ++ I₃ l1)`
-- definitionally. Then every witness is `pcons refl … (pcons refl … (pnil …))`
-- with no transcription and no `++-assoc` transport. The emitted trace is
-- unchanged by construction, but the RIPPLE is real and worth budgeting: every
-- proof that pattern-matches the current shape moves with it —
-- `SlotBudget.cata-nat-below`, `FrameFreeTrace.cata-nat-ff`, `AllocMin`,
-- `CataIRSlotStable`, and `cata-nat-ls` above.

-- the strategy dispatch for the three witnesses. `strat-const`'s trace IS the
-- algebra, so it is `pnil`-free: one copy with empty skeleton either side.
cata-pieces : ∀ (st : CataStrategy) (n1 l1 : ℕ) (at : AbstractTrace)
            → Pieces at l1 (cata-label-of (cata-dispatch st n1 l1 at))
                     (cata-trace-of (cata-dispatch st n1 l1 at))
-- `strat-const`'s trace IS the algebra, so this is one copy with empty
-- skeleton on both sides — modulo `xs ++ [] ≡ xs`.
cata-pieces strat-const         n1 l1 at =
  pieces-≡ (++-identityʳ at) (pcons refl [] (pnil refl []))
cata-pieces strat-nat           n1 l1 at = cata-nat-pieces n1 l1 at
cata-pieces strat-linear        n1 l1 at = cata-lin-pieces n1 l1 at
cata-pieces (strat-branching F) n1 l1 at = cata-br-pieces F n1 l1 at

-- a label-free prefix in front of a fragment: the prefix's window is EMPTY,
-- so it is trivially disjoint from whatever follows.
nolab-any : ∀ (a : ℕ) (t : AbstractTrace) → NoLab t → LabelsIn a a t
nolab-any a []       []       = []
nolab-any a (i ∷ is) (e ∷ es) = li-none e ∷ nolab-any a is es

segagree-pre : ∀ (pre : AbstractTrace) {t : AbstractTrace} (a c d : ℕ)
             → NoLab pre → LabelsIn c d t → a ≤ c
             → SegAgree t → SegAgree (pre ++ t)
segagree-pre pre {t} a c d nl lst le sat =
  segagree-++' pre t a a c d (nolab-any a pre nl) lst (inj₁ le)
               (segagree-nolab pre nl) sat

------------------------------------------------------------------------
-- THE INDUCTION — MEASURED, NOT LANDED (2026-08-05). Attempting it settled
-- the shape, which is the point of closing the island top-down.
--
-- WHAT COMPOSES with what is above: the leaves (`segagree-empty` — an empty
-- range means no labels), the closure clauses / `apply` / the four injections
-- (`segagree-nolab`), `∘` and both pair clauses (`segagree-++'` with
-- `segagree-pre` for the concrete brackets), and **`Cata` — via
-- `pieces-agree` with `cata-pieces`**, the skeleton window `[l1, l2)` sitting
-- ABOVE the algebra's `[l, l1)` so the disjointness is the right disjunct.
--
-- WHAT DOES NOT, and it is `case`. Its skeleton labels `l` (the inl entry) and
-- `suc l` (the join) appear BOTH before `gt` and in the bracket between `gt`
-- and `ft` — so the skeleton window is INTERLEAVED with the branch windows,
-- exactly as in the cata skeletons. A left-to-right `segagree-++'` chain
-- cannot express that: whichever way the split is drawn, both sides mention
-- skeleton labels.
--
-- SO `case` NEEDS A `Pieces` VARIANT, and a small one: unlike the cata
-- skeletons, its two embedded traces are DIFFERENT (`ft` and `gt`) and their
-- windows are DISJOINT, so the cross case closes by a window clash rather than
-- by the same-trace argument. Concretely, a `Pieces` whose `pcons` carries the
-- embedded trace together with its own neutrality, `SegAgree`, and window —
-- roughly 100 lines mirroring `pieces-pos`/`pieces-agree`, with the extra
-- premise that distinct embedded windows are disjoint.
--
-- Everything below the induction is landed and green and is needed either way.
------------------------------------------------------------------------
