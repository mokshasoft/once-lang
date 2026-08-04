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
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.All.Properties using (++⁺)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)

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
  ; push2; pop2; wrap-sum; visit-walk; rebuild-walk)
open import Once.CCC.Codegen.LabelRange using (label-of; cata-label-of; label-mono; cata-label-mono)

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
  li-none refl ∷ li-none refl ∷
  ++⁺ descend
      (li-none refl ∷ li-none refl ∷ li-none refl ∷
       ++⁺ (layer 0)
           (li-none refl ∷ ++⁺ at' ascend))
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
    ascend : LabelsIn lo hi _
    ascend =
      li-lab refl L4 H4 ∷ li-lab refl L5 H5 ∷
      ++⁺ (li-none refl ∷ ++⁺ (layer 1) (li-none refl ∷ ++⁺ at' (li-none refl ∷ [])))
          (li-lab refl L4 H4 ∷ li-lab refl L5 H5 ∷ [])

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
cata-branching-ls F lo n1 l1 at lo≤l1 atls =
  ++⁺ init (++⁺ flatten (++⁺ fold final))
  where
    lv = l1 + 4
    lr = lv + lsize F
    hi = lr + lsize F
    lv≤lr : lv ≤ lr
    lv≤lr = m≤m+n lv (lsize F)
    L0 : lo ≤ l1
    L0 = lo≤l1
    L1 : lo ≤ suc l1
    L1 = ≤-step L0
    L2 : lo ≤ l1 + 2
    L2 = ≤-trans L0 (m≤m+n l1 2)
    L3 : lo ≤ l1 + 3
    L3 = ≤-trans L0 (m≤m+n l1 3)
    l1≤hi : l1 ≤ hi
    l1≤hi = ≤-trans (m≤m+n l1 4) (≤-trans lv≤lr (m≤m+n lr (lsize F)))
    H0 : l1 < hi
    H0 = <-transˡ (a<a+suc l1 3) (≤-trans lv≤lr (m≤m+n lr (lsize F)))
    H1 : suc l1 < hi
    H1 = <-transˡ (sa<a+ss l1 2) (≤-trans lv≤lr (m≤m+n lr (lsize F)))
    H2 : l1 + 2 < hi
    H2 = <-transˡ (+lt l1 2 4 (s≤s (s≤s (s≤s z≤n))))
                  (≤-trans lv≤lr (m≤m+n lr (lsize F)))
    H3 : l1 + 3 < hi
    H3 = <-transˡ (+lt l1 3 4 (s≤s (s≤s (s≤s (s≤s z≤n)))))
                  (≤-trans lv≤lr (m≤m+n lr (lsize F)))
    at' : LabelsIn lo hi at
    at' = ls-weaken ≤-refl (≤-trans lo≤l1' l1≤hi) atls
      where lo≤l1' : l1 ≤ l1
            lo≤l1' = ≤-refl
    -- the VISIT walk's window `[lv, lv + lsize F)` sits below the rebuild's
    visit' : LabelsIn lo hi (visit-walk n1 (n1 + 4) (n1 + 5) F (n1 + 7) lv)
    visit' = ls-weaken (≤-trans L0 (m≤m+n l1 4)) (m≤m+n lr (lsize F))
                       (visit-ls F n1 (n1 + 4) (n1 + 5) (n1 + 7) lv)
    -- …and the REBUILD walk's is `[lr, lr + lsize F) = [lr, hi)`
    rebuild' : LabelsIn lo hi (rebuild-walk (n1 + 2) (n1 + 4) (n1 + 5) F (n1 + 7) lr)
    rebuild' = ls-weaken (≤-trans L0 (≤-trans (m≤m+n l1 4) lv≤lr)) ≤-refl
                         (rebuild-ls F (n1 + 2) (n1 + 4) (n1 + 5) (n1 + 7) lr)
    init : LabelsIn lo hi _
    init =
      ++⁺ (li-none refl ∷ li-none refl ∷ li-none refl ∷ li-none refl ∷ li-none refl ∷
           li-none refl ∷ li-none refl ∷ li-none refl ∷ li-none refl ∷ li-none refl ∷
           li-none refl ∷ li-none refl ∷ li-none refl ∷ li-none refl ∷ [])
          (push2-ls lo hi n1 (n1 + 4) (n1 + 5))
    flatten : LabelsIn lo hi _
    flatten =
      ++⁺ (li-lab refl L0 H0 ∷ li-none refl ∷ li-none refl ∷
           li-lab refl L1 H1 ∷ li-none refl ∷ li-none refl ∷
           li-none refl ∷ li-none refl ∷ li-none refl ∷ li-none refl ∷ [])
          (++⁺ (push2-ls lo hi (suc n1) (n1 + 4) (n1 + 5))
               (++⁺ (li-none refl ∷ li-none refl ∷ [])
                    (++⁺ visit'
                         (li-lab refl L0 H0 ∷ li-lab refl L1 H1 ∷ []))))
    fold : LabelsIn lo hi _
    fold =
      ++⁺ (li-lab refl L2 H2 ∷ li-none refl ∷ li-none refl ∷
           li-lab refl L3 H3 ∷ li-none refl ∷ li-none refl ∷
           li-none refl ∷ li-none refl ∷ [])
          (++⁺ rebuild'
               (++⁺ (li-none refl ∷ [])
                    (++⁺ at'
                         (++⁺ (push2-ls lo hi (n1 + 2) (n1 + 4) (n1 + 5))
                              (li-lab refl L2 H2 ∷ li-lab refl L3 H3 ∷ [])))))
    final : LabelsIn lo hi _
    final = li-none refl ∷ li-none refl ∷ li-none refl ∷ []

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
