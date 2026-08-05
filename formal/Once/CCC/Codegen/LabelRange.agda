-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.CCC.Codegen.LabelRange   (Plan 0.63, obligation (iii))
--
-- THE LABEL COUNTER NEVER RETREATS — the exact mirror of
-- `SlotBudget.frontier-mono` for the OTHER counter `ir-to-trace'` threads.
--
-- Why this exists: with closure bodies inlined (the flip), the slot budget is
-- SEGMENTED, and the runtime invariant `frame-slots ≡ cur (seg-at prog pc)`
-- has to survive a jump. That is LABEL SCOPING — a jump lands in the segment
-- it left — and the only machinery that can establish it is label RANGES: a
-- body's labels come from its own counter range, disjoint from the parent's,
-- so a jump emitted inside a body cannot name a label outside it.
--
-- Ranges need three things, of which this module is the first and cheapest:
--   1. MONOTONICITY (here) — the outgoing counter is at or above the incoming.
--   2. containment — every label a fragment MENTIONS (defines or jumps to) is
--      inside `[l, l')`. The `slots-below`-shaped induction.
--   3. the segment lemma — a jump and its target label agree, by (2) + the
--      disjointness (1) provides.
--
-- Kept in its own module rather than added to `SlotBudget` because it is about
-- the label counter, not the slot frontier, and because (2) will want to
-- import it without dragging the slot development along.
------------------------------------------------------------------------

-- Plan 0.63 (D089): parameterised by the DEFINITION'S identity, which keys
-- its labels. `o` is constant for a whole definition, so it belongs on the
-- module rather than on every lemma — which is exactly what keeps the
-- statements below UNCHANGED under D089: `IRToTrace` is imported APPLIED,
-- so each `ir-to-trace' n l ir` reads as it always did.
open import Once.CanonicalName using (CanonicalName)

module Once.CCC.Codegen.LabelRange (o : CanonicalName) where

open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; _<_; z≤n; s≤s; _*_)
open import Data.Nat.Properties using
  (≤-refl; ≤-trans; ≤-reflexive; n≤1+n; m≤m+n; m≤n+m; +-monoʳ-≤; +-comm; +-assoc)
open import Data.Product using (_×_; _,_)
open import Data.List using (List)

open import Once.IR using (IR; AllocMode; Stack; Heap;
  id; _∘_; ⟨_,_⟩; fst; snd; inl; inr; case; terminal; initial;
  curry; apply;
  In; out-μ; Cata; Para; Out; in-ν; Ana; Hylo; Fuse;
  free-heap; SigOp; const)
open import Once.IRTy using (fits-int; fits-float; ⌈_⌉F)
open import Once.Type using (Functor; K; Id; _⊕_; _⊗_)
open import Once.CCC.Machine.SMCore using (AbstractInstr; AbstractTrace)
open import Once.CCC.Codegen.IRToTrace o using
  (ir-to-trace'; CataStrategy; strat-const; strat-nat; strat-linear; strat-branching;
   cata-strategy; cata-dispatch; lsize)

------------------------------------------------------------------------
-- The label projections of the two result tuples (record patterns, so they
-- reduce under eta — mirrors `SlotBudget.budget-of`).
------------------------------------------------------------------------
label-of : ℕ × ℕ × AbstractTrace × List (ℕ × ℕ × AbstractTrace) → ℕ
label-of (_ , l , _ , _) = l

cata-label-of : ℕ × ℕ × AbstractTrace → ℕ
cata-label-of (_ , l , _) = l

------------------------------------------------------------------------
-- The cata strategies' own label appetite. `strat-const` emits none; the two
-- linear shapes take a fixed block; branching takes four plus a stride-`lsize`
-- window for each of the two compile-time walks (`lv` then `lr`, which is why
-- `lsize F` appears twice — sharing a base would duplicate labels).
------------------------------------------------------------------------
cata-label-mono : ∀ (st : CataStrategy) (n1 l1 : ℕ) (at : AbstractTrace)
                → l1 ≤ cata-label-of (cata-dispatch st n1 l1 at)
cata-label-mono strat-const         n1 l1 at = ≤-refl
cata-label-mono strat-nat           n1 l1 at =
  ≤-trans (n≤1+n l1)
    (≤-trans (n≤1+n (suc l1))
      (≤-trans (n≤1+n (suc (suc l1)))
        (≤-trans (n≤1+n (suc (suc (suc l1))))
          (≤-trans (n≤1+n (suc (suc (suc (suc l1)))))
                   (n≤1+n (suc (suc (suc (suc (suc l1))))))))))
-- linear takes FOUR (`ld-top`, `ld-end`, `la-top`, `la-end`)
cata-label-mono strat-linear        n1 l1 at =
  ≤-trans (n≤1+n l1)
    (≤-trans (n≤1+n (suc l1))
      (≤-trans (n≤1+n (suc (suc l1))) (n≤1+n (suc (suc (suc l1))))))
cata-label-mono (strat-branching F) n1 l1 at =
  ≤-trans (m≤m+n l1 4)
    (≤-trans (m≤m+n (l1 + 4) (lsize F)) (m≤m+n ((l1 + 4) + lsize F) (lsize F)))

------------------------------------------------------------------------
-- THE COUNTER NEVER RETREATS.
------------------------------------------------------------------------
label-mono : ∀ {A B} (ir : IR A B) (n l : ℕ) → l ≤ label-of (ir-to-trace' n l ir)
label-mono id       n l = ≤-refl
label-mono fst      n l = ≤-refl
label-mono snd      n l = ≤-refl
label-mono terminal n l = ≤-refl
label-mono initial  n l = ≤-refl
label-mono (g ∘ f)  n l = ≤-trans (label-mono f n l) (label-mono g _ _)
label-mono (⟨ f , g ⟩ Stack) n l = ≤-trans (label-mono f _ l) (label-mono g _ _)
label-mono (⟨ f , g ⟩ Heap)  n l = ≤-trans (label-mono f _ l) (label-mono g _ _)
-- The closure clauses take TWO labels of their own — the body marker `l` and
-- the end-of-body join `suc l` — and then hand the body its own range starting
-- at `suc (suc l)`. (Pre-flip this was one label; the proof shape is unchanged,
-- which is why this brick was worth landing ahead of the flip.)
label-mono (curry b Stack) n l =
  ≤-trans (n≤1+n l) (≤-trans (n≤1+n (suc l)) (label-mono b 0 (suc (suc l))))
label-mono (curry b Heap)  n l =
  ≤-trans (n≤1+n l) (≤-trans (n≤1+n (suc l)) (label-mono b 0 (suc (suc l))))
label-mono apply n l = ≤-refl
label-mono (inl Stack) n l = ≤-refl
label-mono (inr Stack) n l = ≤-refl
label-mono (inl Heap)  n l = ≤-refl
label-mono (inr Heap)  n l = ≤-refl
-- `case` takes two (the inl entry and the join) then both branches
label-mono (case f g)  n l =
  ≤-trans (n≤1+n l)
    (≤-trans (n≤1+n (suc l))
      (≤-trans (label-mono f n (suc (suc l))) (label-mono g _ _)))
label-mono (In _ _)    n l = ≤-refl
label-mono (out-μ _)   n l = ≤-refl
label-mono (Cata {F} _ alg) n l =
  ≤-trans (label-mono alg n l) (cata-label-mono (cata-strategy ⌈ F ⌉F) _ _ _)
label-mono (Para _ _)     n l = ≤-refl
label-mono (Out _)        n l = ≤-refl
label-mono (in-ν _ _)     n l = ≤-refl
label-mono (Ana _ _)      n l = ≤-refl
label-mono (Hylo _ _ _ _) n l = ≤-refl
label-mono (Fuse _ _ _ _) n l = ≤-refl
label-mono (free-heap _)  n l = ≤-refl
label-mono (SigOp _)      n l = ≤-refl
label-mono (const fits-int _)   n l = ≤-refl
label-mono (const fits-float _) n l = ≤-refl
