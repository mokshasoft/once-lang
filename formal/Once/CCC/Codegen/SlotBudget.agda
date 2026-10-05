-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson
{-# OPTIONS --inversion-max-depth=100 #-}
-- (Plan 0.109: the `seg-idle? … ≡ true` witnesses over long concrete traces need
-- Agda to invert past its default depth of 50; the constraints are satisfiable.)

------------------------------------------------------------------------
-- Once.CCC.Codegen.SlotBudget   (Plan 0.54 rung D, item 2)
--
-- THE EMITTER'S OWN FRONTIER DISCIPLINE: every slot an emitted instruction
-- addresses is below the frontier `ir-to-trace'` returns — and at the top
-- level that frontier IS `ir-stack-budget ir`, the number the per-arch backend
-- turns into `subq $budget*8, %rsp`.
--
-- THIS DISCHARGES `ConcFlatSim.emitted-slot-below-budget`, the emitter half of
-- `slot-read-in-frame`. Its machine half (`FlatStackSlot`: the live window
-- never moves) says the window is still the reserved one; this says the slot
-- fits inside it. Together they carry the whole slot cluster —
-- `load-from-slot`, `store-at-slot`, `restore-input`, `worklist-*`,
-- `lea-indexed`.
--
-- Two inductions, both over `ir-to-trace'`:
--   * `frontier-mono` — the frontier never retreats. Every splice needs it,
--     because a sub-IR's slots are bounded by ITS frontier, which the rest of
--     the emission then advances past.
--   * `slots-below` — every instruction of the returned MAIN trace is bounded
--     by the returned frontier. (Nested `instr-case-on-tag` branches need no
--     clause: `slot-of` is `nothing` on the instruction that carries them, and
--     the flat machine's `fpc` never indexes into them.)
------------------------------------------------------------------------

-- Plan 0.63 (D089): parameterised by the DEFINITION'S identity, which keys
-- its labels. `o` is constant for a whole definition, so it belongs on the
-- module rather than on every lemma — which is exactly what keeps the
-- statements below UNCHANGED under D089: `IRToTrace` is imported APPLIED,
-- so each `ir-to-trace' n l ir` reads as it always did.
open import Once.CanonicalName using (CanonicalName)
open import Once.CCC.Label using (LabelId; ℓ)

module Once.CCC.Codegen.SlotBudget (o : CanonicalName) where

open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; _<_; z≤n; s≤s; _*_)
open import Data.Nat.Properties using
  (≤-refl; ≤-trans; ≤-reflexive; n≤1+n; m≤m+n; m≤n+m; +-monoʳ-≤; +-comm; +-assoc; +-suc;
   *-suc; *-monoʳ-≤; m≤n⇒m≤1+n)
open import Data.Bool using (Bool; true; false; _∧_)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (_×_; _,_; Σ; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.All.Properties using (++⁺)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)

open import Once.IR using (IR; AllocMode; Stack; Heap;
  id; _∘_; ⟨_,_⟩; fst; snd; inl; inr; case; terminal; initial;
  curry; apply;
  In; out-μ; Cata; Out; in-ν; Ana;
  SigOp; Call; const)
open import Once.IRTy using (fits-int; fits-float; ⌈_⌉F; ⟦_⟧TI; ν-type;
  WellFormedFI; wf-K; wf-Id; wf-Sum; wf-Prod)
open import Once.Type using (Functor; K; Id; _⊕_; _⊗_)
open import Once.CCC.Machine.SMCore using (blocks-layout; link-top)
open import Once.CCC.Machine.SMCore using
  (AbstractInstr; AbstractTrace; Slot; lea-slot;
   mov-to-output; mov-to-input; store-at-slot; load-from-slot;
   store-indirect; store-indirect-suc; instr-alloc-heap; instr-load-tag-lit;
   instr-ctrl; c-thunk; c-entry; c-call-fn; c-ret; c-label; c-jmp;
   restore-input; load-indirect; load-indirect-suc; instr-load-code-addr;
   c-branch-tag-zero)
open import Once.CCC.Machine.InstrSlot using (slot-of)
open import Once.SigOp.Info using (SigOpInfo; sem)
open import Once.Arith.CmpOp using (CmpOp)
open import Once.Arith.SigOp.Compare using (cmp-of)
open import Once.CCC.Codegen.IRToTrace o using
  (ir-to-trace'; ir-to-trace; ir-stack-budget; resuspend-layer; ir-to-trace-lab; ir-stack-budget-from;
   ir-to-unit; sigop-budget; sigop-code;
   CataStrategy; strat-const; strat-nat; strat-linear; strat-branching;
   cata-strategy; cata-dispatch; fsize; lsize;
   push2; pop2; wrap-sum; visit-walk; rebuild-walk; cata-nat-layer
   ; cata-br-I₁; cata-br-I₂
   -- D099 / C1: the called-algebra blocks.
   ; cata-body; cata-call-setup; cata-call; cata-trace-const)

-- the o-independent segment machinery (`SlotBelow`, `SegState`, `AllSeg`,
-- `SegOK`, …), split out so a program image shares one `AllSeg`
open import Once.CCC.Codegen.SlotSeg

-- the two projections of `ir-to-trace'`'s 4-tuple this module reads (record
-- patterns, so they reduce under eta — IRToTrace's own are private)

budget-of : ℕ × ℕ × AbstractTrace × List (LabelId × ℕ × AbstractTrace) → ℕ
budget-of (n , _ , _ , _) = n

trace-of : ℕ × ℕ × AbstractTrace × List (LabelId × ℕ × AbstractTrace) → AbstractTrace
trace-of (_ , _ , t , _) = t

cata-budget-of : ℕ × ℕ × AbstractTrace → ℕ
cata-budget-of (n , _ , _) = n

cata-trace-of : ℕ × ℕ × AbstractTrace → AbstractTrace
cata-trace-of (_ , _ , t) = t

------------------------------------------------------------------------
-- THE FRONTIER NEVER RETREATS.
------------------------------------------------------------------------
-- D099 / C1: every strategy now also reserves the call's two slots (`cl`, `k`),
-- and `strat-const` — which used to splice the algebra inline and reserve
-- nothing — goes through the same call, so it reserves two as well.
cata-mono : ∀ (st : CataStrategy) (bb n1 l1 : ℕ) (at : AbstractTrace)
          → n1 ≤ cata-budget-of (cata-dispatch st bb n1 l1 at)
cata-mono strat-const         bb n1 l1 at = m≤m+n n1 4
cata-mono strat-nat           bb n1 l1 at =
  ≤-trans (n≤1+n n1)
    (≤-trans (n≤1+n (suc n1))
      (≤-trans (n≤1+n (suc (suc n1)))
        (≤-trans (n≤1+n (suc (suc (suc n1))))
          (≤-trans (n≤1+n (suc (suc (suc (suc n1)))))
                   (n≤1+n (suc (suc (suc (suc (suc n1))))))))))
cata-mono strat-linear        bb n1 l1 at =
  m≤n⇒m≤1+n (m≤n⇒m≤1+n (m≤n⇒m≤1+n (m≤n⇒m≤1+n (m≤n⇒m≤1+n (m≤n⇒m≤1+n (m≤n⇒m≤1+n (m≤n⇒m≤1+n (m≤n⇒m≤1+n (m≤n⇒m≤1+n ≤-refl)))))))))
cata-mono (strat-branching F) bb n1 l1 at =
  ≤-trans (m≤m+n n1 7)
    (≤-trans (m≤m+n (n1 + 7) (4 * fsize F))
      (≤-trans (m≤m+n ((n1 + 7) + 4 * fsize F) 4)
               (m≤m+n (((n1 + 7) + 4 * fsize F) + 4) 4)))

-- Plan 0.108: a comparison stashes its tag and its sum, two slots.
sigop-mono : ∀ (n : ℕ) (m : Maybe CmpOp) → n ≤ sigop-budget n m
sigop-mono n nothing  = ≤-refl
sigop-mono n (just _) = ≤-trans (n≤1+n n) (n≤1+n (suc n))

frontier-mono : ∀ {A B} (ir : IR A B) (n l : ℕ) → n ≤ budget-of (ir-to-trace' n l ir)
frontier-mono id       n l = ≤-refl
frontier-mono fst      n l = ≤-refl
frontier-mono snd      n l = ≤-refl
frontier-mono terminal n l = ≤-refl
frontier-mono initial  n l = ≤-refl
frontier-mono (g ∘ f)  n l = ≤-trans (frontier-mono f n l) (frontier-mono g _ _)
-- Stage G: the stack-shape clause that stood here collapsed onto this
-- same LHS when the pair's mode was dropped, and shadowed the heap one.
frontier-mono (⟨ f , g ⟩) n l =
  ≤-trans (≤-trans (n≤1+n n)
            (≤-trans (n≤1+n (suc n))
              (≤-trans (n≤1+n (suc (suc n))) (n≤1+n (suc (suc (suc n)))))))
          (≤-trans (frontier-mono f _ l) (frontier-mono g _ _))
frontier-mono (curry b)  n l = ≤-trans (n≤1+n n) (n≤1+n (suc n))
frontier-mono apply n l = ≤-trans (n≤1+n n) (≤-trans (n≤1+n (suc n)) (n≤1+n (suc (suc n))))
frontier-mono inl n l = ≤-trans (n≤1+n n) (n≤1+n (suc n))
frontier-mono inr n l = ≤-trans (n≤1+n n) (n≤1+n (suc n))
frontier-mono (case f g)  n l =
  ≤-trans (frontier-mono f n (suc (suc l))) (frontier-mono g _ _)
frontier-mono (In _)    n l = ≤-refl
frontier-mono (out-μ _)   n l = ≤-refl
-- C1: the algebra runs in its OWN frame (generated at frontier 0), so the
-- caller's frontier is not advanced by it at all — the dispatch takes `n`
-- directly and only the cata's own scratch is added.
frontier-mono (Cata {F} _ alg) n l = cata-mono (cata-strategy ⌈ F ⌉F) _ _ _ _
frontier-mono (Out _)        n l = ≤-refl
-- D189: the same two-cell build as `Ana`, with `id` as the block.
frontier-mono (in-ν _)     n l = ≤-trans (n≤1+n n) (n≤1+n (suc n))
-- D189: the ν suspension is `curry`'s closure record cell for cell, so
-- its walk clause is `curry`'s. The coalgebra is a named block, like the
-- closure body, emitted at frontier 0 under the ν's own label.
frontier-mono (Ana _ c)      n l = ≤-trans (n≤1+n n) (n≤1+n (suc n))
frontier-mono (SigOp si)     n l = sigop-mono n (cmp-of (sem si))
frontier-mono (Call _)      n l = ≤-refl
frontier-mono (const fits-int _)   n l = ≤-refl
frontier-mono (const fits-float _) n l = ≤-refl

------------------------------------------------------------------------
-- EVERY EMITTED SLOT IS BELOW THE RETURNED FRONTIER.
--
-- The cata skeletons reserve their own slots ABOVE the algebra's frontier
-- `n1`, so each strategy is a fixed arithmetic fact about `[n1, next)`.
------------------------------------------------------------------------

-- `k < suc … (suc k)`, the only shape the fixed-layout clauses need
lt-refl : ∀ {k} → k < suc k
lt-refl = ≤-refl

-- `build-layer tag` (inside `cata-trace-nat`): the two stash slots are `n1` and
-- `suc n1`, both below that strategy's frontier `suc (suc n1)`.
cata-nat-layer-below : ∀ (n1 tag b : ℕ) → n1 < b → suc n1 < b
               → All (SlotBelow b)
                   (mov-to-output ∷ store-at-slot n1 ∷ instr-alloc-heap 2 ∷
                    store-at-slot (suc n1) ∷ mov-to-input ∷ instr-load-tag-lit tag ∷
                    store-indirect ∷ load-from-slot n1 ∷ store-indirect-suc ∷
                    load-from-slot (suc n1) ∷ [])
cata-nat-layer-below n1 tag b p<b s<b =
  sb-none refl ∷ sb-slot refl p<b (λ _ ()) ∷ sb-none refl ∷
  sb-slot refl s<b (λ _ ()) ∷ sb-none refl ∷ sb-none refl ∷ sb-none refl ∷
  sb-slot refl p<b (λ _ ()) ∷ sb-none refl ∷ sb-slot refl s<b (λ _ ()) ∷ []

-- STRATEGY `strat-nat` DISCHARGED: the Nat-shaped cata reserves exactly two
-- slots above the algebra's frontier, and every other instruction of the
-- skeleton is slot-free (loop labels, jumps, reg-ops, the two `at` splices).
-- D099 / C1: the algebra is a CALLED BODY, so its slots live in ITS OWN frame
-- and its `SegOK` is taken at its own budget `bb`, not the cata's.
-- `segok-thunk` is exactly the combinator for that — it was built for `curry`'s
-- inline body (`slots-below (curry b) n l` feeds it `slots-below b 0 …`), and
-- the cata's body bracket is the same `c-thunk … / c-ret … / c-label` shape.
--
-- Second place C1 SIMPLIFIES: the old witnesses had to `segok-weaken` the
-- algebra into the CATA's budget at both splice sites, which was only sound
-- because the algebra was generated at the cata's own frontier. It is not any
-- more, and the frame change is what removes the weakening.
cata-body-below : ∀ {B : ℕ} (bl el bb : ℕ) (at : AbstractTrace) → SegOK bb at
                → SegOK B (cata-body bl el bb at)
cata-body-below bl el bb at bok =
  segok-pre (instr-ctrl (c-jmp (ℓ o el)) ∷ []) refl (sb-none refl ∷ [])
    (segok-thunk (ℓ o bl) bb (ℓ o el) at bok)

-- The call path's own slot references: the record pointer `cl` and the layer
-- stash `k`. Everything else in setup/call is slot-free, and
-- `instr-call-closure` is segment-idle (the same reason `slots-below apply`
-- is one `segok-idle`).
cata-const-below : ∀ (bb n1 l1 : ℕ) (at : AbstractTrace) → SegOK bb at
                 → SegOK (cata-budget-of (cata-dispatch strat-const bb n1 l1 at))
                         (cata-trace-of (cata-dispatch strat-const bb n1 l1 at))
cata-const-below bb n1 l1 at bok =
  segok-++ (segok-idle _ refl
      (-- setup (18) then call (12), one flat list as before
       sb-none refl ∷ sb-slot refl ev<b (λ _ ()) ∷ sb-none refl ∷
       sb-slot refl k<b (λ _ ()) ∷ sb-none refl ∷ sb-slot refl pr<b (λ _ ()) ∷
       sb-none refl ∷ sb-slot refl ev<b (λ _ ()) ∷ sb-none refl ∷
       sb-none refl ∷ sb-slot refl cl<b (λ _ ()) ∷ sb-none refl ∷
       sb-none refl ∷ sb-none refl ∷ sb-none refl ∷
       sb-none refl ∷ sb-slot refl k<b (λ _ ()) ∷ sb-none refl ∷
       sb-none refl ∷ sb-slot refl k<b (λ _ ()) ∷ sb-slot refl pr<b (λ _ ()) ∷
       sb-none refl ∷ sb-slot refl k<b (λ _ ()) ∷ sb-none refl ∷
       sb-slot refl cl<b (λ _ ()) ∷ sb-none refl ∷ sb-none refl ∷
       sb-slot refl pr<b (λ _ ()) ∷ sb-none refl ∷ sb-none refl ∷ []))
    (cata-body-below _ _ bb at bok)
  where
    -- D131: four slots now — `cl`/`k` as before, plus `ev` (the fold's
    -- environment) and `pr` (the reused argument pair). `suc (n1 + j) ≡
    -- n1 + suc j` is `+-suc`, and the rest is monotonicity.
    bnd : ∀ (j : ℕ) → suc j ≤ 4 → n1 + j < n1 + 4
    bnd j p = ≤-trans (≤-reflexive (sym (+-suc n1 j))) (+-monoʳ-≤ n1 p)
    cl<b : n1 < n1 + 4
    cl<b = ≤-trans (s≤s (m≤m+n n1 0)) (bnd 0 (s≤s z≤n))
    k<b : n1 + 1 < n1 + 4
    k<b = bnd 1 (s≤s (s≤s z≤n))
    ev<b : n1 + 2 < n1 + 4
    ev<b = bnd 2 (s≤s (s≤s (s≤s z≤n)))
    pr<b : n1 + 3 < n1 + 4
    pr<b = bnd 3 (s≤s (s≤s (s≤s (s≤s z≤n))))

cata-nat-below : ∀ (bb n1 l1 : ℕ) (at : AbstractTrace) → SegOK bb at
               → SegOK (cata-budget-of (cata-dispatch strat-nat bb n1 l1 at))
                       (cata-trace-of (cata-dispatch strat-nat bb n1 l1 at))
-- One `segok-idle` per BLOCK, mirroring the emitter's own `++` structure —
-- rather than one flat 68-entry list, which is what the pre-C1 witness had to
-- be because the algebra was spliced into the middle of it.
cata-nat-below bb n1 l1 at bok =
  segok-++ (segok-idle _ refl setup)
   (segok-++ (segok-idle _ refl I₁)
    (segok-++ (segok-idle _ refl call)
     (segok-++ (segok-idle _ refl I₂)
      (segok-++ (segok-idle _ refl call)
       (segok-++ (segok-idle _ refl I₃) (cata-body-below _ _ bb at bok))))))
  where
    b = suc (suc (suc (suc (suc (suc n1)))))
    p<b : n1 < b
    p<b = m≤n⇒m≤1+n (m≤n⇒m≤1+n (m≤n⇒m≤1+n (m≤n⇒m≤1+n (m≤n⇒m≤1+n (≤-refl)))))
    s<b : suc n1 < b
    s<b = m≤n⇒m≤1+n (m≤n⇒m≤1+n (m≤n⇒m≤1+n (m≤n⇒m≤1+n (≤-refl))))
    cl<b : suc (suc n1) < b
    cl<b = m≤n⇒m≤1+n (m≤n⇒m≤1+n (m≤n⇒m≤1+n (≤-refl)))
    k<b : suc (suc (suc n1)) < b
    k<b = m≤n⇒m≤1+n (m≤n⇒m≤1+n (≤-refl))
    ev<b : suc (suc (suc (suc n1))) < b
    ev<b = m≤n⇒m≤1+n (≤-refl)
    pr<b : suc (suc (suc (suc (suc n1)))) < b
    pr<b = ≤-refl
    setup : All (SlotBelow b) _
    setup = sb-none refl ∷ sb-slot refl ev<b (λ _ ()) ∷ sb-none refl ∷
            sb-slot refl k<b (λ _ ()) ∷ sb-none refl ∷ sb-slot refl pr<b (λ _ ()) ∷
            sb-none refl ∷ sb-slot refl ev<b (λ _ ()) ∷ sb-none refl ∷
            sb-none refl ∷ sb-slot refl cl<b (λ _ ()) ∷ sb-none refl ∷
            sb-none refl ∷ sb-none refl ∷ sb-none refl ∷
            sb-none refl ∷ sb-slot refl k<b (λ _ ()) ∷ sb-none refl ∷ []
    call : All (SlotBelow b) _
    call = sb-none refl ∷ sb-slot refl k<b (λ _ ()) ∷ sb-slot refl pr<b (λ _ ()) ∷
           sb-none refl ∷ sb-slot refl k<b (λ _ ()) ∷ sb-none refl ∷
           sb-slot refl cl<b (λ _ ()) ∷ sb-none refl ∷ sb-none refl ∷
           sb-slot refl pr<b (λ _ ()) ∷ sb-none refl ∷ sb-none refl ∷ []
    I₁ : All (SlotBelow b) _
    I₁ = sb-none refl ∷ sb-none refl ∷
         sb-none refl ∷ sb-none refl ∷ sb-none refl ∷ sb-none refl ∷ sb-none refl ∷
         sb-none refl ∷ sb-none refl ∷ sb-none refl ∷ sb-none refl ∷ sb-none refl ∷
         sb-none refl ∷ sb-none refl ∷
         sb-none refl ∷ sb-none refl ∷ sb-none refl ∷
         sb-none refl ∷ sb-slot refl p<b (λ _ ()) ∷ sb-none refl ∷
         sb-slot refl s<b (λ _ ()) ∷ sb-none refl ∷ sb-none refl ∷ sb-none refl ∷
         sb-slot refl p<b (λ _ ()) ∷ sb-none refl ∷ sb-slot refl s<b (λ _ ()) ∷
         sb-none refl ∷ []
    I₂ : All (SlotBelow b) _
    I₂ = sb-none refl ∷ sb-none refl ∷ sb-none refl ∷
         sb-none refl ∷ sb-slot refl p<b (λ _ ()) ∷ sb-none refl ∷
         sb-slot refl s<b (λ _ ()) ∷ sb-none refl ∷ sb-none refl ∷ sb-none refl ∷
         sb-slot refl p<b (λ _ ()) ∷ sb-none refl ∷ sb-slot refl s<b (λ _ ()) ∷
         sb-none refl ∷ []
    I₃ : All (SlotBelow b) _
    I₃ = sb-none refl ∷ sb-none refl ∷ sb-none refl ∷ []

cata-linear-below : ∀ (bb n1 l1 : ℕ) (at : AbstractTrace) → SegOK bb at
                  → SegOK (cata-budget-of (cata-dispatch strat-linear bb n1 l1 at))
                          (cata-trace-of (cata-dispatch strat-linear bb n1 l1 at))
cata-linear-below bb n1 l1 at bok =
  segok-++ (segok-idle _ refl setup)
   (segok-++ (segok-idle _ refl I₁)
    (segok-++ (segok-idle _ refl call)
     (segok-++ (segok-idle _ refl I₂)
      (segok-++ (segok-idle _ refl call)
       (segok-++ (segok-idle _ refl I₃) (cata-body-below _ _ bb at bok))))))
  where
    b = (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc n1))))))))))
    p0 : n1 < b
    p0 = m≤n⇒m≤1+n (m≤n⇒m≤1+n (m≤n⇒m≤1+n (m≤n⇒m≤1+n (m≤n⇒m≤1+n (m≤n⇒m≤1+n (m≤n⇒m≤1+n (m≤n⇒m≤1+n (m≤n⇒m≤1+n (≤-refl)))))))))
    p1 : suc n1 < b
    p1 = m≤n⇒m≤1+n (m≤n⇒m≤1+n (m≤n⇒m≤1+n (m≤n⇒m≤1+n (m≤n⇒m≤1+n (m≤n⇒m≤1+n (m≤n⇒m≤1+n (m≤n⇒m≤1+n (≤-refl))))))))
    p2 : suc (suc n1) < b
    p2 = m≤n⇒m≤1+n (m≤n⇒m≤1+n (m≤n⇒m≤1+n (m≤n⇒m≤1+n (m≤n⇒m≤1+n (m≤n⇒m≤1+n (m≤n⇒m≤1+n (≤-refl)))))))
    p3 : suc (suc (suc n1)) < b
    p3 = m≤n⇒m≤1+n (m≤n⇒m≤1+n (m≤n⇒m≤1+n (m≤n⇒m≤1+n (m≤n⇒m≤1+n (m≤n⇒m≤1+n (≤-refl))))))
    p4 : suc (suc (suc (suc n1))) < b
    p4 = m≤n⇒m≤1+n (m≤n⇒m≤1+n (m≤n⇒m≤1+n (m≤n⇒m≤1+n (m≤n⇒m≤1+n (≤-refl)))))
    p5 : suc (suc (suc (suc (suc n1)))) < b
    p5 = m≤n⇒m≤1+n (m≤n⇒m≤1+n (m≤n⇒m≤1+n (m≤n⇒m≤1+n (≤-refl))))
    cl<b : (suc (suc (suc (suc (suc (suc n1)))))) < b
    cl<b = m≤n⇒m≤1+n (m≤n⇒m≤1+n (m≤n⇒m≤1+n (≤-refl)))
    k<b : (suc (suc (suc (suc (suc (suc (suc n1))))))) < b
    k<b = m≤n⇒m≤1+n (m≤n⇒m≤1+n (≤-refl))
    ev<b : (suc (suc (suc (suc (suc (suc (suc (suc n1)))))))) < b
    ev<b = m≤n⇒m≤1+n (≤-refl)
    pr<b : (suc (suc (suc (suc (suc (suc (suc (suc (suc n1))))))))) < b
    pr<b = ≤-refl
    setup : All (SlotBelow b) _
    setup = sb-none refl ∷ sb-slot refl ev<b (λ _ ()) ∷ sb-none refl ∷
            sb-slot refl k<b (λ _ ()) ∷ sb-none refl ∷ sb-slot refl pr<b (λ _ ()) ∷
            sb-none refl ∷ sb-slot refl ev<b (λ _ ()) ∷ sb-none refl ∷
            sb-none refl ∷ sb-slot refl cl<b (λ _ ()) ∷ sb-none refl ∷
            sb-none refl ∷ sb-none refl ∷ sb-none refl ∷
            sb-none refl ∷ sb-slot refl k<b (λ _ ()) ∷ sb-none refl ∷ []
    call : All (SlotBelow b) _
    call = sb-none refl ∷ sb-slot refl k<b (λ _ ()) ∷ sb-slot refl pr<b (λ _ ()) ∷
           sb-none refl ∷ sb-slot refl k<b (λ _ ()) ∷ sb-none refl ∷
           sb-slot refl cl<b (λ _ ()) ∷ sb-none refl ∷ sb-none refl ∷
           sb-slot refl pr<b (λ _ ()) ∷ sb-none refl ∷ sb-none refl ∷ []
    I₁ : All (SlotBelow b) _
    I₁ = sb-none refl ∷ sb-none refl ∷ sb-slot refl p3 (λ _ ()) ∷
         sb-none refl ∷ sb-none refl ∷ sb-none refl ∷
         sb-none refl ∷ sb-none refl ∷
         sb-none refl ∷ sb-slot refl p5 (λ _ ()) ∷
         sb-none refl ∷ sb-slot refl p2 (λ _ ()) ∷
         sb-none refl ∷ sb-slot refl p1 (λ _ ()) ∷ sb-none refl ∷
         sb-slot refl p5 (λ _ ()) ∷ sb-none refl ∷
         sb-slot refl p3 (λ _ ()) ∷ sb-none refl ∷
         sb-slot refl p1 (λ _ ()) ∷ sb-slot refl p3 (λ _ ()) ∷
         sb-slot refl p2 (λ _ ()) ∷ sb-none refl ∷
         sb-none refl ∷ sb-none refl ∷ sb-none refl ∷ []
    I₂ : All (SlotBelow b) _
    I₂ = sb-none refl ∷ sb-none refl ∷
         sb-slot refl p4 (λ _ ()) ∷
         sb-slot refl p3 (λ _ ()) ∷ sb-none refl ∷
         sb-none refl ∷ sb-slot refl p5 (λ _ ()) ∷
         sb-none refl ∷ sb-slot refl p3 (λ _ ()) ∷
         sb-none refl ∷ sb-slot refl p1 (λ _ ()) ∷ sb-none refl ∷
         sb-slot refl p5 (λ _ ()) ∷ sb-none refl ∷
         sb-slot refl p4 (λ _ ()) ∷ sb-none refl ∷
         sb-none refl ∷ sb-slot refl p0 (λ _ ()) ∷ sb-none refl ∷
         sb-none refl ∷ sb-none refl ∷
         sb-slot refl p1 (λ _ ()) ∷ sb-none refl ∷
         sb-slot refl p0 (λ _ ()) ∷ sb-none refl ∷ []
    I₃ : All (SlotBelow b) _
    I₃ = sb-none refl ∷ sb-none refl ∷ sb-none refl ∷ []

push2-below : ∀ (topSlot tv tb b : ℕ) → topSlot < b → tv < b → tb < b
            → All (SlotBelow b) (push2 topSlot tv tb)
push2-below topSlot tv tb b pt pv pb =
  sb-slot refl pv (λ _ ()) ∷ sb-none refl ∷ sb-slot refl pb (λ _ ()) ∷
  sb-none refl ∷ sb-slot refl pv (λ _ ()) ∷ sb-none refl ∷
  sb-slot refl pt (λ _ ()) ∷ sb-none refl ∷
  sb-slot refl pb (λ _ ()) ∷ sb-slot refl pt (λ _ ()) ∷ []

-- pop it: one addressed slot
pop2-below : ∀ (topSlot b : ℕ) → topSlot < b → All (SlotBelow b) (pop2 topSlot)
pop2-below topSlot b pt =
  sb-slot refl pt (λ _ ()) ∷ sb-none refl ∷ sb-none refl ∷
  sb-slot refl pt (λ _ ()) ∷ sb-none refl ∷ []

-- wrap the payload into a sum node: two addressed slots (item 6 made this a
-- MAIN-trace segment — it used to hide inside a nested `⊕` branch)
wrap-sum-below : ∀ (tag s b : ℕ) → s < b → suc s < b
               → All (SlotBelow b) (wrap-sum tag s)
wrap-sum-below tag s b ps pss =
  sb-slot refl ps (λ _ ()) ∷ sb-none refl ∷ sb-slot refl pss (λ _ ()) ∷
  sb-none refl ∷ sb-none refl ∷ sb-none refl ∷
  sb-slot refl ps (λ _ ()) ∷ sb-none refl ∷ sb-slot refl pss (λ _ ()) ∷ []

-- the VISIT walk: `Id` is a push (fixed slots), `⊕` one case instruction,
-- `⊗` owns `s` and recurses at `s+4`
visit-below : ∀ (F : Functor) (todo tv tb s lb b : ℕ)
            → todo < b → tv < b → tb < b → s + 4 * fsize F ≤ b
            → All (SlotBelow b) (visit-walk todo tv tb F s lb)
visit-below (K _) todo tv tb s lb b pt pv pb h = []
visit-below Id    todo tv tb s lb b pt pv pb h =
  sb-none refl ∷ push2-below todo tv tb b pt pv pb
-- item 6: the ⊕ dispatch is FLAT — branch prologues/joins are label/ctrl
-- instructions (slot-free), the branch walks are inline splices.
visit-below (F ⊕ G) todo tv tb s lb b pt pv pb h =
  ++⁺ (sb-none refl ∷ sb-none refl ∷ sb-none refl ∷ [])
      (++⁺ (visit-below G todo tv tb (s + 4) _ b pt pv pb recG)
           (++⁺ (sb-none refl ∷ sb-none refl ∷ sb-none refl ∷ sb-none refl ∷ [])
                (++⁺ (visit-below F todo tv tb (s + 4) _ b pt pv pb recF)
                     (sb-none refl ∷ []))))
  where
    recF : s + 4 + 4 * fsize F ≤ b
    recF = ≤-trans (≤-reflexive (+-assoc s 4 (4 * fsize F)))
           (≤-trans (+-monoʳ-≤ s (+-monoʳ-≤ 4 (*-monoʳ-≤ 4 (m≤m+n (fsize F) (fsize G)))))
           (≤-trans (≤-reflexive (cong (s +_) (sym (*-suc 4 (fsize F + fsize G))))) h))
    recG : s + 4 + 4 * fsize G ≤ b
    recG = ≤-trans (≤-reflexive (+-assoc s 4 (4 * fsize G)))
           (≤-trans (+-monoʳ-≤ s (+-monoʳ-≤ 4 (*-monoʳ-≤ 4 (m≤n+m (fsize G) (fsize F)))))
           (≤-trans (≤-reflexive (cong (s +_) (sym (*-suc 4 (fsize F + fsize G))))) h))
visit-below (F ⊗ G) todo tv tb s lb b pt pv pb h =
  ++⁺ (sb-none refl ∷ sb-slot refl s<b (λ _ ()) ∷ sb-none refl ∷ sb-none refl ∷ [])
      (++⁺ (visit-below F todo tv tb (s + 4) _ b pt pv pb recF)
           (++⁺ (sb-slot refl s<b (λ _ ()) ∷ sb-none refl ∷ sb-none refl ∷ [])
                (visit-below G todo tv tb (s + 4) _ b pt pv pb recG)))
  where
    room4 : s + 4 ≤ b
    room4 = ≤-trans (+-monoʳ-≤ s (subst (4 ≤_) (sym (*-suc 4 (fsize F + fsize G)))
                                        (m≤m+n 4 (4 * (fsize F + fsize G))))) h
    s<b : s < b
    s<b = ≤-trans (subst (suc s ≤_) (+-comm 4 s) (m≤n+m (suc s) 3)) room4
    recF : s + 4 + 4 * fsize F ≤ b
    recF = ≤-trans (≤-reflexive (+-assoc s 4 (4 * fsize F)))
           (≤-trans (+-monoʳ-≤ s (+-monoʳ-≤ 4 (*-monoʳ-≤ 4 (m≤m+n (fsize F) (fsize G)))))
           (≤-trans (≤-reflexive (cong (s +_) (sym (*-suc 4 (fsize F + fsize G))))) h))
    recG : s + 4 + 4 * fsize G ≤ b
    recG = ≤-trans (≤-reflexive (+-assoc s 4 (4 * fsize G)))
           (≤-trans (+-monoʳ-≤ s (+-monoʳ-≤ 4 (*-monoʳ-≤ 4 (m≤n+m (fsize G) (fsize F)))))
           (≤-trans (≤-reflexive (cong (s +_) (sym (*-suc 4 (fsize F + fsize G))))) h))

-- the REBUILD walk: `Id` is a pop (the value slot), `⊕` one case instruction
-- (`wrap-sum` lives inside its branches), `⊗` owns `[s, s+3]`
rebuild-below : ∀ (F : Functor) (val tv tb s lb b : ℕ)
              → val < b → s + 4 * fsize F ≤ b
              → All (SlotBelow b) (rebuild-walk val tv tb F s lb)
rebuild-below (K _) val tv tb s lb b pt h = sb-none refl ∷ []
rebuild-below Id    val tv tb s lb b pt h = pop2-below val b pt
-- item 6: flat ⊕ — the `wrap-sum`s are main-trace segments now.
rebuild-below (F ⊕ G) val tv tb s lb b pt h =
  ++⁺ (sb-none refl ∷ sb-none refl ∷ sb-none refl ∷ [])
      (++⁺ (rebuild-below G val tv tb (s + 4) _ b pt recG)
           (++⁺ (wrap-sum-below 1 s b s<b b-ss)
                (++⁺ (sb-none refl ∷ sb-none refl ∷ sb-none refl ∷ sb-none refl ∷ [])
                     (++⁺ (rebuild-below F val tv tb (s + 4) _ b pt recF)
                          (++⁺ (wrap-sum-below 0 s b s<b b-ss)
                               (sb-none refl ∷ []))))))
  where
    room4 : s + 4 ≤ b
    room4 = ≤-trans (+-monoʳ-≤ s (subst (4 ≤_) (sym (*-suc 4 (fsize F + fsize G)))
                                        (m≤m+n 4 (4 * (fsize F + fsize G))))) h
    s<b : s < b
    s<b = ≤-trans (subst (suc s ≤_) (+-comm 4 s) (m≤n+m (suc s) 3)) room4
    b-ss : suc s < b
    b-ss = ≤-trans (subst (suc (suc s) ≤_) (+-comm 4 s) (m≤n+m (suc (suc s)) 2)) room4
    recF : s + 4 + 4 * fsize F ≤ b
    recF = ≤-trans (≤-reflexive (+-assoc s 4 (4 * fsize F)))
           (≤-trans (+-monoʳ-≤ s (+-monoʳ-≤ 4 (*-monoʳ-≤ 4 (m≤m+n (fsize F) (fsize G)))))
           (≤-trans (≤-reflexive (cong (s +_) (sym (*-suc 4 (fsize F + fsize G))))) h))
    recG : s + 4 + 4 * fsize G ≤ b
    recG = ≤-trans (≤-reflexive (+-assoc s 4 (4 * fsize G)))
           (≤-trans (+-monoʳ-≤ s (+-monoʳ-≤ 4 (*-monoʳ-≤ 4 (m≤n+m (fsize G) (fsize F)))))
           (≤-trans (≤-reflexive (cong (s +_) (sym (*-suc 4 (fsize F + fsize G))))) h))
rebuild-below (F ⊗ G) val tv tb s lb b pt h =
  ++⁺ (sb-none refl ∷ sb-slot refl s<b (λ _ ()) ∷ sb-none refl ∷ sb-none refl ∷ [])
      (++⁺ (rebuild-below G val tv tb (s + 4) _ b pt recG)
           (++⁺ (sb-slot refl b-s2 (λ _ ()) ∷ sb-slot refl s<b (λ _ ()) ∷
                 sb-none refl ∷ sb-none refl ∷ [])
                (++⁺ (rebuild-below F val tv tb (s + 4) _ b pt recF)
                     (sb-slot refl b-ss (λ _ ()) ∷ sb-none refl ∷
                      sb-slot refl b-s3 (λ _ ()) ∷ sb-none refl ∷
                      sb-slot refl b-ss (λ _ ()) ∷ sb-none refl ∷
                      sb-slot refl b-s2 (λ _ ()) ∷ sb-none refl ∷
                      sb-slot refl b-s3 (λ _ ()) ∷ []))))
  where
    room4 : s + 4 ≤ b
    room4 = ≤-trans (+-monoʳ-≤ s (subst (4 ≤_) (sym (*-suc 4 (fsize F + fsize G)))
                                        (m≤m+n 4 (4 * (fsize F + fsize G))))) h
    s<b : s < b
    s<b = ≤-trans (subst (suc s ≤_) (+-comm 4 s) (m≤n+m (suc s) 3)) room4
    b-ss : suc s < b
    b-ss = ≤-trans (subst (suc (suc s) ≤_) (+-comm 4 s) (m≤n+m (suc (suc s)) 2)) room4
    b-s2 : s + 2 < b
    b-s2 = ≤-trans (subst (λ z → suc z ≤ s + 4) (+-comm 2 s)
                          (subst (λ w → suc (2 + s) ≤ w) (+-comm 4 s) (n≤1+n (3 + s))))
                   room4
    b-s3 : s + 3 < b
    b-s3 = ≤-trans (subst (λ z → suc z ≤ s + 4) (+-comm 3 s)
                          (subst (λ w → suc (3 + s) ≤ w) (+-comm 4 s) ≤-refl))
                   room4
    recF : s + 4 + 4 * fsize F ≤ b
    recF = ≤-trans (≤-reflexive (+-assoc s 4 (4 * fsize F)))
           (≤-trans (+-monoʳ-≤ s (+-monoʳ-≤ 4 (*-monoʳ-≤ 4 (m≤m+n (fsize F) (fsize G)))))
           (≤-trans (≤-reflexive (cong (s +_) (sym (*-suc 4 (fsize F + fsize G))))) h))
    recG : s + 4 + 4 * fsize G ≤ b
    recG = ≤-trans (≤-reflexive (+-assoc s 4 (4 * fsize G)))
           (≤-trans (+-monoʳ-≤ s (+-monoʳ-≤ 4 (*-monoʳ-≤ 4 (m≤n+m (fsize G) (fsize F)))))
           (≤-trans (≤-reflexive (cong (s +_) (sym (*-suc 4 (fsize F + fsize G))))) h))

-- THE COMPILE-TIME WALKS EMIT NO MARKER. `seg-idle?` cannot reduce on a stuck
-- functor (unlike the fixed skeletons, where it is `refl`), so both walks need
-- their own induction on `F`.
visit-idle : ∀ (F : Functor) (todo tv tb s lb : ℕ)
           → seg-idle? (visit-walk todo tv tb F s lb) ≡ true
visit-idle (K _)   todo tv tb s lb = refl
visit-idle Id      todo tv tb s lb = refl
visit-idle (F ⊕ G) todo tv tb s lb =
  idle-++ (visit-walk todo tv tb G (s + 4) (suc (suc lb) + lsize F)) _
    (visit-idle G todo tv tb (s + 4) (suc (suc lb) + lsize F))
    (idle-++ (visit-walk todo tv tb F (s + 4) (suc (suc lb))) _
      (visit-idle F todo tv tb (s + 4) (suc (suc lb))) refl)
visit-idle (F ⊗ G) todo tv tb s lb =
  idle-++ (visit-walk todo tv tb F (s + 4) lb) _
    (visit-idle F todo tv tb (s + 4) lb)
    (visit-idle G todo tv tb (s + 4) (lb + lsize F))

rebuild-idle : ∀ (F : Functor) (val tv tb s lb : ℕ)
             → seg-idle? (rebuild-walk val tv tb F s lb) ≡ true
rebuild-idle (K _)   val tv tb s lb = refl
rebuild-idle Id      val tv tb s lb = refl
rebuild-idle (F ⊕ G) val tv tb s lb =
  idle-++ (rebuild-walk val tv tb G (s + 4) (suc (suc lb) + lsize F)) _
    (rebuild-idle G val tv tb (s + 4) (suc (suc lb) + lsize F))
    (idle-++ (rebuild-walk val tv tb F (s + 4) (suc (suc lb))) _
      (rebuild-idle F val tv tb (s + 4) (suc (suc lb))) refl)
rebuild-idle (F ⊗ G) val tv tb s lb =
  idle-++ (rebuild-walk val tv tb G (s + 4) (lb + lsize F)) _
    (rebuild-idle G val tv tb (s + 4) (lb + lsize F))
    (idle-++ (rebuild-walk val tv tb F (s + 4) lb) _
      (rebuild-idle F val tv tb (s + 4) lb) refl)

cata-branching-below : ∀ (F : Functor) (bb n1 l1 : ℕ) (at : AbstractTrace)
                     → SegOK bb at
                     → SegOK (cata-budget-of (cata-dispatch (strat-branching F) bb n1 l1 at))
                             (cata-trace-of (cata-dispatch (strat-branching F) bb n1 l1 at))
-- Plan 0.63 (iii): `I₁ ++ at ++ I₂`. I₁ absorbs init, flatten and the fold's
-- prefix (so it carries BOTH functor walks); I₂ is the fold's tail plus the
-- final read.
-- D099 / C1: the skeleton's own witness is UNCHANGED — it is still stated at
-- the pre-C1 budget `b`, and `segok-weaken` lifts it the two extra slots the
-- call path takes. Only the body/setup/call blocks are new, and the algebra's
-- weakening (`at'`, now unused) is gone: it lives in its own frame.
cata-branching-below F bb n1 l1 at bok =
  segok-++ (segok-idle _ refl setup)
   (segok-++ (segok-weaken b≤b2 (segok-idle _ I₁-idle I₁-all))
    (segok-++ (segok-idle _ refl call)
     (segok-++ (segok-weaken b≤b2 (segok-idle _ refl I₂-all))
               (cata-body-below _ _ bb at bok))))
  where
    b = n1 + 7 + 4 * fsize F + 4
    b≤b2 : b ≤ b + 4
    b≤b2 = m≤m+n b 4
    -- D131: `ev`/`pr` join `cl`/`k` above the skeleton's own range.
    bnd : ∀ (j : ℕ) → suc j ≤ 4 → b + j < b + 4
    bnd j p = ≤-trans (≤-reflexive (sym (+-suc b j))) (+-monoʳ-≤ b p)
    cl<b2 : b < b + 4
    cl<b2 = ≤-trans (s≤s (m≤m+n b 0)) (bnd 0 (s≤s z≤n))
    k<b2 : b + 1 < b + 4
    k<b2 = bnd 1 (s≤s (s≤s z≤n))
    ev<b2 : b + 2 < b + 4
    ev<b2 = bnd 2 (s≤s (s≤s (s≤s z≤n)))
    pr<b2 : b + 3 < b + 4
    pr<b2 = bnd 3 (s≤s (s≤s (s≤s (s≤s z≤n))))
    setup : All (SlotBelow (b + 4)) _
    setup = sb-none refl ∷ sb-slot refl ev<b2 (λ _ ()) ∷ sb-none refl ∷
            sb-slot refl k<b2 (λ _ ()) ∷ sb-none refl ∷ sb-slot refl pr<b2 (λ _ ()) ∷
            sb-none refl ∷ sb-slot refl ev<b2 (λ _ ()) ∷ sb-none refl ∷
            sb-none refl ∷ sb-slot refl cl<b2 (λ _ ()) ∷ sb-none refl ∷
            sb-none refl ∷ sb-none refl ∷ sb-none refl ∷
            sb-none refl ∷ sb-slot refl k<b2 (λ _ ()) ∷ sb-none refl ∷ []
    call : All (SlotBelow (b + 4)) _
    call = sb-none refl ∷ sb-slot refl k<b2 (λ _ ()) ∷ sb-slot refl pr<b2 (λ _ ()) ∷
           sb-none refl ∷ sb-slot refl k<b2 (λ _ ()) ∷ sb-none refl ∷
           sb-slot refl cl<b2 (λ _ ()) ∷ sb-none refl ∷ sb-none refl ∷
           sb-slot refl pr<b2 (λ _ ()) ∷ sb-none refl ∷ sb-none refl ∷ []
    fixed7 : n1 + 7 ≤ b
    fixed7 = ≤-trans (m≤m+n (n1 + 7) (4 * fsize F)) (m≤m+n (n1 + 7 + 4 * fsize F) 4)
    fixed7' : 7 + n1 ≤ b
    fixed7' = subst (_≤ b) (+-comm n1 7) fixed7
    q0 : n1 < b
    q0 = ≤-trans (m≤n⇒m≤1+n (m≤n⇒m≤1+n (m≤n⇒m≤1+n (m≤n⇒m≤1+n (m≤n⇒m≤1+n (m≤n⇒m≤1+n ≤-refl)))))) fixed7'
    q1 : suc n1 < b
    q1 = ≤-trans (m≤n⇒m≤1+n (m≤n⇒m≤1+n (m≤n⇒m≤1+n (m≤n⇒m≤1+n (m≤n⇒m≤1+n ≤-refl))))) fixed7'
    q2 : n1 + 2 < b
    q2 = ≤-trans (subst (λ z → suc z ≤ 7 + n1) (+-comm 2 n1)
                        (m≤n⇒m≤1+n (m≤n⇒m≤1+n (m≤n⇒m≤1+n (m≤n⇒m≤1+n ≤-refl))))) fixed7'
    q3 : n1 + 3 < b
    q3 = ≤-trans (subst (λ z → suc z ≤ 7 + n1) (+-comm 3 n1)
                        (m≤n⇒m≤1+n (m≤n⇒m≤1+n (m≤n⇒m≤1+n ≤-refl)))) fixed7'
    q4 : n1 + 4 < b
    q4 = ≤-trans (subst (λ z → suc z ≤ 7 + n1) (+-comm 4 n1)
                        (m≤n⇒m≤1+n (m≤n⇒m≤1+n ≤-refl))) fixed7'
    q5 : n1 + 5 < b
    q5 = ≤-trans (subst (λ z → suc z ≤ 7 + n1) (+-comm 5 n1) (m≤n⇒m≤1+n ≤-refl)) fixed7'
    q6 : n1 + 6 < b
    q6 = ≤-trans (subst (λ z → suc z ≤ 7 + n1) (+-comm 6 n1) ≤-refl) fixed7'
    walk-room : n1 + 7 + 4 * fsize F ≤ b
    walk-room = m≤m+n (n1 + 7 + 4 * fsize F) 4
    I₁-idle : seg-idle? (cata-br-I₁ F n1 l1) ≡ true
    I₁-idle = idle-++ (visit-walk n1 (n1 + 4) (n1 + 5) F (n1 + 7) (l1 + 4)) _
                (visit-idle F n1 (n1 + 4) (n1 + 5) (n1 + 7) (l1 + 4))
                (idle-++ (rebuild-walk (n1 + 2) (n1 + 4) (n1 + 5) F (n1 + 7) (l1 + 4 + lsize F)) _
                  (rebuild-idle F (n1 + 2) (n1 + 4) (n1 + 5) (n1 + 7) (l1 + 4 + lsize F)) refl)
    I₁-all : All (SlotBelow b) (cata-br-I₁ F n1 l1)
    I₁-all =
      ++⁺ (sb-none refl ∷ sb-slot refl q3 (λ _ ()) ∷
           sb-none refl ∷ sb-slot refl q6 (λ _ ()) ∷ sb-none refl ∷
           sb-none refl ∷ sb-none refl ∷
           sb-slot refl q6 (λ _ ()) ∷ sb-slot refl q1 (λ _ ()) ∷
           sb-slot refl q6 (λ _ ()) ∷ sb-slot refl q2 (λ _ ()) ∷
           sb-slot refl q6 (λ _ ()) ∷ sb-slot refl q0 (λ _ ()) ∷
           sb-slot refl q3 (λ _ ()) ∷ [])
      (++⁺ (push2-below n1 (n1 + 4) (n1 + 5) b q0 q4 q5)
      (++⁺ (sb-none refl ∷ sb-slot refl q0 (λ _ ()) ∷ sb-none refl ∷
            sb-none refl ∷ sb-none refl ∷ sb-slot refl q0 (λ _ ()) ∷
            sb-none refl ∷ sb-none refl ∷ sb-slot refl q3 (λ _ ()) ∷
            sb-slot refl q3 (λ _ ()) ∷ [])
      (++⁺ (push2-below (suc n1) (n1 + 4) (n1 + 5) b q1 q4 q5)
      (++⁺ (sb-slot refl q3 (λ _ ()) ∷ sb-none refl ∷ [])
      (++⁺ (visit-below F n1 (n1 + 4) (n1 + 5) (n1 + 7) (l1 + 4) b q0 q4 q5 walk-room)
      (++⁺ (sb-none refl ∷ sb-none refl ∷ [])
      (++⁺ (sb-none refl ∷ sb-slot refl q1 (λ _ ()) ∷ sb-none refl ∷
            sb-none refl ∷ sb-none refl ∷ sb-slot refl q1 (λ _ ()) ∷
            sb-none refl ∷ sb-none refl ∷ [])
      (++⁺ (rebuild-below F (n1 + 2) (n1 + 4) (n1 + 5) (n1 + 7) (l1 + 4 + lsize F) b q2 walk-room)
           (sb-none refl ∷ [])))))))))
    I₂-all : All (SlotBelow b) (cata-br-I₂ n1 l1)
    I₂-all = ++⁺ (push2-below (n1 + 2) (n1 + 4) (n1 + 5) b q2 q4 q5)
                 (sb-none refl ∷ sb-none refl ∷
                  sb-slot refl q2 (λ _ ()) ∷ sb-none refl ∷ sb-none refl ∷ [])



-- D099 / C1: `strat-const` no longer passes the algebra's witness through —
-- it emits a called body like the others, so it has a skeleton (setup + call)
-- and its own witness.
cata-slots-below : ∀ (st : CataStrategy) (bb n1 l1 : ℕ) (at : AbstractTrace)
                 → SegOK bb at
                 → SegOK (cata-budget-of (cata-dispatch st bb n1 l1 at))
                         (cata-trace-of (cata-dispatch st bb n1 l1 at))
cata-slots-below strat-const         bb n1 l1 at bok = cata-const-below bb n1 l1 at bok
cata-slots-below strat-nat           bb n1 l1 at bok = cata-nat-below bb n1 l1 at bok
cata-slots-below strat-linear        bb n1 l1 at bok = cata-linear-below bb n1 l1 at bok
cata-slots-below (strat-branching F) bb n1 l1 at bok = cata-branching-below F bb n1 l1 at bok

------------------------------------------------------------------------
-- THE INDUCTION: every instruction of the emitted MAIN trace addresses a slot
-- below the frontier `ir-to-trace'` hands back. Each splice weakens the
-- sub-IR's bound through `frontier-mono`.
------------------------------------------------------------------------
------------------------------------------------------------------------
-- D199: the re-suspension pass's slot budget.
------------------------------------------------------------------------
-- The pass stashes into the slots from its starting frontier up to the one it
-- returns, so its budget obligation needs the frontier to GROW — which is what
-- `resuspend-mono` says, and the only arithmetic the witness below needs.

resuspend-mono : ∀ (n l : ℕ) (lbl : LabelId) (env : ℕ) {F} (wf : WellFormedFI F)
               → n ≤ proj₁ (resuspend-layer n l lbl env wf)
resuspend-mono n l lbl env (wf-K _) = ≤-refl
resuspend-mono n l lbl env wf-Id    = m≤n⇒m≤1+n (m≤n⇒m≤1+n (m≤n⇒m≤1+n (m≤n⇒m≤1+n ≤-refl)))
resuspend-mono n l lbl env (wf-Prod wfF wfG) =
  ≤-trans (m≤n⇒m≤1+n (m≤n⇒m≤1+n (m≤n⇒m≤1+n ≤-refl)))
    (≤-trans (resuspend-mono (suc (suc (suc n))) l lbl env wfF)
             (resuspend-mono (proj₁ (resuspend-layer (suc (suc (suc n))) l lbl env wfF))
                             (proj₁ (proj₂ (resuspend-layer (suc (suc (suc n))) l lbl env wfF)))
                             lbl env wfG))
resuspend-mono n l lbl env (wf-Sum wfF wfG) =
  ≤-trans (m≤n⇒m≤1+n (m≤n⇒m≤1+n (m≤n⇒m≤1+n ≤-refl)))
    (≤-trans (resuspend-mono (suc (suc (suc n))) (suc (suc l)) lbl env wfF)
             (resuspend-mono (proj₁ (resuspend-layer (suc (suc (suc n))) (suc (suc l)) lbl env wfF))
                             (proj₁ (proj₂ (resuspend-layer (suc (suc (suc n))) (suc (suc l)) lbl env wfF)))
                             lbl env wfG))

resuspend-below : ∀ (n l : ℕ) (lbl : LabelId) (env : ℕ) {F} (wf : WellFormedFI F)
                → env < n
                → SegOK (proj₁ (resuspend-layer n l lbl env wf))
                        (proj₂ (proj₂ (resuspend-layer n l lbl env wf)))
resuspend-below n l lbl env (wf-K _) e<n = segok-idle _ refl []
-- Budget `n + 4`: the seed `a'` and its pair `q` at `n`, `suc n` (D273), then
-- the `Ana` site's two stashes; the environment pair is READ at `env < n`.
resuspend-below n l lbl env wf-Id e<n =
  segok-idle _ refl
    (sb-slot refl n0 (λ _ ()) ∷ sb-none refl ∷
     sb-slot refl n1 (λ _ ()) ∷ sb-slot refl e<B (λ _ ()) ∷ sb-none refl ∷
     sb-slot refl n1 (λ _ ()) ∷ sb-none refl ∷
     sb-slot refl n0 (λ _ ()) ∷ sb-none refl ∷ sb-slot refl n1 (λ _ ()) ∷
     sb-slot refl n2 (λ _ ()) ∷ sb-none refl ∷
     sb-slot refl ≤-refl (λ _ ()) ∷ sb-none refl ∷
     sb-slot refl n2 (λ _ ()) ∷ sb-none refl ∷
     sb-none refl ∷ sb-none refl ∷
     sb-slot refl ≤-refl (λ _ ()) ∷ [])
  where
    n2 : suc (suc n) < suc (suc (suc (suc n)))
    n2 = m≤n⇒m≤1+n ≤-refl
    n1 : suc n < suc (suc (suc (suc n)))
    n1 = m≤n⇒m≤1+n (m≤n⇒m≤1+n ≤-refl)
    n0 : n < suc (suc (suc (suc n)))
    n0 = m≤n⇒m≤1+n (m≤n⇒m≤1+n (m≤n⇒m≤1+n ≤-refl))
    e<B : env < suc (suc (suc (suc n)))
    e<B = ≤-trans e<n (m≤n⇒m≤1+n (m≤n⇒m≤1+n (m≤n⇒m≤1+n (m≤n⇒m≤1+n ≤-refl))))
-- Three stashes per container level — source, destination, and the child being
-- carried across the allocation — so the children start at `n + 3` and the
-- budget bound for every one of them comes from a single `base`.
resuspend-below n l lbl env (wf-Prod wfF wfG) e<n =
  segok-pre (store-at-slot n ∷ restore-input n ∷ load-indirect ∷ []) refl
    (sb-slot refl n<B (λ _ ()) ∷ sb-slot refl n<B (λ _ ()) ∷ sb-none refl ∷ [])
    (segok-++ (segok-weaken mid (resuspend-below (suc (suc (suc n))) l lbl env wfF e<3n))
      (segok-pre (store-at-slot (suc (suc n)) ∷ instr-alloc-heap 2 ∷
                  store-at-slot (suc n) ∷ mov-to-input ∷
                  load-from-slot (suc (suc n)) ∷ store-indirect ∷
                  restore-input n ∷ load-indirect-suc ∷ []) refl
        (sb-slot refl base (λ _ ()) ∷ sb-none refl ∷
         sb-slot refl sn<B (λ _ ()) ∷ sb-none refl ∷
         sb-slot refl base (λ _ ()) ∷ sb-none refl ∷
         sb-slot refl n<B (λ _ ()) ∷ sb-none refl ∷ [])
        (segok-++ (resuspend-below n2 l2 lbl env wfG e<n2)
          (segok-idle _ refl
            (sb-slot refl base (λ _ ()) ∷ sb-slot refl sn<B (λ _ ()) ∷
             sb-slot refl base (λ _ ()) ∷ sb-none refl ∷
             sb-slot refl sn<B (λ _ ()) ∷ [])))))
  where
    n2 = proj₁ (resuspend-layer (suc (suc (suc n))) l lbl env wfF)
    l2 = proj₁ (proj₂ (resuspend-layer (suc (suc (suc n))) l lbl env wfF))
    B  = proj₁ (resuspend-layer n2 l2 lbl env wfG)
    mid : n2 ≤ B
    mid = resuspend-mono n2 l2 lbl env wfG
    base : suc (suc (suc n)) ≤ B
    base = ≤-trans (resuspend-mono (suc (suc (suc n))) l lbl env wfF) mid
    sn<B : suc (suc n) ≤ B
    sn<B = ≤-trans (m≤n⇒m≤1+n ≤-refl) base
    n<B : suc n ≤ B
    n<B = ≤-trans (m≤n⇒m≤1+n (m≤n⇒m≤1+n ≤-refl)) base
    e<3n : env < suc (suc (suc n))
    e<3n = ≤-trans e<n (m≤n⇒m≤1+n (m≤n⇒m≤1+n (m≤n⇒m≤1+n ≤-refl)))
    e<n2 : env < n2
    e<n2 = ≤-trans e<3n (resuspend-mono (suc (suc (suc n))) l lbl env wfF)
resuspend-below n l lbl env (wf-Sum wfF wfG) e<n =
  segok-pre (store-at-slot n ∷ restore-input n ∷
             instr-ctrl (c-branch-tag-zero (ℓ o l)) ∷ []) refl
    (sb-slot refl n<B (λ _ ()) ∷ sb-slot refl n<B (λ _ ()) ∷ sb-none refl ∷ [])
    (segok-++ (arm 1 (resuspend-below n2 l2 lbl env wfG e<n2))
      (segok-pre (instr-ctrl (c-jmp (ℓ o (suc l))) ∷
                  instr-ctrl (c-label (ℓ o l)) ∷ []) refl
        (sb-none refl ∷ sb-none refl ∷ [])
        (segok-++ (arm 0 (segok-weaken mid
                            (resuspend-below (suc (suc (suc n))) (suc (suc l)) lbl env wfF e<3n)))
          (segok-idle _ refl (sb-none refl ∷ [])))))
  where
    n2 = proj₁ (resuspend-layer (suc (suc (suc n))) (suc (suc l)) lbl env wfF)
    l2 = proj₁ (proj₂ (resuspend-layer (suc (suc (suc n))) (suc (suc l)) lbl env wfF))
    B  = proj₁ (resuspend-layer n2 l2 lbl env wfG)
    mid : n2 ≤ B
    mid = resuspend-mono n2 l2 lbl env wfG
    base : suc (suc (suc n)) ≤ B
    base = ≤-trans (resuspend-mono (suc (suc (suc n))) (suc (suc l)) lbl env wfF) mid
    sn<B : suc (suc n) ≤ B
    sn<B = ≤-trans (m≤n⇒m≤1+n ≤-refl) base
    n<B : suc n ≤ B
    n<B = ≤-trans (m≤n⇒m≤1+n (m≤n⇒m≤1+n ≤-refl)) base
    e<3n : env < suc (suc (suc n))
    e<3n = ≤-trans e<n (m≤n⇒m≤1+n (m≤n⇒m≤1+n (m≤n⇒m≤1+n ≤-refl)))
    e<n2 : env < n2
    e<n2 = ≤-trans e<3n (resuspend-mono (suc (suc (suc n))) (suc (suc l)) lbl env wfF)
    arm : ∀ (tag : ℕ) {t} → SegOK B t
        → SegOK B (restore-input n ∷ load-indirect-suc ∷
                   t ++ (store-at-slot (suc (suc n)) ∷ instr-alloc-heap 2 ∷
                         store-at-slot (suc n) ∷ mov-to-input ∷
                         load-from-slot (suc (suc n)) ∷ store-indirect-suc ∷
                         instr-load-tag-lit tag ∷ store-indirect ∷
                         load-from-slot (suc n) ∷ []))
    arm tag ok =
      segok-pre (restore-input n ∷ load-indirect-suc ∷ []) refl
        (sb-slot refl n<B (λ _ ()) ∷ sb-none refl ∷ [])
        (segok-++ ok (segok-idle _ refl
          (sb-slot refl base (λ _ ()) ∷ sb-none refl ∷
           sb-slot refl sn<B (λ _ ()) ∷ sb-none refl ∷
           sb-slot refl base (λ _ ()) ∷ sb-none refl ∷
           sb-none refl ∷ sb-none refl ∷
           sb-slot refl sn<B (λ _ ()) ∷ [])))

sigop-below : ∀ {A B} (si : SigOpInfo A B) (n : ℕ) (m : Maybe CmpOp)
            → SegOK (sigop-budget n m) (sigop-code si n m)
sigop-below si n nothing  = segok-idle _ refl (sb-none refl ∷ [])
sigop-below si n (just _) = segok-idle _ refl
  (sb-none refl ∷ sb-none refl ∷ sb-slot refl (m≤n⇒m≤1+n ≤-refl) (λ _ ()) ∷ sb-none refl ∷
  sb-slot refl ≤-refl (λ _ ()) ∷ sb-none refl ∷ sb-slot refl (m≤n⇒m≤1+n ≤-refl) (λ _ ()) ∷
  sb-none refl ∷ sb-none refl ∷ sb-none refl ∷ sb-slot refl ≤-refl (λ _ ()) ∷ [])

slots-below : ∀ {A B} (ir : IR A B) (n l : ℕ)
            → SegOK (budget-of (ir-to-trace' n l ir)) (trace-of (ir-to-trace' n l ir))
slots-below id       n l = segok-idle _ refl (sb-none refl ∷ [])
slots-below fst      n l = segok-idle _ refl (sb-none refl ∷ [])
slots-below snd      n l = segok-idle _ refl (sb-none refl ∷ [])
slots-below terminal n l = segok-idle _ refl []
slots-below initial  n l = segok-idle _ refl (sb-none refl ∷ [])
slots-below (g ∘ f)  n l =
  segok-++ (segok-weaken (frontier-mono g _ _) (slots-below f n l))
      (segok-pre _ refl (sb-none refl ∷ []) (slots-below g _ _))
-- Stage G: the stack-shape clause that stood here collapsed onto this
-- same LHS when the pair's mode was dropped, and shadowed the heap one.
slots-below (⟨ f , g ⟩) n l =
  segok-pre _ refl
    (sb-none refl ∷ sb-slot refl (≤-trans (m≤n⇒m≤1+n (m≤n⇒m≤1+n (m≤n⇒m≤1+n ≤-refl))) h) (λ _ ()) ∷ [])
  (segok-++ (segok-weaken (frontier-mono g _ _) (slots-below f _ l))
      (segok-pre _ refl
        (sb-slot refl (≤-trans (m≤n⇒m≤1+n (m≤n⇒m≤1+n ≤-refl)) h) (λ _ ()) ∷
         sb-slot refl (≤-trans (m≤n⇒m≤1+n (m≤n⇒m≤1+n (m≤n⇒m≤1+n ≤-refl))) h) (λ _ ()) ∷ [])
       (segok-++ (slots-below g _ _)
           (segok-idle _ refl
            (sb-slot refl (≤-trans (m≤n⇒m≤1+n ≤-refl) h) (λ _ ()) ∷
            sb-none refl ∷
            sb-slot refl h (λ _ ()) ∷
            sb-none refl ∷
            sb-slot refl (≤-trans (m≤n⇒m≤1+n (m≤n⇒m≤1+n ≤-refl)) h) (λ _ ()) ∷
            sb-none refl ∷
            sb-slot refl (≤-trans (m≤n⇒m≤1+n ≤-refl) h) (λ _ ()) ∷
            sb-none refl ∷
            sb-slot refl h (λ _ ()) ∷ [])))))
  where h : suc (suc (suc (suc n))) ≤ budget-of (ir-to-trace' n l (⟨ f , g ⟩))
        h = ≤-trans (frontier-mono f _ l) (frontier-mono g _ _)
-- THE FLIP: the closure construction, then the body's own segment.
-- D159: the ENTRY BLOCK only. The body is a named block now, so its `SegOK`
-- is discharged at the block, AT ITS OWN BUDGET, rather than being folded into
-- the parent's segment here. That is the point: `SegOK (ir-stack-budget ir)`
-- applied the entry block's budget to the whole program, which is wrong for
-- any program with a body.
slots-below (curry b) n l =
  segok-idle _ refl
    (sb-none refl ∷ sb-slot refl (m≤n⇒m≤1+n ≤-refl) (λ _ ()) ∷ sb-none refl ∷
     sb-slot refl ≤-refl (λ _ ()) ∷ sb-none refl ∷ sb-slot refl (m≤n⇒m≤1+n ≤-refl) (λ _ ()) ∷
     sb-none refl ∷ sb-none refl ∷ sb-none refl ∷ sb-slot refl ≤-refl (λ _ ()) ∷ [])
slots-below apply n l = segok-idle _ refl
  (sb-none refl ∷ sb-slot refl (m≤n⇒m≤1+n (m≤n⇒m≤1+n ≤-refl)) (λ _ ()) ∷ sb-none refl ∷
  sb-none refl ∷ sb-none refl ∷ sb-none refl ∷
  sb-slot refl (m≤n⇒m≤1+n ≤-refl) (λ _ ()) ∷ sb-none refl ∷ sb-slot refl ≤-refl (λ _ ()) ∷
  sb-none refl ∷ sb-slot refl (m≤n⇒m≤1+n ≤-refl) (λ _ ()) ∷ sb-none refl ∷
  sb-slot refl (m≤n⇒m≤1+n (m≤n⇒m≤1+n ≤-refl)) (λ _ ()) ∷ sb-none refl ∷
  sb-slot refl ≤-refl (λ _ ()) ∷ sb-none refl ∷ sb-none refl ∷ [])
slots-below inl n l = segok-idle _ refl
  (sb-none refl ∷ sb-slot refl (m≤n⇒m≤1+n ≤-refl) (λ _ ()) ∷ sb-none refl ∷
  sb-slot refl ≤-refl (λ _ ()) ∷ sb-none refl ∷ sb-none refl ∷ sb-none refl ∷
  sb-slot refl (m≤n⇒m≤1+n ≤-refl) (λ _ ()) ∷ sb-none refl ∷ sb-slot refl ≤-refl (λ _ ()) ∷ [])
slots-below inr n l = segok-idle _ refl
  (sb-none refl ∷ sb-slot refl (m≤n⇒m≤1+n ≤-refl) (λ _ ()) ∷ sb-none refl ∷
  sb-slot refl ≤-refl (λ _ ()) ∷ sb-none refl ∷ sb-none refl ∷ sb-none refl ∷
  sb-slot refl (m≤n⇒m≤1+n ≤-refl) (λ _ ()) ∷ sb-none refl ∷ sb-slot refl ≤-refl (λ _ ()) ∷ [])
-- item 6: case is FLAT CONTROL — the branches are main-trace splices, bounded
-- by their own inductions (f weakened through g's frontier, like `∘`).
slots-below (case f g) n l =
  segok-pre _ refl (sb-none refl ∷ sb-none refl ∷ sb-none refl ∷ [])
      (segok-++ (slots-below g _ _)
           (segok-pre _ refl (sb-none refl ∷ sb-none refl ∷ sb-none refl ∷ sb-none refl ∷ [])
                (segok-++ (segok-weaken (frontier-mono g _ _) (slots-below f n (suc (suc l))))
                     (segok-idle _ refl (sb-none refl ∷ [])))))
slots-below (In _)   n l = segok-idle _ refl (sb-none refl ∷ [])
slots-below (out-μ _)  n l = segok-idle _ refl (sb-none refl ∷ [])
-- C1: the algebra is generated at frontier 0 — its slots are its own frame's,
-- so its witness is taken there and `segok-thunk` (inside `cata-body-below`)
-- carries it across the frame change.
slots-below (Cata {F} _ alg) n l =
  cata-slots-below (cata-strategy ⌈ F ⌉F) _ _ _ _ (slots-below alg 0 l)
slots-below (Out _)        n l =
  segok-idle _ refl (sb-none refl ∷ sb-none refl ∷ sb-none refl ∷ sb-none refl ∷ [])
slots-below (in-ν _) n l =
  segok-idle _ refl
    (sb-none refl ∷ sb-slot refl (m≤n⇒m≤1+n ≤-refl) (λ _ ()) ∷ sb-none refl ∷
     sb-slot refl ≤-refl (λ _ ()) ∷ sb-none refl ∷ sb-slot refl (m≤n⇒m≤1+n ≤-refl) (λ _ ()) ∷
     sb-none refl ∷ sb-none refl ∷ sb-none refl ∷ sb-slot refl ≤-refl (λ _ ()) ∷ [])
slots-below (Ana _ c) n l =
  segok-idle _ refl
    (sb-none refl ∷ sb-slot refl (m≤n⇒m≤1+n ≤-refl) (λ _ ()) ∷ sb-none refl ∷
     sb-slot refl ≤-refl (λ _ ()) ∷ sb-none refl ∷ sb-slot refl (m≤n⇒m≤1+n ≤-refl) (λ _ ()) ∷
     sb-none refl ∷ sb-none refl ∷ sb-none refl ∷ sb-slot refl ≤-refl (λ _ ()) ∷ [])
slots-below (SigOp si)     n l = sigop-below si n (cmp-of (sem si))
slots-below (Call _)      n l = segok-idle _ refl (sb-none refl ∷ [])
slots-below (const fits-int _)   n l = segok-idle _ refl (sb-none refl ∷ [])
slots-below (const fits-float _) n l = segok-idle _ refl (sb-none refl ∷ [])

------------------------------------------------------------------------
-- D159: …AND EVERY EMITTED BLOCK IS `SegOK` AT ITS OWN BUDGET.
--
-- `slots-below` covers the ENTRY block. This is its companion over the block
-- list, and together they are what the linked program needs — the entry's
-- budget no longer being claimed to govern a body that has its own.
------------------------------------------------------------------------
bodies-of : ℕ × ℕ × AbstractTrace × List (LabelId × ℕ × AbstractTrace)
          → List (LabelId × ℕ × AbstractTrace)
bodies-of (_ , _ , _ , bs) = bs

blocks-below : ∀ {A B} (ir : IR A B) (n l : ℕ)
             → All BlockOK (bodies-of (ir-to-trace' n l ir))
blocks-below id                  n l = []
blocks-below fst                 n l = []
blocks-below snd                 n l = []
blocks-below terminal            n l = []
blocks-below initial             n l = []
blocks-below (g ∘ f)             n l = ++⁺ (blocks-below f n l) (blocks-below g _ _)
blocks-below (⟨ f , g ⟩)         n l = ++⁺ (blocks-below f _ l) (blocks-below g _ _)
-- the two shapes that CREATE a block
blocks-below (curry b)      n l = slots-below b 0 (suc (suc l))
                                     ∷ blocks-below b 0 (suc (suc l))
blocks-below apply               n l = []
blocks-below inl                 n l = []
blocks-below inr                 n l = []
blocks-below (case f g)          n l = ++⁺ (blocks-below f n (suc (suc l)))
                                           (blocks-below g _ _)
blocks-below (In _)            n l = []
blocks-below (out-μ _)           n l = []
blocks-below (Cata {F} _ alg)    n l = blocks-below alg 0 l
blocks-below (Out _)             n l = []
blocks-below (in-ν _)          n l = segok-idle _ refl (sb-none refl ∷ []) ∷ []
-- D199: the block is `coalg ++ re-suspension`, and the budget is the pass's
-- final frontier — so the coalgebra's own witness weakens up to it.
-- D273: behind the prologue that keeps the seed pair in slot 0.
blocks-below (Ana wf c)          n l =
  segok-pre (mov-to-output ∷ store-at-slot 0 ∷ []) refl
    (sb-none refl ∷ sb-slot refl (≤-trans 0<cb mono) (λ _ ()) ∷ [])
    (segok-++ (segok-weaken mono (slots-below c 1 (suc l)))
              (resuspend-below cb (proj₁ (proj₂ (ir-to-trace' 1 (suc l) c))) (ℓ o l) 0 wf 0<cb))
    ∷ blocks-below c 1 (suc l)
  where
    cb = proj₁ (ir-to-trace' 1 (suc l) c)
    0<cb : 0 < cb
    0<cb = frontier-mono c 1 (suc l)
    mono = resuspend-mono cb (proj₁ (proj₂ (ir-to-trace' 1 (suc l) c))) (ℓ o l) 0 wf
blocks-below (SigOp _)           n l = []
blocks-below (Call _)           n l = []
blocks-below (const fits-int _)  n l = []
blocks-below (const fits-float _) n l = []

------------------------------------------------------------------------
-- …and the form the correspondence consumes.
--
-- D159: this is `AllSeg`, NOT `SegOK`. The linked program is NOT segment-
-- neutral: it ends in the entry block's `c-ret`, whose matching push is the
-- PROLOGUE (`subq $budget*8, %rsp`) — outside the trace entirely. `pop-with []`
-- is the identity, so at the top (`saved ≡ []`) that unmatched pop is harmless,
-- but demanding neutrality of the whole program would be demanding something
-- false. Neutrality stays what it always was: the property of a FRAGMENT, used
-- to compose. `emitted-slot-seg` — the only consumer — never wanted more.
------------------------------------------------------------------------
ir-slots-below-all : ∀ {A B} (ir : IR A B)
                   → AllSeg (mkSeg (ir-stack-budget ir) []) (ir-to-trace ir)
ir-slots-below-all ir =
  allseg-++ (ok-all (slots-below ir 0 0))
    (subst (λ z → AllSeg z (instr-ctrl (c-ret (ir-stack-budget ir)) ∷
                            blocks-layout (bodies-of (ir-to-trace' 0 0 ir))))
           (sym (ok-neu (slots-below ir 0 0) (mkSeg (ir-stack-budget ir) [])))
           (sb-none refl ∷ ok-all (segok-blocks _ (blocks-below ir 0 0))))

emitted-slot-seg : ∀ {A B} (ir : IR A B) (pc : ℕ) (i : AbstractInstr) (slot : Slot)
                 → trace-lookup (ir-to-trace ir) pc ≡ just i → slot-of i ≡ just slot
                 → slot < cur (seg-at (ir-to-trace ir) pc (mkSeg (ir-stack-budget ir) []))
emitted-slot-seg ir pc i slot ftq soq =
  below (allseg-at (ir-to-trace ir) pc (ir-slots-below-all ir) ftq) slot soq

------------------------------------------------------------------------
-- D245: a unit UNDER A SAVED STACK. In a program image a function's unit runs
-- after its entry marker pushed the function's budget over the caller's, so
-- the unit starts at `mkSeg b sv` with `sv` non-empty. Everything is as in
-- `ir-slots-below-all` except the terminator: `c-ret` now pops to the head of
-- `sv` rather than being the identity, and the blocks after it are
-- self-bracketed (`SegOK` at any state, by eta on `SegState`).
------------------------------------------------------------------------
-- D244/D245: a program's unit placed at label counter `l` (`main` is the
-- `l = 0` instance below).
ir-slots-below-under-lab : ∀ {A B} (ir : IR A B) (l : ℕ) (sv : List ℕ)
                     → AllSeg (mkSeg (ir-stack-budget-from l ir) sv) (ir-to-trace-lab l ir)
ir-slots-below-under-lab ir l sv =
  allseg-++ (ok-all (slots-below ir 0 l))
    (subst (λ z → AllSeg z (instr-ctrl (c-ret (ir-stack-budget-from l ir)) ∷
                            blocks-layout (bodies-of (ir-to-trace' 0 l ir))))
           (sym (ok-neu (slots-below ir 0 l) (mkSeg (ir-stack-budget-from l ir) sv)))
           (sb-none refl ∷ ok-all (segok-blocks _ (blocks-below ir 0 l))))

-- …and where it leaves the segment state: the terminator's pop, nothing else.
ir-seg-fold-lab : ∀ {A B} (ir : IR A B) (l : ℕ) (sv : List ℕ)
            → seg-fold (ir-to-trace-lab l ir) (mkSeg (ir-stack-budget-from l ir) sv)
              ≡ pop-with sv (mkSeg (ir-stack-budget-from l ir) sv)
ir-seg-fold-lab ir l sv =
  trans (seg-fold-++ (trace-of (ir-to-trace' 0 l ir))
                     (instr-ctrl (c-ret (ir-stack-budget-from l ir)) ∷
                      blocks-layout (bodies-of (ir-to-trace' 0 l ir)))
                     (mkSeg (ir-stack-budget-from l ir) sv))
        (trans (cong (seg-fold (instr-ctrl (c-ret (ir-stack-budget-from l ir)) ∷
                                blocks-layout (bodies-of (ir-to-trace' 0 l ir))))
                     (ok-neu (slots-below ir 0 l) (mkSeg (ir-stack-budget-from l ir) sv)))
               (ok-neu (segok-blocks {ir-stack-budget-from l ir} _ (blocks-below ir 0 l))
                       (pop-with sv (mkSeg (ir-stack-budget-from l ir) sv))))

-- Plan 0.107: THE OUTERMOST UNIT, linked with the SILENT STOP (`link-top`):
-- exactly `ir-slots-below-under`, except that the terminator is two
-- segment-idle instructions (`c-label`, `c-jmp`) instead of `c-ret`'s pop — so
-- the unit leaves the segment where it began.
ir-slots-below-top : ∀ {A B} (ir : IR A B) (d : LabelId) (sv : List ℕ)
                   → AllSeg (mkSeg (ir-stack-budget ir) sv) (link-top d (ir-to-unit ir))
ir-slots-below-top ir d sv =
  allseg-++ (ok-all (slots-below ir 0 0))
    (subst (λ z → AllSeg z (instr-ctrl (c-label d) ∷ instr-ctrl (c-jmp d) ∷
                            blocks-layout (bodies-of (ir-to-trace' 0 0 ir))))
           (sym (ok-neu (slots-below ir 0 0) (mkSeg (ir-stack-budget ir) sv)))
           (sb-none refl ∷ sb-none refl ∷ ok-all (segok-blocks _ (blocks-below ir 0 0))))

ir-seg-fold-top : ∀ {A B} (ir : IR A B) (d : LabelId) (sv : List ℕ)
                → seg-fold (link-top d (ir-to-unit ir)) (mkSeg (ir-stack-budget ir) sv)
                  ≡ mkSeg (ir-stack-budget ir) sv
ir-seg-fold-top ir d sv =
  trans (seg-fold-++ (trace-of (ir-to-trace' 0 0 ir))
                     (instr-ctrl (c-label d) ∷ instr-ctrl (c-jmp d) ∷
                      blocks-layout (bodies-of (ir-to-trace' 0 0 ir)))
                     (mkSeg (ir-stack-budget ir) sv))
        (trans (cong (seg-fold (instr-ctrl (c-label d) ∷ instr-ctrl (c-jmp d) ∷
                                blocks-layout (bodies-of (ir-to-trace' 0 0 ir))))
                     (ok-neu (slots-below ir 0 0) (mkSeg (ir-stack-budget ir) sv)))
               (ok-neu (segok-blocks {ir-stack-budget ir} _ (blocks-below ir 0 0))
                       (mkSeg (ir-stack-budget ir) sv)))

ir-slots-below-under : ∀ {A B} (ir : IR A B) (sv : List ℕ)
                     → AllSeg (mkSeg (ir-stack-budget ir) sv) (ir-to-trace ir)
ir-slots-below-under ir = ir-slots-below-under-lab ir 0

ir-seg-fold : ∀ {A B} (ir : IR A B) (sv : List ℕ)
            → seg-fold (ir-to-trace ir) (mkSeg (ir-stack-budget ir) sv)
              ≡ pop-with sv (mkSeg (ir-stack-budget ir) sv)
ir-seg-fold ir = ir-seg-fold-lab ir 0
