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
-- `load-from-slot`, `store-at-slot`, `restore-input`, `worklist-*`.
--
-- Two inductions, both over `ir-to-trace'`:
--   * `frontier-mono` — the frontier never retreats. Every splice needs it,
--     because a sub-IR's slots are bounded by ITS frontier, which the rest of
--     the emission then advances past.
--   * `slots-below` — every instruction of the returned MAIN trace is bounded
--     by the returned frontier.
------------------------------------------------------------------------

-- Plan 0.63 (D089): parameterised by the DEFINITION'S identity, which keys
-- its labels. `o` is constant for a whole definition, so it belongs on the
-- module rather than on every lemma — which is exactly what keeps the
-- statements below UNCHANGED under D089: `IRToTrace` is imported APPLIED,
-- so each `ir-to-trace' n l ir` reads as it always did.
open import Once.Spec.Name using (CanonicalName)
open import Once.CCC.Label using (LabelId; ℓ)

module Once.CCC.Codegen.SlotBudget (o : CanonicalName) where

open import Data.Nat using (ℕ; suc; _+_; _≤_; _<_; z≤n; s≤s; _*_; _⊔_; _∸_)
open import Data.Nat.Properties using
  (≤-refl; ≤-trans; ≤-reflexive; n≤1+n; m≤m+n; m≤n+m; +-monoʳ-≤; +-comm; +-assoc; +-suc;
   *-suc; *-monoʳ-≤; m≤n⇒m≤1+n)
open import Data.Bool using (true)
open import Data.Unit using (tt)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.All.Properties using (++⁺)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)

open import Once.IR using (IR; id; _∘_; ⟨_,_⟩; fst; snd; inl; inr; case; terminal; initial; curry; apply; In; out-μ; Cata; Out; in-ν; Ana; Iter; SigOp; Call; const)
open import Once.IRTy using (IRTy; IRFunctor; ⟦_⟧TI; ν-type; fits-int; fits-float; ⌈_⌉F; WellFormedFI; wf-K; wf-Id; wf-Sum; wf-Prod) renaming (_+_ to _+ᵀ_)
open import Once.Spec.Type using (K; Id; _⊕_; _⊗_)
open import Once.Spec.Type using (Fun)
open import Once.CCC.Machine.SMCore using (blocks-layout; link-top)
open import Once.CCC.Machine.SMCore using
  (AbstractInstr; AbstractTrace; mov-to-output; mov-to-input; store-at-slot; load-from-slot; store-indirect; store-indirect-suc; instr-alloc-heap; instr-load-tag-lit; instr-ctrl; c-ret; c-label; c-jmp; restore-input; load-indirect; load-indirect-suc; c-branch-tag-zero; c-leave; store-at; load-at; addr-at; lea-slot)
open import Once.CCC.Machine.Locations using (Slot)
open import Once.CCC.Machine.MuRep using (MuRep; mu-box; mu-unit; mu-ptr; mu-rep)
open import Once.CCC.Machine.InstrSlot using (slot-of)
open import Once.SigOp.Info using (SigOpInfo; module SigOpInfo)
open SigOpInfo using (sem)
open import Once.Arith.CmpOp using (CmpOp)
open import Once.Arith.SigOp.Compare using (cmp-of)
open import Once.CCC.Codegen.IRToTrace o using
  (ir-to-trace'; ir-to-trace; ir-stack-budget; resuspend-layer; ir-to-trace-lab; ir-stack-budget-from; ir-to-unit; sigop-budget; sigop-code; CataStrategy; strat-const; strat-box; strat-branching; cata-strategy; cata-dispatch; in-trace; in-next; out-trace; fsize; lsize; push2; pop2; wrap-sum; visit-walk; rebuild-walk; cata-br-I₁; cata-br-I₂; cata-body; cata-call-setup; cata-call-from; env-entry; env-prologue; inj-trace)

-- the o-independent segment machinery (`SlotBelow`, `SegState`, `AllSeg`,
-- `SegOK`, …), split out so a program image shares one `AllSeg`
open import Once.CCC.Codegen.SlotSeg
open import Once.CCC.Codegen.FlatLayout
  using (Kind; word; flat; kind; put; put-k; get; get-k; fill; put-All; put-k-All; get-All; get-k-All; fill-All; lkind; lsz)
open import Once.CCC.Codegen.Size using (size)
import Data.List.Relation.Unary.All as All
open SegOK using (ok-all; ok-neu)
open SegState using (cur)
open SlotBelow using (below)

------------------------------------------------------------------------
-- plan 0.123 B.4 α: a straight-line piece is OK when each instruction is below
-- the frontier AND leaves the segment alone (`SB`); the flat layout's code is
-- such a piece once its two stash slots are below the frontier.
------------------------------------------------------------------------
SB : ℕ → AbstractInstr → Set
SB b i = SlotBelow b i × (is-id? (seg-action i) ≡ true)

segok-SB : ∀ {b} (t : AbstractTrace) → All (SB b) t → SegOK b t
segok-SB t p = segok-idle t (idle-All t (All.map proj₂ p)) (All.map proj₁ p)

nn : ∀ {b i} → slot-of i ≡ nothing → is-id? (seg-action i) ≡ true → SB b i
nn e i = sb-none e , i

ss : ∀ {b k i} → slot-of i ≡ just k → k < b → (∀ slot → i ≡ lea-slot slot → suc slot < b)
   → is-id? (seg-action i) ≡ true → SB b i
ss e p q i = sb-slot e p q , i

put-SB : ∀ {b} X s blk o′ → s < b → blk < b → All (SB b) (put X s blk o′)
put-SB X s blk o′ ps pb =
  put-All X s blk o′ (ss refl ps (λ _ ()) refl) (ss refl pb (λ _ ()) refl) (ss refl ps (λ _ ()) refl)
          (λ _ → nn refl refl) (λ _ → nn refl refl)

put-k-SB : ∀ {b} kd n s blk o′ → s < b → blk < b → All (SB b) (put-k kd n s blk o′)
put-k-SB kd n s blk o′ ps pb =
  put-k-All kd n s blk o′ (ss refl ps (λ _ ()) refl) (ss refl pb (λ _ ()) refl) (ss refl ps (λ _ ()) refl)
            (λ _ → nn refl refl) (λ _ → nn refl refl)

get-SB : ∀ {b} X k → All (SB b) (get X k)
get-SB X k = get-All X k (λ _ → nn refl refl) (λ _ → nn refl refl) (nn refl refl)

get-k-SB : ∀ {b} kd n k → All (SB b) (get-k kd n k)
get-k-SB kd n k = get-k-All kd n k (λ _ → nn refl refl) (λ _ → nn refl refl) (nn refl refl)

-- D382: a sum's padding fill touches no slot
fill-SB : ∀ {b} from c → All (SB b) (fill from c)
fill-SB from c = fill-All from c (nn refl refl) (λ _ → nn refl refl)

segok-get : ∀ {b} X k → SegOK b (get X k)
segok-get X k = segok-SB _ (get-SB X k)

segok-put : ∀ {b} X s blk o′ → s < b → blk < b → SegOK b (put X s blk o′)
segok-put X s blk o′ ps pb = segok-SB _ (put-SB X s blk o′ ps pb)

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
cata-mono : ∀ (E A : IRTy) (G : Fun 0) (st : CataStrategy) (bb n1 l1 : ℕ) (at : AbstractTrace)
          → n1 ≤ cata-budget-of (cata-dispatch E A G st bb n1 l1 at)
cata-mono E A G strat-const         bb n1 l1 at = m≤m+n n1 4
cata-mono E A G strat-box           bb n1 l1 at = m≤m+n n1 4
cata-mono E A G (strat-branching F) bb n1 l1 at =
  ≤-trans (m≤m+n n1 7)
    (≤-trans (m≤m+n (n1 + 7) (4 * fsize F))
      (≤-trans (m≤m+n ((n1 + 7) + 4 * fsize F) 4)
               (m≤m+n (((n1 + 7) + 4 * fsize F) + 4) 4)))

-- Plan 0.108: a comparison stashes its tag and its sum, two slots.
sigop-mono : ∀ (n : ℕ) (m : Maybe CmpOp) → n ≤ sigop-budget n m
sigop-mono n nothing  = ≤-refl
sigop-mono n (just _) = ≤-trans (n≤1+n n) (n≤1+n (suc n))

-- D366: `In`'s box takes one slot.
in-mono : ∀ (r : MuRep) kd (n : ℕ) → n ≤ in-next r kd n
in-mono mu-box  kd n = n≤1+n n
in-mono mu-unit kd n = ≤-refl
in-mono mu-ptr  word n = ≤-refl
in-mono mu-ptr  flat n = m≤n⇒m≤1+n (n≤1+n n)

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
frontier-mono (In {F} _) n l = in-mono (mu-rep F) _ n
frontier-mono (out-μ _)   n l = ≤-refl
-- C1: the algebra runs in its OWN frame (generated at frontier 0), so the
-- caller's frontier is not advanced by it at all — the dispatch takes `n`
-- directly and only the cata's own scratch is added.
frontier-mono (Cata {F} _ {E} {A} alg) n l = cata-mono E A ⌈ F ⌉F (cata-strategy ⌈ F ⌉F) _ _ _ _
frontier-mono (Out _)        n l = ≤-refl
-- D189: the same two-cell build as `Ana`, with `id` as the block.
frontier-mono (in-ν _)     n l = ≤-trans (n≤1+n n) (n≤1+n (suc n))
-- D189: the ν suspension is `curry`'s closure record cell for cell, so
-- its walk clause is `curry`'s. The coalgebra is a named block, like the
-- closure body, emitted at frontier 0 under the ν's own label.
frontier-mono (Ana _ c)      n l = ≤-trans (n≤1+n n) (n≤1+n (suc n))
-- the loop's two stashes, then the round above them.
frontier-mono (Iter b)       n l =
  ≤-trans (n≤1+n n) (≤-trans (n≤1+n (suc n)) (≤-trans (n≤1+n (suc (suc n))) (≤-trans (n≤1+n (suc (suc (suc n)))) (frontier-mono b _ _))))
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
-- plan 0.123 B.4 α: the setup and the call, at slots `cl`/`k`/`ev`/`pr`
-- below `b` (the environment and the layer `put` into the argument pair).
setup-SB : ∀ {b} E cl k ev bl → cl < b → k < b → ev < b → All (SB b) (cata-call-setup E cl k ev bl)
setup-SB E cl k ev bl pc pk pe =
  ++⁺ (get-SB E 0)
      (ss refl pe (λ _ ()) refl ∷ nn refl refl ∷ ss refl pk (λ _ ()) refl ∷ nn refl refl ∷
       ss refl pc (λ _ ()) refl ∷ nn refl refl ∷ nn refl refl ∷ nn refl refl ∷ nn refl refl ∷
       nn refl refl ∷ ss refl pk (λ _ ()) refl ∷ nn refl refl ∷ [])

call-SB : ∀ {b} i0 → SB b i0 → ∀ E lk ls cl k ev pr → cl < b → k < b → ev < b → pr < b
        → All (SB b) (cata-call-from i0 E lk ls cl k ev pr)
call-SB i0 p0 E lk ls cl k ev pr pc pk pe pp =
  p0 ∷ ss refl pk (λ _ ()) refl ∷ nn refl refl ∷ ss refl pp (λ _ ()) refl ∷
  ++⁺ (put-SB E ev pr 0 pe pp)
      (++⁺ (put-k-SB lk ls k pr _ pk pp)
           (ss refl pc (λ _ ()) refl ∷ nn refl refl ∷ nn refl refl ∷
            ss refl pp (λ _ ()) refl ∷ nn refl refl ∷ nn refl refl ∷ []))

cata-const-below : ∀ (E A : IRTy) (G : Fun 0) (bb n1 l1 : ℕ) (at : AbstractTrace) → SegOK bb at
                 → SegOK (cata-budget-of (cata-dispatch E A G strat-const bb n1 l1 at))
                         (cata-trace-of (cata-dispatch E A G strat-const bb n1 l1 at))
cata-const-below E A G bb n1 l1 at bok =
  segok-++ (segok-SB _ (setup-SB E n1 (n1 + 1) (n1 + 2) l1 cl<b k<b ev<b))
    (segok-++ (segok-SB _ (call-SB _ (nn refl refl) E (lkind G word) (lsz G 1) n1 (n1 + 1) (n1 + 2) (n1 + 3)
                                   cl<b k<b ev<b pr<b))
              (cata-body-below _ _ bb at bok))
  where
    -- D131: four slots now — `cl`/`k` as before, plus `ev` (the fold's
    -- environment) and `pr` (each call's fresh argument pair). `suc (n1 + j) ≡
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

push2-below : ∀ (topSlot tv tb b : ℕ) → topSlot < b → tv < b → tb < b
            → All (SB b) (push2 topSlot tv tb)
push2-below topSlot tv tb b pt pv pb =
  ss refl pv (λ _ ()) refl ∷ nn refl refl ∷ ss refl pb (λ _ ()) refl ∷
  nn refl refl ∷ ss refl pv (λ _ ()) refl ∷ nn refl refl ∷
  ss refl pt (λ _ ()) refl ∷ nn refl refl ∷
  ss refl pb (λ _ ()) refl ∷ ss refl pt (λ _ ()) refl ∷ []

cata-box-below : ∀ (E A : IRTy) (G : Fun 0) (bb n1 l1 : ℕ) (at : AbstractTrace) → SegOK bb at
                 → SegOK (cata-budget-of (cata-dispatch E A G strat-box bb n1 l1 at))
                         (cata-trace-of (cata-dispatch E A G strat-box bb n1 l1 at))
cata-box-below E A G bb n1 l1 at bok =
  segok-++ (segok-SB _ (setup-SB E n1 (n1 + 1) (n1 + 2) l1 cl<b k<b ev<b))
    (segok-++ (segok-SB _ (call-SB _ (nn refl refl) E (lkind G word) (lsz G 1) n1 (n1 + 1) (n1 + 2) (n1 + 3)
                                   cl<b k<b ev<b pr<b))
              (cata-body-below _ _ bb at bok))
  where
    -- D131: four slots now — `cl`/`k` as before, plus `ev` (the fold's
    -- environment) and `pr` (each call's fresh argument pair). `suc (n1 + j) ≡
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

-- pop it: one addressed slot
pop2-below : ∀ (topSlot b : ℕ) → topSlot < b → All (SB b) (pop2 topSlot)
pop2-below topSlot b pt =
  ss refl pt (λ _ ()) refl ∷ nn refl refl ∷ nn refl refl ∷
  ss refl pt (λ _ ()) refl ∷ nn refl refl ∷ []

-- wrap the payload into a sum node: two addressed slots (item 6 made this a
-- MAIN-trace segment — it used to hide inside a nested `⊕` branch)
wrap-sum-below : ∀ (tag : ℕ) pk ps ss′ (s b : ℕ) → s < b → suc s < b
               → All (SB b) (wrap-sum tag pk ps ss′ s)
wrap-sum-below tag pk ps ss′ s b p-s pss =
  ss refl p-s (λ _ ()) refl ∷ nn refl refl ∷ ss refl pss (λ _ ()) refl ∷
  nn refl refl ∷ nn refl refl ∷ nn refl refl ∷
  ++⁺ (fill-SB _ (ss′ ∸ suc ps)) (++⁺ (put-k-SB pk ps s (suc s) 1 p-s pss) (ss refl pss (λ _ ()) refl ∷ []))

getμ-SB : ∀ {b} (G : Fun 0) k → All (SB b) (get-k (lkind G word) (lsz G 1) k)
getμ-SB G k = get-k-SB (lkind G word) (lsz G 1) k

-- the VISIT walk: `Id` is a push (fixed slots), `⊕` one case instruction,
-- `⊗` owns `s` and recurses at `s+4`
visit-below : ∀ (F : Fun 0) (todo tv tb s lb b : ℕ)
            → todo < b → tv < b → tb < b → s + 4 * fsize F ≤ b
            → All (SB b) (visit-walk todo tv tb F s lb)
visit-below (K _) todo tv tb s lb b pt pv pb h = []
visit-below Id    todo tv tb s lb b pt pv pb h =
  nn refl refl ∷ push2-below todo tv tb b pt pv pb
-- item 6: the ⊕ dispatch is FLAT — branch prologues/joins are label/ctrl
-- instructions (slot-free), the branch walks are inline splices.
visit-below (F ⊕ G) todo tv tb s lb b pt pv pb h =
  ++⁺ (nn refl refl ∷ [])
      (++⁺ (getμ-SB G 1)
      (++⁺ (nn refl refl ∷ [])
      (++⁺ (visit-below G todo tv tb (s + 4) _ b pt pv pb recG)
      (++⁺ (nn refl refl ∷ nn refl refl ∷ [])
      (++⁺ (getμ-SB F 1)
      (++⁺ (nn refl refl ∷ [])
      (++⁺ (visit-below F todo tv tb (s + 4) _ b pt pv pb recF)
           (nn refl refl ∷ []))))))))
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
  ++⁺ (nn refl refl ∷ ss refl s<b (λ _ ()) refl ∷ [])
      (++⁺ (getμ-SB F 0)
      (++⁺ (nn refl refl ∷ [])
      (++⁺ (visit-below F todo tv tb (s + 4) _ b pt pv pb recF)
      (++⁺ (ss refl s<b (λ _ ()) refl ∷ [])
      (++⁺ (getμ-SB G (lsz F 1))
      (++⁺ (nn refl refl ∷ [])
           (visit-below G todo tv tb (s + 4) _ b pt pv pb recG)))))))
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
rebuild-below : ∀ (ck : Kind) (cs : ℕ) (F : Fun 0) (val tv tb s lb b : ℕ)
              → val < b → s + 4 * fsize F ≤ b
              → All (SB b) (rebuild-walk val tv tb ck cs F s lb)
rebuild-below ck cs (K _) val tv tb s lb b pt h = nn refl refl ∷ []
rebuild-below ck cs Id    val tv tb s lb b pt h = pop2-below val b pt
-- item 6: flat ⊕ — the `wrap-sum`s are main-trace segments now.
rebuild-below ck cs (F ⊕ G) val tv tb s lb b pt h =
  ++⁺ (nn refl refl ∷ [])
      (++⁺ (getμ-SB G 1)
      (++⁺ (nn refl refl ∷ [])
      (++⁺ (rebuild-below ck cs G val tv tb (s + 4) _ b pt recG)
      (++⁺ (wrap-sum-below 1 (lkind G ck) (lsz G cs) (lsz (F ⊕ G) cs) s b s<b b-ss)
      (++⁺ (nn refl refl ∷ nn refl refl ∷ [])
      (++⁺ (getμ-SB F 1)
      (++⁺ (nn refl refl ∷ [])
      (++⁺ (rebuild-below ck cs F val tv tb (s + 4) _ b pt recF)
      (++⁺ (wrap-sum-below 0 (lkind F ck) (lsz F cs) (lsz (F ⊕ G) cs) s b s<b b-ss)
           (nn refl refl ∷ []))))))))))
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
rebuild-below ck cs (F ⊗ G) val tv tb s lb b pt h =
  ++⁺ (nn refl refl ∷ ss refl s<b (λ _ ()) refl ∷ [])
      (++⁺ (getμ-SB G (lsz F 1))
      (++⁺ (nn refl refl ∷ [])
      (++⁺ (rebuild-below ck cs G val tv tb (s + 4) _ b pt recG)
      (++⁺ (ss refl b-s2 (λ _ ()) refl ∷ ss refl s<b (λ _ ()) refl ∷ [])
      (++⁺ (getμ-SB F 0)
      (++⁺ (nn refl refl ∷ [])
      (++⁺ (rebuild-below ck cs F val tv tb (s + 4) _ b pt recF)
      (++⁺ (ss refl b-ss (λ _ ()) refl ∷ nn refl refl ∷ ss refl b-s3 (λ _ ()) refl ∷ [])
      (++⁺ (put-k-SB (lkind F ck) (lsz F cs) (suc s) (s + 3) 0 b-ss b-s3)
      (++⁺ (put-k-SB (lkind G ck) (lsz G cs) (s + 2) (s + 3) (lsz F cs) b-s2 b-s3)
           (ss refl b-s3 (λ _ ()) refl ∷ [])))))))))))
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

-- THE COMPILE-TIME WALKS EMIT NO MARKER, at any slots (for the label proofs,
-- which need idleness without a frontier).
Idle : AbstractInstr → Set
Idle i = is-id? (seg-action i) ≡ true

getμ-idle : ∀ (G : Fun 0) k → All Idle (get-k (lkind G word) (lsz G 1) k)
getμ-idle G k = get-k-All (lkind G word) (lsz G 1) k (λ _ → refl) (λ _ → refl) refl

push2-idle : ∀ t v b′ → All Idle (push2 t v b′)
push2-idle t v b′ = refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ []

visit-idleA : ∀ (F : Fun 0) (todo tv tb s lb : ℕ) → All Idle (visit-walk todo tv tb F s lb)
visit-idleA (K _)   todo tv tb s lb = []
visit-idleA Id      todo tv tb s lb = refl ∷ push2-idle todo tv tb
visit-idleA (F ⊕ G) todo tv tb s lb =
  ++⁺ (refl ∷ []) (++⁺ (getμ-idle G 1) (++⁺ (refl ∷ [])
  (++⁺ (visit-idleA G todo tv tb (s + 4) _) (++⁺ (refl ∷ refl ∷ [])
  (++⁺ (getμ-idle F 1) (++⁺ (refl ∷ [])
  (++⁺ (visit-idleA F todo tv tb (s + 4) _) (refl ∷ []))))))))
visit-idleA (F ⊗ G) todo tv tb s lb =
  ++⁺ (refl ∷ refl ∷ []) (++⁺ (getμ-idle F 0) (++⁺ (refl ∷ [])
  (++⁺ (visit-idleA F todo tv tb (s + 4) _) (++⁺ (refl ∷ [])
  (++⁺ (getμ-idle G _) (++⁺ (refl ∷ []) (visit-idleA G todo tv tb (s + 4) _)))))))

visit-idle : ∀ (F : Fun 0) (todo tv tb s lb : ℕ)
           → seg-idle? (visit-walk todo tv tb F s lb) ≡ true
visit-idle F todo tv tb s lb = idle-All _ (visit-idleA F todo tv tb s lb)

rebuild-idleA : ∀ (ck : Kind) (cs : ℕ) (F : Fun 0) (val tv tb s lb : ℕ)
              → All Idle (rebuild-walk val tv tb ck cs F s lb)
rebuild-idleA ck cs (K _)   val tv tb s lb = refl ∷ []
rebuild-idleA ck cs Id      val tv tb s lb = refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ []
rebuild-idleA ck cs (F ⊕ G) val tv tb s lb =
  ++⁺ (refl ∷ []) (++⁺ (getμ-idle G 1) (++⁺ (refl ∷ [])
  (++⁺ (rebuild-idleA ck cs G val tv tb (s + 4) _) (++⁺ (ws (lkind G ck) (lsz G cs) 1)
  (++⁺ (refl ∷ refl ∷ []) (++⁺ (getμ-idle F 1) (++⁺ (refl ∷ [])
  (++⁺ (rebuild-idleA ck cs F val tv tb (s + 4) _) (++⁺ (ws (lkind F ck) (lsz F cs) 0) (refl ∷ []))))))))))
  where ws : ∀ pk ps tag → All Idle (wrap-sum tag pk ps (lsz (F ⊕ G) cs) s)
        ws pk ps tag = refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ refl ∷
                       ++⁺ (fill-All _ (lsz (F ⊕ G) cs ∸ suc ps) refl (λ _ → refl))
                           (++⁺ (put-k-All pk ps s (suc s) 1 refl refl refl (λ _ → refl) (λ _ → refl)) (refl ∷ []))
rebuild-idleA ck cs (F ⊗ G) val tv tb s lb =
  ++⁺ (refl ∷ refl ∷ []) (++⁺ (getμ-idle G _) (++⁺ (refl ∷ [])
  (++⁺ (rebuild-idleA ck cs G val tv tb (s + 4) _) (++⁺ (refl ∷ refl ∷ [])
  (++⁺ (getμ-idle F 0) (++⁺ (refl ∷ [])
  (++⁺ (rebuild-idleA ck cs F val tv tb (s + 4) _) (++⁺ (refl ∷ refl ∷ refl ∷ [])
  (++⁺ (put-k-All (lkind F ck) (lsz F cs) (suc s) (s + 3) 0 refl refl refl (λ _ → refl) (λ _ → refl))
  (++⁺ (put-k-All (lkind G ck) (lsz G cs) (s + 2) (s + 3) _ refl refl refl (λ _ → refl) (λ _ → refl))
       (refl ∷ [])))))))))))

rebuild-idle : ∀ (ck : Kind) (cs : ℕ) (F : Fun 0) (val tv tb s lb : ℕ)
             → seg-idle? (rebuild-walk val tv tb ck cs F s lb) ≡ true
rebuild-idle ck cs F val tv tb s lb = idle-All _ (rebuild-idleA ck cs F val tv tb s lb)

cata-branching-below : ∀ (E A : IRTy) (G F : Fun 0) (bb n1 l1 : ℕ) (at : AbstractTrace)
                     → SegOK bb at
                     → SegOK (cata-budget-of (cata-dispatch E A G (strat-branching F) bb n1 l1 at))
                             (cata-trace-of (cata-dispatch E A G (strat-branching F) bb n1 l1 at))
-- Plan 0.63 (iii): `I₁ ++ at ++ I₂`. I₁ absorbs init, flatten and the fold's
-- prefix (so it carries BOTH functor walks); I₂ is the fold's tail plus the
-- final read.
-- D099 / C1: the skeleton's own witness is UNCHANGED — it is still stated at
-- the pre-C1 budget `b`, and `segok-weaken` lifts it the two extra slots the
-- call path takes. Only the body/setup/call blocks are new, and the algebra's
-- weakening (`at'`, now unused) is gone: it lives in its own frame.
cata-branching-below E A G F bb n1 l1 at bok =
  segok-++ (segok-SB _ (setup-SB E b (b + 1) (b + 2) _ cl<b2 k<b2 ev<b2))
   (segok-++ (segok-weaken b≤b2 (segok-SB _ I₁-all))
    (segok-++ (segok-SB _ (call-SB _ (nn refl refl) E (lkind F (kind A)) (lsz F (size A)) b (b + 1) (b + 2) (b + 3)
                                   cl<b2 k<b2 ev<b2 pr<b2))
     (segok-++ (segok-weaken b≤b2 (segok-SB _ I₂-all))
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
    I₁-all : All (SB b) (cata-br-I₁ (kind A) (size A) F n1 l1)
    I₁-all =
      ++⁺ (nn refl refl ∷ ss refl q3 (λ _ ()) refl ∷
           nn refl refl ∷ ss refl q6 (λ _ ()) refl ∷ nn refl refl ∷
           nn refl refl ∷ nn refl refl ∷
           ss refl q6 (λ _ ()) refl ∷ ss refl q1 (λ _ ()) refl ∷
           ss refl q6 (λ _ ()) refl ∷ ss refl q2 (λ _ ()) refl ∷
           ss refl q6 (λ _ ()) refl ∷ ss refl q0 (λ _ ()) refl ∷
           ss refl q3 (λ _ ()) refl ∷ [])
      (++⁺ (push2-below n1 (n1 + 4) (n1 + 5) b q0 q4 q5)
      (++⁺ (nn refl refl ∷ ss refl q0 (λ _ ()) refl ∷ nn refl refl ∷
            nn refl refl ∷ nn refl refl ∷ ss refl q0 (λ _ ()) refl ∷
            nn refl refl ∷ nn refl refl ∷ ss refl q3 (λ _ ()) refl ∷
            ss refl q3 (λ _ ()) refl ∷ [])
      (++⁺ (push2-below (suc n1) (n1 + 4) (n1 + 5) b q1 q4 q5)
      (++⁺ (ss refl q3 (λ _ ()) refl ∷ nn refl refl ∷ [])
      (++⁺ (visit-below F n1 (n1 + 4) (n1 + 5) (n1 + 7) (l1 + 4) b q0 q4 q5 walk-room)
      (++⁺ (nn refl refl ∷ nn refl refl ∷ [])
      (++⁺ (nn refl refl ∷ ss refl q1 (λ _ ()) refl ∷ nn refl refl ∷
            nn refl refl ∷ nn refl refl ∷ ss refl q1 (λ _ ()) refl ∷
            nn refl refl ∷ nn refl refl ∷ [])
      (++⁺ (rebuild-below (kind A) (size A) F (n1 + 2) (n1 + 4) (n1 + 5) (n1 + 7) (l1 + 4 + lsize F) b q2 walk-room)
           (nn refl refl ∷ [])))))))))
    I₂-all : All (SB b) (cata-br-I₂ n1 l1)
    I₂-all = ++⁺ (push2-below (n1 + 2) (n1 + 4) (n1 + 5) b q2 q4 q5)
                 (nn refl refl ∷ nn refl refl ∷
                  ss refl q2 (λ _ ()) refl ∷ nn refl refl ∷ nn refl refl ∷ [])



-- D099 / C1: `strat-const` no longer passes the algebra's witness through —
-- it emits a called body like the others, so it has a skeleton (setup + call)
-- and its own witness.
-- D366: `In`'s box stashes the layer in slot `n` and reads it back; `out-μ`
-- touches no slot.
in-below : ∀ (r : MuRep) kd L (n : ℕ) → SegOK (in-next r kd n) (in-trace r kd L n)
in-below mu-box  kd L n = segok-idle _ refl
  (sb-none refl ∷ sb-slot refl ≤-refl (λ _ ()) ∷ sb-none refl ∷ sb-none refl ∷
   sb-slot refl ≤-refl (λ _ ()) ∷ sb-none refl ∷ sb-none refl ∷ [])
in-below mu-unit kd L n = segok-idle _ refl (sb-none refl ∷ [])
in-below mu-ptr  word L n = segok-idle _ refl (sb-none refl ∷ [])
-- D393 (β1): the copy into a fresh node, two slots
in-below mu-ptr  flat L n =
  segok-SB _
    (nn refl refl ∷ ss refl n< (λ _ ()) refl ∷ nn refl refl ∷ ss refl ≤-refl (λ _ ()) refl ∷
     ++⁺ (put-SB L n (suc n) 0 n< ≤-refl) (ss refl ≤-refl (λ _ ()) refl ∷ []))
  where n< : n < suc (suc n)
        n< = m≤n⇒m≤1+n ≤-refl

out-below : ∀ (r : MuRep) (n : ℕ) → SegOK n (out-trace r)
out-below mu-box  n = segok-idle _ refl (sb-none refl ∷ [])
out-below mu-unit n = segok-idle _ refl (sb-none refl ∷ [])
out-below mu-ptr  n = segok-idle _ refl (sb-none refl ∷ [])

cata-slots-below : ∀ (E A : IRTy) (G : Fun 0) (st : CataStrategy) (bb n1 l1 : ℕ) (at : AbstractTrace)
                 → SegOK bb at
                 → SegOK (cata-budget-of (cata-dispatch E A G st bb n1 l1 at))
                         (cata-trace-of (cata-dispatch E A G st bb n1 l1 at))
cata-slots-below E A G strat-const         bb n1 l1 at bok = cata-const-below E A G bb n1 l1 at bok
cata-slots-below E A G strat-box           bb n1 l1 at bok = cata-box-below E A G bb n1 l1 at bok
cata-slots-below E A G (strat-branching F) bb n1 l1 at bok = cata-branching-below E A G F bb n1 l1 at bok

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

resuspend-mono : ∀ (H : IRFunctor) (E A : IRTy) (n l : ℕ) (lbl : LabelId) (env : ℕ) {F} (wf : WellFormedFI F)
               → n ≤ proj₁ (resuspend-layer H E A n l lbl env wf)
resuspend-mono H E A n l lbl env (wf-K _) = ≤-refl
resuspend-mono H E A n l lbl env wf-Id    = m≤n⇒m≤1+n (m≤n⇒m≤1+n (m≤n⇒m≤1+n (m≤n⇒m≤1+n ≤-refl)))
-- plan 0.123 B.4 α: four slots (`src`, `dst`, two parts) before the parts
resuspend-mono H E A n l lbl env (wf-Prod wfF wfG) =
  ≤-trans (m≤n⇒m≤1+n (m≤n⇒m≤1+n (m≤n⇒m≤1+n (m≤n⇒m≤1+n ≤-refl))))
    (≤-trans (resuspend-mono H E A (suc (suc (suc (suc n)))) l lbl env wfF)
             (resuspend-mono H E A (proj₁ (resuspend-layer H E A (suc (suc (suc (suc n)))) l lbl env wfF))
                             (proj₁ (proj₂ (resuspend-layer H E A (suc (suc (suc (suc n)))) l lbl env wfF)))
                             lbl env wfG))
resuspend-mono H E A n l lbl env (wf-Sum wfF wfG) =
  ≤-trans (m≤n⇒m≤1+n (m≤n⇒m≤1+n (m≤n⇒m≤1+n ≤-refl)))
    (≤-trans (resuspend-mono H E A (suc (suc (suc n))) (suc (suc l)) lbl env wfF)
             (resuspend-mono H E A (proj₁ (resuspend-layer H E A (suc (suc (suc n))) (suc (suc l)) lbl env wfF))
                             (proj₁ (proj₂ (resuspend-layer H E A (suc (suc (suc n))) (suc (suc l)) lbl env wfF)))
                             lbl env wfG))

resuspend-below : ∀ (H : IRFunctor) (E A : IRTy) (n l : ℕ) (lbl : LabelId) (env : ℕ) {F} (wf : WellFormedFI F)
                → env < n
                → SegOK (proj₁ (resuspend-layer H E A n l lbl env wf))
                        (proj₂ (proj₂ (resuspend-layer H E A n l lbl env wf)))
resuspend-below H E A n l lbl env (wf-K _) e<n = segok-idle _ refl []
-- Budget `n + 4`: the seed `a'`, the environment's form, the seed pair `q`, and
-- the suspension; the environment pair is READ at `env < n`.
resuspend-below H E A n l lbl env wf-Id e<n =
  segok-SB _
    (++⁺ (ss refl n0 (λ _ ()) refl ∷ ss refl e<B (λ _ ()) refl ∷ [])
    (++⁺ (get-SB E 0)
    (++⁺ (ss refl n1 (λ _ ()) refl ∷ nn refl refl ∷ ss refl n2 (λ _ ()) refl ∷ [])
    (++⁺ (put-SB E (suc n) (suc (suc n)) 0 n1 n2)
    (++⁺ (put-SB A n (suc (suc n)) _ n0 n2)
         (nn refl refl ∷ ss refl ≤-refl (λ _ ()) refl ∷ nn refl refl ∷ ss refl n2 (λ _ ()) refl ∷
          nn refl refl ∷ nn refl refl ∷ nn refl refl ∷ ss refl ≤-refl (λ _ ()) refl ∷ []))))))
  where
    n2 : suc (suc n) < suc (suc (suc (suc n)))
    n2 = m≤n⇒m≤1+n ≤-refl
    n1 : suc n < suc (suc (suc (suc n)))
    n1 = m≤n⇒m≤1+n (m≤n⇒m≤1+n ≤-refl)
    n0 : n < suc (suc (suc (suc n)))
    n0 = m≤n⇒m≤1+n (m≤n⇒m≤1+n (m≤n⇒m≤1+n ≤-refl))
    e<B : env < suc (suc (suc (suc n)))
    e<B = ≤-trans e<n (m≤n⇒m≤1+n (m≤n⇒m≤1+n (m≤n⇒m≤1+n (m≤n⇒m≤1+n ≤-refl))))
-- plan 0.123 B.4 α: four stashes per product level — source, destination and
-- the two transformed parts — so the parts start at `n + 4`.
resuspend-below H E A n l lbl env (wf-Prod {F} {G} wfF wfG) e<n =
  segok-++ (segok-SB _ (ss refl n<B (λ _ ()) refl ∷ ss refl n<B (λ _ ()) refl ∷ []))
  (segok-++ (segok-get (⟦ F ⟧TI A) 0)
  (segok-++ (segok-weaken mid (resuspend-below H E A (suc (suc (suc (suc n)))) l lbl env wfF e<4n))
  (segok-++ (segok-SB _ (ss refl t1<B (λ _ ()) refl ∷ ss refl n<B (λ _ ()) refl ∷ []))
  (segok-++ (segok-get (⟦ G ⟧TI A) _)
  (segok-++ (resuspend-below H E A n2 l2 lbl env wfG e<n2)
            (segok-SB _
              (++⁺ (ss refl base (λ _ ()) refl ∷ nn refl refl ∷ ss refl d<B (λ _ ()) refl ∷ [])
              (++⁺ (put-SB (⟦ F ⟧TI (ν-type H)) (suc (suc n)) (suc n) 0 t1<B d<B)
              (++⁺ (put-SB (⟦ G ⟧TI (ν-type H)) (suc (suc (suc n))) (suc n) _ base d<B)
                   (ss refl d<B (λ _ ()) refl ∷ []))))))))))
  where
    n2 = proj₁ (resuspend-layer H E A (suc (suc (suc (suc n)))) l lbl env wfF)
    l2 = proj₁ (proj₂ (resuspend-layer H E A (suc (suc (suc (suc n)))) l lbl env wfF))
    B  = proj₁ (resuspend-layer H E A n2 l2 lbl env wfG)
    mid : n2 ≤ B
    mid = resuspend-mono H E A n2 l2 lbl env wfG
    base : suc (suc (suc (suc n))) ≤ B
    base = ≤-trans (resuspend-mono H E A (suc (suc (suc (suc n)))) l lbl env wfF) mid
    t1<B : suc (suc (suc n)) ≤ B
    t1<B = ≤-trans (m≤n⇒m≤1+n ≤-refl) base
    d<B : suc (suc n) ≤ B
    d<B = ≤-trans (m≤n⇒m≤1+n ≤-refl) t1<B
    n<B : suc n ≤ B
    n<B = ≤-trans (m≤n⇒m≤1+n ≤-refl) d<B
    e<4n : env < suc (suc (suc (suc n)))
    e<4n = ≤-trans e<n (m≤n⇒m≤1+n (m≤n⇒m≤1+n (m≤n⇒m≤1+n (m≤n⇒m≤1+n ≤-refl))))
    e<n2 : env < n2
    e<n2 = ≤-trans e<4n (resuspend-mono H E A (suc (suc (suc (suc n)))) l lbl env wfF)
resuspend-below H E A n l lbl env (wf-Sum {F} {G} wfF wfG) e<n =
  segok-pre (store-at-slot n ∷ restore-input n ∷
             instr-ctrl (c-branch-tag-zero (ℓ o l)) ∷ []) refl
    (sb-slot refl n<B (λ _ ()) ∷ sb-slot refl n<B (λ _ ()) ∷ sb-none refl ∷ [])
    (segok-++ (arm G (resuspend-below H E A n2 l2 lbl env wfG e<n2) {sz′ = sz} {c = sz ∸ suc (size (⟦ G ⟧TI (ν-type H)))})
      (segok-pre (instr-ctrl (c-jmp (ℓ o (suc l))) ∷
                  instr-ctrl (c-label (ℓ o l)) ∷ []) refl
        (sb-none refl ∷ sb-none refl ∷ [])
        (segok-++ (arm F (segok-weaken mid
                            (resuspend-below H E A (suc (suc (suc n))) (suc (suc l)) lbl env wfF e<3n)) {sz′ = sz} {c = sz ∸ suc (size (⟦ F ⟧TI (ν-type H)))})
          (segok-idle _ refl (sb-none refl ∷ [])))))
  where
    sz = size (⟦ F ⟧TI (ν-type H) +ᵀ ⟦ G ⟧TI (ν-type H))
    n2 = proj₁ (resuspend-layer H E A (suc (suc (suc n))) (suc (suc l)) lbl env wfF)
    l2 = proj₁ (proj₂ (resuspend-layer H E A (suc (suc (suc n))) (suc (suc l)) lbl env wfF))
    B  = proj₁ (resuspend-layer H E A n2 l2 lbl env wfG)
    mid : n2 ≤ B
    mid = resuspend-mono H E A n2 l2 lbl env wfG
    base : suc (suc (suc n)) ≤ B
    base = ≤-trans (resuspend-mono H E A (suc (suc (suc n))) (suc (suc l)) lbl env wfF) mid
    sn<B : suc (suc n) ≤ B
    sn<B = ≤-trans (m≤n⇒m≤1+n ≤-refl) base
    n<B : suc n ≤ B
    n<B = ≤-trans (m≤n⇒m≤1+n (m≤n⇒m≤1+n ≤-refl)) base
    e<3n : env < suc (suc (suc n))
    e<3n = ≤-trans e<n (m≤n⇒m≤1+n (m≤n⇒m≤1+n (m≤n⇒m≤1+n ≤-refl)))
    e<n2 : env < n2
    e<n2 = ≤-trans e<3n (resuspend-mono H E A (suc (suc (suc n))) (suc (suc l)) lbl env wfF)
    -- plan 0.123 B.4 α: the payload read at word 1, transformed, put at word 1
    arm : ∀ (P : IRFunctor) {t} → SegOK B t → ∀ {tag sz′ c}
        → SegOK B ((restore-input n ∷ []) ++ get (⟦ P ⟧TI A) 1 ++ t ++
                   (store-at-slot (suc (suc n)) ∷ instr-alloc-heap (2 ⊔ sz′) ∷
                    store-at-slot (suc n) ∷ mov-to-input ∷
                    instr-load-tag-lit tag ∷ store-at 0 ∷ []) ++
                   fill (suc (size (⟦ P ⟧TI (ν-type H)))) c ++
                   put (⟦ P ⟧TI (ν-type H)) (suc (suc n)) (suc n) 1 ++
                   (load-from-slot (suc n) ∷ []))
    arm P ok {c = c} =
      segok-++ (segok-SB _ (ss refl n<B (λ _ ()) refl ∷ []))
      (segok-++ (segok-get (⟦ P ⟧TI A) 1)
      (segok-++ ok
        (segok-SB _
          (++⁺ (ss refl base (λ _ ()) refl ∷ nn refl refl ∷ ss refl sn<B (λ _ ()) refl ∷
                nn refl refl ∷ nn refl refl ∷ nn refl refl ∷ [])
          (++⁺ (fill-SB _ c)
               (++⁺ (put-SB (⟦ P ⟧TI (ν-type H)) (suc (suc n)) (suc n) 1 base sn<B) (ss refl sn<B (λ _ ()) refl ∷ [])))))))

sigop-below : ∀ {A B} (si : SigOpInfo A B) (n : ℕ) (m : Maybe CmpOp)
            → SegOK (sigop-budget n m) (sigop-code si n m)
sigop-below si n nothing  = segok-idle _ refl (sb-none refl ∷ [])
sigop-below si n (just _) = segok-idle _ refl
  (sb-none refl ∷ sb-none refl ∷ sb-slot refl (m≤n⇒m≤1+n ≤-refl) (λ _ ()) ∷ sb-none refl ∷
  sb-slot refl ≤-refl (λ _ ()) ∷ sb-none refl ∷ sb-slot refl (m≤n⇒m≤1+n ≤-refl) (λ _ ()) ∷
  sb-none refl ∷ sb-slot refl ≤-refl (λ _ ()) ∷ [])

-- plan 0.123 B.4 α: an injection — the payload and the block in slots `n`,
-- `suc n`, the payload `put` at word 1 after the tag
inj-below : ∀ (t : ℕ) (P S : IRTy) (n : ℕ) → SegOK (suc (suc n)) (inj-trace t P S n)
inj-below t P S n =
  segok-SB _
    (nn refl refl ∷ ss refl n< (λ _ ()) refl ∷ nn refl refl ∷ ss refl ≤-refl (λ _ ()) refl ∷
     nn refl refl ∷ nn refl refl ∷ nn refl refl ∷
     ++⁺ (fill-SB _ (size S ∸ suc (size P))) (++⁺ (put-SB P n (suc n) 1 n< ≤-refl) (ss refl ≤-refl (λ _ ()) refl ∷ [])))
  where n< : n < suc (suc n)
        n< = m≤n⇒m≤1+n ≤-refl

slots-below : ∀ {A B} (ir : IR A B) (n l : ℕ)
            → SegOK (budget-of (ir-to-trace' n l ir)) (trace-of (ir-to-trace' n l ir))
slots-below id       n l = segok-idle _ refl (sb-none refl ∷ [])
slots-below (fst {A} {B}) n l = segok-get A 0
slots-below (snd {A} {B}) n l = segok-get B (size A)
slots-below terminal n l = segok-idle _ refl []
slots-below initial  n l = segok-idle _ refl (sb-none refl ∷ [])
slots-below (g ∘ f)  n l =
  segok-++ (segok-weaken (frontier-mono g _ _) (slots-below f n l))
      (segok-pre _ refl (sb-none refl ∷ []) (slots-below g _ _))
-- Stage G: the stack-shape clause that stood here collapsed onto this
-- same LHS when the pair's mode was dropped, and shadowed the heap one.
slots-below (⟨_,_⟩ {A} {B} {C} f g) n l =
  segok-pre _ refl
    (sb-none refl ∷ sb-slot refl (≤-trans (m≤n⇒m≤1+n (m≤n⇒m≤1+n (m≤n⇒m≤1+n ≤-refl))) h) (λ _ ()) ∷ [])
  (segok-++ (segok-weaken (frontier-mono g _ _) (slots-below f _ l))
      (segok-pre _ refl
        (sb-slot refl (≤-trans (m≤n⇒m≤1+n (m≤n⇒m≤1+n ≤-refl)) h) (λ _ ()) ∷
         sb-slot refl (≤-trans (m≤n⇒m≤1+n (m≤n⇒m≤1+n (m≤n⇒m≤1+n ≤-refl))) h) (λ _ ()) ∷ [])
       (segok-++ (slots-below g _ _)
           (segok-SB _
            (++⁺ (ss refl (≤-trans (m≤n⇒m≤1+n ≤-refl) h) (λ _ ()) refl ∷
                  nn refl refl ∷
                  ss refl h (λ _ ()) refl ∷ [])
            (++⁺ (put-SB B (suc n) (suc (suc (suc n))) 0 f< h)
            (++⁺ (put-SB C (suc (suc n)) (suc (suc (suc n))) _ (≤-trans (m≤n⇒m≤1+n ≤-refl) h) h)
                 (ss refl h (λ _ ()) refl ∷ []))))))))
  where h : suc (suc (suc (suc n))) ≤ budget-of (ir-to-trace' n l (⟨_,_⟩ {A} {B} {C} f g))
        h = ≤-trans (frontier-mono f _ l) (frontier-mono g _ _)
        f< : suc n < budget-of (ir-to-trace' n l (⟨_,_⟩ {A} {B} {C} f g))
        f< = ≤-trans (m≤n⇒m≤1+n (m≤n⇒m≤1+n ≤-refl)) h
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
-- D380: the call pair `[env-word, arg…]`, the argument `put` at word 1.
slots-below (apply {A} {B}) n l =
  segok-++ (segok-get A 1)
    (segok-SB _
      (++⁺ (ss refl a< (λ _ ()) refl ∷ nn refl refl ∷ nn refl refl ∷ nn refl refl ∷ nn refl refl ∷
            ss refl e< (λ _ ()) refl ∷ nn refl refl ∷ ss refl ≤-refl (λ _ ()) refl ∷ nn refl refl ∷
            ss refl e< (λ _ ()) refl ∷ nn refl refl ∷ [])
      (++⁺ (put-SB A n (suc (suc n)) 1 a< ≤-refl)
           (ss refl ≤-refl (λ _ ()) refl ∷ nn refl refl ∷ nn refl refl ∷ []))))
  where a< : n < suc (suc (suc n))
        a< = m≤n⇒m≤1+n (m≤n⇒m≤1+n ≤-refl)
        e< : suc n < suc (suc (suc n))
        e< = m≤n⇒m≤1+n ≤-refl
slots-below (inl {A} {B}) n l = inj-below 0 A (A +ᵀ B) n
slots-below (inr {A} {B}) n l = inj-below 1 B (A +ᵀ B) n
-- item 6: case is FLAT CONTROL — the branches are main-trace splices, bounded
-- by their own inductions (f weakened through g's frontier, like `∘`).
slots-below (case {A} {B} f g) n l =
  segok-pre _ refl (sb-none refl ∷ [])
   (segok-++ (segok-get B 1)
    (segok-pre _ refl (sb-none refl ∷ [])
      (segok-++ (slots-below g _ _)
           (segok-pre _ refl (sb-none refl ∷ sb-none refl ∷ [])
            (segok-++ (segok-get A 1)
             (segok-pre _ refl (sb-none refl ∷ [])
                (segok-++ (segok-weaken (frontier-mono g _ _) (slots-below f n (suc (suc l))))
                     (segok-idle _ refl (sb-none refl ∷ [])))))))))
slots-below (In {F} _)    n l = in-below (mu-rep F) _ _ n
slots-below (out-μ {F} _) n l = out-below (mu-rep F) n
-- C1: the algebra is generated at frontier 0 — its slots are its own frame's,
-- so its witness is taken there and `segok-thunk` (inside `cata-body-below`)
-- carries it across the frame change.
slots-below (Cata {F} _ {E} {A} alg) n l =
  cata-slots-below E A ⌈ F ⌉F (cata-strategy ⌈ F ⌉F) _ _ _ _ (slots-below alg 0 l)
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
-- the loop: the environment stash, the round (its own frontier is the loop's
-- budget), then the branch and the next pair through the two stashes.
-- plan 0.123 B.4 α: the environment's form kept, the next pair `put` together.
slots-below (Iter {E} {A} {B} b) n l =
  segok-++ (segok-get E 0)
   (segok-pre _ refl (sb-slot refl e< (λ _ ()) ∷ sb-none refl ∷ [])
    (segok-++ (slots-below b _ _)
     (segok-pre _ refl (sb-none refl ∷ sb-none refl ∷ [])
      (segok-++ (segok-get A 1)
       (segok-SB _
          (++⁺ (ss refl s2< (λ _ ()) refl ∷ nn refl refl ∷ ss refl h (λ _ ()) refl ∷ [])
          (++⁺ (put-SB E (suc n) (suc (suc (suc n))) 0 e< h)
          (++⁺ (put-SB A (suc (suc n)) (suc (suc (suc n))) _ s2< h)
          (++⁺ (ss refl h (λ _ ()) refl ∷ nn refl refl ∷ nn refl refl ∷ nn refl refl ∷ [])
               (get-SB B 1))))))))))
  where h : suc (suc (suc (suc n))) ≤ budget-of (ir-to-trace' n l (Iter {E} {A} {B} b))
        h = frontier-mono b _ _
        s2< : suc (suc (suc n)) ≤ budget-of (ir-to-trace' n l (Iter {E} {A} {B} b))
        s2< = ≤-trans (m≤n⇒m≤1+n ≤-refl) h
        e< : suc (suc n) ≤ budget-of (ir-to-trace' n l (Iter {E} {A} {B} b))
        e< = ≤-trans (m≤n⇒m≤1+n ≤-refl) s2<
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
-- D380: a closure body's entry. A word environment adds nothing; a flat one
-- rebuilds the input in slots 0–3, and the body's own slots start at 4.
env-prologue-below : ∀ (E A : IRTy) → SegOK 4 (env-prologue E A)
env-prologue-below E A =
  segok-SB _
    (nn refl refl ∷ ss refl p0 (λ _ ()) refl ∷ nn refl refl ∷ ss refl p1 (λ _ ()) refl ∷
     ss refl p0 (λ _ ()) refl ∷
     ++⁺ (get-SB A 1)
         (ss refl p2 (λ _ ()) refl ∷ nn refl refl ∷ ss refl ≤-refl (λ _ ()) refl ∷
          ++⁺ (put-SB E 1 3 0 p1 ≤-refl)
              (++⁺ (put-SB A 2 3 _ p2 ≤-refl) (ss refl ≤-refl (λ _ ()) refl ∷ nn refl refl ∷ []))))
  where p0 : 0 < 4
        p0 = s≤s z≤n
        p1 : 1 < 4
        p1 = s≤s (s≤s z≤n)
        p2 : 2 < 4
        p2 = s≤s (s≤s (s≤s z≤n))

curry-body-below : ∀ (kd : Kind) (E A : IRTy) {X Y} (b : IR X Y) (l : ℕ)
                 → SegOK (budget-of (ir-to-trace' (proj₁ (env-entry kd E A)) l b))
                         (proj₂ (env-entry kd E A) ++ trace-of (ir-to-trace' (proj₁ (env-entry kd E A)) l b))
curry-body-below word E A b l = slots-below b 0 l
curry-body-below flat E A b l =
  segok-++ (segok-weaken (frontier-mono b 4 l) (env-prologue-below E A)) (slots-below b 4 l)

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
blocks-below (curry {E} {A} b) n l = curry-body-below (kind E) E A b (suc (suc l))
                                     ∷ blocks-below b _ (suc (suc l))
blocks-below apply               n l = []
blocks-below inl                 n l = []
blocks-below inr                 n l = []
blocks-below (case f g)          n l = ++⁺ (blocks-below f n (suc (suc l)))
                                           (blocks-below g _ _)
blocks-below (In _)            n l = []
blocks-below (out-μ _)           n l = []
blocks-below (Cata {F} _ alg)    n l = blocks-below alg 0 l
blocks-below (Iter b)            n l = blocks-below b _ _
blocks-below (Out _)             n l = []
blocks-below (in-ν _)          n l = segok-idle _ refl (sb-none refl ∷ []) ∷ []
-- D199: the block is `coalg ++ re-suspension`, and the budget is the pass's
-- final frontier — so the coalgebra's own witness weakens up to it.
-- D273: behind the prologue that keeps the seed pair in slot 0.
blocks-below (Ana {F} wf {E} {A} c) n l =
  segok-pre (mov-to-output ∷ store-at-slot 0 ∷ []) refl
    (sb-none refl ∷ sb-slot refl (≤-trans 0<cb mono) (λ _ ()) ∷ [])
    (segok-++ (segok-weaken mono (slots-below c 1 (suc l)))
              (resuspend-below F E A cb (proj₁ (proj₂ (ir-to-trace' 1 (suc l) c))) (ℓ o l) 0 wf 0<cb))
    ∷ blocks-below c 1 (suc l)
  where
    cb = proj₁ (ir-to-trace' 1 (suc l) c)
    0<cb : 0 < cb
    0<cb = frontier-mono c 1 (suc l)
    mono = resuspend-mono F E A cb (proj₁ (proj₂ (ir-to-trace' 1 (suc l) c))) (ℓ o l) 0 wf
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

-- THE OUTERMOST UNIT, linked with the program's LEAVE (`link-top`, D320):
-- exactly `ir-slots-below-under`, except that the terminator is a
-- segment-idle instruction (`c-leave`) instead of `c-ret`'s pop — so the unit
-- leaves the segment where it began.
ir-slots-below-top : ∀ {A B} (ir : IR A B) (sv : List ℕ)
                   → AllSeg (mkSeg (ir-stack-budget ir) sv) (link-top (ir-to-unit ir))
ir-slots-below-top ir sv =
  allseg-++ (ok-all (slots-below ir 0 0))
    (subst (λ z → AllSeg z (instr-ctrl c-leave ∷
                            blocks-layout (bodies-of (ir-to-trace' 0 0 ir))))
           (sym (ok-neu (slots-below ir 0 0) (mkSeg (ir-stack-budget ir) sv)))
           (sb-none refl ∷ ok-all (segok-blocks _ (blocks-below ir 0 0))))

ir-seg-fold-top : ∀ {A B} (ir : IR A B) (sv : List ℕ)
                → seg-fold (link-top (ir-to-unit ir)) (mkSeg (ir-stack-budget ir) sv)
                  ≡ mkSeg (ir-stack-budget ir) sv
ir-seg-fold-top ir sv =
  trans (seg-fold-++ (trace-of (ir-to-trace' 0 0 ir))
                     (instr-ctrl c-leave ∷
                      blocks-layout (bodies-of (ir-to-trace' 0 0 ir)))
                     (mkSeg (ir-stack-budget ir) sv))
        (trans (cong (seg-fold (instr-ctrl c-leave ∷
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
