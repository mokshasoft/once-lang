-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.AllocMin   (Plan 0.54 rung D, item 5)
--
-- EVERY EMITTED ALLOCATION HAS AT LEAST TWO WORDS: each `instr-alloc-heap n` in
-- an emitted trace has `n ≥ 2`. plan 0.123 B.4 α: a flat block is sized by its
-- type, `2 ⊔ size …` (the pair, the sum, the call pair, the cata's argument
-- pair and layers, the re-suspended layers), and the fixed two-word nodes (the
-- closure and ν records, the stacks, the box) are literally `2`.
--
-- This is the emitter half of the pointer-bounds invariant
-- (`Once.CCC.Machine.FlatPtrBounds`): the fresh pointer an alloc hands out is
-- the start of a block of at least one cell (two is more than it needs; the
-- floor of 2 is kept so a 0-word value still has a block to be addressed in).
--
-- Since item 6 (case compiles to FLAT control) there is no nesting anywhere:
-- every alloc site of every branch is in the main trace, so this `All` covers
-- the WHOLE emitted program. Structure: the induction of `FrameFreeTrace`
-- (`All P` over `trace-of (ir-to-trace' n l ir)`, `++⁺` at every splice); the
-- layout code by `FlatLayout`'s `All` lemmas (it allocates nothing).
------------------------------------------------------------------------

-- Plan 0.63 (D089): parameterised by the DEFINITION'S identity, which keys
-- its labels. `o` is constant for a whole definition, so it belongs on the
-- module rather than on every lemma — which is exactly what keeps the
-- statements below UNCHANGED under D089: `IRToTrace` is imported APPLIED,
-- so each `ir-to-trace' n l ir` reads as it always did.
open import Once.Spec.Name using (CanonicalName)

module Once.CCC.Codegen.AllocMin (o : CanonicalName) where

open import Data.Nat using (ℕ; suc; _+_; _≤_; s≤s; z≤n; _*_; _⊔_)
open import Data.Nat.Properties using (m≤m⊔n)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.All.Properties using (++⁺)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; subst; sym)

open import Once.IR using (IR; id; _∘_; ⟨_,_⟩; fst; snd; inl; inr; case; terminal; initial; curry; apply; In; out-μ; Cata; Out; in-ν; Ana; Iter; SigOp; Call; const)
open import Once.IRTy using (IRTy; IRFunctor; ⟦_⟧TI; ν-type; fits-int; fits-float; ⌈_⌉F; WellFormedFI; wf-K; wf-Id; wf-Sum; wf-Prod) renaming (_+_ to _+ᵀ_; _*_ to _*ᵀ_)
open import Once.CCC.Codegen.Size using (size)
open import Once.Spec.Type using (Fun; K; Id; _⊕_; _⊗_)
open import Once.CCC.Label using (ℓ)
open import Once.CCC.Machine.MuRep using (MuRep; mu-box; mu-unit; mu-ptr; mu-rep)
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.SMCore using (AbstractInstr; AbstractTrace; instr-alloc-heap
  ; blocks-layout; blocks-layout-++; LabelId; link-top)
import Once.CCC.Machine.SMCore as SM
open import Once.CCC.Machine.Flat using (module FlatMachine)
open import Once.CCC.Codegen.FlatLayout
  using (Kind; word; flat; kind; put; put-k; get; get-k; fill; put-All; put-k-All; get-All; get-k-All; fill-All; lkind; lsz)
open import Once.SigOp.Info using (SigOpInfo; module SigOpInfo)
open SigOpInfo using (sem)
open import Once.Arith.CmpOp using (CmpOp)
open import Once.Arith.SigOp.Compare using (cmp-of)
open import Once.CCC.Codegen.IRToTrace o using
  (sigop-code; ir-to-trace'; ir-to-trace; ir-to-trace-at-frontier; ir-to-trace-lab; ir-to-unit; strat-const; strat-box; strat-branching; cata-strategy; cata-dispatch; cata-trace-branching; cata-trace-box; cata-call-box; in-trace; out-trace; push2; pop2; wrap-sum; visit-walk; rebuild-walk; lsize; cata-body; cata-call-setup; cata-call; cata-call-from; cata-trace-const; fsize; resuspend-layer; env-entry; env-prologue; inj-trace)
open import Once.CCC.Codegen.FrameFreeTrace o using (trace-of; cata-trace-of)

AllocMinI : AbstractInstr → Set
AllocMinI (instr-alloc-heap n) = 2 ≤ n
{-# CATCHALL #-}
AllocMinI _                    = ⊤

AllocMinTrace : AbstractTrace → Set
AllocMinTrace = All AllocMinI

am2 : 2 ≤ 2
am2 = s≤s (s≤s z≤n)

-- plan 0.123 B.4 α: a flat block, `2 ⊔ size …`
am⊔ : ∀ n → 2 ≤ 2 ⊔ n
am⊔ n = m≤m⊔n 2 n

------------------------------------------------------------------------
-- plan 0.123 B.4 α: the layout code allocates nothing.
------------------------------------------------------------------------
put-am : ∀ X s b o′ → AllocMinTrace (put X s b o′)
put-am X s b o′ = put-All {AllocMinI} X s b o′ tt tt tt (λ _ → tt) (λ _ → tt)

put-k-am : ∀ kd n s b o′ → AllocMinTrace (put-k kd n s b o′)
put-k-am kd n s b o′ = put-k-All {AllocMinI} kd n s b o′ tt tt tt (λ _ → tt) (λ _ → tt)

get-am : ∀ X k → AllocMinTrace (get X k)
get-am X k = get-All {AllocMinI} X k (λ _ → tt) (λ _ → tt) tt

get-k-am : ∀ kd n k → AllocMinTrace (get-k kd n k)
get-k-am kd n k = get-k-All {AllocMinI} kd n k (λ _ → tt) (λ _ → tt) tt

fill-am : ∀ from c → AllocMinTrace (fill from c)
fill-am from c = fill-All {AllocMinI} from c tt (λ _ → tt)

inj-am : ∀ t P S n → AllocMinTrace (inj-trace t P S n)
inj-am t P S n = tt ∷ tt ∷ am⊔ (size S) ∷ tt ∷ tt ∷ tt ∷ tt ∷ ++⁺ (put-am P n (suc n) 1) (++⁺ (fill-am _ _) (tt ∷ []))

-- D380: a closure body's entry
env-entry-am : ∀ kd E A → AllocMinTrace (proj₂ (env-entry kd E A))
env-entry-am word E A = []
env-entry-am flat E A =
  tt ∷ tt ∷ tt ∷ tt ∷ tt ∷
  ++⁺ (get-am A 1)
      (tt ∷ am⊔ (size (E *ᵀ A)) ∷ tt ∷
       ++⁺ (put-am E 1 3 0) (++⁺ (put-am A 2 3 _) (tt ∷ tt ∷ [])))

------------------------------------------------------------------------
-- The heap-linked-stack bricks the cata codegen is built from.
------------------------------------------------------------------------
push2-am : ∀ topSlot tv tb → AllocMinTrace (push2 topSlot tv tb)
push2-am topSlot tv tb = tt ∷ am2 ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ []

pop2-am : ∀ topSlot → AllocMinTrace (pop2 topSlot)
pop2-am topSlot = tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ []

wrap-sum-am : ∀ tag pk ps ss s → AllocMinTrace (wrap-sum tag pk ps ss s)
wrap-sum-am tag pk ps ss s =
  tt ∷ am⊔ ss ∷ tt ∷ tt ∷ tt ∷ tt ∷ ++⁺ (put-k-am pk ps s (suc s) 1) (++⁺ (fill-am _ _) (tt ∷ []))

getμ-am : ∀ (G : Fun 0) k → AllocMinTrace (get-k (lkind G word) (lsz G 1) k)
getμ-am G k = get-k-am (lkind G word) (lsz G 1) k

------------------------------------------------------------------------
-- The compile-time functor walks (Tier 2).
------------------------------------------------------------------------
visit-walk-am : ∀ todoSlot tv tb F s lb → AllocMinTrace (visit-walk todoSlot tv tb F s lb)
visit-walk-am todoSlot tv tb (K _)   s lb = []
visit-walk-am todoSlot tv tb Id      s lb = tt ∷ push2-am todoSlot tv tb
visit-walk-am todoSlot tv tb (F ⊕ G) s lb =
  ++⁺ (tt ∷ [])
      (++⁺ (getμ-am G 1)
      (++⁺ (tt ∷ [])
      (++⁺ (visit-walk-am todoSlot tv tb G (s + 4) (suc (suc lb) + lsize F))
      (++⁺ (tt ∷ tt ∷ [])
      (++⁺ (getμ-am F 1)
      (++⁺ (tt ∷ [])
      (++⁺ (visit-walk-am todoSlot tv tb F (s + 4) (suc (suc lb)))
           (tt ∷ []))))))))
visit-walk-am todoSlot tv tb (F ⊗ G) s lb =
  ++⁺ (tt ∷ tt ∷ [])
      (++⁺ (getμ-am F 0)
      (++⁺ (tt ∷ [])
      (++⁺ (visit-walk-am todoSlot tv tb F (s + 4) lb)
      (++⁺ (tt ∷ [])
      (++⁺ (getμ-am G (lsz F 1))
      (++⁺ (tt ∷ [])
           (visit-walk-am todoSlot tv tb G (s + 4) (lb + lsize F))))))))

rebuild-walk-am : ∀ valSlot tv tb ck cs F s lb → AllocMinTrace (rebuild-walk valSlot tv tb ck cs F s lb)
rebuild-walk-am valSlot tv tb ck cs (K _)   s lb = tt ∷ []
rebuild-walk-am valSlot tv tb ck cs Id      s lb = pop2-am valSlot
rebuild-walk-am valSlot tv tb ck cs (F ⊕ G) s lb =
  ++⁺ (tt ∷ [])
      (++⁺ (getμ-am G 1)
      (++⁺ (tt ∷ [])
      (++⁺ (rebuild-walk-am valSlot tv tb ck cs G (s + 4) (suc (suc lb) + lsize F))
      (++⁺ (wrap-sum-am 1 (lkind G ck) (lsz G cs) (lsz (F ⊕ G) cs) s)
      (++⁺ (tt ∷ tt ∷ [])
      (++⁺ (getμ-am F 1)
      (++⁺ (tt ∷ [])
      (++⁺ (rebuild-walk-am valSlot tv tb ck cs F (s + 4) (suc (suc lb)))
      (++⁺ (wrap-sum-am 0 (lkind F ck) (lsz F cs) (lsz (F ⊕ G) cs) s)
           (tt ∷ []))))))))))
rebuild-walk-am valSlot tv tb ck cs (F ⊗ G) s lb =
  ++⁺ (tt ∷ tt ∷ [])
      (++⁺ (getμ-am G (lsz F 1))
      (++⁺ (tt ∷ [])
      (++⁺ (rebuild-walk-am valSlot tv tb ck cs G (s + 4) (lb + lsize F))
      (++⁺ (tt ∷ tt ∷ [])
      (++⁺ (getμ-am F 0)
      (++⁺ (tt ∷ [])
      (++⁺ (rebuild-walk-am valSlot tv tb ck cs F (s + 4) lb)
      (++⁺ (tt ∷ am⊔ (lsz (F ⊗ G) cs) ∷ tt ∷ [])
      (++⁺ (put-k-am (lkind F ck) (lsz F cs) (suc s) (s + 3) 0)
      (++⁺ (put-k-am (lkind G ck) (lsz G cs) (s + 2) (s + 3) (lsz F cs))
           (tt ∷ [])))))))))))

------------------------------------------------------------------------
-- The three cata strategies.
------------------------------------------------------------------------
cata-body-am : ∀ b e bb at → AllocMinTrace at → AllocMinTrace (cata-body b e bb at)
cata-body-am b e bb at am = tt ∷ tt ∷ ++⁺ am (tt ∷ tt ∷ [])

cata-setup-am : ∀ E cl k ev bl → AllocMinTrace (cata-call-setup E cl k ev bl)
cata-setup-am E cl k ev bl =
  ++⁺ (get-am E 0) (tt ∷ tt ∷ tt ∷ am2 ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ [])

cata-call-from-am : ∀ i0 → AllocMinI i0 → ∀ E lk ls cl k ev pr
                  → AllocMinTrace (cata-call-from i0 E lk ls cl k ev pr)
cata-call-from-am i0 a0 E lk ls cl k ev pr =
  a0 ∷ tt ∷ am⊔ (size E + ls) ∷ tt ∷
  ++⁺ (put-am E ev pr 0)
      (++⁺ (put-k-am lk ls k pr _) (tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ []))

cata-const-am : ∀ E G bb n1 l1 at → AllocMinTrace at
              → AllocMinTrace (cata-trace-of (cata-trace-const E G bb n1 l1 at))
cata-const-am E G bb n1 l1 at am =
  ++⁺ (cata-setup-am E n1 (n1 + 1) (n1 + 2) l1)
      (++⁺ (cata-call-from-am _ tt E (lkind G word) _ n1 (n1 + 1) (n1 + 2) (n1 + 3)) (cata-body-am l1 (l1 + 1) bb at am))

cata-box-am : ∀ E G bb n1 l1 at → AllocMinTrace at
              → AllocMinTrace (cata-trace-of (cata-trace-box E G bb n1 l1 at))
cata-box-am E G bb n1 l1 at am =
  ++⁺ (cata-setup-am E n1 (n1 + 1) (n1 + 2) l1)
      (++⁺ (cata-call-from-am _ tt E (lkind G word) _ n1 (n1 + 1) (n1 + 2) (n1 + 3)) (cata-body-am l1 (l1 + 1) bb at am))

cata-branching-am : ∀ E A F bb n1 l1 at → AllocMinTrace at
                  → AllocMinTrace (cata-trace-of (cata-trace-branching E A F bb n1 l1 at))
cata-branching-am E A F bb n1 l1 at am =
  ++⁺ (cata-setup-am E cl (cl + 1) (cl + 2) bodyL)
      (++⁺ I₁ (++⁺ (cata-call-from-am _ tt E (lkind F (kind A)) _ cl (cl + 1) (cl + 2) (cl + 3))
                   (++⁺ I₂ (cata-body-am bodyL (bodyL + 1) bb at am))))
  where
    bodyL = l1 + 4 + lsize F + lsize F
    cl    = n1 + 7 + (4 * fsize F) + 4
    I₁ : AllocMinTrace _
    I₁ = ++⁺ (tt ∷ tt ∷ am2 ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ [])
             (++⁺ (push2-am n1 (n1 + 4) (n1 + 5))
             (++⁺ (tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ [])
             (++⁺ (push2-am (suc n1) (n1 + 4) (n1 + 5))
             (++⁺ (tt ∷ tt ∷ [])
             (++⁺ (visit-walk-am n1 (n1 + 4) (n1 + 5) F (n1 + 7) (l1 + 4))
             (++⁺ (tt ∷ tt ∷ [])
             (++⁺ (tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ [])
             (++⁺ (rebuild-walk-am (n1 + 2) (n1 + 4) (n1 + 5) (kind A) _ F (n1 + 7) ((l1 + 4) + lsize F))
                  (tt ∷ [])))))))))
    I₂ : AllocMinTrace _
    I₂ = ++⁺ (push2-am (n1 + 2) (n1 + 4) (n1 + 5))
             (++⁺ (tt ∷ tt ∷ []) (tt ∷ tt ∷ tt ∷ []))

cata-dispatch-am : ∀ E A G st bb n1 l1 at → AllocMinTrace at
                 → AllocMinTrace (cata-trace-of (cata-dispatch E A G st bb n1 l1 at))
cata-dispatch-am E A G strat-box           bb n1 l1 at am = cata-box-am E G bb n1 l1 at am
cata-dispatch-am E A G strat-const         bb n1 l1 at am = cata-const-am E G bb n1 l1 at am
cata-dispatch-am E A G (strat-branching F) bb n1 l1 at am = cata-branching-am E A F bb n1 l1 at am

sigop-alloc-min : ∀ {A B} (si : SigOpInfo A B) (n : ℕ) (m : Maybe CmpOp) → AllocMinTrace (sigop-code si n m)
sigop-alloc-min si n nothing  = tt ∷ []
sigop-alloc-min si n (just _) = tt ∷ tt ∷ tt ∷ am2 ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ []

in-am : ∀ (r : MuRep) (n : ℕ) → AllocMinTrace (in-trace r n)
in-am mu-box  n = tt ∷ tt ∷ am2 ∷ tt ∷ tt ∷ tt ∷ tt ∷ []
in-am mu-unit n = am2 ∷ []
in-am mu-ptr  n = tt ∷ []

out-am : ∀ (r : MuRep) → AllocMinTrace (out-trace r)
out-am mu-box  = tt ∷ []
out-am mu-unit = tt ∷ []
out-am mu-ptr  = tt ∷ []

alloc-min-trace' : ∀ {A B} (ir : IR A B) (n l : ℕ)
                 → AllocMinTrace (trace-of (ir-to-trace' n l ir))
alloc-min-trace' id       n l = tt ∷ []
alloc-min-trace' (fst {A} {B}) n l = get-am A 0
alloc-min-trace' (snd {A} {B}) n l = get-am B _
alloc-min-trace' terminal n l = []
alloc-min-trace' initial  n l = tt ∷ []
alloc-min-trace' (g ∘ f)  n l =
  ++⁺ (alloc-min-trace' f _ _) (tt ∷ alloc-min-trace' g _ _)
alloc-min-trace' (⟨_,_⟩ {A} {B} {C} f g) n l =
  tt ∷ tt ∷
  ++⁺ (alloc-min-trace' f _ _)
      (tt ∷ tt ∷
       ++⁺ (alloc-min-trace' g _ _)
           (tt ∷ am⊔ (size (B *ᵀ C)) ∷ tt ∷
            ++⁺ (put-am B _ _ 0) (++⁺ (put-am C _ _ _) (tt ∷ []))))
alloc-min-trace' (curry b)  n l =
  tt ∷ tt ∷ am2 ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ []
alloc-min-trace' (apply {A} {B}) n l =
  ++⁺ (get-am A 1)
      (tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ am⊔ (suc (size A)) ∷ tt ∷ tt ∷ tt ∷ tt ∷
       ++⁺ (put-am A _ _ 1) (tt ∷ tt ∷ tt ∷ []))
alloc-min-trace' (inl {A} {B}) n l = inj-am 0 A (A +ᵀ B) n
alloc-min-trace' (inr {A} {B}) n l = inj-am 1 B (A +ᵀ B) n
alloc-min-trace' (case {A} {B} f g) n l =
  ++⁺ (tt ∷ [])
      (++⁺ (get-am B 1)
      (++⁺ (tt ∷ [])
      (++⁺ (alloc-min-trace' g _ _)
      (++⁺ (tt ∷ tt ∷ [])
      (++⁺ (get-am A 1)
      (++⁺ (tt ∷ [])
      (++⁺ (alloc-min-trace' f _ _) (tt ∷ []))))))))
alloc-min-trace' (Iter {E} {A} {B} b) n l =
  ++⁺ (get-am E 0)
      (++⁺ (tt ∷ tt ∷ [])
      (++⁺ (alloc-min-trace' b _ _)
      (++⁺ (tt ∷ tt ∷ [])
      (++⁺ (get-am A 1)
      (++⁺ (tt ∷ am⊔ (size (E *ᵀ A)) ∷ tt ∷ [])
      (++⁺ (put-am E _ _ 0)
      (++⁺ (put-am A _ _ _)
      (++⁺ (tt ∷ tt ∷ tt ∷ tt ∷ [])
           (get-am B 1)))))))))
alloc-min-trace' (In {F} _) n l = in-am (mu-rep F) n
alloc-min-trace' (out-μ {F} _) n l = out-am (mu-rep F)
alloc-min-trace' (Cata {F} _ {E} {A} alg) n l =
  cata-dispatch-am E A ⌈ F ⌉F (cata-strategy ⌈ F ⌉F) _ _ _ _ (alloc-min-trace' alg 0 l)
alloc-min-trace' (Out _)        n l = tt ∷ tt ∷ tt ∷ tt ∷ []
alloc-min-trace' (in-ν _)     n l =
  tt ∷ tt ∷ am2 ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ []
alloc-min-trace' (Ana _ c)      n l =
  tt ∷ tt ∷ am2 ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ []
alloc-min-trace' (SigOp si)     n l = sigop-alloc-min si n (cmp-of (sem si))
alloc-min-trace' (Call _)      n l = tt ∷ []
alloc-min-trace' (const fits-int _)   n l = tt ∷ []
alloc-min-trace' (const fits-float _) n l = tt ∷ []

------------------------------------------------------------------------
-- D159: …AND EVERY EMITTED BLOCK.
------------------------------------------------------------------------
bodies-of : ℕ × ℕ × AbstractTrace × List (LabelId × ℕ × AbstractTrace)
          → List (LabelId × ℕ × AbstractTrace)
bodies-of (_ , _ , _ , bs) = bs

bud : ℕ × ℕ × AbstractTrace × List (LabelId × ℕ × AbstractTrace) → ℕ
bud (b , _ , _ , _) = b

lab : ℕ × ℕ × AbstractTrace × List (LabelId × ℕ × AbstractTrace) → ℕ
lab (_ , k , _ , _) = k

resuspend-am : ∀ (H : IRFunctor) (E A : IRTy) (n l : ℕ) (lbl : LabelId) (env : ℕ) {F} (wf : WellFormedFI F)
             → AllocMinTrace (proj₂ (proj₂ (resuspend-layer H E A n l lbl env wf)))
resuspend-am H E A n l lbl env (wf-K _) = []
resuspend-am H E A n l lbl env wf-Id =
  ++⁺ (tt ∷ tt ∷ [])
      (++⁺ (get-am E 0)
      (++⁺ (tt ∷ am⊔ (size (E *ᵀ A)) ∷ tt ∷ [])
      (++⁺ (put-am E _ _ 0)
      (++⁺ (put-am A _ _ _)
           (am2 ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ [])))))
resuspend-am H E A n l lbl env (wf-Prod {F} {G} wfF wfG) =
  ++⁺ (tt ∷ tt ∷ [])
      (++⁺ (get-am (⟦ F ⟧TI A) 0)
      (++⁺ (resuspend-am H E A (suc (suc (suc (suc n)))) l lbl env wfF)
      (++⁺ (tt ∷ tt ∷ [])
      (++⁺ (get-am (⟦ G ⟧TI A) _)
      (++⁺ (resuspend-am H E A n2 l2 lbl env wfG)
      (++⁺ (tt ∷ am⊔ (size (⟦ F ⟧TI (ν-type H) *ᵀ ⟦ G ⟧TI (ν-type H))) ∷ tt ∷ [])
      (++⁺ (put-am (⟦ F ⟧TI (ν-type H)) _ _ 0)
      (++⁺ (put-am (⟦ G ⟧TI (ν-type H)) _ _ _)
           (tt ∷ [])))))))))
  where
    n2 = proj₁ (resuspend-layer H E A (suc (suc (suc (suc n)))) l lbl env wfF)
    l2 = proj₁ (proj₂ (resuspend-layer H E A (suc (suc (suc (suc n)))) l lbl env wfF))
resuspend-am H E A n l lbl env (wf-Sum {F} {G} wfF wfG) =
  ++⁺ (tt ∷ tt ∷ tt ∷ [])
      (++⁺ (arm G (resuspend-am H E A n2 l2 lbl env wfG) {sz = sz})
      (++⁺ (tt ∷ tt ∷ [])
      (++⁺ (arm F (resuspend-am H E A (suc (suc (suc n))) (suc (suc l)) lbl env wfF) {sz = sz})
           (tt ∷ []))))
  where
    sz = size (⟦ F ⟧TI (ν-type H) +ᵀ ⟦ G ⟧TI (ν-type H))
    n2 = proj₁ (resuspend-layer H E A (suc (suc (suc n))) (suc (suc l)) lbl env wfF)
    l2 = proj₁ (proj₂ (resuspend-layer H E A (suc (suc (suc n))) (suc (suc l)) lbl env wfF))
    arm : ∀ (P : IRFunctor) {t} → AllocMinTrace t → ∀ {tag sz c}
        → AllocMinTrace ((SM.restore-input n ∷ []) ++ get (⟦ P ⟧TI A) 1 ++ t ++
                         (SM.store-at-slot (suc (suc n)) ∷
                          SM.instr-alloc-heap (2 ⊔ sz) ∷
                          SM.store-at-slot (suc n) ∷
                          SM.mov-to-input ∷
                          SM.instr-load-tag-lit tag ∷
                          SM.store-at 0 ∷ []) ++
                         put (⟦ P ⟧TI (ν-type H)) (suc (suc n)) (suc n) 1 ++
                         fill (suc (size (⟦ P ⟧TI (ν-type H)))) c ++
                         (SM.load-from-slot (suc n) ∷ []))
    arm P am {sz = sz} =
      ++⁺ (tt ∷ [])
          (++⁺ (get-am (⟦ P ⟧TI A) 1)
          (++⁺ am
          (++⁺ (tt ∷ am⊔ sz ∷ tt ∷ tt ∷ tt ∷ tt ∷ [])
          (++⁺ (put-am (⟦ P ⟧TI (ν-type H)) _ _ 1) (++⁺ (fill-am _ _) (tt ∷ []))))))

alloc-min-blocks : ∀ {A B} (ir : IR A B) (n l : ℕ)
                 → AllocMinTrace (blocks-layout (bodies-of (ir-to-trace' n l ir)))
alloc-min-blocks id       n l = []
alloc-min-blocks fst      n l = []
alloc-min-blocks snd      n l = []
alloc-min-blocks terminal n l = []
alloc-min-blocks initial  n l = []
alloc-min-blocks apply    n l = []
alloc-min-blocks inl n l = []
alloc-min-blocks inr n l = []
alloc-min-blocks (In _)   n l = []
alloc-min-blocks (out-μ _)  n l = []
alloc-min-blocks (Out _)    n l = []
alloc-min-blocks (in-ν _) n l = tt ∷ tt ∷ tt ∷ []
alloc-min-blocks (Ana {F} wf {E} {A} c) n l =
  ++⁺ (tt ∷ ++⁺ (tt ∷ tt ∷ (++⁺ (alloc-min-trace' c 1 (suc l))
                     (resuspend-am F E A (proj₁ (ir-to-trace' 1 (suc l) c))
                                   (proj₁ (proj₂ (ir-to-trace' 1 (suc l) c)))
                                   (ℓ o l) 0 wf)))
                (tt ∷ []))
      (alloc-min-blocks c 1 (suc l))
alloc-min-blocks (SigOp _)      n l = []
alloc-min-blocks (Call _)      n l = []
alloc-min-blocks (const fits-int _)   n l = []
alloc-min-blocks (const fits-float _) n l = []
-- D380: the body starts with its environment's entry.
alloc-min-blocks (curry {E} {A} b) n l =
  ++⁺ (tt ∷ ++⁺ (++⁺ (env-entry-am (kind E) E A) (alloc-min-trace' b _ (suc (suc l)))) (tt ∷ []))
      (alloc-min-blocks b _ (suc (suc l)))
alloc-min-blocks (g ∘ f) n l =
  subst AllocMinTrace (sym (blocks-layout-++ (bodies-of F) (bodies-of G)))
    (++⁺ (alloc-min-blocks f n l) (alloc-min-blocks g (bud F) (lab F)))
  where F = ir-to-trace' n l f
        G = ir-to-trace' (bud F) (lab F) g
alloc-min-blocks (⟨ f , g ⟩) n l =
  subst AllocMinTrace (sym (blocks-layout-++ (bodies-of F) (bodies-of G)))
    (++⁺ (alloc-min-blocks f (suc (suc (suc (suc n)))) l)
         (alloc-min-blocks g (bud F) (lab F)))
  where F = ir-to-trace' (suc (suc (suc (suc n)))) l f
        G = ir-to-trace' (bud F) (lab F) g
alloc-min-blocks (case f g) n l =
  subst AllocMinTrace (sym (blocks-layout-++ (bodies-of F) (bodies-of G)))
    (++⁺ (alloc-min-blocks f n (suc (suc l))) (alloc-min-blocks g (bud F) (lab F)))
  where F = ir-to-trace' n (suc (suc l)) f
        G = ir-to-trace' (bud F) (lab F) g
alloc-min-blocks (Iter b) n l = alloc-min-blocks b _ _
alloc-min-blocks (Cata {F} _ alg) n l = alloc-min-blocks alg 0 l

alloc-min-at-frontier : ∀ {A B} (ir : IR A B) (n : ℕ)
                      → AllocMinTrace (ir-to-trace-at-frontier n ir)
alloc-min-at-frontier ir n =
  ++⁺ (alloc-min-trace' ir n 0) (tt ∷ alloc-min-blocks ir n 0)

ir-to-trace-alloc-min : ∀ {A B} (ir : IR A B) → AllocMinTrace (ir-to-trace ir)
ir-to-trace-alloc-min ir = alloc-min-at-frontier ir 0

ir-to-trace-lab-alloc-min : ∀ {A B} (ir : IR A B) (l : ℕ) → AllocMinTrace (ir-to-trace-lab l ir)
ir-to-trace-lab-alloc-min ir l = ++⁺ (alloc-min-trace' ir 0 l) (tt ∷ alloc-min-blocks ir 0 l)

ir-to-trace-top-alloc-min : ∀ {A B} (ir : IR A B) → AllocMinTrace (link-top (ir-to-unit ir))
ir-to-trace-top-alloc-min ir = ++⁺ (alloc-min-trace' ir 0 0) (tt ∷ alloc-min-blocks ir 0 0)

module _ {FS : FrameSemantics} where
  open FlatMachine {FS}

  fetch-alloc-min : ∀ {A B} (ir : IR A B) {k i}
                  → fetch (ir-to-trace ir) k ≡ just i → AllocMinI i
  fetch-alloc-min ir = fetch-All (ir-to-trace-alloc-min ir)
