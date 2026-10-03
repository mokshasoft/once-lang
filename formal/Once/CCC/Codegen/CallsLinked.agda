-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.CallsLinked   (plan 0.103 6a‴, D245)
--
-- EVERY EMITTED DIRECT CALL NAMES A TABLE ENTRY: each `c-call-fn f` in the
-- trace of a LINKED IR (`Once.Denotation.Program.Linked tbl`) names an entry
-- of `tbl` at some objects. The emitter writes `c-call-fn f` for `Call f` and
-- nowhere else, so the induction is `AllocMin`'s (`All P` over the entry
-- block and the block channel), with linkedness threaded to the `Call` leaf.
------------------------------------------------------------------------

open import Once.CanonicalName using (CanonicalName)
open import Data.List using (List)
open import Once.Denotation.Program using (IRFun; LinkedAt; Linked)
open import Once.Spec.Contract using (ISig)

module Once.CCC.Codegen.CallsLinked (o : CanonicalName) (tbl : List IRFun) where

-- plan 0.105: only the CALLS matter here; the signatures linkedness also
-- carries are any.
private variable σ : ISig

open import Data.Nat using (ℕ; suc; _+_; _≤_; s≤s; z≤n; _*_)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.All.Properties using (++⁺)
open import Data.Maybe using (just)
open import Relation.Binary.PropositionalEquality using (_≡_; subst; sym)

open import Once.IR using (IR; AllocMode; Stack; Heap;
  id; _∘_; ⟨_,_⟩; fst; snd; inl; inr; case; terminal; initial;
  curry; apply;
  In; out-μ; Cata; Out; in-ν; Ana;
  SigOp; Call; const)
open import Once.IRTy using (IRTy; fits-int; fits-float; ⌈_⌉F; ⟦_⟧TI; ν-type;
  WellFormedFI; wf-K; wf-Id; wf-Sum; wf-Prod)
open import Once.Type using (Functor; K; Id; _⊕_; _⊗_)
open import Once.CCC.Label using (ℓ)
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.SMCore using (AbstractInstr; AbstractTrace; instr-alloc-heap; instr-ctrl; c-call-fn
  ; blocks-layout; blocks-layout-++; LabelId
  ; restore-input; load-indirect-suc; store-at-slot; mov-to-input
  ; load-from-slot; store-indirect-suc; instr-load-tag-lit; store-indirect)
open import Once.CCC.Machine.Flat using (module FlatMachine)
open import Once.CCC.Codegen.IRToTrace o using
  (ir-to-trace'; ir-to-trace; ir-to-trace-at-frontier; ir-to-trace-lab;
   CataStrategy; strat-const; strat-nat; strat-linear; strat-branching;
   cata-strategy; cata-dispatch; cata-trace-nat; cata-trace-linear;
   cata-trace-branching; push2; pop2; wrap-sum; visit-walk; rebuild-walk; lsize;
   -- D099 / C1: the called-algebra blocks.
   cata-body; cata-call-setup; cata-call; cata-trace-const;
   cata-nat-I₁; cata-nat-I₂; cata-nat-I₃; fsize; resuspend-layer)
open import Once.CCC.Codegen.FrameFreeTrace o using (trace-of; cata-trace-of)

open import Once.CCC.Codegen.CallOK using (CallOKI)

CLTrace : AbstractTrace → Set
CLTrace = All (CallOKI tbl)

------------------------------------------------------------------------
-- The heap-linked-stack bricks the cata codegen is built from.
------------------------------------------------------------------------
push2-cl : ∀ topSlot tv tb → CLTrace (push2 topSlot tv tb)
push2-cl topSlot tv tb = tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ []

pop2-cl : ∀ topSlot → CLTrace (pop2 topSlot)
pop2-cl topSlot = tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ []

wrap-sum-cl : ∀ tag s → CLTrace (wrap-sum tag s)
wrap-sum-cl tag s = tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ []

------------------------------------------------------------------------
-- The compile-time functor walks. A sum node's dispatch is ONE
-- `instr-case-on-tag`, on which the predicate is `⊤` (shallow — see header).
------------------------------------------------------------------------
visit-walk-cl : ∀ todoSlot tv tb F s lb → CLTrace (visit-walk todoSlot tv tb F s lb)
visit-walk-cl todoSlot tv tb (K _)   s lb = []
visit-walk-cl todoSlot tv tb Id      s lb = tt ∷ push2-cl todoSlot tv tb
visit-walk-cl todoSlot tv tb (F ⊕ G) s lb =
  ++⁺ (tt ∷ tt ∷ tt ∷ [])
      (++⁺ (visit-walk-cl todoSlot tv tb G (s + 4) (suc (suc lb) + lsize F))
           (++⁺ (tt ∷ tt ∷ tt ∷ tt ∷ [])
                (++⁺ (visit-walk-cl todoSlot tv tb F (s + 4) (suc (suc lb)))
                     (tt ∷ []))))
visit-walk-cl todoSlot tv tb (F ⊗ G) s lb =
  ++⁺ (tt ∷ tt ∷ tt ∷ tt ∷ [])
      (++⁺ (visit-walk-cl todoSlot tv tb F (s + 4) lb)
           (++⁺ (tt ∷ tt ∷ tt ∷ [])
                (visit-walk-cl todoSlot tv tb G (s + 4) (lb + lsize F))))

rebuild-walk-cl : ∀ valSlot tv tb F s lb → CLTrace (rebuild-walk valSlot tv tb F s lb)
rebuild-walk-cl valSlot tv tb (K _)   s lb = tt ∷ []
rebuild-walk-cl valSlot tv tb Id      s lb = pop2-cl valSlot
rebuild-walk-cl valSlot tv tb (F ⊕ G) s lb =
  ++⁺ (tt ∷ tt ∷ tt ∷ [])
      (++⁺ (rebuild-walk-cl valSlot tv tb G (s + 4) (suc (suc lb) + lsize F))
           (++⁺ (wrap-sum-cl 1 s)
                (++⁺ (tt ∷ tt ∷ tt ∷ tt ∷ [])
                     (++⁺ (rebuild-walk-cl valSlot tv tb F (s + 4) (suc (suc lb)))
                          (++⁺ (wrap-sum-cl 0 s) (tt ∷ []))))))
rebuild-walk-cl valSlot tv tb (F ⊗ G) s lb =
  ++⁺ (tt ∷ tt ∷ tt ∷ tt ∷ [])
      (++⁺ (rebuild-walk-cl valSlot tv tb G (s + 4) (lb + lsize F))
           (++⁺ (tt ∷ tt ∷ tt ∷ tt ∷ [])
                (++⁺ (rebuild-walk-cl valSlot tv tb F (s + 4) lb)
                     (tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ []))))

------------------------------------------------------------------------
-- The three cata strategies (the algebra trace `at` is the caller's IH).
------------------------------------------------------------------------
-- D099 / C1: the three shared blocks. D131: `cata-call-setup` now allocates
-- TWO 2-cell heap blocks — the algebra's closure record, and the reusable
-- `(env , layer)` argument pair — so `tt` appears twice. `cata-call` still
-- allocates NOTHING: the pair is written in place, which is the point of
-- hoisting it out of the loop.
cata-body-cl : ∀ b e bb at → CLTrace at → CLTrace (cata-body b e bb at)
cata-body-cl b e bb  at ih = tt ∷ tt ∷ ++⁺ ih (tt ∷ tt ∷ [])

cata-setup-cl : ∀ cl k ev pr bl → CLTrace (cata-call-setup cl k ev pr bl)
cata-setup-cl cl k ev pr bl =
  tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷
  tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ []

cata-call-cl : ∀ cl k pr → CLTrace (cata-call cl k pr)
cata-call-cl cl k pr =
  tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ []

nat-I₁-cl : ∀ n1 l1 → CLTrace (cata-nat-I₁ n1 l1)
nat-I₁-cl n1 l1 =
  tt ∷ tt ∷
  ++⁺ (tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ [])
      (tt ∷ tt ∷ tt ∷
       ++⁺ (tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ []) (tt ∷ []))

nat-I₂-cl : ∀ n1 l1 → CLTrace (cata-nat-I₂ n1 l1)
nat-I₂-cl n1 l1 =
  tt ∷ tt ∷ tt ∷ ++⁺ (tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ []) (tt ∷ [])

nat-I₃-cl : ∀ l1 → CLTrace (cata-nat-I₃ l1)
nat-I₃-cl l1 = tt ∷ tt ∷ tt ∷ []

cata-nat-cl : ∀ bb n1 l1 at → CLTrace at
            → CLTrace (cata-trace-of (cata-trace-nat bb n1 l1 at))
cata-nat-cl bb n1 l1  at ih =
  ++⁺ (cata-setup-cl cl k ev pr bodyL)
      (++⁺ (nat-I₁-cl n1 l1)
           (++⁺ (cata-call-cl cl k pr)
                (++⁺ (nat-I₂-cl n1 l1)
                     (++⁺ (cata-call-cl cl k pr)
                          (++⁺ (nat-I₃-cl l1)
                               (cata-body-cl bodyL endL bb at ih))))))
  where
    bodyL = suc (suc (suc (suc (suc (suc l1)))))
    endL  = suc (suc (suc (suc (suc (suc (suc l1))))))
    cl    = suc (suc n1)
    k     = suc (suc (suc n1))
    ev    = suc (suc (suc (suc n1)))
    pr    = suc (suc (suc (suc (suc n1))))

cata-const-cl : ∀ bb n1 l1 at → CLTrace at
              → CLTrace (cata-trace-of (cata-trace-const bb n1 l1 at))
cata-const-cl bb n1 l1  at ih =
  ++⁺ (cata-setup-cl n1 (n1 + 1) (n1 + 2) (n1 + 3) l1)
      (++⁺ (cata-call-cl n1 (n1 + 1) (n1 + 3)) (cata-body-cl l1 (l1 + 1) bb at ih))

cata-linear-cl : ∀ bb n1 l1 at → CLTrace at
               → CLTrace (cata-trace-of (cata-trace-linear bb n1 l1 at))
cata-linear-cl bb n1 l1  at ih =
  ++⁺ (cata-setup-cl (suc (suc (suc (suc (suc (suc n1)))))) (suc (suc (suc (suc (suc (suc (suc n1))))))) (suc (suc (suc (suc (suc (suc (suc (suc n1)))))))) (suc (suc (suc (suc (suc (suc (suc (suc (suc n1)))))))))
                     (suc (suc (suc (suc l1)))))
      (++⁺ lin-I₁
           (++⁺ (cata-call-cl (suc (suc (suc (suc (suc (suc n1)))))) (suc (suc (suc (suc (suc (suc (suc n1))))))) (suc (suc (suc (suc (suc (suc (suc (suc (suc n1))))))))))
                (++⁺ lin-I₂
                     (++⁺ (cata-call-cl (suc (suc (suc (suc (suc (suc n1)))))) (suc (suc (suc (suc (suc (suc (suc n1))))))) (suc (suc (suc (suc (suc (suc (suc (suc (suc n1))))))))))
                          (++⁺ lin-I₃ (cata-body-cl (suc (suc (suc (suc l1)))) (suc (suc (suc (suc (suc l1))))) bb at ih))))))
  where
    lin-I₁ : CLTrace _
    lin-I₁ = tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷
             tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ []
    lin-I₂ : CLTrace _
    lin-I₂ = tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷
             tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ []
    lin-I₃ : CLTrace _
    lin-I₃ = tt ∷ tt ∷ tt ∷ []

cata-branching-cl : ∀ F bb n1 l1 at → CLTrace at
                  → CLTrace (cata-trace-of (cata-trace-branching F bb n1 l1 at))
cata-branching-cl F bb n1 l1  at ih =
  ++⁺ (cata-setup-cl cl (cl + 1) (cl + 2) (cl + 3) bodyL)
      (++⁺ I₁ (++⁺ (cata-call-cl cl (cl + 1) (cl + 3))
                   (++⁺ I₂ (cata-body-cl bodyL (bodyL + 1) bb at ih))))
  where
    bodyL = l1 + 4 + lsize F + lsize F
    cl    = n1 + 7 + (4 * fsize F) + 4
    I₁ : CLTrace _
    I₁ = ++⁺ (tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ [])
             (++⁺ (push2-cl n1 (n1 + 4) (n1 + 5))
             (++⁺ (tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ [])
             (++⁺ (push2-cl (suc n1) (n1 + 4) (n1 + 5))
             (++⁺ (tt ∷ tt ∷ [])
             (++⁺ (visit-walk-cl n1 (n1 + 4) (n1 + 5) F (n1 + 7) (l1 + 4))
             (++⁺ (tt ∷ tt ∷ [])
             (++⁺ (tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ [])
             (++⁺ (rebuild-walk-cl (n1 + 2) (n1 + 4) (n1 + 5) F (n1 + 7) ((l1 + 4) + lsize F))
                  (tt ∷ [])))))))))
    I₂ : CLTrace _
    I₂ = ++⁺ (push2-cl (n1 + 2) (n1 + 4) (n1 + 5))
             (++⁺ (tt ∷ tt ∷ []) (tt ∷ tt ∷ tt ∷ []))

cata-dispatch-cl : ∀ st bb n1 l1 at → CLTrace at
                 → CLTrace (cata-trace-of (cata-dispatch st bb n1 l1 at))
cata-dispatch-cl strat-const         bb n1 l1  at ih = cata-const-cl bb n1 l1 at ih
cata-dispatch-cl strat-nat           bb n1 l1  at ih = cata-nat-cl bb n1 l1 at ih
cata-dispatch-cl strat-linear        bb n1 l1  at ih = cata-linear-cl bb n1 l1 at ih
cata-dispatch-cl (strat-branching F) bb n1 l1  at ih = cata-branching-cl F bb n1 l1 at ih

------------------------------------------------------------------------
-- THE THEOREM, over arbitrary frontier `n` / label counter `l`.
------------------------------------------------------------------------

calls-trace' : ∀ {A B} (ir : IR A B) (n l : ℕ) → Linked σ tbl ir
             → CLTrace (trace-of (ir-to-trace' n l ir))
calls-trace' id       n l _ = tt ∷ []
calls-trace' fst      n l _ = tt ∷ []
calls-trace' snd      n l _ = tt ∷ []
calls-trace' terminal n l _ = []
calls-trace' initial  n l _ = tt ∷ []
calls-trace' (g ∘ f)  n l (lg , lf) =
  ++⁺ (calls-trace' f _ _ lf) (tt ∷ calls-trace' g _ _ lg)
calls-trace' (⟨ f , g ⟩) n l (lf , lg) =
  tt ∷ tt ∷
  ++⁺ (calls-trace' f _ _ lf)
      (tt ∷ tt ∷
       ++⁺ (calls-trace' g _ _ lg)
           (tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ []))
calls-trace' (curry b)  n l _ =
  tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ []
calls-trace' apply n l _ =
  tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷
  tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ []
calls-trace' inl n l _ =
  tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ []
calls-trace' inr n l _ =
  tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ []
calls-trace' (case f g) n l (lf , lg) =
  ++⁺ (tt ∷ tt ∷ tt ∷ [])
      (++⁺ (calls-trace' g _ _ lg)
           (++⁺ (tt ∷ tt ∷ tt ∷ tt ∷ [])
                (++⁺ (calls-trace' f _ _ lf) (tt ∷ []))))
calls-trace' (In _)  n l _ = tt ∷ []
calls-trace' (out-μ _) n l _ = tt ∷ []
calls-trace' (Cata {F} _ alg) n l la =
  cata-dispatch-cl (cata-strategy ⌈ F ⌉F) _ _ _ _ (calls-trace' alg 0 l la)
calls-trace' (Out _)        n l _ = tt ∷ tt ∷ tt ∷ tt ∷ []
calls-trace' (in-ν _)     n l _ =
  tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ []
calls-trace' (Ana _ c)      n l _ =
  tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ []
calls-trace' (SigOp _)      n l _ = tt ∷ []
calls-trace' (Call {A} {B} f) n l lk = (A , B , lk) ∷ []
calls-trace' (const fits-int _)   n l _ = tt ∷ []
calls-trace' (const fits-float _) n l _ = tt ∷ []

------------------------------------------------------------------------
-- THE BLOCK CHANNEL (D160): the emitted closure bodies call too.
------------------------------------------------------------------------

bodies-of : ℕ × ℕ × AbstractTrace × List (LabelId × ℕ × AbstractTrace)
          → List (LabelId × ℕ × AbstractTrace)
bodies-of (_ , _ , _ , bs) = bs

bud : ℕ × ℕ × AbstractTrace × List (LabelId × ℕ × AbstractTrace) → ℕ
bud (b , _ , _ , _) = b

lab : ℕ × ℕ × AbstractTrace × List (LabelId × ℕ × AbstractTrace) → ℕ
lab (_ , k , _ , _) = k

-- D199: every heap allocation the re-suspension pass emits is the two-cell
-- one — the suspension in `wf-Id`, the fresh pair in `wf-Prod`, the fresh
-- tagged node in each `wf-Sum` arm — so `tt` discharges all of them.
resuspend-cl : ∀ (n l : ℕ) (lbl : LabelId) {F} (wf : WellFormedFI F)
             → CLTrace (proj₂ (proj₂ (resuspend-layer n l lbl wf)))
resuspend-cl n l lbl (wf-K _) = []
resuspend-cl n l lbl wf-Id =
  tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ []
resuspend-cl n l lbl (wf-Prod wfF wfG) =
  tt ∷ tt ∷ tt ∷
  ++⁺ (resuspend-cl (suc (suc (suc n))) l lbl wfF)
      (tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷
       ++⁺ (resuspend-cl n2 l2 lbl wfG)
           (tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ []))
  where
    n2 = proj₁ (resuspend-layer (suc (suc (suc n))) l lbl wfF)
    l2 = proj₁ (proj₂ (resuspend-layer (suc (suc (suc n))) l lbl wfF))
resuspend-cl n l lbl (wf-Sum wfF wfG) =
  tt ∷ tt ∷ tt ∷
  ++⁺ (arm 1 (resuspend-cl n2 l2 lbl wfG))
      (tt ∷ tt ∷
       ++⁺ (arm 0 (resuspend-cl (suc (suc (suc n))) (suc (suc l)) lbl wfF))
           (tt ∷ []))
  where
    n2 = proj₁ (resuspend-layer (suc (suc (suc n))) (suc (suc l)) lbl wfF)
    l2 = proj₁ (proj₂ (resuspend-layer (suc (suc (suc n))) (suc (suc l)) lbl wfF))
    arm : ∀ (tag : ℕ) {t} → CLTrace t
        → CLTrace (restore-input n ∷ load-indirect-suc ∷
                         t ++ (store-at-slot (suc (suc n)) ∷ instr-alloc-heap 2 ∷
                               store-at-slot (suc n) ∷ mov-to-input ∷
                               load-from-slot (suc (suc n)) ∷ store-indirect-suc ∷
                               instr-load-tag-lit tag ∷ store-indirect ∷
                               load-from-slot (suc n) ∷ []))
    arm tag ih = tt ∷ tt ∷ ++⁺ ih (tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ [])

calls-blocks : ∀ {A B} (ir : IR A B) (n l : ℕ) → Linked σ tbl ir
             → CLTrace (blocks-layout (bodies-of (ir-to-trace' n l ir)))
calls-blocks id       n l _ = []
calls-blocks fst      n l _ = []
calls-blocks snd      n l _ = []
calls-blocks terminal n l _ = []
calls-blocks initial  n l _ = []
calls-blocks apply    n l _ = []
calls-blocks inl n l _ = []
calls-blocks inr n l _ = []
calls-blocks (In _)   n l _ = []
calls-blocks (out-μ _)  n l _ = []
calls-blocks (Out _)    n l _ = []
calls-blocks (in-ν _) n l _ = tt ∷ tt ∷ tt ∷ []
calls-blocks (Ana wf c) n l lc =
  ++⁺ (tt ∷ ++⁺ (++⁺ (calls-trace' c 0 (suc l) lc)
                     (resuspend-cl (proj₁ (ir-to-trace' 0 (suc l) c))
                                   (proj₁ (proj₂ (ir-to-trace' 0 (suc l) c)))
                                   (ℓ o l) wf))
                (tt ∷ []))
      (calls-blocks c 0 (suc l) lc)
calls-blocks (SigOp _)      n l _ = []
calls-blocks (Call _)      n l _ = []
calls-blocks (const fits-int _)   n l _ = []
calls-blocks (const fits-float _) n l _ = []
calls-blocks (curry b) n l lb =
  ++⁺ (tt ∷ ++⁺ (calls-trace' b 0 (suc (suc l)) lb) (tt ∷ []))
      (calls-blocks b 0 (suc (suc l)) lb)
calls-blocks (g ∘ f) n l (lg , lf) =
  subst CLTrace (sym (blocks-layout-++ (bodies-of F) (bodies-of G)))
    (++⁺ (calls-blocks f n l lf) (calls-blocks g (bud F) (lab F) lg))
  where F = ir-to-trace' n l f
        G = ir-to-trace' (bud F) (lab F) g
calls-blocks (⟨ f , g ⟩) n l (lf , lg) =
  subst CLTrace (sym (blocks-layout-++ (bodies-of F) (bodies-of G)))
    (++⁺ (calls-blocks f (suc (suc (suc (suc n)))) l lf)
         (calls-blocks g (bud F) (lab F) lg))
  where F = ir-to-trace' (suc (suc (suc (suc n)))) l f
        G = ir-to-trace' (bud F) (lab F) g
calls-blocks (case f g) n l (lf , lg) =
  subst CLTrace (sym (blocks-layout-++ (bodies-of F) (bodies-of G)))
    (++⁺ (calls-blocks f n (suc (suc l)) lf) (calls-blocks g (bud F) (lab F) lg))
  where F = ir-to-trace' n (suc (suc l)) f
        G = ir-to-trace' (bud F) (lab F) g
calls-blocks (Cata {F} _ alg) n l la = calls-blocks alg 0 l la

------------------------------------------------------------------------
-- Over the public entry points.
------------------------------------------------------------------------

ir-to-trace-calls : ∀ {A B} (ir : IR A B) → Linked σ tbl ir → CLTrace (ir-to-trace ir)
ir-to-trace-calls ir lk = ++⁺ (calls-trace' ir 0 0 lk) (tt ∷ calls-blocks ir 0 0 lk)

ir-to-trace-lab-calls : ∀ {A B} (ir : IR A B) (l : ℕ) → Linked σ tbl ir → CLTrace (ir-to-trace-lab l ir)
ir-to-trace-lab-calls ir l lk = ++⁺ (calls-trace' ir 0 l lk) (tt ∷ calls-blocks ir 0 l lk)
