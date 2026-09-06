-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.AllocMin   (Plan 0.54 rung D, item 5)
--
-- EVERY EMITTED ALLOCATION IS A PAIR BLOCK: each `instr-alloc-heap n` in an
-- emitted trace has `n ≥ 2` — in fact every site is literally
-- `instr-alloc-heap 2` (the pair `⟨_,_⟩ Heap`, the closure record
-- `curry _ Heap`, `apply`'s (env, arg) pair, the sum nodes `inl`/`inr Heap`,
-- and the cata payload-stack nodes `push2`/`wrap-sum`/`build-layer`).
--
-- This is the emitter half of the pointer-bounds invariant
-- (`Once.CCC.Machine.FlatPtrBounds`): the fresh pointer an alloc hands out is
-- the START of a pair, so `suc offset < block-size` holds for it.
--
-- Since item 6 (case compiles to FLAT control) there is no nesting anywhere:
-- every alloc site of every branch is in the main trace, so this `All` covers
-- the WHOLE emitted program. Structure: the induction of `FrameFreeTrace`
-- (`All P` over `trace-of (ir-to-trace' n l ir)`, `++⁺` at every splice).
------------------------------------------------------------------------

-- Plan 0.63 (D089): parameterised by the DEFINITION'S identity, which keys
-- its labels. `o` is constant for a whole definition, so it belongs on the
-- module rather than on every lemma — which is exactly what keeps the
-- statements below UNCHANGED under D089: `IRToTrace` is imported APPLIED,
-- so each `ir-to-trace' n l ir` reads as it always did.
open import Once.CanonicalName using (CanonicalName)

module Once.CCC.Codegen.AllocMin (o : CanonicalName) where

open import Data.Nat using (ℕ; suc; _+_; _≤_; s≤s; z≤n; _*_)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_×_; _,_)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.All.Properties using (++⁺)
open import Data.Maybe using (just)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Once.IR using (IR; AllocMode; Stack; Heap;
  id; _∘_; ⟨_,_⟩; fst; snd; inl; inr; case; terminal; initial;
  curry; apply;
  In; out-μ; Cata; Para; Out; in-ν; Ana; Hylo; Fuse;
  free-heap; SigOp; const)
open import Once.IRTy using (fits-int; fits-float; ⌈_⌉F)
open import Once.Type using (Functor; K; Id; _⊕_; _⊗_)
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.SMCore using (AbstractInstr; AbstractTrace; instr-alloc-heap)
open import Once.CCC.Machine.Flat using (module FlatMachine)
open import Once.CCC.Codegen.IRToTrace o using
  (ir-to-trace'; ir-to-trace; ir-to-trace-at-frontier;
   CataStrategy; strat-const; strat-nat; strat-linear; strat-branching;
   cata-strategy; cata-dispatch; cata-trace-nat; cata-trace-linear;
   cata-trace-branching; push2; pop2; wrap-sum; visit-walk; rebuild-walk; lsize;
   -- D099 / C1: the called-algebra blocks.
   cata-body; cata-call-setup; cata-call; cata-trace-const;
   cata-nat-I₁; cata-nat-I₂; cata-nat-I₃; fsize)
open import Once.CCC.Codegen.FrameFreeTrace o using (trace-of; cata-trace-of)

-- The per-instruction fact, reducing on every constructor (CATCHALL): only an
-- allocation is constrained.
AllocMinI : AbstractInstr → Set
AllocMinI (instr-alloc-heap n) = 2 ≤ n
{-# CATCHALL #-}
AllocMinI _                    = ⊤

AllocMinTrace : AbstractTrace → Set
AllocMinTrace = All AllocMinI

-- every emitted site is literally `instr-alloc-heap 2`
am2 : 2 ≤ 2
am2 = s≤s (s≤s z≤n)

------------------------------------------------------------------------
-- The heap-linked-stack bricks the cata codegen is built from.
------------------------------------------------------------------------
push2-am : ∀ topSlot tv tb → AllocMinTrace (push2 topSlot tv tb)
push2-am topSlot tv tb = tt ∷ am2 ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ []

pop2-am : ∀ topSlot → AllocMinTrace (pop2 topSlot)
pop2-am topSlot = tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ []

wrap-sum-am : ∀ tag s → AllocMinTrace (wrap-sum tag s)
wrap-sum-am tag s = tt ∷ am2 ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ []

------------------------------------------------------------------------
-- The compile-time functor walks. A sum node's dispatch is ONE
-- `instr-case-on-tag`, on which the predicate is `⊤` (shallow — see header).
------------------------------------------------------------------------
visit-walk-am : ∀ todoSlot tv tb F s lb → AllocMinTrace (visit-walk todoSlot tv tb F s lb)
visit-walk-am todoSlot tv tb (K _)   s lb = []
visit-walk-am todoSlot tv tb Id      s lb = tt ∷ push2-am todoSlot tv tb
visit-walk-am todoSlot tv tb (F ⊕ G) s lb =
  ++⁺ (tt ∷ tt ∷ tt ∷ [])
      (++⁺ (visit-walk-am todoSlot tv tb G (s + 4) (suc (suc lb) + lsize F))
           (++⁺ (tt ∷ tt ∷ tt ∷ tt ∷ [])
                (++⁺ (visit-walk-am todoSlot tv tb F (s + 4) (suc (suc lb)))
                     (tt ∷ []))))
visit-walk-am todoSlot tv tb (F ⊗ G) s lb =
  ++⁺ (tt ∷ tt ∷ tt ∷ tt ∷ [])
      (++⁺ (visit-walk-am todoSlot tv tb G (s + 4) (lb + lsize F))
           (++⁺ (tt ∷ tt ∷ tt ∷ [])
                (visit-walk-am todoSlot tv tb F (s + 4) lb)))

rebuild-walk-am : ∀ valSlot tv tb F s lb → AllocMinTrace (rebuild-walk valSlot tv tb F s lb)
rebuild-walk-am valSlot tv tb (K _)   s lb = tt ∷ []
rebuild-walk-am valSlot tv tb Id      s lb = pop2-am valSlot
rebuild-walk-am valSlot tv tb (F ⊕ G) s lb =
  ++⁺ (tt ∷ tt ∷ tt ∷ [])
      (++⁺ (rebuild-walk-am valSlot tv tb G (s + 4) (suc (suc lb) + lsize F))
           (++⁺ (wrap-sum-am 1 s)
                (++⁺ (tt ∷ tt ∷ tt ∷ tt ∷ [])
                     (++⁺ (rebuild-walk-am valSlot tv tb F (s + 4) (suc (suc lb)))
                          (++⁺ (wrap-sum-am 0 s) (tt ∷ []))))))
rebuild-walk-am valSlot tv tb (F ⊗ G) s lb =
  ++⁺ (tt ∷ tt ∷ tt ∷ tt ∷ [])
      (++⁺ (rebuild-walk-am valSlot tv tb F (s + 4) lb)
           (++⁺ (tt ∷ tt ∷ tt ∷ tt ∷ [])
                (++⁺ (rebuild-walk-am valSlot tv tb G (s + 4) (lb + lsize F))
                     (tt ∷ am2 ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ []))))

------------------------------------------------------------------------
-- The three cata strategies (the algebra trace `at` is the caller's IH).
------------------------------------------------------------------------
-- D099 / C1: the three shared blocks. D131: `cata-call-setup` now allocates
-- TWO 2-cell heap blocks — the algebra's closure record, and the reusable
-- `(env , layer)` argument pair — so `am2` appears twice. `cata-call` still
-- allocates NOTHING: the pair is written in place, which is the point of
-- hoisting it out of the loop.
cata-body-am : ∀ b e bb at → AllocMinTrace at → AllocMinTrace (cata-body b e bb at)
cata-body-am b e bb at am = tt ∷ tt ∷ ++⁺ am (tt ∷ tt ∷ [])

cata-setup-am : ∀ cl k ev pr bl → AllocMinTrace (cata-call-setup cl k ev pr bl)
cata-setup-am cl k ev pr bl =
  tt ∷ tt ∷ tt ∷ tt ∷ am2 ∷ tt ∷ tt ∷ tt ∷ tt ∷
  am2 ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ []

cata-call-am : ∀ cl k pr → AllocMinTrace (cata-call cl k pr)
cata-call-am cl k pr =
  tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ []

nat-I₁-am : ∀ n1 l1 → AllocMinTrace (cata-nat-I₁ n1 l1)
nat-I₁-am n1 l1 =
  tt ∷ tt ∷
  ++⁺ (tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ [])
      (tt ∷ tt ∷ tt ∷
       ++⁺ (tt ∷ tt ∷ am2 ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ []) (tt ∷ []))

nat-I₂-am : ∀ n1 l1 → AllocMinTrace (cata-nat-I₂ n1 l1)
nat-I₂-am n1 l1 =
  tt ∷ tt ∷ tt ∷ ++⁺ (tt ∷ tt ∷ am2 ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ []) (tt ∷ [])

nat-I₃-am : ∀ l1 → AllocMinTrace (cata-nat-I₃ l1)
nat-I₃-am l1 = tt ∷ tt ∷ tt ∷ []

cata-nat-am : ∀ bb n1 l1 at → AllocMinTrace at
            → AllocMinTrace (cata-trace-of (cata-trace-nat bb n1 l1 at))
cata-nat-am bb n1 l1 at am =
  ++⁺ (cata-setup-am cl k ev pr bodyL)
      (++⁺ (nat-I₁-am n1 l1)
           (++⁺ (cata-call-am cl k pr)
                (++⁺ (nat-I₂-am n1 l1)
                     (++⁺ (cata-call-am cl k pr)
                          (++⁺ (nat-I₃-am l1)
                               (cata-body-am bodyL endL bb at am))))))
  where
    bodyL = suc (suc (suc (suc (suc (suc l1)))))
    endL  = suc (suc (suc (suc (suc (suc (suc l1))))))
    cl    = suc (suc n1)
    k     = suc (suc (suc n1))
    ev    = suc (suc (suc (suc n1)))
    pr    = suc (suc (suc (suc (suc n1))))

cata-const-am : ∀ bb n1 l1 at → AllocMinTrace at
              → AllocMinTrace (cata-trace-of (cata-trace-const bb n1 l1 at))
cata-const-am bb n1 l1 at am =
  ++⁺ (cata-setup-am n1 (n1 + 1) (n1 + 2) (n1 + 3) l1)
      (++⁺ (cata-call-am n1 (n1 + 1) (n1 + 3)) (cata-body-am l1 (l1 + 1) bb at am))

cata-linear-am : ∀ bb n1 l1 at → AllocMinTrace at
               → AllocMinTrace (cata-trace-of (cata-trace-linear bb n1 l1 at))
cata-linear-am bb n1 l1 at am =
  ++⁺ (cata-setup-am (suc (suc (suc (suc (suc (suc n1)))))) (suc (suc (suc (suc (suc (suc (suc n1))))))) (suc (suc (suc (suc (suc (suc (suc (suc n1)))))))) (suc (suc (suc (suc (suc (suc (suc (suc (suc n1)))))))))
                     (suc (suc (suc (suc l1)))))
      (++⁺ lin-I₁
           (++⁺ (cata-call-am (suc (suc (suc (suc (suc (suc n1)))))) (suc (suc (suc (suc (suc (suc (suc n1))))))) (suc (suc (suc (suc (suc (suc (suc (suc (suc n1))))))))))
                (++⁺ lin-I₂
                     (++⁺ (cata-call-am (suc (suc (suc (suc (suc (suc n1)))))) (suc (suc (suc (suc (suc (suc (suc n1))))))) (suc (suc (suc (suc (suc (suc (suc (suc (suc n1))))))))))
                          (++⁺ lin-I₃ (cata-body-am (suc (suc (suc (suc l1)))) (suc (suc (suc (suc (suc l1))))) bb at am))))))
  where
    lin-I₁ : AllocMinTrace _
    lin-I₁ = tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ am2 ∷
             tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ []
    lin-I₂ : AllocMinTrace _
    lin-I₂ = tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ am2 ∷ tt ∷ tt ∷ tt ∷
             tt ∷ tt ∷ tt ∷ am2 ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ []
    lin-I₃ : AllocMinTrace _
    lin-I₃ = tt ∷ tt ∷ tt ∷ []

cata-branching-am : ∀ F bb n1 l1 at → AllocMinTrace at
                  → AllocMinTrace (cata-trace-of (cata-trace-branching F bb n1 l1 at))
cata-branching-am F bb n1 l1 at am =
  ++⁺ (cata-setup-am cl (cl + 1) (cl + 2) (cl + 3) bodyL)
      (++⁺ I₁ (++⁺ (cata-call-am cl (cl + 1) (cl + 3))
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
             (++⁺ (rebuild-walk-am (n1 + 2) (n1 + 4) (n1 + 5) F (n1 + 7) ((l1 + 4) + lsize F))
                  (tt ∷ [])))))))))
    I₂ : AllocMinTrace _
    I₂ = ++⁺ (push2-am (n1 + 2) (n1 + 4) (n1 + 5))
             (++⁺ (tt ∷ tt ∷ []) (tt ∷ tt ∷ tt ∷ []))

cata-dispatch-am : ∀ st bb n1 l1 at → AllocMinTrace at
                 → AllocMinTrace (cata-trace-of (cata-dispatch st bb n1 l1 at))
cata-dispatch-am strat-const         bb n1 l1 at am = cata-const-am bb n1 l1 at am
cata-dispatch-am strat-nat           bb n1 l1 at am = cata-nat-am bb n1 l1 at am
cata-dispatch-am strat-linear        bb n1 l1 at am = cata-linear-am bb n1 l1 at am
cata-dispatch-am (strat-branching F) bb n1 l1 at am = cata-branching-am F bb n1 l1 at am

------------------------------------------------------------------------
-- THE THEOREM, over arbitrary frontier `n` / label counter `l`.
------------------------------------------------------------------------
alloc-min-trace' : ∀ {A B} (ir : IR A B) (n l : ℕ)
                 → AllocMinTrace (trace-of (ir-to-trace' n l ir))
alloc-min-trace' id       n l = tt ∷ []
alloc-min-trace' fst      n l = tt ∷ []
alloc-min-trace' snd      n l = tt ∷ []
alloc-min-trace' terminal n l = []
alloc-min-trace' initial  n l = tt ∷ []
alloc-min-trace' (g ∘ f)  n l =
  ++⁺ (alloc-min-trace' f _ _) (tt ∷ alloc-min-trace' g _ _)
-- Stage G: the stack-shape clause that stood here collapsed onto this
-- same LHS when the pair's mode was dropped, and shadowed the heap one.
alloc-min-trace' (⟨ f , g ⟩) n l =
  tt ∷ tt ∷
  ++⁺ (alloc-min-trace' f _ _)
      (tt ∷ tt ∷
       ++⁺ (alloc-min-trace' g _ _)
           (tt ∷ am2 ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ []))
-- the flip: the body is inline here, so the walk recurses into it (one line)
alloc-min-trace' (curry b Stack) n l =
  tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷
  ++⁺ (alloc-min-trace' b _ _) (tt ∷ tt ∷ [])
alloc-min-trace' (curry b Heap)  n l =
  tt ∷ tt ∷ am2 ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷
  ++⁺ (alloc-min-trace' b _ _) (tt ∷ tt ∷ [])
alloc-min-trace' apply n l =
  tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ am2 ∷ tt ∷
  tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ []
alloc-min-trace' (inl Stack) n l = tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ []
alloc-min-trace' (inr Stack) n l = tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ []
alloc-min-trace' (inl Heap)  n l =
  tt ∷ tt ∷ am2 ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ []
alloc-min-trace' (inr Heap)  n l =
  tt ∷ tt ∷ am2 ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ []
-- case is FLAT CONTROL since item 6 — plain splices.
alloc-min-trace' (case f g) n l =
  ++⁺ (tt ∷ tt ∷ tt ∷ [])
      (++⁺ (alloc-min-trace' g _ _)
           (++⁺ (tt ∷ tt ∷ tt ∷ tt ∷ [])
                (++⁺ (alloc-min-trace' f _ _) (tt ∷ []))))
alloc-min-trace' (In _ _)  n l = tt ∷ []
alloc-min-trace' (out-μ _) n l = tt ∷ []
-- C1: the algebra is generated at frontier 0 (its own frame).
alloc-min-trace' (Cata {F} _ alg) n l =
  cata-dispatch-am (cata-strategy ⌈ F ⌉F) _ _ _ _ (alloc-min-trace' alg 0 l)
alloc-min-trace' (Para _ _)     n l = []
alloc-min-trace' (Out _)        n l = tt ∷ []
alloc-min-trace' (in-ν _ _)     n l = []
alloc-min-trace' (Ana _ _)      n l = []
alloc-min-trace' (Hylo _ _ _ _) n l = []
alloc-min-trace' (Fuse _ _ _ _) n l = []
alloc-min-trace' (free-heap _)  n l = tt ∷ []
alloc-min-trace' (SigOp _)      n l = tt ∷ []
alloc-min-trace' (const fits-int _)   n l = tt ∷ []
alloc-min-trace' (const fits-float _) n l = tt ∷ []

------------------------------------------------------------------------
-- Corollaries over the public entry points, and the fetch form the
-- flat↔x86-64 correspondence consumes.
------------------------------------------------------------------------
alloc-min-at-frontier : ∀ {A B} (ir : IR A B) (n : ℕ)
                      → AllocMinTrace (ir-to-trace-at-frontier n ir)
alloc-min-at-frontier ir n with ir-to-trace' n 0 ir | alloc-min-trace' ir n 0
... | _ , _ , _ , _ | am = am

ir-to-trace-alloc-min : ∀ {A B} (ir : IR A B) → AllocMinTrace (ir-to-trace ir)
ir-to-trace-alloc-min ir = alloc-min-at-frontier ir 0

module _ {FS : FrameSemantics} where
  open FlatMachine {FS}

  fetch-alloc-min : ∀ {A B} (ir : IR A B) {k i}
                  → fetch (ir-to-trace ir) k ≡ just i → AllocMinI i
  fetch-alloc-min ir = fetch-All (ir-to-trace-alloc-min ir)
