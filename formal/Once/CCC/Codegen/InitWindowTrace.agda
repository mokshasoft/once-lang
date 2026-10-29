-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.InitWindowTrace   (Plan 0.123 A.4 step 4, part 1)
--
-- THE EMITTED CODE WRITES EVERY BLOCK BEFORE IT READS IT: `InitDisc` holds
-- of everything the code generator emits (`InitWindow`). The induction is
-- `AllocMin`'s, clause for clause: where that proof had `am2` (the block is a
-- pair) this one has the allocation's window, which is one of the three
-- shapes `std` / `std1` / `stdr` (or, in the re-suspension's `wf-Id`, a
-- window that loads the environment's cell between the two writes). The
-- only facts a window needs are that its value loads do not read the stash
-- slot, which is slot arithmetic (`apL`/`apR`/`apM`).
--
-- One site is not covered yet: the re-suspension of a PRODUCT layer, whose
-- second cell is written after the second child is re-suspended. The claim
-- carries `AnaNoProd` until that clause is reordered (plan 0.123 A.4).
------------------------------------------------------------------------

open import Once.Spec.Name using (CanonicalName)

module Once.CCC.Codegen.InitWindowTrace (o : CanonicalName) where

open import Data.Nat using (ℕ; suc; _+_; _<_; _<ᵇ_; _*_)
open import Data.Nat.Properties using (<⇒≢; >⇒≢; +-monoʳ-<; +-monoˡ-<; +-comm; <ᵇ⇒<)
open import Data.Bool using (T)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; subst; sym; trans)

open import Once.IR using (IR; id; _∘_; ⟨_,_⟩; fst; snd; inl; inr; case; terminal; initial; curry; apply; In; out-μ; Cata; Out; in-ν; Ana; Iter; SigOp; Call; const)
open import Once.IRTy using (fits-int; fits-float; ⌈_⌉F; WellFormedFI; wf-K; wf-Id; wf-Sum; wf-Prod)
open import Once.Spec.Type using (K; Id; _⊕_; _⊗_)
open import Once.CCC.Label using (ℓ)
open import Once.CCC.Machine.SMCore using (AbstractInstr; AbstractTrace; instr-alloc-heap
  ; blocks-layout; blocks-layout-++; LabelId; link-top
  ; restore-input; load-indirect-suc; store-at-slot; mov-to-input
  ; load-from-slot; store-indirect-suc; instr-load-tag-lit; store-indirect)
open import Once.SigOp.Info using (SigOpInfo; module SigOpInfo)
open SigOpInfo using (sem)
open import Once.Arith.CmpOp using (CmpOp)
open import Once.Arith.SigOp.Compare using (cmp-of)
open import Once.CCC.Codegen.IRToTrace o using
  (sigop-code; ir-to-trace'; ir-to-trace; ir-to-trace-at-frontier; ir-to-trace-lab; ir-to-unit; strat-const; strat-nat; strat-linear; strat-branching; cata-strategy; cata-dispatch; cata-trace-nat; cata-trace-linear; cata-trace-branching; push2; pop2; wrap-sum; visit-walk; rebuild-walk; lsize; cata-body; cata-call-setup; cata-call; cata-trace-const; cata-nat-I₁; cata-nat-I₂; cata-nat-I₃; fsize; resuspend-layer)
open import Once.CCC.Codegen.FrameFreeTrace o using (trace-of; cata-trace-of)
open import Once.CCC.Codegen.InitWindow

-- an allocation and its window, in the list syntax the proofs are written in
infixr 5 _▸_
_▸_ : ∀ {n t} → WinFrom t → InitDisc t → InitDisc (instr-alloc-heap n ∷ t)
w ▸ d = alloc w d

-- SLOT ARITHMETIC: two stack slots a constant apart are different. `a + n`
-- is `suc` applied `a` times, the form the code generator's `suc` chains
-- take; `n + a` is the `ℕ.+` form; `apM` mixes them.
lit : ∀ a b → {T (a <ᵇ b)} → a < b
lit a b {p} = <ᵇ⇒< a b p

apL : ∀ n {a b} → a < b → ¬ (a + n ≡ b + n)
apL n lt = <⇒≢ (+-monoˡ-< n lt)

apL' : ∀ n {a b} → b < a → ¬ (a + n ≡ b + n)
apL' n lt = >⇒≢ (+-monoˡ-< n lt)

apR : ∀ n {a b} → a < b → ¬ (n + a ≡ n + b)
apR n lt = <⇒≢ (+-monoʳ-< n lt)

apM : ∀ n {a b} → a < b → ¬ (a + n ≡ n + b)
apM n {a} {b} lt eq = apL n lt (trans eq (+-comm n b))

------------------------------------------------------------------------
-- The heap-linked-stack bricks the cata codegen is built from.
------------------------------------------------------------------------
push2-id : ∀ topSlot tv tb → ¬ (tv ≡ tb) → ¬ (topSlot ≡ tb) → InitDisc (push2 topSlot tv tb)
push2-id topSlot tv tb a b = tt ∷ (std (s-slot a) (s-slot b)) ▸ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ []

pop2-id : ∀ topSlot → InitDisc (pop2 topSlot)
pop2-id topSlot = tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ []

wrap-sum-id : ∀ tag s → InitDisc (wrap-sum tag s)
wrap-sum-id tag s = tt ∷ (std s-tag (s-slot (apL s (lit 0 1)))) ▸ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ []

------------------------------------------------------------------------
-- The compile-time functor walks. A sum node's dispatch is ONE
-- `instr-case-on-tag`, on which the predicate is `⊤` (shallow — see header).
------------------------------------------------------------------------
visit-walk-id : ∀ todoSlot tv tb → ¬ (tv ≡ tb) → ¬ (todoSlot ≡ tb) → ∀ F s lb → InitDisc (visit-walk todoSlot tv tb F s lb)
visit-walk-id todoSlot tv tb a b (K _)   s lb = []
visit-walk-id todoSlot tv tb a b Id      s lb = tt ∷ push2-id todoSlot tv tb a b
visit-walk-id todoSlot tv tb a b (F ⊕ G) s lb =
  init-++ (tt ∷ tt ∷ tt ∷ [])
      (init-++ (visit-walk-id todoSlot tv tb a b G (s + 4) (suc (suc lb) + lsize F))
           (init-++ (tt ∷ tt ∷ tt ∷ tt ∷ [])
                (init-++ (visit-walk-id todoSlot tv tb a b F (s + 4) (suc (suc lb)))
                     (tt ∷ []))))
visit-walk-id todoSlot tv tb a b (F ⊗ G) s lb =
  init-++ (tt ∷ tt ∷ tt ∷ tt ∷ [])
      (init-++ (visit-walk-id todoSlot tv tb a b F (s + 4) lb)
           (init-++ (tt ∷ tt ∷ tt ∷ [])
                (visit-walk-id todoSlot tv tb a b G (s + 4) (lb + lsize F))))

rebuild-walk-id : ∀ valSlot tv tb F s lb → InitDisc (rebuild-walk valSlot tv tb F s lb)
rebuild-walk-id valSlot tv tb (K _)   s lb = tt ∷ []
rebuild-walk-id valSlot tv tb Id      s lb = pop2-id valSlot
rebuild-walk-id valSlot tv tb (F ⊕ G) s lb =
  init-++ (tt ∷ tt ∷ tt ∷ [])
      (init-++ (rebuild-walk-id valSlot tv tb G (s + 4) (suc (suc lb) + lsize F))
           (init-++ (wrap-sum-id 1 s)
                (init-++ (tt ∷ tt ∷ tt ∷ tt ∷ [])
                     (init-++ (rebuild-walk-id valSlot tv tb F (s + 4) (suc (suc lb)))
                          (init-++ (wrap-sum-id 0 s) (tt ∷ []))))))
rebuild-walk-id valSlot tv tb (F ⊗ G) s lb =
  init-++ (tt ∷ tt ∷ tt ∷ tt ∷ [])
      (init-++ (rebuild-walk-id valSlot tv tb G (s + 4) (lb + lsize F))
           (init-++ (tt ∷ tt ∷ tt ∷ tt ∷ [])
                (init-++ (rebuild-walk-id valSlot tv tb F (s + 4) lb)
                     (tt ∷ (std (s-slot (apM s (lit 1 3))) (s-slot (apR s (lit 2 3)))) ▸ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ []))))

------------------------------------------------------------------------
-- The three cata strategies (the algebra trace `at` is the caller's IH).
------------------------------------------------------------------------
-- D099 / C1: the three shared blocks. D131: `cata-call-setup` now allocates
-- TWO 2-cell heap blocks — the algebra's closure record, and the reusable
-- `(env , layer)` argument pair — so `am2` appears twice. `cata-call` still
-- allocates NOTHING: the pair is written in place, which is the point of
-- hoisting it out of the loop.
cata-body-id : ∀ b e bb at → InitDisc at → InitDisc (cata-body b e bb at)
cata-body-id b e bb at am = tt ∷ tt ∷ init-++ am (tt ∷ tt ∷ [])

cata-setup-id : ∀ cl k ev pr bl → ¬ (ev ≡ pr) → InitDisc (cata-call-setup cl k ev pr bl)
cata-setup-id cl k ev pr bl e =
  tt ∷ tt ∷ tt ∷ tt ∷ (std1 (s-slot e)) ▸ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷
  (std s-tag s-code) ▸ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ []

cata-call-id : ∀ cl k pr → InitDisc (cata-call cl k pr)
cata-call-id cl k pr =
  tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ []

nat-I₁-id : ∀ n1 l1 → InitDisc (cata-nat-I₁ n1 l1)
nat-I₁-id n1 l1 =
  tt ∷ tt ∷
  init-++ (tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ [])
      (tt ∷ tt ∷ tt ∷
       init-++ (tt ∷ tt ∷ (std s-tag (s-slot (apL n1 (lit 0 1)))) ▸ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ []) (tt ∷ []))

nat-I₂-id : ∀ n1 l1 → InitDisc (cata-nat-I₂ n1 l1)
nat-I₂-id n1 l1 =
  tt ∷ tt ∷ tt ∷ init-++ (tt ∷ tt ∷ (std s-tag (s-slot (apL n1 (lit 0 1)))) ▸ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ []) (tt ∷ [])

nat-I₃-id : ∀ l1 → InitDisc (cata-nat-I₃ l1)
nat-I₃-id l1 = tt ∷ tt ∷ tt ∷ []

cata-nat-id : ∀ bb n1 l1 at → InitDisc at
            → InitDisc (cata-trace-of (cata-trace-nat bb n1 l1 at))
cata-nat-id bb n1 l1 at am =
  init-++ (cata-setup-id cl k ev pr bodyL (apL n1 (lit 4 5)))
      (init-++ (nat-I₁-id n1 l1)
           (init-++ (cata-call-id cl k pr)
                (init-++ (nat-I₂-id n1 l1)
                     (init-++ (cata-call-id cl k pr)
                          (init-++ (nat-I₃-id l1)
                               (cata-body-id bodyL endL bb at am))))))
  where
    bodyL = suc (suc (suc (suc (suc (suc l1)))))
    endL  = suc (suc (suc (suc (suc (suc (suc l1))))))
    cl    = suc (suc n1)
    k     = suc (suc (suc n1))
    ev    = suc (suc (suc (suc n1)))
    pr    = suc (suc (suc (suc (suc n1))))

cata-const-id : ∀ bb n1 l1 at → InitDisc at
              → InitDisc (cata-trace-of (cata-trace-const bb n1 l1 at))
cata-const-id bb n1 l1 at am =
  init-++ (cata-setup-id n1 (n1 + 1) (n1 + 2) (n1 + 3) l1 (apR n1 (lit 2 3)))
      (init-++ (cata-call-id n1 (n1 + 1) (n1 + 3)) (cata-body-id l1 (l1 + 1) bb at am))

cata-linear-id : ∀ bb n1 l1 at → InitDisc at
               → InitDisc (cata-trace-of (cata-trace-linear bb n1 l1 at))
cata-linear-id bb n1 l1 at am =
  init-++ (cata-setup-id (suc (suc (suc (suc (suc (suc n1)))))) (suc (suc (suc (suc (suc (suc (suc n1))))))) (suc (suc (suc (suc (suc (suc (suc (suc n1)))))))) (suc (suc (suc (suc (suc (suc (suc (suc (suc n1)))))))))
                     (suc (suc (suc (suc l1)))) (apL n1 (lit 8 9)))
      (init-++ lin-I₁
           (init-++ (cata-call-id (suc (suc (suc (suc (suc (suc n1)))))) (suc (suc (suc (suc (suc (suc (suc n1))))))) (suc (suc (suc (suc (suc (suc (suc (suc (suc n1))))))))))
                (init-++ lin-I₂
                     (init-++ (cata-call-id (suc (suc (suc (suc (suc (suc n1)))))) (suc (suc (suc (suc (suc (suc (suc n1))))))) (suc (suc (suc (suc (suc (suc (suc (suc (suc n1))))))))))
                          (init-++ lin-I₃ (cata-body-id (suc (suc (suc (suc l1)))) (suc (suc (suc (suc (suc l1))))) bb at am))))))
  where
    lin-I₁ : InitDisc _
    lin-I₁ = tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ (std (s-slot (apL' n1 (lit 1 5))) (s-slot (apL' n1 (lit 1 3)))) ▸
             tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ []
    lin-I₂ : InitDisc _
    lin-I₂ = tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ (std (s-slot (apL' n1 (lit 1 5))) (s-slot (apL' n1 (lit 1 4)))) ▸ tt ∷ tt ∷ tt ∷
             tt ∷ tt ∷ tt ∷ (std s-tag (s-slot (apL' n1 (lit 0 1)))) ▸ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ []
    lin-I₃ : InitDisc _
    lin-I₃ = tt ∷ tt ∷ tt ∷ []

cata-branching-id : ∀ F bb n1 l1 at → InitDisc at
                  → InitDisc (cata-trace-of (cata-trace-branching F bb n1 l1 at))
cata-branching-id F bb n1 l1 at am =
  init-++ (cata-setup-id cl (cl + 1) (cl + 2) (cl + 3) bodyL (apR cl (lit 2 3)))
      (init-++ I₁ (init-++ (cata-call-id cl (cl + 1) (cl + 3))
                   (init-++ I₂ (cata-body-id bodyL (bodyL + 1) bb at am))))
  where
    bodyL = l1 + 4 + lsize F + lsize F
    cl    = n1 + 7 + (4 * fsize F) + 4
    I₁ : InitDisc _
    I₁ = init-++ (tt ∷ tt ∷ (std1 s-tag) ▸ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ [])
             (init-++ (push2-id n1 (n1 + 4) (n1 + 5) (apR n1 (lit 4 5)) (apM n1 (lit 0 5)))
             (init-++ (tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ [])
             (init-++ (push2-id (suc n1) (n1 + 4) (n1 + 5) (apR n1 (lit 4 5)) (apM n1 (lit 1 5)))
             (init-++ (tt ∷ tt ∷ [])
             (init-++ (visit-walk-id n1 (n1 + 4) (n1 + 5) (apR n1 (lit 4 5)) (apM n1 (lit 0 5)) F (n1 + 7) (l1 + 4))
             (init-++ (tt ∷ tt ∷ [])
             (init-++ (tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ [])
             (init-++ (rebuild-walk-id (n1 + 2) (n1 + 4) (n1 + 5) F (n1 + 7) ((l1 + 4) + lsize F))
                  (tt ∷ [])))))))))
    I₂ : InitDisc _
    I₂ = init-++ (push2-id (n1 + 2) (n1 + 4) (n1 + 5) (apR n1 (lit 4 5)) (apR n1 (lit 2 5)))
             (init-++ (tt ∷ tt ∷ []) (tt ∷ tt ∷ tt ∷ []))

cata-dispatch-id : ∀ st bb n1 l1 at → InitDisc at
                 → InitDisc (cata-trace-of (cata-dispatch st bb n1 l1 at))
cata-dispatch-id strat-const         bb n1 l1 at am = cata-const-id bb n1 l1 at am
cata-dispatch-id strat-nat           bb n1 l1 at am = cata-nat-id bb n1 l1 at am
cata-dispatch-id strat-linear        bb n1 l1 at am = cata-linear-id bb n1 l1 at am
cata-dispatch-id (strat-branching F) bb n1 l1 at am = cata-branching-id F bb n1 l1 at am

------------------------------------------------------------------------
-- THE THEOREM, over arbitrary frontier `n` / label counter `l`.
------------------------------------------------------------------------
-- Plan 0.108: a comparison allocates its sum node, two cells.
sigop-init : ∀ {A B} (si : SigOpInfo A B) (n : ℕ) (m : Maybe CmpOp) → InitDisc (sigop-code si n m)
sigop-init si n nothing  = tt ∷ []
sigop-init si n (just _) = tt ∷ tt ∷ tt ∷ (std (s-slot (apL n (lit 0 1))) s-tag) ▸ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ []

init-trace' : ∀ {A B} (ir : IR A B) (n l : ℕ)
                 → InitDisc (trace-of (ir-to-trace' n l ir))
init-trace' id       n l = tt ∷ []
init-trace' fst      n l = tt ∷ []
init-trace' snd      n l = tt ∷ []
init-trace' terminal n l = []
init-trace' initial  n l = tt ∷ []
init-trace' (g ∘ f)  n l =
  init-++ (init-trace' f _ _) (tt ∷ init-trace' g _ _)
-- Stage G: the stack-shape clause that stood here collapsed onto this
-- same LHS when the pair's mode was dropped, and shadowed the heap one.
init-trace' (⟨ f , g ⟩) n l =
  tt ∷ tt ∷
  init-++ (init-trace' f _ _)
      (tt ∷ tt ∷
       init-++ (init-trace' g _ _)
           (tt ∷ (std (s-slot (apL n (lit 1 3))) (s-slot (apL n (lit 2 3)))) ▸ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ []))
-- D159 UNFLIPPED THIS: the body is a NAMED BLOCK now, not a splice, so these
-- clauses are the closure's own five/ten instructions and nothing else. The
-- recursion into the body moved to `init-blocks` — where it belongs, and
-- where the discipline is actually claimed of the emitted body.
init-trace' (curry b)  n l =
  tt ∷ tt ∷ (std (s-slot (apL n (lit 0 1))) s-code) ▸ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ []
init-trace' apply n l =
  tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ (std (s-slot (apL n (lit 1 2))) (s-slot (apL n (lit 0 2)))) ▸ tt ∷
  tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ []
init-trace' inl n l =
  tt ∷ tt ∷ (std s-tag (s-slot (apL n (lit 0 1)))) ▸ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ []
init-trace' inr n l =
  tt ∷ tt ∷ (std s-tag (s-slot (apL n (lit 0 1)))) ▸ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ []
-- case is FLAT CONTROL since item 6 — plain splices.
init-trace' (case f g) n l =
  init-++ (tt ∷ tt ∷ tt ∷ [])
      (init-++ (init-trace' g _ _)
           (init-++ (tt ∷ tt ∷ tt ∷ tt ∷ [])
                (init-++ (init-trace' f _ _) (tt ∷ []))))
init-trace' (Iter b) n l = tt ∷ tt ∷ tt ∷ init-++ (init-trace' b _ _) (tt ∷ tt ∷ tt ∷ tt ∷ (std (s-slot (apL n (lit 1 3))) (s-slot (apL n (lit 2 3)))) ▸ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ [])
init-trace' (In _)  n l = tt ∷ []
init-trace' (out-μ _) n l = tt ∷ []
-- C1: the algebra is generated at frontier 0 (its own frame).
init-trace' (Cata {F} _ alg) n l =
  cata-dispatch-id (cata-strategy ⌈ F ⌉F) _ _ _ _ (init-trace' alg 0 l)
init-trace' (Out _)        n l = tt ∷ tt ∷ tt ∷ tt ∷ []
-- D189: the same two-cell build as `Ana`, with `id` as the block.
init-trace' (in-ν _)     n l =
  tt ∷ tt ∷ (std (s-slot (apL n (lit 0 1))) s-code) ▸ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ []
-- D189: the ν suspension is `curry`'s closure record cell for cell, so
-- its walk clause is `curry`'s. The coalgebra is a named block, like the
-- closure body, emitted at frontier 0 under the ν's own label.
init-trace' (Ana _ c)      n l =
  tt ∷ tt ∷ (std (s-slot (apL n (lit 0 1))) s-code) ▸ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ []
init-trace' (SigOp si)     n l = sigop-init si n (cmp-of (sem si))
init-trace' (Call _)      n l = tt ∷ []
init-trace' (const fits-int _)   n l = tt ∷ []
init-trace' (const fits-float _) n l = tt ∷ []

------------------------------------------------------------------------
-- THE BLOCK CHANNEL (D160). `init-trace'` covers the ENTRY block; the
-- linked program is `entry ++ c-ret ∷ blocks-layout bodies`, and the emitted
-- closure bodies allocate too. Without this the discipline was CLAIMED of the
-- program and PROVED of its first block — which was invisible only while
-- `bodies` was always empty.
------------------------------------------------------------------------
bodies-of : ℕ × ℕ × AbstractTrace × List (LabelId × ℕ × AbstractTrace)
          → List (LabelId × ℕ × AbstractTrace)
bodies-of (_ , _ , _ , bs) = bs

bud : ℕ × ℕ × AbstractTrace × List (LabelId × ℕ × AbstractTrace) → ℕ
bud (b , _ , _ , _) = b

lab : ℕ × ℕ × AbstractTrace × List (LabelId × ℕ × AbstractTrace) → ℕ
lab (_ , k , _ , _) = k

-- D199: every heap allocation the re-suspension pass emits is the two-cell
-- one, and each is written in its window — except `wf-Prod`'s fresh pair,
-- whose cell 1 is written after the second child's whole re-suspension
-- (plan 0.123: reordered once plan 0.125's proof of it lands). Until then
-- the claim excludes coalgebras with a product layer (`NoProd`). The
-- environment slot is 0, as at every call (`Ana`).
resuspend-id : ∀ (n l : ℕ) (lbl : LabelId) {F} (wf : WellFormedFI F) → NoProd wf
             → InitDisc (proj₂ (proj₂ (resuspend-layer n l lbl 0 wf)))
resuspend-id n l lbl (wf-K _) _ = []
resuspend-id n l lbl wf-Id _ =
  tt ∷ (w-stash (w-restore-slot (λ ()) (w-load (w-restore-stash (w-store (w-load-slot (apL n (lit 0 1)) (w-store-suc w-done))))))) ▸ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷
  tt ∷ (std (s-slot (apL n (lit 2 3))) s-code) ▸ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ []
resuspend-id n l lbl (wf-Prod wfF wfG) ()
resuspend-id n l lbl (wf-Sum wfF wfG) (pF , pG) =
  tt ∷ tt ∷ tt ∷
  init-++ (arm 1 (resuspend-id n2 l2 lbl wfG pG))
      (tt ∷ tt ∷
       init-++ (arm 0 (resuspend-id (suc (suc (suc n))) (suc (suc l)) lbl wfF pF))
           (tt ∷ []))
  where
    n2 = proj₁ (resuspend-layer (suc (suc (suc n))) (suc (suc l)) lbl 0 wfF)
    l2 = proj₁ (proj₂ (resuspend-layer (suc (suc (suc n))) (suc (suc l)) lbl 0 wfF))
    arm : ∀ (tag : ℕ) {t} → InitDisc t
        → InitDisc (restore-input n ∷ load-indirect-suc ∷
                         t ++ (store-at-slot (suc (suc n)) ∷ instr-alloc-heap 2 ∷
                               store-at-slot (suc n) ∷ mov-to-input ∷
                               load-from-slot (suc (suc n)) ∷ store-indirect-suc ∷
                               instr-load-tag-lit tag ∷ store-indirect ∷
                               load-from-slot (suc n) ∷ []))
    arm tag am = tt ∷ tt ∷ init-++ am (tt ∷ (stdr (s-slot (apL' n (lit 1 2))) s-tag) ▸ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ [])

init-blocks : ∀ {A B} (ir : IR A B) (n l : ℕ) → AnaNoProd ir
                 → InitDisc (blocks-layout (bodies-of (ir-to-trace' n l ir)))
init-blocks id       n l _ = []
init-blocks fst      n l _ = []
init-blocks snd      n l _ = []
init-blocks terminal n l _ = []
init-blocks initial  n l _ = []
init-blocks apply    n l _ = []
init-blocks inl n l _ = []
init-blocks inr n l _ = []
init-blocks (In _)   n l _ = []
init-blocks (out-μ _)  n l _ = []
init-blocks (Out _)    n l _ = []
init-blocks (in-ν _) n l _ = tt ∷ tt ∷ tt ∷ []
-- D199: the block is `coalg ++ re-suspension`.
init-blocks (Ana wf c) n l (pw , pc) =
  init-++ (tt ∷ init-++ (tt ∷ tt ∷ (init-++ (init-trace' c 1 (suc l))
                     (resuspend-id (proj₁ (ir-to-trace' 1 (suc l) c))
                                   (proj₁ (proj₂ (ir-to-trace' 1 (suc l) c)))
                                   (ℓ o l) wf pw)))
                (tt ∷ []))
      (init-blocks c 1 (suc l) pc)
init-blocks (SigOp _)      n l _ = []
init-blocks (Call _)      n l _ = []
init-blocks (const fits-int _)   n l _ = []
init-blocks (const fits-float _) n l _ = []
-- the closure's block: `c-thunk`, the body, `c-ret` — then the body's own
init-blocks (curry b) n l pb =
  init-++ (tt ∷ init-++ (init-trace' b 0 (suc (suc l))) (tt ∷ []))
      (init-blocks b 0 (suc (suc l)) pb)
init-blocks (g ∘ f) n l (pg , pf) =
  subst InitDisc (sym (blocks-layout-++ (bodies-of F) (bodies-of G)))
    (init-++ (init-blocks f n l pf) (init-blocks g (bud F) (lab F) pg))
  where F = ir-to-trace' n l f
        G = ir-to-trace' (bud F) (lab F) g
init-blocks (⟨ f , g ⟩) n l (pf , pg) =
  subst InitDisc (sym (blocks-layout-++ (bodies-of F) (bodies-of G)))
    (init-++ (init-blocks f (suc (suc (suc (suc n)))) l pf)
         (init-blocks g (bud F) (lab F) pg))
  where F = ir-to-trace' (suc (suc (suc (suc n)))) l f
        G = ir-to-trace' (bud F) (lab F) g
init-blocks (case f g) n l (pf , pg) =
  subst InitDisc (sym (blocks-layout-++ (bodies-of F) (bodies-of G)))
    (init-++ (init-blocks f n (suc (suc l)) pf) (init-blocks g (bud F) (lab F) pg))
  where F = ir-to-trace' n (suc (suc l)) f
        G = ir-to-trace' (bud F) (lab F) g
init-blocks (Iter b) n l pb = init-blocks b _ _ pb
init-blocks (Cata {F} _ alg) n l pa = init-blocks alg 0 l pa

------------------------------------------------------------------------
-- Corollaries over the public entry points, and the fetch form the
-- flat↔x86-64 correspondence consumes.
------------------------------------------------------------------------
init-at-frontier : ∀ {A B} (ir : IR A B) (n : ℕ) → AnaNoProd ir
                      → InitDisc (ir-to-trace-at-frontier n ir)
init-at-frontier ir n p =
  init-++ (init-trace' ir n 0) (tt ∷ init-blocks ir n 0 p)

ir-to-trace-init : ∀ {A B} (ir : IR A B) → AnaNoProd ir → InitDisc (ir-to-trace ir)
ir-to-trace-init ir = init-at-frontier ir 0

-- D244/D245: …and a program's unit placed at label counter `l`.
ir-to-trace-lab-init : ∀ {A B} (ir : IR A B) (l : ℕ) → AnaNoProd ir → InitDisc (ir-to-trace-lab l ir)
ir-to-trace-lab-init ir l p = init-++ (init-trace' ir 0 l) (tt ∷ init-blocks ir 0 l p)

-- …and the OUTERMOST unit, linked with the program's leave (D320).
ir-to-trace-top-init : ∀ {A B} (ir : IR A B) → AnaNoProd ir → InitDisc (link-top (ir-to-unit ir))
ir-to-trace-top-init ir p = init-++ (init-trace' ir 0 0) (tt ∷ init-blocks ir 0 0 p)

