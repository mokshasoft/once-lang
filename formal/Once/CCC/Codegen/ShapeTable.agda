-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.ShapeTable   (Plan 0.62 M2)
--
-- THE TYPED EXPECTATION TABLE, computed — not hand-written. A transfer
-- function (`step-expect`) abstract-interprets the trace over a small
-- expectation language; the per-pc table is its scan, so trace/table
-- ALIGNMENT is free. Labels carry a supplied `LabelEnv` (the loop
-- invariants — gate G2's artifacts); a BOOLEAN checker (`check-shapes`,
-- the `CataIRSlotStable` decider mold) validates every jump and branch
-- against its target's entry, so the per-emitter fact is a `refl`-heavy
-- walk and the soundness theorem (M3) is per-instruction.
--
-- The language is deliberately small (D076: shapes, not values):
--   e-any     — no claim;
--   e-repr A  — the register holds a representation of `A` (a pointer to a
--               `ShapeAt A` cell block, or a fitting literal, per
--               `RegShapeOf` — the `Meets` interpretation lives in the
--               FS-parameterized half);
--   e-inl A B / e-inr A B — a sum representation REFINED by a taken tag
--               test (the branch fall-through knows inr, the target inl —
--               path-sensitivity is what lets the descend loops type).
--
-- Slots: an association list (finite, decidable) — the scan adds an entry
-- at `store-at-slot`/`worklist-push` and reads it back at
-- `load-from-slot`/`restore-input`/`worklist-pop`. Scratch/Count carry no
-- expectations here (`FlatRegTagWF` owns them).
------------------------------------------------------------------------

module Once.CCC.Codegen.ShapeTable where

open import Data.Nat using (ℕ; suc; zero; _≟_; _+_)
open import Data.Bool using (Bool; true; false; _∧_; if_then_else_)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

open import Once.IRTy using (IRTy; IRFunctor; Unit; Void; Int; Float; Str; Buffer;
  _*_; _⇛_; μ-type; ν-type; K; Id; _⊕_; _⊗_)
  renaming (_+_ to _+ᵗ_)
open import Once.IR using (⟦_⟧TI; IR; AllocMode; Heap; Stack;
  id; _∘_; ⟨_,_⟩; fst; snd; inl; inr; case; terminal; initial;
  curry; apply; In; out-μ; Cata; Para; Out; in-ν; Ana; Hylo; Fuse;
  free-heap; SigOp; const)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Once.CCC.Machine.SMCore using
  (AbstractInstr; AbstractTrace; mov-to-output; mov-to-input;
   load-indirect; load-indirect-suc; load-from-slot; store-at-slot;
   store-indirect; store-indirect-suc; lea-slot; restore-input;
   lea-indexed; instr-alloc-stack; instr-dealloc-stack; instr-push-frame;
   instr-pop-frame; instr-reclaim-to; instr-call-closure; worklist-init;
   worklist-push; worklist-pop; worklist-check; instr-sigop;
   instr-load-const; instr-load-code-addr; instr-save-closure-reg;
   instr-load-tag-lit; instr-alloc-heap; instr-loop; instr-case-on-tag;
   instr-reg-op; instr-ctrl; c-label; c-jmp; c-branch-scratch-zero;
   c-branch-tag-zero; c-thunk; c-ret)
open import Once.CCC.Label using (LabelId)

------------------------------------------------------------------------
-- The expectation language.
------------------------------------------------------------------------

data RegExpect : Set where
  e-any  : RegExpect
  e-repr : IRTy → RegExpect
  e-inl  : IRTy → IRTy → RegExpect
  e-inr  : IRTy → IRTy → RegExpect
  -- a known tag value (`instr-load-tag-lit`)
  e-tag  : ℕ → RegExpect
  -- a pointer to the MOST-RECENTLY-ALLOCATED block, carrying what has been
  -- written into its two cells so far (`nothing` = unwritten). Node
  -- construction lives entirely in this constructor: alloc starts it,
  -- `store-indirect{,-suc}` fill it, and consumers read the carried claims
  -- (completed fresh is consumed UNTYPED; `sub-reg` converts to `e-repr`
  -- at ctrl points only).
  e-fresh : Maybe RegExpect → Maybe RegExpect → RegExpect

SlotEnv : Set
SlotEnv = List (ℕ × RegExpect)

record Expect : Set where
  constructor mkExpect
  field
    e-in1  : RegExpect
    e-out  : RegExpect
    e-slot : SlotEnv
open Expect public

-- slot lookup (default: no claim)
slot-get : SlotEnv → ℕ → RegExpect
slot-get []             k = e-any
slot-get ((j , e) ∷ es) k with j ≟ k
... | yes _ = e
... | no  _ = slot-get es k

slot-put : SlotEnv → ℕ → RegExpect → SlotEnv
slot-put es k e = (k , e) ∷ es

-- The label environment: the invariant the program claims at each label.
-- Supplied by the emitter walk (the G2 loop invariants live here).
LabelEnv : Set
LabelEnv = LabelId → Expect

------------------------------------------------------------------------
-- Decidable syntactic equality of IRTy (structural; needed by the
-- entailment check). `Functor` equality is required underneath μ/ν.
------------------------------------------------------------------------
func-eq : IRFunctor → IRFunctor → Bool
ty-eq : IRTy → IRTy → Bool

func-eq (K a)   (K b)   = ty-eq a b
func-eq Id      Id      = true
func-eq (f ⊕ g) (h ⊕ i) = func-eq f h ∧ func-eq g i
func-eq (f ⊗ g) (h ⊗ i) = func-eq f h ∧ func-eq g i
func-eq _       _       = false

ty-eq Unit      Unit      = true
ty-eq Int       Int       = true
ty-eq Float     Float     = true
ty-eq Str       Str       = true
ty-eq Buffer    Buffer    = true
ty-eq (a * b)   (c * d)   = ty-eq a c ∧ ty-eq b d
ty-eq (a +ᵗ b)  (c +ᵗ d)  = ty-eq a c ∧ ty-eq b d
ty-eq (a ⇛ b)   (c ⇛ d)   = ty-eq a c ∧ ty-eq b d
ty-eq (μ-type f) (μ-type g) = func-eq f g
ty-eq (ν-type f) (ν-type g) = func-eq f g
ty-eq _         _         = false

nat-eq : ℕ → ℕ → Bool
nat-eq zero    zero    = true
nat-eq (suc a) (suc b) = nat-eq a b
nat-eq _       _       = false

-- entailment on register expectations: anything entails e-any; otherwise
-- syntactic equality (refinements entail their unrefined sum).
sub-reg : RegExpect → RegExpect → Bool
sub-reg _            e-any        = true
sub-reg (e-repr a)   (e-repr b)   = ty-eq a b
sub-reg (e-inl a b)  (e-inl c d)  = ty-eq a c ∧ ty-eq b d
sub-reg (e-inr a b)  (e-inr c d)  = ty-eq a c ∧ ty-eq b d
sub-reg (e-inl a b)  (e-repr c)   = ty-eq (a +ᵗ b) c
sub-reg (e-inr a b)  (e-repr c)   = ty-eq (a +ᵗ b) c
sub-reg (e-tag m)    (e-tag n)    = nat-eq m n
-- COMPLETED fresh converts to a typed representation at check points: a
-- sum node needs tag 0/1 + a payload cell claiming the branch type; a pair
-- needs both cells claiming the component types. Cell claims are PTR-only
-- (`MeetsCell`), so the conversion demands `e-repr` cells exactly.
sub-reg (e-fresh (just (e-tag zero)) (just (e-repr p))) (e-repr (a +ᵗ b)) = ty-eq p a
sub-reg (e-fresh (just (e-tag (suc zero))) (just (e-repr p))) (e-repr (a +ᵗ b)) = ty-eq p b
sub-reg (e-fresh (just (e-repr p)) (just (e-repr q))) (e-repr (a * b)) = ty-eq p a ∧ ty-eq q b
sub-reg _            _            = false

-- entailment on whole expectations: registers pointwise; every slot claim
-- of the TARGET must be entailed by the source's claim for that slot.
sub-slots : SlotEnv → SlotEnv → Bool
sub-slots src []             = true
sub-slots src ((k , e) ∷ es) = sub-reg (slot-get src k) e ∧ sub-slots src es

sub-expect : Expect → Expect → Bool
sub-expect s t = sub-reg (e-in1 s) (e-in1 t)
               ∧ sub-reg (e-out s) (e-out t)
               ∧ sub-slots (e-slot s) (e-slot t)

------------------------------------------------------------------------
-- Type-driven projections the transfer needs.
------------------------------------------------------------------------

-- the sum view of a TYPE (aux-style — no `with`, so it inverts)
as-sum-of : IRTy → Maybe (IRTy × IRTy)
as-sum-of (a +ᵗ b) = just (a , b)
as-sum-of _        = nothing

as-sum-of-inv : ∀ T {a b} → as-sum-of T ≡ just (a , b) → T ≡ (a +ᵗ b)
as-sum-of-inv (a +ᵗ b) refl = refl

-- view a representation expectation as a SUM (unfolding one μ/ν layer —
-- the μ node IS its layer, `shape-μ`)
as-sum : RegExpect → Maybe (IRTy × IRTy)
as-sum (e-repr (a +ᵗ b))   = just (a , b)
as-sum (e-repr (μ-type f)) = as-sum-of (⟦ f ⟧TI (μ-type f))
as-sum (e-repr (ν-type f)) = as-sum-of (⟦ f ⟧TI (ν-type f))
as-sum _ = nothing

-- is this claim certainly a pointer? (the load/store site requirement)
is-ptr : RegExpect → Bool
is-ptr (e-repr (a * b))  = true
is-ptr (e-repr (a ⇛ b))  = true
is-ptr (e-repr (μ-type f)) = true
is-ptr (e-repr (ν-type f)) = true
is-ptr (e-repr (a +ᵗ b)) = true
is-ptr (e-inl a b)       = true
is-ptr (e-inr a b)       = true
is-ptr (e-fresh _ _)     = true
is-ptr _                 = false

-- the shape of cell 0 seen through a load (`load-indirect`): pairs yield
-- the first component's representation; a fresh block yields its carried
-- cell claim; closures yield the env pointer (its type is existential, so:
-- no claim); everything else: no claim.
fst-of : IRTy → RegExpect
fst-of (a * b) = e-repr a
fst-of _       = e-any

load-fst : RegExpect → RegExpect
load-fst (e-repr (a * b)) = e-repr a
load-fst (e-fresh (just c₀) _) = c₀
load-fst (e-repr (μ-type f)) = fst-of (⟦ f ⟧TI (μ-type f))
load-fst _ = e-any

-- cell 1 through `load-indirect-suc`: pairs yield the second component; a
-- REFINED sum yields its payload (this is the descend-loop step, G2).
snd-of : IRTy → RegExpect
snd-of (a * b) = e-repr b
snd-of _       = e-any

load-snd : RegExpect → RegExpect
load-snd (e-repr (a * b)) = e-repr b
load-snd (e-inl a b)      = e-repr a
load-snd (e-inr a b)      = e-repr b
load-snd (e-fresh _ (just c₁)) = c₁
load-snd (e-repr (μ-type f)) = snd-of (⟦ f ⟧TI (μ-type f))
load-snd _ = e-any

------------------------------------------------------------------------
-- The transfer function: what holds AFTER one instruction, given what
-- holds before. Conservative (`e-any`) wherever the machine writes
-- something the language does not track.
------------------------------------------------------------------------

step-expect : LabelEnv → Expect → AbstractInstr → Expect
step-expect env st mov-to-output =
  record st { e-out = e-in1 st }
step-expect env st mov-to-input =
  record st { e-in1 = e-out st }
step-expect env st load-indirect =
  record st { e-out = load-fst (e-in1 st) }
step-expect env st load-indirect-suc =
  record st { e-out = load-snd (e-in1 st) }
step-expect env st (load-from-slot k) =
  record st { e-out = slot-get (e-slot st) k }
step-expect env st (store-at-slot k) =
  record st { e-slot = slot-put (e-slot st) k (e-out st) }
-- a heap store writes MEMORY, not a tracked register; the written cell's
-- shape obligations are M3's business (heap evolution), the register
-- claims survive
-- a store through a FRESH pointer fills the carried cell claim; the
-- register claims survive (the written cell is the unclaimed block's —
-- every live claim is elsewhere). Non-fresh heap stores are rejected by
-- `site-ok` (the emitter's init discipline: allocate, fill, only then
-- share).
step-expect env st store-indirect with e-in1 st
... | e-fresh c₀ c₁ = record st { e-in1 = e-fresh (just (e-out st)) c₁ }
... | _             = st
step-expect env st store-indirect-suc with e-in1 st
... | e-fresh c₀ c₁ = record st { e-in1 = e-fresh c₀ (just (e-out st)) }
... | _             = st
step-expect env st (lea-slot k) =
  record st { e-out = e-any }
step-expect env st (restore-input k) =
  record st { e-in1 = slot-get (e-slot st) k }
step-expect env st (lea-indexed k)     = st    -- unemittable
step-expect env st (instr-alloc-stack n)   = st    -- unemittable
step-expect env st (instr-dealloc-stack n) = st    -- unemittable
step-expect env st (instr-push-frame n)    = st    -- unemittable
step-expect env st instr-pop-frame         = st    -- unemittable
step-expect env st (instr-reclaim-to n)    = st
step-expect env st instr-call-closure =
  -- the call's result contract is the model gap (`events-running-call`);
  -- no claim survives it
  mkExpect e-any e-any []
step-expect env st (worklist-init k) = st
step-expect env st (worklist-push k) =
  record st { e-slot = slot-put (e-slot st) k (e-out st) }
step-expect env st (worklist-pop k) =
  record st { e-out = slot-get (e-slot st) k }
step-expect env st (worklist-check k) = st
step-expect env st (instr-sigop si) =
  record st { e-out = e-any }
step-expect env st (instr-load-const p v) =
  record st { e-out = e-any }
step-expect env st (instr-load-code-addr n) =
  record st { e-out = e-any }
step-expect env st instr-save-closure-reg = st
step-expect env st (instr-load-tag-lit n) =
  record st { e-out = e-tag n }
-- a NEW allocation supersedes the previous "newest block": every live
-- fresh claim is scrubbed (one block under construction at a time)
step-expect env st (instr-alloc-heap n) =
  record (scrub-expect st) { e-out = e-fresh nothing nothing }
  where
    scrub : RegExpect → RegExpect
    scrub (e-fresh _ _) = e-any
    scrub e             = e
    scrub-slots : SlotEnv → SlotEnv
    scrub-slots []             = []
    scrub-slots ((k , e) ∷ es) = (k , scrub e) ∷ scrub-slots es
    scrub-expect : Expect → Expect
    scrub-expect e = mkExpect (scrub (e-in1 e))
                              (scrub (e-out e)) (scrub-slots (e-slot e))
step-expect env st (instr-loop b)          = st    -- unemittable
step-expect env st (instr-case-on-tag f g) = st    -- unemittable
step-expect env st (instr-reg-op op) = st
-- CONTROL. A label ADOPTS its environment entry (the join point's claim —
-- the fall-in path's obligation to entail it is the checker's job). A jump
-- transfers nowhere (the next pc is unreachable from here; its entry comes
-- from its own label/fall-in). Branches refine the scrutinee.
step-expect env st (instr-ctrl (c-label m)) = env m
-- Plan 0.63. A closure-body entry is reached from a CALL, which this layer
-- does not model yet (`ir-to-trace` is main-only, so `c-thunk` has no
-- producer). Claim NOTHING there rather than adopting a jump label's entry
-- from a namespace it does not belong to: the empty expectation is met by
-- every state, so the walk stays sound. Step 2, which emits the bodies,
-- owns giving body entries a real per-body entry claim (and `c-ret` a real
-- obligation against the caller's continuation).
step-expect env st (instr-ctrl (c-thunk m b)) = mkExpect e-any e-any []
-- after a return the fall-through is dead, exactly as after `c-jmp`
step-expect env st (instr-ctrl (c-ret b)) = mkExpect e-any e-any []
step-expect env st (instr-ctrl (c-jmp m)) =
  -- fall-through after an unconditional jump is dead until the next label;
  -- no claim
  mkExpect e-any e-any []
step-expect env st (instr-ctrl (c-branch-scratch-zero m)) = st
step-expect env st (instr-ctrl (c-branch-tag-zero m)) with e-in1 st
... | e-fresh c₀ c₁ = st                     -- statically-decided tag: no refinement needed
... | e₁ with as-sum e₁
...   | just (a , b) = record st { e-in1 = e-inr a b }   -- fall-through = inr
...   | nothing      = st

------------------------------------------------------------------------
-- The checker: scan the trace, validating every control transfer against
-- the label environment. `true` means: every jump/branch source entails
-- its target's entry, and every discipline site's requirement is met by
-- the incoming state. The soundness theorem (M3) turns this Bool into the
-- run-level invariant.
------------------------------------------------------------------------

-- what a discipline site REQUIRES of the incoming state
is-fresh : RegExpect → Bool
is-fresh (e-fresh _ _) = true
is-fresh _             = false

is-just : ∀ {A : Set} → Maybe A → Bool
is-just (just _) = true
is-just nothing  = false

-- the branch-site requirement: a statically-known tag (completed fresh) or
-- a sum-viewed representation
tag-site-ok : RegExpect → Bool
tag-site-ok (e-fresh (just (e-tag t)) c₁) = true
tag-site-ok (e-fresh _ _)                 = false
tag-site-ok e₁                            = is-just (as-sum e₁)

-- A SLOT READ REQUIRES A CLAIM (Plan 0.54 rung D). `MeetsSlot e-any … = ⊤`
-- permits an UNWRITTEN slot, so without this a checked program could read a
-- slot the abstract machine never wrote — where the abstract machine halts
-- (`readLoc ≡ nothing`) and the concrete one reads whatever the previous frame
-- left behind. That is a genuine DIVERGENCE, not merely an unprovable case, and
-- it is what the old bidirectional `Window` was hiding: it asserted the concrete
-- cell was unmapped too, so both sides "agreed" by getting stuck together.
--
-- With `Window` one-directional the divergence is visible, and the honest fix is
-- for the emitter's own discipline to rule the read out. Every non-`e-any`
-- claim makes `MeetsSlot … nothing` uninhabited, so this conjunct is exactly
-- what refutes the empty-slot routes.
not-any : RegExpect → Bool
not-any e-any = false
not-any _     = true

site-ok : Expect → AbstractInstr → Bool
site-ok st load-indirect     = is-ptr (e-in1 st)
site-ok st load-indirect-suc = is-ptr (e-in1 st)
site-ok st (load-from-slot k) = not-any (slot-get (e-slot st) k)
site-ok st (restore-input k)  = not-any (slot-get (e-slot st) k)
site-ok st (worklist-pop k)   = not-any (slot-get (e-slot st) k)
-- heap stores go through the block under construction ONLY (init discipline)
site-ok st store-indirect     = is-fresh (e-in1 st)
site-ok st store-indirect-suc = is-fresh (e-in1 st)
site-ok st (instr-ctrl (c-branch-tag-zero m)) = tag-site-ok (e-in1 st)
site-ok st _ = true

-- control-transfer obligation of one instruction: jumps and taken branches
-- must entail the target's entry
ctrl-ok : LabelEnv → Expect → AbstractInstr → Bool
ctrl-ok env st (instr-ctrl (c-jmp m)) = sub-expect st (env m)
ctrl-ok env st (instr-ctrl (c-branch-scratch-zero m)) = sub-expect st (env m)
ctrl-ok env st (instr-ctrl (c-branch-tag-zero m)) with e-in1 st
-- tag 0 known: the branch is ALWAYS taken — only the target obligation
... | e-fresh (just (e-tag zero)) c₁ = sub-expect st (env m)
-- nonzero tag known: never taken — no obligation at all
... | e-fresh (just (e-tag (suc t))) c₁ = true
... | e-fresh c₀ c₁ = false
... | e₁ with as-sum e₁
...   | just (a , b) = sub-expect (record st { e-in1 = e-inl a b }) (env m)
...   | nothing      = false
-- a label is a join point: the FALL-IN state must entail the adopted entry
ctrl-ok env st (instr-ctrl (c-label m)) = sub-expect st (env m)
-- Plan 0.63: a body entry claims nothing (see `step-expect`) so falling in
-- entails it trivially; a return transfers to a pc this layer does not
-- track. Both are vacuous while `c-thunk`/`c-ret` have no producer — step 2
-- replaces them with the per-body entry/return obligations.
ctrl-ok env st (instr-ctrl (c-thunk m b)) = true
ctrl-ok env st (instr-ctrl (c-ret b)) = true
ctrl-ok env st _ = true

check-shapes : LabelEnv → Expect → AbstractTrace → Bool
check-shapes env st []       = true
check-shapes env st (i ∷ is) =
  site-ok st i ∧ ctrl-ok env st i ∧ check-shapes env (step-expect env st i) is

-- the computed per-pc table (alignment with the trace is `scan-length`)
scan-expect : LabelEnv → Expect → AbstractTrace → List Expect
scan-expect env st []       = []
scan-expect env st (i ∷ is) = st ∷ scan-expect env (step-expect env st i) is

scan-length : ∀ env st t → length (scan-expect env st t) ≡ length t
scan-length env st []       = refl
scan-length env st (i ∷ is) rewrite scan-length env (step-expect env st i) is = refl

------------------------------------------------------------------------
-- Compositionality of the scan/check over `++` (every emitter clause is a
-- splice; these are the bricks its walk is made of).
------------------------------------------------------------------------

post-expect : LabelEnv → Expect → AbstractTrace → Expect
post-expect env st []       = st
post-expect env st (i ∷ is) = post-expect env (step-expect env st i) is

check-++ : ∀ env st t₁ t₂
         → check-shapes env st (t₁ ++ t₂)
           ≡ check-shapes env st t₁ ∧ check-shapes env (post-expect env st t₁) t₂
check-++ env st [] t₂ = refl
check-++ env st (i ∷ is) t₂
  rewrite check-++ env (step-expect env st i) is t₂
  = ∧-assoc₂ (site-ok st i) (ctrl-ok env st i) _ _
  where
    ∧-assoc₂ : ∀ (a b c d : Bool) → a ∧ b ∧ (c ∧ d) ≡ (a ∧ b ∧ c) ∧ d
    ∧-assoc₂ false b c d = refl
    ∧-assoc₂ true false c d = refl
    ∧-assoc₂ true true c d = refl

post-++ : ∀ env st t₁ t₂
        → post-expect env st (t₁ ++ t₂) ≡ post-expect env (post-expect env st t₁) t₂
post-++ env st []       t₂ = refl
post-++ env st (i ∷ is) t₂ = post-++ env (step-expect env st i) is t₂

------------------------------------------------------------------------
-- HEAP-MODEDNESS: every `AllocMode` argument in the IR is `Heap`. The
-- checker's claims are heap-shaped (a stack-mode shape mentions stack
-- cells, which `store-at-slot` clobbers while the transfer keeps the
-- claim), so the emitter shape check is CONDITIONAL on this predicate —
-- supplied at the apex from the pipeline (`compileFromModule C.Heap`).
------------------------------------------------------------------------
IsHeap : AllocMode → Set
IsHeap Heap  = ⊤
IsHeap Stack = ⊥

HeapModed : ∀ {A B} → IR A B → Set
HeapModed id        = ⊤
HeapModed fst       = ⊤
HeapModed snd       = ⊤
HeapModed terminal  = ⊤
HeapModed initial   = ⊤
HeapModed apply     = ⊤
HeapModed (g ∘ f)   = HeapModed f × HeapModed g
HeapModed (⟨ f , g ⟩ m) = IsHeap m × HeapModed f × HeapModed g
HeapModed (curry b m)   = IsHeap m × HeapModed b
HeapModed (inl m)   = IsHeap m
HeapModed (inr m)   = IsHeap m
HeapModed (case f g) = HeapModed f × HeapModed g
HeapModed (In _ m)  = IsHeap m
HeapModed (out-μ _) = ⊤
HeapModed (Cata _ alg) = HeapModed alg
HeapModed (Para _ alg) = HeapModed alg
HeapModed (Out _)   = ⊤
HeapModed (in-ν _ m) = IsHeap m
HeapModed (Ana _ coalg) = HeapModed coalg
HeapModed (Hylo _ _ alg _) = HeapModed alg
HeapModed (Fuse _ _ alg _) = HeapModed alg
HeapModed (free-heap _) = ⊤
HeapModed (SigOp _) = ⊤
HeapModed (const _ _) = ⊤

-- the entry expectation of a fragment with input type `A` (`main`'s is
-- `entry-expect Unit`, which the D074 all-tag entry state meets via
-- `rs-unit`)
entry-expect : IRTy → Expect
entry-expect A = mkExpect (e-repr A) e-any []

------------------------------------------------------------------------
-- THE SITE EXTRACTION (FS-free): a positive check localizes — at every
-- position of the trace, the scanned state passes `site-ok`/`ctrl-ok`.
-- `state-at` is the scan's state at a pc; the flat machine's `fetch` is
-- list lookup, mirrored here as `at-pc` (the FS half proves them equal).
------------------------------------------------------------------------

at-pc : AbstractTrace → ℕ → Maybe AbstractInstr
at-pc []       k       = nothing
at-pc (i ∷ is) zero    = just i
at-pc (i ∷ is) (suc k) = at-pc is k

state-at : LabelEnv → Expect → AbstractTrace → ℕ → Expect
state-at env st []       k       = st
state-at env st (i ∷ is) zero    = st
state-at env st (i ∷ is) (suc k) = state-at env (step-expect env st i) is k

∧-split : ∀ (a b : Bool) → a ∧ b ≡ true → a ≡ true × b ≡ true
∧-split true  true  refl = refl , refl
∧-split true  false ()
∧-split false b     ()

check-at : ∀ env st t k {i}
         → check-shapes env st t ≡ true
         → at-pc t k ≡ just i
         → site-ok (state-at env st t k) i ≡ true
           × ctrl-ok env (state-at env st t k) i ≡ true
check-at env st []       k       ok ()
check-at env st (i ∷ is) zero    ok refl =
  proj₁ (∧-split (site-ok st i) _ ok) ,
  proj₁ (∧-split (ctrl-ok env st i) _
          (proj₂ (∧-split (site-ok st i) _ ok)))
check-at env st (i ∷ is) (suc k) ok fq =
  check-at env (step-expect env st i) is k
    (proj₂ (∧-split (ctrl-ok env st i) _
             (proj₂ (∧-split (site-ok st i) _ ok)))) fq

------------------------------------------------------------------------
-- THE INTERPRETATION (`Meets`) — the FS-parameterized half: what it MEANS
-- for a machine state to satisfy an expectation. Register claims interpret
-- through `RegShape` (a representation of `A`: a pointer to a `ShapeAt A`
-- block, a fitting literal, or anything for `Unit` — `InputAt`'s three
-- routes, shape-only); refined sum claims through the constructor-refined
-- records `InlAt`/`InrAt`; slot claims through `slot-get` (so shadowed
-- association-list entries carry no obligation).
------------------------------------------------------------------------

open import Once.CCC.FrameSemantics using (FrameSemantics)

module Sem (FS : FrameSemantics) where
  open import Data.Unit using (⊤; tt)
  open import Data.Empty using (⊥; ⊥-elim)
  open import Once.Type using ()
    renaming (fits-int to fits-intˢ; fits-float to fits-floatˢ)
  open import Once.CCC.Machine.SMCore as SM using
    (LocState; ValueLocation; StoredValue; SV-Ptr; SV-Tag; SV-Lit; SV-Code;
     AtStack; AtDynamic; sucLoc; regs; readReg; Input1; Output;
     stackMem; heapMem; current-frame; AllocState; next-heap-ref)
  open import Once.Memory.HeapAddress
    using (HeapLocation; heap-loc; mkHeapRef; heap-ref; heap-offset; ref-id; sucHL)
  open import Data.Nat using (suc; zero; _<_; s≤s; z≤n)
  open import Data.Nat.Properties using (≤-refl)
  open SM.MemOps {FS} using (readLoc)
  open import Once.CCC.Machine.Flat using (module FlatMachine)
  open FlatMachine {FS} using (FlatState; floc; falloc; fetch; fpc)
  open import Once.CCC.Machine.ShapeAt FS using
    (ShapeAt; TagAt; tag-at-read;
     shape-unit; shape-pair; shape-closure; shape-inl; shape-inr;
     shape-inl-reg; shape-inr-reg;
     shape-μ; shape-ν; shape-int; shape-float; shape-str; shape-buffer)
  open import Once.CCC.Machine.LocMatchesMode using (LocMatchesMode)
  open import Once.CCC.Machine.Allocation using (module FrontierInvariant)
  open FrontierInvariant {FS} using (BeforeFrontier; heap-before)
  open import Once.IR using (AllocMode; Heap; Stack)

  -- the register-resident representation of a type (shape-only `InputAt`)
  data RegShape (alloc : AllocState {FS}) (ls : LocState FS)
       : IRTy → StoredValue FS → Set where
    rs-unit  : ∀ {v} → RegShape alloc ls Unit v
    rs-ptr   : ∀ {A m loc} → ShapeAt m alloc A loc ls
             → RegShape alloc ls A (SV-Ptr loc)
    rs-int   : ∀ {n} → RegShape alloc ls Int (SV-Lit fits-intˢ n)
    rs-float : ∀ {x} → RegShape alloc ls Float (SV-Lit fits-floatˢ x)

  -- the REFINED sum node (the fields of `shape-inl`/`shape-inr`, as records
  -- so a branch's knowledge survives as data)
  record InlAt (alloc : AllocState {FS}) (A B : IRTy)
               (loc : ValueLocation FS) (ls : LocState FS) : Set where
    field
      {i-m i-mA}  : AllocMode
      {i-payload} : ValueLocation FS
      i-mode : LocMatchesMode i-m loc
      i-tag  : TagAt i-m 0 ls loc
      i-cell : readLoc ls (sucLoc loc) ≡ just (SV-Ptr i-payload)
      i-bf-p : BeforeFrontier alloc i-payload
      i-bf-s : BeforeFrontier alloc (sucLoc loc)
      i-pay  : ShapeAt i-mA alloc A i-payload ls

  record InrAt (alloc : AllocState {FS}) (A B : IRTy)
               (loc : ValueLocation FS) (ls : LocState FS) : Set where
    field
      {r-m r-mB}  : AllocMode
      {r-payload} : ValueLocation FS
      r-mode : LocMatchesMode r-m loc
      r-tag  : TagAt r-m 1 ls loc
      r-cell : readLoc ls (sucLoc loc) ≡ just (SV-Ptr r-payload)
      r-bf-p : BeforeFrontier alloc r-payload
      r-bf-s : BeforeFrontier alloc (sucLoc loc)
      r-pay  : ShapeAt r-mB alloc B r-payload ls

  -- CELL claims are PTR-only for `e-repr` (mirrors the `SV-Ptr` cells of
  -- `shape-inl`/`valid-pair-wf` — a heap cell of a node never holds a bare
  -- literal representation in the reference-based model), and the fresh
  -- interpretation is mutual with them (a fresh block's cells carry claims).
  MeetsR : RegExpect → AllocState {FS} → StoredValue FS → LocState FS → Set
  MeetsCell : RegExpect → AllocState {FS} → Maybe (StoredValue FS) → LocState FS → Set
  MCell : Maybe RegExpect → AllocState {FS} → Maybe (StoredValue FS) → LocState FS → Set
  FreshAt : Maybe RegExpect → Maybe RegExpect → AllocState {FS}
          → StoredValue FS → LocState FS → Set

  MeetsR e-any       alloc v ls = ⊤
  MeetsR (e-repr A)  alloc v ls = RegShape alloc ls A v
  MeetsR (e-inl A B) alloc v ls =
    Σ (ValueLocation FS) λ loc → (v ≡ SV-Ptr loc) × InlAt alloc A B loc ls
  MeetsR (e-inr A B) alloc v ls =
    Σ (ValueLocation FS) λ loc → (v ≡ SV-Ptr loc) × InrAt alloc A B loc ls
  MeetsR (e-tag t)   alloc v ls = v ≡ SV-Tag t
  MeetsR (e-fresh c₀ c₁) alloc v ls = FreshAt c₀ c₁ alloc v ls

  MeetsCell e-any       alloc mc ls = ⊤
  MeetsCell (e-repr A)  alloc mc ls =
    Σ (ValueLocation FS) λ loc → (mc ≡ just (SV-Ptr loc))
      × BeforeFrontier alloc loc
      × Σ AllocMode λ m → ShapeAt m alloc A loc ls
  MeetsCell (e-inl A B) alloc mc ls =
    Σ (ValueLocation FS) λ loc → (mc ≡ just (SV-Ptr loc))
      × BeforeFrontier alloc loc × InlAt alloc A B loc ls
  MeetsCell (e-inr A B) alloc mc ls =
    Σ (ValueLocation FS) λ loc → (mc ≡ just (SV-Ptr loc))
      × BeforeFrontier alloc loc × InrAt alloc A B loc ls
  MeetsCell (e-tag t)   alloc mc ls = mc ≡ just (SV-Tag t)
  -- a fresh claim stored INTO a heap cell cannot arise (the scrub keeps a
  -- single fresh live, and a block never stores its own construction
  -- pointer); ⊥ keeps the transfer honest — if the scan ever produces it,
  -- soundness fails THERE instead of being papered over.
  MeetsCell (e-fresh c₀ c₁) alloc mc ls = ⊥

  -- inside a FRESH block, a `nothing` claim means the cell is genuinely
  -- UNWRITTEN — this is what makes the store-soundness brick go through: a
  -- write to an unwritten cell cannot invalidate any claim (every claim's
  -- read-equation on that cell would be `nothing ≡ just …`).
  MCell nothing  alloc mc ls = mc ≡ nothing
  MCell (just c) alloc mc ls = MeetsCell c alloc mc ls

  -- the newest block: block start, ref just below the frontier, cells per
  -- the carried claims
  FreshAt c₀ c₁ alloc v ls =
    Σ HeapLocation λ hl → (v ≡ SV-Ptr (AtDynamic hl))
      × (heap-offset hl ≡ 0)
      × (suc (ref-id (heap-ref hl)) ≡ next-heap-ref alloc)
      × MCell c₀ alloc (heapMem ls hl) ls
      × MCell c₁ alloc (heapMem ls (sucHL hl)) ls

  MeetsSlot : RegExpect → AllocState {FS} → Maybe (StoredValue FS)
            → LocState FS → Set
  MeetsSlot e-any alloc mv       ls = ⊤
  MeetsSlot (e-repr A)   alloc (just v) ls = MeetsR (e-repr A) alloc v ls
  MeetsSlot (e-inl A B)  alloc (just v) ls = MeetsR (e-inl A B) alloc v ls
  MeetsSlot (e-inr A B)  alloc (just v) ls = MeetsR (e-inr A B) alloc v ls
  MeetsSlot (e-tag t)    alloc (just v) ls = MeetsR (e-tag t) alloc v ls
  MeetsSlot (e-fresh c₀ c₁) alloc (just v) ls = MeetsR (e-fresh c₀ c₁) alloc v ls
  MeetsSlot (e-repr A)   alloc nothing  ls = ⊥
  MeetsSlot (e-inl A B)  alloc nothing  ls = ⊥
  MeetsSlot (e-inr A B)  alloc nothing  ls = ⊥
  MeetsSlot (e-tag t)    alloc nothing  ls = ⊥
  MeetsSlot (e-fresh c₀ c₁) alloc nothing ls = ⊥

  Meets : Expect → FlatState → Set
  Meets e fs =
    MeetsR (e-in1 e) (falloc fs) (readReg (regs (floc fs)) Input1) (floc fs)
    × MeetsR (e-out e) (falloc fs) (readReg (regs (floc fs)) Output) (floc fs)
    × (∀ k → MeetsSlot (slot-get (e-slot e) k) (falloc fs)
              (stackMem (floc fs) (current-frame (falloc fs)) k) (floc fs))

  ------------------------------------------------------------------------
  -- ENTAILMENT SOUNDNESS (the jump/branch cases of M3): a `true` from
  -- `sub-expect` really is semantic entailment. `ty-eq`/`func-eq` are sound
  -- (boolean equality reflects propositional equality), a refinement
  -- entails its unrefined sum (`shape-inl`/`shape-inr` intro), and slot
  -- claims transfer through `slot-get`.
  ------------------------------------------------------------------------
  func-eq-sound : ∀ f g → func-eq f g ≡ true → f ≡ g
  ty-eq-sound : ∀ a b → ty-eq a b ≡ true → a ≡ b

  func-eq-sound (K a) (K b) ok rewrite ty-eq-sound a b ok = refl
  func-eq-sound Id Id ok = refl
  func-eq-sound (f ⊕ g) (h ⊕ i) ok
    rewrite func-eq-sound f h (proj₁ (∧-split (func-eq f h) _ ok))
          | func-eq-sound g i (proj₂ (∧-split (func-eq f h) _ ok)) = refl
  func-eq-sound (f ⊗ g) (h ⊗ i) ok
    rewrite func-eq-sound f h (proj₁ (∧-split (func-eq f h) _ ok))
          | func-eq-sound g i (proj₂ (∧-split (func-eq f h) _ ok)) = refl
  func-eq-sound (K _) Id ()
  func-eq-sound (K _) (_ ⊕ _) ()
  func-eq-sound (K _) (_ ⊗ _) ()
  func-eq-sound Id (K _) ()
  func-eq-sound Id (_ ⊕ _) ()
  func-eq-sound Id (_ ⊗ _) ()
  func-eq-sound (_ ⊕ _) (K _) ()
  func-eq-sound (_ ⊕ _) Id ()
  func-eq-sound (_ ⊕ _) (_ ⊗ _) ()
  func-eq-sound (_ ⊗ _) (K _) ()
  func-eq-sound (_ ⊗ _) Id ()
  func-eq-sound (_ ⊗ _) (_ ⊕ _) ()

  ty-eq-sound Unit Unit ok = refl
  ty-eq-sound Int Int ok = refl
  ty-eq-sound Float Float ok = refl
  ty-eq-sound Str Str ok = refl
  ty-eq-sound Buffer Buffer ok = refl
  ty-eq-sound (a * b) (c * d) ok
    rewrite ty-eq-sound a c (proj₁ (∧-split (ty-eq a c) _ ok))
          | ty-eq-sound b d (proj₂ (∧-split (ty-eq a c) _ ok)) = refl
  ty-eq-sound (a +ᵗ b) (c +ᵗ d) ok
    rewrite ty-eq-sound a c (proj₁ (∧-split (ty-eq a c) _ ok))
          | ty-eq-sound b d (proj₂ (∧-split (ty-eq a c) _ ok)) = refl
  ty-eq-sound (a ⇛ b) (c ⇛ d) ok
    rewrite ty-eq-sound a c (proj₁ (∧-split (ty-eq a c) _ ok))
          | ty-eq-sound b d (proj₂ (∧-split (ty-eq a c) _ ok)) = refl
  ty-eq-sound (μ-type f) (μ-type g) ok rewrite func-eq-sound f g ok = refl
  ty-eq-sound (ν-type f) (ν-type g) ok rewrite func-eq-sound f g ok = refl

  nat-eq-sound : ∀ m n → nat-eq m n ≡ true → m ≡ n
  nat-eq-sound zero zero ok = refl
  nat-eq-sound (suc a) (suc b) ok rewrite nat-eq-sound a b ok = refl

  -- a refinement rebuilds its sum shape (`shape-inl` / `shape-inr` intro)

  inl-shape : ∀ {alloc A B loc ls} (r : InlAt alloc A B loc ls)
            → ShapeAt (InlAt.i-m r) alloc (A +ᵗ B) loc ls
  inl-shape r = shape-inl (InlAt.i-mode r) (InlAt.i-tag r) (InlAt.i-cell r)
                          (InlAt.i-bf-p r) (InlAt.i-bf-s r) (InlAt.i-pay r)

  inr-shape : ∀ {alloc A B loc ls} (r : InrAt alloc A B loc ls)
            → ShapeAt (InrAt.r-m r) alloc (A +ᵗ B) loc ls
  inr-shape r = shape-inr (InrAt.r-mode r) (InrAt.r-tag r) (InrAt.r-cell r)
                          (InrAt.r-bf-p r) (InrAt.r-bf-s r) (InrAt.r-pay r)

  sub-reg-sound : ∀ e e' {alloc v ls} → sub-reg e e' ≡ true
                → MeetsR e alloc v ls → MeetsR e' alloc v ls
  sub-reg-sound e e-any ok m = tt
  sub-reg-sound (e-repr a) (e-repr b) ok m
    rewrite ty-eq-sound a b ok = m
  sub-reg-sound (e-inl a b) (e-inl c d) ok m
    rewrite ty-eq-sound a c (proj₁ (∧-split (ty-eq a c) _ ok))
          | ty-eq-sound b d (proj₂ (∧-split (ty-eq a c) _ ok)) = m
  sub-reg-sound (e-inr a b) (e-inr c d) ok m
    rewrite ty-eq-sound a c (proj₁ (∧-split (ty-eq a c) _ ok))
          | ty-eq-sound b d (proj₂ (∧-split (ty-eq a c) _ ok)) = m
  sub-reg-sound (e-inl a b) (e-repr c) ok (loc , v-eq , r)
    rewrite sym (ty-eq-sound (a +ᵗ b) c ok) | v-eq = rs-ptr (inl-shape r)
  sub-reg-sound (e-inr a b) (e-repr c) ok (loc , v-eq , r)
    rewrite sym (ty-eq-sound (a +ᵗ b) c ok) | v-eq = rs-ptr (inr-shape r)
  sub-reg-sound (e-tag m') (e-tag n) ok mm
    rewrite nat-eq-sound m' n ok = mm
  -- COMPLETED FRESH → typed representation: build the sum/pair shape from
  -- the carried cell facts. The block start is a heap location whose ref
  -- sits just below the frontier, so `BeforeFrontier` for its cells is the
  -- frontier arithmetic; `LocMatchesMode Heap (AtDynamic _)` is `tt`.
  sub-reg-sound (e-fresh (just (e-tag zero)) (just (e-repr p))) (e-repr (a +ᵗ b)) ok
    (hl , v-eq , off0 , suc-nhr , tag-cell , (ploc , pc-eq , pbf , pm , pshape))
    rewrite v-eq | sym (ty-eq-sound p a ok) =
    rs-ptr {m = Heap}
      (shape-inl tt tag-cell pc-eq pbf
        (heap-before (subst (ref-id (heap-ref hl) <_) suc-nhr ≤-refl)) pshape)
  sub-reg-sound (e-fresh (just (e-tag (suc zero))) (just (e-repr p))) (e-repr (a +ᵗ b)) ok
    (hl , v-eq , off0 , suc-nhr , tag-cell , (ploc , pc-eq , pbf , pm , pshape))
    rewrite v-eq | sym (ty-eq-sound p b ok) =
    rs-ptr {m = Heap}
      (shape-inr tt tag-cell pc-eq pbf
        (heap-before (subst (ref-id (heap-ref hl) <_) suc-nhr ≤-refl)) pshape)
  sub-reg-sound (e-fresh (just (e-repr p)) (just (e-repr q))) (e-repr (a * b)) ok
    (hl , v-eq , off0 , suc-nhr ,
     (floc' , fc-eq , fbf , fm , fshape) , (sloc , sc-eq , sbf , sm , sshape))
    rewrite v-eq
          | sym (ty-eq-sound p a (proj₁ (∧-split (ty-eq p a) _ ok)))
          | sym (ty-eq-sound q b (proj₂ (∧-split (ty-eq p a) _ ok))) =
    rs-ptr {m = Heap}
      (shape-pair tt fc-eq sc-eq fbf sbf
        (heap-before (subst (ref-id (heap-ref hl) <_) suc-nhr ≤-refl))
        fshape sshape)

  slot-just : ∀ e {alloc v ls} → MeetsSlot e alloc (just v) ls → MeetsR e alloc v ls
  slot-just e-any       m = tt
  slot-just (e-repr _)  m = m
  slot-just (e-inl _ _) m = m
  slot-just (e-inr _ _) m = m
  slot-just (e-tag _)   m = m
  slot-just (e-fresh _ _) m = m

  just-slot : ∀ e {alloc v ls} → MeetsR e alloc v ls → MeetsSlot e alloc (just v) ls
  just-slot e-any       m = tt
  just-slot (e-repr _)  m = m
  just-slot (e-inl _ _) m = m
  just-slot (e-inr _ _) m = m
  just-slot (e-tag _)   m = m
  just-slot (e-fresh _ _) m = m

  sub-slot-sound : ∀ e e' {alloc mv ls} → sub-reg e e' ≡ true
                 → MeetsSlot e alloc mv ls → MeetsSlot e' alloc mv ls
  sub-slot-sound e e' {mv = just v} ok m =
    just-slot e' (sub-reg-sound e e' ok (slot-just e m))
  sub-slot-sound e e-any {mv = nothing} ok m = tt
  sub-slot-sound e-any (e-repr _) {mv = nothing} () m
  sub-slot-sound e-any (e-inl _ _) {mv = nothing} () m
  sub-slot-sound e-any (e-inr _ _) {mv = nothing} () m
  sub-slot-sound e-any (e-tag _) {mv = nothing} () m
  sub-slot-sound e-any (e-fresh _ _) {mv = nothing} () m
  sub-slot-sound (e-repr _) (e-repr _) {mv = nothing} ok m = ⊥-elim m
  sub-slot-sound (e-repr _) (e-inl _ _) {mv = nothing} ok m = ⊥-elim m
  sub-slot-sound (e-repr _) (e-inr _ _) {mv = nothing} ok m = ⊥-elim m
  sub-slot-sound (e-repr _) (e-tag _) {mv = nothing} ok m = ⊥-elim m
  sub-slot-sound (e-repr _) (e-fresh _ _) {mv = nothing} ok m = ⊥-elim m
  sub-slot-sound (e-inl _ _) (e-repr _) {mv = nothing} ok m = ⊥-elim m
  sub-slot-sound (e-inl _ _) (e-inl _ _) {mv = nothing} ok m = ⊥-elim m
  sub-slot-sound (e-inl _ _) (e-inr _ _) {mv = nothing} ok m = ⊥-elim m
  sub-slot-sound (e-inl _ _) (e-tag _) {mv = nothing} ok m = ⊥-elim m
  sub-slot-sound (e-inl _ _) (e-fresh _ _) {mv = nothing} ok m = ⊥-elim m
  sub-slot-sound (e-inr _ _) (e-repr _) {mv = nothing} ok m = ⊥-elim m
  sub-slot-sound (e-inr _ _) (e-inl _ _) {mv = nothing} ok m = ⊥-elim m
  sub-slot-sound (e-inr _ _) (e-inr _ _) {mv = nothing} ok m = ⊥-elim m
  sub-slot-sound (e-inr _ _) (e-tag _) {mv = nothing} ok m = ⊥-elim m
  sub-slot-sound (e-inr _ _) (e-fresh _ _) {mv = nothing} ok m = ⊥-elim m
  sub-slot-sound (e-tag _) (e-repr _) {mv = nothing} ok m = ⊥-elim m
  sub-slot-sound (e-tag _) (e-inl _ _) {mv = nothing} ok m = ⊥-elim m
  sub-slot-sound (e-tag _) (e-inr _ _) {mv = nothing} ok m = ⊥-elim m
  sub-slot-sound (e-tag _) (e-tag _) {mv = nothing} ok m = ⊥-elim m
  sub-slot-sound (e-tag _) (e-fresh _ _) {mv = nothing} ok m = ⊥-elim m
  sub-slot-sound (e-fresh _ _) (e-repr _) {mv = nothing} ok m = ⊥-elim m
  sub-slot-sound (e-fresh _ _) (e-inl _ _) {mv = nothing} ok m = ⊥-elim m
  sub-slot-sound (e-fresh _ _) (e-inr _ _) {mv = nothing} ok m = ⊥-elim m
  sub-slot-sound (e-fresh _ _) (e-tag _) {mv = nothing} ok m = ⊥-elim m
  sub-slot-sound (e-fresh _ _) (e-fresh _ _) {mv = nothing} ok m = ⊥-elim m

  sub-slots-sound : ∀ src tgt → sub-slots src tgt ≡ true
                  → ∀ k → sub-reg (slot-get src k) (slot-get tgt k) ≡ true
  sub-slots-sound src [] ok k = sub-any (slot-get src k)
    where sub-any : ∀ e → sub-reg e e-any ≡ true
          sub-any e-any = refl
          sub-any (e-repr _) = refl
          sub-any (e-inl _ _) = refl
          sub-any (e-inr _ _) = refl
          sub-any (e-tag _) = refl
          sub-any (e-fresh _ _) = refl
  sub-slots-sound src ((j , e) ∷ es) ok k with j ≟ k
  ... | yes refl = proj₁ (∧-split (sub-reg (slot-get src j) e) _ ok)
  ... | no _     = sub-slots-sound src es (proj₂ (∧-split (sub-reg (slot-get src j) e) _ ok)) k

  sub-expect-sound : ∀ s' t {fs} → sub-expect s' t ≡ true → Meets s' fs → Meets t fs
  sub-expect-sound s' t ok (m1 , m3 , ms) =
    sub-reg-sound (e-in1 s') (e-in1 t) (proj₁ (∧-split (sub-reg (e-in1 s') (e-in1 t)) _ ok)) m1 ,
    sub-reg-sound (e-out s') (e-out t)
      (proj₁ (∧-split (sub-reg (e-out s') (e-out t)) _
        (proj₂ (∧-split (sub-reg (e-in1 s') (e-in1 t)) _ ok)))) m3 ,
    λ k → sub-slot-sound (slot-get (e-slot s') k) (slot-get (e-slot t) k)
            (sub-slots-sound (e-slot s') (e-slot t)
              (proj₂ (∧-split (sub-reg (e-out s') (e-out t)) _
                (proj₂ (∧-split (sub-reg (e-in1 s') (e-in1 t)) _ ok))))
              k)
            (ms k)

  ------------------------------------------------------------------------
  -- THE SITE FACTS (M4's payload): `site-ok` + `Meets` yield exactly what
  -- the discipline residuals claim — a pointer at a load site, a pointer
  -- to a written tag cell (either residence) at a branch site.
  ------------------------------------------------------------------------

  -- A CLAIMED SLOT IS WRITTEN (Plan 0.54 rung D). `MeetsSlot` sends every
  -- non-`e-any` claim at `nothing` to `⊥`, so a slot the checker claims cannot
  -- be unwritten in a state that meets the expectation. This is the fact that
  -- makes the empty-slot routes UNREACHABLE now that `Window` no longer asserts
  -- the concrete cell is unmapped — see `not-any`/`site-ok` above.
  site-slot-written : ∀ (e₁ : RegExpect) {alloc ls} → not-any e₁ ≡ true
                    → MeetsSlot e₁ alloc nothing ls → ⊥
  site-slot-written e-any           () _
  site-slot-written (e-repr A)      _  ()
  site-slot-written (e-inl A B)     _  ()
  site-slot-written (e-inr A B)     _  ()
  site-slot-written (e-tag t)       _  ()
  site-slot-written (e-fresh c₀ c₁) _  ()

  site-load-ptr : ∀ (e₁ : RegExpect) {alloc v ls} → is-ptr e₁ ≡ true
                → MeetsR e₁ alloc v ls
                → Σ (ValueLocation FS) λ loc → v ≡ SV-Ptr loc
  site-load-ptr (e-repr (a * b))    ok (rs-ptr {loc = loc} _) = loc , refl
  site-load-ptr (e-repr (a ⇛ b))    ok (rs-ptr {loc = loc} _) = loc , refl
  site-load-ptr (e-repr (μ-type f)) ok (rs-ptr {loc = loc} _) = loc , refl
  site-load-ptr (e-repr (ν-type f)) ok (rs-ptr {loc = loc} _) = loc , refl
  site-load-ptr (e-repr (a +ᵗ b))   ok (rs-ptr {loc = loc} _) = loc , refl
  site-load-ptr (e-inl a b)     ok (loc , v-eq , _) = loc , v-eq
  site-load-ptr (e-inr a b)     ok (loc , v-eq , _) = loc , v-eq
  site-load-ptr (e-fresh c₀ c₁) ok (hl , v-eq , _)  = AtDynamic hl , v-eq
  site-load-ptr e-any           () _
  site-load-ptr (e-tag _)       () _
  site-load-ptr (e-repr Unit)   () _
  site-load-ptr (e-repr Void)   () _
  site-load-ptr (e-repr Int)    () _
  site-load-ptr (e-repr Float)  () _
  site-load-ptr (e-repr Str)    () _
  site-load-ptr (e-repr Buffer) () _

  -- a sum shape's node carries a written tag (0 for inl, 1 for inr)
  tag-of-shape : ∀ {m alloc A B loc ls} → ShapeAt m alloc (A +ᵗ B) loc ls
               → Σ ℕ λ t → readLoc ls loc ≡ just (SV-Tag t)
  tag-of-shape (shape-inl {m = m} lm tg cell bfp bfs pay) = 0 , tag-at-read m 0 _ _ tg
  tag-of-shape (shape-inr {m = m} lm tg cell bfp bfs pay) = 1 , tag-at-read m 1 _ _ tg
  -- Stage F: an inline payload changes nothing here — the TAG cell is the
  -- same cell, written the same way. Only the payload cell differs.
  tag-of-shape (shape-inl-reg {m = m} lm tg fit cell bfs) = 0 , tag-at-read m 0 _ _ tg
  tag-of-shape (shape-inr-reg {m = m} lm tg fit cell bfs) = 1 , tag-at-read m 1 _ _ tg

  -- …and through one μ/ν unfolding, provided the layer is a sum
  tag-of-μ : ∀ {m alloc loc ls} (T : IRTy) {a b : IRTy}
           → as-sum-of T ≡ just (a , b)
           → ShapeAt m alloc T loc ls
           → Σ ℕ λ t → readLoc ls loc ≡ just (SV-Tag t)
  tag-of-μ (a +ᵗ b) refl sh = tag-of-shape sh

  site-branch-tag : ∀ (e₁ : RegExpect) {alloc v ls} → tag-site-ok e₁ ≡ true
                  → MeetsR e₁ alloc v ls
                  → Σ (ValueLocation FS) λ loc → (v ≡ SV-Ptr loc)
                      × Σ ℕ λ t → readLoc ls loc ≡ just (SV-Tag t)
  site-branch-tag (e-fresh (just (e-tag t)) c₁) ok (hl , v-eq , _ , _ , tag-cell , _) =
    AtDynamic hl , v-eq , t , tag-cell
  site-branch-tag (e-repr (a +ᵗ b)) ok (rs-ptr {loc = loc} sh) =
    loc , refl , tag-of-shape sh
  site-branch-tag (e-inl a b) ok (loc , v-eq , r) =
    loc , v-eq , 0 , tag-at-read (InlAt.i-m r) 0 _ _ (InlAt.i-tag r)
  site-branch-tag (e-inr a b) ok (loc , v-eq , r) =
    loc , v-eq , 1 , tag-at-read (InrAt.r-m r) 1 _ _ (InrAt.r-tag r)
  site-branch-tag (e-repr (μ-type f)) ok (rs-ptr {loc = loc} (shape-μ wf layer)) =
    loc , refl , go (⟦ f ⟧TI (μ-type f)) (as-sum-of (⟦ f ⟧TI (μ-type f))) refl ok layer
    where
      go : ∀ T (ms : Maybe (IRTy × IRTy)) → as-sum-of T ≡ ms
         → is-just ms ≡ true
         → ∀ {m alloc loc' ls} → ShapeAt m alloc T loc' ls
         → Σ ℕ λ t → readLoc ls loc' ≡ just (SV-Tag t)
      go T (just (a , b)) as-eq ok' sh = tag-of-μ T as-eq sh
      go T nothing        as-eq () sh
  site-branch-tag (e-repr (ν-type f)) ok (rs-ptr {loc = loc} (shape-ν wf layer)) =
    loc , refl , go (⟦ f ⟧TI (ν-type f)) (as-sum-of (⟦ f ⟧TI (ν-type f))) refl ok layer
    where
      go : ∀ T (ms : Maybe (IRTy × IRTy)) → as-sum-of T ≡ ms
         → is-just ms ≡ true
         → ∀ {m alloc loc' ls} → ShapeAt m alloc T loc' ls
         → Σ ℕ λ t → readLoc ls loc' ≡ just (SV-Tag t)
      go T (just (a , b)) as-eq ok' sh = tag-of-μ T as-eq sh
      go T nothing        as-eq () sh
  site-branch-tag e-any           () _
  site-branch-tag (e-tag _)       () _
  site-branch-tag (e-fresh nothing c₁) () _
  site-branch-tag (e-fresh (just e-any) c₁) () _
  site-branch-tag (e-fresh (just (e-repr _)) c₁) () _
  site-branch-tag (e-fresh (just (e-inl _ _)) c₁) () _
  site-branch-tag (e-fresh (just (e-inr _ _)) c₁) () _
  site-branch-tag (e-fresh (just (e-fresh _ _)) c₁) () _
  site-branch-tag (e-repr Unit)   () _
  site-branch-tag (e-repr Void)   () _
  site-branch-tag (e-repr Int)    () _
  site-branch-tag (e-repr Float)  () _
  site-branch-tag (e-repr Str)    () _
  site-branch-tag (e-repr Buffer) () _
  site-branch-tag (e-repr (a * b)) () _
  site-branch-tag (e-repr (a ⇛ b)) () _

  ------------------------------------------------------------------------
  -- THE STORE-SOUNDNESS BRICK: a write to a PREVIOUSLY-UNWRITTEN heap cell
  -- preserves every claim — a claim mentions a cell only through a
  -- `readLoc … ≡ just …` equation, and the target read `nothing`.
  ------------------------------------------------------------------------
  open SM.MemOps {FS} using (writeLocToHeap; writeHeapMem-aux)
  open import Relation.Nullary using (Dec; yes; no)
  open import Once.Memory.HeapAddress using (_≟HL_)

  nothing≢just : ∀ {A : Set} {x : A} → (nothing {A = A}) ≡ just x → ⊥
  nothing≢just ()

  -- read-back after an unwritten-cell write: every established `just` read
  -- survives (the yes-branch would contradict unwritten-ness)
  read-uw : ∀ (ls : LocState FS) (hl' : HeapLocation) (v' : StoredValue FS)
              (c : ValueLocation FS) {w : StoredValue FS}
          → heapMem ls hl' ≡ nothing
          → readLoc ls c ≡ just w
          → readLoc (writeLocToHeap ls hl' v') c ≡ just w
  read-uw ls hl' v' (AtStack f k)    uw r = r
  read-uw ls hl' v' (AtDynamic hl'') {w} uw r = go (hl' ≟HL hl'')
    where
      go : (d : Dec (hl' ≡ hl''))
         → writeHeapMem-aux d (heapMem ls hl'') v' ≡ just w
      go (yes refl) = ⊥-elim (nothing≢just (trans (sym uw) r))
      go (no _)     = r

  tag-uw : ∀ (m : AllocMode) (t : ℕ) {ls : LocState FS} (hl' : HeapLocation)
             (v' : StoredValue FS) {loc : ValueLocation FS}
         → heapMem ls hl' ≡ nothing
         → TagAt m t ls loc
         → TagAt m t (writeLocToHeap ls hl' v') loc
  tag-uw Heap  t {ls} hl' v' {loc} uw tg = read-uw ls hl' v' loc uw tg
  tag-uw Stack t {ls} hl' v' {loc} uw tg = read-uw ls hl' v' loc uw tg

  shape-uw : ∀ {m} {alloc : AllocState {FS}} {A loc} {ls : LocState FS}
               (hl' : HeapLocation) (v' : StoredValue FS)
           → heapMem ls hl' ≡ nothing
           → ShapeAt m alloc A loc ls
           → ShapeAt m alloc A loc (writeLocToHeap ls hl' v')
  shape-uw hl' v' uw shape-unit = shape-unit
  shape-uw {ls = ls} hl' v' uw (shape-pair {pair-loc = pl} lm r1 r2 b1 b2 b3 sa sb) =
    shape-pair lm (read-uw ls hl' v' pl uw r1) (read-uw ls hl' v' (sucLoc pl) uw r2)
               b1 b2 b3 (shape-uw hl' v' uw sa) (shape-uw hl' v' uw sb)
  shape-uw {ls = ls} hl' v' uw (shape-closure {closure-loc = cl} lm r1 r2 b1 b2 senv) =
    shape-closure lm (read-uw ls hl' v' cl uw r1) (read-uw ls hl' v' (sucLoc cl) uw r2)
                  b1 b2 (shape-uw hl' v' uw senv)
  shape-uw {m = m} {ls = ls} hl' v' uw (shape-inl {sum-loc = sl} lm tg r b1 b2 sp) =
    shape-inl lm (tag-uw m 0 hl' v' uw tg) (read-uw ls hl' v' (sucLoc sl) uw r)
              b1 b2 (shape-uw hl' v' uw sp)
  shape-uw {m = m} {ls = ls} hl' v' uw (shape-inr {sum-loc = sl} lm tg r b1 b2 sp) =
    shape-inr lm (tag-uw m 1 hl' v' uw tg) (read-uw ls hl' v' (sucLoc sl) uw r)
              b1 b2 (shape-uw hl' v' uw sp)
  -- Stage F: the inline variants have no payload SHAPE to carry through the
  -- heap write, so there is no recursive call — just the two cell reads.
  shape-uw {m = m} {ls = ls} hl' v' uw (shape-inl-reg {sum-loc = sl} lm tg fit r b) =
    shape-inl-reg lm (tag-uw m 0 hl' v' uw tg) fit (read-uw ls hl' v' (sucLoc sl) uw r) b
  shape-uw {m = m} {ls = ls} hl' v' uw (shape-inr-reg {sum-loc = sl} lm tg fit r b) =
    shape-inr-reg lm (tag-uw m 1 hl' v' uw tg) fit (read-uw ls hl' v' (sucLoc sl) uw r) b
  shape-uw hl' v' uw (shape-μ wf sh) = shape-μ wf (shape-uw hl' v' uw sh)
  shape-uw hl' v' uw (shape-ν wf sh) = shape-ν wf (shape-uw hl' v' uw sh)
  shape-uw {loc = l} {ls = ls} hl' v' uw (shape-int b r)   = shape-int b (read-uw ls hl' v' l uw r)
  shape-uw {loc = l} {ls = ls} hl' v' uw (shape-float b r) = shape-float b (read-uw ls hl' v' l uw r)
  shape-uw hl' v' uw (shape-str b)    = shape-str b
  shape-uw hl' v' uw (shape-buffer b) = shape-buffer b

  ------------------------------------------------------------------------
  -- Claim transports under the two machine effects the transfer tracks:
  -- a register write (read-back enumeration) and an unwritten-cell heap
  -- write (`shape-uw` compositions). A heap write touches NO register and
  -- NO stack cell, so those components transport definitionally.
  ------------------------------------------------------------------------
  meets-cell-uw : ∀ (c : RegExpect) {alloc} {ls : LocState FS}
                    (hl' : HeapLocation) (v' : StoredValue FS) {mc}
                → heapMem ls hl' ≡ nothing
                → MeetsCell c alloc mc ls
                → (∀ {w} → mc ≡ just w
                   → MeetsCell c alloc mc (writeLocToHeap ls hl' v'))
  meets-cell-uw e-any hl' v' uw m _ = tt
  meets-cell-uw (e-repr A) hl' v' uw (loc , c-eq , bf , mo , sh) _ =
    loc , c-eq , bf , mo , shape-uw hl' v' uw sh
  meets-cell-uw (e-inl A B) {ls = ls} hl' v' uw (loc , c-eq , bf , r) _ =
    loc , c-eq , bf , inl-uw r
    where inl-uw : ∀ {alloc'} → InlAt alloc' A B loc ls
                 → InlAt alloc' A B loc (writeLocToHeap ls hl' v')
          inl-uw record { i-mode = im ; i-tag = it ; i-cell = ic
                        ; i-bf-p = bp ; i-bf-s = bs ; i-pay = ip } =
            record { i-mode = im ; i-tag = tag-uw _ 0 hl' v' uw it
                   ; i-cell = read-uw ls hl' v' (sucLoc loc) uw ic
                   ; i-bf-p = bp ; i-bf-s = bs ; i-pay = shape-uw hl' v' uw ip }
  meets-cell-uw (e-inr A B) {ls = ls} hl' v' uw (loc , c-eq , bf , r) _ =
    loc , c-eq , bf , inr-uw r
    where inr-uw : ∀ {alloc'} → InrAt alloc' A B loc ls
                 → InrAt alloc' A B loc (writeLocToHeap ls hl' v')
          inr-uw record { r-mode = im ; r-tag = it ; r-cell = ic
                        ; r-bf-p = bp ; r-bf-s = bs ; r-pay = ip } =
            record { r-mode = im ; r-tag = tag-uw _ 1 hl' v' uw it
                   ; r-cell = read-uw ls hl' v' (sucLoc loc) uw ic
                   ; r-bf-p = bp ; r-bf-s = bs ; r-pay = shape-uw hl' v' uw ip }
  meets-cell-uw (e-tag t) hl' v' uw m _ = m
  meets-cell-uw (e-fresh c₀ c₁) hl' v' uw m mj = ⊥-elim m

  -- the flat machine's `fetch` IS `at-pc`
  fetch-at-pc : ∀ (t : AbstractTrace) (k : ℕ) → fetch t k ≡ at-pc t k
  fetch-at-pc []       k       = refl
  fetch-at-pc (i ∷ is) zero    = refl
  fetch-at-pc (i ∷ is) (suc k) = fetch-at-pc is k

  -- a store site's requirement (`is-fresh`) is stronger than a load's
  fresh⇒ptr : ∀ (e : RegExpect) → is-fresh e ≡ true → is-ptr e ≡ true
  fresh⇒ptr (e-fresh _ _) ok = refl
  fresh⇒ptr e-any        ()
  fresh⇒ptr (e-repr _)   ()
  fresh⇒ptr (e-inl _ _)  ()
  fresh⇒ptr (e-inr _ _)  ()
  fresh⇒ptr (e-tag _)    ()

  site-store-ptr : ∀ (e₁ : RegExpect) {alloc v ls} → is-fresh e₁ ≡ true
                 → MeetsR e₁ alloc v ls
                 → Σ (ValueLocation FS) λ loc → v ≡ SV-Ptr loc
  site-store-ptr e₁ ok m = site-load-ptr e₁ (fresh⇒ptr e₁ ok) m
