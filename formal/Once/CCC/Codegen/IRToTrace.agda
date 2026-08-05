-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.CCC.Codegen.IRToTrace
--
-- Shared IR → AbstractTrace lowering used by every architecture's
-- Target instance, including X86-64 after Plan 0.10 Phase C lands.
-- New architectures only need:
--
--   * `compile-trace : AbstractTrace → arch.Program`
--     (already provided as `Once.CCC.Target.<arch>.AbstractTo<arch>.compile-trace`)
--
--   * `programToText : arch.Program → String`
--     (per-arch `Emit.agda`)
--
-- and they're done — `Once.Target.<arch>` composes them with this
-- function.
--
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- State threading
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--
-- `ir-to-trace'` threads a slot frontier counter so pair/curry/apply
-- can allocate the slots they need. The frontier mirrors
-- `next-slot alloc` in the verified Dispatcher's AllocState.
--
-- Convention: each operation that allocates k slots advances the
-- frontier by k. The OUTGOING frontier is what the next operation
-- sees. Reclamation (slot reuse on subsequent allocations) is a
-- caller-side concern; this function is monotone.
--
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- Coverage (Plan 0.10 Phase B)
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--
-- Implemented (emit a real trace, mirroring the corresponding *WF module):
--   id           — SimpleWF
--   _∘_          — ComposeWF
--   fst, snd     — SimpleWF
--   terminal     — SimpleWF
--   initial      — SimpleWF
--   arr          — SimpleWF
--   ⟨_,_⟩        — PairStackWF.pair-trace
--   curry        — CurryStackWF.curry-trace
--   apply        — ApplyWF.apply-setup-trace + instr-call-closure
--   SigOp        — `instr-sigop name` (per-arch decode)
--
-- Stubbed (emit `[]` — Layer 0 doesn't need these):
--   inl, inr, case
--   In, out-μ, Cata, Para, Out, in-ν, Ana, Hylo, Fuse
--   free-heap
--
-- See `plans/0.10-verification-gap-closure.md`.
------------------------------------------------------------------------

module Once.CCC.Codegen.IRToTrace where

open import Data.Nat using (ℕ; zero; suc; _⊔_; _*_) renaming (_+_ to _+ℕ_)
open import Data.Bool using (Bool; true; false; if_then_else_; _∨_)
open import Data.Product using (_×_; _,_; proj₂)
open import Data.List using (List; []; _∷_; _++_)

open import Once.SigOp.Info using (SigOpInfo)
open SigOpInfo using (name)

open import Once.IR using (IR; AllocMode; Stack; Heap;
  id; _∘_; ⟨_,_⟩; fst; snd; inl; inr; case; terminal; initial;
  curry; apply;
  In; out-μ; Cata; Para; Out; in-ν; Ana; Hylo; Fuse;
  free-heap; SigOp; const)
-- Plan 0.36 Phase 2b: functor structure drives the cata codegen strategy.
open import Once.Type using (Functor; K; Id; _⊕_; _⊗_)
open import Once.IRTy using (fits-int; fits-float; ⌈_⌉F)
import Once.Type as Ty

open import Once.CCC.Machine.SMCore
  using (AbstractInstr; AbstractTrace;
         mov-to-output; mov-to-input; mov-output-to-input2; mov-input2-to-output;
         load-indirect; load-indirect-suc; load-from-slot;
         store-at-slot; store-indirect; store-indirect-suc;
         lea-slot; restore-input;
         instr-alloc-stack; instr-alloc-heap; instr-dealloc-stack; instr-reclaim-to;
         instr-push-frame; instr-pop-frame; instr-call-closure;
         instr-sigop; instr-load-const; instr-load-code-addr;
         instr-save-closure-reg;
         instr-load-tag-lit; instr-case-on-tag;
         instr-loop; instr-reg-op;
         instr-ctrl; c-label; c-jmp; c-thunk; c-ret; c-branch-scratch-zero; c-branch-tag-zero;
         scratch-one; scratch-zero; scratch-dec; scratch-load-count;
         count-zero; count-inc)

------------------------------------------------------------------------
-- IR → AbstractTrace, state-passing
------------------------------------------------------------------------

-- | State-passing form. Plan 0.2.4.2 Phase C: extended to also
-- thread a label counter and accumulate closure-body traces.
--
-- Inputs:
--   slot-frontier — current next-available stack slot
--   label-counter — current next-available .L_thunk_<n> index
--   IR
--
-- Output (4-tuple):
--   slot-frontier-after — slots used by this IR's main trace
--   label-counter-after — labels used by this IR + nested bodies
--   main-trace          — the trace executed in the parent function
--   body-traces         — `(label, body-budget, body-trace)` triples
--                         for each curry encountered (this IR + nested).
--                         Plan 0.2.4.5 D1: body-budget is the slot
--                         frontier reached by the body, used by codegen
--                         to emit `subq budget*8, %rsp` / `addq` brackets
--                         around the body's trace (frameless model —
--                         body has its own %rsp-relative frame).
--
-- The `curry` clause is the only one that allocates a new label.
-- Other clauses thread the counter and accumulate body lists.
-- ────────────────────────────────────────────────────────────────────
-- Plan 0.36 Phase 2b: cata codegen STRATEGY, dispatched at compile time
-- on the (statically-known) functor `F`. Keeps the fast Nat path; linear
-- functors get an upfront-allocated payload stack (count pre-pass);
-- branching functors need a dynamic worklist. `rec-count` = the max
-- number of recursive (`Id`) positions reachable in a single constructor
-- (sum = distinct constructors → max; product = same constructor → sum).
-- ────────────────────────────────────────────────────────────────────
rec-count : Functor → ℕ
rec-count (K _)   = 0
rec-count Id      = 1
rec-count (F ⊕ G) = rec-count F ⊔ rec-count G
rec-count (F ⊗ G) = rec-count F +ℕ rec-count G

data CataStrategy : Set where
  strat-const     : CataStrategy   -- 0 rec positions: cata = alg on the In-layer
  strat-nat       : CataStrategy   -- 1 bare-Id rec position, no payload (Nat)
  strat-linear    : CataStrategy   -- 1 rec position + payload (Tier 1)
  strat-branching : Functor → CataStrategy  -- ≥2 rec positions (Tier 2); carries F

-- `has-id F` — does `Id` occur anywhere in `F`? `id-under-product F` — does
-- some `Id` sit INSIDE a `⊗`? A single-recursive functor with `Id` under a
-- product (List `K Unit + (K Int * Id)`, nelist, nested-product payload) is
-- "linear with payload": the rec arm is `_ ⊗ Id`, so each layer carries a
-- payload word the fold must stash (Tier 1). A single-recursive functor with a
-- bare `Id` arm (Nat `K Unit + Id`) carries no payload (Tier nat).
has-id : Functor → Bool
has-id (K _)   = false
has-id Id      = true
has-id (F ⊕ G) = has-id F ∨ has-id G
has-id (F ⊗ G) = has-id F ∨ has-id G

id-under-product : Functor → Bool
id-under-product (K _)   = false
id-under-product Id      = false
id-under-product (F ⊕ G) = id-under-product F ∨ id-under-product G
id-under-product (F ⊗ G) = has-id F ∨ has-id G ∨ id-under-product F ∨ id-under-product G

-- The classifier: no recursion → Nat (no loop); one recursive position →
-- linear (with payload) vs Nat (bare Id) per `id-under-product`; two or more →
-- branching (Tier 2, still TODO).
cata-strategy : Functor → CataStrategy
cata-strategy F with rec-count F
... | 0           = strat-const
... | 1           = if id-under-product F then strat-linear else strat-nat
... | suc (suc _) = strat-branching F

-- The current (Nat-shaped) codegen body, extracted so the dispatch can
-- pick it. Takes the post-`alg` frontier/label counters + alg's main
-- trace `at`; returns (frontier-after , label-after , main-trace).
-- Plan 0.63 (iii): THE SKELETON PIECES ARE TOP-LEVEL, and the trace is their
-- ALTERNATION with the algebra:
--
--     cata-nat-I₁ ++ at ++ (cata-nat-I₂ ++ at ++ cata-nat-I₃)
--
-- Same list as before — only the bracketing of the `++`s changed (the ascend
-- arm used to nest as `(at ++ X) ++ Y`). The point is that the decomposition
-- is now DEFINITIONAL, so a proof about "idle skeleton with embedded copies of
-- the algebra" (`LabelScope.Pieces`) can be given without transcribing 28
-- instructions into the proof and letting them rot.
cata-nat-layer : ℕ → ℕ → AbstractTrace
cata-nat-layer n1 tag =
  mov-to-output ∷ store-at-slot n1 ∷ instr-alloc-heap 2 ∷
  store-at-slot (suc n1) ∷ mov-to-input ∷ instr-load-tag-lit tag ∷
  store-indirect ∷ load-from-slot n1 ∷ store-indirect-suc ∷
  load-from-slot (suc n1) ∷ []

cata-nat-descend : ℕ → AbstractTrace
cata-nat-descend l1 =
  instr-ctrl (c-label l1) ∷
  instr-ctrl (c-branch-scratch-zero (suc l1)) ∷
  instr-ctrl (c-branch-tag-zero (suc (suc l1))) ∷
  instr-reg-op count-inc ∷ load-indirect-suc ∷ mov-to-input ∷
  instr-ctrl (c-jmp (suc (suc (suc l1)))) ∷
  instr-ctrl (c-label (suc (suc l1))) ∷ instr-reg-op scratch-zero ∷
  instr-ctrl (c-label (suc (suc (suc l1)))) ∷ instr-ctrl (c-jmp l1) ∷
  instr-ctrl (c-label (suc l1)) ∷ []

cata-nat-I₁ : ℕ → ℕ → AbstractTrace
cata-nat-I₁ n1 l1 =
  instr-reg-op scratch-one ∷ instr-reg-op count-zero ∷
  (cata-nat-descend l1 ++
   (instr-reg-op scratch-load-count ∷ instr-load-tag-lit 0 ∷ mov-to-input ∷
    (cata-nat-layer n1 0 ++ (mov-to-input ∷ []))))

cata-nat-I₂ : ℕ → ℕ → AbstractTrace
cata-nat-I₂ n1 l1 =
  instr-ctrl (c-label (suc (suc (suc (suc l1))))) ∷
  instr-ctrl (c-branch-scratch-zero (suc (suc (suc (suc (suc l1)))))) ∷
  mov-to-input ∷ (cata-nat-layer n1 1 ++ (mov-to-input ∷ []))

cata-nat-I₃ : ℕ → AbstractTrace
cata-nat-I₃ l1 =
  instr-reg-op scratch-dec ∷
  instr-ctrl (c-jmp (suc (suc (suc (suc l1))))) ∷
  instr-ctrl (c-label (suc (suc (suc (suc (suc l1)))))) ∷ []

cata-trace-nat : ℕ → ℕ → AbstractTrace → ℕ × ℕ × AbstractTrace
cata-trace-nat n1 l1 at =
  suc (suc n1) , suc (suc (suc (suc (suc (suc l1))))) ,
  (cata-nat-I₁ n1 l1 ++ at ++ (cata-nat-I₂ n1 l1 ++ at ++ cata-nat-I₃ l1))

-- Plan 0.36 Phase 2b Tier 1: functor-general LINEAR (single recursive
-- position, with payload) cata codegen via a SIMPLE 2-cell linked payload
-- stack on the heap (Plan 0.37 chunks it later — needs an ISA extension).
--
-- Layouts the frontend emits (`In`/`inr`/pair codegen):
--   cons node `In (inr (x, child))` = `[1, pair-ptr]`, pair = `[x, child-ptr]`
--     ⇒ payload x = node[1][0], recursive child = node[1][1].
--   base node `In (inl b)`          = `[0, b]` (b = unit for K Unit, the
--     terminal Int for K Int) — fed to `alg` directly (uniform base handling).
--
-- Three phases (Scratch survives `alg` — CCC code never touches rbx):
--   DESCEND+PUSH: Input2 counts depth n; for each cons, push x onto the
--     payload stack (`[x, prev-top]`, top in `stack-top`); advance to child.
--     Ends with Input1 at the base node.
--   BASE: Scratch := n; run `alg` on the base node → Output = base acc.
--   ASCEND+POP: while Scratch ≠ 0, pop x (top := top[1]), build pair `[x,acc]`,
--     build layer `[1, pair]`, run `alg` → acc'; Scratch--. LIFO pop gives
--     reverse (innermost-first = foldr) order. Output = final fold result.
-- Plan 0.63 (iii): same top-level decomposition as the Nat skeleton —
-- `I₁ ++ at ++ (I₂ ++ at ++ I₃)`, same list, only the `++` bracketing moved.
cata-lin-I₁ : ℕ → ℕ → AbstractTrace
cata-lin-I₁ n1 l1 =
  instr-reg-op count-zero ∷
  instr-load-tag-lit 0 ∷ store-at-slot (suc (suc (suc n1))) ∷
  instr-ctrl (c-label l1) ∷
  instr-ctrl (c-branch-tag-zero (suc l1)) ∷
  instr-reg-op count-inc ∷
  load-indirect-suc ∷ mov-to-input ∷
  load-indirect ∷ store-at-slot (suc (suc (suc (suc (suc n1))))) ∷
  load-indirect-suc ∷ store-at-slot (suc (suc n1)) ∷
  instr-alloc-heap 2 ∷ store-at-slot (suc n1) ∷ mov-to-input ∷
  load-from-slot (suc (suc (suc (suc (suc n1))))) ∷ store-indirect ∷
  load-from-slot (suc (suc (suc n1))) ∷ store-indirect-suc ∷
  load-from-slot (suc n1) ∷ store-at-slot (suc (suc (suc n1))) ∷
  load-from-slot (suc (suc n1)) ∷ mov-to-input ∷
  instr-ctrl (c-jmp l1) ∷
  instr-ctrl (c-label (suc l1)) ∷
  instr-reg-op scratch-load-count ∷ []

cata-lin-I₂ : ℕ → ℕ → AbstractTrace
cata-lin-I₂ n1 l1 =
  instr-ctrl (c-label (suc (suc l1))) ∷
  instr-ctrl (c-branch-scratch-zero (suc (suc (suc l1)))) ∷
  store-at-slot (suc (suc (suc (suc n1)))) ∷
  load-from-slot (suc (suc (suc n1))) ∷ mov-to-input ∷
  load-indirect ∷ store-at-slot (suc (suc (suc (suc (suc n1))))) ∷
  load-indirect-suc ∷ store-at-slot (suc (suc (suc n1))) ∷
  instr-alloc-heap 2 ∷ store-at-slot (suc n1) ∷ mov-to-input ∷
  load-from-slot (suc (suc (suc (suc (suc n1))))) ∷ store-indirect ∷
  load-from-slot (suc (suc (suc (suc n1)))) ∷ store-indirect-suc ∷
  instr-alloc-heap 2 ∷ store-at-slot n1 ∷ mov-to-input ∷
  instr-load-tag-lit 1 ∷ store-indirect ∷
  load-from-slot (suc n1) ∷ store-indirect-suc ∷
  load-from-slot n1 ∷ mov-to-input ∷ []

cata-lin-I₃ : ℕ → AbstractTrace
cata-lin-I₃ l1 =
  instr-reg-op scratch-dec ∷
  instr-ctrl (c-jmp (suc (suc l1))) ∷
  instr-ctrl (c-label (suc (suc (suc l1)))) ∷ []

cata-trace-linear : ℕ → ℕ → AbstractTrace → ℕ × ℕ × AbstractTrace
cata-trace-linear n1 l1 at =
  suc (suc (suc (suc (suc (suc n1))))) , suc (suc (suc (suc l1))) ,
  (cata-lin-I₁ n1 l1 ++ at ++ (cata-lin-I₂ n1 l1 ++ at ++ cata-lin-I₃ l1))

-- ────────────────────────────────────────────────────────────────────
-- Plan 0.36 Phase 2b Tier 2: functor-general BRANCHING cata codegen
-- (≥2 recursive positions: leaf/node/ternary trees, multi-constructor).
-- Iterative POST-ORDER over two heap-linked stacks (same no-ISA principle
-- as Tier 1; NOT lea-indexed):
--   * todo stack — nodes to flatten;
--   * eval stack — post-order node sequence (children before parents);
--   * value stack — folded `A` results awaiting their parent's combine.
-- Pass 1 (flatten): pop a node off todo, push it to eval, push its Id
--   children to todo (`visit-walk`, RIGHT-to-LEFT). Pass 2 (fold): pop a
--   node off eval, rebuild its `⟦F⟧A` layer popping one value-stack result
--   per Id position (`rebuild-walk`, LEFT-to-RIGHT — the LIFO value stack
--   inverts visit's order, so positions line up), run `alg`, push result.
-- visit-walk / rebuild-walk are COMPILE-TIME recursions over F that emit
-- runtime tag-dispatched node walks (nested `instr-case-on-tag` for sums;
-- `instr-case-on-tag` carries no labels — its x86 labels are assigned
-- downstream by compile-trace-cnt, so this codegen's own label count is
-- just the 4 loop labels). The per-node walk is bounded by F's size and so
-- is unrolled into straight-line code; only the tree-sized stacks are
-- heap-linked. Stacks share a sentinel block `[SV-Tag 0, _]` so emptiness
-- is detected by `c-branch-tag-zero` on the popped block's cell-0.
-- ────────────────────────────────────────────────────────────────────

-- size bound (≥ nesting depth) — drives the structural-walk slot budget.
fsize : Functor → ℕ
fsize (K _)   = 1
fsize Id      = 1
fsize (F ⊕ G) = suc (fsize F +ℕ fsize G)
fsize (F ⊗ G) = suc (fsize F +ℕ fsize G)

-- push the value in Output onto a 2-cell linked stack at `topSlot`
-- (`[value, prev]`), using scratch slots `tv` (value) and `tb` (block).
push2 : (topSlot tv tb : ℕ) → AbstractTrace
push2 topSlot tv tb =
  store-at-slot tv ∷ instr-alloc-heap 2 ∷ store-at-slot tb ∷ mov-to-input ∷
  load-from-slot tv ∷ store-indirect ∷
  load-from-slot topSlot ∷ store-indirect-suc ∷
  load-from-slot tb ∷ store-at-slot topSlot ∷ []

-- pop a 2-cell linked stack at `topSlot`; popped value → Output, advance
-- top to its `prev`. (Clobbers Input1 — caller re-establishes.)
pop2 : (topSlot : ℕ) → AbstractTrace
pop2 topSlot =
  load-from-slot topSlot ∷ mov-to-input ∷
  load-indirect-suc ∷ store-at-slot topSlot ∷
  load-indirect ∷ []

-- wrap the payload repr in Output into a sum node `[tag, payload]` (Output
-- := new block); scratch slots `s` (payload) and `s+1` (block).
wrap-sum : (tag s : ℕ) → AbstractTrace
wrap-sum tag s =
  store-at-slot s ∷ instr-alloc-heap 2 ∷ store-at-slot (suc s) ∷ mov-to-input ∷
  instr-load-tag-lit tag ∷ store-indirect ∷
  load-from-slot s ∷ store-indirect-suc ∷
  load-from-slot (suc s) ∷ []

-- VISIT walk: Input1 = repr(G); push every Id child (a μF pointer) of G
-- onto the todo stack, RIGHT-to-LEFT. `s` = structural-walk slot base
-- (stride 4 per level, so a level's own slots [s..s+3] never overlap its
-- children's [s+4..]).
-- LABEL BUDGET of a functor walk: each ⊕ node consumes exactly TWO labels
-- (branch target + join). Positional allocation — a node at label base `lb`
-- takes [lb, lb+1], its F child starts at lb+2, its G child at lb+2+lsize F —
-- so the walks stay plain trace-builders (no threaded counter to return).
lsize : Functor → ℕ
lsize (K _)   = 0
lsize Id      = 0
lsize (F ⊕ G) = suc (suc (lsize F +ℕ lsize G))
lsize (F ⊗ G) = lsize F +ℕ lsize G

-- Plan 0.54 item 6 (2026-08-01): the ⊕ dispatch is FLAT CONTROL, not a nested
-- `instr-case-on-tag` — same shape as `case f g` below and as the branching
-- cata's own loop: `c-branch-tag-zero` to the inl branch, inr falls through,
-- `c-jmp` joins. Branch prologue (payload into Input1) unchanged.
visit-walk : (todoSlot tv tb : ℕ) → Functor → (s lb : ℕ) → AbstractTrace
visit-walk todoSlot tv tb (K _) s lb = []
visit-walk todoSlot tv tb Id    s lb = mov-to-output ∷ push2 todoSlot tv tb
visit-walk todoSlot tv tb (F ⊕ G) s lb =
  (instr-ctrl (c-branch-tag-zero lb) ∷ load-indirect-suc ∷ mov-to-input ∷ []) ++
  visit-walk todoSlot tv tb G (s +ℕ 4) (suc (suc lb) +ℕ lsize F) ++
  (instr-ctrl (c-jmp (suc lb)) ∷ instr-ctrl (c-label lb) ∷
   load-indirect-suc ∷ mov-to-input ∷ []) ++
  visit-walk todoSlot tv tb F (s +ℕ 4) (suc (suc lb)) ++
  (instr-ctrl (c-label (suc lb)) ∷ [])
visit-walk todoSlot tv tb (F ⊗ G) s lb =
  (mov-to-output ∷ store-at-slot s ∷ load-indirect-suc ∷ mov-to-input ∷ []) ++
  visit-walk todoSlot tv tb G (s +ℕ 4) (lb +ℕ lsize F) ++
  (restore-input s ∷ load-indirect ∷ mov-to-input ∷ []) ++
  visit-walk todoSlot tv tb F (s +ℕ 4) lb

-- REBUILD walk: Input1 = repr(G) (the node sublayer); build the ⟦G⟧A layer
-- in Output, popping one value-stack result per Id position, LEFT-to-RIGHT.
rebuild-walk : (valSlot tv tb : ℕ) → Functor → (s lb : ℕ) → AbstractTrace
rebuild-walk valSlot tv tb (K _) s lb = mov-to-output ∷ []
rebuild-walk valSlot tv tb Id    s lb = pop2 valSlot
rebuild-walk valSlot tv tb (F ⊕ G) s lb =
  (instr-ctrl (c-branch-tag-zero lb) ∷ load-indirect-suc ∷ mov-to-input ∷ []) ++
  rebuild-walk valSlot tv tb G (s +ℕ 4) (suc (suc lb) +ℕ lsize F) ++ wrap-sum 1 s ++
  (instr-ctrl (c-jmp (suc lb)) ∷ instr-ctrl (c-label lb) ∷
   load-indirect-suc ∷ mov-to-input ∷ []) ++
  rebuild-walk valSlot tv tb F (s +ℕ 4) (suc (suc lb)) ++ wrap-sum 0 s ++
  (instr-ctrl (c-label (suc lb)) ∷ [])
rebuild-walk valSlot tv tb (F ⊗ G) s lb =
  (mov-to-output ∷ store-at-slot s ∷ load-indirect ∷ mov-to-input ∷ []) ++
  rebuild-walk valSlot tv tb F (s +ℕ 4) lb ++
  (store-at-slot (suc s) ∷ restore-input s ∷ load-indirect-suc ∷ mov-to-input ∷ []) ++
  rebuild-walk valSlot tv tb G (s +ℕ 4) (lb +ℕ lsize F) ++
  (store-at-slot (s +ℕ 2) ∷ instr-alloc-heap 2 ∷ store-at-slot (s +ℕ 3) ∷ mov-to-input ∷
   load-from-slot (suc s) ∷ store-indirect ∷
   load-from-slot (s +ℕ 2) ∷ store-indirect-suc ∷
   load-from-slot (s +ℕ 3) ∷ [])

-- The branching codegen. Precondition: Input1 = root μ-value; `at` = alg
-- trace (Input1 = ⟦F⟧A layer → Output = A). Output := root fold.
-- Plan 0.63 (iii): the branching skeleton splices the algebra ONCE, so its
-- decomposition is `I₁ ++ at ++ I₂`. Same list as before; the old form nested
-- as `(… ++ at ++ B) ++ final-read`.
cata-br-I₁ : Functor → ℕ → ℕ → AbstractTrace
cata-br-I₁ F n1 l1 =
  -- init
  (mov-to-output ∷ store-at-slot (n1 +ℕ 3) ∷
   instr-alloc-heap 2 ∷ store-at-slot (n1 +ℕ 6) ∷ mov-to-input ∷
   instr-load-tag-lit 0 ∷ store-indirect ∷
   load-from-slot (n1 +ℕ 6) ∷ store-at-slot (suc n1) ∷
   load-from-slot (n1 +ℕ 6) ∷ store-at-slot (n1 +ℕ 2) ∷
   load-from-slot (n1 +ℕ 6) ∷ store-at-slot n1 ∷
   load-from-slot (n1 +ℕ 3) ∷ []) ++ push2 n1 (n1 +ℕ 4) (n1 +ℕ 5) ++
  -- flatten
  (instr-ctrl (c-label l1) ∷
   load-from-slot n1 ∷ mov-to-input ∷
   instr-ctrl (c-branch-tag-zero (suc l1)) ∷
   load-indirect-suc ∷ store-at-slot n1 ∷
   load-indirect ∷ mov-to-input ∷ store-at-slot (n1 +ℕ 3) ∷
   load-from-slot (n1 +ℕ 3) ∷ []) ++ push2 (suc n1) (n1 +ℕ 4) (n1 +ℕ 5) ++
  (load-from-slot (n1 +ℕ 3) ∷ mov-to-input ∷ []) ++
  visit-walk n1 (n1 +ℕ 4) (n1 +ℕ 5) F (n1 +ℕ 7) (l1 +ℕ 4) ++
  (instr-ctrl (c-jmp l1) ∷ instr-ctrl (c-label (suc l1)) ∷ []) ++
  -- the fold's prefix, up to the algebra splice
  (instr-ctrl (c-label (l1 +ℕ 2)) ∷
   load-from-slot (suc n1) ∷ mov-to-input ∷
   instr-ctrl (c-branch-tag-zero (l1 +ℕ 3)) ∷
   load-indirect-suc ∷ store-at-slot (suc n1) ∷
   load-indirect ∷ mov-to-input ∷ []) ++
  rebuild-walk (n1 +ℕ 2) (n1 +ℕ 4) (n1 +ℕ 5) F (n1 +ℕ 7) (l1 +ℕ 4 +ℕ lsize F) ++
  (mov-to-input ∷ [])

cata-br-I₂ : ℕ → ℕ → AbstractTrace
cata-br-I₂ n1 l1 =
  push2 (n1 +ℕ 2) (n1 +ℕ 4) (n1 +ℕ 5) ++
  (instr-ctrl (c-jmp (l1 +ℕ 2)) ∷ instr-ctrl (c-label (l1 +ℕ 3)) ∷ []) ++
  -- final-read
  (load-from-slot (n1 +ℕ 2) ∷ mov-to-input ∷ load-indirect ∷ [])

cata-trace-branching : Functor → ℕ → ℕ → AbstractTrace → ℕ × ℕ × AbstractTrace
cata-trace-branching F n1 l1 at =
  n1 +ℕ 7 +ℕ (4 * fsize F) +ℕ 4 , l1 +ℕ 4 +ℕ lsize F +ℕ lsize F ,
  (cata-br-I₁ F n1 l1 ++ at ++ cata-br-I₂ n1 l1)

-- Dispatch the strategy. Nat / branching still route to the Nat codegen
-- (branching = Tier 2, still segfaults); linear gets the Tier-1 codegen.
cata-dispatch : CataStrategy → ℕ → ℕ → AbstractTrace → ℕ × ℕ × AbstractTrace
-- 0 rec positions (`Mu (K _)`): `In` is heap-identity, so the μ-value IS the
-- `⟦F⟧A` layer; `cata alg = alg` on it. No descend/ascend, no slots/labels.
cata-dispatch strat-const     n1 l1 at = n1 , l1 , at
cata-dispatch strat-nat            n1 l1 at = cata-trace-nat n1 l1 at
cata-dispatch strat-linear         n1 l1 at = cata-trace-linear n1 l1 at
cata-dispatch (strat-branching F)  n1 l1 at = cata-trace-branching F n1 l1 at

ir-to-trace' : ∀ {A B} → ℕ → ℕ → IR A B
              → ℕ × ℕ × AbstractTrace × List (ℕ × ℕ × AbstractTrace)

-- ────────────────────────────────────────────────────────────────────
-- Trivial morphisms (no slots needed; mirror SimpleWF.run-*-trace).
-- ────────────────────────────────────────────────────────────────────

ir-to-trace' n l id        = n , l , (mov-to-output ∷ []) , []
-- Plan 0.2.4.5 Stage C γ-revert: uniform packed-pair convention.
-- fst / snd dereference Input1 (= pointer to packed pair record).
-- The split-input optimization (apply pre-unpacks pair into
-- Input1/Input2) was reverted because nested fst/snd (reading from
-- packed compound values) needed layout-discriminating lowering,
-- which adds context tracking complexity that's a hiding place for
-- postulates. Future: type-driven split for register-fittable
-- primitive args, layered as an optimization pass on top of the
-- uniform packed base.
ir-to-trace' n l fst       = n , l , (load-indirect ∷ []) , []
ir-to-trace' n l snd       = n , l , (load-indirect-suc ∷ []) , []
-- Plan 0.2.4.5 D1 (Unit erasure): terminal produces a Unit value
-- which carries no information — emit no instructions. Matches
-- run-terminal's empty-trace WF spec.
ir-to-trace' n l terminal  = n , l , [] , []
ir-to-trace' n l initial   = n , l , (mov-to-output ∷ []) , []

-- ────────────────────────────────────────────────────────────────────
-- Compose: thread output of f into input of g via the abstract bridge.
-- Mirror ComposeWF.compose-trace = f-trace ++ mov-to-input ∷ g-trace.
-- ────────────────────────────────────────────────────────────────────

ir-to-trace' n l (g ∘ f)   =
  let (n1 , l1 , ft , fb) = ir-to-trace' n  l  f
      (n2 , l2 , gt , gb) = ir-to-trace' n1 l1 g
  in n2 , l2 , (ft ++ mov-to-input ∷ gt) , (fb ++ gb)

-- ────────────────────────────────────────────────────────────────────
-- ⟨ f , g ⟩ — pair construction.
-- Mirror PairStackWF.pair-trace:
--   backup-slot = next-slot
--   fst-slot    = suc backup-slot
--   snd-slot    = suc fst-slot
--   pair-trace  =
--     mov-to-output ∷ store-at-slot backup-slot ∷
--     f-trace ++
--     store-at-slot fst-slot ∷ restore-input backup-slot ∷
--     g-trace ++
--     store-at-slot snd-slot ∷ lea-slot fst-slot ∷ []
-- ────────────────────────────────────────────────────────────────────

-- Stack mode: pair lives on stack at [fst-slot, snd-slot].
ir-to-trace' n l (⟨ f , g ⟩ Stack) =
  let backup-slot = n
      fst-slot    = suc backup-slot
      snd-slot    = suc fst-slot
      f-start     = suc snd-slot
      (n1 , l1 , ft , fb) = ir-to-trace' f-start l  f
      (n2 , l2 , gt , gb) = ir-to-trace' n1 l1 g
  in n2 , l2 ,
     (mov-to-output ∷ store-at-slot backup-slot ∷
      ft ++
      store-at-slot fst-slot ∷ restore-input backup-slot ∷
      gt ++
      store-at-slot snd-slot ∷ lea-slot fst-slot ∷ []) ,
     (fb ++ gb)

-- Heap mode: pair lives on the heap (2 cells). Mirrors
-- PairAllocWF setup + mid + post. Uses 4 scratch slots:
-- backup-slot (input ptr), fst-stash (f-result), snd-stash (g-result),
-- pair-stash (heap ptr). f starts at n+4.
ir-to-trace' n l (⟨ f , g ⟩ Heap) =
  let backup-slot = n
      fst-stash   = suc backup-slot
      snd-stash   = suc fst-stash
      pair-stash  = suc snd-stash
      f-start     = suc pair-stash
      (n1 , l1 , ft , fb) = ir-to-trace' f-start l  f
      (n2 , l2 , gt , gb) = ir-to-trace' n1 l1 g
  in n2 , l2 ,
     (mov-to-output ∷ store-at-slot backup-slot ∷
      ft ++
      store-at-slot fst-stash ∷ restore-input backup-slot ∷
      gt ++
      store-at-slot snd-stash ∷
      instr-alloc-heap 2 ∷
      store-at-slot pair-stash ∷
      mov-to-input ∷
      load-from-slot fst-stash ∷
      store-indirect ∷
      load-from-slot snd-stash ∷
      store-indirect-suc ∷
      load-from-slot pair-stash ∷ []) ,
     (fb ++ gb)

-- ────────────────────────────────────────────────────────────────────
-- curry — closure construction.
-- Mirror CurryStackWF.curry-trace closure-slot:
--   mov-to-output ∷                       -- Output := Input1 (env ptr)
--   store-at-slot closure-slot ∷          -- closure[0] := env
--   lea-slot (suc closure-slot) ∷         -- Output := &closure[1]
--   store-at-slot (suc closure-slot) ∷    -- closure[1] := code-ptr
--   lea-slot closure-slot ∷ []            -- Output := closure address
--
-- The body's trace is emitted separately and reachable via the code
-- pointer. For Phase B we don't yet inline the body into the closure
-- record (that's what `apply-full-trace` does in the verified path);
-- runtime closure-call resolution comes via `instr-call-closure` at
-- the apply site.
-- ────────────────────────────────────────────────────────────────────

-- Plan 0.2.4.2 Phase C: closure construction with REAL code-pointer.
--
-- 1. Allocate a fresh body label `this-label = l` (the input
--    counter); bump the counter to `l+1`.
-- 2. Recursively process the body's IR with a fresh slot frame
--    (slot = 0, since the body has its own SysV stack frame —
--    Plan 0.2.4.2 D2). The body may itself contain more curries
--    contributing their bodies; we collect them.
-- 3. Emit the closure-record construction at parent's slots
--    `[closure-slot, suc closure-slot]`. Both Stack and Heap
--    AllocMode use parent's slots in this phase; Phase D will
--    migrate Heap to a static `.bss` bump pool.
-- 4. The crucial fix vs. the old emission: instead of
--    `lea-slot (suc closure-slot)` (which gives the slot's own
--    address), emit `instr-load-code-addr this-label` which
--    per-arch lowers to `lea .L_thunk_<this-label>(%rip), %rax`
--    (the body's actual code address).
--
-- The `_` for AllocMode is intentional in this phase — Stack and
-- Heap diverge only at the record-allocation step, which is still
-- "use parent's slots" for both. Phase D adds the divergence.
-- Stack mode: closure record at slots [closure-slot, closure-slot+1].
-- Plan 0.63 (2b): THE BODY IS INLINE, at its own `curry` clause. Layout:
--
--     <closure construction> ++ c-jmp end ∷ c-thunk this b ∷
--     body-trace ++ c-ret b ∷ c-label end ∷ []
--
-- The jump is what stops the parent FALLING INTO the body (the emitter used
-- to place bodies after main's `ret` TEXT, which the modelled program did not
-- see at all). Inlining HERE rather than in the public `ir-to-trace` wrapper
-- is what keeps every emitter walk a one-line change: they already recurse
-- into `body` at this clause.
ir-to-trace' n l (curry body Stack) =
  let this-label = l
      end-label  = suc l
      l1         = suc (suc l)
      closure-slot = n
      next        = suc (suc closure-slot)
      (body-budget , l2 , body-trace , body-bodies) = ir-to-trace' 0 l1 body
      this-trace  = (mov-to-output ∷
                     store-at-slot closure-slot ∷
                     instr-load-code-addr this-label ∷
                     store-at-slot (suc closure-slot) ∷
                     lea-slot closure-slot ∷
                     instr-ctrl (c-jmp end-label) ∷
                     instr-ctrl (c-thunk this-label body-budget) ∷ []) ++
                    body-trace ++
                    (instr-ctrl (c-ret body-budget) ∷
                     instr-ctrl (c-label end-label) ∷ [])
      all-bodies  = body-bodies
  in next , l2 , this-trace , all-bodies

-- Heap mode: closure record bump-allocated on the heap (2 cells:
-- env-ptr at offset 0, code-address at offset 8). Mirrors
-- CurryAllocWF.curry-heap-trace. Uses 2 scratch slots
-- (env-stash, closure-stash).
ir-to-trace' n l (curry body Heap) =
  let this-label    = l
      end-label     = suc l
      l1            = suc (suc l)
      env-stash     = n
      closure-stash = suc env-stash
      next          = suc closure-stash
      (body-budget , l2 , body-trace , body-bodies) = ir-to-trace' 0 l1 body
      this-trace  = (mov-to-output ∷
                     store-at-slot env-stash ∷
                     instr-alloc-heap 2 ∷
                     store-at-slot closure-stash ∷
                     mov-to-input ∷
                     load-from-slot env-stash ∷
                     store-indirect ∷
                     instr-load-code-addr this-label ∷
                     store-indirect-suc ∷
                     load-from-slot closure-stash ∷
                     instr-ctrl (c-jmp end-label) ∷
                     instr-ctrl (c-thunk this-label body-budget) ∷ []) ++
                    body-trace ++
                    (instr-ctrl (c-ret body-budget) ∷
                     instr-ctrl (c-label end-label) ∷ [])
      all-bodies  = body-bodies
  in next , l2 , this-trace , all-bodies

-- ────────────────────────────────────────────────────────────────────
-- apply — runtime closure call.
-- Mirror ApplyWF.apply-setup-trace + instr-call-closure:
--   pair-slot = next-slot   (used for env+arg backup)
--   apply-setup-trace pair-slot ++ instr-call-closure ∷ []
--
-- Setup loads (closure, arg) from the input pair, stores them at
-- slot/slot+1, points Input1 at the new pair. Then instr-call-closure
-- transfers control to the closure's code pointer (per-arch lowering
-- knows the calling convention).
-- ────────────────────────────────────────────────────────────────────

-- Plan 0.2.4.5 Stage C γ-revert: uniform packed-pair convention.
-- Apply receives a (closure, arg) pair pointer in Input1. It packs
-- a NEW (env, arg) pair at slots [pair-slot, pair-slot+1] for the
-- body and points Input1 at it. Body uses uniform fst/snd =
-- load-indirect / load-indirect-suc to project from packed pairs,
-- regardless of nesting level.
-- Plan 0.53: the new (env, arg) pair MUST be HEAP-allocated, not stacked.
-- A curried callee's body captures its `Input1` (a pointer to THIS pair) into
-- a heap closure; with the pair on the stack that capture points into a
-- transient stack cell that is reused once the frame is popped — the x86-32
-- `arith-lambda-2` dangling read (x86-64/riscv64 only survived by luck). We are
-- heap-only, so build it on the heap (mirrors the `⟨ f , g ⟩ Heap` clause).
ir-to-trace' n l apply =
  let arg-stash  = n
      env-stash  = suc arg-stash
      pair-stash = suc env-stash
  in (suc pair-stash) , l ,
     (load-indirect-suc ∷                -- Output := arg-loc from input pair
      store-at-slot arg-stash ∷          -- stash arg
      load-indirect ∷                    -- Output := closure-loc from input pair
      mov-to-input ∷                     -- Input1 := closure-loc
      instr-save-closure-reg ∷           -- closure-reg := closure (survives below)
      load-indirect ∷                    -- Output := env-loc from closure[0]
      store-at-slot env-stash ∷          -- stash env
      instr-alloc-heap 2 ∷               -- Output := fresh heap pair
      store-at-slot pair-stash ∷
      mov-to-input ∷                     -- Input1 := heap pair
      load-from-slot env-stash ∷
      store-indirect ∷                   -- heap-pair[0] := env
      load-from-slot arg-stash ∷
      store-indirect-suc ∷               -- heap-pair[1] := arg
      load-from-slot pair-stash ∷        -- Output := &heap-pair
      mov-to-input ∷                     -- Input1 := &heap-pair
      instr-call-closure ∷ []) ,
     []

-- ────────────────────────────────────────────────────────────────────
-- SigOp — per-name dispatch handled by per-arch compile-abstract.
-- ────────────────────────────────────────────────────────────────────

ir-to-trace' n l (SigOp si) = n , l , (instr-sigop si ∷ []) , []

-- Plan 0.11: const literal — emit a single load-const abstract instr.
-- 0.47: matching the FitsInReg evidence reduces `⟦ ℕ ⟧-base A` to `⟦ A ⟧`.
ir-to-trace' n l (const fits-int   v) = n , l , (instr-load-const Ty.fits-int   v ∷ []) , []
ir-to-trace' n l (const fits-float v) = n , l , (instr-load-const Ty.fits-float v ∷ []) , []

-- ────────────────────────────────────────────────────────────────────
-- Stubbed — emit `[]`. Not needed for Layer 0; future work.
-- ────────────────────────────────────────────────────────────────────

-- ────────────────────────────────────────────────────────────────────
-- inl / inr — sum construction (Plan 0.13.1 Phase 4).
-- 5-instruction sum payload layout:
--   slot[N]   := SV-Tag t            (t = 0 for inl, 1 for inr)
--   slot[N+1] := payload pointer (Input1)
--   Output    := &slot[N]
-- Mirrors SumRecWF.run-inl / run-inr's expected trace shape (Phase 3).
-- ────────────────────────────────────────────────────────────────────

-- Stack mode: 5-instruction stack lowering at slots [n, n+1].
ir-to-trace' n l (inl Stack) =
  let sum-slot = n
      next     = suc (suc sum-slot)
  in next , l ,
     (instr-load-tag-lit 0 ∷
      store-at-slot sum-slot ∷
      mov-to-output ∷
      store-at-slot (suc sum-slot) ∷
      lea-slot sum-slot ∷ []) ,
     []

ir-to-trace' n l (inr Stack) =
  let sum-slot = n
      next     = suc (suc sum-slot)
  in next , l ,
     (instr-load-tag-lit 1 ∷
      store-at-slot sum-slot ∷
      mov-to-output ∷
      store-at-slot (suc sum-slot) ∷
      lea-slot sum-slot ∷ []) ,
     []

-- Heap mode: bump-allocate a 2-cell heap block, write [tag, payload-ptr].
-- Mirrors SumInlAllocWF.inl-heap-trace / SumInrAllocWF.inr-heap-trace.
-- Uses 2 scratch slots for stashing: payload-stash = n, sum-stash = n+1.
ir-to-trace' n l (inl Heap) =
  let payload-stash = n
      sum-stash     = suc payload-stash
      next          = suc sum-stash
  in next , l ,
     (mov-to-output ∷
      store-at-slot payload-stash ∷
      instr-alloc-heap 2 ∷
      store-at-slot sum-stash ∷
      mov-to-input ∷
      instr-load-tag-lit 0 ∷
      store-indirect ∷
      load-from-slot payload-stash ∷
      store-indirect-suc ∷
      load-from-slot sum-stash ∷ []) ,
     []

ir-to-trace' n l (inr Heap) =
  let payload-stash = n
      sum-stash     = suc payload-stash
      next          = suc sum-stash
  in next , l ,
     (mov-to-output ∷
      store-at-slot payload-stash ∷
      instr-alloc-heap 2 ∷
      store-at-slot sum-stash ∷
      mov-to-input ∷
      instr-load-tag-lit 1 ∷
      store-indirect ∷
      load-from-slot payload-stash ∷
      store-indirect-suc ∷
      load-from-slot sum-stash ∷ []) ,
     []

-- ────────────────────────────────────────────────────────────────────
-- case f g — sum elimination (Plan 0.13.1 Phase 4; FLAT since Plan 0.54
-- item 6, 2026-08-01). Compiled to flat control the way `Cata` already is —
-- the exact shape the x86 lowering always had
-- (`cmp [rdi],0 ; je inl ; <g> ; jmp end ; inl: <f>`):
--
--   c-branch-tag-zero l-inl ∷        -- tag 0 (inl) → jump to f's branch
--   load-indirect-suc ∷ mov-to-input ∷ gt ++   -- inr falls through
--   c-jmp l-end ∷ c-label l-inl ∷
--   load-indirect-suc ∷ mov-to-input ∷ ft ++
--   c-label l-end ∷ []
--
-- Per-branch prologue (payload pointer from sucLoc Input1 into Input1)
-- unchanged. Labels come from the SAME counter as the cata's, so they are
-- collision-free by construction; `instr-case-on-tag` now has NO PRODUCER
-- (it joins the frame ops / `instr-loop` / `lea-indexed` in `FrameFreeI`'s
-- ⊥ set) and the flat machine needs no nested-trace correspondence at all.
-- ────────────────────────────────────────────────────────────────────

ir-to-trace' n l (case f g) =
  let l-inl = l
      l-end = suc l
      (n1 , l1 , ft , fb) = ir-to-trace' n  (suc (suc l)) f
      (n2 , l2 , gt , gb) = ir-to-trace' n1 l1 g
  in n2 , l2 ,
     (instr-ctrl (c-branch-tag-zero l-inl) ∷
      load-indirect-suc ∷ mov-to-input ∷ []) ++
     gt ++
     (instr-ctrl (c-jmp l-end) ∷ instr-ctrl (c-label l-inl) ∷
      load-indirect-suc ∷ mov-to-input ∷ []) ++
     ft ++
     (instr-ctrl (c-label l-end) ∷ []) ,
     (fb ++ gb)

-- In: μ Lambek constructor. Heap-identity — the F-layer node IS the
-- μ-value (same pointer). `mov-to-output` (Output := Input1) passes the
-- pointer through, matching `out-μ` (its inverse) and the heap-identity
-- `run-In` (SumRecWF). Plan 0.27 Phase B: was `[]` (a stub correct only
-- when Output happened to be pre-loaded by a preceding sub-IR).
ir-to-trace' n l (In _ _)       = n , l , (mov-to-output ∷ []) , []
-- out-μ and Out: ν/μ Lambek inverses; semantically Output := Input1.
-- run-X uses `mov-to-output ∷ []`; mirror it so the discharge falls
-- out via the same `transport-trivial` pattern as id/arr/free-heap.
ir-to-trace' n l (out-μ _)      = n , l , (mov-to-output ∷ []) , []
-- Plan 0.29 (M5): NatF catamorphism via the generic fuel loop.
-- descend (count `inr` depth into Input2, Scratch = continue flag) →
-- Scratch := depth → base inl layer + alg → ascend (rebuild inr layer
-- with prev result, alg, Scratch--). Scratch (rbx) survives `alg` (CCC
-- code never touches rbx). Layer builds mirror the inl/inr Heap codegen.
-- Plan 0.36 Phase 2b: dispatch on the functor's strategy (compile-time).
-- Today every strategy routes to `cata-trace-nat`; Tier 1/2 refine it.
ir-to-trace' n l (Cata {F} _ alg) =
  let (n1 , l1 , at , ab) = ir-to-trace' n l alg
      (next , l2 , trace) = cata-dispatch (cata-strategy ⌈ F ⌉F) n1 l1 at
  in next , l2 , trace , ab
ir-to-trace' n l (Para _ _)     = n , l , [] , []
ir-to-trace' n l (Out _)        = n , l , (mov-to-output ∷ []) , []
ir-to-trace' n l (in-ν _ _)     = n , l , [] , []
ir-to-trace' n l (Ana _ _)      = n , l , [] , []
ir-to-trace' n l (Hylo _ _ _ _) = n , l , [] , []
ir-to-trace' n l (Fuse _ _ _ _) = n , l , [] , []

-- free-heap is semantically a no-op (returns its input unchanged).
-- run-free-heap emits `mov-to-output ∷ []` to copy Input1 → Output as
-- the identity behavior; we mirror that exactly so trace correctness
-- discharges via the same transport-trivial pattern as id/arr.
ir-to-trace' n l (free-heap _)  = n , l , (mov-to-output ∷ []) , []

------------------------------------------------------------------------
-- Public wrapper: starts at frontier 0, returns just the trace.
------------------------------------------------------------------------

-- | Plan 0.2.4.2 Phase C: helpers to project main trace / bodies
-- from `ir-to-trace'`'s 4-tuple result.
private
  proj-trace : ℕ × ℕ × AbstractTrace × List (ℕ × ℕ × AbstractTrace) → AbstractTrace
  proj-trace (_ , _ , t , _) = t

  proj-bodies : ℕ × ℕ × AbstractTrace × List (ℕ × ℕ × AbstractTrace) → List (ℕ × ℕ × AbstractTrace)
  proj-bodies (_ , _ , _ , bs) = bs

  proj-budget : ℕ × ℕ × AbstractTrace × List (ℕ × ℕ × AbstractTrace) → ℕ
  proj-budget (n , _ , _ , _) = n

ir-to-trace : ∀ {A B} → IR A B → AbstractTrace
ir-to-trace ir = proj-trace (ir-to-trace' 0 0 ir)

-- | Plan 0.14 (2026-05-17): trace-at-frontier entry point. The
-- runtime path uses `ir-to-trace = ir-to-trace-at-frontier 0` since
-- each function's `subq` allocates a fresh %rsp-relative frame
-- indexing slots from 0. The IR-side correctness proof needs to
-- match the trace's slot indexing to `next-slot alloc` to share
-- slot bindings with the run-X helpers in IR/*WF (which use
-- `next-slot alloc` as their scratch base). At function entry,
-- `next-slot alloc = 0`, so `ir-to-trace-at-frontier 0 ≡ ir-to-trace`
-- and the runtime and proof paths agree.
ir-to-trace-at-frontier : ∀ {A B} → ℕ → IR A B → AbstractTrace
ir-to-trace-at-frontier n ir = proj-trace (ir-to-trace' n 0 ir)

-- | Plan 0.2.4.5 D1: slot budget for an IR's main trace.
-- Used by per-arch codegen to emit `subq budget*8, %rsp` / `addq` around
-- the trace, so all slot accesses are %rsp-relative within a private frame.
ir-stack-budget : ∀ {A B} → IR A B → ℕ
ir-stack-budget ir = proj-budget (ir-to-trace' 0 0 ir)

-- | Plan 0.2.4.2 Phase C: closure-body traces collected for an IR.
-- Each `(label, body-budget, body-trace)` triple becomes a
-- `.L_thunk_<label>:` block, framed by `subq body-budget*8, %rsp` and
-- `addq body-budget*8, %rsp` (frameless model — body has its own
-- %rsp-relative frame, physically disjoint from caller's).
ir-to-bodies : ∀ {A B} → IR A B → List (ℕ × ℕ × AbstractTrace)
ir-to-bodies ir = proj-bodies (ir-to-trace' 0 0 ir)

------------------------------------------------------------------------
-- Plan 0.12 Layer 1: label-counter-threading entry points.
--
-- Each top-level user function (CompiledFun) emits its own thunk
-- bodies. Without threading the label counter, every function's
-- `ir-to-trace'` starts from 0 and produces overlapping
-- `.L_thunk_0`, `.L_thunk_1`, … — the assembler then rejects the
-- module with "symbol already defined".
--
-- These variants take a starting label `l` and return the
-- next-available label alongside the result. `Once.Compile`'s
-- `compileAllWithTarget` left-folds with this counter to keep
-- thunk labels globally unique across the module.
------------------------------------------------------------------------

-- | Trace + next-label, given a starting label counter.
-- (`l₀ → ir → (l₁, trace)` where `l₁ ≥ l₀` and labels in `trace` /
-- emitted bodies are drawn from `[l₀, l₁)`.)
ir-to-trace-from : ∀ {A B} → ℕ → IR A B → ℕ × AbstractTrace
ir-to-trace-from l ir =
  let (_ , l' , t , _) = ir-to-trace' 0 l ir
  in l' , t

-- | Slot budget — independent of label counter; provided in this
-- form for symmetry.
ir-stack-budget-from : ∀ {A B} → ℕ → IR A B → ℕ
ir-stack-budget-from l ir = proj-budget (ir-to-trace' 0 l ir)

-- | Closure bodies + next-label, given a starting label counter.
ir-to-bodies-from : ∀ {A B} → ℕ → IR A B → ℕ × List (ℕ × ℕ × AbstractTrace)
ir-to-bodies-from l ir =
  let (_ , l' , _ , bs) = ir-to-trace' 0 l ir
  in l' , bs
