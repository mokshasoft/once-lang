------------------------------------------------------------------------
-- Once.Backend.X86.Correct.StackInstantiation
--
-- X86 instantiation layer: concrete arithmetic for stack operations.
--
-- This module contains ALL computational arithmetic (∸, +ℕ, *ℕ slot-size) that
-- proves the abstract StackInvariant properties for the X86 backend.
--
-- DESIGN (D041 Architecture):
-- - StackInvariant.agda: abstract types (R15Status, RbpInvariant) - NO arithmetic
-- - StackInstantiation.agda (this file): arithmetic proofs, imports StackInvariant
-- - IR/*.agda (proof layer): imports this module for all stack operations
--
-- The proof layer should use abstract interfaces like:
--   apply-frame-1, abstract-to-rsp-slot-in-stack
-- These hide the arithmetic (rsp ∸ slot-size) behind region-based types.
------------------------------------------------------------------------

module Once.Backend.X86.Correct.StackInstantiation where

open import Once.Type
open import Once.Semantics
open import Once.IR

-- Import slot-size and slots from Syntax (single source of truth)
open import Once.Backend.X86.Syntax public using (slot-size; slots)
open import Once.Backend.X86.Syntax hiding (slot-size; slots)

-- Import computed slot consumption values from CodeGen (derived from instruction lists)
open import Once.Backend.X86.CodeGen public
  using (apply-consumed-slots; pair-setup-consumed-slots;
         thunk-setup-consumed-slots; curry-closure-consumed-slots;
         injection-consumed-slots;
         -- Slot positions (semantic names for frame layout)
         thunk-r15-slot; thunk-rbp-slot;
         pair-r14-slot; pair-r15-slot; pair-rbp-slot)
open import Once.Backend.X86.Semantics
open Once.Backend.X86.Semantics.State

-- Import and re-export abstract types from StackInvariant
open import Once.Backend.X86.Correct.StackInvariant public
  using (R15Status; r15-unused; r15-in-heap; r15-in-code; r15-in-stack;
         RbpInvariant;
         StackInvariant; FrameEvidenceFor;
         stack-write-preserves-heap-r15; stack-write-preserves-code-r15;
         stack-write-preserves-unused-r15; stack-write-preserves-instack-r15;
         stack-write-preserves-r15;
         stack-inv-preserved-unchanged; stack-inv-preserved-r15-unchanged;
         stack-inv-for-code-ptr)
open RbpInvariant public

-- Import region abstractions
open import Once.Backend.Common.MemoryRegions
  using (Region; stack; heap; code; Addr; region-of;
         regions-disjoint; stack≢heap; stack≢code;
         stack-heap-disjoint; stack-code-disjoint;
         zero-not-in-stack; pc-in-code;
         stack-sub-preserves-region;
         StackPointer; slot-addr; sp-distinct; offset-distinct;
         frames-disjoint-slots; slot-in-stack; slot-addr-0-is-base;
         slot-addr-1-is-base+8;
         encode-in-heap; heap-offset)
open import Once.Backend.Common.MemoryRegions using () renaming (addr to sp-addr; in-stack to sp-in-stack)
open import Data.Unit using (⊤; tt)

-- Arithmetic imports (the instantiation layer uses these)
open import Data.Nat using (ℕ; zero; suc; _∸_; _<_; _≤_; _>_; _≥_; s≤s; z≤n; _≤?_) renaming (_+_ to _+ℕ_; _*_ to _*ℕ_)
open import Data.Nat.Properties using (+-comm; +-assoc; ∸-+-assoc; +-∸-assoc; m+n∸n≡m; ≤-trans; +-monoʳ-≤; +-monoʳ-<; m∸n≤m; ≤-refl; ∸-monoʳ-<; m≤n⇒m∸n≡0; ≰⇒>; <⇒≤; <⇒≢; ⊔-mono-≤; m∸n+n≡m; m≤n⊔m; m≤m+n)
open import Relation.Nullary using (yes; no)

-- Import constant comparisons from Arithmetic (replaces verbose s≤s chains)
open import Once.Backend.X86.Correct.Arithmetic
  using (word<pair; word≤pair; word<regs; word≤regs; pair≤regs;
         word≤frame∸word; pair≤frame∸word; regs≤frame∸word;
         word+1≤pair; pair<regs;
         slot1-plus-word≡slot2;
         from-yes-≤; from-yes-<)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst)

------------------------------------------------------------------------
-- Named Constants (D041: replace magic numbers with semantic names)
------------------------------------------------------------------------

-- slot-size and slots are imported from Once.Backend.X86.Syntax
-- Computed slot consumption values are imported from Once.Backend.X86.CodeGen:
--   apply-consumed-slots, pair-setup-consumed-slots,
--   thunk-setup-consumed-slots, curry-closure-consumed-slots

-- Stack frame offsets (derived from slots function)
push-offset : ℕ
push-offset = slots 1                      -- 8: one push instruction

two-push-offset : ℕ
two-push-offset = slots 2                  -- 16: push r15 + push rbp

three-slot-offset : ℕ
three-slot-offset = slots 3                -- 24: three slots

four-slot-offset : ℕ
four-slot-offset = slots 4                 -- 32: four slots

five-slot-offset : ℕ
five-slot-offset = slots 5                 -- 40: five slots

thunk-local-size : ℕ
thunk-local-size = slots 2                 -- 16: sub rsp, 16 in thunk

thunk-frame-size : ℕ
thunk-frame-size = four-slot-offset        -- 32: total thunk frame (2 pushes + 16 local)

pair-frame-size : ℕ
pair-frame-size = five-slot-offset         -- 40: Pair operation (5 slots)

curry-frame-size : ℕ
curry-frame-size = slots 2                 -- 16: Curry closure setup

-- Closure/Pair memory layout offsets
closure-code-offset : ℕ
closure-code-offset = slot-size            -- 8: offset to code pointer in closure
                                           -- closure layout: [env-addr, code-ptr]
                                           -- closure-addr + 0 = env-addr
                                           -- closure-addr + 8 = code-ptr

pair-snd-offset : ℕ
pair-snd-offset = slot-size                -- 8: offset to second element of pair
                                           -- pair layout: [fst, snd]
                                           -- pair-addr + 0 = fst
                                           -- pair-addr + 8 = snd

-- Minimum rsp bounds for safe operations (DEPRECATED: use slot-based constants below)
thunk-min-rsp : ℕ
thunk-min-rsp = thunk-frame-size +ℕ slot-size   -- 40: need > four-slot-offset with buffer

pair-min-rsp : ℕ
pair-min-rsp = pair-frame-size +ℕ slot-size     -- 48: need > five-slot-offset with buffer

apply-min-rsp : ℕ
apply-min-rsp = two-push-offset                -- 16: need > two-push-offset for apply

------------------------------------------------------------------------
-- Slot-based Capacity Constants (for StackCapacity)
--
-- Consumed slot values are COMPUTED from codegen instruction lists and
-- imported from Once.Backend.X86.CodeGen:
--   - apply-consumed-slots (push r15 + call = 2)
--   - pair-setup-consumed-slots (3 pushes + sub 16 = 5)
--   - thunk-setup-consumed-slots (2 pushes + sub 16 = 4)
--   - curry-closure-consumed-slots (sub 16 = 2)
--
-- ARCHITECTURE: See docs/formal/historical/lessons-learned.md
-- - No magic numbers in proofs
-- - All slot counts derived from codegen
-- - ir-stack-requirement computes total dynamically per IR
------------------------------------------------------------------------

-- | Output slots: capacity guaranteed after any operation completes
-- All operations return with at least this much capacity remaining
output-slots : ℕ
output-slots = 2

------------------------------------------------------------------------
-- Capacity constants (literal values with correctness proofs)
--
-- These are defined as literals for fast type checking.
-- The correctness proofs ensure they match the computed values.
-- If codegen changes, the proofs will fail, alerting us to update.
------------------------------------------------------------------------

-- Simple operations: no stack allocation, just output capacity
simple-capacity : ℕ
simple-capacity = 2

-- Apply: push r15 (1) + call (1) + thunk output (2) = 4
apply-capacity : ℕ
apply-capacity = 4

-- Apply intermediate capacities (for threading through state transitions)
-- Capacity after push r15 in apply setup: used for call phase
apply-cap-after-push : ℕ
apply-cap-after-push = apply-capacity ∸ 1  -- = 3

-- Capacity after call in apply: same as output-slots (thunk needs output-slots)
apply-cap-after-call : ℕ
apply-cap-after-call = output-slots  -- = 2

-- Thunk setup: push r15 (1) + push rbp (1) + sub 16 (2) + output (2) = 6
thunk-setup-capacity : ℕ
thunk-setup-capacity = 6

-- Thunk intermediate capacities (for threading through state transitions)
-- Capacity after first push (push r15) in thunk setup
thunk-cap-after-first-push : ℕ
thunk-cap-after-first-push = thunk-setup-capacity ∸ 1

-- Capacity after both pushes (push r15 + push rbp) in thunk setup
thunk-cap-after-pushes : ℕ
thunk-cap-after-pushes = thunk-setup-capacity ∸ 2

-- Semantic relationships: capacity invariants for thunk-setup
-- Used when deriving bounds from capacity proofs
output-fits-thunk-cap : output-slots ≤ thunk-setup-capacity
output-fits-thunk-cap = from-yes-≤ (output-slots ≤? thunk-setup-capacity)

-- Slot positions are imported from CodeGen (thunk-r15-slot, thunk-rbp-slot, etc.)
-- Slot position inequalities are defined above (thunk-rbp-slot≤thunk-setup, etc.)

-- Pair: push r14 (1) + push r15 (1) + push rbp (1) + sub 16 (2) + output (2) = 7
pair-capacity : ℕ
pair-capacity = 7

-- Curry closure: sub rsp,16 (2) + output (2) = 4
curry-closure-capacity : ℕ
curry-closure-capacity = 4

-- Inl/Inr: need to allocate output pair (tag + value), require 4 slots
inl-inr-capacity : ℕ
inl-inr-capacity = 4

-- Correctness proofs: ensure literals match computed values from codegen
-- These will fail if codegen changes and we need to update the literals
private
  apply-capacity-correct : apply-capacity ≡ apply-consumed-slots +ℕ output-slots
  apply-capacity-correct = refl

  thunk-setup-capacity-correct : thunk-setup-capacity ≡ thunk-setup-consumed-slots +ℕ output-slots
  thunk-setup-capacity-correct = refl

  pair-capacity-correct : pair-capacity ≡ pair-setup-consumed-slots +ℕ output-slots
  pair-capacity-correct = refl

  curry-closure-capacity-correct : curry-closure-capacity ≡ curry-closure-consumed-slots +ℕ output-slots
  curry-closure-capacity-correct = refl

-- Semantic capacity relationships: setup phases fit in full capacity
-- Single source of truth for these inequalities
pair-setup-fits-capacity : pair-setup-consumed-slots ≤ pair-capacity
pair-setup-fits-capacity = m≤m+n pair-setup-consumed-slots output-slots

thunk-setup-fits-capacity : thunk-setup-consumed-slots ≤ thunk-setup-capacity
thunk-setup-fits-capacity = m≤m+n thunk-setup-consumed-slots output-slots

apply-setup-fits-capacity : apply-consumed-slots ≤ apply-capacity
apply-setup-fits-capacity = m≤m+n apply-consumed-slots output-slots

-- Cross-capacity relationships: thunk-setup fits in pair capacity
-- Used when curry thunk setup runs with pair capacity bound
thunk-setup-fits-pair-capacity : thunk-setup-capacity ≤ pair-capacity
thunk-setup-fits-pair-capacity = from-yes-≤ (thunk-setup-capacity ≤? pair-capacity)

inl-inr-capacity-correct : inl-inr-capacity ≡ injection-consumed-slots +ℕ output-slots
inl-inr-capacity-correct = refl

------------------------------------------------------------------------
-- Slot position inequalities (semantic proofs that slots fit in frames)
------------------------------------------------------------------------
-- These prove that specific saved register slots are within the frame bounds.
-- Derived algebraically from the slot position and frame size definitions.

-- Thunk frame: rbp is at slot 2, frame has 4 slots
thunk-rbp-slot≤thunk-setup : thunk-rbp-slot ≤ thunk-setup-consumed-slots
thunk-rbp-slot≤thunk-setup = from-yes-≤ (thunk-rbp-slot ≤? thunk-setup-consumed-slots)

-- Thunk slot positions fit in capacity (for slot-based bounds)
-- r15 is at slot 1, capacity is 6, so 1 ≤ 6
r15-slot-fits-thunk-cap : thunk-r15-slot ≤ thunk-setup-capacity
r15-slot-fits-thunk-cap = from-yes-≤ (thunk-r15-slot ≤? thunk-setup-capacity)

-- rbp is at slot 2, capacity is 6, so 2 ≤ 6
rbp-slot-fits-thunk-cap : thunk-rbp-slot ≤ thunk-setup-capacity
rbp-slot-fits-thunk-cap = from-yes-≤ (thunk-rbp-slot ≤? thunk-setup-capacity)

-- Pair frame: rbp is at slot 3, frame has 5 slots
pair-rbp-slot≤pair-setup : pair-rbp-slot ≤ pair-setup-consumed-slots
pair-rbp-slot≤pair-setup = from-yes-≤ (pair-rbp-slot ≤? pair-setup-consumed-slots)

------------------------------------------------------------------------
-- RSP Delta: How much RSP changes (decreases) during IR execution
------------------------------------------------------------------------
-- Most IRs preserve rsp (delta = 0). Curry allocates closure on stack (delta = 2).
-- This is used for proper capacity threading through compose.
-- MUST be defined before ir-stack-requirement since compose uses it.

ir-rsp-delta : ∀ {A B} → IR A B → ℕ
-- Simple operations: preserve rsp
ir-rsp-delta id = 0
ir-rsp-delta fst = 0
ir-rsp-delta snd = 0
ir-rsp-delta terminal = 0
ir-rsp-delta initial = 0
ir-rsp-delta fold = 0
ir-rsp-delta unfold = 0
ir-rsp-delta arr = 0
ir-rsp-delta (Prim _) = 0
-- Injections: allocate slots on stack for tag+value, do NOT restore
-- Value derived from CodeGen.injection-consumed-slots (computes from inl-instrs)
ir-rsp-delta inl = injection-consumed-slots
ir-rsp-delta inr = injection-consumed-slots
-- Compose: total delta is sum of deltas (both execute)
ir-rsp-delta (g ∘ f) = ir-rsp-delta f +ℕ ir-rsp-delta g
-- Pair/Case: setup/teardown balance, rsp restored
ir-rsp-delta ⟨ f , g ⟩ = 0
ir-rsp-delta [ l , r ] = 0
-- Curry: allocates slots for closure, does NOT restore
-- Value derived from CodeGen.curry-closure-consumed-slots
ir-rsp-delta (curry f) = curry-closure-consumed-slots
-- Apply: call/ret balance, rsp restored
ir-rsp-delta apply = 0

------------------------------------------------------------------------
-- Dynamic IR Stack Requirement (computed from IR structure)
--
-- This function computes the exact stack capacity needed for each IR.
-- For compose/pair/case, it takes the max of sub-operations.
-- For curry, it includes the inner thunk's requirement.
-- For apply, we use a fixed bound (thunk requirement unknown at static time).
--
-- NOTE: Uses literal slot values for fast type checking.
------------------------------------------------------------------------

open import Data.Nat using (_⊔_)  -- max

-- | Compute stack requirement for an IR operation dynamically
-- This is the capacity dispatcher should require: ir-stack-requirement ir
ir-stack-requirement : ∀ {A B} → IR A B → ℕ
-- Simple operations: no stack allocation (literal 2)
ir-stack-requirement id = 2
ir-stack-requirement fst = 2
ir-stack-requirement snd = 2
ir-stack-requirement terminal = 2
ir-stack-requirement initial = 2  -- unreachable, but need a bound
-- Recursive types: isomorphisms, no stack allocation
ir-stack-requirement fold = 2
ir-stack-requirement unfold = 2
-- Effect lifting: essentially identity at runtime
ir-stack-requirement arr = 2
-- Primitives: external operations, assume simple capacity
ir-stack-requirement (Prim _) = 2
-- Injections: need capacity for tag+value write (literal 4)
ir-stack-requirement inl = 4
ir-stack-requirement inr = 4
-- Compose: run f, then g. Account for rsp delta: after f uses delta slots,
-- we need enough remaining for g. So: max(req f, delta f + req g)
ir-stack-requirement (g ∘ f) = ir-stack-requirement f ⊔ (ir-rsp-delta f +ℕ ir-stack-requirement g)
-- Pair: setup frame consumes pair-setup-consumed-slots, then run f, then g
ir-stack-requirement ⟨ f , g ⟩ = pair-setup-consumed-slots +ℕ (ir-stack-requirement f ⊔ ir-stack-requirement g)
-- Case: frame setup (1 slot for saved rbp), then run left or right branch
ir-stack-requirement [ l , r ] = 1 +ℕ (ir-stack-requirement l ⊔ ir-stack-requirement r)
-- Curry: closure setup (2) + thunk setup (4) + inner requirement
ir-stack-requirement (curry f) = 2 +ℕ (4 +ℕ ir-stack-requirement f)
-- Apply: calls thunk from closure (literal 4)
ir-stack-requirement apply = 4

------------------------------------------------------------------------
-- Output Capacity (what remains after IR execution)
--
-- After an IR runs, the stack capacity is reduced by ir-rsp-delta.
-- Output capacity = input requirement - consumed delta
------------------------------------------------------------------------

-- | Compute output capacity after IR execution
-- This is the capacity available after the IR has run.
ir-output-capacity : ∀ {A B} → IR A B → ℕ
ir-output-capacity ir = ir-stack-requirement ir ∸ ir-rsp-delta ir

-- | RSP delta never exceeds stack requirement
-- This is fundamental: we can't consume more stack than we require.
-- Proof by case analysis on each IR constructor.
ir-delta-≤-requirement : ∀ {A B} (ir : IR A B) → ir-rsp-delta ir ≤ ir-stack-requirement ir
ir-delta-≤-requirement id = z≤n
ir-delta-≤-requirement fst = z≤n
ir-delta-≤-requirement snd = z≤n
ir-delta-≤-requirement terminal = z≤n
ir-delta-≤-requirement initial = z≤n
ir-delta-≤-requirement fold = z≤n
ir-delta-≤-requirement unfold = z≤n
ir-delta-≤-requirement arr = z≤n
ir-delta-≤-requirement (Prim _) = z≤n
ir-delta-≤-requirement inl = m≤m+n injection-consumed-slots output-slots  -- 2 ≤ 4
ir-delta-≤-requirement inr = m≤m+n injection-consumed-slots output-slots  -- 2 ≤ 4
ir-delta-≤-requirement (g ∘ f) =
  let δf = ir-rsp-delta f
      δg = ir-rsp-delta g
      req-f = ir-stack-requirement f
      req-g = ir-stack-requirement g
      -- Need: δf + δg ≤ max(req-f, δf + req-g)
      -- δg ≤ req-g by IH, so δf + δg ≤ δf + req-g ≤ max(...)
      δg≤req-g = ir-delta-≤-requirement g
      δf+δg≤δf+req-g = +-monoʳ-≤ δf δg≤req-g
  in ≤-trans δf+δg≤δf+req-g (m≤n⊔m req-f (δf +ℕ req-g))
ir-delta-≤-requirement ⟨ f , g ⟩ = z≤n  -- delta = 0
ir-delta-≤-requirement [ l , r ] = z≤n  -- delta = 0
ir-delta-≤-requirement (curry f) = m≤m+n curry-closure-consumed-slots _  -- 2 ≤ 2 + (4 + req f)
ir-delta-≤-requirement apply = z≤n  -- delta = 0

-- | Requirement = delta + output (exact decomposition)
-- Since delta ≤ requirement, we have requirement ∸ delta + delta = requirement
ir-requirement-split : ∀ {A B} (ir : IR A B) →
  ir-stack-requirement ir ≡ ir-rsp-delta ir +ℕ ir-output-capacity ir
ir-requirement-split ir = trans (sym (m∸n+n≡m (ir-delta-≤-requirement ir)))
                                (+-comm (ir-output-capacity ir) (ir-rsp-delta ir))

-- | Inner requirement for pair: maximum of f and g requirements
-- This is what's needed AFTER the pair-setup-consumed-slots frame setup is complete.
-- Semantically: pair-inner-requirement f g = ir-stack-requirement ⟨ f , g ⟩ ∸ pair-setup-consumed-slots
pair-inner-requirement : ∀ {A B C} → IR C A → IR C B → ℕ
pair-inner-requirement f g = ir-stack-requirement f ⊔ ir-stack-requirement g

-- | Pair setup slots ≤ pair requirement
-- Follows from: ir-stack-requirement ⟨ f , g ⟩ = pair-setup-consumed-slots +ℕ inner-req
pair-setup≤pair-req : ∀ {A B C} (f : IR C A) (g : IR C B) →
  pair-setup-consumed-slots ≤ ir-stack-requirement ⟨ f , g ⟩
pair-setup≤pair-req f g = m≤m+n pair-setup-consumed-slots (pair-inner-requirement f g)

-- | Output slots ≤ pair setup consumed slots
-- Both are computed from instruction lists: output-slots = 2, pair-setup-consumed-slots = 5
output-slots≤pair-setup : output-slots ≤ pair-setup-consumed-slots
output-slots≤pair-setup = from-yes-≤ (output-slots ≤? pair-setup-consumed-slots)

-- | Output slots ≤ pair requirement (transitivity)
output-slots≤pair-req : ∀ {A B C} (f : IR C A) (g : IR C B) →
  output-slots ≤ ir-stack-requirement ⟨ f , g ⟩
output-slots≤pair-req f g = ≤-trans output-slots≤pair-setup (pair-setup≤pair-req f g)

-- | All IRs have output capacity ≥ 2
-- This is the minimum capacity any IR leaves after execution.
-- Used to derive weaker bounds from dynamic ir-output-capacity.
--
-- Proof sketch for compose (g ∘ f):
--   output(g ∘ f) = max(req f, delta f + req g) - (delta f + delta g)
--   Case 1 (req f ≥ delta f + req g): output = out f - delta g ≥ 2 (complex monus arithmetic)
--   Case 2 (req f < delta f + req g): output = out g ≥ 2 by IH
------------------------------------------------------------------------
-- Centralized Arithmetic Helpers (D041: define early for use throughout)
------------------------------------------------------------------------

-- | Stack addresses are never 0 (moved from MemoryRegions to keep it high-level)
stack-addr-nonzero : ∀ a → region-of a ≡ stack → a ≢ 0
stack-addr-nonzero a a-in-stack a≡0 =
  zero-not-in-stack (subst (λ x → region-of x ≡ stack) a≡0 a-in-stack)

-- | Common bound conversion: rsp > two-push-offset implies rsp > slot-size
-- Used in many proofs where we have two-slot bound but need single-slot bound
rsp>slot-from-2slot : ∀ {n} → n > two-push-offset → n > slot-size
rsp>slot-from-2slot n>2slot = ≤-trans word+1≤pair (<⇒≤ n>2slot)

-- | Generic subtraction-less-than helper (m ∸ n < m when m > n and n > 0)
-- Centralized to avoid defining this pattern in every proof
m∸n<m-when-m>n : ∀ m n → n > 0 → m > n → m ∸ n < m
m∸n<m-when-m>n (suc m') (suc n') _ (s≤s m'≥n') = s≤s (m∸n≤m m' n')

------------------------------------------------------------------------
-- Stack Capacity (X86 instantiation)
------------------------------------------------------------------------

-- | Stack capacity: X86-specific proof that stack can accommodate n slots.
-- Each slot is 8 bytes (one word on x86-64).
--
-- This type contains ARITHMETIC in its fields (rsp > n *ℕ slot-size).
-- The proof layer should not use these fields directly.
-- Instead, use the abstract interface functions below.
record StackCapacity (s : State) (n : ℕ) : Set where
  field
    -- rsp points to stack region
    rsp-in-stack : region-of (readReg (regs s) rsp) ≡ stack

    -- rsp has sufficient space for n slots (concrete X86 bound)
    rsp-sufficient : readReg (regs s) rsp > n *ℕ slot-size

    -- After allocating k slots (k ≤ n), still in stack region
    capacity-maintained : ∀ k → k ≤ n →
      region-of (readReg (regs s) rsp ∸ (k *ℕ slot-size)) ≡ stack

open StackCapacity public

------------------------------------------------------------------------
-- IR Stack Frame Requirements
--
-- Each IR operation has a known stack frame requirement. These functions
-- allow computing the required input capacity to ensure safe execution.
------------------------------------------------------------------------

-- | Stack slots needed by each IR operation
-- This reflects the maximum stack depth used during execution:
-- - Simple operations (id, fst, snd, etc): 0 slots
-- - Curry: 5 slots (push r15, push rbp, sub 24 = 3 more slots)
-- - Apply: 3 slots (call pushes ret addr, thunk uses 2 more)
ir-frame-slots : ∀ {A B} → IR A B → ℕ
ir-frame-slots id             = 0
ir-frame-slots (_ ∘ _)        = 0   -- Composition itself doesn't allocate
ir-frame-slots fst            = 0
ir-frame-slots snd            = 0
ir-frame-slots ⟨ _ , _ ⟩      = 5   -- Pair: push r14, push r15, push rbp, sub rsp 16
ir-frame-slots inl            = 0
ir-frame-slots inr            = 0
ir-frame-slots [ _ , _ ]      = 0   -- Case branches don't allocate
ir-frame-slots terminal       = 0
ir-frame-slots initial        = 0
ir-frame-slots (curry _)      = 5   -- push r15, push rbp, sub rsp 24
ir-frame-slots apply          = 3   -- call + thunk frame setup
ir-frame-slots fold           = 0
ir-frame-slots unfold         = 0
ir-frame-slots arr            = 0
ir-frame-slots (Prim _)       = 0

-- | Input capacity needed: frame slots + output capacity (2)
-- This ensures that after the operation, we have capacity for 2 slots.
ir-input-capacity : ∀ {A B} → IR A B → ℕ
ir-input-capacity ir = ir-frame-slots ir +ℕ 2

------------------------------------------------------------------------
-- Capacity Operations (arithmetic-heavy)
------------------------------------------------------------------------

-- | Capacity is preserved when rsp doesn't change
capacity-preserved-rsp-unchanged : ∀ (s s' : State) (n : ℕ) →
  StackCapacity s n →
  readReg (regs s') rsp ≡ readReg (regs s) rsp →
  StackCapacity s' n
capacity-preserved-rsp-unchanged s s' n cap rsp-eq = record
  { rsp-in-stack = trans (cong region-of rsp-eq) (rsp-in-stack cap)
  ; rsp-sufficient = subst (_> n *ℕ slot-size) (sym rsp-eq) (rsp-sufficient cap)
  ; capacity-maintained = λ k k≤n →
      trans (cong (λ r → region-of (r ∸ (k *ℕ slot-size))) rsp-eq)
            (capacity-maintained cap k k≤n)
  }

-- | After push (rsp -= slot-size), capacity decreases by 1
capacity-after-push : ∀ (s s' : State) (n : ℕ) →
  StackCapacity s (suc n) →
  readReg (regs s') rsp ≡ readReg (regs s) rsp ∸ slot-size →
  StackCapacity s' n
capacity-after-push s s' n cap rsp-eq = record
  { rsp-in-stack = rsp'-in-stack
  ; rsp-sufficient = rsp'-sufficient
  ; capacity-maintained = cap-maintained
  }
  where
    open import Data.Nat.Properties using (m+n∸n≡m; m∸n+n≡m; <⇒≤; +-monoʳ-<)

    old-rsp = readReg (regs s) rsp
    new-rsp = readReg (regs s') rsp

    rsp'-in-stack : region-of new-rsp ≡ stack
    rsp'-in-stack = trans (cong region-of rsp-eq) (capacity-maintained cap 1 (s≤s z≤n))

    rsp'-sufficient : new-rsp > n *ℕ slot-size
    rsp'-sufficient = subst (_> n *ℕ slot-size) (sym rsp-eq) sub-lemma
      where
        open import Data.Nat.Properties using (≤-<-trans; m≤m+n; +-cancelʳ-<; +-comm)

        old-bound : old-rsp > slot-size +ℕ n *ℕ slot-size
        old-bound = rsp-sufficient cap

        slot-size≤old : slot-size ≤ old-rsp
        slot-size≤old = <⇒≤ (≤-<-trans (m≤m+n slot-size (n *ℕ slot-size)) old-bound)

        old-rsp-eq : (old-rsp ∸ slot-size) +ℕ slot-size ≡ old-rsp
        old-rsp-eq = m∸n+n≡m slot-size≤old

        old-bound' : old-rsp > n *ℕ slot-size +ℕ slot-size
        old-bound' = subst (old-rsp >_) (+-comm slot-size (n *ℕ slot-size)) old-bound

        sub-lemma : old-rsp ∸ slot-size > n *ℕ slot-size
        sub-lemma = +-cancelʳ-< slot-size (n *ℕ slot-size) (old-rsp ∸ slot-size) bound-step
          where
            bound-step : n *ℕ slot-size +ℕ slot-size < (old-rsp ∸ slot-size) +ℕ slot-size
            bound-step = subst (n *ℕ slot-size +ℕ slot-size <_) (sym old-rsp-eq) old-bound'

    cap-maintained : ∀ k → k ≤ n → region-of (new-rsp ∸ (k *ℕ slot-size)) ≡ stack
    cap-maintained k k≤n =
      let 1+k≤sn : (1 +ℕ k) ≤ suc n
          1+k≤sn = s≤s k≤n
          old-cap-at-1+k : region-of (old-rsp ∸ ((1 +ℕ k) *ℕ slot-size)) ≡ stack
          old-cap-at-1+k = capacity-maintained cap (1 +ℕ k) 1+k≤sn
          step1 : (old-rsp ∸ slot-size) ∸ (k *ℕ slot-size) ≡ old-rsp ∸ (slot-size +ℕ k *ℕ slot-size)
          step1 = ∸-+-assoc old-rsp slot-size (k *ℕ slot-size)
          arith-eq : slot-size +ℕ k *ℕ slot-size ≡ (1 +ℕ k) *ℕ slot-size
          arith-eq = refl
          addr-eq : new-rsp ∸ (k *ℕ slot-size) ≡ old-rsp ∸ ((1 +ℕ k) *ℕ slot-size)
          addr-eq = trans (cong (λ r → r ∸ (k *ℕ slot-size)) rsp-eq)
                          (trans step1 (cong (old-rsp ∸_) arith-eq))
      in trans (cong region-of addr-eq) old-cap-at-1+k

-- | After pop (rsp += slot-size), capacity increases by 1
capacity-after-pop : ∀ (s s' : State) (n : ℕ) →
  StackCapacity s n →
  readReg (regs s') rsp ≡ readReg (regs s) rsp +ℕ slot-size →
  region-of (readReg (regs s') rsp) ≡ stack →
  StackCapacity s' (suc n)
capacity-after-pop s s' n cap rsp-eq new-rsp-in-stack = record
  { rsp-in-stack = new-rsp-in-stack
  ; rsp-sufficient = rsp'-sufficient
  ; capacity-maintained = cap-maintained
  }
  where
    open import Data.Nat.Properties using (+-monoʳ-<; +-comm)

    old-rsp = readReg (regs s) rsp
    new-rsp = readReg (regs s') rsp

    rsp'-sufficient : new-rsp > (suc n) *ℕ slot-size
    rsp'-sufficient = subst (_> (suc n) *ℕ slot-size) (sym rsp-eq) add-lemma
      where
        open import Data.Nat.Properties using (+-monoˡ-<)
        step1 : old-rsp +ℕ slot-size > n *ℕ slot-size +ℕ slot-size
        step1 = +-monoˡ-< slot-size (rsp-sufficient cap)
        add-lemma : old-rsp +ℕ slot-size > (suc n) *ℕ slot-size
        add-lemma = subst (old-rsp +ℕ slot-size >_) (+-comm (n *ℕ slot-size) slot-size) step1

    cap-maintained : ∀ k → k ≤ suc n → region-of (new-rsp ∸ (k *ℕ slot-size)) ≡ stack
    cap-maintained zero _ = new-rsp-in-stack
    cap-maintained (suc k) (s≤s k≤n) = trans (cong region-of addr-eq) old-cap-at-k
      where
        open import Data.Nat.Properties using (m+n∸n≡m)
        old-cap-at-k : region-of (old-rsp ∸ (k *ℕ slot-size)) ≡ stack
        old-cap-at-k = capacity-maintained cap k k≤n
        step1 : (old-rsp +ℕ slot-size) ∸ (slot-size +ℕ k *ℕ slot-size) ≡ ((old-rsp +ℕ slot-size) ∸ slot-size) ∸ (k *ℕ slot-size)
        step1 = sym (∸-+-assoc (old-rsp +ℕ slot-size) slot-size (k *ℕ slot-size))
        step2 : (old-rsp +ℕ slot-size) ∸ slot-size ≡ old-rsp
        step2 = m+n∸n≡m old-rsp slot-size
        arith-eq : (old-rsp +ℕ slot-size) ∸ ((suc k) *ℕ slot-size) ≡ old-rsp ∸ (k *ℕ slot-size)
        arith-eq = trans step1 (cong (_∸ (k *ℕ slot-size)) step2)
        addr-eq : new-rsp ∸ ((suc k) *ℕ slot-size) ≡ old-rsp ∸ (k *ℕ slot-size)
        addr-eq = trans (cong (λ r → r ∸ ((suc k) *ℕ slot-size)) rsp-eq) arith-eq

-- | After sub rsp, 16 (rsp -= 16), capacity decreases by 2
capacity-after-alloc-2-slots : ∀ (s s' : State) (n : ℕ) →
  StackCapacity s (suc (suc n)) →
  readReg (regs s') rsp ≡ readReg (regs s) rsp ∸ two-push-offset →
  StackCapacity s' n
capacity-after-alloc-2-slots s s' n cap rsp-eq = record
  { rsp-in-stack = rsp'-in-stack
  ; rsp-sufficient = rsp'-sufficient
  ; capacity-maintained = cap-maintained
  }
  where
    open import Data.Nat.Properties using (m∸n+n≡m; <⇒≤; ≤-<-trans; m≤m+n; +-cancelʳ-<; +-comm)

    old-rsp = readReg (regs s) rsp
    new-rsp = readReg (regs s') rsp

    rsp'-in-stack : region-of new-rsp ≡ stack
    rsp'-in-stack = trans (cong region-of rsp-eq) (capacity-maintained cap 2 (s≤s (s≤s z≤n)))

    rsp'-sufficient : new-rsp > n *ℕ slot-size
    rsp'-sufficient = subst (_> n *ℕ slot-size) (sym rsp-eq) sub-lemma
      where
        old-bound : old-rsp > two-push-offset +ℕ n *ℕ slot-size
        old-bound = rsp-sufficient cap

        two-push≤old : two-push-offset ≤ old-rsp
        two-push≤old = <⇒≤ (≤-<-trans (m≤m+n two-push-offset (n *ℕ slot-size)) old-bound)

        old-rsp-eq : (old-rsp ∸ two-push-offset) +ℕ two-push-offset ≡ old-rsp
        old-rsp-eq = m∸n+n≡m two-push≤old

        old-bound' : old-rsp > n *ℕ slot-size +ℕ two-push-offset
        old-bound' = subst (old-rsp >_) (+-comm two-push-offset (n *ℕ slot-size)) old-bound

        sub-lemma : old-rsp ∸ two-push-offset > n *ℕ slot-size
        sub-lemma = +-cancelʳ-< two-push-offset (n *ℕ slot-size) (old-rsp ∸ two-push-offset) bound-step
          where
            bound-step : n *ℕ slot-size +ℕ two-push-offset < (old-rsp ∸ two-push-offset) +ℕ two-push-offset
            bound-step = subst (n *ℕ slot-size +ℕ two-push-offset <_) (sym old-rsp-eq) old-bound'

    cap-maintained : ∀ k → k ≤ n → region-of (new-rsp ∸ (k *ℕ slot-size)) ≡ stack
    cap-maintained k k≤n =
      let 2+k≤ssn : (2 +ℕ k) ≤ suc (suc n)
          2+k≤ssn = s≤s (s≤s k≤n)
          old-cap-at-2+k : region-of (old-rsp ∸ ((2 +ℕ k) *ℕ slot-size)) ≡ stack
          old-cap-at-2+k = capacity-maintained cap (2 +ℕ k) 2+k≤ssn
          step1 : (old-rsp ∸ two-push-offset) ∸ (k *ℕ slot-size) ≡ old-rsp ∸ (two-push-offset +ℕ k *ℕ slot-size)
          step1 = ∸-+-assoc old-rsp two-push-offset (k *ℕ slot-size)
          arith-eq : two-push-offset +ℕ k *ℕ slot-size ≡ (2 +ℕ k) *ℕ slot-size
          arith-eq = refl
          addr-eq : new-rsp ∸ (k *ℕ slot-size) ≡ old-rsp ∸ ((2 +ℕ k) *ℕ slot-size)
          addr-eq = trans (cong (λ r → r ∸ (k *ℕ slot-size)) rsp-eq)
                          (trans step1 (cong (old-rsp ∸_) arith-eq))
      in trans (cong region-of addr-eq) old-cap-at-2+k

-- | After add rsp, 16 (rsp += 16), capacity increases by 2
capacity-after-dealloc-2-slots : ∀ (s s' : State) (n : ℕ) →
  StackCapacity s n →
  readReg (regs s') rsp ≡ readReg (regs s) rsp +ℕ two-push-offset →
  region-of (readReg (regs s') rsp) ≡ stack →
  StackCapacity s' (suc (suc n))
capacity-after-dealloc-2-slots s s' n cap rsp-eq new-rsp-in-stack = record
  { rsp-in-stack = new-rsp-in-stack
  ; rsp-sufficient = rsp'-sufficient
  ; capacity-maintained = cap-maintained
  }
  where
    open import Data.Nat.Properties using (+-monoʳ-<; +-comm; m≤m+n)

    old-rsp = readReg (regs s) rsp
    new-rsp = readReg (regs s') rsp

    rsp'-sufficient : new-rsp > (suc (suc n)) *ℕ slot-size
    rsp'-sufficient = subst (_> (suc (suc n)) *ℕ slot-size) (sym rsp-eq) add-lemma
      where
        open import Data.Nat.Properties using (+-monoˡ-<)
        step1 : old-rsp +ℕ two-push-offset > n *ℕ slot-size +ℕ two-push-offset
        step1 = +-monoˡ-< two-push-offset (rsp-sufficient cap)
        add-lemma : old-rsp +ℕ two-push-offset > (suc (suc n)) *ℕ slot-size
        add-lemma = subst (old-rsp +ℕ two-push-offset >_) (+-comm (n *ℕ slot-size) two-push-offset) step1

    cap-maintained : ∀ k → k ≤ suc (suc n) → region-of (new-rsp ∸ (k *ℕ slot-size)) ≡ stack
    cap-maintained zero _ = new-rsp-in-stack
    cap-maintained 1 _ = stack-sub-preserves-region new-rsp slot-size new-rsp-in-stack slot-size≤new-rsp
      where
        open import Data.Nat.Properties using (<⇒≤; +-monoˡ-<; <-trans)
        rsp>0 : old-rsp > 0
        rsp>0 = ≤-trans (s≤s z≤n) (rsp-sufficient cap)
        step1 : old-rsp +ℕ two-push-offset > two-push-offset
        step1 = +-monoˡ-< two-push-offset rsp>0
        step2 : two-push-offset > slot-size
        step2 = word<pair
        new-rsp-bound : new-rsp > slot-size
        new-rsp-bound = subst (_> slot-size) (sym rsp-eq) (<-trans step2 step1)
        slot-size≤new-rsp : slot-size ≤ new-rsp
        slot-size≤new-rsp = <⇒≤ new-rsp-bound
    cap-maintained (suc (suc k)) (s≤s (s≤s k≤n)) = trans (cong region-of addr-eq) old-cap-at-k
      where
        open import Data.Nat.Properties using (m+n∸n≡m)
        old-cap-at-k : region-of (old-rsp ∸ (k *ℕ slot-size)) ≡ stack
        old-cap-at-k = capacity-maintained cap k k≤n
        step1 : (old-rsp +ℕ two-push-offset) ∸ (two-push-offset +ℕ k *ℕ slot-size) ≡ ((old-rsp +ℕ two-push-offset) ∸ two-push-offset) ∸ (k *ℕ slot-size)
        step1 = sym (∸-+-assoc (old-rsp +ℕ two-push-offset) two-push-offset (k *ℕ slot-size))
        step2 : (old-rsp +ℕ two-push-offset) ∸ two-push-offset ≡ old-rsp
        step2 = m+n∸n≡m old-rsp two-push-offset
        arith-eq : (old-rsp +ℕ two-push-offset) ∸ ((suc (suc k)) *ℕ slot-size) ≡ old-rsp ∸ (k *ℕ slot-size)
        arith-eq = trans step1 (cong (_∸ (k *ℕ slot-size)) step2)
        addr-eq : new-rsp ∸ ((suc (suc k)) *ℕ slot-size) ≡ old-rsp ∸ (k *ℕ slot-size)
        addr-eq = trans (cong (λ r → r ∸ ((suc (suc k)) *ℕ slot-size)) rsp-eq) arith-eq

-- | When RSP is restored (rsp s' = rsp s), capacity is preserved
-- Used by apply which restores RSP via push/pop pattern
capacity-when-rsp-restored : ∀ (s s' : State) (n : ℕ) →
  StackCapacity s n →
  readReg (regs s') rsp ≡ readReg (regs s) rsp →
  StackCapacity s' n
capacity-when-rsp-restored s s' n cap rsp-eq = record
  { rsp-in-stack = subst (λ r → region-of r ≡ stack) (sym rsp-eq) (rsp-in-stack cap)
  ; rsp-sufficient = subst (_> n *ℕ slot-size) (sym rsp-eq) (rsp-sufficient cap)
  ; capacity-maintained = λ k k≤n → subst (λ r → region-of (r ∸ k *ℕ slot-size) ≡ stack)
                                          (sym rsp-eq) (capacity-maintained cap k k≤n)
  }

------------------------------------------------------------------------
-- Deriving Address Properties from Capacity
------------------------------------------------------------------------

-- | With capacity n ≥ 2, address rsp - 16 is in stack region
slot-2-addr-in-stack : ∀ (s : State) →
  StackCapacity s 2 →
  region-of (readReg (regs s) rsp ∸ two-push-offset) ≡ stack
slot-2-addr-in-stack s cap = capacity-maintained cap 2 (s≤s (s≤s z≤n))

-- | With capacity n ≥ 1, address rsp - slot-size is in stack region
slot-1-addr-in-stack : ∀ (s : State) →
  StackCapacity s 1 →
  region-of (readReg (regs s) rsp ∸ slot-size) ≡ stack
slot-1-addr-in-stack s cap = capacity-maintained cap 1 (s≤s z≤n)

------------------------------------------------------------------------
-- Converting from rsp bounds to StackCapacity
------------------------------------------------------------------------

-- | General conversion: rsp > n*8 gives StackCapacity s n
rsp-bound-to-capacity : ∀ (n : ℕ) (s : State) →
  region-of (readReg (regs s) rsp) ≡ stack →
  readReg (regs s) rsp > n *ℕ slot-size →
  StackCapacity s n
rsp-bound-to-capacity n s rsp-in-stack rsp-bound = record
  { rsp-in-stack = rsp-in-stack
  ; rsp-sufficient = rsp-bound
  ; capacity-maintained = cap-maintained
  }
  where
    open import Data.Nat.Properties using (*-monoˡ-≤; <⇒≤; ≤-<-trans)
    rsp-val = readReg (regs s) rsp
    k*slot≤rsp : ∀ k → k ≤ n → k *ℕ slot-size ≤ rsp-val
    k*slot≤rsp k k≤n = <⇒≤ (≤-<-trans (*-monoˡ-≤ slot-size k≤n) rsp-bound)
    cap-maintained : ∀ k → k ≤ n → region-of (rsp-val ∸ (k *ℕ slot-size)) ≡ stack
    cap-maintained k k≤n = stack-sub-preserves-region rsp-val (k *ℕ slot-size) rsp-in-stack (k*slot≤rsp k k≤n)

-- Note: rsp-to-capacity-N wrappers have been removed.
-- Use rsp-bound-to-capacity n s rsp-in-stack rsp-bound directly.

-- | Convert StackCapacity back to concrete bound (for compatibility)
capacity-2-to-rsp-bound : ∀ (s : State) →
  StackCapacity s 2 →
  readReg (regs s) rsp > two-push-offset
capacity-2-to-rsp-bound s cap = rsp-sufficient cap

-- | rsp > bound preservation when rsp is unchanged (generic version)
rsp-bound-preserved-unchanged : ∀ (bound : ℕ) (s s' : State) →
  readReg (regs s) rsp > bound →
  readReg (regs s') rsp ≡ readReg (regs s) rsp →
  readReg (regs s') rsp > bound
rsp-bound-preserved-unchanged bound s s' rsp-sufficient rsp-eq = subst (_> bound) (sym rsp-eq) rsp-sufficient

------------------------------------------------------------------------
-- Max-based Capacity Derivation (for compose/case/pair threading)
--
-- These lemmas enable deriving sub-capacity from max-based requirements.
-- This is NOT arbitrary weakening - it's principled arithmetic tied to
-- how ir-stack-requirement computes requirements for composed operations.
--
-- ir-stack-requirement (g ∘ f) = ir-stack-requirement f ⊔ ir-stack-requirement g
-- ir-stack-requirement [ l , r ] = ir-stack-requirement l ⊔ ir-stack-requirement r
-- ir-stack-requirement ⟨ f , g ⟩ = 5 + (ir-stack-requirement f ⊔ ir-stack-requirement g)
------------------------------------------------------------------------

open import Data.Nat using (_⊔_)
open import Data.Nat.Properties using (m≤m⊔n; m≤n⊔m; *-monoˡ-≤; ≤-<-trans; ⊔-comm; m≤m+n)

-- Helper: n ≤ m ⊔ n (via commutativity: n ≤ n ⊔ m = m ⊔ n)
private
  n≤m⊔n : ∀ m n → n ≤ m ⊔ n
  n≤m⊔n m n = subst (n ≤_) (⊔-comm n m) (m≤m⊔n n m)

-- | Derive left sub-capacity from max: m ≤ m ⊔ n
capacity-left-from-max : ∀ (s : State) (m n : ℕ) →
  StackCapacity s (m ⊔ n) → StackCapacity s m
capacity-left-from-max s m n cap = record
  { rsp-in-stack = rsp-in-stack cap
  ; rsp-sufficient = ≤-<-trans (*-monoˡ-≤ slot-size (m≤m⊔n m n)) (rsp-sufficient cap)
  ; capacity-maintained = λ k k≤m →
      capacity-maintained cap k (≤-trans k≤m (m≤m⊔n m n))
  }

-- | Derive right sub-capacity from max: n ≤ m ⊔ n
capacity-right-from-max : ∀ (s : State) (m n : ℕ) →
  StackCapacity s (m ⊔ n) → StackCapacity s n
capacity-right-from-max s m n cap = record
  { rsp-in-stack = rsp-in-stack cap
  ; rsp-sufficient = ≤-<-trans (*-monoˡ-≤ slot-size (n≤m⊔n m n)) (rsp-sufficient cap)
  ; capacity-maintained = λ k k≤n →
      capacity-maintained cap k (≤-trans k≤n (n≤m⊔n m n))
  }

-- | Derive capacity when we have more than needed: m ≤ n
-- Used when ir-stack-requirement returns a value smaller than what we have
capacity-from-larger : ∀ (s : State) (m n : ℕ) →
  StackCapacity s n → m ≤ n → StackCapacity s m
capacity-from-larger s m n cap m≤n = record
  { rsp-in-stack = rsp-in-stack cap
  ; rsp-sufficient = ≤-<-trans (*-monoˡ-≤ slot-size m≤n) (rsp-sufficient cap)
  ; capacity-maintained = λ k k≤m →
      capacity-maintained cap k (≤-trans k≤m m≤n)
  }

-- | Slot distribution over addition: slots (a + b) = slots a + slots b
-- This is multiplication distributivity: (a + b) * 8 = a * 8 + b * 8
-- Used for compose rsp tracking: rsp s3 = rsp s ∸ slots (delta f + delta g)
slots-distribute : ∀ a b → slots (a +ℕ b) ≡ slots a +ℕ slots b
slots-distribute zero b = refl
slots-distribute (suc a) b =
  trans (cong (slot-size +ℕ_) (slots-distribute a b))
        (sym (+-assoc slot-size (slots a) (slots b)))

-- | Derive capacity after RSP delta: if we have capacity for d+n at rsp, and rsp
-- decreases by d slots, then we have capacity for n at the new rsp.
-- This is critical for compose capacity threading when f has non-zero rsp delta.
capacity-after-delta : ∀ (s s' : State) (d n : ℕ) →
  StackCapacity s (d +ℕ n) →
  readReg (regs s') rsp ≡ readReg (regs s) rsp ∸ slots d →
  StackCapacity s' n
capacity-after-delta s s' d n cap rsp-eq = record
  { rsp-in-stack = rsp'-in-stack
  ; rsp-sufficient = rsp'-sufficient
  ; capacity-maintained = cap'-maintained
  }
  where
    open import Data.Nat.Properties using (m+n∸n≡m; +-monoˡ-<; <-≤-trans; m+n∸m≡n; +-cancelˡ-<)
    rsp-s = readReg (regs s) rsp
    rsp-s' = readReg (regs s') rsp

    -- rsp' in stack: from capacity-maintained at k=d
    d≤d+n : d ≤ d +ℕ n
    d≤d+n = m≤m+n d n
    rsp'-in-stack : region-of rsp-s' ≡ stack
    rsp'-in-stack = subst (λ r → region-of r ≡ stack) (sym rsp-eq) (capacity-maintained cap d d≤d+n)

    -- rsp' sufficient: rsp s > slots (d+n), so rsp s - slots d > slots n
    -- Key insight: if m > a + b, then m - a > b
    -- Proof: m > a + b means a + b < m, so b < m - a (by +-cancelˡ-< after rearranging)
    rsp-suff : rsp-s > slots (d +ℕ n)
    rsp-suff = rsp-sufficient cap
    slot-eq : slots (d +ℕ n) ≡ slots d +ℕ slots n
    slot-eq = slots-distribute d n
    rsp-suff' : rsp-s > slots d +ℕ slots n
    rsp-suff' = subst (rsp-s >_) slot-eq rsp-suff
    -- slots d + slots n < rsp-s, so slots n < rsp-s - slots d
    rsp'-sufficient : rsp-s' > slots n
    rsp'-sufficient = subst (_> slots n) (sym rsp-eq) helper
      where
        open import Data.Nat.Properties using (m+[n∸m]≡n)
        -- We have: slots d + slots n < rsp-s
        -- Want: slots n < rsp-s - slots d
        -- Use: if a + b < m, then b < m - a (when a ≤ m)
        sum<rsp : slots d +ℕ slots n < rsp-s
        sum<rsp = rsp-suff'
        -- slots d ≤ rsp-s (follows from slots d + slots n < rsp-s)
        -- slots d ≤ slots d + slots n < rsp-s, so slots d < rsp-s, so slots d ≤ rsp-s
        d-slots≤rsp : slots d ≤ rsp-s
        d-slots≤rsp = <⇒≤ (≤-<-trans (m≤m+n (slots d) (slots n)) sum<rsp)
        -- rsp-s = slots d + (rsp-s - slots d) by m+[n∸m]≡n
        rsp-split : rsp-s ≡ slots d +ℕ (rsp-s ∸ slots d)
        rsp-split = sym (m+[n∸m]≡n d-slots≤rsp)
        -- slots d + slots n < slots d + (rsp-s - slots d)
        -- Therefore slots n < rsp-s - slots d (i.e., rsp-s - slots d > slots n)
        sum<rsp' : slots d +ℕ slots n < slots d +ℕ (rsp-s ∸ slots d)
        sum<rsp' = subst (λ x → slots d +ℕ slots n < x) rsp-split sum<rsp
        helper : slots n < rsp-s ∸ slots d
        helper = +-cancelˡ-< (slots d) (slots n) (rsp-s ∸ slots d) sum<rsp'

    -- capacity maintained: for k ≤ n, region-of (rsp' ∸ slots k) = stack
    -- rsp' ∸ slots k = (rsp s ∸ slots d) ∸ slots k = rsp s ∸ (slots d + slots k) = rsp s ∸ slots (d + k)
    cap'-maintained : ∀ k → k ≤ n → region-of (rsp-s' ∸ slots k) ≡ stack
    cap'-maintained k k≤n = step4
      where
        -- Step 1: capacity-maintained gives us region proof for rsp-s ∸ slots (d+k)
        step1 : region-of (rsp-s ∸ slots (d +ℕ k)) ≡ stack
        step1 = capacity-maintained cap (d +ℕ k) (+-monoʳ-≤ d k≤n)
        -- Step 2: slots (d+k) = slots d + slots k (slots-distribute)
        step2 : region-of (rsp-s ∸ (slots d +ℕ slots k)) ≡ stack
        step2 = subst (λ x → region-of (rsp-s ∸ x) ≡ stack) (slots-distribute d k) step1
        -- Step 3: rsp-s ∸ (slots d + slots k) = (rsp-s ∸ slots d) ∸ slots k (sym ∸-+-assoc)
        -- ∸-+-assoc gives: (m ∸ n) ∸ o ≡ m ∸ (n + o), so we use sym
        step3 : region-of ((rsp-s ∸ slots d) ∸ slots k) ≡ stack
        step3 = subst (λ x → region-of x ≡ stack) (sym (∸-+-assoc rsp-s (slots d) (slots k))) step2
        -- Step 4: rsp-s ∸ slots d = rsp-s' (from rsp-eq)
        step4 : region-of (rsp-s' ∸ slots k) ≡ stack
        step4 = subst (λ r → region-of (r ∸ slots k) ≡ stack) (sym rsp-eq) step3

------------------------------------------------------------------------
-- IR-Specific Capacity Derivation Lemmas
--
-- These lemmas prove that internal proof requirements are bounded by
-- ir-stack-requirement. They enable deriving the capacity needed for
-- sub-proofs (Curry.agda, Inl.agda, etc.) from the dispatcher's capacity.
------------------------------------------------------------------------

-- | ir-rsp-delta (curry f) ≤ curry-closure-capacity
-- Proof: ir-rsp-delta (curry f) = curry-closure-consumed-slots
--        curry-closure-capacity = curry-closure-consumed-slots + output-slots
--        So delta ≤ capacity by m≤m+n
curry-rsp-delta≤curry-capacity : ∀ {A B C} (f : IR (A * B) C) →
  ir-rsp-delta (curry f) ≤ curry-closure-capacity
curry-rsp-delta≤curry-capacity f = m≤m+n curry-closure-consumed-slots output-slots

-- | curry-closure-capacity ≤ ir-stack-requirement (curry f)
-- Proof: curry-closure-capacity = 4
--        ir-stack-requirement (curry f) = 2 + (4 + ir-stack-requirement f) = 6 + ir-stack-requirement f ≥ 6 ≥ 4
curry-closure-capacity≤curry-req : ∀ {A B C} (f : IR (A * B) C) →
  curry-closure-capacity ≤ ir-stack-requirement (curry f)
curry-closure-capacity≤curry-req f = ≤-trans (from-yes-≤ (curry-closure-capacity ≤? 6)) (m≤m+n 6 (ir-stack-requirement f))

-- | ir-rsp-delta (curry f) ≤ ir-stack-requirement (curry f)
-- Combines the above two lemmas by transitivity
curry-rsp-delta≤curry-req : ∀ {A B C} (f : IR (A * B) C) →
  ir-rsp-delta (curry f) ≤ ir-stack-requirement (curry f)
curry-rsp-delta≤curry-req f = ≤-trans (curry-rsp-delta≤curry-capacity f) (curry-closure-capacity≤curry-req f)

-- | ir-rsp-delta inl ≤ inl-inr-capacity
-- Proof: ir-rsp-delta inl = injection-consumed-slots
--        inl-inr-capacity = injection-consumed-slots + output-slots
--        So delta ≤ capacity by m≤m+n
inl-rsp-delta≤inl-capacity : ∀ {A B} → ir-rsp-delta (inl {A} {B}) ≤ inl-inr-capacity
inl-rsp-delta≤inl-capacity = m≤m+n injection-consumed-slots output-slots

-- | inl-inr-capacity ≤ ir-stack-requirement inl
-- Proof: both are 4 (definitionally equal)
inl-capacity≤inl-req : ∀ {A B} → inl-inr-capacity ≤ ir-stack-requirement (inl {A} {B})
inl-capacity≤inl-req = ≤-refl

-- | ir-rsp-delta inl ≤ ir-stack-requirement inl
-- Combines the above two lemmas by transitivity
inl-rsp-delta≤inl-req : ∀ {A B} → ir-rsp-delta (inl {A} {B}) ≤ ir-stack-requirement (inl {A} {B})
inl-rsp-delta≤inl-req {A} {B} = ≤-trans (inl-rsp-delta≤inl-capacity {A} {B}) (inl-capacity≤inl-req {A} {B})

-- | ir-rsp-delta inr ≤ inl-inr-capacity
-- Same as inl (both use injection-consumed-slots)
inr-rsp-delta≤inr-capacity : ∀ {A B} → ir-rsp-delta (inr {A} {B}) ≤ inl-inr-capacity
inr-rsp-delta≤inr-capacity = m≤m+n injection-consumed-slots output-slots

-- | inl-inr-capacity ≤ ir-stack-requirement inr
-- Proof: both are 4 (definitionally equal)
inr-capacity≤inr-req : ∀ {A B} → inl-inr-capacity ≤ ir-stack-requirement (inr {A} {B})
inr-capacity≤inr-req = ≤-refl

-- | ir-rsp-delta inr ≤ ir-stack-requirement inr
-- Combines the above two lemmas by transitivity
inr-rsp-delta≤inr-req : ∀ {A B} → ir-rsp-delta (inr {A} {B}) ≤ ir-stack-requirement (inr {A} {B})
inr-rsp-delta≤inr-req {A} {B} = ≤-trans (inr-rsp-delta≤inr-capacity {A} {B}) (inr-capacity≤inr-req {A} {B})

-- | apply-capacity ≤ ir-stack-requirement apply
-- Proof: both are 4 (definitionally equal)
apply-capacity≤apply-req : ∀ {A B} → apply-capacity ≤ ir-stack-requirement (apply {A} {B})
apply-capacity≤apply-req = ≤-refl

------------------------------------------------------------------------
-- Abstract Frame Creation
------------------------------------------------------------------------

-- | Create a StackPointer for a frame at offset k slots below current rsp.
make-frame-at-slot : ∀ {n} (s : State) → StackCapacity s n → (k : ℕ) → k ≤ n → StackPointer
make-frame-at-slot s cap k k≤n = record
  { addr = readReg (regs s) rsp ∸ (k *ℕ slot-size)
  ; in-stack = capacity-maintained cap k k≤n
  }

-- | Parameterized: frame at slot k has addr = rsp - slots k
make-frame-at-slot-addr : (k : ℕ) {n : ℕ} (s : State) (cap : StackCapacity s n) (k≤n : k ≤ n) →
  sp-addr (make-frame-at-slot s cap k k≤n) ≡ readReg (regs s) rsp ∸ slots k
make-frame-at-slot-addr k s cap k≤n = refl

-- | Frames at lower slot indices have higher addresses (stack grows down)
frame-at-lower-slot-≥ : ∀ {n} (s : State) (cap : StackCapacity s n) (k₁ k₂ : ℕ)
  (k₁≤n : k₁ ≤ n) (k₂≤n : k₂ ≤ n) →
  k₁ ≤ k₂ →
  sp-addr (make-frame-at-slot s cap k₁ k₁≤n) ≥ sp-addr (make-frame-at-slot s cap k₂ k₂≤n)
frame-at-lower-slot-≥ s cap k₁ k₂ k₁≤n k₂≤n k₁≤k₂ = ∸-monoʳ-≤ (readReg (regs s) rsp) (*-monoˡ-≤ slot-size k₁≤k₂)
  where
    open import Data.Nat.Properties using (∸-monoʳ-≤; *-monoˡ-≤)

------------------------------------------------------------------------
-- Apply-specific Abstract Interface (D041-compliant)
------------------------------------------------------------------------

-- | Apply frame at slot 1 (one slot below rsp)
apply-frame-1 : ∀ {n} (s : State) (cap : StackCapacity s (suc n)) → StackPointer
apply-frame-1 s cap = make-frame-at-slot s cap 1 (s≤s z≤n)

apply-frame-slot-0-in-stack : ∀ {n} (s : State) (cap : StackCapacity s (suc n)) →
                              region-of (slot-addr (apply-frame-1 s cap) 0) ≡ stack
apply-frame-slot-0-in-stack s cap = slot-in-stack (apply-frame-1 s cap) 0

-- | Bridge from abstract to concrete for Apply's push address (rsp - slot-size)
abstract-to-rsp-slot-in-stack : ∀ {n} (s : State) (cap : StackCapacity s (suc n)) →
                             region-of (readReg (regs s) rsp ∸ slot-size) ≡ stack
abstract-to-rsp-slot-in-stack s cap =
  subst (λ addr → region-of addr ≡ stack)
        (trans (slot-addr-0-is-base (apply-frame-1 s cap))
               (make-frame-at-slot-addr 1 s cap (s≤s z≤n)))
        (apply-frame-slot-0-in-stack s cap)

------------------------------------------------------------------------
-- Generic slot-in-stack proof (D041: unified interface)
------------------------------------------------------------------------

-- | Generic: (rsp - slots k) is in stack when we have capacity ≥ k
-- This is the core abstraction - all specific slot proofs derive from this
rsp-minus-n-slots-in-stack : ∀ (k : ℕ) {n} (s : State) (cap : StackCapacity s n) →
                              k ≤ n →
                              region-of (readReg (regs s) rsp ∸ slots k) ≡ stack
rsp-minus-n-slots-in-stack k s cap k≤n = capacity-maintained cap k k≤n

------------------------------------------------------------------------
-- ThunkExec-specific Abstract Interface (D041-compliant)
------------------------------------------------------------------------

-- | Parameterized thunk frame at slot k
-- Alias for make-frame-at-slot with clearer naming for thunk context
thunk-frame : (k : ℕ) {n : ℕ} (s : State) (cap : StackCapacity s n) (k≤n : k ≤ n) → StackPointer
thunk-frame k s cap k≤n = make-frame-at-slot s cap k k≤n

-- | Parameterized bridge from abstract to concrete for (rsp - k*slot-size)
abstract-to-rsp-slots-in-stack : (k : ℕ) {n : ℕ} (s : State) (cap : StackCapacity s n) (k≤n : k ≤ n) →
                                 region-of (readReg (regs s) rsp ∸ slots k) ≡ stack
abstract-to-rsp-slots-in-stack k s cap k≤n = rsp-minus-n-slots-in-stack k s cap k≤n

-- | Thunk rbp frame (at thunk-rbp-slot) >= new rsp frame (at thunk-setup-consumed-slots)
thunk-rbp-frame-≥-new-rsp : ∀ (s : State) (cap : StackCapacity s thunk-setup-consumed-slots) →
  sp-addr (make-frame-at-slot s cap thunk-rbp-slot thunk-rbp-slot≤thunk-setup) ≥
  sp-addr (make-frame-at-slot s cap thunk-setup-consumed-slots ≤-refl)
thunk-rbp-frame-≥-new-rsp s cap =
  frame-at-lower-slot-≥ s cap thunk-rbp-slot thunk-setup-consumed-slots
                        thunk-rbp-slot≤thunk-setup ≤-refl thunk-rbp-slot≤thunk-setup

------------------------------------------------------------------------
-- Pair-specific Abstract Interface
------------------------------------------------------------------------

-- | Pair frame at slot 5 (rsp - 40)
pair-frame-0 : (s : State) (cap : StackCapacity s pair-setup-consumed-slots) → StackPointer
pair-frame-0 s cap = make-frame-at-slot s cap pair-setup-consumed-slots pair-setup-consumed-slots≤pair-setup-consumed-slots
  where
    pair-setup-consumed-slots≤pair-setup-consumed-slots : pair-setup-consumed-slots ≤ pair-setup-consumed-slots
    pair-setup-consumed-slots≤pair-setup-consumed-slots = ≤-refl

pair-frame-slot-0-in-stack : (s : State) (cap : StackCapacity s pair-setup-consumed-slots) →
                             region-of (slot-addr (pair-frame-0 s cap) 0) ≡ stack
pair-frame-slot-0-in-stack s cap = slot-in-stack (pair-frame-0 s cap) 0

pair-frame-slot-1-in-stack : (s : State) (cap : StackCapacity s pair-setup-consumed-slots) →
                             region-of (slot-addr (pair-frame-0 s cap) 1) ≡ stack
pair-frame-slot-1-in-stack s cap = slot-in-stack (pair-frame-0 s cap) 1

-- | Pair frame 0 address equals rsp - 40
pair-frame-0-addr-eq : (s : State) (cap : StackCapacity s pair-setup-consumed-slots) →
                       sp-addr (pair-frame-0 s cap) ≡ readReg (regs s) rsp ∸ five-slot-offset
pair-frame-0-addr-eq s cap = refl

-- | Pair frame slot 1 address equals (rsp - five-slot-offset) + slot-size
pair-frame-slot-1-addr-eq : (s : State) (cap : StackCapacity s pair-setup-consumed-slots) →
                            slot-addr (pair-frame-0 s cap) 1 ≡ (readReg (regs s) rsp ∸ five-slot-offset) +ℕ slot-size
pair-frame-slot-1-addr-eq s cap =
  trans (slot-addr-1-is-base+8 (pair-frame-0 s cap))
        (cong (_+ℕ slot-size) (pair-frame-0-addr-eq s cap))

-- | Pair rbp frame (at pair-rbp-slot) ≥ r15 frame (at pair-setup-consumed-slots)
pair-rbp-frame-≥-r15-frame : ∀ (s : State) (cap : StackCapacity s pair-setup-consumed-slots) →
  sp-addr (make-frame-at-slot s cap pair-rbp-slot pair-rbp-slot≤pair-setup) ≥
  sp-addr (make-frame-at-slot s cap pair-setup-consumed-slots ≤-refl)
pair-rbp-frame-≥-r15-frame s cap =
  frame-at-lower-slot-≥ s cap pair-rbp-slot pair-setup-consumed-slots
                        pair-rbp-slot≤pair-setup ≤-refl pair-rbp-slot≤pair-setup

-- | rsp - 40 is in stack region when we have pair-setup capacity
pair-r15-in-stack : ∀ (s : State) →
  StackCapacity s pair-setup-consumed-slots →
  region-of (readReg (regs s) rsp ∸ five-slot-offset) ≡ stack
pair-r15-in-stack s cap = capacity-maintained cap pair-setup-consumed-slots ≤-refl

-- | (rsp - five-slot-offset) + slot-size is in stack region when we have pair-setup capacity
pair-second-slot-in-stack : ∀ (s : State) →
  StackCapacity s pair-setup-consumed-slots →
  region-of ((readReg (regs s) rsp ∸ five-slot-offset) +ℕ slot-size) ≡ stack
pair-second-slot-in-stack s cap =
  subst (λ a → region-of a ≡ stack)
        (sym (alloc-5-slots-second-addr-eq rsp-val (cap-to-pair-setup-rsp-bound cap)))
        (capacity-maintained cap 4 slot-4≤pair-setup)
  where
    open import Data.Nat.Properties using (m∸n+n≡m; ∸-+-assoc; ∸-monoˡ-≤; <⇒≤)
    rsp-val = readReg (regs s) rsp
    slot-4≤pair-setup : 4 ≤ pair-setup-consumed-slots
    slot-4≤pair-setup = from-yes-≤ (4 ≤? pair-setup-consumed-slots)
    cap-to-pair-setup-rsp-bound : StackCapacity s pair-setup-consumed-slots → readReg (regs s) rsp ≥ five-slot-offset
    cap-to-pair-setup-rsp-bound cap = <⇒≤ (rsp-sufficient cap)
    alloc-5-slots-second-addr-eq : ∀ (rsp-val : ℕ) → rsp-val ≥ five-slot-offset → (rsp-val ∸ five-slot-offset) +ℕ slot-size ≡ rsp-val ∸ four-slot-offset
    alloc-5-slots-second-addr-eq rsp-val rsp≥40 = trans (cong (_+ℕ slot-size) step1) (m∸n+n≡m word-fits-after-4-slots)
      where
        step1 : rsp-val ∸ five-slot-offset ≡ (rsp-val ∸ four-slot-offset) ∸ slot-size
        step1 = sym (∸-+-assoc rsp-val four-slot-offset slot-size)
        word-fits-after-4-slots : slot-size ≤ rsp-val ∸ four-slot-offset
        word-fits-after-4-slots = ∸-monoˡ-≤ four-slot-offset rsp≥40

-- | Get StackCapacity for Pair setup from runtime rsp bound
pair-stack-capacity : ∀ (s : State) →
  region-of (readReg (regs s) rsp) ≡ stack →
  readReg (regs s) rsp > five-slot-offset →
  StackCapacity s pair-setup-consumed-slots
pair-stack-capacity s rsp-in-stack rsp-bound = rsp-bound-to-capacity pair-setup-consumed-slots s rsp-in-stack rsp-bound

-- | Create StackInvariant for state after Pair setup
pair-setup-stack-inv : ∀ (s s-setup : State) →
  StackCapacity s pair-setup-consumed-slots →
  readReg (regs s-setup) r15 ≡ readReg (regs s) rsp ∸ five-slot-offset →
  readReg (regs s-setup) rsp ≡ readReg (regs s) rsp ∸ five-slot-offset →
  StackInvariant s-setup
pair-setup-stack-inv s s-setup cap r15-eq rsp-eq =
  r15-in-stack pair-frame 0 r15-is-slot0 pair-frame-bound
  where
    base-in-stack : region-of (readReg (regs s) rsp ∸ five-slot-offset) ≡ stack
    base-in-stack = pair-r15-in-stack s cap
    pair-frame : StackPointer
    pair-frame = record
      { addr = readReg (regs s) rsp ∸ five-slot-offset
      ; in-stack = base-in-stack
      }
    r15-is-slot0 : readReg (regs s-setup) r15 ≡ slot-addr pair-frame 0
    r15-is-slot0 = trans r15-eq (sym (slot-addr-0-is-base pair-frame))
    pair-frame-bound : sp-addr pair-frame ≥ readReg (regs s-setup) rsp
    pair-frame-bound = subst (sp-addr pair-frame ≥_) (sym rsp-eq) ≤-refl

------------------------------------------------------------------------
-- Combined Region Lemmas for Stack Operations
------------------------------------------------------------------------

-- | After sub rsp 16, both write addresses (new-rsp and new-rsp+slot) are in stack
alloc-2-slots-addrs-in-stack : ∀ (s : State) →
  StackCapacity s 2 →
  let rsp-val = readReg (regs s) rsp
      new-rsp = rsp-val ∸ two-push-offset
  in (region-of new-rsp ≡ stack) × (region-of (new-rsp +ℕ slot-size) ≡ stack)
alloc-2-slots-addrs-in-stack s cap =
  let rsp-val = readReg (regs s) rsp
      new-rsp = rsp-val ∸ two-push-offset
      write1-in-stack : region-of new-rsp ≡ stack
      write1-in-stack = slot-2-addr-in-stack s cap
      write2-in-stack : region-of (new-rsp +ℕ slot-size) ≡ stack
      write2-in-stack = subst (λ a → region-of a ≡ stack)
                              (sym (alloc-2-slots-second-addr-eq rsp-val (cap-to-inl-inr-rsp-bound cap)))
                              (slot-1-addr-in-stack s (capacity-weaken cap))
  in write1-in-stack , write2-in-stack
  where
    open import Data.Nat.Properties using (<⇒≤; m∸n+n≡m; ∸-+-assoc; ∸-monoˡ-≤; <-trans)
    cap-to-inl-inr-rsp-bound : StackCapacity s 2 → readReg (regs s) rsp ≥ two-push-offset
    cap-to-inl-inr-rsp-bound cap = <⇒≤ (rsp-sufficient cap)
    capacity-weaken : StackCapacity s 2 → StackCapacity s 1
    capacity-weaken cap-input = record
      { rsp-in-stack = rsp-in-stack cap-input
      ; rsp-sufficient = <-trans slot<2slot (rsp-sufficient cap-input)
      ; capacity-maintained = λ k k≤1 →
          capacity-maintained cap-input k (≤-trans k≤1 (s≤s z≤n))
      }
      where
        slot<2slot : slot-size < two-push-offset
        slot<2slot = word<pair
    alloc-2-slots-second-addr-eq : ∀ (rsp-val : ℕ) → rsp-val ≥ two-push-offset → (rsp-val ∸ two-push-offset) +ℕ slot-size ≡ rsp-val ∸ slot-size
    alloc-2-slots-second-addr-eq rsp-val rsp≥16 = trans (cong (_+ℕ slot-size) step1) (m∸n+n≡m word-fits-after-1-slot)
      where
        step1 : rsp-val ∸ two-push-offset ≡ (rsp-val ∸ slot-size) ∸ slot-size
        step1 = sym (∸-+-assoc rsp-val slot-size slot-size)
        word-fits-after-1-slot : slot-size ≤ rsp-val ∸ slot-size
        word-fits-after-1-slot = ∸-monoˡ-≤ slot-size rsp≥16

-- | Stack writes at rsp - k*8 don't affect heap addresses
stack-write-disjoint-from-heap : ∀ (s : State) (n k : ℕ) (heap-addr : Addr) →
  StackCapacity s n →
  k ≤ n →
  region-of heap-addr ≡ heap →
  readReg (regs s) rsp ∸ (k *ℕ slot-size) ≢ heap-addr
stack-write-disjoint-from-heap s n k heap-addr cap k≤n heap-proof =
  stack-heap-disjoint (readReg (regs s) rsp ∸ (k *ℕ slot-size)) heap-addr
                      (capacity-maintained cap k k≤n) heap-proof

------------------------------------------------------------------------
-- Combined State Invariant (R15Status + StackCapacity)
------------------------------------------------------------------------

-- | Combined invariant for x86 execution state
record AbstractStackInvariant (s : State) : Set where
  field
    r15-status : R15Status s
    capacity   : StackCapacity s 2

open AbstractStackInvariant public

-- | Create AbstractStackInvariant from StackInvariant and rsp bound
from-old-invariants : ∀ (s : State) →
  StackInvariant s →
  region-of (readReg (regs s) rsp) ≡ stack →
  readReg (regs s) rsp > two-push-offset →
  AbstractStackInvariant s
from-old-invariants s stack-inv rsp-in-stack rsp-sufficient = record
  { r15-status = stack-inv
  ; capacity = rsp-bound-to-capacity 2 s rsp-in-stack rsp-sufficient
  }

------------------------------------------------------------------------
-- Address disjointness proofs using regions
------------------------------------------------------------------------

-- | Prove that stack write at (rsp - 16) doesn't affect r15
stack-write-slot-2-preserves-r15 : ∀ (s : State) →
  AbstractStackInvariant s →
  readReg (regs s) rsp ∸ two-push-offset ≢ readReg (regs s) r15
stack-write-slot-2-preserves-r15 s inv = helper (r15-status inv)
  where
    open import Data.Nat.Properties using (<⇒≢; <-≤-trans)
    stack-addr = readReg (regs s) rsp ∸ two-push-offset
    stack-addr-in-stack = slot-2-addr-in-stack s (capacity inv)
    addr<rsp : stack-addr < readReg (regs s) rsp
    addr<rsp = m∸n<m-when-m>n (readReg (regs s) rsp) two-push-offset (s≤s z≤n) (rsp-sufficient (capacity inv))
    helper : R15Status s → stack-addr ≢ readReg (regs s) r15
    helper (r15-unused r15≡0) = stack-write-preserves-unused-r15 s stack-addr stack-addr-in-stack r15≡0
    helper (r15-in-heap r15-heap) = stack-write-preserves-heap-r15 s stack-addr stack-addr-in-stack r15-heap
    helper (r15-in-code r15-code) = stack-write-preserves-code-r15 s stack-addr stack-addr-in-stack r15-code
    helper (r15-in-stack r15-frame r15-slot r15-eq frame-bound) =
      let write-addr = readReg (regs s) rsp ∸ two-push-offset
          addr<frame : write-addr < sp-addr r15-frame
          addr<frame = <-≤-trans addr<rsp frame-bound
          write-frame : StackPointer
          write-frame = record { addr = write-addr ; in-stack = stack-addr-in-stack }
          frames-neq : sp-addr write-frame ≢ sp-addr r15-frame
          frames-neq = <⇒≢ addr<frame
      in stack-write-preserves-instack-r15 s stack-addr
           write-frame 0 (sym (slot-addr-0-is-base write-frame))
           r15-frame r15-slot r15-eq frames-neq

-- | Similarly for (rsp - slot-size)
stack-write-slot-1-preserves-r15 : ∀ (s : State) →
  AbstractStackInvariant s →
  readReg (regs s) rsp ∸ slot-size ≢ readReg (regs s) r15
stack-write-slot-1-preserves-r15 s inv = helper (r15-status inv)
  where
    open import Data.Nat.Properties using (<-trans; <⇒≢; <-≤-trans)
    stack-addr = readReg (regs s) rsp ∸ slot-size
    stack-addr-in-stack = capacity-maintained (capacity inv) 1 (s≤s z≤n)
    rsp>slot : readReg (regs s) rsp > slot-size
    rsp>slot = <-trans word<pair (rsp-sufficient (capacity inv))
    addr<rsp : stack-addr < readReg (regs s) rsp
    addr<rsp = m∸n<m-when-m>n (readReg (regs s) rsp) slot-size (s≤s z≤n) rsp>slot
    helper : R15Status s → stack-addr ≢ readReg (regs s) r15
    helper (r15-unused r15≡0) = stack-write-preserves-unused-r15 s stack-addr stack-addr-in-stack r15≡0
    helper (r15-in-heap r15-heap) = stack-write-preserves-heap-r15 s stack-addr stack-addr-in-stack r15-heap
    helper (r15-in-code r15-code) = stack-write-preserves-code-r15 s stack-addr stack-addr-in-stack r15-code
    helper (r15-in-stack r15-frame r15-slot r15-eq frame-bound) =
      let write-addr = readReg (regs s) rsp ∸ slot-size
          addr<frame : write-addr < sp-addr r15-frame
          addr<frame = <-≤-trans addr<rsp frame-bound
          write-frame : StackPointer
          write-frame = record { addr = write-addr ; in-stack = stack-addr-in-stack }
          frames-neq : sp-addr write-frame ≢ sp-addr r15-frame
          frames-neq = <⇒≢ addr<frame
      in stack-write-preserves-instack-r15 s stack-addr
           write-frame 0 (sym (slot-addr-0-is-base write-frame))
           r15-frame r15-slot r15-eq frames-neq

-- | Proof that stack writes don't affect heap-allocated data
stack-write-preserves-heap-data : ∀ (s : State) (heap-addr : Addr) →
  AbstractStackInvariant s →
  region-of heap-addr ≡ heap →
  readReg (regs s) rsp ∸ two-push-offset ≢ heap-addr
stack-write-preserves-heap-data s heap-addr inv heap-proof =
  stack-heap-disjoint (readReg (regs s) rsp ∸ two-push-offset) heap-addr
                      (slot-2-addr-in-stack s (capacity inv))
                      heap-proof

------------------------------------------------------------------------
-- Address disjointness from StackInvariant (legacy compatibility)
------------------------------------------------------------------------

-- | Prove (rsp - two-push-offset) and (rsp - slot-size) are different from r15
addr-diff-from-invariant : ∀ (s : State) →
  StackInvariant s →
  region-of (readReg (regs s) rsp) ≡ stack →
  readReg (regs s) rsp > two-push-offset →
  let new-rsp = readReg (regs s) rsp ∸ two-push-offset
      orig-r15 = readReg (regs s) r15
  in (new-rsp ≢ orig-r15) × ((new-rsp +ℕ slot-size) ≢ orig-r15)
addr-diff-from-invariant s stack-inv rsp-in-stack rsp-suff = diff1 , diff2
  where
    open import Data.Nat.Properties using (<-trans; <⇒≢; <-≤-trans; ∸-monoˡ-≤)
    open import Data.Product using (proj₁; proj₂)
    rsp-val = readReg (regs s) rsp
    cap = rsp-bound-to-capacity 2 s rsp-in-stack rsp-suff
    addrs-in-stack = alloc-2-slots-addrs-in-stack s cap
    write1-in-stack = proj₁ addrs-in-stack
    write2-in-stack = proj₂ addrs-in-stack
    stack-addr1 = rsp-val ∸ two-push-offset
    stack-addr2 = (rsp-val ∸ two-push-offset) +ℕ slot-size
    addr1<rsp : stack-addr1 < rsp-val
    addr1<rsp = m∸n<m-when-m>n rsp-val two-push-offset (s≤s z≤n) rsp-suff
    rsp>slot : rsp-val > slot-size
    rsp>slot = rsp>slot-from-2slot rsp-suff
    addr2<rsp : stack-addr2 < rsp-val
    addr2<rsp = subst (_< rsp-val) (sym addr2-eq) (m∸n<m-when-m>n rsp-val slot-size (s≤s z≤n) rsp>slot)
      where
        open import Data.Nat.Properties using (m∸n+n≡m; ∸-+-assoc)
        rsp≥16 : rsp-val ≥ two-push-offset
        rsp≥16 = <⇒≤ rsp-suff
        addr2-eq : stack-addr2 ≡ rsp-val ∸ slot-size
        addr2-eq = trans (cong (_+ℕ slot-size) (sym (∸-+-assoc rsp-val slot-size slot-size)))
                         (m∸n+n≡m (∸-monoˡ-≤ slot-size rsp≥16))
    diff-helper : ∀ stack-addr → region-of stack-addr ≡ stack → stack-addr < rsp-val →
                  R15Status s → stack-addr ≢ readReg (regs s) r15
    diff-helper addr addr-in-stack addr<rsp (r15-unused r15≡0) =
      stack-write-preserves-unused-r15 s addr addr-in-stack r15≡0
    diff-helper addr addr-in-stack addr<rsp (r15-in-heap r15-heap) =
      stack-write-preserves-heap-r15 s addr addr-in-stack r15-heap
    diff-helper addr addr-in-stack addr<rsp (r15-in-code r15-code) =
      stack-write-preserves-code-r15 s addr addr-in-stack r15-code
    diff-helper addr addr-in-stack addr<rsp (r15-in-stack r15-frame r15-slot r15-eq frame-bound) =
      let addr<frame : addr < sp-addr r15-frame
          addr<frame = <-≤-trans addr<rsp frame-bound
          write-frame : StackPointer
          write-frame = record { addr = addr ; in-stack = addr-in-stack }
          frames-neq : sp-addr write-frame ≢ sp-addr r15-frame
          frames-neq = <⇒≢ addr<frame
      in stack-write-preserves-instack-r15 s addr
           write-frame 0 (sym (slot-addr-0-is-base write-frame))
           r15-frame r15-slot r15-eq frames-neq
    diff1 = diff-helper stack-addr1 write1-in-stack addr1<rsp stack-inv
    diff2 = diff-helper stack-addr2 write2-in-stack addr2<rsp stack-inv

------------------------------------------------------------------------
-- RbpInvariant address disjointness proofs
------------------------------------------------------------------------

-- | Prove (rsp - two-push-offset) and (rsp - slot-size) are different from rbp
rbp-addr-diff-from-invariant : ∀ (s : State) →
  RbpInvariant s →
  readReg (regs s) rsp > two-push-offset →
  let new-rsp = readReg (regs s) rsp ∸ two-push-offset
      orig-rbp = readReg (regs s) rbp
  in (new-rsp ≢ orig-rbp) × ((new-rsp +ℕ slot-size) ≢ orig-rbp)
rbp-addr-diff-from-invariant s rbp-inv rsp-sufficient =
  rbp-diff-proof , rbp-diff-proof-2
  where
    open import Data.Nat.Properties using (<⇒≢; <-≤-trans; m∸n+n≡m; ∸-+-assoc; ∸-monoˡ-≤; n≤1+n)
    rsp-val = readReg (regs s) rsp
    new-rsp = rsp-val ∸ two-push-offset
    orig-rbp = readReg (regs s) rbp
    new-rsp<rsp : new-rsp < rsp-val
    new-rsp<rsp = m∸n<m-when-m>n rsp-val two-push-offset (s≤s z≤n) rsp-sufficient
    new-rsp<rbp : new-rsp < orig-rbp
    new-rsp<rbp = subst (new-rsp <_) (sym (rbp-is-base rbp-inv))
                        (<-≤-trans new-rsp<rsp (frame-bound rbp-inv))
    rbp-diff-proof : new-rsp ≢ orig-rbp
    rbp-diff-proof = <⇒≢ new-rsp<rbp
    rsp>slot : rsp-val > slot-size
    rsp>slot = rsp>slot-from-2slot rsp-sufficient
    rsp-slot<rsp : rsp-val ∸ slot-size < rsp-val
    rsp-slot<rsp = m∸n<m-when-m>n rsp-val slot-size (s≤s z≤n) rsp>slot
    rsp-slot<rbp : rsp-val ∸ slot-size < orig-rbp
    rsp-slot<rbp = subst (rsp-val ∸ slot-size <_) (sym (rbp-is-base rbp-inv))
                      (<-≤-trans rsp-slot<rsp (frame-bound rbp-inv))
    second-slot-eq : new-rsp +ℕ slot-size ≡ rsp-val ∸ slot-size
    second-slot-eq = trans (cong (_+ℕ slot-size) step1) (m∸n+n≡m word-fits)
      where
        step1 : rsp-val ∸ two-push-offset ≡ (rsp-val ∸ slot-size) ∸ slot-size
        step1 = sym (∸-+-assoc rsp-val slot-size slot-size)
        two-slots-fit : two-push-offset ≤ rsp-val
        two-slots-fit = ≤-trans (n≤1+n two-push-offset) rsp-sufficient
        word-fits : slot-size ≤ rsp-val ∸ slot-size
        word-fits = ∸-monoˡ-≤ slot-size two-slots-fit
    rbp-diff-proof-2 : (new-rsp +ℕ slot-size) ≢ orig-rbp
    rbp-diff-proof-2 = subst (_≢ orig-rbp) (sym second-slot-eq) (<⇒≢ rsp-slot<rbp)

-- | Prove (rsp - two-push-offset) and (rsp - slot-size) are different from (rbp + slot-size)
rbp+slot-addr-diff-from-invariant : ∀ (s : State) →
  RbpInvariant s →
  readReg (regs s) rsp > two-push-offset →
  let new-rsp = readReg (regs s) rsp ∸ two-push-offset
      orig-rbp+slot = readReg (regs s) rbp +ℕ slot-size
  in (new-rsp ≢ orig-rbp+slot) × ((new-rsp +ℕ slot-size) ≢ orig-rbp+slot)
rbp+slot-addr-diff-from-invariant s rbp-inv rsp-sufficient =
  rbp+slot-diff-1 , rbp+slot-diff-2
  where
    open import Data.Nat.Properties using (<⇒≢; <-≤-trans; m≤m+n; m∸n+n≡m; ∸-+-assoc; ∸-monoˡ-≤; n≤1+n)
    rsp-val = readReg (regs s) rsp
    new-rsp = rsp-val ∸ two-push-offset
    orig-rbp = readReg (regs s) rbp
    orig-rbp+slot = orig-rbp +ℕ slot-size
    new-rsp<rsp : new-rsp < rsp-val
    new-rsp<rsp = m∸n<m-when-m>n rsp-val two-push-offset (s≤s z≤n) rsp-sufficient
    new-rsp<rbp : new-rsp < orig-rbp
    new-rsp<rbp = subst (new-rsp <_) (sym (rbp-is-base rbp-inv))
                        (<-≤-trans new-rsp<rsp (frame-bound rbp-inv))
    new-rsp<rbp+slot : new-rsp < orig-rbp+slot
    new-rsp<rbp+slot = ≤-trans new-rsp<rbp (m≤m+n orig-rbp slot-size)
    rbp+slot-diff-1 : new-rsp ≢ orig-rbp+slot
    rbp+slot-diff-1 = <⇒≢ new-rsp<rbp+slot
    rsp>slot : rsp-val > slot-size
    rsp>slot = rsp>slot-from-2slot rsp-sufficient
    rsp-slot<rsp : rsp-val ∸ slot-size < rsp-val
    rsp-slot<rsp = m∸n<m-when-m>n rsp-val slot-size (s≤s z≤n) rsp>slot
    rsp-slot<rbp : rsp-val ∸ slot-size < orig-rbp
    rsp-slot<rbp = subst (rsp-val ∸ slot-size <_) (sym (rbp-is-base rbp-inv))
                      (<-≤-trans rsp-slot<rsp (frame-bound rbp-inv))
    rsp-slot<rbp+slot : rsp-val ∸ slot-size < orig-rbp+slot
    rsp-slot<rbp+slot = ≤-trans rsp-slot<rbp (m≤m+n orig-rbp slot-size)
    second-slot-eq : new-rsp +ℕ slot-size ≡ rsp-val ∸ slot-size
    second-slot-eq = trans (cong (_+ℕ slot-size) step1) (m∸n+n≡m word-fits)
      where
        step1 : rsp-val ∸ two-push-offset ≡ (rsp-val ∸ slot-size) ∸ slot-size
        step1 = sym (∸-+-assoc rsp-val slot-size slot-size)
        two-slots-fit : two-push-offset ≤ rsp-val
        two-slots-fit = ≤-trans (n≤1+n two-push-offset) rsp-sufficient
        word-fits : slot-size ≤ rsp-val ∸ slot-size
        word-fits = ∸-monoˡ-≤ slot-size two-slots-fit
    rbp+slot-diff-2 : (new-rsp +ℕ slot-size) ≢ orig-rbp+slot
    rbp+slot-diff-2 = subst (_≢ orig-rbp+slot) (sym second-slot-eq) (<⇒≢ rsp-slot<rbp+slot)

-- | Combined rbp and rbp+slot disjointness for curry
curry-frame-disjoint-from-rbp : ∀ (s : State) →
  RbpInvariant s →
  readReg (regs s) rsp > two-push-offset →
  let new-rsp = readReg (regs s) rsp ∸ two-push-offset
      orig-rbp = readReg (regs s) rbp
  in (new-rsp ≢ orig-rbp) × ((new-rsp +ℕ slot-size) ≢ orig-rbp) ×
     (new-rsp ≢ orig-rbp +ℕ slot-size) × ((new-rsp +ℕ slot-size) ≢ orig-rbp +ℕ slot-size)
curry-frame-disjoint-from-rbp s rbp-inv rsp-suff =
  let (d1 , d2) = rbp-addr-diff-from-invariant s rbp-inv rsp-suff
      (d3 , d4) = rbp+slot-addr-diff-from-invariant s rbp-inv rsp-suff
  in d1 , d2 , d3 , d4

-- | Stack invariant frame bound update after 2-slot allocation
curry-stack-inv-frame-bound-update : ∀ (s s' : State) →
  readReg (regs s') rsp ≡ readReg (regs s) rsp ∸ two-push-offset →
  (frame : StackPointer) →
  sp-addr frame ≥ readReg (regs s) rsp →
  sp-addr frame ≥ readReg (regs s') rsp
curry-stack-inv-frame-bound-update s s' rsp-eq frame old-bound =
  subst (sp-addr frame ≥_) (sym rsp-eq) (≤-trans (m∸n≤m (readReg (regs s) rsp) two-push-offset) old-bound)

-- | RbpInvariant preservation after 2-slot allocation
curry-rbp-inv-update : ∀ (s s' : State) →
  RbpInvariant s →
  readReg (regs s') rbp ≡ readReg (regs s) rbp →
  readReg (regs s') rsp ≡ readReg (regs s) rsp ∸ two-push-offset →
  RbpInvariant s'
curry-rbp-inv-update s s' rbp-inv rbp-eq rsp-eq = record
  { rbp-frame = RbpInvariant.rbp-frame rbp-inv
  ; rbp-is-base = trans rbp-eq (RbpInvariant.rbp-is-base rbp-inv)
  ; frame-bound = curry-stack-inv-frame-bound-update s s' rsp-eq
                    (RbpInvariant.rbp-frame rbp-inv)
                    (RbpInvariant.frame-bound rbp-inv)
  }

-- | Ordering facts for curry: new-rsp < rbp and (new-rsp + slot-size) < rbp
curry-alloc-below-rbp : ∀ (s : State) →
  RbpInvariant s →
  readReg (regs s) rsp > two-push-offset →
  let new-rsp = readReg (regs s) rsp ∸ two-push-offset
      orig-rbp = readReg (regs s) rbp
  in (new-rsp < orig-rbp) × ((new-rsp +ℕ slot-size) < orig-rbp)
curry-alloc-below-rbp s rbp-inv rsp-sufficient = new-rsp<rbp , new-rsp+slot<rbp
  where
    open import Data.Nat.Properties using (<-≤-trans; <⇒≤; +-monoʳ-<; m∸n+n≡m; ≤-<-trans; ∸-+-assoc; ∸-monoˡ-≤)
    rsp-val = readReg (regs s) rsp
    new-rsp = rsp-val ∸ two-push-offset
    orig-rbp = readReg (regs s) rbp
    new-rsp<rsp : new-rsp < rsp-val
    new-rsp<rsp = m∸n<m-when-m>n rsp-val two-push-offset (s≤s z≤n) rsp-sufficient
    new-rsp<rbp : new-rsp < orig-rbp
    new-rsp<rbp = subst (new-rsp <_) (sym (rbp-is-base rbp-inv))
                        (<-≤-trans new-rsp<rsp (frame-bound rbp-inv))
    two-push≤rsp : two-push-offset ≤ rsp-val
    two-push≤rsp = <⇒≤ rsp-sufficient
    rsp>slot : rsp-val > slot-size
    rsp>slot = rsp>slot-from-2slot rsp-sufficient
    rsp-slot<rsp : rsp-val ∸ slot-size < rsp-val
    rsp-slot<rsp = m∸n<m-when-m>n rsp-val slot-size (s≤s z≤n) rsp>slot
    rsp-slot<rbp : rsp-val ∸ slot-size < orig-rbp
    rsp-slot<rbp = subst (rsp-val ∸ slot-size <_) (sym (rbp-is-base rbp-inv))
                      (<-≤-trans rsp-slot<rsp (frame-bound rbp-inv))
    second-slot-eq : new-rsp +ℕ slot-size ≡ rsp-val ∸ slot-size
    second-slot-eq = trans (cong (_+ℕ slot-size) step1) (m∸n+n≡m word-fits)
      where
        open import Data.Nat.Properties using (n≤1+n)
        step1 : rsp-val ∸ two-push-offset ≡ (rsp-val ∸ slot-size) ∸ slot-size
        step1 = sym (∸-+-assoc rsp-val slot-size slot-size)
        two-slots-fit : two-push-offset ≤ rsp-val
        two-slots-fit = ≤-trans (n≤1+n two-push-offset) rsp-sufficient
        word-fits : slot-size ≤ rsp-val ∸ slot-size
        word-fits = ∸-monoˡ-≤ slot-size two-slots-fit
    new-rsp+slot<rbp : (new-rsp +ℕ slot-size) < orig-rbp
    new-rsp+slot<rbp = subst (_< orig-rbp) (sym second-slot-eq) rsp-slot<rbp

-- | Prove curry allocation addresses are non-zero
curry-alloc-nonzero : ∀ (s : State) →
  readReg (regs s) rsp > two-push-offset →
  let new-rsp = readReg (regs s) rsp ∸ two-push-offset
  in (new-rsp ≢ 0) × ((new-rsp +ℕ slot-size) ≢ 0)
curry-alloc-nonzero s rsp-sufficient = diff-new-rsp , diff-new-rsp+slot
  where
    open import Data.Nat.Properties using (<⇒≢; ∸-monoˡ-≤; <-trans; +-monoˡ-<)
    rsp-val = readReg (regs s) rsp
    new-rsp = rsp-val ∸ two-push-offset
    17≤rsp : 17 ≤ rsp-val
    17≤rsp = rsp-sufficient
    1≤new-rsp : 1 ≤ new-rsp
    1≤new-rsp = subst (1 ≤_) refl (∸-monoˡ-≤ two-push-offset 17≤rsp)
    0<new-rsp : 0 < new-rsp
    0<new-rsp = 1≤new-rsp
    0<new-rsp+slot : 0 < (new-rsp +ℕ slot-size)
    0<new-rsp+slot = <-trans (s≤s z≤n) (+-monoˡ-< slot-size 0<new-rsp)
    diff-new-rsp : new-rsp ≢ 0
    diff-new-rsp eq = <⇒≢ 0<new-rsp (sym eq)
    diff-new-rsp+slot : (new-rsp +ℕ slot-size) ≢ 0
    diff-new-rsp+slot eq = <⇒≢ 0<new-rsp+slot (sym eq)

------------------------------------------------------------------------
-- Apply helpers: 1-slot allocation (push r15)
------------------------------------------------------------------------

-- | Slot monotonicity for ≤ (follows from slots being multiplication)
-- Useful for deriving smaller bounds: a ≤ b → slots a ≤ slots b
slots-mono-≤ : ∀ {a b} → a ≤ b → slots a ≤ slots b
slots-mono-≤ {zero} {b} _ = z≤n
slots-mono-≤ {suc a} {suc b} (s≤s a≤b) = +-monoʳ-≤ slot-size (slots-mono-≤ a≤b)

-- | Compose rsp delta: chain two rsp deltas into one
-- Given: rsp₁ = rsp₀ ∸ slots a, rsp₂ = rsp₁ ∸ slots b
-- Proves: rsp₂ = rsp₀ ∸ slots (a + b)
compose-rsp-delta : ∀ (rsp₀ rsp₁ rsp₂ : ℕ) (a b : ℕ) →
  rsp₁ ≡ rsp₀ ∸ slots a →
  rsp₂ ≡ rsp₁ ∸ slots b →
  rsp₂ ≡ rsp₀ ∸ slots (a +ℕ b)
compose-rsp-delta rsp₀ rsp₁ rsp₂ a b eq1 eq2 =
  trans eq2
        (trans (cong (_∸ slots b) eq1)
               (trans (∸-+-assoc rsp₀ (slots a) (slots b))
                      (cong (rsp₀ ∸_) (sym (slots-distribute a b)))))

private
  m∸slot<m : ∀ m → m > slot-size → m ∸ slot-size < m
  m∸slot<m (suc m') (s≤s _) = s≤s (m∸n≤m m' 7)

-- | Prove 1-slot allocation address is below original rsp
apply-alloc-below-rsp : ∀ (s : State) →
  readReg (regs s) rsp > two-push-offset →
  readReg (regs s) rsp ∸ slot-size < readReg (regs s) rsp
apply-alloc-below-rsp s rsp-sufficient = m∸slot<m rsp-val rsp>slot
  where
    rsp-val = readReg (regs s) rsp
    rsp>slot : rsp-val > slot-size
    rsp>slot = rsp>slot-from-2slot rsp-sufficient

-- | Prove 1-slot allocation address is different from addresses >= rsp
apply-alloc-diff-from-above : ∀ (s : State) →
  readReg (regs s) rsp > two-push-offset →
  (addr : ℕ) →
  addr ≥ readReg (regs s) rsp →
  readReg (regs s) rsp ∸ slot-size ≢ addr
apply-alloc-diff-from-above s rsp-sufficient addr addr≥rsp = <⇒≢ new-rsp<addr
  where
    open import Data.Nat.Properties using (<⇒≢; <-≤-trans)
    rsp-val = readReg (regs s) rsp
    new-rsp = rsp-val ∸ slot-size
    new-rsp<rsp = apply-alloc-below-rsp s rsp-sufficient
    new-rsp<addr : new-rsp < addr
    new-rsp<addr = <-≤-trans new-rsp<rsp addr≥rsp

-- | Prove rsp ≢ (rsp - slot-size) when rsp > two-push-offset
apply-rsp-diff-from-alloc : ∀ (s : State) →
  readReg (regs s) rsp > two-push-offset →
  readReg (regs s) rsp ≢ readReg (regs s) rsp ∸ slot-size
apply-rsp-diff-from-alloc s rsp-sufficient eq =
  <⇒≢ (apply-alloc-below-rsp s rsp-sufficient) (sym eq)
  where
    open import Data.Nat.Properties using (<⇒≢)

-- | Prove 2-slot allocation is below original rsp
apply-double-alloc-below-rsp : ∀ (s : State) →
  readReg (regs s) rsp > two-push-offset →
  (readReg (regs s) rsp ∸ slot-size) ∸ slot-size < readReg (regs s) rsp
apply-double-alloc-below-rsp s rsp-sufficient = ≤-<-trans rsp∸2slot≤rsp∸slot rsp∸slot<rsp
  where
    open import Data.Nat.Properties using (≤-<-trans)
    rsp-val = readReg (regs s) rsp
    rsp∸slot<rsp = apply-alloc-below-rsp s rsp-sufficient
    rsp∸2slot≤rsp∸slot = m∸n≤m (rsp-val ∸ slot-size) slot-size

-- | Prove 2-slot allocation address is different from addresses >= rsp
apply-double-alloc-diff-from-above : ∀ (s : State) →
  readReg (regs s) rsp > two-push-offset →
  (addr : ℕ) →
  addr ≥ readReg (regs s) rsp →
  (readReg (regs s) rsp ∸ slot-size) ∸ slot-size ≢ addr
apply-double-alloc-diff-from-above s rsp-sufficient addr addr≥rsp =
  <⇒≢ (<-≤-trans (apply-double-alloc-below-rsp s rsp-sufficient) addr≥rsp)
  where
    open import Data.Nat.Properties using (<⇒≢; <-≤-trans)

------------------------------------------------------------------------
-- D041: Thunk-specific Abstract Helpers
------------------------------------------------------------------------

-- | Helper: 2-slot is below 1-slot when rsp > two-push-offset
thunk-2slot-below-1slot : ∀ (s : State) →
  readReg (regs s) rsp > two-push-offset →
  let rsp-val = readReg (regs s) rsp
  in (rsp-val ∸ two-push-offset) < (rsp-val ∸ slot-size)
thunk-2slot-below-1slot s rsp-sufficient = ∸-monoʳ-< word<pair (<⇒≤ rsp-sufficient)

-- | Helper: 2-slot is below orig-rsp when rsp > two-push-offset
thunk-2slot-below-orig : ∀ (s : State) →
  readReg (regs s) rsp > two-push-offset →
  let rsp-val = readReg (regs s) rsp
  in (rsp-val ∸ two-push-offset) < rsp-val
thunk-2slot-below-orig s rsp-sufficient = <-trans rsp∸2slot<rsp∸slot rsp∸slot<rsp
  where
    open import Data.Nat.Properties using (<-trans)
    rsp∸2slot<rsp∸slot = thunk-2slot-below-1slot s rsp-sufficient
    rsp∸slot<rsp = apply-alloc-below-rsp s rsp-sufficient

-- | Helper: 2-slot is different from orig-rsp when rsp > two-push-offset
thunk-2slot-diff-from-orig : ∀ (s : State) →
  readReg (regs s) rsp > two-push-offset →
  let rsp-val = readReg (regs s) rsp
  in (rsp-val ∸ two-push-offset) ≢ rsp-val
thunk-2slot-diff-from-orig s rsp-sufficient eq =
  <⇒≢ (thunk-2slot-below-orig s rsp-sufficient) eq
  where
    open import Data.Nat.Properties using (<⇒≢)

-- | Helper: 4-slot is below orig-rsp when rsp > two-push-offset
thunk-4slot-below-orig : ∀ (s : State) →
  readReg (regs s) rsp > two-push-offset →
  let rsp-val = readReg (regs s) rsp
  in (rsp-val ∸ four-slot-offset) < rsp-val
thunk-4slot-below-orig s rsp-sufficient = ≤-<-trans rsp∸4slot≤rsp∸slot rsp∸slot<rsp
  where
    open import Data.Nat.Properties using (≤-<-trans; ∸-monoʳ-≤)
    rsp-val = readReg (regs s) rsp
    rsp∸slot<rsp = apply-alloc-below-rsp s rsp-sufficient
    rsp∸4slot≤rsp∸slot : (rsp-val ∸ four-slot-offset) ≤ (rsp-val ∸ slot-size)
    rsp∸4slot≤rsp∸slot = ∸-monoʳ-≤ rsp-val word≤frame∸word

-- | Helper: 4-slot is different from addresses >= orig-rsp
thunk-4slot-diff-from-above : ∀ (s : State) →
  readReg (regs s) rsp > two-push-offset →
  (addr : ℕ) →
  addr ≥ readReg (regs s) rsp →
  (readReg (regs s) rsp ∸ four-slot-offset) ≢ addr
thunk-4slot-diff-from-above s rsp-sufficient addr addr≥rsp =
  <⇒≢ (<-≤-trans (thunk-4slot-below-orig s rsp-sufficient) addr≥rsp)
  where
    open import Data.Nat.Properties using (<⇒≢; <-≤-trans)

------------------------------------------------------------------------
-- D041: Raw ℕ versions of thunk helpers
------------------------------------------------------------------------

-- | Raw ℕ version: 1-slot below orig when n > two-push-offset
n∸slot<n-raw : ∀ (n : ℕ) → n > two-push-offset → (n ∸ slot-size) < n
n∸slot<n-raw n n>16 = m∸slot<m n (≤-trans word+1≤pair (<⇒≤ n>16))

-- | Raw ℕ version: 2-slot below 1-slot when n > two-push-offset
n∸2slot<n∸slot-raw : ∀ (n : ℕ) → n > two-push-offset → (n ∸ two-push-offset) < (n ∸ slot-size)
n∸2slot<n∸slot-raw n n>16 = ∸-monoʳ-< word<pair (<⇒≤ n>16)

-- | Raw ℕ version: 2-slot below orig when n > two-push-offset
n∸2slot<n-raw : ∀ (n : ℕ) → n > two-push-offset → (n ∸ two-push-offset) < n
n∸2slot<n-raw n n>16 = <-trans (n∸2slot<n∸slot-raw n n>16) (n∸slot<n-raw n n>16)
  where
    open import Data.Nat.Properties using (<-trans)

-- | Raw ℕ version: 4-slot below orig when n > two-push-offset
n∸4slot<n-raw : ∀ (n : ℕ) → n > two-push-offset → (n ∸ four-slot-offset) < n
n∸4slot<n-raw n n>16 = ≤-<-trans n∸4slot≤n∸slot (n∸slot<n-raw n n>16)
  where
    open import Data.Nat.Properties using (≤-<-trans; ∸-monoʳ-≤)
    n∸4slot≤n∸slot : (n ∸ four-slot-offset) ≤ (n ∸ slot-size)
    n∸4slot≤n∸slot = ∸-monoʳ-≤ n word≤frame∸word

-- | Raw ℕ version: 3-slot below orig when n > two-push-offset
n∸3slot<n-raw : ∀ (n : ℕ) → n > two-push-offset → (n ∸ three-slot-offset) < n
n∸3slot<n-raw n n>16 = ≤-<-trans n∸3slot≤n∸slot (n∸slot<n-raw n n>16)
  where
    open import Data.Nat.Properties using (≤-<-trans; ∸-monoʳ-≤)
    n∸3slot≤n∸slot : (n ∸ three-slot-offset) ≤ (n ∸ slot-size)
    n∸3slot≤n∸slot = ∸-monoʳ-≤ n word≤regs

-- | Raw ℕ version: 3-slot below < 1-slot below when n > three-slot-offset
n∸3slot<n∸slot-raw : ∀ (n : ℕ) → n > three-slot-offset → (n ∸ three-slot-offset) < (n ∸ slot-size)
n∸3slot<n∸slot-raw n n>24 = ∸-monoʳ-< word<regs (<⇒≤ n>24)

-- | Identity: (n ∸ four-slot-offset) + slot-size ≡ n ∸ three-slot-offset when n ≥ 32
-- Uses slot1-plus-word≡slot2 from Arithmetic
n∸4slot+slot≡n∸3slot : ∀ (n : ℕ) → four-slot-offset ≤ n → (n ∸ four-slot-offset) +ℕ slot-size ≡ n ∸ three-slot-offset
n∸4slot+slot≡n∸3slot = slot1-plus-word≡slot2

-- | Raw ℕ version: 4-slot below orig + slot-size < orig when n > two-push-offset
n∸4slot+slot<n-raw : ∀ (n : ℕ) → n > two-push-offset → (n ∸ four-slot-offset) +ℕ slot-size < n
n∸4slot+slot<n-raw n n>16 = <-≤-trans step-slot<step-2slot step-2slot≤n
  where
    open import Data.Nat.Properties using (<-≤-trans; +-monoˡ-≤; +-monoʳ-<; ∸-monoʳ-≤; m∸n+n≡m)
    step-slot<step-2slot : (n ∸ four-slot-offset) +ℕ slot-size < (n ∸ four-slot-offset) +ℕ two-push-offset
    step-slot<step-2slot = +-monoʳ-< (n ∸ four-slot-offset) word<pair
    n∸4slot≤n∸2slot : (n ∸ four-slot-offset) ≤ (n ∸ two-push-offset)
    n∸4slot≤n∸2slot = ∸-monoʳ-≤ n pair≤frame∸word
    step-2slot≤n∸2slot+2slot : (n ∸ four-slot-offset) +ℕ two-push-offset ≤ (n ∸ two-push-offset) +ℕ two-push-offset
    step-2slot≤n∸2slot+2slot = +-monoˡ-≤ two-push-offset n∸4slot≤n∸2slot
    2slot≤n : two-push-offset ≤ n
    2slot≤n = <⇒≤ n>16
    n∸2slot+2slot≡n : (n ∸ two-push-offset) +ℕ two-push-offset ≡ n
    n∸2slot+2slot≡n = m∸n+n≡m 2slot≤n
    step-2slot≤n : (n ∸ four-slot-offset) +ℕ two-push-offset ≤ n
    step-2slot≤n = subst ((n ∸ four-slot-offset) +ℕ two-push-offset ≤_) n∸2slot+2slot≡n step-2slot≤n∸2slot+2slot

-- | Subtraction with positive n gives different result
∸-gives-different : ∀ m n → m > 0 → n > 0 → m ∸ n ≢ m
∸-gives-different zero _ () _
∸-gives-different (suc m) zero _ ()
∸-gives-different (suc m) (suc n) _ _ eq with suc n ≤? suc m
... | yes n≤m = <⇒≢ m∸n<m eq
  where
    z<s : 0 < suc n
    z<s = s≤s z≤n
    m∸n<m : suc m ∸ suc n < suc m
    m∸n<m = ∸-monoʳ-< z<s n≤m
... | no ¬n≤m = 0≢suc m∸n≡0-then-eq
  where
    -- ≰⇒> gives suc m < suc n, which is s≤s (m < n)
    -- <⇒≤ then gives suc m ≤ suc n, which is s≤s (m ≤ n)
    sucm≤sucn : suc m ≤ suc n
    sucm≤sucn = <⇒≤ (≰⇒> ¬n≤m)
    m≤n : m ≤ n
    m≤n with sucm≤sucn
    ... | s≤s le = le
    m∸n≡0 : m ∸ n ≡ 0
    m∸n≡0 = m≤n⇒m∸n≡0 m≤n
    0≢suc : 0 ≢ suc m
    0≢suc ()
    m∸n≡0-then-eq : 0 ≡ suc m
    m∸n≡0-then-eq = trans (sym m∸n≡0) eq

-- | Subtraction with positive n gives smaller result
∸-gives-smaller : ∀ m n → m > 0 → n > 0 → m ∸ n < m
∸-gives-smaller (suc m′) (suc n′) _ _ = s≤s (m∸n≤m m′ n′)

-- | Subtraction composition (wraps ∸-+-assoc from stdlib)
∸-∸-compose : ∀ m a b → (m ∸ a) ∸ b ≡ m ∸ (a +ℕ b)
∸-∸-compose m a b = ∸-+-assoc m a b

-- | Named composition: two pushes compose to two-push-offset
push-push-eq : ∀ m → (m ∸ push-offset) ∸ push-offset ≡ m ∸ two-push-offset
push-push-eq m = ∸-+-assoc m push-offset push-offset

-- | Named composition: thunk frame from two-push + local allocation
thunk-frame-eq : ∀ m → (m ∸ two-push-offset) ∸ thunk-local-size ≡ m ∸ thunk-frame-size
thunk-frame-eq m = ∸-+-assoc m two-push-offset thunk-local-size

------------------------------------------------------------------------
-- Pair/SeqExec Arithmetic Helpers (D041: migrate from SeqExec)
------------------------------------------------------------------------

-- | Different offsets give different addresses (when m is large enough)
-- If a < b and m ≥ b, then m ∸ b < m ∸ a, so they're different
∸-different-offsets : ∀ m a b → a < b → m ≥ b → m ∸ b ≢ m ∸ a
∸-different-offsets m a b a<b m≥b eq = <⇒≢ (∸-monoʳ-< a<b m≥b) eq

-- Specific instances for SeqExec pair setup
-- m ∸ two-push-offset ≢ m ∸ slot-size when m > two-push-offset
-- Note: slot-size < two-push-offset means 9 ≤ 16, requiring s≤s^9 z≤n
∸two-slot≢∸one-slot : ∀ m → m > two-push-offset → m ∸ two-push-offset ≢ m ∸ push-offset
∸two-slot≢∸one-slot m m>16 = ∸-different-offsets m push-offset two-push-offset word<pair (<⇒≤ m>16)

-- m ∸ three-slot-offset ≢ m ∸ slot-size when m > three-slot-offset
∸three-slot≢∸one-slot : ∀ m → m > three-slot-offset → m ∸ three-slot-offset ≢ m ∸ push-offset
∸three-slot≢∸one-slot m m>24 = ∸-different-offsets m push-offset three-slot-offset word<regs (<⇒≤ m>24)

-- m ∸ three-slot-offset ≢ m ∸ two-push-offset when m > three-slot-offset
∸three-slot≢∸two-slot : ∀ m → m > three-slot-offset → m ∸ three-slot-offset ≢ m ∸ two-push-offset
∸three-slot≢∸two-slot m m>24 = ∸-different-offsets m two-push-offset three-slot-offset pair<regs (<⇒≤ m>24)

------------------------------------------------------------------------
-- SlotFrame Abstraction (D041 Phase B)
------------------------------------------------------------------------
-- Replaces arithmetic-based slot disjointness with frame-identity reasoning.
-- SlotFrame is FULLY PROVABLE from arithmetic - no new postulates.
--
-- Key insight: different slot indices give disjoint addresses when
-- the base address is large enough. This generalizes the existing
-- ∸two-slot≢∸one-slot, ∸three-slot≢∸one-slot lemmas.

-- | Slot monotonicity: k₁ < k₂ → slots k₁ < slots k₂
-- Proven by induction using +-monoʳ-< and slot-size = 8
slots-mono-8 : ∀ k₁ k₂ → k₁ < k₂ → slots k₁ < slots k₂
slots-mono-8 zero (suc k₂) _ = s≤s z≤n  -- 0 < 8 + k₂ * 8
slots-mono-8 (suc k₁) (suc k₂) (s≤s k₁<k₂) = helper
  where
    -- slots (suc k₁) = 8 + k₁ * 8
    -- slots (suc k₂) = 8 + k₂ * 8
    -- Need: 8 + k₁ * 8 < 8 + k₂ * 8
    -- Which follows from k₁ * 8 < k₂ * 8
    helper : slots (suc k₁) < slots (suc k₂)
    helper = +-monoʳ-< slot-size (slots-mono-8 k₁ k₂ k₁<k₂)

-- | Slot disjointness (cleaner version using slots-mono-8)
slots-disjoint' : ∀ m k₁ k₂ →
  k₁ < k₂ →
  m ≥ slots k₂ →
  m ∸ slots k₂ ≢ m ∸ slots k₁
slots-disjoint' m k₁ k₂ k₁<k₂ m≥k₂ =
  ∸-different-offsets m (slots k₁) (slots k₂) (slots-mono-8 k₁ k₂ k₁<k₂) m≥k₂

-- | SlotFrame: a stack frame at a specific slot offset
-- This abstracts over the concrete arithmetic (rsp ∸ slots k).
record SlotFrame (s : State) (k : ℕ) : Set where
  field
    -- The concrete address of this frame
    frame-addr : ℕ
    -- The address equals rsp - slots k
    addr-eq : frame-addr ≡ readReg (regs s) rsp ∸ slots k
    -- The address is in the stack region
    in-stack : region-of frame-addr ≡ stack

open SlotFrame public

-- | Create a SlotFrame from StackCapacity
-- When we have capacity for n slots and k ≤ n, we can create a frame at slot k
mk-slot-frame : ∀ (s : State) (k n : ℕ) →
  StackCapacity s n →
  k ≤ n →
  SlotFrame s k
mk-slot-frame s k n cap k≤n = record
  { frame-addr = readReg (regs s) rsp ∸ slots k
  ; addr-eq = refl
  ; in-stack = capacity-maintained cap k k≤n
  }

-- | Key theorem: frames at different slot indices have disjoint addresses
-- This is the core abstraction - instead of proving arithmetic disjointness
-- each time, we prove it once here and reuse via frame identity.
frame-addrs-disjoint : ∀ {s : State} {k₁ k₂ n : ℕ} →
  (f₁ : SlotFrame s k₁) →
  (f₂ : SlotFrame s k₂) →
  k₁ < k₂ →
  StackCapacity s n →
  k₂ ≤ n →
  frame-addr f₁ ≢ frame-addr f₂
frame-addrs-disjoint {s} {k₁} {k₂} {n} f₁ f₂ k₁<k₂ cap k₂≤n eq =
  slots-disjoint' rsp-val k₁ k₂ k₁<k₂ rsp≥k₂ addr-eq-contra
  where
    rsp-val = readReg (regs s) rsp
    -- We have: slots n < rsp-val and k₂ ≤ n, so slots k₂ ≤ slots n < rsp-val
    slots-k₂≤slots-n : slots k₂ ≤ slots n
    slots-k₂≤slots-n = slots-mono-≤ k₂≤n
    rsp≥k₂ : rsp-val ≥ slots k₂
    rsp≥k₂ = ≤-trans slots-k₂≤slots-n (<⇒≤ (rsp-sufficient cap))
    -- f₁.addr = rsp ∸ slots k₁, f₂.addr = rsp ∸ slots k₂
    -- eq : f₁.addr ≡ f₂.addr
    -- Need: rsp ∸ slots k₂ ≡ rsp ∸ slots k₁ (for slots-disjoint')
    addr-eq-contra : rsp-val ∸ slots k₂ ≡ rsp-val ∸ slots k₁
    addr-eq-contra = trans (sym (addr-eq f₂)) (trans (sym eq) (addr-eq f₁))

------------------------------------------------------------------------
-- Specific Frame Constructors
------------------------------------------------------------------------

-- | Pair r15 frame (at pair-setup-consumed-slots, i.e., rsp - 40)
mk-pair-r15-frame : ∀ (s : State) → StackCapacity s pair-setup-consumed-slots → SlotFrame s pair-setup-consumed-slots
mk-pair-r15-frame s cap = mk-slot-frame s pair-setup-consumed-slots pair-setup-consumed-slots cap ≤-refl

-- | Pair rbp frame (at pair-rbp-slot, i.e., rsp - 24)
mk-pair-rbp-frame : ∀ (s : State) → StackCapacity s pair-setup-consumed-slots → SlotFrame s pair-rbp-slot
mk-pair-rbp-frame s cap = mk-slot-frame s pair-rbp-slot pair-setup-consumed-slots cap pair-rbp-slot≤pair-setup

-- | Apply frame at slot 1 (rsp - 8)
mk-apply-frame : ∀ (s : State) → StackCapacity s output-slots → SlotFrame s 1
mk-apply-frame s cap = mk-slot-frame s 1 output-slots cap (s≤s z≤n)

-- | Thunk rbp frame (at thunk-rbp-slot, i.e., rsp - 16)
mk-thunk-rbp-frame : ∀ (s : State) → StackCapacity s thunk-setup-consumed-slots → SlotFrame s thunk-rbp-slot
mk-thunk-rbp-frame s cap = mk-slot-frame s thunk-rbp-slot thunk-setup-consumed-slots cap thunk-rbp-slot≤thunk-setup

-- | Thunk new-rsp frame (at thunk-setup-consumed-slots, i.e., rsp - 32)
mk-thunk-rsp-frame : ∀ (s : State) → StackCapacity s thunk-setup-consumed-slots → SlotFrame s thunk-setup-consumed-slots
mk-thunk-rsp-frame s cap = mk-slot-frame s thunk-setup-consumed-slots thunk-setup-consumed-slots cap ≤-refl

------------------------------------------------------------------------
-- Heap-Stack Disjointness via Regions
--
-- These lemmas replace the heap-stack-disjoint postulate in Postulates.agda
-- by using the region-based abstraction from MemoryRegions.agda.
------------------------------------------------------------------------

-- | Encoded values are in the heap region (specialized for Once.Semantics.encode)
encode-in-heap-sem : ∀ {A : Type} (x : ⟦ A ⟧) → region-of (encode x) ≡ heap
encode-in-heap-sem {A} x = encode-in-heap {⟦ A ⟧} (encode {A}) x

-- | Encoded value + offset is in heap region
encode-offset-in-heap : ∀ {A : Type} (x : ⟦ A ⟧) (offset : ℕ) →
  region-of (encode x +ℕ offset) ≡ heap
encode-offset-in-heap x offset = heap-offset (encode x) offset (encode-in-heap-sem x)

-- | Heap-stack disjointness via regions (replaces postulate)
-- Usage: heap-stack-disjoint-via-region pair 0 new-rsp stack-proof
heap-stack-disjoint-via-region : ∀ {A : Type} (x : ⟦ A ⟧) (offset stack-addr : ℕ) →
  region-of stack-addr ≡ stack →
  (encode x +ℕ offset) ≢ stack-addr
heap-stack-disjoint-via-region x offset stack-addr stack-proof eq =
  stack-heap-disjoint stack-addr (encode x +ℕ offset)
    stack-proof
    (encode-offset-in-heap x offset)
    (sym eq)

