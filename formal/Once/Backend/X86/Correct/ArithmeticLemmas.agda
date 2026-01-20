------------------------------------------------------------------------
-- Once.Backend.X86.Correct.ArithmeticLemmas
--
-- Consolidated numeric comparison lemmas for X86 backend proofs.
-- Uses decidability-based proofs for fast typechecking.
--
-- NAMING CONVENTION (from arch-proof-instructions.md):
-- - Name invariants, not relationships
-- - No ordering symbols (≤, <, ≥, >) in names - arch-specific direction
-- - Use "fits", "within", "sufficient" for containment
-- - Describe the SEMANTIC meaning, not numeric comparison
------------------------------------------------------------------------

module Once.Backend.X86.Correct.ArithmeticLemmas where

open import Data.Nat using (ℕ; _<_; _≤_; _<?_; _≤?_; _∸_)
open import Once.Backend.X86.Correct.Arithmetic
  using (from-yes-<; from-yes-≤;
         word-size; pair-alloc; saved-regs-size; frame-size)

------------------------------------------------------------------------
-- Frame containment (components fit within frame)
------------------------------------------------------------------------

-- | Word fits strictly within frame
word-fits-frame-strict : word-size < frame-size
word-fits-frame-strict = from-yes-< (word-size <? frame-size)

-- | Pair-alloc fits strictly within frame
pair-fits-frame-strict : pair-alloc < frame-size
pair-fits-frame-strict = from-yes-< (pair-alloc <? frame-size)

-- | Saved-regs fits strictly within frame
regs-fits-frame-strict : saved-regs-size < frame-size
regs-fits-frame-strict = from-yes-< (saved-regs-size <? frame-size)

-- | Word fits within frame
word-fits-frame : word-size ≤ frame-size
word-fits-frame = from-yes-≤ (word-size ≤? frame-size)

-- | Pair-alloc fits within frame
pair-fits-frame : pair-alloc ≤ frame-size
pair-fits-frame = from-yes-≤ (pair-alloc ≤? frame-size)

-- | Saved-regs fits within frame
regs-fits-frame : saved-regs-size ≤ frame-size
regs-fits-frame = from-yes-≤ (saved-regs-size ≤? frame-size)

------------------------------------------------------------------------
-- Slot-1 containment (frame - word = 32)
------------------------------------------------------------------------

-- | Pair-alloc fits within slot-1 offset
pair-fits-slot1 : pair-alloc ≤ (frame-size ∸ word-size)
pair-fits-slot1 = from-yes-≤ (pair-alloc ≤? (frame-size ∸ word-size))

-- | Saved-regs fits within slot-1 offset
regs-fits-slot1 : saved-regs-size ≤ (frame-size ∸ word-size)
regs-fits-slot1 = from-yes-≤ (saved-regs-size ≤? (frame-size ∸ word-size))

------------------------------------------------------------------------
-- Saved-regs containment
------------------------------------------------------------------------

-- | Word fits within saved-regs
word-fits-regs : word-size ≤ saved-regs-size
word-fits-regs = from-yes-≤ (word-size ≤? saved-regs-size)

-- | Pair-alloc fits within saved-regs
pair-fits-regs : pair-alloc ≤ saved-regs-size
pair-fits-regs = from-yes-≤ (pair-alloc ≤? saved-regs-size)

------------------------------------------------------------------------
-- Rsp minimum bounds (for stack operations)
------------------------------------------------------------------------

-- | Minimum rsp for pair frame fits within frame
rsp-min-pair-fits-frame : 33 ≤ frame-size
rsp-min-pair-fits-frame = from-yes-≤ (33 ≤? frame-size)

-- NOTE: single-slot-fits-thunk-bound deleted, use slots-bound-positive from StackInstantiation

-- | Word fits thunk rsp bound
word-fits-thunk-bound : word-size ≤ 17
word-fits-thunk-bound = from-yes-≤ (word-size ≤? 17)

-- | Word fits strictly within thunk rsp bound
word-fits-thunk-bound-strict : word-size < 17
word-fits-thunk-bound-strict = from-yes-< (word-size <? 17)

-- NOTE: Capacity containment lemmas moved to StackInstantiation.agda
-- with symbolic names (output-slots, apply-capacity, etc.)

-- NOTE: thunk-setup-within-apply-code moved to ThunkStructure.agda
-- as thunk-entry-within-curry-overhead (uses symbolic constants)

------------------------------------------------------------------------
-- Word/pair containment
------------------------------------------------------------------------

-- | Word fits strictly within pair-alloc
word-fits-pair-strict : word-size < pair-alloc
word-fits-pair-strict = from-yes-< (word-size <? pair-alloc)

------------------------------------------------------------------------
-- Thunk capacity bounds
------------------------------------------------------------------------

-- | Pair-alloc fits post-rbp-push minimum
pair-fits-post-rbp-push : pair-alloc ≤ 25
pair-fits-post-rbp-push = from-yes-≤ (pair-alloc ≤? 25)

-- | Word fits word+1 bound
word-fits-word-plus-one : word-size ≤ 9
word-fits-word-plus-one = from-yes-≤ (word-size ≤? 9)

-- | Thunk minimum fits actual thunk capacity
thunk-min-fits-actual : 41 ≤ 49
thunk-min-fits-actual = from-yes-≤ (41 ≤? 49)

-- | Four slots fit thunk actual capacity
four-slots-fit-thunk-actual : 32 ≤ 49
four-slots-fit-thunk-actual = from-yes-≤ (32 ≤? 49)

-- | Post-rbp-push minimum fits thunk actual
post-rbp-push-fits-thunk-actual : 25 ≤ 49
post-rbp-push-fits-thunk-actual = from-yes-≤ (25 ≤? 49)

-- | Three slots fit four slots
three-slots-fit-four-slots : 24 ≤ 32
three-slots-fit-four-slots = from-yes-≤ (24 ≤? 32)

-- NOTE: Thunk setup capacity lemmas moved to StackInstantiation.agda
-- See: output-fits-thunk-cap, apply-cap-after-push-fits-thunk-cap, apply-capacity-fits-thunk-cap

------------------------------------------------------------------------
-- Positive bounds (non-zero)
------------------------------------------------------------------------

-- | Word-size is positive
word-positive : 0 < word-size
word-positive = from-yes-< (0 <? word-size)

-- | Pair-alloc is positive
pair-positive : 0 < pair-alloc
pair-positive = from-yes-< (0 <? pair-alloc)

-- | Saved-regs is positive
regs-positive : 0 < saved-regs-size
regs-positive = from-yes-< (0 <? saved-regs-size)

-- NOTE: Apply capacity bounds moved to StackInstantiation.agda
-- See: single-slot-fits-apply-cap

------------------------------------------------------------------------
-- Inr capacity bounds
------------------------------------------------------------------------

-- | Inr-setup fits within full injection capacity
inr-setup-within-injection : 33 ≤ 57
inr-setup-within-injection = from-yes-≤ (33 ≤? 57)
