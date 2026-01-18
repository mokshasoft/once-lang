------------------------------------------------------------------------
-- Once.Backend.X86.Correct.ArithmeticLemmas
--
-- Consolidated numeric comparison lemmas for X86 backend proofs.
-- Uses decidability-based proofs for fast typechecking.
--
-- Naming convention: semantic names describing what the invariant means,
-- not the numeric relationship (e.g., `word<frame` not `8<40`).
--
-- Lemmas grouped by relationship type for duplicate detection.
------------------------------------------------------------------------

module Once.Backend.X86.Correct.ArithmeticLemmas where

open import Data.Nat using (ℕ; _<_; _≤_; _<?_; _≤?_; _∸_)
open import Once.Backend.X86.Correct.Arithmetic
  using (from-yes-<; from-yes-≤;
         word-size; pair-alloc; saved-regs-size; frame-size)

------------------------------------------------------------------------
-- Frame-size bounds (_ < frame-size, _ ≤ frame-size)
--
-- frame-size = 40 = saved-regs-size + pair-alloc = 24 + 16
------------------------------------------------------------------------

-- | word-size < frame-size (8 < 40)
word<frame : word-size < frame-size
word<frame = from-yes-< (word-size <? frame-size)

-- | pair-alloc < frame-size (16 < 40)
pair<frame : pair-alloc < frame-size
pair<frame = from-yes-< (pair-alloc <? frame-size)

-- | saved-regs-size < frame-size (24 < 40)
regs<frame : saved-regs-size < frame-size
regs<frame = from-yes-< (saved-regs-size <? frame-size)

-- | word-size ≤ frame-size (8 ≤ 40)
word≤frame : word-size ≤ frame-size
word≤frame = from-yes-≤ (word-size ≤? frame-size)

-- | pair-alloc ≤ frame-size (16 ≤ 40)
pair≤frame : pair-alloc ≤ frame-size
pair≤frame = from-yes-≤ (pair-alloc ≤? frame-size)

-- | saved-regs-size ≤ frame-size (24 ≤ 40)
regs≤frame : saved-regs-size ≤ frame-size
regs≤frame = from-yes-≤ (saved-regs-size ≤? frame-size)

------------------------------------------------------------------------
-- Slot-1 bounds (_ < frame-size ∸ word-size, _ ≤ frame-size ∸ word-size)
--
-- frame-size ∸ word-size = 32 (offset to slot 1)
------------------------------------------------------------------------

-- | pair-alloc ≤ (frame-size ∸ word-size) (16 ≤ 32)
pair≤slot1 : pair-alloc ≤ (frame-size ∸ word-size)
pair≤slot1 = from-yes-≤ (pair-alloc ≤? (frame-size ∸ word-size))

-- | saved-regs-size ≤ (frame-size ∸ word-size) (24 ≤ 32)
regs≤slot1 : saved-regs-size ≤ (frame-size ∸ word-size)
regs≤slot1 = from-yes-≤ (saved-regs-size ≤? (frame-size ∸ word-size))

------------------------------------------------------------------------
-- Saved-regs-size bounds (_ ≤ saved-regs-size)
--
-- saved-regs-size = 24
------------------------------------------------------------------------

-- | word-size ≤ saved-regs-size (8 ≤ 24)
-- Already in Arithmetic.agda as word≤regs, re-exported for convenience
word≤regs : word-size ≤ saved-regs-size
word≤regs = from-yes-≤ (word-size ≤? saved-regs-size)

-- | pair-alloc ≤ saved-regs-size (16 ≤ 24)
-- Already in Arithmetic.agda as pair≤regs, re-exported for convenience
pair≤regs : pair-alloc ≤ saved-regs-size
pair≤regs = from-yes-≤ (pair-alloc ≤? saved-regs-size)

------------------------------------------------------------------------
-- Rsp-bound lemmas for specific stack configurations
--
-- These relate to minimum rsp values needed for various operations.
-- 33 = frame-size - word-size + 1 (minimum rsp for pair frame with margin)
-- 17 = pair-alloc + 1 (minimum rsp for thunk operations)
------------------------------------------------------------------------

-- | Minimum rsp for pair frame operations (33 ≤ 40)
-- 33 = saved-regs-size + word-size + 1 = 24 + 8 + 1
rsp-min-pair≤frame : 33 ≤ frame-size
rsp-min-pair≤frame = from-yes-≤ (33 ≤? frame-size)

-- | Minimum rsp for thunk operations (1 ≤ 17)
rsp-min-thunk-1 : 1 ≤ 17
rsp-min-thunk-1 = from-yes-≤ (1 ≤? 17)

-- | word-size fits in thunk rsp bound (8 ≤ 17)
word≤thunk-bound : word-size ≤ 17
word≤thunk-bound = from-yes-≤ (word-size ≤? 17)

-- | word-size < thunk rsp bound (8 < 17, i.e., 9 ≤ 17)
word<thunk-bound : word-size < 17
word<thunk-bound = from-yes-< (word-size <? 17)

------------------------------------------------------------------------
-- Small slot bounds (for capacity proofs)
------------------------------------------------------------------------

-- | 2 ≤ 3 (slot bounds)
2≤3 : 2 ≤ 3
2≤3 = from-yes-≤ (2 ≤? 3)

-- | 3 ≤ 5 (slot bounds for pair setup)
3≤5 : 3 ≤ 5
3≤5 = from-yes-≤ (3 ≤? 5)

-- | 2 ≤ 5 (slot bounds)
2≤5 : 2 ≤ 5
2≤5 = from-yes-≤ (2 ≤? 5)

-- | 3 ≤ 3 (reflexive, for capacity)
3≤3 : 3 ≤ 3
3≤3 = from-yes-≤ (3 ≤? 3)

------------------------------------------------------------------------
-- Compile-length bounds (instruction sequence lengths)
------------------------------------------------------------------------

-- | 6 < 19 (closure header < curry instructions)
6<19 : 6 < 19
6<19 = from-yes-< (6 <? 19)

------------------------------------------------------------------------
-- Word vs pair-alloc bounds
------------------------------------------------------------------------

-- | word-size < pair-alloc (8 < 16)
word<pair : word-size < pair-alloc
word<pair = from-yes-< (word-size <? pair-alloc)

------------------------------------------------------------------------
-- Thunk setup bounds (for ThunkExec.agda)
--
-- thunk-min-rsp = 41 = slots 5 + 1 (minimum rsp for thunk operations)
-- rsp-after-rbp-min = 25 = 33 - 8 (rsp after rbp push, minimum)
------------------------------------------------------------------------

-- | pair-alloc ≤ rsp-after-rbp-min (16 ≤ 25)
-- Used for local-alloc-safe-after-pushes in thunk setup
pair≤rsp-after-rbp-min : pair-alloc ≤ 25
pair≤rsp-after-rbp-min = from-yes-≤ (pair-alloc ≤? 25)

-- | word-size ≤ word-size + 1 (8 ≤ 9)
-- Used for 8≤9 proofs in thunk frame calculations
word≤word+1 : word-size ≤ 9
word≤word+1 = from-yes-≤ (word-size ≤? 9)

-- | thunk-min-rsp-actual = 49 = slots thunk-setup-capacity + 1 = 48 + 1
-- This is what StackCapacity.rsp-sufficient gives: old-rsp > 48

-- | 41 ≤ thunk-rsp-actual-min (41 ≤ 49)
-- Used for rsp-safe-after-r15-push derivation from capacity
41≤thunk-rsp-actual : 41 ≤ 49
41≤thunk-rsp-actual = from-yes-≤ (41 ≤? 49)

-- | four-slot-offset ≤ thunk-rsp-actual-min (32 ≤ 49)
-- Used for rsp-above-4-slots, rsp-fits-4-slots in thunk operations
four-slots≤thunk-rsp-actual : 32 ≤ 49
four-slots≤thunk-rsp-actual = from-yes-≤ (32 ≤? 49)

-- | three-slot-offset+1 ≤ thunk-rsp-actual-min (25 ≤ 49)
-- Used for rsp-above-3-slot-offset in thunk operations
rsp-after-rbp-min≤thunk-rsp-actual : 25 ≤ 49
rsp-after-rbp-min≤thunk-rsp-actual = from-yes-≤ (25 ≤? 49)

-- | three-slots ≤ four-slots (24 ≤ 32)
-- Used for three-slots-fit-in-four associativity proofs
three-slots≤four-slots : 24 ≤ 32
three-slots≤four-slots = from-yes-≤ (24 ≤? 32)

------------------------------------------------------------------------
-- Capacity slot bounds (for slot≤capacity proofs)
------------------------------------------------------------------------

-- | 2 ≤ 6 (output slots ≤ thunk setup capacity)
2≤6 : 2 ≤ 6
2≤6 = from-yes-≤ (2 ≤? 6)

-- | 3 ≤ 6 (various slot bounds)
3≤6 : 3 ≤ 6
3≤6 = from-yes-≤ (3 ≤? 6)

-- | 4 ≤ 6 (curry closure capacity ≤ thunk setup capacity)
4≤6 : 4 ≤ 6
4≤6 = from-yes-≤ (4 ≤? 6)

------------------------------------------------------------------------
-- Zero bounds (for non-zero proofs)
------------------------------------------------------------------------

-- | 0 < word-size (stack operations need positive offsets)
0<word : 0 < word-size
0<word = from-yes-< (0 <? word-size)

-- | 0 < pair-alloc
0<pair : 0 < pair-alloc
0<pair = from-yes-< (0 <? pair-alloc)
