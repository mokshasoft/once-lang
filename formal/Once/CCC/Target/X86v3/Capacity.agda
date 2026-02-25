------------------------------------------------------------------------
-- Once.CCC.Target.X86v3.Capacity
--
-- Capacity invariants for X86v3 SlotMachine proof.
--
-- The key insight: if frame-capacity is large enough to accommodate
-- both working usage (pair-slots * ir-size) and reserved capacity
-- (pair-slots * program-bound), then program-bound-cap holds throughout.
--
-- See final-postulate-elimination.md for the two-capacity-pools design.
------------------------------------------------------------------------

module Once.CCC.Target.X86v3.Capacity where

open import Data.Nat using (ℕ; _≤_; _<_) renaming (_+_ to _+ℕ_; _*_ to _*ℕ_)
open import Data.Nat.Properties using (≤-refl; ≤-trans; +-monoˡ-≤; +-monoʳ-≤; m≤m+n; <⇒≤; *-monoʳ-≤; m+n≤o⇒m≤o; m+n≤o⇒n≤o)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; trans)

open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.SlotMachine
open import Once.CCC.Target.X86v3.Allocation
open import Once.CCC.IR using (pair-slots)

------------------------------------------------------------------------
-- Two Capacity Pools Design
--
-- The frame has two conceptual pools:
--   working-pool:  pair-slots * program-bound (for structural recursion)
--   reserved-pool: pair-slots * program-bound (for apply bodies)
--
-- If frame-capacity ≥ 2 * pair-slots * program-bound, then at any point
-- during execution where next-slot ≤ pair-slots * program-bound,
-- we have: next-slot +ℕ pair-slots * program-bound ≤ frame-capacity
------------------------------------------------------------------------

module CapacityLemmas {FS : FrameSemantics} (program-bound : ℕ) where
  open FrameSemantics FS

  ------------------------------------------------------------------------
  -- Core Types
  ------------------------------------------------------------------------

  -- The capacity invariant: frame has enough space for two pools
  -- Plus extra pair-slots for apply's pair allocation overhead
  -- Total: 2 * ps * pb + ps = ps * (2*pb + 1)
  CapacityInvariant : AllocState {FS} → Set
  CapacityInvariant alloc =
    pair-slots +ℕ pair-slots *ℕ program-bound +ℕ pair-slots *ℕ program-bound ≤ frame-capacity alloc

  -- Slot is within working pool with slack for apply's pair allocation
  -- Invariant: slot +ℕ pair-slots ≤ ps * pb
  -- This ensures that after apply allocates pair-slots, we still have SlotInWorking
  SlotInWorking : AllocState {FS} → Set
  SlotInWorking alloc = next-slot alloc +ℕ pair-slots ≤ pair-slots *ℕ program-bound

  ------------------------------------------------------------------------
  -- Main Lemma: derive program-bound-cap from invariant + slot-in-working
  ------------------------------------------------------------------------

  -- From invariant and slot-in-working, derive program-bound-cap
  -- New derivation with tighter SlotInWorking:
  --   SlotInWorking: slot +ℕ ps ≤ ps * pb  (so slot ≤ ps * (pb - 1))
  --   CapacityInvariant: ps + 2 * ps * pb ≤ cap
  --
  --   slot +ℕ ps * pb ≤ (ps * pb - ps) + ps * pb = 2 * ps * pb - ps ≤ 2 * ps * pb ≤ ps + 2 * ps * pb ≤ cap
  program-bound-cap-from-invariant : ∀ (alloc : AllocState {FS}) →
    CapacityInvariant alloc →
    SlotInWorking alloc →
    next-slot alloc +ℕ pair-slots *ℕ program-bound ≤ frame-capacity alloc
  program-bound-cap-from-invariant alloc inv slot-in-working =
    let
      -- From SlotInWorking: slot +ℕ ps ≤ ps * pb
      -- So: slot ≤ ps * pb - ps (subtracting ps from both sides)
      --
      -- slot +ℕ ps * pb ≤ (ps * pb - ps) + ps * pb = 2 * ps * pb - ps
      --
      -- Need: 2 * ps * pb - ps ≤ cap
      -- Have: ps + 2 * ps * pb ≤ cap (CapacityInvariant)
      --
      -- Since 2 * ps * pb - ps ≤ 2 * ps * pb < ps + 2 * ps * pb ≤ cap, done.
      --
      -- But we need to prove this without subtraction. Alternative approach:
      -- slot +ℕ ps * pb + ps ≤ ps * pb + ps * pb = 2 * ps * pb ≤ ps + 2 * ps * pb ≤ cap
      --
      -- From SlotInWorking: slot +ℕ ps ≤ ps * pb
      -- Add ps * pb to both sides: slot +ℕ ps + ps * pb ≤ ps * pb + ps * pb = 2 * ps * pb
      -- Need: slot +ℕ ps * pb ≤ ... but we have slot +ℕ ps + ps * pb

      -- Cleaner: use ≤-trans chains
      -- slot +ℕ ps * pb ≤ slot +ℕ ps + ps * pb (since ps ≥ 0, add ps to RHS is ok)
      --   NO! slot +ℕ ps * pb is NOT ≤ slot +ℕ ps + ps * pb unless 0 ≤ ps
      --   slot +ℕ ps * pb ≤ slot +ℕ ps * pb + ps = slot +ℕ ps + ps * pb (since ps ≥ 0)
      --   Wait, ps * pb + ps = ps * (pb + 1), not ps + ps * pb = ps * (1 + pb). Same thing.

      -- Actually, from slot-in-working: slot +ℕ ps ≤ ps * pb
      -- We want: slot +ℕ ps * pb ≤ cap
      --
      -- Observe: slot ≤ ps * pb - ps (if ps * pb ≥ ps, i.e., pb ≥ 1)
      -- BUT we can't do subtraction in Agda without monus.
      --
      -- Alternative: use the associativity
      -- slot +ℕ ps * pb = (slot +ℕ ps) + (ps * pb - ps) when ps * pb ≥ ps
      -- But again, no subtraction.
      --
      -- Let me try a different approach using the invariant directly:
      -- CapacityInvariant: ps + (ps * pb + ps * pb) ≤ cap
      --
      -- From SlotInWorking: slot +ℕ ps ≤ ps * pb
      -- Add ps * pb: (slot +ℕ ps) + ps * pb ≤ ps * pb + ps * pb = 2 * ps * pb
      -- So: slot + (ps + ps * pb) ≤ 2 * ps * pb
      -- Rearrange: slot +ℕ ps * pb + ps ≤ 2 * ps * pb
      -- This gives: slot +ℕ ps * pb ≤ 2 * ps * pb - ps (if we could subtract)
      --
      -- Instead, observe:
      -- slot +ℕ ps * pb ≤ (slot +ℕ ps) + ps * pb - ps (NO subtraction!)
      --
      -- Let me just use transitivity with the invariant:
      -- slot +ℕ ps * pb ≤ slot +ℕ ps + ps * pb (adding ps is fine)
      --                ≤ ps * pb + ps * pb (from SlotInWorking: slot +ℕ ps ≤ ps * pb)
      --                ≤ ps + ps * pb + ps * pb (adding ps)
      --                ≤ cap (CapacityInvariant)
      --
      -- Wait, I'm adding ps twice. That's wrong.
      -- Let me be more careful.

      -- From SlotInWorking: slot +ℕ ps ≤ ps * pb
      -- Goal: slot +ℕ ps * pb ≤ cap

      -- Approach: show slot +ℕ ps * pb ≤ 2 * ps * pb ≤ cap
      --
      -- From slot +ℕ ps ≤ ps * pb:
      --   Adding (ps * pb - ps) to both sides... but we can't subtract.
      --
      -- Alternative: Add ps * (pb - 1) to both sides of SlotInWorking:
      --   slot +ℕ ps + ps * (pb - 1) ≤ ps * pb + ps * (pb - 1) = ps * (pb + pb - 1) = ps * (2*pb - 1)
      --   slot +ℕ ps * pb ≤ ps * (2*pb - 1)  (since ps + ps*(pb-1) = ps*pb)
      --   And ps * (2*pb - 1) ≤ ps * (2*pb + 1) ≤ cap

      -- Hmm, this requires (pb - 1) which needs pb ≥ 1.

      -- Simpler: just use the weaker bound
      -- From SlotInWorking: slot +ℕ ps ≤ ps * pb
      --   implies slot ≤ ps * pb (since ps ≥ 0)
      -- So: slot +ℕ ps * pb ≤ ps * pb + ps * pb = 2 * ps * pb
      -- And: 2 * ps * pb ≤ ps + 2 * ps * pb ≤ cap (from CapacityInvariant)

      slot-bound : next-slot alloc ≤ pair-slots *ℕ program-bound
      slot-bound = m+n≤o⇒m≤o (next-slot alloc) slot-in-working

      two-pools : next-slot alloc +ℕ pair-slots *ℕ program-bound ≤ pair-slots *ℕ program-bound +ℕ pair-slots *ℕ program-bound
      two-pools = +-monoˡ-≤ (pair-slots *ℕ program-bound) slot-bound

      pools-fit : pair-slots *ℕ program-bound +ℕ pair-slots *ℕ program-bound ≤ frame-capacity alloc
      pools-fit = m+n≤o⇒n≤o pair-slots inv
    in ≤-trans two-pools pools-fit

  -- After apply's pair allocation, program-bound-cap still holds
  -- (even though SlotInWorking might not, since slot + 2*ps may exceed ps * pb)
  apply-pair-preserves-program-bound-cap : ∀ (alloc : AllocState {FS}) →
    CapacityInvariant alloc →
    SlotInWorking alloc →
    (next-slot alloc +ℕ pair-slots) +ℕ pair-slots *ℕ program-bound ≤ frame-capacity alloc
  apply-pair-preserves-program-bound-cap alloc inv slot-in-working =
    let
      -- From SlotInWorking: slot +ℕ ps ≤ ps * pb
      -- Goal: (slot +ℕ ps) + ps * pb ≤ cap

      -- (slot +ℕ ps) + ps * pb ≤ ps * pb + ps * pb (using SlotInWorking: slot +ℕ ps ≤ ps * pb)
      -- = 2 * ps * pb
      -- ≤ ps + 2 * ps * pb ≤ cap (from CapacityInvariant)

      step1 : (next-slot alloc +ℕ pair-slots) +ℕ pair-slots *ℕ program-bound ≤
              pair-slots *ℕ program-bound +ℕ pair-slots *ℕ program-bound
      step1 = +-monoˡ-≤ (pair-slots *ℕ program-bound) slot-in-working

      step2 : pair-slots *ℕ program-bound +ℕ pair-slots *ℕ program-bound ≤ frame-capacity alloc
      step2 = m+n≤o⇒n≤o pair-slots inv
    in ≤-trans step1 step2

  ------------------------------------------------------------------------
  -- Preservation Lemmas
  ------------------------------------------------------------------------

  -- Invariant is preserved when frame-capacity is preserved
  invariant-preserved : ∀ (alloc alloc' : AllocState {FS}) →
    frame-capacity alloc' ≡ frame-capacity alloc →
    CapacityInvariant alloc →
    CapacityInvariant alloc'
  invariant-preserved alloc alloc' cap-eq inv =
    subst (pair-slots +ℕ pair-slots *ℕ program-bound +ℕ pair-slots *ℕ program-bound ≤_) (sym cap-eq) inv

  -- SlotInWorking is preserved when slot advances by at most ir-stack-requirement
  -- if ir-size ir < program-bound
  -- Proof: slot' ≤ slot +ℕ ps * ir-size ≤ ps * pb (if slot = 0 and ir-size < pb)
  --
  -- More generally: if slot ≤ ps * pb AND slot advances by at most ps * (pb - current-depth),
  -- then slot' ≤ ps * pb.
  --
  -- For compose/pair: slot₁ ≤ slot +ℕ ps * sf where sf < pb
  -- Need: slot₁ ≤ ps * pb
  --
  -- This requires: slot +ℕ ps * sf ≤ ps * pb
  -- i.e., slot ≤ ps * (pb - sf)
  --
  -- The key insight: slot-in-working should track "remaining budget"
  -- slot ≤ ps * remaining-size where remaining-size decreases with recursion

  -- For initial call: remaining-size = pb, so slot ≤ ps * pb (slot = 0 works)
  -- After running f (size sf): slot₁ ≤ slot +ℕ ps * sf ≤ ps * (pb - sf) + ps * sf = ps * pb ✓

  -- Simplified: If slot ≤ ps * (pb - ir-size) AND slot' ≤ slot +ℕ ps * ir-size,
  -- then slot' ≤ ps * pb
  slot-in-working-preserved : ∀ (slot slot' : ℕ) (ir-sz : ℕ) →
    slot +ℕ pair-slots *ℕ ir-sz ≤ pair-slots *ℕ program-bound →
    slot' ≤ slot +ℕ pair-slots *ℕ ir-sz →
    slot' ≤ pair-slots *ℕ program-bound
  slot-in-working-preserved slot slot' ir-sz budget slot'-bound =
    ≤-trans slot'-bound budget

  -- Combined preservation: when running sub-IR preserves both invariants
  -- NOTE: This lemma needs updating for the new SlotInWorking definition.
  -- The new SlotInWorking (slot +ℕ ps ≤ ps * pb) is not preserved through
  -- structural recursion in the same way. The actual code paths use
  -- program-bound-cap-from-invariant and apply-pair-preserves-program-bound-cap
  -- directly, so this helper is not currently needed.
  --
  -- capacity-preserved-after-ir : ...
  -- (commented out until invariant tracking is redesigned)

  ------------------------------------------------------------------------
  -- IR Size Budget Lemmas
  --
  -- For structural recursion: running sub-IR of size sf consumes ps*sf
  -- from the working pool. The remaining budget is ps*(pb - sf).
  --
  -- Key insight: combined-cap (slot +ℕ ps * ir-size ≤ cap) together with
  -- SlotInWorking (slot ≤ ps * pb) ensures sub-IRs stay in working pool.
  ------------------------------------------------------------------------

  -- If slot +ℕ ps*size ≤ ps*pb AND sf < size, then slot +ℕ ps*sf ≤ ps*pb
  -- This shows that running sub-IR f (size sf < size) stays in working pool
  sub-ir-in-working : ∀ (slot : ℕ) (sf sz : ℕ) →
    sf < sz →
    slot +ℕ pair-slots *ℕ sz ≤ pair-slots *ℕ program-bound →
    slot +ℕ pair-slots *ℕ sf ≤ pair-slots *ℕ program-bound
  sub-ir-in-working slot sf sz sf<sz budget =
    ≤-trans (+-monoʳ-≤ slot (*-monoʳ-≤ pair-slots (<⇒≤ sf<sz))) budget

  ------------------------------------------------------------------------
  -- Working Pool Entry Condition
  --
  -- For the invariant system to work, we need that at entry:
  -- 1. slot = 0 (fresh frame)
  -- 2. ps * ir-size main ≤ ps * pb (main program fits in working pool)
  --
  -- This is established by WholeProgram.
  ------------------------------------------------------------------------

  -- Entry condition: slot = 0 implies SlotInWorking (slot +ℕ ps ≤ ps * pb)
  -- This requires program-bound ≥ 1, which is true for any non-trivial program.
  -- When slot = 0, we need: 0 + ps ≤ ps * pb, i.e., ps ≤ ps * pb
  entry-slot-in-working : ∀ (alloc : AllocState {FS}) →
    next-slot alloc ≡ 0 →
    1 ≤ program-bound →
    SlotInWorking alloc
  entry-slot-in-working alloc slot-zero pb≥1 =
    subst (λ s → s +ℕ pair-slots ≤ pair-slots *ℕ program-bound) (sym slot-zero) ps-bound
    where
      open import Data.Nat using (z≤n)
      open import Data.Nat.Properties using (*-identityʳ)
      -- ps ≤ ps * pb when pb ≥ 1
      -- Proof: ps = ps * 1 ≤ ps * pb (by *-monoʳ-≤ and pb ≥ 1)
      ps-bound : pair-slots ≤ pair-slots *ℕ program-bound
      ps-bound = subst (_≤ pair-slots *ℕ program-bound) (*-identityʳ pair-slots)
                   (*-monoʳ-≤ pair-slots pb≥1)

  -- Main IR fits in working pool
  main-fits-in-working : ∀ (main-size : ℕ) →
    main-size ≤ program-bound →
    pair-slots *ℕ main-size ≤ pair-slots *ℕ program-bound
  main-fits-in-working main-size sz≤pb = *-monoʳ-≤ pair-slots sz≤pb

