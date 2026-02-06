------------------------------------------------------------------------
-- Once.Backend.X86.FrameInstantiation
--
-- X86-64 instantiation of FrameSemantics.
--
-- On x86-64, stack grows downward:
--   - Caller's frame: addresses ≥ entry-rsp (above the boundary)
--   - Callee's frame: addresses < entry-rsp (below the boundary)
--
-- The boundary is the stack pointer value at function entry (rsp).
-- Callee allocates by decrementing rsp (sub rsp, N), so callee's
-- addresses are always below the entry boundary.
------------------------------------------------------------------------

module Once.Backend.X86.FrameInstantiation where

open import Data.Nat using (ℕ; _<_; _≥_; _≤_)
open import Data.Nat.Properties using (<⇒≱; ≮⇒≥; <-irrefl)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-- Import the architecture-independent interface
open import Once.Backend.Common.FrameSemantics using (FrameSemantics)
open import Once.Backend.Common.MemoryLayoutSemantics using (Addr)

-- Import Word from Memory
open import Once.Backend.Common.Memory using (Word)

------------------------------------------------------------------------
-- X86-64 Frame Regions
--
-- On x86-64:
--   - Stack grows downward (push decrements rsp)
--   - Caller's data is at higher addresses (≥ entry-rsp)
--   - Callee allocates at lower addresses (< entry-rsp)
------------------------------------------------------------------------

-- | Boundary is the stack pointer value at function entry
X86Boundary : Set
X86Boundary = Word

-- | Address is in caller's frame if it's at or above the boundary
-- (caller allocated before the call, at higher addresses)
X86InCallerFrame : Addr → X86Boundary → Set
X86InCallerFrame addr boundary = addr ≥ boundary

-- | Address is in callee's frame if it's below the boundary
-- (callee allocates by sub rsp, at lower addresses)
X86InCalleeFrame : Addr → X86Boundary → Set
X86InCalleeFrame addr boundary = addr < boundary

------------------------------------------------------------------------
-- Disjointness Proof
--
-- An address cannot be both ≥ boundary and < boundary.
-- This is a fundamental property of < and ≥ on naturals.
------------------------------------------------------------------------

x86-frames-disjoint : ∀ (addr : Addr) (b : X86Boundary) →
  X86InCallerFrame addr b →
  X86InCalleeFrame addr b →
  ⊥
x86-frames-disjoint addr b addr≥b addr<b = <⇒≱ addr<b addr≥b

------------------------------------------------------------------------
-- X86-64 FrameSemantics Instance
------------------------------------------------------------------------

x86-frame-semantics : FrameSemantics
x86-frame-semantics = record
  { Boundary = X86Boundary
  ; InCallerFrame = X86InCallerFrame
  ; InCalleeFrame = X86InCalleeFrame
  ; frames-disjoint = x86-frames-disjoint
  }

------------------------------------------------------------------------
-- Convenience Re-exports
--
-- For modules that import this instantiation.
------------------------------------------------------------------------

open FrameSemantics x86-frame-semantics public
  renaming ( InCallerFrame to X86-InCallerFrame
           ; InCalleeFrame to X86-InCalleeFrame
           ; frames-disjoint to X86-frames-disjoint
           )
