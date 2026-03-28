------------------------------------------------------------------------
-- Once.CCC.Machine.IR.FunctorDispatch
--
-- Functor structure helpers for recursion scheme code generation.
--
-- OCP-0003: These helpers enable the unified RecCoreWF pattern to
-- dispatch based on functor structure (K/Id/⊕/⊗).
------------------------------------------------------------------------

module Once.CCC.Machine.IR.FunctorDispatch where

open import Data.Nat using (ℕ; zero; suc; _⊔_) renaming (_+_ to _+ℕ_)
open import Data.Nat.Properties using (⊔-comm; m≤m⊔n; n≤m⊔n)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Once.Type using (Functor; K; Id; _⊕_; _⊗_)
open import Once.Functor.Translate using (WellFormedF; wf-K; wf-Id; wf-Sum; wf-Prod)

------------------------------------------------------------------------
-- Recursive Position Counting
--
-- For slot allocation, we need to know the maximum number of
-- recursive positions that can be encountered in parallel.
--
-- K _   : 0 recursive positions (constant)
-- Id    : 1 recursive position
-- F ⊕ G : max of F and G (at runtime, only one branch taken)
-- F ⊗ G : F + G (both must be processed)
------------------------------------------------------------------------

-- | Count maximum recursive positions for slot allocation
--
-- This determines how many slots we need for work variables
-- during functor dispatch.
max-rec-positions : ∀ {F} → WellFormedF F → ℕ
max-rec-positions (wf-K _) = 0
max-rec-positions wf-Id = 1
max-rec-positions (wf-Sum wfF wfG) = max-rec-positions wfF ⊔ max-rec-positions wfG
max-rec-positions (wf-Prod wfF wfG) = max-rec-positions wfF +ℕ max-rec-positions wfG

------------------------------------------------------------------------
-- Functor Case Tags
--
-- At runtime, functor layers are represented with tags for dispatch.
-- This mirrors the IR sum type representation.
------------------------------------------------------------------------

-- | Functor structure tag for runtime dispatch
data FunctorTag : Set where
  tag-K    : FunctorTag  -- Constant (no recursion needed)
  tag-Id   : FunctorTag  -- Single recursive position
  tag-Inl  : FunctorTag  -- Left branch of sum
  tag-Inr  : FunctorTag  -- Right branch of sum
  tag-Pair : FunctorTag  -- Product (both components)

------------------------------------------------------------------------
-- Slot Layout for Functor Dispatch
--
-- During recursion scheme execution, we need slots for:
--   - backup-slot: save input μ-value before destructing
--   - layer-slot: store the F-layer after destructing
--   - acc-slot: accumulate results (for non-tail recursive schemes)
--   - work-slots: temporary storage during functor dispatch
--   - alg/trans-workspace: space for algebra/transform IR execution
------------------------------------------------------------------------

-- | Slot indices for the unified recursive core
record RecCoreSlots : Set where
  field
    backup-slot   : ℕ  -- Save input before out-μ
    layer-slot    : ℕ  -- Store F/G layer
    acc-slot      : ℕ  -- Accumulator for results
    work-base     : ℕ  -- Base index for work slots

-- | Default slot layout starting at a given frontier
default-slots : ℕ → RecCoreSlots
default-slots frontier = record
  { backup-slot = frontier
  ; layer-slot  = suc frontier
  ; acc-slot    = suc (suc frontier)
  ; work-base   = suc (suc (suc frontier))
  }

------------------------------------------------------------------------
-- Functor Layer Structure
--
-- For code generation, we need to know how to traverse the F-layer
-- structure and find recursive positions.
------------------------------------------------------------------------

-- | Functor layer structure description
-- Describes how to traverse an F(X) value to find recursive X positions
data FunctorShape : Set where
  shape-K    : FunctorShape                           -- Constant, no recursion
  shape-Id   : FunctorShape                           -- Single recursive slot
  shape-Sum  : FunctorShape → FunctorShape → FunctorShape  -- Branch on tag
  shape-Prod : FunctorShape → FunctorShape → FunctorShape  -- Process both

-- | Extract shape from WellFormedF proof
wf-to-shape : ∀ {F} → WellFormedF F → FunctorShape
wf-to-shape (wf-K _) = shape-K
wf-to-shape wf-Id = shape-Id
wf-to-shape (wf-Sum wfF wfG) = shape-Sum (wf-to-shape wfF) (wf-to-shape wfG)
wf-to-shape (wf-Prod wfF wfG) = shape-Prod (wf-to-shape wfF) (wf-to-shape wfG)

------------------------------------------------------------------------
-- Recursive Position Iteration
--
-- For Cata/Fuse/Hylo, we need to iterate over all recursive positions
-- in an F-layer, applying the recursive call to each.
------------------------------------------------------------------------

-- | Count recursive positions in a shape
rec-count : FunctorShape → ℕ
rec-count shape-K = 0
rec-count shape-Id = 1
rec-count (shape-Sum s1 s2) = rec-count s1 ⊔ rec-count s2
rec-count (shape-Prod s1 s2) = rec-count s1 +ℕ rec-count s2

-- | Positions in shape for indexing
-- Each position identifies a recursive slot in the functor layer
data RecPosition : FunctorShape → Set where
  pos-Id   : RecPosition shape-Id
  pos-Inl  : ∀ {s1 s2} → RecPosition s1 → RecPosition (shape-Sum s1 s2)
  pos-Inr  : ∀ {s1 s2} → RecPosition s2 → RecPosition (shape-Sum s1 s2)
  pos-Fst  : ∀ {s1 s2} → RecPosition s1 → RecPosition (shape-Prod s1 s2)
  pos-Snd  : ∀ {s1 s2} → RecPosition s2 → RecPosition (shape-Prod s1 s2)

------------------------------------------------------------------------
-- Functor Layer Access Paths
--
-- For code generation, we need to know how to access each recursive
-- position within the F-layer memory representation.
------------------------------------------------------------------------

-- | Access path to a recursive position
-- Describes memory offsets from the layer base pointer
data AccessPath : Set where
  path-here : AccessPath                              -- Current location (Id)
  path-left : AccessPath → AccessPath                 -- Follow fst/inl pointer
  path-right : AccessPath → AccessPath                -- Follow snd/inr pointer

-- | Convert RecPosition to AccessPath
position-to-path : ∀ {s} → RecPosition s → AccessPath
position-to-path pos-Id = path-here
position-to-path (pos-Inl p) = path-left (position-to-path p)
position-to-path (pos-Inr p) = path-right (position-to-path p)
position-to-path (pos-Fst p) = path-left (position-to-path p)
position-to-path (pos-Snd p) = path-right (position-to-path p)

------------------------------------------------------------------------
-- Shape has no recursive positions predicate
------------------------------------------------------------------------

-- | Shape has no recursive positions (is constant-like)
is-constant-shape : FunctorShape → Set
is-constant-shape shape-K = ⊤
is-constant-shape shape-Id = ⊤ → ⊤  -- False (never inhabited except by id)
is-constant-shape (shape-Sum s1 s2) = is-constant-shape s1 × is-constant-shape s2
is-constant-shape (shape-Prod s1 s2) = is-constant-shape s1 × is-constant-shape s2

------------------------------------------------------------------------
-- Summary
--
-- This module provides:
--   1. max-rec-positions: count slots needed for functor dispatch
--   2. FunctorShape: structural description for code generation
--   3. RecPosition: identifies recursive positions for iteration
--   4. AccessPath: memory access patterns for positions
--
-- RecCoreWF.agda will use these to generate dispatch code.
------------------------------------------------------------------------
