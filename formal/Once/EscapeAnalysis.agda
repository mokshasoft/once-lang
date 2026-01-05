------------------------------------------------------------------------
-- Once.EscapeAnalysis
--
-- Escape analysis for determining Stack vs Heap allocation mode.
--
-- Level 1 (Conservative): Identifies obvious safe cases for stack allocation:
--   - Pairs that are immediately consumed (not returned)
--   - Sums that are immediately case-analyzed
--   - Everything else uses Heap
--
-- Key insight: A value can be stack-allocated if it doesn't outlive
-- its allocation context. Values that escape (get returned, stored in
-- closures, etc.) must be heap-allocated.
------------------------------------------------------------------------

module Once.EscapeAnalysis where

open import Once.Type
open import Once.IR

------------------------------------------------------------------------
-- Escape Context
------------------------------------------------------------------------

-- | Context tracks whether we're in a position where allocated values escape
data EscapeContext : Set where
  Returning : EscapeContext  -- Allocated value will be returned (escapes)
  Consuming : EscapeContext  -- Allocated value will be consumed (safe)

------------------------------------------------------------------------
-- Allocation Mode Analysis
------------------------------------------------------------------------

-- | Analyze an IR term to determine allocation mode for each constructor
--
-- Conservative rules:
--   - Pairs in ⟨f,g⟩ that are immediately consumed by composition: Stack
--   - Sums (inl/inr) that are immediately case-analyzed: Stack
--   - Curry closures: always Heap (they escape by definition)
--   - Everything else: Heap (conservative)

analyzeAlloc : ∀ {A B} → IR A B → EscapeContext → AllocMode

-- Identity never allocates
analyzeAlloc id _ = Heap  -- dummy, id doesn't use AllocMode

-- Composition: the result of g is returned (escapes)
-- but intermediate results from f can be stack-allocated
analyzeAlloc (g ∘ f) ctx = analyzeAlloc g ctx

-- Projections don't allocate
analyzeAlloc fst _ = Heap  -- dummy
analyzeAlloc snd _ = Heap  -- dummy

-- Pair ⟨f,g⟩:
--   - If we're in a Consuming context (e.g., followed by fst/snd), use Stack
--   - If we're Returning, must use Heap
analyzeAlloc (⟨ f , g ⟩ _) Consuming = Stack  -- Safe: pair consumed immediately
analyzeAlloc (⟨ f , g ⟩ _) Returning = Heap   -- Escapes: must heap-allocate

-- Left injection inl:
--   - Conservative for now: always Heap
--   - TODO: Stack if immediately case-analyzed
analyzeAlloc (inl _) _ = Heap

-- Right injection inr:
--   - Conservative for now: always Heap
--   - TODO: Stack if immediately case-analyzed
analyzeAlloc (inr _) _ = Heap

-- Case analysis [f,g]:
--   - The result of f or g determines allocation
analyzeAlloc [ f , g ] ctx = analyzeAlloc f ctx  -- Both branches analyzed same way

-- Terminal/Initial don't allocate meaningfully
analyzeAlloc terminal _ = Heap  -- dummy
analyzeAlloc initial _ = Heap   -- dummy

-- Curry: always Heap (closure escapes by definition)
analyzeAlloc (curry f _) _ = Heap  -- Closures must be heap-allocated

-- Apply doesn't allocate
analyzeAlloc apply _ = Heap  -- dummy

-- Fold/unfold are identity at runtime
analyzeAlloc fold _ = Heap    -- dummy
analyzeAlloc unfold _ = Heap  -- dummy

-- Arr is identity at runtime
analyzeAlloc arr _ = Heap     -- dummy
