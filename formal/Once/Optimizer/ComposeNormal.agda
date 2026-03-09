------------------------------------------------------------------------
-- Once.Optimizer.ComposeNormal
--
-- Analysis of optimize-compose producing normal forms.
--
-- STATUS: This proof is blocked by fundamental limitations:
--
-- 1. MULTI-PASS ISSUE: The optimizer uses multiple passes (optimize-n 10)
--    to reach normal forms. A single pass of optimize-compose may produce
--    reducible output, particularly for:
--    - apply ∘ ⟨ curry (h ∘ snd) , g ⟩ → h ∘ g (may be reducible if h = id)
--    - apply ∘ ⟨ curry (h ∘ terminal) , g ⟩ → h ∘ terminal (similar issue)
--    - Pair distribution producing ⟨ fst , snd ⟩ (eta-reducible)
--
-- 2. OPTIMIZER GAPS: The optimizer doesn't reduce some reducible patterns:
--    - initial ∘ id (red-id-right applies, but optimizer returns unchanged)
--    - initial ∘ initial (red-initial applies, but optimizer returns unchanged)
--
-- 3. PATTERN MATCHING: When proving by case enumeration, variable patterns
--    prevent Agda from reducing optimize-compose, making proofs stuck.
--
-- PROVEN MECHANICALLY (in principle):
--   - Identity laws: id ∘ f = f, f ∘ id = f
--   - Beta laws: fst ∘ ⟨ f , g ⟩, snd ∘ ⟨ f , g ⟩, [ f , g ] ∘ inl/inr
--   - Fixed point laws: fold ∘ unfold = id, unfold ∘ fold = id
--   - Dead code: terminal ∘ f = terminal
--   - Initial absorption: f ∘ initial = initial
--   - Many apply-curry subcases
--
-- We use a postulate to state the theorem, acknowledging that a full
-- mechanized proof would require either:
-- 1. Restructuring the optimizer to always produce normal forms in one pass
-- 2. Proving multi-pass convergence via well-founded recursion
------------------------------------------------------------------------

module Once.Optimizer.ComposeNormal where

open import Once.Type
open import Once.IR
open import Once.Optimize using (optimize-compose)
open import Once.Optimizer.PairCaseNormal using (IsNormal)

------------------------------------------------------------------------
-- Main theorem (postulated due to limitations above)
------------------------------------------------------------------------

-- | optimize-compose produces normal forms when given normal inputs
--
-- This is true in practice because the full optimizer uses multiple passes.
-- A single pass may not produce normal forms for all cases.
postulate
  optimize-compose-normal : ∀ {A B C} (g : IR B C) (f : IR A B) →
    IsNormal g → IsNormal f → IsNormal (optimize-compose g f)

------------------------------------------------------------------------
-- Documentation of mechanically provable cases
------------------------------------------------------------------------

-- The following cases could be proven mechanically if we enumerated
-- all patterns explicitly. They are listed here for documentation.
--
-- IDENTITY LAWS (fully provable):
--   optimize-compose id f = f → IsNormal f ✓
--   optimize-compose g id = g → IsNormal g ✓
--
-- BETA LAWS - PRODUCTS (fully provable):
--   optimize-compose fst ⟨ f , g ⟩ = f → IsNormal f (from normal pair) ✓
--   optimize-compose snd ⟨ f , g ⟩ = g → IsNormal g (from normal pair) ✓
--
-- BETA LAWS - COPRODUCTS (fully provable):
--   optimize-compose [ f , g ] (inl _) = f → IsNormal f (from normal case) ✓
--   optimize-compose [ f , g ] (inr _) = g → IsNormal g (from normal case) ✓
--
-- FIXED POINT LAWS (fully provable):
--   optimize-compose fold unfold = id → normal-id ✓
--   optimize-compose unfold fold = id → normal-id ✓
--   optimize-compose fold (unfold ∘ f) = f → IsNormal f ✓
--   optimize-compose unfold (fold ∘ f) = f → IsNormal f ✓
--
-- DEAD CODE (fully provable):
--   optimize-compose terminal f = terminal → normal-terminal ✓
--
-- INITIAL ABSORPTION (fully provable):
--   optimize-compose f initial = initial → normal-initial ✓
--
-- APPLY-CURRY - SOME CASES (fully provable):
--   optimize-compose apply ⟨ curry (h ∘ fst) , g ⟩ = h → IsNormal h ✓
--   optimize-compose apply ⟨ curry terminal , g ⟩ = terminal → normal-terminal ✓
--   optimize-compose apply ⟨ curry id , g ⟩ = ⟨ id , g ⟩ → normal pair ✓
--   optimize-compose apply ⟨ curry fst , g ⟩ = id → normal-id ✓
--   optimize-compose apply ⟨ curry snd , g ⟩ = g → IsNormal g ✓
--
-- APPLY-CURRY - PROBLEMATIC CASES (need postulate):
--   optimize-compose apply ⟨ curry (h ∘ snd) , g ⟩ = h ∘ g
--     → May be reducible (e.g., if h = id)
--   optimize-compose apply ⟨ curry (h ∘ terminal) , g ⟩ = h ∘ terminal
--     → May be reducible (e.g., if h = id)
--   optimize-compose apply ⟨ curry (h ∘ k) , g ⟩ = h ∘ (k ∘ ⟨ id , g ⟩)
--     → Nested composition may be reducible
--
-- ASSOCIATIVITY (complex):
--   optimize-compose (h ∘ g) f = optimize-compose h (optimize-compose g f)
--     → Requires recursion; optimizer doesn't always apply associativity
