------------------------------------------------------------------------
-- Once.CCC.Machine.IR.RecSchemeProof
--
-- PROOF of rec-scheme-semantic via structural induction on μ-values.
--
-- Key insight: If the Dispatcher proves that algebra IR preserves
-- ValidAtWF (input valid → output valid), then Cata also preserves
-- ValidAtWF, by induction on the μ-value structure.
--
-- Proof strategy:
--   1. Base case (K layers): ValidAtWF for constants is trivial
--   2. Id case: Use IH to get ValidAtWF for recursive result
--   3. Sum case: Use ValidAtWF for the taken branch
--   4. Prod case: Build ValidAtWF for pair from components
--   5. Apply algebra: Dispatcher correctness gives ValidAtWF for result
--
-- The semantic equation (sem-cata-compute) drives the induction:
--   sem-cata alg (In x) = alg (fmap (sem-cata alg) x)
--
-- At each step:
--   - IH gives ValidAtWF for recursive results in x
--   - fmap applies sem-cata to recursive positions
--   - We build ValidAtWF for the whole F-layer
--   - Dispatcher correctness for alg gives ValidAtWF for final result
------------------------------------------------------------------------

module Once.CCC.Machine.IR.RecSchemeProof where

open import Data.Nat using (ℕ; zero; suc; _<_; _≤_) renaming (_+_ to _+ℕ_)
open import Data.Nat.Properties using (≤-refl; ≤-trans; n≤1+n)
open import Data.Bool using (false)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.SMCore hiding (AllocMode; Stack; Heap)
open import Once.IR using (IR; Cata)
open import Once.Type using (Type; Functor; K; Id; _⊕_; _⊗_; μ-type)
open import Once.Functor.Translate using (WellFormedF; wf-K; wf-Id; wf-Sum; wf-Prod)
import Once.CCC.Eval as Ev
import Once.Semantics.Machine as EvV
open import Once.Semantics.Machine using (⟦_⟧)
open import Once.IR.Size
open import Once.CCC.Machine.Allocation using (AllocMode; Stack; Heap; AllocState)

-- Import semantic operations
open import Once.Word using (Carrier)
open import Once.Float.Decimal using (Decimal)
open import Once.Semantics.Value Carrier Carrier using (⟦μ⟧; ⟦_⟧F; sem-In; sem-Out; sem-cata; sem-cata-compute; sem-fmap)

------------------------------------------------------------------------
-- Proof Module
--
-- Parameterized by FrameSemantics, program-bound, and SigOpSem.
------------------------------------------------------------------------

module RecSchemeProofImpl {FS : FrameSemantics} (program-bound : ℕ) where
  -- Plan 0.73 (D113): `eval` is target-relative at `Float` — a float literal
  -- has no format-free machine value. Inside a module already fixed to this
  -- target's `FrameSemantics`, THE evaluator is the one at its float format,
  -- so it is named once here and used unqualified below.
  eval : ∀ {A B} → IR A B → EvV.⟦ A ⟧ᴵ → EvV.⟦ B ⟧ᴵ
  eval = Ev.eval (Once.CCC.FrameSemantics.fs-numerics FS)

  open FrameSemantics FS
  open import Once.CCC.Machine.ClosureWellFormed
  open ClosureWellFormedDef {FS} program-bound

  ------------------------------------------------------------------------
  -- ValidAtWF Preservation
  --
  -- An IR "preserves ValidAtWF" if:
  --   Given ValidAtWF input, Dispatcher execution produces ValidAtWF output.
  --
  -- This is exactly what the Dispatcher proves for all IR operations.
  -- We capture this as a predicate for use in the inductive proof.
  ------------------------------------------------------------------------

  -- ValidAtWF preservation: if input is valid, output is valid
  -- This is the contract that Dispatcher establishes for each IR operation.
  record PreservesValidAtWF {A B : Type} (ir : IR A B) : Set where
    field
      -- For any valid input, executing ir produces valid output
      preserves : ∀ (m : AllocMode) (alloc : AllocState {FS})
        (x : ⟦ A ⟧) (input-loc result-loc : ValueLocation FS) (s s' : LocState FS)
        → ValidAtWF m alloc x input-loc s
        → BeforeFrontier alloc input-loc
        → BeforeFrontier alloc result-loc
        -- After some trace execution, result is valid
        → ValidAtWF Heap alloc (eval ir x) result-loc s'

  ------------------------------------------------------------------------
  -- Functor Layer ValidAtWF
  --
  -- For each functor shape, show how to build ValidAtWF for the layer
  -- given ValidAtWF for all recursive positions.
  ------------------------------------------------------------------------

  -- For K A (constant): ValidAtWF for A directly
  -- No recursive positions, so this is the base case.

  -- For Id: ValidAtWF for the single recursive position
  -- This is handled by the IH.

  -- For F ⊕ G (sum): ValidAtWF for inl or inr branch
  -- We use valid-inl-wf or valid-inr-wf constructor.

  -- For F ⊗ G (product): ValidAtWF from components
  -- We use valid-pair-wf constructor.

  ------------------------------------------------------------------------
  -- Main Theorem: Cata Preserves ValidAtWF
  --
  -- If the algebra IR preserves ValidAtWF (Dispatcher proves this),
  -- then Cata wf alg also preserves ValidAtWF.
  --
  -- Proof by structural induction on μ-values.
  --
  -- NOTE: This requires well-founded recursion on μ-values.
  -- Agda cannot see that sem-Out produces a structurally smaller value.
  -- (This comment used to claim a TERMINATING pragma was used here; there is
  -- none in this module. Plan 0.27 Option B replaced that approach with the
  -- reified `MuSize` measure — see `Once.CCC.Machine.IR.MuSize`.)
  ------------------------------------------------------------------------

  -- The inductive hypothesis type for Cata proof
  -- This captures what we need to prove at each μ-value level.
  CataIH : ∀ {F B : Type} (wf : WellFormedF F) (alg : IR (⟦ F ⟧T B) B)
         → ⟦ μ-type F ⟧ → Set
  CataIH {F} {B} wf alg x =
    ∀ (alloc : AllocState {FS}) (result-loc : ValueLocation FS) (s : LocState FS)
    → BeforeFrontier alloc result-loc
    → ValidAtWF Heap alloc (sem-cata wf (λ fa → eval alg fa) x) result-loc s

  ------------------------------------------------------------------------
  -- Proof Sketch (to be completed)
  --
  -- The full proof would:
  --
  -- 1. Define cata-valid by well-founded recursion on μ-values:
  --    cata-valid : ∀ x → CataIH wf alg x
  --
  -- 2. Case split on sem-Out wf x:
  --    - For each functor constructor, build ValidAtWF for the F-layer
  --    - Use IH for recursive positions
  --    - Apply algebra (Dispatcher gives ValidAtWF)
  --
  -- 3. Connect to rec-scheme-semantic:
  --    - Show eval (Cata wf alg) x = sem-cata wf (eval ps alg) x
  --    - Use cata-valid to get ValidAtWF
  --
  -- The main technical challenges:
  --   a) Termination: sem-Out obscures structural decrease
  --   b) Functor dispatch: handling all shapes uniformly
  --   c) Algebra application: connecting to Dispatcher
  ------------------------------------------------------------------------

  ------------------------------------------------------------------------
  -- Lambek Isomorphism Proof
  --
  -- For In, out-μ, Out, in-ν: these are representationally identity.
  -- ValidAtWF transfers because μF and F(μF) have the same representation.
  --
  -- Proof: Show that ValidAtWF for F(μF) can be converted to ValidAtWF
  -- for μF and vice versa, since they have identical memory layout.
  --
  -- This is simpler than the Cata case because there's no recursion -
  -- it's just showing that the same value in memory satisfies both types.
  ------------------------------------------------------------------------

  -- ValidAtWF respects isomorphic representation
  -- If x : F(μF) is valid at loc, then sem-In F x : μF is valid at loc
  -- (same memory layout, different type interpretation)

  -- Note: This requires showing that ValidAtWF's structural constraints
  -- are preserved through the type isomorphism. Since μF ≅ F(μF) by
  -- Lambek, and our representation follows this isomorphism, the proof
  -- should be straightforward.

------------------------------------------------------------------------
-- CRITICAL ISSUE: Abstract Machine Doesn't Model Recursive Execution
--
-- The current abstract machine architecture has a fundamental gap:
--
-- Current state:
--   - Traces are LINEAR sequences of abstract instructions
--   - Recursive execution is NOT modeled in traces
--   - RecCoreWF generates STUB traces that just store/return pointers
--   - The postulate says "trust that the semantic value ends up there"
--
-- What the stub trace does:
--   cata-trace = mov-to-output ∷ store-at-slot n ∷ lea-slot n ∷ []
--   1. Copy input pointer to output
--   2. Store at slot n
--   3. Return pointer to slot n
--   This does NOT compute the catamorphism!
--
-- Why this is a trust boundary:
--   - The actual recursive computation happens "outside" the trace model
--   - We trust that SOME mechanism correctly computes the catamorphism
--   - The trace just records where the result will be stored
--   - ValidAtWF at that location is POSTULATED, not proven
--
------------------------------------------------------------------------
-- PATH TO ELIMINATE THE POSTULATE
--
-- Option A: Extend Abstract Machine
--   1. Add recursive trace execution (call stack, return addresses)
--   2. Generate traces that include recursive calls
--   3. Prove: executing these traces computes sem-cata
--   4. Connect execution result to ValidAtWF
--   Effort: MAJOR - requires new machine model
--
-- Option B: Direct Semantic Proof
--   1. Prove at semantic level: eval (Cata wf alg) preserves ValidAtWF
--   2. This requires showing: if alg preserves ValidAtWF, so does Cata
--   3. Use well-founded recursion on μ-values
--   4. Connect to trace model via representation lemmas
--   Effort: MODERATE - extends current architecture
--
-- Option C: Accept Trust Boundary
--   1. Document that rec-scheme-semantic is a compiler correctness claim
--   2. The abstract trace model doesn't capture recursive execution
--   3. Correctness relies on: eval and runtime agree on recursion schemes
--   4. This is analogous to trusting the GHC RTS implements recursion
--   Effort: MINIMAL - documentation only
--
------------------------------------------------------------------------
-- CURRENT STATUS
--
-- This module provides the ARCHITECTURE for Option B, but doesn't
-- complete the proof due to:
--   1. Termination: sem-Out obscures structural decrease
--   2. Machine model gap: traces don't model recursive execution
--
-- The semantic equations (sem-cata-compute) are proven.
-- The connection to ValidAtWF requires either:
--   - Extended machine model (Option A)
--   - Direct semantic proof with termination workaround (Option B)
--
-- For now, rec-scheme-semantic remains a TRUST BOUNDARY that captures:
--   "The Once compiler correctly implements recursion schemes"
------------------------------------------------------------------------
