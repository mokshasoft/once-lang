------------------------------------------------------------------------
-- Once.Postulates
--
-- CENTRAL REGISTRY OF ALL ASSUMPTIONS AND POSTULATES
--
-- This module collects all postulates, axioms, and known semantic gaps
-- in the Once formalization. Any proof that depends on unproven
-- assumptions should import from here, making dependencies explicit.
--
-- When adding new assumptions, document:
--   1. What is assumed (the postulate or limitation)
--   2. Why it's needed (which proofs depend on it)
--   3. Justification (why we believe it's sound)
--   4. Impact (what would break if it's wrong)
--
-- To detect all postulates in the codebase:
--   agda --safe <file>        # fails if file uses postulates
--   grep -r "postulate" .     # find all postulate declarations
--
------------------------------------------------------------------------

module Once.Postulates where

open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)
open import Data.Nat using (ℕ; _≤_) renaming (_+_ to _+ℕ_)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Maybe using (Maybe; just; nothing)

open import Once.Type
open import Once.CCC.IR
open import Once.Memory using (Word)
open import Once.Semantics

-- Note: X86-specific postulates have been ELIMINATED.
-- All X86 proofs now use proper capacity and region threading.

-- Re-export encode and PROVEN encoding properties from Semantics
open Once.Semantics public using (encode; encode-unit; encode-fix-wrap; encode-fix-unwrap; encode-arr-identity)
-- Re-export low-level encoding postulates (for proofs that need them directly)
open Once.Semantics public using (encode-pair-addr; encode-inl-addr; encode-inr-addr; encode-closure-addr)

------------------------------------------------------------------------
-- Postulate P1: Function Extensionality
------------------------------------------------------------------------
--
-- Two functions are equal if they agree on all inputs.
--
-- NEEDED BY: Once.Surface.Correct (elaborate-correct for lambdas)
--
-- JUSTIFICATION:
--   Function extensionality is consistent with Agda's type theory
--   and holds in most models (e.g., setoid model, cubical type theory).
--   It's used only in proof terms, which are erased during extraction.
--
-- IMPACT:
--   If function extensionality were somehow false, the elaboration
--   correctness proof for lambda expressions would be invalid.
--   However, this would also break most of mathematics, so we're
--   confident this is safe.
--
-- RUNTIME EFFECT: None (erased during extraction)
--
------------------------------------------------------------------------

postulate
  extensionality : ∀ {A : Set} {B : A → Set} {f g : (x : A) → B x} →
                   (∀ x → f x ≡ g x) → f ≡ g

------------------------------------------------------------------------
-- Postulate P1b: Closure Equality (Semantics-Based)
------------------------------------------------------------------------
--
-- STATUS: SHOULD BE ELIMINATED for closed Once programs
--
-- Two closures are equal if their semantics are equal.
--
-- NEEDED BY: Once.Surface.Correct (elaborate-correct for lambdas)
--
-- WHY IT EXISTS:
--   The proof in Surface.Correct compares closures abstractly without
--   tracking how they were created. It needs to show that a closure from
--   surface semantics equals one from IR semantics.
--
-- WHY IT'S ELIMINABLE:
--   For closed Once programs, ALL closures are created by Once:
--   - Surface closures come from Once lambdas
--   - IR closures come from Once's curry operation
--
--   Since we control both, we can track closure creation and prove
--   STRUCTURAL equality (same env-addr, same code-ptr) rather than
--   assuming semantic equality implies structural equality.
--
-- ELIMINATION STRATEGY:
--   1. Thread ClosureEntry tracking through Surface.Elaborate
--   2. Show that elaborated lambdas produce closures with known structure
--   3. Prove env-addr and code-ptr match between surface and IR closures
--   4. Derive full closure equality structurally
--
--   This follows the same pattern as apply-produces-result elimination:
--   track closure provenance instead of treating closures as opaque.
--
-- NOTE: For open programs (interfacing with external code), this would
--   remain as a trust boundary - external closures must behave correctly.
--
-- RUNTIME EFFECT: None (erased during extraction)
--
------------------------------------------------------------------------

postulate
  closure-semantics-eq : ∀ {A B : Type} (c1 c2 : Closure A B) →
                         Closure.semantics c1 ≡ Closure.semantics c2 →
                         c1 ≡ c2

------------------------------------------------------------------------
-- Postulate P1c: Arrow Quantity Coercion for IR
------------------------------------------------------------------------
--
-- STATUS: ELIMINATED
--
-- This postulate was eliminated by making curry and apply quantity-
-- polymorphic in Once.IR:
--
--   curry : ∀ {A B C q} → IR (A * B) C → AllocMode → IR A (B ⇒[ q ] C)
--   apply : ∀ {A B q} → IR ((A ⇒[ q ] B) * A) B
--
-- Now Once.Surface.Elaborate can directly produce the correct type:
--   elaborate (lam q e) = curry (elaborate e) Heap
--   elaborate (app f x) = apply ∘ ⟨ elaborate f , elaborate x ⟩ Heap
--
-- No coercion needed since quantities are phantom type parameters.
--
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Semantic Gap S1: Fixed Point Semantics
------------------------------------------------------------------------
--
-- NOT A POSTULATE (no axiom is assumed), but a KNOWN SEMANTIC GAP.
--
-- The current interpretation of Fix F uses a simple newtype wrapper:
--
--   record ⟦Fix⟧ (A : Set) : Set where
--     constructor wrap
--     field unwrap : A
--
--   ⟦ Fix F ⟧ = ⟦Fix⟧ ⟦ F ⟧
--
-- This models Fix F ≅ F, but the correct equation should be:
--
--   Fix F ≅ F[Fix F / X]   (F with recursive occurrences substituted)
--
-- CONSEQUENCE:
--   The proofs eval-fold-unfold and eval-unfold-fold are trivially refl.
--   They prove the wrapper isomorphism, NOT the recursive fixed point
--   property.
--
-- IMPACT:
--   Programs using Fix (like Nat, List) are not fully verified.
--   The fold/unfold operations are type-correct and operationally
--   behave correctly, but the semantic model doesn't capture the
--   true recursive structure.
--
-- RESOLUTION:
--   See docs/formal/what-is-proven.md for options:
--   - Option 1: Universe of strictly positive functors
--   - Option 2: Sized types
--   - Option 3: Well-founded recursion
--   - Option 4: QIITs
--
-- This limitation is documented here and in Once.Semantics.agda.
--
------------------------------------------------------------------------

-- No postulate needed; this is a documentation marker
-- The limitation is intrinsic to how ⟦_⟧ is defined for Fix.

------------------------------------------------------------------------
-- CHECKLIST FOR ADDING NEW ASSUMPTIONS
------------------------------------------------------------------------
--
-- When you need to add a postulate or discover a semantic gap:
--
-- 1. ADD IT HERE with full documentation (P2, P3, ... or S2, S3, ...)
-- 2. Document which modules depend on it (NEEDED BY)
-- 3. Explain why it's believed sound (JUSTIFICATION)
-- 4. Describe what would fail if it's wrong (IMPACT)
-- 5. Note if it affects runtime (RUNTIME EFFECT)
-- 6. Update docs/formal/what-is-proven.md
--
-- Postulates (P): Explicit axioms assumed without proof
-- Semantic Gaps (S): Limitations in the semantic model itself
--
-- The goal is that anyone reading the formalization can quickly
-- understand exactly what is assumed vs. fully proven.
--
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Postulate P2: x86-64 Value Encoding
------------------------------------------------------------------------
--
-- These axioms define how semantic values are encoded as machine words.
-- A full proof would require modeling the heap explicitly and proving
-- that allocation produces the correct memory layout.
--
-- PROGRESS: 4 axioms are now PROVEN in Once.Semantics!
--   - encode-unit       : PROVEN (encode {Unit} tt = 0 by definition)
--   - encode-fix-wrap   : PROVEN (Fix is identity at runtime)
--   - encode-fix-unwrap : PROVEN (Fix is identity at runtime)
--   - encode-arr-identity : PROVEN (Eff = Closure at runtime)
--
-- REMAINING: Memory-dependent axioms for pairs/sums/closures.
-- These require knowing that values are properly allocated in memory.
--
-- NEEDED BY: Once.CCC.Target.X86.Correct (generator proofs)
--
-- JUSTIFICATION:
--   These capture the intended memory layout for the x86-64 backend:
--   - Pairs → pointer to [fst, snd]
--   - Sums → pointer to [tag, value]
--   - Functions → pointer to closure [env, code]
--
-- IMPACT:
--   If the encoding doesn't match the actual code generation,
--   the correctness theorem would be vacuously true but the
--   generated code would be wrong.
--
-- RUNTIME EFFECT: None (proof-only)
--
------------------------------------------------------------------------

-- Word is now imported from Once.Memory

-- | Memory model
Memory : Set
Memory = Word → Maybe Word

-- | Read from memory
readMem : Memory → Word → Maybe Word
readMem m addr = m addr

-- encode is now defined in Once.Semantics (partially concrete!)
-- encode-unit, encode-fix-*, encode-arr-identity are now PROVEN there.
--
-- ELIMINATION STATUS:
-- These postulates can be eliminated by switching to "stateful validity"
-- predicates (PairAtS, InlAtS, InrAtS) that track actual addresses
-- instead of using the abstract `encode` function.
--
-- See Once.CCC.Target.X86.Correct.StarBase for working examples:
--   - run-fst-star-s, run-snd-star-s: eliminate encode-pair-fst/snd
--   - run-inl-star-s, run-inr-star-s: eliminate encode-*-construct
--   - test-fst/snd/inl/inr-stateful: complete E2E proofs with NO postulates
--
-- PATH TO FULL ELIMINATION:
--   1. Thread IRStarResultS through IRRunner in MutualIR.agda
--   2. Replace encode-based proofs with validity-based proofs
--   3. Remove these postulates

postulate
  -- ELIMINABLE via PairAtS + run-fst-star-s (see StarBase.agda)
  -- Encoding preserves pair structure
  -- encode (a , b) is an address pointing to [encode a, encode b]
  encode-pair-fst : ∀ {A B} (a : ⟦ A ⟧) (b : ⟦ B ⟧) (m : Memory) →
    readMem m (encode (a , b)) ≡ just (encode a)

  -- ELIMINABLE via PairAtS + run-snd-star-s (see StarBase.agda)
  encode-pair-snd : ∀ {A B} (a : ⟦ A ⟧) (b : ⟦ B ⟧) (m : Memory) →
    readMem m ((encode (a , b)) +ℕ 8) ≡ just (encode b)

  -- ELIMINABLE via InlAtS + inl-tag-from-validity (see StarBase.agda)
  -- Encoding preserves sum structure
  -- encode (inj₁ a) is address pointing to [0, encode a]
  -- encode (inj₂ b) is address pointing to [1, encode b]
  encode-inl-tag : ∀ {A B} (a : ⟦ A ⟧) (m : Memory) →
    readMem m (encode {A + B} (inj₁ a)) ≡ just 0

  -- ELIMINABLE via InlAtS + inl-val-from-validity (see StarBase.agda)
  encode-inl-val : ∀ {A B} (a : ⟦ A ⟧) (m : Memory) →
    readMem m ((encode {A + B} (inj₁ a)) +ℕ 8) ≡ just (encode a)

  -- ELIMINABLE via InrAtS + inr-tag-from-validity (see StarBase.agda)
  encode-inr-tag : ∀ {A B} (b : ⟦ B ⟧) (m : Memory) →
    readMem m (encode {A + B} (inj₂ b)) ≡ just 1

  -- ELIMINABLE via InrAtS + inr-val-from-validity (see StarBase.agda)
  encode-inr-val : ∀ {A B} (b : ⟦ B ⟧) (m : Memory) →
    readMem m ((encode {A + B} (inj₂ b)) +ℕ 8) ≡ just (encode b)

  -- Encoding construction axioms:
  -- If memory at p has the correct shape, then p is the encoding
  -- These are the "constructors" for encoded values

  -- ELIMINABLE: run-inl-star-s produces InlAtS directly from memory writes
  -- No need to prove p ≡ encode; just track the address
  encode-inl-construct : ∀ {A B} (a : ⟦ A ⟧) (p : Word) (m : Memory) →
    readMem m p ≡ just 0 →
    readMem m (p +ℕ 8) ≡ just (encode a) →
    p ≡ encode {A + B} (inj₁ a)

  -- ELIMINABLE: run-inr-star-s produces InrAtS directly from memory writes
  encode-inr-construct : ∀ {A B} (b : ⟦ B ⟧) (p : Word) (m : Memory) →
    readMem m p ≡ just 1 →
    readMem m (p +ℕ 8) ≡ just (encode b) →
    p ≡ encode {A + B} (inj₂ b)

  -- ELIMINABLE: pair-stores-create-validity produces PairAtS from memory writes
  -- Encoding construction for pairs:
  -- If memory at p has [encode a, encode b], then p is encode (a, b)
  encode-pair-construct : ∀ {A B} (a : ⟦ A ⟧) (b : ⟦ B ⟧) (p : Word) (m : Memory) →
    readMem m p ≡ just (encode a) →
    readMem m (p +ℕ 8) ≡ just (encode b) →
    p ≡ encode {A * B} (a , b)

  -- ELIMINABLE: Need ClosureAtS validity predicate (similar to PairAtS)
  -- Encoding preserves closure structure
  -- A closure is encoded as a pointer to [env-addr, code-ptr]
  -- env-addr is part of the semantic Closure; code-ptr is a compilation artifact
  encode-closure-env : ∀ {A B} (closure : ⟦ A ⇒ B ⟧) (m : Memory) →
    readMem m (encode {A ⇒ B} closure) ≡ just (Closure.env-addr closure)

  -- NOTE: encode-closure-code-ptr removed - code-ptr is not in semantic Closure
  -- Runtime code-ptr is tracked via ClosureAtS and ClosureWellFormed

  -- ELIMINABLE: ClosureAtS produces closures directly from memory writes
  -- Encoding construction for closures (functions):
  -- A closure representing curry f applied to a is encoded as a pointer to [env, code]
  -- where env = encode a
  -- NOTE: With explicit Closure record, this may become derivable from env-addr field
  -- NOTE: {q} parameter added since curry is now quantity-polymorphic
  encode-closure-construct : ∀ {A B C q} (f : IR (A * B) C) (a : ⟦ A ⟧) (p : Word) (m : Memory) →
    readMem m p ≡ just (encode a) →
    -- (code pointer is abstract - we just need env to be correct)
    p ≡ encode {B ⇒[ q ] C} (eval (curry {q = q} f Heap) a)

------------------------------------------------------------------------
-- Postulate P3: QTT Quantity Erasure (Coercion)
------------------------------------------------------------------------
--
-- STATUS: SHOULD BE ELIMINATED alongside coerceIRArrow
--
-- Expressions can be coerced between contexts that differ only in
-- quantity annotations (0/1/ω). This reflects the QTT erasure property:
-- quantities are compile-time annotations that don't affect runtime
-- semantics.
--
-- NEEDED BY: Once.TypeCheck.Elaborate (weakening and context manipulation)
--
-- JUSTIFICATION:
--   Quantitative Type Theory (QTT) is designed with an erasure property:
--   quantities track compile-time resource usage but are erased before
--   execution. Two expressions that differ only in their context's
--   quantity annotations have identical runtime behavior.
--
--   Example: λx.x has the same semantics whether x is:
--     - Linear (used exactly once)
--     - Unrestricted (used 0+ times)
--     - Erased (compile-time only)
--
--   The actual usage checking happens during type checking.
--   This postulate allows infrastructure code to adjust quantities
--   without affecting semantics.
--
--   DESIGN NOTE (Inference-Based QTT):
--   Once uses QTT for optimization inference rather than enforcement.
--   The compiler infers actual usage patterns and optimizes accordingly,
--   without requiring programmers to write explicit linearity annotations.
--   This postulate enables that flexibility: we can adjust quantity
--   annotations during analysis without changing program semantics.
--
-- IMPACT:
--   If quantity erasure were false, then QTT would affect runtime
--   semantics, which violates the design. Programs would behave
--   differently based on linearity annotations, breaking parametricity.
--
-- RUNTIME EFFECT: None (quantities are erased)
--
-- ELIMINATION STRATEGY:
--   This postulate is eliminated together with coerceIRArrow (see P1c above).
--   When curry/apply become quantity-polymorphic, the Surface.Syntax
--   context quantities flow through naturally:
--
--   1. Surface.Syntax Ctx tracks quantities: Γ , A ^ q
--   2. elaborate preserves quantities via polymorphic curry
--   3. No coercion needed between contexts with different quantities
--
--   The key insight: quantities should be parameters that flow through,
--   not constraints that require coercion. Once IR and Surface.Syntax
--   are quantity-polymorphic, this postulate becomes unnecessary.
--
--   BACKEND IMPACT: None. This is purely a Surface/TypeCheck concern.
--   Backend proofs work with IR which already erases quantities in
--   its semantics (⟦ A ⇒[q] B ⟧ = Closure A B for all q).
--
------------------------------------------------------------------------

open import Once.Surface.Syntax as Surface using ()
  renaming (Ctx to SCtx; Expr to SExpr; _,_^_ to _S,_^_)

postulate
  coerceQuantity : ∀ {n} {Γ : SCtx n} {A B : Type} {q q' : Quantity}
                 → SExpr (_S,_^_ Γ A q) B → SExpr (_S,_^_ Γ A q') B

------------------------------------------------------------------------
-- Postulate P4: Heap-Stack Separation
------------------------------------------------------------------------
--
-- Stack addresses (derived from rsp) don't overlap with heap addresses
-- (produced by encode). This is a fundamental property of the memory layout.
--
-- NEEDED BY: X86 apply proof (push r15 before reading from heap)
--
-- JUSTIFICATION:
--   The runtime initializes memory with separate regions:
--   - Stack: grows down from stackBase
--   - Heap: grows up from heapStart
--   - stackBase < heapStart (they don't overlap)
--
--   The encode function allocates on the heap (returns addresses ≥ heapStart).
--   Stack operations use addresses near rsp (≤ stackBase).
--   Therefore stack addresses ≠ heap addresses.
--
-- IMPACT:
--   If heap and stack overlapped, stack operations could corrupt heap data.
--   This would cause silent data corruption in generated code.
--
-- ELIMINATION:
--   Could be proven by:
--   1. Adding HeapAddr/StackAddr predicates to track address regions
--   2. Threading these through all memory operations
--   3. Proving encode produces HeapAddr, rsp operations use StackAddr
--   This is invasive but achievable for whole-program proofs.
--
-- RUNTIME EFFECT: None (proof-only)
--
------------------------------------------------------------------------

-- D041 ELIMINATED: heap-stack-disjoint postulate removed
-- Now derived in StackInstantiation.heap-stack-disjoint-via-region from:
--   - MemoryRegions.encode-in-heap
--   - MemoryRegions.heap-offset
--   - MemoryRegions.regions-disjoint

------------------------------------------------------------------------
-- Postulate P5: x86-64 Execution Helpers (in Once.CCC.Target.X86.Correct)
------------------------------------------------------------------------
--
-- The x86-64 backend has additional postulates for instruction execution:
--
--   run-single-mov          : Single mov reg,reg instruction
--   run-single-mov-imm      : Single mov reg,imm instruction
--   run-single-mov-mem-base : Single mov reg,[reg] instruction
--   run-single-mov-mem-disp : Single mov reg,[reg+disp] instruction
--   run-inl-seq             : Left injection sequence (tag=0)
--   run-inr-seq             : Right injection sequence (tag=1)
--   run-seq-compose         : Sequential composition of programs
--   run-generator           : General generator correctness
--   run-case-inl            : Case dispatch (left branch)
--   run-case-inr            : Case dispatch (right branch)
--   run-pair-seq            : Pair construction sequence
--   run-curry-seq           : Closure creation sequence
--   run-apply-seq           : Closure application sequence
--
-- These are kept in Once.CCC.Target.X86.Correct because they depend on
-- x86-specific types (State, Program, Instr, etc.).
--
-- NEEDED BY: Individual compile-*-correct proofs
--
-- JUSTIFICATION:
--   Each postulate captures the expected behavior of an instruction
--   sequence. They can be proven by:
--   1. Proving lemmas about fetch, step, and exec
--   2. Stepping through each instruction
--   3. Tracking register and memory state changes
--
-- IMPACT:
--   If any postulate is wrong, the corresponding correctness proof
--   would be invalid. However, the structure is mechanically derivable
--   from the instruction definitions.
--
-- RUNTIME EFFECT: None (proof-only)
--
------------------------------------------------------------------------
