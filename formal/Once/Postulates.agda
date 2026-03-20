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

open import Relation.Binary.PropositionalEquality using (_≡_)

open import Once.Type
open import Once.Semantics.IR

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
-- Postulate P1b: Closure Equality (ELIMINATED)
------------------------------------------------------------------------
--
-- STATUS: ELIMINATED
--
-- This postulate was eliminated by switching to plain functions for
-- function semantics. With plain Agda functions instead of Closure
-- records, function equality follows from function extensionality (P1).
--
-- Previously needed because Closure records contained env-addr which
-- made equality non-trivial. Now ⟦ A ⇒ B ⟧ = ⟦ A ⟧ → ⟦ B ⟧ (plain function).
--
------------------------------------------------------------------------

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
-- Postulate P2: QTT Quantity Erasure (Coercion)
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

