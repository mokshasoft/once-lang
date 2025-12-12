------------------------------------------------------------------------
-- Once.Backend.X86.Correct
--
-- Correctness proofs for x86-64 code generation.
--
-- Main theorem:
--   codegen-x86-correct : ∀ (ir : IR A B) (x : ⟦A⟧) →
--     exec-x86 (compile-x86 ir) (encode-x86 x) ≡ encode-x86 (eval ir x)
--
-- This module proves that the code generator preserves semantics:
-- executing the generated x86-64 code on an encoded input produces
-- the same result as encoding the semantic evaluation.
------------------------------------------------------------------------

module Once.Backend.X86.Correct where

open import Once.Type
open import Once.IR
open import Once.Semantics

open import Once.Backend.X86.Syntax
open import Once.Backend.X86.Semantics
open Once.Backend.X86.Semantics.State
open import Once.Backend.X86.CodeGen

open import Data.Nat using (ℕ; zero; suc) renaming (_+_ to _+ℕ_)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂) renaming ([_,_] to case-sum)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)

------------------------------------------------------------------------
-- Value Encoding
------------------------------------------------------------------------

-- | Encode semantic values as x86-64 words
--
-- The encoding maps Agda values to machine words:
--   Unit    → 0
--   A * B   → address of [encode A, encode B]
--   A + B   → address of [tag, encode (A or B)]
--   A ⇒ B   → address of closure [env, code]
--
-- For simplicity, we model this abstractly with postulates.
-- A full implementation would need to model heap allocation.

postulate
  -- Encoding of values to words (address or immediate)
  encode : ∀ {A} → ⟦ A ⟧ → Word

  -- Encoding Unit produces 0
  encode-unit : encode {Unit} tt ≡ 0

  -- Encoding preserves pair structure
  -- encode (a , b) is an address pointing to [encode a, encode b]
  encode-pair-fst : ∀ {A B} (a : ⟦ A ⟧) (b : ⟦ B ⟧) (m : Memory) →
    readMem m (encode (a , b)) ≡ just (encode a)

  encode-pair-snd : ∀ {A B} (a : ⟦ A ⟧) (b : ⟦ B ⟧) (m : Memory) →
    readMem m ((encode (a , b)) +ℕ 8) ≡ just (encode b)

  -- Encoding preserves sum structure
  -- encode (inj₁ a) is address pointing to [0, encode a]
  -- encode (inj₂ b) is address pointing to [1, encode b]
  encode-inl-tag : ∀ {A B} (a : ⟦ A ⟧) (m : Memory) →
    readMem m (encode {A + B} (inj₁ a)) ≡ just 0

  encode-inl-val : ∀ {A B} (a : ⟦ A ⟧) (m : Memory) →
    readMem m ((encode {A + B} (inj₁ a)) +ℕ 8) ≡ just (encode a)

  encode-inr-tag : ∀ {A B} (b : ⟦ B ⟧) (m : Memory) →
    readMem m (encode {A + B} (inj₂ b)) ≡ just 1

  encode-inr-val : ∀ {A B} (b : ⟦ B ⟧) (m : Memory) →
    readMem m ((encode {A + B} (inj₂ b)) +ℕ 8) ≡ just (encode b)

------------------------------------------------------------------------
-- Initial State Setup
------------------------------------------------------------------------

-- | Create initial state with input in rdi
--
-- Sets up machine state ready to execute generated code:
--   - rdi contains encoded input
--   - Memory contains encoded heap objects
--   - Other registers initialized to 0
--   - Stack pointer set appropriately

postulate
  -- Initial state with input value
  initWithInput : ∀ {A} → ⟦ A ⟧ → State

  -- The input is placed in rdi
  initWithInput-rdi : ∀ {A} (x : ⟦ A ⟧) →
    readReg (regs (initWithInput x)) rdi ≡ encode x

  -- Memory contains encoded representation
  -- (Further properties about memory would specify the heap layout)

------------------------------------------------------------------------
-- Correctness Theorems
------------------------------------------------------------------------

-- Note: Full proofs require:
--   1. Precise modeling of stack allocation
--   2. Relating exec/run to step-by-step execution
--   3. Careful handling of intermediate states
--
-- The proofs below are structured but incomplete (postulated).
-- A complete formalization would fill in these proofs.

-- | Main correctness theorem
--
-- Executing compiled code on encoded input produces encoded output.

postulate
  codegen-x86-correct : ∀ {A B} (ir : IR A B) (x : ⟦ A ⟧) →
    ∃[ s ] (run (compile-x86 ir) (initWithInput x) ≡ just s
          × readReg (regs s) rax ≡ encode (eval ir x))

------------------------------------------------------------------------
-- Per-Generator Correctness (Sub-theorems)
------------------------------------------------------------------------

-- These would be proven individually and composed into the main theorem.

postulate
  -- | id: output equals input
  compile-id-correct : ∀ {A} (x : ⟦ A ⟧) →
    ∃[ s ] (run (compile-x86 {A} {A} id) (initWithInput x) ≡ just s
          × readReg (regs s) rax ≡ encode x)

  -- | fst: extracts first component
  compile-fst-correct : ∀ {A B} (a : ⟦ A ⟧) (b : ⟦ B ⟧) →
    ∃[ s ] (run (compile-x86 {A * B} {A} fst) (initWithInput (a , b)) ≡ just s
          × readReg (regs s) rax ≡ encode a)

  -- | snd: extracts second component
  compile-snd-correct : ∀ {A B} (a : ⟦ A ⟧) (b : ⟦ B ⟧) →
    ∃[ s ] (run (compile-x86 {A * B} {B} snd) (initWithInput (a , b)) ≡ just s
          × readReg (regs s) rax ≡ encode b)

  -- | pair: constructs pair from two computations
  compile-pair-correct : ∀ {A B C} (f : IR C A) (g : IR C B) (x : ⟦ C ⟧) →
    ∃[ s ] (run (compile-x86 ⟨ f , g ⟩) (initWithInput x) ≡ just s
          × readReg (regs s) rax ≡ encode (eval f x , eval g x))

  -- | inl: creates left injection
  compile-inl-correct : ∀ {A B} (a : ⟦ A ⟧) →
    ∃[ s ] (run (compile-x86 {A} {A + B} inl) (initWithInput a) ≡ just s
          × readReg (regs s) rax ≡ encode {A + B} (inj₁ a))

  -- | inr: creates right injection
  compile-inr-correct : ∀ {A B} (b : ⟦ B ⟧) →
    ∃[ s ] (run (compile-x86 {B} {A + B} inr) (initWithInput b) ≡ just s
          × readReg (regs s) rax ≡ encode {A + B} (inj₂ b))

  -- | case: branches on sum tag
  compile-case-correct : ∀ {A B C} (f : IR A C) (g : IR B C) (x : ⟦ A ⟧ ⊎ ⟦ B ⟧) →
    ∃[ s ] (run (compile-x86 {A + B} {C} [ f , g ]) (initWithInput x) ≡ just s
          × readReg (regs s) rax ≡ encode {C} (case-sum (eval f) (eval g) x))

  -- | terminal: produces unit
  compile-terminal-correct : ∀ {A} (x : ⟦ A ⟧) →
    ∃[ s ] (run (compile-x86 {A} {Unit} terminal) (initWithInput x) ≡ just s
          × readReg (regs s) rax ≡ 0)

  -- | initial: unreachable (Void has no values)
  -- No theorem needed: there are no inputs of type Void

  -- | compose: sequential composition
  compile-compose-correct : ∀ {A B C} (g : IR B C) (f : IR A B) (x : ⟦ A ⟧) →
    ∃[ s ] (run (compile-x86 (g ∘ f)) (initWithInput x) ≡ just s
          × readReg (regs s) rax ≡ encode (eval g (eval f x)))

  -- | fold: identity at runtime
  compile-fold-correct : ∀ {F} (x : ⟦ F ⟧) →
    ∃[ s ] (run (compile-x86 {F} {Fix F} fold) (initWithInput x) ≡ just s
          × readReg (regs s) rax ≡ encode x)

  -- | unfold: identity at runtime
  compile-unfold-correct : ∀ {F} (x : ⟦ Fix F ⟧) →
    ∃[ s ] (run (compile-x86 {Fix F} {F} unfold) (initWithInput x) ≡ just s
          × readReg (regs s) rax ≡ encode (⟦Fix⟧.unwrap x))

------------------------------------------------------------------------
-- Closure Correctness (Future Work)
------------------------------------------------------------------------

-- curry and apply require a more sophisticated treatment:
--   - Closure allocation and representation
--   - Thunk generation for curry
--   - Indirect calls for apply
--
-- These are marked as future work in the current formalization.

-- | curry: creates closure (SIMPLIFIED/INCOMPLETE)
-- Full proof requires modeling closure creation

-- | apply: calls closure (SIMPLIFIED/INCOMPLETE)
-- Full proof requires modeling indirect calls

------------------------------------------------------------------------
-- Notes on Postulates
------------------------------------------------------------------------

-- The postulates in this module fall into two categories:
--
-- 1. ENCODING AXIOMS (encode-*, initWithInput-*)
--    These specify the relationship between semantic values and
--    machine representation. A full formalization would:
--    - Model heap explicitly
--    - Prove these as lemmas rather than assume them
--
-- 2. CORRECTNESS THEOREMS (compile-*-correct)
--    These are the actual proof obligations. Each requires:
--    - Stepping through the generated code
--    - Tracking state changes
--    - Showing final state matches expected
--
-- The structure shows WHAT needs to be proven. The proofs themselves
-- require significant work to complete.
--
-- See docs/compiler/formal-verification-plan.md for estimated effort.
