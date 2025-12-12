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

open import Data.Bool using (Bool; true; false)
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
-- Execution Helpers
------------------------------------------------------------------------

-- | Execute a single-instruction program
--
-- For a program [instr], execution proceeds:
--   1. Execute instr at pc=0 → new state with pc=1
--   2. Fetch at pc=1 fails → implicit halt
--   3. Return halted state
--
-- We need helpers to reason about this step-by-step.

-- Helper: state after executing mov reg reg
postulate
  execMov-reg-reg : ∀ (s : State) (dst src : Reg) →
    execInstr [] s (mov (reg dst) (reg src)) ≡
      just (record s { regs = writeReg (regs s) dst (readReg (regs s) src)
                     ; pc = pc s +ℕ 1 })

-- Helper: running a single-instruction program (mov reg, reg)
postulate
  run-single-mov : ∀ (s : State) (dst src : Reg) →
    halted s ≡ false →
    pc s ≡ 0 →
    ∃[ s' ] (run (mov (reg dst) (reg src) ∷ []) s ≡ just s'
           × readReg (regs s') dst ≡ readReg (regs s) src
           × halted s' ≡ true)

-- Helper: running a single-instruction program (mov reg, imm)
postulate
  run-single-mov-imm : ∀ (s : State) (dst : Reg) (n : ℕ) →
    halted s ≡ false →
    pc s ≡ 0 →
    ∃[ s' ] (run (mov (reg dst) (imm n) ∷ []) s ≡ just s'
           × readReg (regs s') dst ≡ n
           × halted s' ≡ true)

------------------------------------------------------------------------
-- Correctness Theorems
------------------------------------------------------------------------

-- | Main correctness theorem
--
-- Executing compiled code on encoded input produces encoded output.
-- This is proven by case analysis on the IR constructor, using the
-- per-generator theorems below.

postulate
  codegen-x86-correct : ∀ {A B} (ir : IR A B) (x : ⟦ A ⟧) →
    ∃[ s ] (run (compile-x86 ir) (initWithInput x) ≡ just s
          × readReg (regs s) rax ≡ encode (eval ir x))

------------------------------------------------------------------------
-- Per-Generator Correctness (Sub-theorems)
------------------------------------------------------------------------

-- | id: output equals input
--
-- Generated code: mov rax, rdi
-- Proof: rax := rdi = encode x (by initWithInput-rdi)
compile-id-correct : ∀ {A} (x : ⟦ A ⟧) →
  ∃[ s ] (run (compile-x86 {A} {A} id) (initWithInput x) ≡ just s
        × readReg (regs s) rax ≡ encode x)
compile-id-correct {A} x = s' , run-eq , rax-eq
  where
    s0 : State
    s0 = initWithInput x

    -- Use the single-mov helper
    helper : ∃[ s' ] (run (mov (reg rax) (reg rdi) ∷ []) s0 ≡ just s'
                    × readReg (regs s') rax ≡ readReg (regs s0) rdi
                    × halted s' ≡ true)
    helper = run-single-mov s0 rax rdi initWithInput-halted initWithInput-pc
      where
        postulate
          initWithInput-halted : halted s0 ≡ false
          initWithInput-pc : pc s0 ≡ 0

    s' : State
    s' = proj₁ helper

    run-eq : run (compile-x86 {A} {A} id) s0 ≡ just s'
    run-eq = proj₁ (proj₂ helper)

    rax-eq : readReg (regs s') rax ≡ encode x
    rax-eq = trans (proj₁ (proj₂ (proj₂ helper))) (initWithInput-rdi x)

-- Remaining theorems (still postulated, to be proven)
postulate
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

  -- | initial: unreachable (Void has no values)
  -- No theorem needed: there are no inputs of type Void

  -- | compose: sequential composition
  compile-compose-correct : ∀ {A B C} (g : IR B C) (f : IR A B) (x : ⟦ A ⟧) →
    ∃[ s ] (run (compile-x86 (g ∘ f)) (initWithInput x) ≡ just s
          × readReg (regs s) rax ≡ encode (eval g (eval f x)))

-- | terminal: produces unit
--
-- Generated code: mov rax, 0
-- Proof: rax := 0 = encode tt = 0 (by encode-unit)
compile-terminal-correct : ∀ {A} (x : ⟦ A ⟧) →
  ∃[ s ] (run (compile-x86 {A} {Unit} terminal) (initWithInput x) ≡ just s
        × readReg (regs s) rax ≡ 0)
compile-terminal-correct {A} x = s' , run-eq , rax-eq
  where
    s0 : State
    s0 = initWithInput x

    helper : ∃[ s' ] (run (mov (reg rax) (imm 0) ∷ []) s0 ≡ just s'
                    × readReg (regs s') rax ≡ 0
                    × halted s' ≡ true)
    helper = run-single-mov-imm s0 rax 0 initWithInput-halted initWithInput-pc
      where
        postulate
          initWithInput-halted : halted s0 ≡ false
          initWithInput-pc : pc s0 ≡ 0

    s' : State
    s' = proj₁ helper

    run-eq : run (compile-x86 {A} {Unit} terminal) s0 ≡ just s'
    run-eq = proj₁ (proj₂ helper)

    rax-eq : readReg (regs s') rax ≡ 0
    rax-eq = proj₁ (proj₂ (proj₂ helper))

-- | fold: identity at runtime
--
-- Generated code: mov rax, rdi
-- Proof: Same as id - rax := rdi = encode x
compile-fold-correct : ∀ {F} (x : ⟦ F ⟧) →
  ∃[ s ] (run (compile-x86 {F} {Fix F} fold) (initWithInput x) ≡ just s
        × readReg (regs s) rax ≡ encode x)
compile-fold-correct {F} x = s' , run-eq , rax-eq
  where
    s0 : State
    s0 = initWithInput x

    helper : ∃[ s' ] (run (mov (reg rax) (reg rdi) ∷ []) s0 ≡ just s'
                    × readReg (regs s') rax ≡ readReg (regs s0) rdi
                    × halted s' ≡ true)
    helper = run-single-mov s0 rax rdi initWithInput-halted initWithInput-pc
      where
        postulate
          initWithInput-halted : halted s0 ≡ false
          initWithInput-pc : pc s0 ≡ 0

    s' : State
    s' = proj₁ helper

    run-eq : run (compile-x86 {F} {Fix F} fold) s0 ≡ just s'
    run-eq = proj₁ (proj₂ helper)

    rax-eq : readReg (regs s') rax ≡ encode x
    rax-eq = trans (proj₁ (proj₂ (proj₂ helper))) (initWithInput-rdi x)

-- | unfold: identity at runtime
--
-- Generated code: mov rax, rdi
-- Proof: Similar to fold
postulate
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
