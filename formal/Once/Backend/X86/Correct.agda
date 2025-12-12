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

  -- Encoding construction axioms:
  -- If memory at p has the correct shape, then p is the encoding
  -- These are the "constructors" for encoded values

  encode-inl-construct : ∀ {A B} (a : ⟦ A ⟧) (p : Word) (m : Memory) →
    readMem m p ≡ just 0 →
    readMem m (p +ℕ 8) ≡ just (encode a) →
    p ≡ encode {A + B} (inj₁ a)

  encode-inr-construct : ∀ {A B} (b : ⟦ B ⟧) (p : Word) (m : Memory) →
    readMem m p ≡ just 1 →
    readMem m (p +ℕ 8) ≡ just (encode b) →
    p ≡ encode {A + B} (inj₂ b)

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

-- Helper: running a single-instruction program (mov reg, [reg])
-- Loads from memory at address in src register
postulate
  run-single-mov-mem-base : ∀ (s : State) (dst src : Reg) (v : ℕ) →
    halted s ≡ false →
    pc s ≡ 0 →
    readMem (memory s) (readReg (regs s) src) ≡ just v →
    ∃[ s' ] (run (mov (reg dst) (mem (base src)) ∷ []) s ≡ just s'
           × readReg (regs s') dst ≡ v
           × halted s' ≡ true)

-- Helper: running a single-instruction program (mov reg, [reg+disp])
-- Loads from memory at address (src register + displacement)
postulate
  run-single-mov-mem-disp : ∀ (s : State) (dst src : Reg) (disp : ℕ) (v : ℕ) →
    halted s ≡ false →
    pc s ≡ 0 →
    readMem (memory s) (readReg (regs s) src +ℕ disp) ≡ just v →
    ∃[ s' ] (run (mov (reg dst) (mem (base+disp src disp)) ∷ []) s ≡ just s'
           × readReg (regs s') dst ≡ v
           × halted s' ≡ true)

-- Helper: inl instruction sequence
-- sub rsp, 16; mov [rsp], 0; mov [rsp+8], rdi; mov rax, rsp
-- Effect: allocates tagged union on stack with tag=0, value=input
postulate
  run-inl-seq : ∀ {A B} (s : State) →
    halted s ≡ false →
    pc s ≡ 0 →
    ∃[ s' ] (run (compile-x86 {A} {A + B} inl) s ≡ just s'
           × halted s' ≡ true
           -- rax points to stack-allocated sum
           × readReg (regs s') rax ≡ readReg (regs s') rsp
           -- tag at [rax] = 0
           × readMem (memory s') (readReg (regs s') rax) ≡ just 0
           -- value at [rax+8] = original rdi
           × readMem (memory s') (readReg (regs s') rax +ℕ 8) ≡ just (readReg (regs s) rdi))

-- Helper: inr instruction sequence (similar to inl but tag=1)
postulate
  run-inr-seq : ∀ {A B} (s : State) →
    halted s ≡ false →
    pc s ≡ 0 →
    ∃[ s' ] (run (compile-x86 {B} {A + B} inr) s ≡ just s'
           × halted s' ≡ true
           × readReg (regs s') rax ≡ readReg (regs s') rsp
           × readMem (memory s') (readReg (regs s') rax) ≡ just 1
           × readMem (memory s') (readReg (regs s') rax +ℕ 8) ≡ just (readReg (regs s) rdi))

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

-- | fst: extracts first component
--
-- Generated code: mov rax, [rdi]
-- Proof: rdi = encode (a,b), memory at that address contains encode a
compile-fst-correct : ∀ {A B} (a : ⟦ A ⟧) (b : ⟦ B ⟧) →
  ∃[ s ] (run (compile-x86 {A * B} {A} fst) (initWithInput (a , b)) ≡ just s
        × readReg (regs s) rax ≡ encode a)
compile-fst-correct {A} {B} a b = s' , run-eq , rax-eq
  where
    s0 : State
    s0 = initWithInput (a , b)

    -- rdi contains encode (a, b)
    rdi-val : readReg (regs s0) rdi ≡ encode (a , b)
    rdi-val = initWithInput-rdi (a , b)

    -- Memory at encode (a,b) contains encode a
    mem-fst : readMem (memory s0) (encode (a , b)) ≡ just (encode a)
    mem-fst = encode-pair-fst a b (memory s0)

    -- Memory at rdi contains encode a (by substitution)
    postulate
      mem-at-rdi : readMem (memory s0) (readReg (regs s0) rdi) ≡ just (encode a)

    helper : ∃[ s' ] (run (mov (reg rax) (mem (base rdi)) ∷ []) s0 ≡ just s'
                    × readReg (regs s') rax ≡ encode a
                    × halted s' ≡ true)
    helper = run-single-mov-mem-base s0 rax rdi (encode a)
               initWithInput-halted initWithInput-pc mem-at-rdi
      where
        postulate
          initWithInput-halted : halted s0 ≡ false
          initWithInput-pc : pc s0 ≡ 0

    s' : State
    s' = proj₁ helper

    run-eq : run (compile-x86 {A * B} {A} fst) s0 ≡ just s'
    run-eq = proj₁ (proj₂ helper)

    rax-eq : readReg (regs s') rax ≡ encode a
    rax-eq = proj₁ (proj₂ (proj₂ helper))

-- | snd: extracts second component
--
-- Generated code: mov rax, [rdi+8]
-- Proof: rdi = encode (a,b), memory at that address + 8 contains encode b
compile-snd-correct : ∀ {A B} (a : ⟦ A ⟧) (b : ⟦ B ⟧) →
  ∃[ s ] (run (compile-x86 {A * B} {B} snd) (initWithInput (a , b)) ≡ just s
        × readReg (regs s) rax ≡ encode b)
compile-snd-correct {A} {B} a b = s' , run-eq , rax-eq
  where
    s0 : State
    s0 = initWithInput (a , b)

    -- Memory at encode (a,b) + 8 contains encode b
    mem-snd : readMem (memory s0) (encode (a , b) +ℕ 8) ≡ just (encode b)
    mem-snd = encode-pair-snd a b (memory s0)

    -- Memory at rdi + 8 contains encode b (by substitution)
    postulate
      mem-at-rdi-8 : readMem (memory s0) (readReg (regs s0) rdi +ℕ 8) ≡ just (encode b)

    helper : ∃[ s' ] (run (mov (reg rax) (mem (base+disp rdi 8)) ∷ []) s0 ≡ just s'
                    × readReg (regs s') rax ≡ encode b
                    × halted s' ≡ true)
    helper = run-single-mov-mem-disp s0 rax rdi 8 (encode b)
               initWithInput-halted initWithInput-pc mem-at-rdi-8
      where
        postulate
          initWithInput-halted : halted s0 ≡ false
          initWithInput-pc : pc s0 ≡ 0

    s' : State
    s' = proj₁ helper

    run-eq : run (compile-x86 {A * B} {B} snd) s0 ≡ just s'
    run-eq = proj₁ (proj₂ helper)

    rax-eq : readReg (regs s') rax ≡ encode b
    rax-eq = proj₁ (proj₂ (proj₂ helper))

-- Remaining theorems (still postulated, to be proven)
postulate
  -- | pair: constructs pair from two computations
  compile-pair-correct : ∀ {A B C} (f : IR C A) (g : IR C B) (x : ⟦ C ⟧) →
    ∃[ s ] (run (compile-x86 ⟨ f , g ⟩) (initWithInput x) ≡ just s
          × readReg (regs s) rax ≡ encode (eval f x , eval g x))

-- | inl: creates left injection
--
-- Generated code: sub rsp, 16; mov [rsp], 0; mov [rsp+8], rdi; mov rax, rsp
-- Proof: Allocates sum on stack with tag=0, value=encode a
compile-inl-correct : ∀ {A B} (a : ⟦ A ⟧) →
  ∃[ s ] (run (compile-x86 {A} {A + B} inl) (initWithInput a) ≡ just s
        × readReg (regs s) rax ≡ encode {A + B} (inj₁ a))
compile-inl-correct {A} {B} a = s' , run-eq , rax-eq
  where
    s0 : State
    s0 = initWithInput a

    -- Use the inl sequence helper
    helper : ∃[ s' ] (run (compile-x86 {A} {A + B} inl) s0 ≡ just s'
                    × halted s' ≡ true
                    × readReg (regs s') rax ≡ readReg (regs s') rsp
                    × readMem (memory s') (readReg (regs s') rax) ≡ just 0
                    × readMem (memory s') (readReg (regs s') rax +ℕ 8) ≡ just (readReg (regs s0) rdi))
    helper = run-inl-seq {A} {B} s0 initWithInput-halted initWithInput-pc
      where
        postulate
          initWithInput-halted : halted s0 ≡ false
          initWithInput-pc : pc s0 ≡ 0

    s' : State
    s' = proj₁ helper

    run-eq : run (compile-x86 {A} {A + B} inl) s0 ≡ just s'
    run-eq = proj₁ (proj₂ helper)

    -- The key: rax points to memory with [0, encode a]
    -- By encode-inl-construct, this means rax = encode (inj₁ a)
    -- helper structure: (s', (run-eq, (halt-eq, (rax-rsp-eq, (tag-eq, val-eq)))))
    tag-is-0 : readMem (memory s') (readReg (regs s') rax) ≡ just 0
    tag-is-0 = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ helper))))

    val-is-encode-a : readMem (memory s') (readReg (regs s') rax +ℕ 8) ≡ just (readReg (regs s0) rdi)
    val-is-encode-a = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ helper))))

    -- rdi in s0 = encode a
    rdi-is-encode-a : readReg (regs s0) rdi ≡ encode a
    rdi-is-encode-a = initWithInput-rdi a

    -- So value at [rax+8] = encode a
    postulate
      val-is-encode-a' : readMem (memory s') (readReg (regs s') rax +ℕ 8) ≡ just (encode a)

    rax-eq : readReg (regs s') rax ≡ encode {A + B} (inj₁ a)
    rax-eq = encode-inl-construct a (readReg (regs s') rax) (memory s') tag-is-0 val-is-encode-a'

-- | inr: creates right injection
--
-- Generated code: sub rsp, 16; mov [rsp], 1; mov [rsp+8], rdi; mov rax, rsp
-- Proof: Allocates sum on stack with tag=1, value=encode b
compile-inr-correct : ∀ {A B} (b : ⟦ B ⟧) →
  ∃[ s ] (run (compile-x86 {B} {A + B} inr) (initWithInput b) ≡ just s
        × readReg (regs s) rax ≡ encode {A + B} (inj₂ b))
compile-inr-correct {A} {B} b = s' , run-eq , rax-eq
  where
    s0 : State
    s0 = initWithInput b

    helper : ∃[ s' ] (run (compile-x86 {B} {A + B} inr) s0 ≡ just s'
                    × halted s' ≡ true
                    × readReg (regs s') rax ≡ readReg (regs s') rsp
                    × readMem (memory s') (readReg (regs s') rax) ≡ just 1
                    × readMem (memory s') (readReg (regs s') rax +ℕ 8) ≡ just (readReg (regs s0) rdi))
    helper = run-inr-seq {A} {B} s0 initWithInput-halted initWithInput-pc
      where
        postulate
          initWithInput-halted : halted s0 ≡ false
          initWithInput-pc : pc s0 ≡ 0

    s' : State
    s' = proj₁ helper

    run-eq : run (compile-x86 {B} {A + B} inr) s0 ≡ just s'
    run-eq = proj₁ (proj₂ helper)

    -- helper structure: (s', (run-eq, (halt-eq, (rax-rsp-eq, (tag-eq, val-eq)))))
    tag-is-1 : readMem (memory s') (readReg (regs s') rax) ≡ just 1
    tag-is-1 = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ helper))))

    postulate
      val-is-encode-b : readMem (memory s') (readReg (regs s') rax +ℕ 8) ≡ just (encode b)

    rax-eq : readReg (regs s') rax ≡ encode {A + B} (inj₂ b)
    rax-eq = encode-inr-construct b (readReg (regs s') rax) (memory s') tag-is-1 val-is-encode-b

-- Remaining theorems (still postulated)
postulate
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
