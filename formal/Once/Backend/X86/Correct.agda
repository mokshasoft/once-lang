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
open import Once.Semantics hiding (code-ptr; env-addr; semantics)  -- Hide clashing names

open import Once.Backend.X86.Syntax
open import Once.Backend.X86.Semantics
open Once.Backend.X86.Semantics.State
open Once.Backend.X86.Semantics.Flags
open import Once.Backend.X86.CodeGen

-- Import Star relation for compositional proofs
open import Once.Backend.X86.Correct.Star
  using (Star; refl*; step*; star-trans; star-single;
         _◅◅_; ⟨_,_⟩◅_; star-step2; star-step3; star-step4;
         exec-to-star; exec-until-pc-to-star;
         StarResult; star-exec; not-halted; rax-correct;
         exec-to-star-result; compose-star-results)

-- Import common fetch lemmas (polymorphic, work with any instruction type)
open import Once.Backend.Common.Fetch
  using ( fetch-0; fetch-1; fetch-2; fetch-3
        ; fetch-1-single; fetch-4-of-4
        ; fetch-append-left; fetch-append-right
        )

-- Import common memory helper lemmas
open import Once.Backend.Common.Memory
  using (≡ᵇ-refl; n≢n+suc)

-- Import common program manipulation lemmas
open import Once.Backend.Common.ProgramLemmas
  using ( prog-shift-1; prog-shift-2; prog-shift-3
        ; len-shift-1; len-shift-2; len-shift-3
        ; compose-prog-eq; compose-transfer-eq; compose-g-eq
        )

-- Import common exec N-steps lemmas (parameterized module)
-- Instantiated below after defining the base lemmas exec-on-non-halted-step and exec-on-halted-step

-- Import StackPointer for caller frame tracking (D041)
open import Once.Backend.Common.MemoryRegions using (StackPointer)

-- Import encoding axioms from central postulates module
open import Once.Postulates public
  using ( encode
        ; encode-unit
        ; encode-pair-fst
        ; encode-pair-snd
        ; encode-inl-tag
        ; encode-inl-val
        ; encode-inr-tag
        ; encode-inr-val
        ; encode-inl-construct
        ; encode-inr-construct
        ; encode-fix-unwrap
        ; encode-fix-wrap
        ; encode-arr-identity
        ; encode-pair-construct
        ; encode-closure-construct
        )

-- Import extracted correctness proof modules
-- Level 0: Independent modules
open import Once.Backend.X86.Correct.RegisterLemmas public
open import Once.Backend.X86.Correct.FetchStep public
open import Once.Backend.X86.Correct.CompileLength public hiding (length-++)
open import Once.Backend.X86.Correct.InitState public
  using (initWithInput; initWithInput-rdi; initWithInput-halted; initWithInput-pc; stackBase)
open import Once.Backend.X86.Correct.InstrExec public

-- Level 1: Depends on InitState
open import Once.Backend.X86.Correct.StackInvariant public

-- Level 2: Depends on FetchStep, InstrExec, RegisterLemmas
open import Once.Backend.X86.Correct.ExecLemmas public

-- Level 3: Sequential execution helpers
open import Once.Backend.X86.Correct.SeqExec public

-- Level 4: Mutual block for run-ir-star-at-offset (Star-based IR execution)
open import Once.Backend.X86.Correct.MutualIR public

open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ; zero; suc; _∸_; _≡ᵇ_; _<_; _≤_; _>_; _≥_; s≤s; z≤n; _≟_) renaming (_+_ to _+ℕ_)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂) renaming ([_,_] to case-sum)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Maybe using (Maybe; just; nothing)
open import Function using (case_of_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; sym; trans; subst; subst₂; module ≡-Reasoning; inspect) renaming ([_] to ⟦_⟧ᵢ)
open import Relation.Nullary using (yes; no)
open ≡-Reasoning

-- NOTE: InitState and StackInvariant sections are now imported from:
--   Once.Backend.X86.Correct.InitState
--   Once.Backend.X86.Correct.StackInvariant

------------------------------------------------------------------------
-- Execution Helpers
------------------------------------------------------------------------
--
-- These helpers capture the behavior of instruction sequences.
-- See Once.Postulates for a summary of what remains postulated.
--
-- PROVEN (non-recursive IR helpers):
--   execMov-reg-reg, execMov-reg-imm, execMov-reg-mem-base,
--   execMov-reg-mem-disp, execMov-mem-base-imm, execMov-mem-disp-reg,
--   execSub-reg-imm, execJmp
--   run-single-mov, run-single-mov-imm, run-single-mov-mem-base,
--   run-single-mov-mem-disp
--   run-inl-seq, run-inr-seq, run-curry-seq
--
-- PROVEN (run-generator base cases - non-recursive IR constructors):
--   run-generator-id       : id (mov rax, rdi)
--   run-generator-terminal : terminal (mov rax, 0)
--   run-generator-fold     : fold (mov rax, rdi + encoding)
--   run-generator-unfold   : unfold (mov rax, rdi + encoding)
--   run-generator-arr      : arr (mov rax, rdi + encoding)
--   run-generator-fst      : fst (mov rax, [rdi])
--   run-generator-snd      : snd (mov rax, [rdi+8])
--   run-generator-inl      : inl (allocate + tag=0)
--   run-generator-inr      : inr (allocate + tag=1)
--   run-generator-curry    : curry (create closure)
--
-- PROVEN (compose base cases - specific IR combinations):
--   run-seq-compose-id-id         : id ∘ id (3 instructions)
--   run-seq-compose-terminal-id   : terminal ∘ id (3 instructions)
--   run-seq-compose-id-terminal   : id ∘ terminal (3 instructions)
--   run-generator-compose-id-id   : uses run-seq-compose-id-id
--   run-generator-compose-terminal-id: uses run-seq-compose-terminal-id
--   run-generator-compose-id-terminal: uses run-seq-compose-id-terminal
--
-- POSTULATED (case base cases - concrete instances, used before mutual induction):
--   run-case-inl-id   : [ id , g ] for left injection (8 instructions)
--   run-case-inr-id   : [ f , id ] for right injection (8 instructions)
--
-- PROVEN (via run-ir-star-at-offset mutual block):
--   run-seq-compose  : Sequential composition - derived from run-generator
--   run-case-inl/inr : Case analysis - derived from run-generator
--   run-generator    : Main induction theorem - uses run-ir-star-at-offset
--
-- TRUSTED ASSUMPTION (intentionally kept postulated):
--   run-apply-seq    : Closure application (complex calling convention)
--
-- The non-recursive helpers trace through fixed instruction sequences.
-- The recursive helpers form a mutually-dependent cluster that requires
-- structural induction on IR. See lessons-learned.md for details.
--
-- Note: The codegen uses placeholder label numbers (100, 200, 300, 400)
-- that don't match actual instruction positions. This causes jmp/jne
-- to out-of-bounds addresses, triggering halt. For recursive IR,
-- proper label resolution would be needed.
------------------------------------------------------------------------

-- NOTE: Execution helpers (execMov-*, execSub-*, execJmp, etc.) are now imported from:
--   Once.Backend.X86.Correct.InstrExec

-- NOTE: Register File Lemmas (readReg-writeReg-*) are now imported from:
--   Once.Backend.X86.Correct.RegisterLemmas

-- NOTE: Memory Lemmas (readMem-writeMem-*) are now imported from:
--   Once.Backend.X86.Correct.RegisterLemmas

open import Data.Nat.Properties using (≡ᵇ⇒≡; ≡⇒≡ᵇ; +-comm; +-assoc; +-identityʳ; m+[n∸m]≡n; ∸-+-assoc)

-- NOTE: Fetch and Step Lemmas (step-exec, step-exec-N, fetch-N, etc.) are now imported from:
--   Once.Backend.X86.Correct.FetchStep

-- NOTE: compile-length-correct is now imported from:
--   Once.Backend.X86.Correct.CompileLength

-- NOTE: The following are now imported from extracted modules:
--   - compile-length-correct, length-++ from CompileLength/FetchStep
--   - step-exec-N, fetch-N, step-halt-on-fetch-fail from FetchStep
--   - exec-*-steps-nonhalt, exec-chain, exec-until-pc-* from ExecLemmas
--   - exec-transfer-at, exec-pair-setup-at (5-step) from ExecLemmas
--   - run-*-at-offset functions from ExecLemmas

------------------------------------------------------------------------
-- run-ir-star-at-offset: Star-based non-halting execution of IR
--
-- This is the key recursive function using Star relations for composable
-- proofs without fuel arithmetic. It executes IR code at any position
-- in a larger program WITHOUT halting (continues to next instruction).
--
-- Returns IRStarResult with Star proof and all register/memory properties.
------------------------------------------------------------------------

------------------------------------------------------------------------

-- Complex IR cases (compose, pair, case, curry, apply) are defined
-- in MutualIR.agda using Star-based proofs (run-*-star-direct).


-- NOTE: List manipulation lemmas (compose-prog-eq, compose-transfer-eq, compose-g-eq)
-- are now imported from Once.Backend.Common.ProgramLemmas

------------------------------------------------------------------------
-- run-ir-star: Star-based version of IR execution
--
-- Delegates directly to run-ir-star-at-offset which returns IRStarResult.
--
-- Note: IRStarResult is defined in MutualIR.agda and re-exported from there.
------------------------------------------------------------------------

-- | Star-based IR execution at arbitrary offset
-- caller-sp: StackPointer representing the caller's stack frame (D041)
run-ir-star : ∀ {A B} (ir : IR A B) (prefix suffix : Program) (caller-sp : StackPointer) (x : ⟦ A ⟧) (s : State) →
    halted s ≡ false →
    pc s ≡ length prefix →
    readReg (regs s) rdi ≡ encode x →
    StackInvariant s →
    readReg (regs s) rsp > 16 →
    RbpInvariant s →
    ∃[ s' ] IRStarResult ir (prefix ++ compile-x86 ir ++ suffix) s s' x (length prefix)
run-ir-star = run-ir-star-at-offset

------------------------------------------------------------------------
-- Example: Composing IR proofs with Star
--
-- This demonstrates the simplification: instead of computing
-- (compile-length f + 1 + compile-length g) fuel and proving exec chains,
-- we just use star-trans to compose Star proofs.
------------------------------------------------------------------------

-- Helper: Execute single transfer instruction (mov rdi, rax)
-- Returns Star proof for one step
transfer-star : ∀ (prog : Program) (s : State) →
    halted s ≡ false →
    step prog s ≡ just (record s { regs = writeReg (regs s) rdi (readReg (regs s) rax)
                                 ; pc = pc s +ℕ 1 }) →
    Star prog s (record s { regs = writeReg (regs s) rdi (readReg (regs s) rax)
                          ; pc = pc s +ℕ 1 })
transfer-star prog s h-false step-eq = star-single h-false step-eq

-- | Compose two IR computations using Star
-- caller-sp: StackPointer representing the caller's stack frame (D041)
compose-with-star : ∀ {A B C} (f : IR A B) (g : IR B C) (caller-sp : StackPointer) (x : ⟦ A ⟧) (s : State) →
    halted s ≡ false →
    pc s ≡ 0 →
    readReg (regs s) rdi ≡ encode x →
    StackInvariant s →
    readReg (regs s) rsp > 16 →
    RbpInvariant s →
    ∃[ s' ] (Star (compile-x86 (g ∘ f)) s s'
           × halted s' ≡ false
           × readReg (regs s') rax ≡ encode (eval (g ∘ f) x))
compose-with-star {A} {B} {C} f g caller-sp x s h-false pc-0 rdi-eq stack-inv rsp>16 rbp-inv =
    s-final , star-proof , h-final , rax-final
  where
    open import Data.List.Properties using (++-identityʳ)

    -- Use run-ir-star-at-offset (Star-based, no fuel conversion needed)
    result = run-ir-star-at-offset (g ∘ f) [] [] caller-sp x s h-false pc-0 rdi-eq stack-inv rsp>16 rbp-inv
    s-final = proj₁ result
    r = proj₂ result
    h-final = ir-halted r
    rax-final = ir-rax r

    -- Convert program equality
    prog-eq : [] ++ compile-x86 (g ∘ f) ++ [] ≡ compile-x86 (g ∘ f)
    prog-eq = ++-identityʳ (compile-x86 (g ∘ f))

    star-proof : Star (compile-x86 (g ∘ f)) s s-final
    star-proof = subst (λ p → Star p s s-final) prog-eq (ir-star r)

-- The key insight: with Star, the compose proof structure becomes:
--
--   Step 1: Star prog s s₁      (execute f via run-ir-star f)
--   Step 2: Star prog s₁ s₂     (single transfer via star-single)
--   Step 3: Star prog s₂ s₃     (execute g via run-ir-star g)
--   ───────────────────────────────────────────────────────────
--   Result: Star prog s s₃      (star-trans (star-trans step1 step2) step3)
--
-- No fuel arithmetic like (compile-length f + 1 + compile-length g)!
-- Just transitivity of the star relation.

-- | Detailed Star-based compose showing the 3-step composition
-- Uses run-ir-star-at-offset directly - no fuel conversion needed
-- caller-sp: StackPointer representing the caller's stack frame (D041)
run-ir-star-compose-internal : ∀ {A B C} (f : IR A B) (g : IR B C)
    (prefix suffix : Program) (caller-sp : StackPointer) (x : ⟦ A ⟧) (s : State) →
    halted s ≡ false →
    pc s ≡ length prefix →
    readReg (regs s) rdi ≡ encode x →
    StackInvariant s →
    readReg (regs s) rsp > 16 →
    RbpInvariant s →
    ∃[ s' ] (Star (prefix ++ compile-x86 (g ∘ f) ++ suffix) s s'
           × halted s' ≡ false
           × readReg (regs s') rax ≡ encode (eval (g ∘ f) x))
run-ir-star-compose-internal {A} {B} {C} f g prefix suffix caller-sp x s h-false pc-eq rdi-eq stack-inv rsp>16 rbp-inv =
  let
    -- Use run-ir-star-at-offset (Star-based, no fuel conversion needed)
    result = run-ir-star-at-offset (g ∘ f) prefix suffix caller-sp x s h-false pc-eq rdi-eq stack-inv rsp>16 rbp-inv
    s-final = proj₁ result
    r = proj₂ result
  in
    s-final , ir-star r , ir-halted r , ir-rax r

-- The real benefit: when we need to compose multiple IR terms,
-- we can now use star-trans directly instead of fuel arithmetic.
--
-- Example: proving (h ∘ g ∘ f)
-- OLD: exec ((len-f + 1 + len-g) + 1 + len-h) with multiple exec-chain calls
-- NEW: star-trans (star-trans star-f star-g) star-h

------------------------------------------------------------------------
-- Full Star-based compose: explicit 3-step composition
--
-- DISABLED: These example functions have incorrect type annotations.
-- For Star-based compose, see compose-with-star above.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Connecting run-ir-star-at-offset to run-generator
------------------------------------------------------------------------

-- Key insight: run-ir-star-at-offset with empty prefix/suffix gives us:
--   Star (compile-x86 ir) s s' (via IRStarResult.ir-star)
--   halted s' ≡ false
--   pc s' ≡ compile-length ir = length (compile-x86 ir)
--
-- One more step causes fetch to fail (pc ≥ length), which halts.
-- This connects to run-generator which expects halted s' ≡ true.

-- Lemma: fetch at length returns nothing (by induction on list)
fetch-at-length : ∀ (xs : Program) → fetch xs (length xs) ≡ nothing
fetch-at-length [] = refl
fetch-at-length (x ∷ xs) = fetch-at-length xs

-- Lemma: At pc = compile-length ir with program = compile-x86 ir, fetch fails
-- Because compile-length ir = length (compile-x86 ir), there's nothing to fetch
fetch-at-end : ∀ {A B} (ir : IR A B) →
  fetch (compile-x86 ir) (compile-length ir) ≡ nothing
fetch-at-end ir = subst (λ n → fetch (compile-x86 ir) n ≡ nothing)
                        (compile-length-correct ir)
                        (fetch-at-length (compile-x86 ir))

-- Lemma: step halts when fetch fails
-- When fetch returns nothing, state becomes halted with true
-- Proof follows from step definition: when halted=false and fetch=nothing, step sets halted=true
--
-- This is tricky to prove directly because step uses with-abstraction.
-- Alias for step-halt-on-fetch-fail
step-halts-on-fetch-fail : ∀ (prog : Program) (s : State) →
  halted s ≡ false →
  fetch prog (pc s) ≡ nothing →
  step prog s ≡ just (record s { halted = true })
step-halts-on-fetch-fail = step-halt-on-fetch-fail

-- Lemma: When halted, step returns the same state
step-halted-stable : ∀ (prog : Program) (s : State) →
  halted s ≡ true →
  step prog s ≡ just s
step-halted-stable prog s h-true with halted s
... | true = refl
... | false with () ← h-true

-- Lemma: When halted, further exec keeps the same state
-- This is exec-n-halted from ExecLemmas, re-exported
exec-halted-stable : ∀ (n : ℕ) (prog : Program) (s : State) →
  halted s ≡ true →
  exec n prog s ≡ just s
exec-halted-stable = exec-n-halted

------------------------------------------------------------------------
-- Star-based generator: Primary interface (no fuel postulates)
--
-- Returns a Star execution trace from initial state to halted final state.
-- This is the cleanest interface - no fuel postulates needed.
------------------------------------------------------------------------

-- caller-sp: StackPointer representing the caller's stack frame (D041)
run-generator : ∀ {A B} (ir : IR A B) (caller-sp : StackPointer) (x : ⟦ A ⟧) (s : State) →
  halted s ≡ false → pc s ≡ 0 → readReg (regs s) rdi ≡ encode x →
  StackInvariant s → readReg (regs s) rsp > 16 → RbpInvariant s →
  ∃[ s' ] (Star (compile-x86 ir) s s'
         × halted s' ≡ true
         × readReg (regs s') rax ≡ encode (eval ir x))
run-generator {A} {B} ir caller-sp x s h-false pc-0 rdi-eq stack-inv rsp>16 rbp-inv =
  s-halted , star-full , halted-true , rax-preserved
  where
    open import Data.List.Properties using (++-identityʳ)

    prog : Program
    prog = compile-x86 ir

    -- Use run-ir-star-at-offset (Star-based)
    result = run-ir-star-at-offset ir [] [] caller-sp x s h-false pc-0 rdi-eq stack-inv rsp>16 rbp-inv
    s' = proj₁ result
    r = proj₂ result

    h' : halted s' ≡ false
    h' = ir-halted r

    pc' : pc s' ≡ compile-length ir
    pc' = ir-pc r

    rax' : readReg (regs s') rax ≡ encode (eval ir x)
    rax' = ir-rax r

    -- Program equality: [] ++ compile-x86 ir ++ [] = compile-x86 ir
    prog-eq : [] ++ compile-x86 ir ++ [] ≡ prog
    prog-eq = ++-identityʳ prog

    -- Convert Star to use prog
    star-raw : Star ([] ++ compile-x86 ir ++ []) s s'
    star-raw = ir-star r

    star-prog : Star prog s s'
    star-prog = subst (λ p → Star p s s') prog-eq star-raw

    -- One more step halts (fetch fails at end of program)
    s-halted : State
    s-halted = record s' { halted = true }

    -- fetch at pc s' = compile-length ir fails
    fetch-fail : fetch prog (pc s') ≡ nothing
    fetch-fail = subst (λ n → fetch prog n ≡ nothing) (sym pc') (fetch-at-end ir)

    step-halt : step prog s' ≡ just s-halted
    step-halt = step-halts-on-fetch-fail prog s' h' fetch-fail

    -- Extend star with halt step
    star-halt-step : Star prog s' s-halted
    star-halt-step = step* h' step-halt refl*

    star-full : Star prog s s-halted
    star-full = star-trans star-prog star-halt-step

    halted-true : halted s-halted ≡ true
    halted-true = refl

    -- rax is preserved when we just set halted = true
    rax-preserved : readReg (regs s-halted) rax ≡ encode (eval ir x)
    rax-preserved = rax'

------------------------------------------------------------------------
-- Helper: sequential execution of two programs (Star-based)
-- If p1 produces s1 with rax=v, and p2 with rdi=v produces s2,
-- then p1 ++ [mov rdi, rax] ++ p2 produces s2
-- Now derived from run-generator directly
------------------------------------------------------------------------

-- caller-sp: StackPointer representing the caller's stack frame (D041)
run-seq-compose : ∀ {A B C} (f : IR A B) (g : IR B C) (caller-sp : StackPointer) (x : ⟦ A ⟧) (s0 : State) →
  halted s0 ≡ false →
  pc s0 ≡ 0 →
  readReg (regs s0) rdi ≡ encode x →
  StackInvariant s0 →
  readReg (regs s0) rsp > 16 →
  RbpInvariant s0 →
  -- After running g ∘ f: exists s2 with Star trace and rax = encode (eval g (eval f x))
  ∃[ s2 ] (Star (compile-x86 (g ∘ f)) s0 s2
         × halted s2 ≡ true
         × readReg (regs s2) rax ≡ encode (eval g (eval f x)))
run-seq-compose {A} {B} {C} f g caller-sp x s0 h-false pc-0 rdi-eq stack-inv rsp>16 rbp-inv =
  run-generator (g ∘ f) caller-sp x s0 h-false pc-0 rdi-eq stack-inv rsp>16 rbp-inv

------------------------------------------------------------------------
-- Code generation correctness
--
-- Main theorem: executing compiled code produces the correct result.
-- The execution trace is witnessed by Star (reflexive-transitive closure).
------------------------------------------------------------------------

-- caller-sp: StackPointer representing the external caller's stack frame (D041)
codegen-x86-correct : ∀ {A B} (ir : IR A B) (caller-sp : StackPointer) (x : ⟦ A ⟧) →
  ∃[ s ] (Star (compile-x86 ir) (initWithInput x) s
        × halted s ≡ true
        × readReg (regs s) rax ≡ encode (eval ir x))
codegen-x86-correct ir caller-sp x =
  let (s' , star-eq , halt-eq , rax-eq) = run-generator ir caller-sp x (initWithInput x)
        (initWithInput-halted x) (initWithInput-pc x) (initWithInput-rdi x)
        (initWithInput-stack-inv x) (initWithInput-rsp>16 x) (initWithInput-rbp-inv x)
  in s' , star-eq , halt-eq , rax-eq

------------------------------------------------------------------------
-- Concrete E2E Tests
------------------------------------------------------------------------

-- | Test 1: Identity
-- IR: id
-- Input: any value x
-- Expected: x
test-id : ∀ {A} (caller-sp : StackPointer) (x : ⟦ A ⟧) →
  ∃[ s ] (Star (compile-x86 (id {A})) (initWithInput x) s
        × halted s ≡ true
        × readReg (regs s) rax ≡ encode x)
test-id {A} caller-sp x = codegen-x86-correct (id {A}) caller-sp x

-- | Test 2: First projection
-- IR: fst
-- Input: (a, b)
-- Expected: a
test-fst : ∀ {A B} (caller-sp : StackPointer) (a : ⟦ A ⟧) (b : ⟦ B ⟧) →
  ∃[ s ] (Star (compile-x86 (fst  {A} {B})) (initWithInput (a , b)) s
        × halted s ≡ true
        × readReg (regs s) rax ≡ encode a)
test-fst {A} {B} caller-sp a b = codegen-x86-correct (fst  {A} {B}) caller-sp (a , b)

-- | Test 3: Composition (fst after pairing)
-- IR: fst ∘ ⟨id, id⟩
-- Input: x
-- Expected: x (creates pair (x,x), extracts first = x)
test-fst-pair : ∀ {A} (caller-sp : StackPointer) (x : ⟦ A ⟧) →
  ∃[ s ] (Star (compile-x86 (fst  {A} {A} ∘ ⟨ id  {A} , id  {A} ⟩)) (initWithInput x) s
        × halted s ≡ true
        × readReg (regs s) rax ≡ encode x)
test-fst-pair {A} caller-sp x = codegen-x86-correct (fst  {A} {A} ∘ ⟨ id  {A} , id  {A} ⟩) caller-sp x

-- | Test 4: Case analysis
-- IR: [ id , id ]
-- Input: inl a or inr b
-- Expected: a or b (identity on sum)
test-case-id : ∀ {A} (caller-sp : StackPointer) (x : ⟦ A ⟧ ⊎ ⟦ A ⟧) →
  ∃[ s ] (Star (compile-x86 [ id  {A} , id  {A} ]) (initWithInput x) s
        × halted s ≡ true
        × readReg (regs s) rax ≡ encode (eval [ id  {A} , id  {A} ] x))
test-case-id {A} caller-sp x = codegen-x86-correct [ id  {A} , id  {A} ] caller-sp x

-- | Test 5: Curry creates closure
-- IR: curry fst
-- Input: a
-- Expected: closure that takes b and returns a
test-curry : ∀ {A B} (caller-sp : StackPointer) (a : ⟦ A ⟧) →
  ∃[ s ] (Star (compile-x86 (curry (fst  {A} {B}))) (initWithInput a) s
        × halted s ≡ true
        × readReg (regs s) rax ≡ encode {B ⇒ A} (eval (curry (fst  {A} {B})) a))
test-curry {A} {B} caller-sp a = codegen-x86-correct (curry (fst  {A} {B})) caller-sp a

-- | Test 6: TRUE E2E - Curry + Apply composed
-- IR: apply ∘ ⟨curry fst, id⟩
-- Input: a
-- Expected: a (creates closure λb.a, pairs with a, applies closure to a, returns a)
--
-- THIS IS THE KEY TEST: The compiled program includes BOTH:
--   - curry's thunk code (inside the pairing)
--   - apply's call instruction
-- When apply calls the closure, it jumps to the thunk WITHIN THE SAME PROGRAM.
-- With RIP-relative addressing, the code-ptr is computed correctly.
test-curry-apply : ∀ {A} (caller-sp : StackPointer) (a : ⟦ A ⟧) →
  ∃[ s ] (Star (compile-x86 (apply  {A} {A} ∘ ⟨ curry (fst  {A} {A}) , id  {A} ⟩)) (initWithInput a) s
        × halted s ≡ true
        × readReg (regs s) rax ≡ encode (eval (apply  {A} {A} ∘ ⟨ curry (fst  {A} {A}) , id  {A} ⟩) a))
test-curry-apply {A} caller-sp a = codegen-x86-correct (apply  {A} {A} ∘ ⟨ curry (fst  {A} {A}) , id  {A} ⟩) caller-sp a

------------------------------------------------------------------------
-- E2E Summary
------------------------------------------------------------------------

-- The x86 backend correctness theorem (codegen-x86-correct) proves:
--
--   For ANY IR morphism ir : A → B and input x : ⟦A⟧,
--   running compile-x86 ir on encoded input produces encoded output:
--     Star (compile-x86 ir) (initWithInput x) = just s
--     readReg (regs s) rax = encode (eval ir x)
--
-- This is proven by structural induction on IR, with each generator
-- handled by its own correctness lemma.
--
-- Postulates:
--   - run-apply-seq: apply in isolation (proof engineering convenience)
--   - Encoding axioms: memory layout of pairs, sums, closures
--   - Some internal stepping lemmas (tedious but straightforward)
--
-- KEY INSIGHT: With RIP-relative LEA and PC-relative jumps, the compiled
-- program for `apply ∘ ⟨curry fst, id⟩` IS truly executable E2E:
--
--   Layout (34 instructions):
--     0-4:   Pair setup (push r14, push r15, sub rsp 16, mov r15 rsp, mov r14 rdi)
--     5-18:  curry fst (includes thunk at positions 11-17)
--       5:   sub rsp, 16
--       6:   mov [rsp], rdi
--       7:   lea r9, [rip+4]     ← Computes 7+4=11 (thunk absolute address!)
--       8:   mov [rsp+8], r9
--       9:   mov rax, rsp
--       10:  jmp 7               ← PC-relative: 10+1+7=18 (skips thunk)
--       11:  label 6             ← THUNK ENTRY (code-ptr points here)
--       12:  sub rsp, 16
--       13:  mov [rsp], r12      ← r12 = env from closure
--       14:  mov [rsp+8], rdi    ← rdi = argument
--       15:  mov rdi, rsp
--       16:  mov rax, [rdi]      ← fst loads env
--       17:  ret                 ← returns (halts in our model)
--       18:  label 13            ← end-label
--     19-26: Pair completion (store results, cleanup)
--     27:    mov rdi, rax        ← Composition connector
--     28-33: apply
--       28:  mov r15, [rdi]      ← closure from pair.fst
--       29:  mov rsi, [rdi+8]    ← argument from pair.snd
--       30:  mov r12, [r15]      ← env from closure
--       31:  mov r15, [r15+8]    ← code-ptr from closure → r15 = 11
--       32:  mov rdi, rsi        ← argument to rdi
--       33:  call r15            ← CALLS POSITION 11 (thunk within program!)
--
--   Execution flow for apply ∘ ⟨curry fst, id⟩ on input a:
--     1. Pairing creates pair (closure-for-a, a)
--     2. curry stores code-ptr=11 (computed by LEA at pc=7: 7+4=11)
--     3. apply loads code-ptr=11, calls r15
--     4. Execution jumps to position 11 (thunk WITHIN THIS PROGRAM)
--     5. Thunk creates pair (env, arg) = (a, a), executes fst → a
--     6. ret halts, rax = encode(a) ✓
--
-- The run-apply-seq postulate is a PROOF ENGINEERING convenience for
-- modularity. The actual execution IS fully contained in the compiled program.
--
------------------------------------------------------------------------
-- Structural E2E Verification
------------------------------------------------------------------------
--
-- To prove that apply ∘ ⟨curry fst, id⟩ is truly self-contained,
-- we verify that the thunk address computed by curry is within the program:

-- | Compiled program for curry ∘ ⟨curry fst, id⟩
curry-apply-prog : {A : Type} → Program
curry-apply-prog {A} = compile-x86 (apply  {A} {A} ∘ ⟨ curry (fst  {A} {A}) , id  {A} ⟩)

-- | Program length
curry-apply-len : {A : Type} → ℕ
curry-apply-len {A} = length (curry-apply-prog {A})

-- | Expected length: (15 + (19 + 1) + 1) + 1 + 8 = 45
-- Curry is now 19 + len-f due to frame pointer and r15 save/restore
-- Apply is now 8 instructions (was 6) due to r15 save/restore
curry-apply-len-check : curry-apply-len {Int} ≡ 45
curry-apply-len-check = refl

-- | Position of curry's LEA instruction (within pairing, offset 7 + 2 = 9)
-- LEA computes: pc + 4 = 9 + 4 = 13
curry-lea-pos : ℕ
curry-lea-pos = 9

-- | Position of thunk entry (label at position 13)
thunk-entry-pos : ℕ
thunk-entry-pos = 13

-- | Verify thunk is within program bounds (13 < 45, i.e., 14 ≤ 45)
-- Using arithmetic lemma: 14 + 31 = 45, so m≤m+n 14 31 proves 14 ≤ 45 in O(1)
thunk-in-bounds : thunk-entry-pos < curry-apply-len {Int}
thunk-in-bounds = m≤m+n 14 31
  where
    open import Data.Nat.Properties using (m≤m+n)

-- | The instruction at thunk entry is a label (no-op)
thunk-entry-is-label : fetch (curry-apply-prog {Int}) thunk-entry-pos ≡ just (label 6)
thunk-entry-is-label = refl

-- | LEA instruction computes thunk address correctly
-- At position 7, LEA r9 [rip+4] computes: 7 + 4 = 11
lea-computes-thunk : curry-lea-pos +ℕ 4 ≡ thunk-entry-pos
lea-computes-thunk = refl

-- CONCLUSION: The call target (thunk at position 11) IS within the 34-instruction
-- program. When apply executes 'call r15' with r15=11, execution jumps to
-- position 11, which is the thunk's entry point - a valid instruction.

------------------------------------------------------------------------
-- Generalized Composition Theorems
------------------------------------------------------------------------
--
-- These theorems make explicit the key insight: apply is only meaningful
-- in composition with curry. The compiled code for curry embeds a thunk,
-- and apply's `call r15` jumps to that thunk within the same program.
--
-- See docs/formal/x86-full-proof-architecture.md for the full proof strategy.

-- | Curry-Apply Fundamental Theorem
--
-- For any f : IR (A * B) C, the composition `apply ∘ ⟨curry f ∘ fst, snd⟩`
-- correctly implements f. This is the categorical curry-apply law at the
-- code generation level.
--
-- Semantically: eval (apply ∘ ⟨curry f ∘ fst, snd⟩) (a, b) = eval f (a, b)
curry-apply-composition : ∀ {A B C} (f : IR (A * B) C) (caller-sp : StackPointer) (a : ⟦ A ⟧) (b : ⟦ B ⟧) →
  ∃[ s ] (Star (compile-x86 (apply ∘ ⟨ curry f ∘ fst , snd ⟩)) (initWithInput (a , b)) s
        × halted s ≡ true
        × readReg (regs s) rax ≡ encode (eval f (a , b)))
curry-apply-composition {A} {B} {C} f caller-sp a b =
  -- This follows directly from codegen-x86-correct
  -- The key is that eval (apply ∘ ⟨curry f ∘ fst, snd⟩) (a,b) = eval f (a,b)
  -- by the categorical curry-apply law (proven in Once.Category.Laws)
  codegen-x86-correct (apply ∘ ⟨ curry f ∘ fst , snd ⟩) caller-sp (a , b)

-- | Curry-Apply with arbitrary second component
--
-- More general: for any f : IR (A * B) C and g : IR D B,
-- `apply ∘ ⟨curry f, g⟩` applies the closure (curry f x) to (g x).
--
-- Semantically: eval (apply ∘ ⟨curry f, g⟩) x = eval f (x, eval g x)
curry-apply-any-g : ∀ {A B C} (f : IR (A * B) C) (g : IR A B) (caller-sp : StackPointer) (x : ⟦ A ⟧) →
  ∃[ s ] (Star (compile-x86 (apply ∘ ⟨ curry f , g ⟩)) (initWithInput x) s
        × halted s ≡ true
        × readReg (regs s) rax ≡ encode (eval f (x , eval g x)))
curry-apply-any-g {A} {B} {C} f g caller-sp x =
  codegen-x86-correct (apply ∘ ⟨ curry f , g ⟩) caller-sp x

-- | Curry-Apply with identity (the E2E test case)
--
-- Special case: `apply ∘ ⟨curry f, id⟩` where the argument is passed through.
-- This is the pattern proven step-by-step in E2E-Trace below.
--
-- Semantically: eval (apply ∘ ⟨curry f, id⟩) x = eval f (x, x)
curry-apply-id : ∀ {A C} (f : IR (A * A) C) (caller-sp : StackPointer) (x : ⟦ A ⟧) →
  ∃[ s ] (Star (compile-x86 (apply ∘ ⟨ curry f , id ⟩)) (initWithInput x) s
        × halted s ≡ true
        × readReg (regs s) rax ≡ encode (eval f (x , x)))
curry-apply-id {A} {C} f caller-sp x =
  codegen-x86-correct (apply ∘ ⟨ curry f , id ⟩) caller-sp x

-- | Curry-Apply with constant environment
--
-- Shows curry works with a constant captured value:
-- `apply ∘ ⟨curry f ∘ terminal, id⟩` where f : IR (Unit * A) B
-- The closure captures unit (empty environment) and applies to the input.
curry-apply-const-env : ∀ {A B} (f : IR (Unit * A) B) (caller-sp : StackPointer) (x : ⟦ A ⟧) →
  ∃[ s ] (Star (compile-x86 (apply ∘ ⟨ curry f ∘ terminal , id ⟩)) (initWithInput x) s
        × halted s ≡ true
        × readReg (regs s) rax ≡ encode (eval f (tt , x)))
curry-apply-const-env {A} {B} f caller-sp x =
  codegen-x86-correct (apply ∘ ⟨ curry f ∘ terminal , id ⟩) caller-sp x

