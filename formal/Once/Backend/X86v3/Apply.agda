------------------------------------------------------------------------
-- Once.Backend.X86v3.Apply
--
-- Apply proof using SlotMachine with CONCRETE validity definitions.
--
-- This module proves the Apply setup phase:
--   - Extract closure-loc and arg-loc from input pair
--   - Extract env-loc and code-loc from closure
--   - Set up registers for recursive dispatch
--
-- The actual recursive dispatch requires MutualIR structure.
------------------------------------------------------------------------

module Once.Backend.X86v3.Apply where

open import Data.Nat using (ℕ; suc; _<_; _≤_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Bool using (Bool; true; false)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; ∃-syntax)
open import Data.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; trans; sym; subst)
open import Induction.WellFounded using (Acc; acc)

open import Once.Backend.Common.FrameSemantics using (FrameSemantics)
open import Once.Backend.Common.SlotMachine
open import Once.Backend.X86v3.Validity
open import Once.Backend.X86v3.IR
open import Once.Backend.X86v3.Allocation

------------------------------------------------------------------------
-- Apply Instructions
------------------------------------------------------------------------

module ApplyInstrs {FS : FrameSemantics} where

  -- Apply setup extracts closure components and argument
  -- Input: RDI = input-loc (pair of closure and arg)
  -- Output: R15 = code-loc, R12 = env-loc, RDI = arg-loc
  apply-setup : (input-loc : ValueLocation FS) → List (Instr FS)
  apply-setup input-loc =
    load R15 (Loc input-loc) ∷        -- R15 := closure-loc
    load RSI (Loc (sucLoc input-loc)) ∷ -- RSI := arg-loc
    load R12 (IndReg R15) ∷           -- R12 := env-loc
    load R15 (IndRegSuc R15) ∷        -- R15 := code-loc
    mov RDI RSI ∷                     -- RDI := arg-loc
    []

------------------------------------------------------------------------
-- Apply Correctness Proof
------------------------------------------------------------------------

module ApplyProof {FS : FrameSemantics} (program-bound : ℕ) where
  open ApplyInstrs {FS}
  open MemOps {FS}
  open ExecFinal {FS}
  open ExecLemmas {FS}
  open ValidityDef {FS} program-bound
  open FrontierInvariant {FS}

  -- Apply setup result: extracts all component locations and sets up registers
  -- for recursive dispatch to the closure's code.
  --
  -- KEY: Now includes the body IR and env for dispatch!
  -- The closure has semantic value: λ arg → eval body (pair env arg)
  -- So to compute (fst input) (snd input), we dispatch to body with (env, snd input).
  record ApplySetupResult
           {A B : Type}
           (alloc : AllocState {FS})
           (input : ⟦ (A ⇒ B) * A ⟧)
           (input-loc : ValueLocation FS)
           (s s' : LocState FS) : Set where
    field
      -- Locations extracted
      closure-loc : ValueLocation FS
      arg-loc : ValueLocation FS
      env-loc : ValueLocation FS
      code-loc : ValueLocation FS
      -- Body IR and env from closure (for recursive dispatch)
      EnvType : Type
      body : IR (EnvType * A) B
      env : ⟦ EnvType ⟧
      -- Size bound for body (enables termination in Apply via rs body<bound)
      body<bound : ir-size body < program-bound
      -- Proof that closure semantics matches
      closure-is-body : fst input ≡ (λ arg → eval body (pair env arg))
      -- Register contents after setup
      r15-is-code : readReg (regs s') R15 ≡ code-loc
      r12-is-env  : readReg (regs s') R12 ≡ env-loc
      rdi-is-arg  : readReg (regs s') RDI ≡ arg-loc
      rsi-is-arg  : readReg (regs s') RSI ≡ arg-loc
      not-halted  : halted s' ≡ false
      -- Frontier tracking for all extracted locations
      closure-before : BeforeFrontier alloc closure-loc
      arg-before : BeforeFrontier alloc arg-loc
      env-before : BeforeFrontier alloc env-loc
      code-before : BeforeFrontier alloc code-loc
      -- For recursive dispatch, we need validity of (env, arg)
      env-valid : ValidAt alloc env env-loc s'
      arg-valid : ValidAt alloc (snd input) arg-loc s'

  -- Helper for readLoc equality transport
  readLoc-mem-eq : ∀ (s₁ s₂ : LocState FS) loc →
    stackMem s₁ ≡ stackMem s₂ →
    heapMem s₁ ≡ heapMem s₂ →
    readLoc s₁ loc ≡ readLoc s₂ loc
  readLoc-mem-eq s₁ s₂ (OnStack f k) seq heq = cong (λ m → m f k) seq
  readLoc-mem-eq s₁ s₂ (OnHeap r o) seq heq = cong (λ m → m r o) heq

  apply-setup-correct :
    ∀ {A B : Type}
      (alloc : AllocState {FS})
      (input : ⟦ (A ⇒ B) * A ⟧)
      (input-loc : ValueLocation FS)
      (s : LocState FS) →
    ValidAt alloc input input-loc s →
    BeforeFrontier alloc input-loc →
    halted s ≡ false →
    ∃[ s' ] ApplySetupResult {A} {B} alloc input input-loc s s'

  apply-setup-correct {A} {B} alloc input input-loc s input-valid input-before not-halted =
    s5 , record
      { closure-loc = closure-loc
      ; arg-loc = arg-loc
      ; env-loc = env-loc
      ; code-loc = code-loc
      ; EnvType = EnvType
      ; body = body
      ; env = env
      ; body<bound = body<bound'
      ; closure-is-body = closure-is-body
      ; r15-is-code = r15-s5
      ; r12-is-env = r12-s5
      ; rdi-is-arg = rdi-s5
      ; rsi-is-arg = rsi-s5
      ; not-halted = halted-s5
      ; closure-before = closure-before
      ; arg-before = arg-before
      ; env-before = env-before
      ; code-before = code-before
      ; env-valid = env-valid-s5
      ; arg-valid = arg-valid-s5
      }
    where
      -- ========== Decompose validity ==========

      pair-decomp : PairValid alloc input input-loc s
      pair-decomp = decomposePair input-valid

      closure-loc : ValueLocation FS
      closure-loc = PairValid.fst-loc pair-decomp

      arg-loc : ValueLocation FS
      arg-loc = PairValid.snd-loc pair-decomp

      -- Frontier proofs from decomposition
      closure-before : BeforeFrontier alloc closure-loc
      closure-before = PairValid.fst-before pair-decomp

      arg-before : BeforeFrontier alloc arg-loc
      arg-before = PairValid.snd-before pair-decomp

      closure-valid : ValidAt alloc (fst input) closure-loc s
      closure-valid = PairValid.fst-valid pair-decomp

      arg-valid : ValidAt alloc (snd input) arg-loc s
      arg-valid = PairValid.snd-valid pair-decomp

      closure-decomp : ClosureValid alloc (fst input) closure-loc s
      closure-decomp = decomposeClosure closure-valid

      -- Extract body IR and env from closure!
      EnvType : Type
      EnvType = ClosureValid.EnvType closure-decomp

      body : IR (EnvType * A) B
      body = ClosureValid.body closure-decomp

      env : ⟦ EnvType ⟧
      env = ClosureValid.env closure-decomp

      closure-is-body : fst input ≡ (λ arg → eval body (pair env arg))
      closure-is-body = ClosureValid.f-is-closure closure-decomp

      -- Size bound for body (enables termination in Apply via rs body<bound)
      body<bound' : ir-size body < program-bound
      body<bound' = ClosureValid.body<bound closure-decomp

      env-loc : ValueLocation FS
      env-loc = ClosureValid.env-loc closure-decomp

      code-loc : ValueLocation FS
      code-loc = ClosureValid.code-loc closure-decomp

      -- Frontier proofs from closure decomposition
      env-before : BeforeFrontier alloc env-loc
      env-before = ClosureValid.env-before closure-decomp

      code-before : BeforeFrontier alloc code-loc
      code-before = ClosureValid.code-before closure-decomp

      -- Env validity from closure
      env-valid : ValidAt alloc env env-loc s
      env-valid = ClosureValid.env-valid closure-decomp

      -- ========== Memory facts from validity ==========

      mem-closure : readLoc s input-loc ≡ just closure-loc
      mem-closure = PairValid.fst-ptr pair-decomp

      mem-arg : readLoc s (sucLoc input-loc) ≡ just arg-loc
      mem-arg = PairValid.snd-ptr pair-decomp

      mem-env : readLoc s closure-loc ≡ just env-loc
      mem-env = ClosureValid.env-ptr closure-decomp

      mem-code : readLoc s (sucLoc closure-loc) ≡ just code-loc
      mem-code = ClosureValid.code-ptr closure-decomp

      -- ========== Step 1: load R15 (Loc input-loc) ==========

      s1 : LocState FS
      s1 = exec (load R15 (Loc input-loc)) s

      mem-read-s1 : readLoc s (resolveSourceExt (regs s) (Loc input-loc)) ≡ just closure-loc
      mem-read-s1 = mem-closure

      r15-s1 : readReg (regs s1) R15 ≡ closure-loc
      r15-s1 = load-result R15 (Loc input-loc) s closure-loc mem-read-s1

      halted-s1 : halted s1 ≡ false
      halted-s1 = load-no-halt R15 (Loc input-loc) s closure-loc mem-read-s1 not-halted

      stackMem-s1 : stackMem s1 ≡ stackMem s
      stackMem-s1 = load-preserves-stackMem R15 (Loc input-loc) s

      heapMem-s1 : heapMem s1 ≡ heapMem s
      heapMem-s1 = load-preserves-heapMem R15 (Loc input-loc) s

      -- ========== Step 2: load RSI (Loc (sucLoc input-loc)) ==========

      s2 : LocState FS
      s2 = exec (load RSI (Loc (sucLoc input-loc))) s1

      mem-arg-s1 : readLoc s1 (sucLoc input-loc) ≡ just arg-loc
      mem-arg-s1 = trans (sym (readLoc-mem-eq s s1 (sucLoc input-loc) (sym stackMem-s1) (sym heapMem-s1))) mem-arg

      mem-read-s2 : readLoc s1 (resolveSourceExt (regs s1) (Loc (sucLoc input-loc))) ≡ just arg-loc
      mem-read-s2 = mem-arg-s1

      rsi-s2 : readReg (regs s2) RSI ≡ arg-loc
      rsi-s2 = load-result RSI (Loc (sucLoc input-loc)) s1 arg-loc mem-read-s2

      r15-s2 : readReg (regs s2) R15 ≡ closure-loc
      r15-s2 = trans (load-preserves-reg RSI (Loc (sucLoc input-loc)) s1 R15 arg-loc
                       mem-read-s2 (λ ())) r15-s1

      halted-s2 : halted s2 ≡ false
      halted-s2 = load-no-halt RSI (Loc (sucLoc input-loc)) s1 arg-loc mem-read-s2 halted-s1

      stackMem-s2 : stackMem s2 ≡ stackMem s
      stackMem-s2 = trans (load-preserves-stackMem RSI (Loc (sucLoc input-loc)) s1) stackMem-s1

      heapMem-s2 : heapMem s2 ≡ heapMem s
      heapMem-s2 = trans (load-preserves-heapMem RSI (Loc (sucLoc input-loc)) s1) heapMem-s1

      -- ========== Step 3: load R12 (IndReg R15) ==========

      s3 : LocState FS
      s3 = exec (load R12 (IndReg R15)) s2

      resolve-s3 : resolveSourceExt (regs s2) (IndReg R15) ≡ closure-loc
      resolve-s3 = r15-s2

      mem-env-s2 : readLoc s2 closure-loc ≡ just env-loc
      mem-env-s2 = trans (sym (readLoc-mem-eq s s2 closure-loc (sym stackMem-s2) (sym heapMem-s2))) mem-env

      mem-read-s3 : readLoc s2 (resolveSourceExt (regs s2) (IndReg R15)) ≡ just env-loc
      mem-read-s3 = subst (λ loc → readLoc s2 loc ≡ just env-loc) (sym resolve-s3) mem-env-s2

      r12-s3 : readReg (regs s3) R12 ≡ env-loc
      r12-s3 = load-result R12 (IndReg R15) s2 env-loc mem-read-s3

      r15-s3 : readReg (regs s3) R15 ≡ closure-loc
      r15-s3 = trans (load-preserves-reg R12 (IndReg R15) s2 R15 env-loc mem-read-s3 (λ ())) r15-s2

      rsi-s3 : readReg (regs s3) RSI ≡ arg-loc
      rsi-s3 = trans (load-preserves-reg R12 (IndReg R15) s2 RSI env-loc mem-read-s3 (λ ())) rsi-s2

      halted-s3 : halted s3 ≡ false
      halted-s3 = load-no-halt R12 (IndReg R15) s2 env-loc mem-read-s3 halted-s2

      stackMem-s3 : stackMem s3 ≡ stackMem s
      stackMem-s3 = trans (load-preserves-stackMem R12 (IndReg R15) s2) stackMem-s2

      heapMem-s3 : heapMem s3 ≡ heapMem s
      heapMem-s3 = trans (load-preserves-heapMem R12 (IndReg R15) s2) heapMem-s2

      -- ========== Step 4: load R15 (IndRegSuc R15) ==========

      s4 : LocState FS
      s4 = exec (load R15 (IndRegSuc R15)) s3

      resolve-s4 : resolveSourceExt (regs s3) (IndRegSuc R15) ≡ sucLoc closure-loc
      resolve-s4 = cong sucLoc r15-s3

      mem-code-s3 : readLoc s3 (sucLoc closure-loc) ≡ just code-loc
      mem-code-s3 = trans (sym (readLoc-mem-eq s s3 (sucLoc closure-loc) (sym stackMem-s3) (sym heapMem-s3))) mem-code

      mem-read-s4 : readLoc s3 (resolveSourceExt (regs s3) (IndRegSuc R15)) ≡ just code-loc
      mem-read-s4 = subst (λ loc → readLoc s3 loc ≡ just code-loc) (sym resolve-s4) mem-code-s3

      r15-s4 : readReg (regs s4) R15 ≡ code-loc
      r15-s4 = load-result R15 (IndRegSuc R15) s3 code-loc mem-read-s4

      r12-s4 : readReg (regs s4) R12 ≡ env-loc
      r12-s4 = trans (load-preserves-reg R15 (IndRegSuc R15) s3 R12 code-loc mem-read-s4 (λ ())) r12-s3

      rsi-s4 : readReg (regs s4) RSI ≡ arg-loc
      rsi-s4 = trans (load-preserves-reg R15 (IndRegSuc R15) s3 RSI code-loc mem-read-s4 (λ ())) rsi-s3

      halted-s4 : halted s4 ≡ false
      halted-s4 = load-no-halt R15 (IndRegSuc R15) s3 code-loc mem-read-s4 halted-s3

      -- ========== Step 5: mov RDI RSI ==========

      s5 : LocState FS
      s5 = exec (mov RDI RSI) s4

      rdi-s5 : readReg (regs s5) RDI ≡ arg-loc
      rdi-s5 = trans (mov-result RDI RSI s4) rsi-s4

      r15-s5 : readReg (regs s5) R15 ≡ code-loc
      r15-s5 = trans (mov-preserves-reg RDI RSI s4 R15 (λ ())) r15-s4

      r12-s5 : readReg (regs s5) R12 ≡ env-loc
      r12-s5 = trans (mov-preserves-reg RDI RSI s4 R12 (λ ())) r12-s4

      rsi-s5 : readReg (regs s5) RSI ≡ arg-loc
      rsi-s5 = trans (mov-preserves-reg RDI RSI s4 RSI (λ ())) rsi-s4

      halted-s5 : halted s5 ≡ false
      halted-s5 = halted-s4  -- mov doesn't change halted

      -- ========== Validity preservation for arg ==========
      -- Memory is unchanged through all load/mov operations

      stackMem-s4 : stackMem s4 ≡ stackMem s
      stackMem-s4 = trans (load-preserves-stackMem R15 (IndRegSuc R15) s3) stackMem-s3

      heapMem-s4 : heapMem s4 ≡ heapMem s
      heapMem-s4 = trans (load-preserves-heapMem R15 (IndRegSuc R15) s3) heapMem-s3

      stackMem-s5 : stackMem s5 ≡ stackMem s
      stackMem-s5 = trans (mov-preserves-stackMem RDI RSI s4) stackMem-s4

      heapMem-s5 : heapMem s5 ≡ heapMem s
      heapMem-s5 = trans (mov-preserves-heapMem RDI RSI s4) heapMem-s4

      env-valid-s5 : ValidAt alloc env env-loc s5
      env-valid-s5 = validity-mem-only env env-loc s s5
                       (sym stackMem-s5) (sym heapMem-s5) env-valid

      arg-valid-s5 : ValidAt alloc (snd input) arg-loc s5
      arg-valid-s5 = validity-mem-only (snd input) arg-loc s s5
                       (sym stackMem-s5) (sym heapMem-s5) arg-valid

------------------------------------------------------------------------
-- Summary
--
-- apply-setup-correct proves the setup phase:
--   Input:  ValidAt alloc input input-loc s
--           BeforeFrontier alloc input-loc
--   Output: ApplySetupResult with:
--           - closure-loc, arg-loc, env-loc, code-loc extracted
--           - EnvType, body, env from closure (for dispatch!)
--           - closure-is-body : fst input ≡ (λ arg → eval body (pair env arg))
--           - R15 = code-loc, R12 = env-loc, RDI = arg-loc
--           - BeforeFrontier for all extracted locations
--           - ValidAt for env and arg (ready for recursive dispatch)
--
-- KEY INSIGHT: Since closures track their body IR, we extract it here!
-- The closure has semantic value: λ arg → eval body (pair env arg)
-- So (fst input) (snd input) = eval body (pair env (snd input))
-- Dispatcher can call body on (env, snd input) to compute the result.
--
-- FROM Validity.agda (ALL PROVEN):
--   - ValidAt with AllocState parameter
--   - valid-closure tracks body IR and env
--   - decomposePair, decomposeClosure (pattern matching on ValidAt)
--   - PairValid, ClosureValid (include BeforeFrontier AND body IR)
--   - validity-mem-only (validity preserved when memory unchanged)
--
-- FROM SlotMachine.agda (ALL PROVEN):
--   - load-result, load-preserves-reg
--   - load-preserves-stackMem, load-preserves-heapMem
--   - load-no-halt
--   - mov-result, mov-preserves-reg
--   - mov-preserves-stackMem, mov-preserves-heapMem
--
-- NO POSTULATES in this module!
------------------------------------------------------------------------
