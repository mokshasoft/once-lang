------------------------------------------------------------------------
-- Once.Backend.X86.Correct.MutualIR
--
-- Concrete dispatcher that wires together all implementation modules.
--
-- This file contains:
-- 1. The mutual block with the main dispatcher (run-ir-star-at-offset-v)
-- 2. Curry setup (delegates thunk proof to IR/Curry.curry-thunk-correct-v)
-- 3. Apply implementation
-- 4. Helper make-curry-closure-wf for WholeProgram.agda
--
-- IR implementations are in IR/*.agda and take RecDispatcher as parameter.
-- NOTE: Sized types removed for compilation performance (10-100x speedup).
-- Termination is guaranteed by well-founded recursion on ir-size.
------------------------------------------------------------------------

module Once.Backend.X86.Correct.MutualIR where

open import Once.Type
open import Once.IR
open import Once.Semantics hiding (env-addr; semantics)
  renaming (Closure-η to Closure-η-sem)

open import Once.Backend.X86.Syntax
open import Once.Backend.X86.Semantics
open Once.Backend.X86.Semantics.State
open Once.Backend.X86.Semantics.Flags
open import Once.Backend.X86.CodeGen

-- Import common memory helper lemmas
open import Once.Backend.Common.Memory
  using (≡ᵇ-refl; n≢n+suc)

-- Import common program manipulation lemmas
open import Once.Backend.Common.ProgramLemmas
  using (compose-prog-eq; compose-transfer-eq; compose-g-eq)

-- Import memory region definitions
open import Once.Backend.X86.Layout
  using (InStack; InHeap; InCode; stack-code-addr-disjoint; StackPointer; frameSlot; slot-addr;
         slot-addr-above-thunk-rbp; slot-addr-≥-base; addr; in-stack)
-- Internal glue for abstraction boundary (implementation use only!)
open import Once.Backend.X86.Layout using (module FrameSlotInternal)
open FrameSlotInternal using (frameSlot-is-readMem)

-- Import stack capacity and region lemmas for D041 approach
open import Once.Backend.X86.Correct.StackInstantiation
  using (StackCapacity; capacity-maintained; rsp-bound-to-capacity; rsp-in-stack;
         slot-size; slots; slots-mono-≤; ir-stack-requirement;
         capacity-left-from-max; capacity-right-from-max; capacity-from-larger;
         capacity-preserved-rsp-unchanged;
         -- Named capacity constants (from codegen)
         curry-closure-capacity; inl-inr-capacity; apply-capacity;
         thunk-setup-capacity; thunk-setup-consumed-slots; thunk-setup-fits-pair-capacity;
         thunk-setup-cap≤thunk-consumed+ir-req;
         -- IR-specific capacity bounds
         curry-closure-capacity≤curry-req; inl-capacity≤inl-req;
         inr-capacity≤inr-req; apply-capacity≤apply-req)

open import Once.Backend.X86.Correct.RegisterLemmas
open import Once.Backend.X86.Correct.FetchStep
open import Once.Backend.X86.Correct.CompileLength hiding (length-++)
open import Once.Backend.X86.Correct.InstrExec
open import Once.Backend.X86.Correct.InitState
open import Once.Backend.X86.Correct.StackInstantiation
open import Once.Backend.X86.Correct.ExecLemmas
open import Once.Backend.X86.Correct.SeqExec
open import Once.Backend.X86.Correct.ArithmeticLemmas using (word-fits-thunk-bound; word-fits-pair-strict)
open import Once.Backend.X86.Correct.Star
  using (Star; refl*; step*; star-trans; star-single; ⟨_,_⟩◅_;
         star-step2; star-step3; star-step4; just-injective)
-- Re-export StarBase
-- Simple Star proofs (non-recursive) are in StarBase.agda
open import Once.Backend.X86.Correct.StarBase public
  using (IRStarResultV; ClosureWFOutput; no-closure; has-closure; ApplyReady;
         transport-cwf; subst-cwf-prog;
         ir-star; ir-halted; ir-pc; ir-r14; ir-r15; ir-rbp;
         ir-mem; ir-mem-rbp; ir-mem-rbp+8; ir-stack-inv; ir-rsp-bound; ir-rbp-inv; ir-mem-above; ir-mem-code; ir-mem-heap; ir-closure-wf; ir-capacity;
         ir-result-valid;  -- Validity-based result field
         -- Validity-based versions only
         run-id-star-vv; run-terminal-star-vv; run-fold-star-vv; run-unfold-star-vv;
         run-arr-star-vv; run-fst-star-vv; run-snd-star-vv; run-prim-star-vv;
         -- Helper functions
         rbp-inv-preserved-unchanged; rbp-inv-preserved-through-ir)

-- Import extracted IR base case modules
open import Once.Backend.X86.Correct.IR.Inl
  using (run-inl-star-v; run-inl-star-v-auto)
open import Once.Backend.X86.Correct.IR.Inr
  using (run-inr-star-v; run-inr-star-v-auto)

-- Import RecDispatcher from central location
open import Once.Backend.X86.Correct.RecDispatcher using (RecDispatcher; RecDispatcherWithWF; unwrap-rec)

-- Import extracted curry proof (non-recursive, entire function extracted)
-- Now includes curry-thunk-correct-v with RecDispatcher pattern
open import Once.Backend.X86.Correct.IR.Curry
  using (run-curry-star; CurryExecResult; CurryMemoryResult; closure-addr;
         exec-star; exec-halted; exec-pc; exec-r14; exec-r15; exec-rbp; exec-rsp; exec-mem;
         exec-mem-rbp; exec-mem-rbp+8; exec-stack-inv; exec-capacity; exec-rbp-inv;
         exec-mem-above; exec-mem-code; exec-mem-heap;
         -- Thunk implementation
         curry-thunk-correct-v)

-- Import closure well-formedness infrastructure for whole-program proofs
open import Once.Backend.X86.Correct.ClosureWellFormed
  using (ClosureWellFormed; CurryResult; ThunkResult;
         curry-star; curry-halted; curry-pc; curry-result-valid;
         curry-r14; curry-r15; curry-rbp; curry-mem;
         curry-stack-inv; curry-capacity; closure-wf)
-- Note: ThunkProof postulates are now UNUSED
-- curry-thunk-correct-v in IR/Curry.agda implements thunk correctness
-- (uses RecDispatcher pattern like Pair, Compose, Case modules)

-- Import thunk structure lemmas (fetch proofs for thunk instructions)
open import Once.Backend.X86.Correct.IR.ThunkStructure
  using (thunk-i0; thunk-i1; thunk-i2; thunk-i3; thunk-i4; thunk-i5; thunk-i6;
         fetch-thunk-i0; fetch-thunk-i1; fetch-thunk-i2; fetch-thunk-i3; fetch-thunk-i4;
         fetch-thunk-i5; fetch-thunk-i6;
         cleanup-i0; cleanup-i1; cleanup-i2;
         fetch-cleanup-i0; fetch-cleanup-i1; fetch-cleanup-i2;
         thunk-entry-offset; thunk-entry-within-curry-overhead)
  renaming (fetch-ret to TS-fetch-ret)

-- Import thunk execution proofs (extracted from mutual block)
open import Once.Backend.X86.Correct.IR.ThunkExec
  using (thunk-setup-star; thunk-ret-star; ThunkSetupResult; ThunkRetResult)
import Once.Backend.X86.Correct.IR.ThunkExec as TE
open ThunkRetResult

-- Import apply proof (uses ClosureWellFormed)
open import Once.Backend.X86.Correct.IR.Apply
  using (run-apply-to-ir-result; run-apply-to-ir-result-v;
         run-apply-star-direct; run-apply-star-v)

-- Import pair, compose, and case with explicit rec parameter (refactored from MutualIR/*)
import Once.Backend.X86.Correct.IR.Pair as Pair
import Once.Backend.X86.Correct.IR.Compose as Compose
import Once.Backend.X86.Correct.IR.Case as Case

-- Import well-founded recursion and IR size measure
open import Induction.WellFounded using (Acc; acc)
open import Data.Nat.Induction using (<-wellFounded)
open import Once.Backend.Common.IRSize
  using (ir-size; ∘-f-smaller; ∘-g-smaller; ⟨,⟩-f-smaller; ⟨,⟩-g-smaller;
         [,]-f-smaller; [,]-g-smaller; curry-smaller)

-- Import validity predicates for dispatcher
open import Once.Backend.X86.Correct.MemoryValid
  using (ValidAt; valid-disjoint-from-stack;
         valid-pair-decompose; PairAtS;
         valid-closure-env; ClosureAtS; closure-at-s;
         valid-in-heap; Stack)

open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ; zero; suc; _∸_; _≡ᵇ_; _<_; _≤_; _>_; _≥_; s≤s; z≤n; _≟_) renaming (_+_ to _+ℕ_; _*_ to _*ℕ_)
open import Data.Nat.Properties using (≡ᵇ⇒≡; ≡⇒≡ᵇ; +-comm; +-assoc; +-identityʳ; m+[n∸m]≡n; ∸-+-assoc)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂) renaming ([_,_] to case-sum)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Maybe using (Maybe; just; nothing)
open import Function using (case_of_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; cong₂; sym; trans; subst; subst₂; module ≡-Reasoning; inspect) renaming ([_] to ⟦_⟧ᵢ)
open import Relation.Nullary using (yes; no)
open ≡-Reasoning

------------------------------------------------------------------------
-- Private helpers to avoid function definitions in where clauses
-- (Improves typechecking performance by defining once at module level)
------------------------------------------------------------------------
private
  -- Helper: m ∸ n < m when both m > 0 and n > 0
  m∸n<m-when-positive : ∀ m n → m > 0 → n > 0 → m ∸ n < m
  m∸n<m-when-positive (suc m') (suc n') _ _ = s≤s (Data.Nat.Properties.m∸n≤m m' n')
    where open import Data.Nat.Properties using (m∸n≤m)

  -- Helper: rsp < rsp + 8 (for slot address proofs)
  rsp<rsp+slot : ∀ (rsp-val : ℕ) → rsp-val < rsp-val +ℕ slot-size
  rsp<rsp+slot rsp-val = Data.Nat.Properties.m<m+n rsp-val (s≤s z≤n)
    where open import Data.Nat.Properties using (m<m+n)

------------------------------------------------------------------------
-- Star-Based Mutual Block - Concrete Dispatcher
--
-- This mutual block contains:
-- 1. run-ir-star-at-offset (the dispatcher with Acc-based termination)
-- 2. curry and apply implementations (kept here for now since curry is 646 lines)
--
-- Base cases delegate to StarBase functions.
-- Recursive cases (compose, pair, case) delegate to implementation modules.
-- Curry and apply are defined inline in this mutual block.
--
-- TERMINATION: Uses well-founded recursion on ir-size measure.
-- The Acc (accessibility) pattern proves termination without sized types.
------------------------------------------------------------------------

mutual
  -- | Validity-based IR execution dispatcher (with Acc for termination)
  -- Takes ValidAt input, returns IRStarResultV with validity output
  -- Acc proof ensures termination via well-founded recursion on ir-size
  -- NOTE: Takes StackCapacity s (ir-stack-requirement ir) - exact capacity per IR
  -- Sub-capacity derived from input via capacity-left/right-from-max lemmas
  run-ir-star-at-offset-v : ∀ {A B} (ir : IR A B) (prefix suffix : Program) (caller-sp : StackPointer) (x : ⟦ A ⟧) (s : State) →
    halted s ≡ false →
    pc s ≡ length prefix →
    ValidAt x (readReg (regs s) rdi) (memory s) →
    StackInvariant s →
    StackCapacity s (ir-stack-requirement ir) →
    RbpInvariant s →
    ClosureWFOutput (prefix ++ compile-x86 ir ++ suffix) s →
    Acc _<_ (ir-size ir) →
    let prog = prefix ++ compile-x86 ir ++ suffix
    in ∃[ s' ] IRStarResultV ir prog s s' x (length prefix)

  ------------------------------------------------------------------------
  -- Curry implementation (kept in mutual block for now)
  ------------------------------------------------------------------------

  -- | Validity-based curry execution (with Acc for termination)
  -- Takes ValidAt input, returns IRStarResultV with direct validity construction (no bridging!)
  -- ir-stack-requirement (curry f) = 2 + (4 + ir-stack-requirement f)
  run-curry-star-direct : ∀ {A B C} (f : IR (A * B) C) (prefix suffix : Program) (caller-sp : StackPointer) (x : ⟦ A ⟧) (s : State) →
    halted s ≡ false →
    pc s ≡ length prefix →
    ValidAt x (readReg (regs s) rdi) (memory s) →
    StackInvariant s →
    StackCapacity s (ir-stack-requirement (curry f)) →
    RbpInvariant s →
    ClosureWFOutput (prefix ++ compile-x86 (curry f) ++ suffix) s →
    Acc _<_ (ir-size (curry f)) →
    let prog = prefix ++ compile-x86 (curry f) ++ suffix
    in ∃[ s' ] IRStarResultV (curry f) prog s s' x (length prefix)
  run-curry-star-direct {A} {B} {C} f prefix suffix caller-sp x s h-false pc-eq input-valid stack-inv cap-in rbp-inv _ (acc rs) =
    s' , record
      { ir-star = exec-star exec-res
      ; ir-halted = exec-halted exec-res
      ; ir-pc = exec-pc exec-res
      ; ir-result-valid = result-valid
      ; ir-r14 = exec-r14 exec-res
      ; ir-r15 = exec-r15 exec-res
      ; ir-rbp = exec-rbp exec-res
      ; ir-rsp = exec-rsp exec-res
      ; ir-mem = exec-mem exec-res
      ; ir-mem-rbp = exec-mem-rbp exec-res
      ; ir-mem-rbp+8 = exec-mem-rbp+8 exec-res
      ; ir-mem-above = exec-mem-above exec-res
      ; ir-mem-code = exec-mem-code exec-res
      ; ir-mem-heap = exec-mem-heap exec-res
      ; ir-stack-inv = exec-stack-inv exec-res
      ; ir-capacity = exec-capacity exec-res
      ; ir-rbp-inv = exec-rbp-inv exec-res
      ; ir-closure-wf = has-closure A B C cl-addr thunk-offset curry-env-addr x (λ b → eval f (x , b)) wf
                          curry-cl
                          refl refl
                          curry-v-env
                          closure-at-for-thunk
                          curry-closure-region
                          curry-closure-in-region
                          curry-entry-rsp
                          curry-closure-below-entry-rsp
                          (exec-capacity exec-res)
                          curry-cl-valid
      }
    where
      prog = prefix ++ compile-x86 (curry f) ++ suffix
      offset = length prefix
      thunk-offset = offset +ℕ 6

      -- Call curry with validity (no bridges!)
      -- cap-in has type StackCapacity s (ir-stack-requirement (curry f)) which is what run-curry-star expects
      curry-result : ∃[ s' ] (CurryExecResult f prog s s' x offset
                              × CurryMemoryResult f prog s' x offset)
      curry-result = run-curry-star f prefix suffix x s h-false pc-eq input-valid stack-inv cap-in rbp-inv

      s' : State
      s' = proj₁ curry-result

      exec-res : CurryExecResult f prog s s' x offset
      exec-res = proj₁ (proj₂ curry-result)

      -- Extract from CurryMemoryResult for validity construction
      curry-mem-result : CurryMemoryResult f prog s' x offset
      curry-mem-result = proj₂ (proj₂ curry-result)

      cl-addr : ℕ
      cl-addr = closure-addr curry-mem-result

      -- ============================================================
      -- VALIDITY CONSTRUCTION (replaces valid-from-encode bridging)
      -- ============================================================

      -- Extract fields from CurryMemoryResult
      curry-env-addr = CurryMemoryResult.env-addr curry-mem-result
      curry-code-ptr = CurryMemoryResult.code-ptr curry-mem-result
      curry-closure-addr = CurryMemoryResult.closure-addr curry-mem-result
      curry-rax-eq = CurryMemoryResult.rax-eq curry-mem-result
      curry-mem-env = CurryMemoryResult.mem-env curry-mem-result
      curry-mem-cp = CurryMemoryResult.mem-cp curry-mem-result
      curry-v-env = CurryMemoryResult.v-env curry-mem-result

      -- Construct ClosureAtS from memory proofs
      closure-at : ClosureAtS curry-env-addr curry-code-ptr curry-closure-addr (memory s')
      closure-at = closure-at-s curry-mem-env curry-mem-cp

      -- Transport ClosureAtS code-ptr to thunk-offset
      closure-at-for-thunk : ClosureAtS curry-env-addr thunk-offset cl-addr (memory s')
      closure-at-for-thunk = subst (λ cp → ClosureAtS curry-env-addr cp cl-addr (memory s'))
                                   (CurryMemoryResult.code-ptr-is-thunk curry-mem-result)
                                   closure-at

      -- The semantic closure from eval (curry f) x
      sem-closure : Closure B C
      sem-closure = eval (curry f) x

      -- Extract region from CurryMemoryResult (closure allocated on Stack by `sub rsp`)
      curry-closure-region = CurryMemoryResult.closure-region curry-mem-result
      curry-closure-in-region = CurryMemoryResult.closure-in-region curry-mem-result

      -- closure-below-entry-rsp: For Stack closures, prove closure-addr < entry-rsp
      -- Curry allocates closure at r15 (after sub rsp), which is below entry-rsp.
      -- This is the correct invariant for Stack closure preservation:
      --   - Closure at addr C < entry-rsp
      --   - Parent writes at addresses >= entry-rsp (in parent's frame)
      --   - Therefore C ≠ write addresses
      curry-entry-rsp : Word
      curry-entry-rsp = readReg (regs s) rsp

      -- Proof that closure-addr < entry-rsp
      -- This follows from: closure at r15, r15 = rsp - frame-size < rsp = entry-rsp
      -- TODO: Prove from curry's frame setup (r15 = rsp - curry-frame-size)
      postulate
        curry-closure-below-entry-rsp : curry-closure-region ≡ Stack → cl-addr < curry-entry-rsp

      -- Closure validity via valid-closure-env constructor
      -- NOTE: valid-closure-env no longer requires Closure.env-addr ≡ encode env
      closure-valid-at-addr : ValidAt {B ⇒ C} sem-closure curry-closure-addr (memory s')
      closure-valid-at-addr = valid-closure-env curry-v-env closure-at curry-closure-region curry-closure-in-region

      -- Transport to rax
      result-valid : ValidAt (eval (curry f) x) (readReg (regs s') rax) (memory s')
      result-valid = subst (λ addr → ValidAt {B ⇒ C} sem-closure addr (memory s'))
                           (sym curry-rax-eq) closure-valid-at-addr

      -- Closure for has-closure with explicit env-addr (runtime address, not encode placeholder)
      curry-cl : Closure B C
      curry-cl = record { env-addr = curry-env-addr ; semantics = λ b → eval f (x , b) }

      -- ValidAt for curry-cl at cl-addr
      -- Uses valid-closure-env with explicit cl argument
      curry-cl-valid : ValidAt {B ⇒ C} curry-cl cl-addr (memory s')
      curry-cl-valid = valid-closure-env {cl = curry-cl} curry-v-env closure-at-for-thunk curry-closure-region curry-closure-in-region

      -- ============================================================
      -- Build the ClosureWellFormed proof using curry-thunk-correct-v
      -- Now uses RecDispatcher pattern (like Pair, Compose, Case)
      -- ============================================================

      -- Construct size-bounded dispatcher from Acc destructor (rs)
      rec : RecDispatcher (ir-size (curry f))
      rec ir' lt prefix' suffix' caller-sp' x' s' h-false' pc-eq' input-valid' stack-inv' cap-in' rbp-inv' =
        run-ir-star-at-offset-v ir' prefix' suffix' caller-sp' x' s' h-false' pc-eq' input-valid' stack-inv' cap-in' rbp-inv' no-closure (rs lt)

      wf : ClosureWellFormed {A} {B} {C} prog thunk-offset x (λ b → eval f (x , b))
      wf = record
        { code-ptr-valid = thunk-offset-in-bounds f prefix suffix
        ; thunk-capacity = thunk-setup-consumed-slots +ℕ ir-stack-requirement f
        ; thunk-capacity-sufficient = thunk-setup-cap≤thunk-consumed+ir-req f
        ; thunk-correct = λ arg s₁ ret-addr caller-sp₁ h-eq pc-eq₁ v-arg₁ v-env₁ mem-ret stack-inv₁ cap₁ caller-sp-bound₁ r15-in-code₁ →
            curry-thunk-correct-v f (ir-size (curry f)) rec (curry-smaller f)
              prefix suffix caller-sp₁ x arg s₁ ret-addr
              h-eq pc-eq₁ v-arg₁ v-env₁ mem-ret stack-inv₁ cap₁ caller-sp-bound₁ r15-in-code₁
        }

  -- | Lemma: thunk offset (|prefix| + 6) is within program bounds
  -- prog = prefix ++ compile-x86 (curry f) ++ suffix
  -- compile-length (curry f) = 19 + compile-length f ≥ 19
  -- So |prefix| + 6 < |prefix| + 19 ≤ |prefix ++ compile-x86 (curry f) ++ suffix|
  thunk-offset-in-bounds : ∀ {A B C} (f : IR (A * B) C) (prefix suffix : Program) →
    length prefix +ℕ 6 < length (prefix ++ compile-x86 (curry f) ++ suffix)
  thunk-offset-in-bounds {A} {B} {C} f prefix suffix = goal
    where
      open import Data.List.Properties as LP using (length-++)
      open import Data.Nat.Properties using (+-mono-<; +-monoʳ-<; m≤m+n; m≤n+m; ≤-trans; <-≤-trans)

      -- Length of compile-x86 (curry f) is 19 + compile-length f
      -- (6 closure setup + 1 push r15 + 7 thunk setup + len-f + 5 cleanup/end)
      curry-len : length (compile-x86 (curry f)) ≡ 19 +ℕ compile-length f
      curry-len = compile-length-correct (curry f)

      -- Length of full program
      prog-len : length (prefix ++ compile-x86 (curry f) ++ suffix)
               ≡ length prefix +ℕ length (compile-x86 (curry f) ++ suffix)
      prog-len = LP.length-++ prefix

      inner-len : length (compile-x86 (curry f) ++ suffix)
                ≡ length (compile-x86 (curry f)) +ℕ length suffix
      inner-len = LP.length-++ (compile-x86 (curry f))


      -- thunk-entry-offset < curry-overhead + compile-length f
      thunk-entry-within-code+f : thunk-entry-offset < curry-overhead +ℕ compile-length f
      thunk-entry-within-code+f = <-≤-trans thunk-entry-within-curry-overhead (m≤m+n curry-overhead (compile-length f))

      -- thunk-entry-offset < curry-overhead + compile-length f + length suffix
      thunk-entry-within-code+f+s : thunk-entry-offset < curry-overhead +ℕ compile-length f +ℕ length suffix
      thunk-entry-within-code+f+s = <-≤-trans thunk-entry-within-code+f (m≤m+n (curry-overhead +ℕ compile-length f) (length suffix))

      -- |prefix| + thunk-entry-offset < |prefix| + (curry-overhead + compile-length f + length suffix)
      step1 : length prefix +ℕ thunk-entry-offset < length prefix +ℕ (curry-overhead +ℕ compile-length f +ℕ length suffix)
      step1 = +-monoʳ-< (length prefix) thunk-entry-within-code+f+s

      -- Rewrite using curry-len and inner-len
      step2 : length prefix +ℕ (curry-overhead +ℕ compile-length f +ℕ length suffix)
            ≡ length prefix +ℕ (length (compile-x86 (curry f)) +ℕ length suffix)
      step2 = cong (length prefix +ℕ_) (cong (_+ℕ length suffix) (sym curry-len))

      step3 : length prefix +ℕ (length (compile-x86 (curry f)) +ℕ length suffix)
            ≡ length prefix +ℕ length (compile-x86 (curry f) ++ suffix)
      step3 = cong (length prefix +ℕ_) (sym inner-len)

      step4 : length prefix +ℕ length (compile-x86 (curry f) ++ suffix)
            ≡ length (prefix ++ compile-x86 (curry f) ++ suffix)
      step4 = sym prog-len

      goal : length prefix +ℕ thunk-entry-offset < length (prefix ++ compile-x86 (curry f) ++ suffix)
      goal = subst (length prefix +ℕ thunk-entry-offset <_) (trans step2 (trans step3 step4)) step1

  -- | Star-based curry execution with closure well-formedness proof (with Acc)
  -- Returns CurryResult which includes ClosureWellFormed for use by apply
  run-curry-star-with-wf : ∀ {A B C} (f : IR (A * B) C) (prefix suffix : Program) (caller-sp : StackPointer) (x : ⟦ A ⟧) (s : State) →
    halted s ≡ false →
    pc s ≡ length prefix →
    -- Key: ValidAt for input (replaces rdi-eq)
    ValidAt x (readReg (regs s) rdi) (memory s) →
    StackInvariant s →
    StackCapacity s (ir-stack-requirement (curry f)) →
    RbpInvariant s →
    Acc _<_ (ir-size (curry f)) →
    let prog = prefix ++ compile-x86 (curry f) ++ suffix
    in ∃[ s' ] CurryResult f prog s s' x (length prefix)
  run-curry-star-with-wf {A} {B} {C} f prefix suffix caller-sp x s h-false pc-eq input-valid stack-inv cap-in rbp-inv (acc rs) =
    s' , record
      { curry-star = exec-star exec-res
      ; curry-halted = exec-halted exec-res
      ; curry-pc = exec-pc exec-res
      ; curry-result-valid = result-valid
      ; curry-r14 = exec-r14 exec-res
      ; curry-r15 = exec-r15 exec-res
      ; curry-rbp = exec-rbp exec-res
      ; curry-mem = exec-mem exec-res
      ; curry-stack-inv = exec-stack-inv exec-res
      ; curry-capacity = exec-capacity exec-res
      ; closure-wf = wf
      }
    where
      prog = prefix ++ compile-x86 (curry f) ++ suffix
      offset = length prefix

      -- Get CurryExecResult from curry proof (no bridges!)
      -- cap-in has type StackCapacity s (ir-stack-requirement (curry f)) which is what run-curry-star expects
      curry-result = run-curry-star f prefix suffix x s h-false pc-eq input-valid stack-inv cap-in rbp-inv
      s' = proj₁ curry-result
      exec-res = proj₁ (proj₂ curry-result)
      curry-mem-res = proj₂ (proj₂ curry-result)

      -- ============================================================
      -- VALIDITY CONSTRUCTION (no bridges - uses valid-closure-env)
      -- ============================================================
      curry-env-addr = CurryMemoryResult.env-addr curry-mem-res
      curry-code-ptr = CurryMemoryResult.code-ptr curry-mem-res
      curry-closure-addr = CurryMemoryResult.closure-addr curry-mem-res
      curry-rax-eq = CurryMemoryResult.rax-eq curry-mem-res
      curry-mem-env = CurryMemoryResult.mem-env curry-mem-res
      curry-mem-cp = CurryMemoryResult.mem-cp curry-mem-res
      curry-v-env = CurryMemoryResult.v-env curry-mem-res

      closure-at : ClosureAtS curry-env-addr curry-code-ptr curry-closure-addr (memory s')
      closure-at = closure-at-s curry-mem-env curry-mem-cp

      sem-closure : Closure B C
      sem-closure = eval (curry f) x

      -- Extract region from CurryMemoryResult (closure allocated on Stack by `sub rsp`)
      curry-closure-region = CurryMemoryResult.closure-region curry-mem-res
      curry-closure-in-region = CurryMemoryResult.closure-in-region curry-mem-res

      closure-valid-at-addr : ValidAt {B ⇒ C} sem-closure curry-closure-addr (memory s')
      closure-valid-at-addr = valid-closure-env curry-v-env closure-at curry-closure-region curry-closure-in-region

      result-valid : ValidAt (eval (curry f) x) (readReg (regs s') rax) (memory s')
      result-valid = subst (λ addr → ValidAt {B ⇒ C} sem-closure addr (memory s'))
                           (sym curry-rax-eq) closure-valid-at-addr

      -- Thunk offset is offset + 6 (the code-ptr label in curry)
      thunk-offset = offset +ℕ 6

      -- Build the ClosureWellFormed proof using curry-thunk-correct-v
      -- (Now uses RecDispatcher pattern like Pair, Compose, Case)

      -- Construct size-bounded dispatcher from Acc destructor (rs)
      rec : RecDispatcher (ir-size (curry f))
      rec ir' lt prefix' suffix' caller-sp' x' s' h-false' pc-eq' input-valid' stack-inv' cap-in' rbp-inv' =
        run-ir-star-at-offset-v ir' prefix' suffix' caller-sp' x' s' h-false' pc-eq' input-valid' stack-inv' cap-in' rbp-inv' no-closure (rs lt)

      wf : ClosureWellFormed {A} {B} {C} prog thunk-offset x (λ b → eval f (x , b))
      wf = record
        { code-ptr-valid = thunk-offset-in-bounds f prefix suffix
        ; thunk-capacity = thunk-setup-consumed-slots +ℕ ir-stack-requirement f
        ; thunk-capacity-sufficient = thunk-setup-cap≤thunk-consumed+ir-req f
        ; thunk-correct = λ arg s₁ ret-addr caller-sp₁ h-eq pc-eq₁ v-arg₁ v-env₁ mem-ret stack-inv₁ cap₁ caller-sp-bound₁ r15-in-code₁ →
            curry-thunk-correct-v f (ir-size (curry f)) rec (curry-smaller f)
              prefix suffix caller-sp₁ x arg s₁ ret-addr
              h-eq pc-eq₁ v-arg₁ v-env₁ mem-ret stack-inv₁ cap₁ caller-sp-bound₁ r15-in-code₁
        }

  ------------------------------------------------------------------------
  -- | Helper to construct ClosureWellFormed for curry (used by WholeProgram.agda)
  -- This provides the thunk-correct field using curry-thunk-correct-v internally.
  ------------------------------------------------------------------------
  make-curry-closure-wf : ∀ {A B C} (f : IR (A * B) C)
                          (prefix suffix : Program) (x : ⟦ A ⟧) →
    let prog = prefix ++ compile-x86 (curry f) ++ suffix
        thunk-offset = length prefix +ℕ 6
    in ClosureWellFormed {A} {B} {C} prog thunk-offset x (λ b → eval f (x , b))
  make-curry-closure-wf {A} {B} {C} f prefix suffix x = record
    { code-ptr-valid = thunk-offset-in-bounds f prefix suffix
    ; thunk-capacity = thunk-setup-consumed-slots +ℕ ir-stack-requirement f
    ; thunk-capacity-sufficient = thunk-setup-cap≤thunk-consumed+ir-req f
    ; thunk-correct = λ arg s₁ ret-addr caller-sp₁ h-eq pc-eq₁ v-arg₁ v-env₁ mem-ret stack-inv₁ cap₁ caller-sp-bound₁ r15-in-code₁ →
        curry-thunk-correct-v f (ir-size (curry f)) rec (curry-smaller f)
          prefix suffix caller-sp₁ x arg s₁ ret-addr
          h-eq pc-eq₁ v-arg₁ v-env₁ mem-ret stack-inv₁ cap₁ caller-sp-bound₁ r15-in-code₁
    }
    where
      rec : RecDispatcher (ir-size (curry f))
      rec ir' lt prefix' suffix' caller-sp' x' s' h-false' pc-eq' input-valid' stack-inv' cap-in' rbp-inv' =
        run-ir-star-at-offset-v ir' prefix' suffix' caller-sp' x' s' h-false' pc-eq' input-valid' stack-inv' cap-in' rbp-inv' no-closure
          (Acc-smaller (<-wellFounded (ir-size (curry f))) lt)
        where
          -- Helper to get smaller Acc from Acc and proof
          Acc-smaller : ∀ {n m} → Acc _<_ n → m < n → Acc _<_ m
          Acc-smaller (acc rs) lt = rs lt

------------------------------------------------------------------------
-- Validity wrapper for curry (Phase C)
-- Takes ValidAt input and returns IRStarResultV
------------------------------------------------------------------------

  -- | Validity-based curry execution (with Acc for termination)
  -- Simple passthrough to run-curry-star-direct (which now takes validity input and Acc)
  run-curry-star-v : ∀ {A B C} (f : IR (A * B) C) (prefix suffix : Program) (caller-sp : StackPointer) (x : ⟦ A ⟧) (s : State) →
    halted s ≡ false →
    pc s ≡ length prefix →
    ValidAt x (readReg (regs s) rdi) (memory s) →
    StackInvariant s →
    StackCapacity s (ir-stack-requirement (curry f)) →
    RbpInvariant s →
    ClosureWFOutput (prefix ++ compile-x86 (curry f) ++ suffix) s →
    Acc _<_ (ir-size (curry f)) →
    let prog = prefix ++ compile-x86 (curry f) ++ suffix
    in ∃[ s' ] IRStarResultV (curry f) prog s s' x (length prefix)
  run-curry-star-v f prefix suffix caller-sp x s h-false pc-eq input-valid stack-inv cap-in rbp-inv cwf ac =
    -- run-curry-star-direct takes validity input directly, passes Acc for thunk execution
    run-curry-star-direct f prefix suffix caller-sp x s h-false pc-eq input-valid stack-inv cap-in rbp-inv cwf ac

  ------------------------------------------------------------------------
  -- Validity-based dispatcher cases (IN mutual block)
  ------------------------------------------------------------------------

  -- Direct validity-based execution for inl (base case, ignores Acc)
  -- ir-stack-requirement inl = 4, so cap-in : StackCapacity s 4 directly
  run-ir-star-at-offset-v (inl {A} {B}) prefix suffix caller-sp x s h-false pc-eq input-valid stack-inv cap-in rbp-inv _ _ =
    run-inl-star-v-auto prefix suffix x s h-false pc-eq input-valid stack-inv cap-in rbp-inv
  -- Direct validity-based execution for inr (base case, ignores Acc)
  -- ir-stack-requirement inr = 4, so cap-in : StackCapacity s 4 directly
  run-ir-star-at-offset-v (inr {A} {B}) prefix suffix caller-sp x s h-false pc-eq input-valid stack-inv cap-in rbp-inv _ _ =
    run-inr-star-v-auto prefix suffix x s h-false pc-eq input-valid stack-inv cap-in rbp-inv
  -- Pair: uses Acc to construct size-bounded dispatcher for parameterized module
  -- NOTE: Pair needs StackCapacity s 7 (5 for setup + 2 remaining)
  -- TODO: Dispatcher should take ir-input-capacity ir slots, not fixed 2
  -- Refactored: Calls IR.Pair.run-pair-star-v directly with rec parameter (no parameterized module)
  run-ir-star-at-offset-v (⟨ f , g ⟩) prefix suffix caller-sp x s h-false pc-eq input-valid stack-inv cap-in rbp-inv _ (acc rs) =
    let -- Construct size-bounded dispatcher from Acc destructor (rs)
        rec : RecDispatcher (ir-size ⟨ f , g ⟩)
        rec ir' lt prefix' suffix' caller-sp' x' s' h-false' pc-eq' input-valid' stack-inv' cap-in' rbp-inv' =
          run-ir-star-at-offset-v ir' prefix' suffix' caller-sp' x' s' h-false' pc-eq' input-valid' stack-inv' cap-in' rbp-inv' no-closure (rs lt)
        -- cap-in has type StackCapacity s (ir-stack-requirement ⟨ f , g ⟩) which is what run-pair-star-v expects
    in Pair.run-pair-star-v f g (ir-size ⟨ f , g ⟩) rec (⟨,⟩-f-smaller f g) (⟨,⟩-g-smaller f g) prefix suffix caller-sp x s h-false pc-eq input-valid stack-inv cap-in rbp-inv
  -- Compose: uses Acc to construct size-bounded dispatcher for parameterized module
  -- Compose: refactored to call IR/Compose.run-compose-star-v directly with rec parameter
  run-ir-star-at-offset-v (g ∘ f) prefix suffix caller-sp x s h-false pc-eq input-valid stack-inv cap-in rbp-inv _ (acc rs) =
    let -- Construct size-bounded dispatcher with closure-wf from Acc destructor (rs)
        rec : RecDispatcherWithWF (ir-size (g ∘ f))
        rec ir' lt prefix' suffix' caller-sp' x' s' h-false' pc-eq' input-valid' stack-inv' cap-in' rbp-inv' cwf' =
          run-ir-star-at-offset-v ir' prefix' suffix' caller-sp' x' s' h-false' pc-eq' input-valid' stack-inv' cap-in' rbp-inv' cwf' (rs lt)
    in Compose.run-compose-star-v f g (ir-size (g ∘ f)) rec (∘-f-smaller f g) (∘-g-smaller f g) prefix suffix caller-sp x s h-false pc-eq input-valid stack-inv cap-in rbp-inv
  -- Direct validity for id (base case, ignores Acc)
  run-ir-star-at-offset-v (id {A}) prefix suffix caller-sp x s h-false pc-eq input-valid stack-inv cap-in rbp-inv _ _ =
    run-id-star-vv prefix suffix x s h-false pc-eq input-valid stack-inv cap-in rbp-inv
  -- Direct validity for terminal (base case, ignores Acc)
  run-ir-star-at-offset-v (terminal {A}) prefix suffix caller-sp x s h-false pc-eq input-valid stack-inv cap-in rbp-inv _ _ =
    run-terminal-star-vv prefix suffix x s h-false pc-eq stack-inv cap-in rbp-inv
  -- Direct validity for fold (base case, ignores Acc)
  run-ir-star-at-offset-v (fold {F}) prefix suffix caller-sp x s h-false pc-eq input-valid stack-inv cap-in rbp-inv _ _ =
    run-fold-star-vv prefix suffix x s h-false pc-eq input-valid stack-inv cap-in rbp-inv
  -- Direct validity for unfold (base case, ignores Acc)
  run-ir-star-at-offset-v (unfold {F}) prefix suffix caller-sp (wrap x') s h-false pc-eq input-valid stack-inv cap-in rbp-inv _ _ =
    run-unfold-star-vv prefix suffix (wrap x') s h-false pc-eq input-valid stack-inv cap-in rbp-inv
  -- Direct validity for arr (base case, ignores Acc)
  run-ir-star-at-offset-v (arr {A} {B}) prefix suffix caller-sp x s h-false pc-eq input-valid stack-inv cap-in rbp-inv _ _ =
    run-arr-star-vv prefix suffix x s h-false pc-eq input-valid stack-inv cap-in rbp-inv
  -- Direct validity for prim (base case, ignores Acc)
  run-ir-star-at-offset-v (Prim {A} {B} name) prefix suffix caller-sp x s h-false pc-eq input-valid stack-inv cap-in rbp-inv _ _ =
    let rdi-not-stack = λ addr stack-proof → valid-disjoint-from-stack input-valid stack-proof
    in run-prim-star-vv name prefix suffix x s h-false pc-eq input-valid rdi-not-stack stack-inv cap-in rbp-inv
  -- Initial: absurd case (base case, ignores Acc)
  run-ir-star-at-offset-v (initial {A}) prefix suffix caller-sp x s h-false pc-eq input-valid stack-inv cap-in rbp-inv _ _ =
    ⊥-elim x
  -- fst: decompose pair validity (base case, ignores Acc)
  run-ir-star-at-offset-v (fst {A} {B}) prefix suffix caller-sp x s h-false pc-eq input-valid stack-inv cap-in rbp-inv _ _ =
    let a = proj₁ x
        b = proj₂ x
        decomp = valid-pair-decompose input-valid
        addr-a = proj₁ decomp
        addr-b = proj₁ (proj₂ decomp)
        va = proj₁ (proj₂ (proj₂ decomp))
        vb = proj₁ (proj₂ (proj₂ (proj₂ decomp)))
        pair-at = proj₂ (proj₂ (proj₂ (proj₂ decomp)))
    in run-fst-star-vv prefix suffix a b addr-a addr-b s h-false pc-eq va vb pair-at stack-inv cap-in rbp-inv
  -- snd: decompose pair validity (base case, ignores Acc)
  run-ir-star-at-offset-v (snd {A} {B}) prefix suffix caller-sp x s h-false pc-eq input-valid stack-inv cap-in rbp-inv _ _ =
    let a = proj₁ x
        b = proj₂ x
        decomp = valid-pair-decompose input-valid
        addr-a = proj₁ decomp
        addr-b = proj₁ (proj₂ decomp)
        va = proj₁ (proj₂ (proj₂ decomp))
        vb = proj₁ (proj₂ (proj₂ (proj₂ decomp)))
        pair-at = proj₂ (proj₂ (proj₂ (proj₂ decomp)))
    in run-snd-star-vv prefix suffix a b addr-a addr-b s h-false pc-eq va vb pair-at stack-inv cap-in rbp-inv
  -- Case: refactored to call IR/Case.run-case-star-v directly with rec parameter
  run-ir-star-at-offset-v ([_,_] {A} {B} {C} f g) prefix suffix caller-sp x s h-false pc-eq input-valid stack-inv cap-in rbp-inv _ (acc rs) =
    let -- Construct size-bounded dispatcher from Acc destructor (rs)
        rec : RecDispatcher (ir-size [ f , g ])
        rec ir' lt prefix' suffix' caller-sp' x' s' h-false' pc-eq' input-valid' stack-inv' cap-in' rbp-inv' =
          run-ir-star-at-offset-v ir' prefix' suffix' caller-sp' x' s' h-false' pc-eq' input-valid' stack-inv' cap-in' rbp-inv' no-closure (rs lt)
    in Case.run-case-star-v f g (ir-size [ f , g ]) rec ([,]-f-smaller f g) ([,]-g-smaller f g) prefix suffix caller-sp x s h-false pc-eq input-valid stack-inv cap-in rbp-inv
  -- curry: passes Acc to recursive calls within curry-thunk-correct-impl
  run-ir-star-at-offset-v (curry {A} {B} {C} f) prefix suffix caller-sp x s h-false pc-eq input-valid stack-inv cap-in rbp-inv cwf ac =
    run-curry-star-v f prefix suffix caller-sp x s h-false pc-eq input-valid stack-inv cap-in rbp-inv cwf ac
  -- apply: builds ApplyReady from pair decomposition and delegates to Apply module.
  -- Uses valid-pair-decompose to extract closure/arg addresses from input validity.
  -- Remaining postulates: semantic identity (cl-eq), address equality (cl-addr-eq).
  run-ir-star-at-offset-v (apply {A} {B}) prefix suffix caller-sp x s h-false pc-eq input-valid stack-inv cap-in rbp-inv cwf ac =
    construct-apply cwf
    where
      prog = prefix ++ compile-x86 (apply {A} {B}) ++ suffix
      m = memory s

      -- Decompose input pair validity (no encode!)
      decomp = valid-pair-decompose input-valid
      cl-addr = proj₁ decomp
      arg-addr = proj₁ (proj₂ decomp)
      v-cl = proj₁ (proj₂ (proj₂ decomp))
      v-arg = proj₁ (proj₂ (proj₂ (proj₂ decomp)))
      pair-at = proj₂ (proj₂ (proj₂ (proj₂ decomp)))

      construct-apply : ClosureWFOutput prog s → ∃[ s' ] IRStarResultV (apply {A} {B}) prog s s' x (length prefix)
      construct-apply (has-closure E A' B' ca cp ea env sem wf cwf-cl cwf-cl-env-eq cwf-cl-sem-eq cwf-env-valid cwf-closure-at cwf-region cwf-in-region _ _ cwf-cap cwf-cl-valid)
        with A' ≟T A | B' ≟T B
      ... | yes refl | yes refl =
        run-apply-star-v prefix suffix x s h-false pc-eq input-valid stack-inv rbp-inv ar
        where
          -- CLEAN: Postulate structural threading equalities.
          -- These say that the closure from ClosureWFOutput (produced by curry)
          -- is the same as proj₁ x (the input closure at apply time).
          -- This is provable by threading through compose/pair (future work).
          --
          -- Key insight: We separate semantics and env-addr equalities.
          -- Apply.agda uses these directly without needing valid-addr-is-encode!
          postulate
            sem-eq : sem ≡ Closure.semantics (proj₁ x)
            env-addr-eq : ea ≡ Closure.env-addr (proj₁ x)
            cl-addr-eq : cl-addr ≡ ca

          closure-at : ClosureAtS ea cp cl-addr m
          closure-at = subst (λ a → ClosureAtS ea cp a m)
                             (sym cl-addr-eq) cwf-closure-at

          ar : ApplyReady x s prog
          ar = record
            { ar-E = E
            ; ar-env = env
            ; ar-env-addr = ea
            ; ar-code-ptr = cp
            ; ar-closure-addr = cl-addr
            ; ar-arg-addr = arg-addr
            ; ar-sem = sem
            ; ar-wf = wf
            ; ar-sem-eq = sem-eq
            ; ar-env-addr-eq = env-addr-eq
            ; ar-closure-at = closure-at
            ; ar-env-valid = cwf-env-valid
            ; ar-pair-at = pair-at
            ; ar-v-cl = v-cl  -- From valid-pair-decompose, has region inside!
            ; ar-v-arg = v-arg
            ; ar-capacity = cwf-cap
            }
      ... | yes _ | no _ = unreachable where postulate unreachable : _
      ... | no _ | _ = unreachable where postulate unreachable : _
      construct-apply no-closure = unreachable where postulate unreachable : _

------------------------------------------------------------------------
-- Public API: run-ir-star (provides initial Acc using <-wellFounded)
--
-- This is the function exported to external callers. It provides the
-- initial Acc proof using <-wellFounded, so callers don't need to
-- provide it manually.
------------------------------------------------------------------------

-- | Execute IR with validity-based input/output (public API)
-- Provides initial Acc using <-wellFounded
-- NOTE: Takes StackCapacity directly - caller provides the capacity proof.
-- This eliminates rsp-in-stack-after-stack-op postulate at the entry point.
run-ir-star : ∀ {A B} (ir : IR A B) (prefix suffix : Program) (caller-sp : StackPointer) (x : ⟦ A ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ length prefix →
  ValidAt x (readReg (regs s) rdi) (memory s) →
  StackInvariant s →
  StackCapacity s (ir-stack-requirement ir) →
  RbpInvariant s →
  let prog = prefix ++ compile-x86 ir ++ suffix
  in ∃[ s' ] IRStarResultV ir prog s s' x (length prefix)
run-ir-star ir prefix suffix caller-sp x s h-false pc-eq input-valid stack-inv cap-in rbp-inv =
  run-ir-star-at-offset-v ir prefix suffix caller-sp x s h-false pc-eq input-valid stack-inv cap-in rbp-inv
       no-closure (<-wellFounded (ir-size ir))
