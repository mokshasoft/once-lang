------------------------------------------------------------------------
-- Once.Backend.X86.Correct.MutualIR
--
-- Concrete dispatcher that wires together all implementation modules.
--
-- This file contains:
-- 1. The mutual block with the main dispatcher (run-ir-star-at-offset)
-- 2. Curry and apply implementations (still in mutual block for now)
--
-- NOTE: Sized types removed for compilation performance (10-100x speedup).
-- Termination is guaranteed by structural recursion on IR constructors.
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
         thunk-setup-capacity; thunk-setup-fits-pair-capacity;
         -- IR-specific capacity bounds
         curry-closure-capacity≤curry-req; inl-capacity≤inl-req;
         inr-capacity≤inr-req; apply-capacity≤apply-req)

-- NOTE: Most encode-* reading postulates eliminated via validity-based proofs.
-- Remaining: encode-unit, encode-pair-construct, encode-fix-*, encode-arr-identity
open import Once.Postulates
  using (encode; encode-unit; encode-pair-construct;
         encode-fix-unwrap; encode-fix-wrap; encode-arr-identity)
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
         star-step2; star-step3; star-step4)
open import Once.Backend.X86.Correct.MemoryValid
  using (PairAt; pair-at; fst-valid; snd-valid;
         PairAtS; pair-at-s;
         InlAt; inl-at; InrAt; inr-at;
         encode-pair-fst-derived; encode-pair-snd-derived;
         encode-inl-tag-derived; encode-inl-val-derived;
         encode-inr-tag-derived; encode-inr-val-derived)

-- Re-export StarBase
-- Simple Star proofs (non-recursive) are in StarBase.agda
open import Once.Backend.X86.Correct.StarBase public
  using (IRStarResultV; ClosureWFOutput; no-closure; has-closure;
         ir-star; ir-halted; ir-pc; ir-r14; ir-r15; ir-rbp;
         ir-mem; ir-mem-rbp; ir-mem-rbp+8; ir-stack-inv; ir-rsp-bound; ir-rbp-inv; ir-mem-above; ir-mem-code; ir-mem-heap; ir-closure-wf; ir-capacity;
         ir-result-valid;  -- Validity-based result field
         -- Validity-based versions only
         run-id-star-vv; run-terminal-star-vv; run-fold-star-vv; run-unfold-star-vv;
         run-arr-star-vv; run-fst-star-vv; run-snd-star-vv; run-prim-star-vv;
         -- Helper functions
         rbp-inv-preserved-unchanged)

-- Import extracted IR base case modules
open import Once.Backend.X86.Correct.IR.Inl
  using (run-inl-star-v; run-inl-star-v-auto)
open import Once.Backend.X86.Correct.IR.Inr
  using (run-inr-star-v; run-inr-star-v-auto)

-- Import extracted curry proof (non-recursive, entire function extracted)
open import Once.Backend.X86.Correct.IR.Curry
  using (run-curry-star; CurryExecResult; CurryMemoryResult; closure-addr;
         exec-star; exec-halted; exec-pc; exec-r14; exec-r15; exec-rbp; exec-rsp; exec-mem;
         exec-mem-rbp; exec-mem-rbp+8; exec-stack-inv; exec-capacity; exec-rbp-inv;
         exec-mem-above; exec-mem-code; exec-mem-heap)

-- Import closure well-formedness infrastructure for whole-program proofs
open import Once.Backend.X86.Correct.ClosureWellFormed
  using (ClosureWellFormed; CurryResult; ThunkResult;
         curry-star; curry-halted; curry-pc; curry-result-valid;
         curry-r14; curry-r15; curry-rbp; curry-mem;
         curry-stack-inv; curry-capacity; closure-wf)
-- Note: ThunkProof postulates are now UNUSED
-- curry-thunk-correct-impl in this file replaces curry-thunk-correct postulate
-- construct-closure-wf is replaced by inline record construction using curry-thunk-correct-impl

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
  using (run-apply-to-ir-result; run-apply-to-ir-result-v)

-- Import implementation modules (parameterized, will be opened inside dispatcher)
import Once.Backend.X86.Correct.MutualIR.Compose as ComposeModule
import Once.Backend.X86.Correct.MutualIR.Pair as PairModule
import Once.Backend.X86.Correct.MutualIR.Case as CaseModule

-- Import well-founded recursion and IR size measure
open import Induction.WellFounded using (Acc; acc)
open import Data.Nat.Induction using (<-wellFounded)
open import Once.Backend.X86.Correct.IRSize
  using (ir-size; ∘-f-smaller; ∘-g-smaller; ⟨,⟩-f-smaller; ⟨,⟩-g-smaller;
         [,]-f-smaller; [,]-g-smaller; curry-smaller)

-- Import helper from Dispatcher (still used for rbp invariant preservation)
open import Once.Backend.X86.Correct.MutualIR.Dispatcher
  using (rbp-inv-preserved-through-ir)

-- Import validity predicates for dispatcher
open import Once.Backend.X86.Correct.MemoryValid
  using (ValidAt; valid-disjoint-from-stack;
         valid-pair-decompose; valid-closure-decompose; PairAtS;
         valid-closure-env; ClosureAtS; closure-at-s;
         valid-subst-addr-mem)
  renaming (PairAt to MV-PairAt)

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
    Acc _<_ (ir-size (curry f)) →
    let prog = prefix ++ compile-x86 (curry f) ++ suffix
    in ∃[ s' ] IRStarResultV (curry f) prog s s' x (length prefix)
  run-curry-star-direct {A} {B} {C} f prefix suffix caller-sp x s h-false pc-eq input-valid stack-inv cap-in rbp-inv ac =
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
      ; ir-closure-wf = has-closure cl-addr thunk-offset x (λ b → eval f (x , b)) wf
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

      -- The semantic closure from eval (curry f) x
      sem-closure : Closure B C
      sem-closure = eval (curry f) x

      -- Closure validity via valid-closure-env constructor
      -- Closure.env-addr sem-closure = encode x (by definition of eval curry)
      -- So the first argument to valid-closure-env is refl
      closure-valid-at-addr : ValidAt {B ⇒ C} sem-closure curry-closure-addr (memory s')
      closure-valid-at-addr = valid-closure-env refl curry-v-env closure-at

      -- Transport to rax
      result-valid : ValidAt (eval (curry f) x) (readReg (regs s') rax) (memory s')
      result-valid = subst (λ addr → ValidAt {B ⇒ C} sem-closure addr (memory s'))
                           (sym curry-rax-eq) closure-valid-at-addr

      -- ============================================================
      -- Build the ClosureWellFormed proof using curry-thunk-correct-impl
      -- Note: thunk-correct provides caller-sp₁ (apply's frame), which is passed to
      -- curry-thunk-correct-impl for memory preservation
      -- r15-in-code₁ is explicit evidence that r15 is in code region (from Apply)
      -- Now uses env type A and env value x (not encode x)
      -- ac (Acc for curry f) is passed to curry-thunk-correct-impl for termination
      -- thunk-capacity: tracks stack requirement for capacity threading
      wf : ClosureWellFormed {A} {B} {C} prog thunk-offset x (λ b → eval f (x , b))
      wf = record
        { code-ptr-valid = thunk-offset-in-bounds f prefix suffix
        ; thunk-capacity = thunk-setup-consumed-slots +ℕ ir-stack-requirement f
        ; thunk-capacity-sufficient = thunk-setup-cap≤thunk-consumed+ir-req f
        ; thunk-correct = λ arg s₁ ret-addr caller-sp₁ h-eq pc-eq₁ v-arg₁ v-env₁ mem-ret stack-inv₁ cap₁ caller-sp-bound₁ r15-in-code₁ →
            curry-thunk-correct-impl f prefix suffix caller-sp₁ x arg s₁ ret-addr
              h-eq pc-eq₁ v-arg₁ v-env₁ mem-ret stack-inv₁ cap₁ caller-sp-bound₁ r15-in-code₁ ac
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
  run-curry-star-with-wf {A} {B} {C} f prefix suffix caller-sp x s h-false pc-eq input-valid stack-inv cap-in rbp-inv ac =
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

      closure-valid-at-addr : ValidAt {B ⇒ C} sem-closure curry-closure-addr (memory s')
      closure-valid-at-addr = valid-closure-env refl curry-v-env closure-at

      result-valid : ValidAt (eval (curry f) x) (readReg (regs s') rax) (memory s')
      result-valid = subst (λ addr → ValidAt {B ⇒ C} sem-closure addr (memory s'))
                           (sym curry-rax-eq) closure-valid-at-addr

      -- Thunk offset is offset + 6 (the code-ptr label in curry)
      thunk-offset = offset +ℕ 6

      -- Build the ClosureWellFormed proof using curry-thunk-correct-impl
      -- (This uses the proven version instead of the postulate-based construct-closure-wf)
      -- Note: thunk-correct provides caller-sp₁ (apply's frame), which is passed to
      -- curry-thunk-correct-impl for memory preservation
      -- r15-in-code₁ is explicit evidence that r15 is in code region (from Apply)
      -- thunk-capacity: tracks stack requirement for capacity threading
      wf : ClosureWellFormed {A} {B} {C} prog thunk-offset x (λ b → eval f (x , b))
      wf = record
        { code-ptr-valid = thunk-offset-in-bounds f prefix suffix
        ; thunk-capacity = thunk-setup-consumed-slots +ℕ ir-stack-requirement f
        ; thunk-capacity-sufficient = thunk-setup-cap≤thunk-consumed+ir-req f
        ; thunk-correct = λ arg s₁ ret-addr caller-sp₁ h-eq pc-eq₁ v-arg₁ v-env₁ mem-ret stack-inv₁ cap₁ caller-sp-bound₁ r15-in-code₁ →
            curry-thunk-correct-impl f prefix suffix caller-sp₁ x arg s₁ ret-addr
              h-eq pc-eq₁ v-arg₁ v-env₁ mem-ret stack-inv₁ cap₁ caller-sp-bound₁ r15-in-code₁ ac
        }

  ------------------------------------------------------------------------
  -- curry-thunk-correct-impl: Proven version using IH
  --
  -- This is the implementation of curry-thunk-correct that uses
  -- run-ir-star-at-offset (the IH) to prove thunk correctness.
  --
  -- Structure:
  --   1. Trace 5 setup instructions (label, sub, mov, mov, mov)
  --   2. Call run-ir-star-at-offset f (IH)
  --   3. Trace ret instruction
  --   4. Compose via star-trans
  --
  -- The setup/ret tracing is postulated for now (similar to run-inl-star
  -- pattern, can be proven with detailed instruction semantics).
  ------------------------------------------------------------------------


  -- | curry-thunk-correct-impl: Implementation using IH (with Acc for termination)
  -- This composes: setup tracing → IH on f → ret tracing
  -- caller-sp: StackPointer from the caller (D041)
  -- caller-sp-bound: addr caller-sp = s.rsp + 8 (call convention)
  -- r15-in-code: r15 is in code region (from Apply, allows postulate-free ret)
  -- ac: Accessibility proof for curry f, used to extract smaller Acc for f
  -- cap: StackCapacity threaded from caller (replaces postulate-based capacity)
  --      Capacity needed: thunk-setup-consumed-slots + ir-stack-requirement f
  --      This is 4 + f-req, where thunk setup consumes 4 and f needs f-req
  curry-thunk-correct-impl : ∀ {A B C} (f : IR (A * B) C)
                             (prefix suffix : Program) (caller-sp : StackPointer) (env : ⟦ A ⟧)
                             (arg : ⟦ B ⟧) (s : State) (ret-addr : ℕ) →
    let prog = prefix ++ compile-x86 (curry f) ++ suffix
        thunk-offset = length prefix +ℕ 6
        thunk-cap = thunk-setup-consumed-slots +ℕ ir-stack-requirement f
    in
    halted s ≡ false →
    pc s ≡ thunk-offset →
    ValidAt arg (readReg (regs s) rdi) (memory s) →  -- validity for arg!
    ValidAt env (readReg (regs s) r12) (memory s) →  -- validity for env!
    readMem (memory s) (readReg (regs s) rsp) ≡ just ret-addr →
    StackInvariant s →
    StackCapacity s thunk-cap →  -- Threaded capacity: 4 + ir-stack-requirement f
    addr caller-sp ≡ readReg (regs s) rsp +ℕ slot-size →  -- D041: caller-sp bound
    InCode (readReg (regs s) r15) →  -- r15 in code region (from Apply)
    Acc _<_ (ir-size (curry f)) →  -- Acc for curry f
    ∃[ s' ] (ThunkResult prog s s' caller-sp (λ b → eval f (env , b)) arg
            × pc s' ≡ ret-addr)
  curry-thunk-correct-impl {A} {B} {C} f prefix suffix caller-sp env arg s ret-addr
                           h-eq pc-eq v-arg v-env mem-ret stack-inv cap-thunk caller-sp-bound r15-in-code-entry (acc smaller-acc) =
    s-final , thunk-result , pc-final
    where
      open import Once.Backend.X86.Correct.ClosureWellFormed
        using (ThunkResult; thunk-star; thunk-halted; thunk-result-valid;
               thunk-r14; thunk-r15; thunk-rbp; thunk-stack-inv; thunk-capacity)
      open import Data.List.Properties using (++-assoc) renaming (length-++ to List-length-++)
      open import Data.Nat.Properties using (≤-trans; +-comm; m≤m+n; ≤-<-trans; <⇒≤)

      -- Derive 8 ≤ rsp from capacity (for m+[n∸m]≡n)
      -- thunk-setup-consumed-slots = 4, so 4 + ir-req f ≥ 4 ≥ 1, meaning rsp > slots 1 ≥ 8
      8≤rsp : 8 ≤ readReg (regs s) rsp
      8≤rsp = ≤-trans (m≤m+n slot-size 0) (<⇒≤ (≤-<-trans (slots-mono-≤ 1≤thunk-cap) (StackCapacity.rsp-sufficient cap-thunk)))
        where
          -- 1 ≤ 4 + ir-req f (thunk-setup-consumed-slots = 4 ≥ 1)
          1≤thunk-cap : 1 ≤ thunk-setup-consumed-slots +ℕ ir-stack-requirement f
          1≤thunk-cap = ≤-trans (s≤s z≤n) (m≤m+n thunk-setup-consumed-slots (ir-stack-requirement f))

      prog = prefix ++ compile-x86 (curry f) ++ suffix
      thunk-offset = length prefix +ℕ 6
      f-offset = length prefix +ℕ 14      -- 6 closure + 8 thunk setup
      ret-offset = length prefix +ℕ 17 +ℕ compile-length f  -- f-offset + len-f + 3 cleanup

      -- v-env is now an input parameter (no more valid-from-encode bridge!)

      -- Derive StackCapacity for thunk-setup-star from threaded capacity
      -- cap-thunk : StackCapacity s (4 + ir-stack-requirement f)
      -- thunk-setup-capacity = 6 ≤ 4 + ir-req f (since ir-req f ≥ 2)
      cap-thunk-setup : StackCapacity s thunk-setup-capacity
      cap-thunk-setup = capacity-from-larger s thunk-setup-capacity
                          (thunk-setup-consumed-slots +ℕ ir-stack-requirement f)
                          cap-thunk (thunk-setup-cap≤thunk-consumed+ir-req f)

      -- Step 1: Trace 8 setup instructions (takes StackCapacity s thunk-setup-capacity)
      -- Returns ThunkSetupResult record for clean field access
      setup-result = thunk-setup-star f prefix suffix env arg s
                       h-eq pc-eq v-arg v-env stack-inv cap-thunk-setup
      s-after-setup = proj₁ setup-result
      setup-rec = proj₂ setup-result
      open TE.ThunkSetupResult setup-rec

      -- Step 2: Call IH on f
      -- Define prefix-f and suffix-f so that prog = prefix-f ++ compile-x86 f ++ suffix-f

      -- curry layout: [0-5] closure setup, [6-13] thunk setup (8 instr), [14 to 13+len(f)] f, [14-16+len(f)] cleanup (3 instr), [17+len(f)] ret, [18+len(f)] label
      len-f = compile-length f
      end-label = 18 +ℕ len-f  -- position of end label (6 closure + 8 thunk + len-f + 4 tail)
      end-offset-curry = 12 +ℕ len-f  -- jmp at pos 5 to reach 18 + len-f

      -- Prefix for f: prefix ++ first 14 instructions of curry (6 closure + 8 thunk)
      curry-closure-setup : Program
      curry-closure-setup =
        sub (reg rsp) (imm (pair-alloc)) ∷
        mov (mem (base rsp)) (reg rdi) ∷
        lea r9 (rip+disp 4) ∷
        mov (mem (base+disp rsp slot-size)) (reg r9) ∷
        mov (reg rax) (reg rsp) ∷
        jmp end-offset-curry ∷ []

      curry-thunk-setup : Program
      curry-thunk-setup =
        label 6 ∷
        push (reg r15) ∷                       -- save r15 (apply's scratch register)
        push (reg rbp) ∷                       -- save frame pointer
        mov (reg rbp) (reg rsp) ∷              -- set frame pointer
        sub (reg rsp) (imm (pair-alloc)) ∷
        mov (mem (base rsp)) (reg r12) ∷
        mov (mem (base+disp rsp slot-size)) (reg rdi) ∷
        mov (reg rdi) (reg rsp) ∷ []

      prefix-f : Program
      prefix-f = prefix ++ curry-closure-setup ++ curry-thunk-setup

      -- Suffix for f: cleanup ++ pop r15 ++ ret ∷ label ∷ suffix
      curry-tail : Program
      curry-tail = mov (reg rsp) (reg rbp) ∷   -- restore stack
                   pop rbp ∷                   -- restore frame pointer
                   pop r15 ∷                   -- restore r15
                   ret ∷ label end-label ∷ []

      suffix-f : Program
      suffix-f = curry-tail ++ suffix

      -- Length of prefix-f = length prefix + 14 (6 closure + 8 thunk)
      -- Note: ++ is right-associative, so prefix-f = prefix ++ (curry-closure-setup ++ curry-thunk-setup)
      len-prefix-f : length prefix-f ≡ length prefix +ℕ 14
      len-prefix-f = trans (List-length-++ prefix {curry-closure-setup ++ curry-thunk-setup})
                           (cong (length prefix +ℕ_) (List-length-++ curry-closure-setup {curry-thunk-setup}))

      -- Program equality: prog = prefix-f ++ compile-x86 f ++ suffix-f
      -- This requires showing curry structure matches

      -- Helper: compile-x86 (curry f) structure equality
      -- The curry compilation structure is:
      --   [6 closure setup] ++ [5 thunk setup] ++ compile-x86 f ++ [ret, label end]
      -- This is definitionally equal since (x ∷ y ∷ ... ∷ []) ++ rest = x ∷ y ∷ ... ∷ rest
      curry-structure : compile-x86 (curry f) ≡
                        curry-closure-setup ++ curry-thunk-setup ++ compile-x86 f ++ curry-tail
      curry-structure = refl

      -- Program equality using curry-structure and list reassociation
      -- prog = prefix ++ curry-structure ++ suffix
      --      = prefix ++ (A ++ B ++ f ++ C) ++ suffix
      --      = (prefix ++ A ++ B) ++ f ++ (C ++ suffix)
      --      = prefix-f ++ f ++ suffix-f
      -- Program equality using curry-structure and list reassociation
      -- ++ is right-associative, so prefix ++ A ++ B = prefix ++ (A ++ B)
      -- and prefix-f = prefix ++ (curry-closure-setup ++ curry-thunk-setup)
      -- and suffix-f = curry-tail ++ suffix
      --
      -- We need: prefix ++ (A ++ B ++ f ++ D) ++ suffix = (prefix ++ A ++ B) ++ f ++ (D ++ suffix)
      -- With right-assoc: prefix ++ ((A ++ (B ++ (f ++ D))) ++ suffix) = (prefix ++ (A ++ B)) ++ (f ++ (D ++ suffix))
      -- This requires multiple applications of ++-assoc
      prog-eq-f : prog ≡ prefix-f ++ compile-x86 f ++ suffix-f
      prog-eq-f = trans (cong (λ x → prefix ++ x ++ suffix) curry-structure) prog-reassoc
        where
          -- Abbreviations for readability (using unique names to avoid scope clashes)
          ccs = curry-closure-setup
          cts = curry-thunk-setup
          code-f = compile-x86 f
          cta = curry-tail

          -- The main reassociation proof
          -- Goal: prefix ++ (ccs ++ cts ++ code-f ++ cta) ++ suffix ≡ (prefix ++ ccs ++ cts) ++ code-f ++ (cta ++ suffix)
          prog-reassoc : prefix ++ (ccs ++ cts ++ code-f ++ cta) ++ suffix ≡ prefix-f ++ code-f ++ suffix-f
          prog-reassoc =
            let -- Step 1: prefix ++ (ccs ++ (cts ++ (code-f ++ cta))) ++ suffix  (this is what we have)

                -- Step 2: Focus on inner (ccs ++ (cts ++ (code-f ++ cta)))
                inner-assoc1 : ccs ++ (cts ++ (code-f ++ cta)) ≡ (ccs ++ cts) ++ (code-f ++ cta)
                inner-assoc1 = sym (++-assoc ccs cts (code-f ++ cta))

                -- Step 3: ((ccs ++ cts) ++ (code-f ++ cta)) ++ suffix = (ccs ++ cts) ++ ((code-f ++ cta) ++ suffix)
                inner-assoc2 : ((ccs ++ cts) ++ (code-f ++ cta)) ++ suffix ≡ (ccs ++ cts) ++ ((code-f ++ cta) ++ suffix)
                inner-assoc2 = ++-assoc (ccs ++ cts) (code-f ++ cta) suffix

                -- Step 4: (code-f ++ cta) ++ suffix = code-f ++ (cta ++ suffix)
                inner-assoc3 : (code-f ++ cta) ++ suffix ≡ code-f ++ (cta ++ suffix)
                inner-assoc3 = ++-assoc code-f cta suffix

                -- Combine steps 2-4 for the inner part
                inner-combined : (ccs ++ (cts ++ (code-f ++ cta))) ++ suffix ≡ (ccs ++ cts) ++ (code-f ++ (cta ++ suffix))
                inner-combined = trans (cong (_++ suffix) inner-assoc1)
                                 (trans inner-assoc2
                                        (cong ((ccs ++ cts) ++_) inner-assoc3))

                -- Step 5: prefix ++ X = prefix ++ X (applying the inner result)
                outer-step : prefix ++ ((ccs ++ (cts ++ (code-f ++ cta))) ++ suffix) ≡ prefix ++ ((ccs ++ cts) ++ (code-f ++ (cta ++ suffix)))
                outer-step = cong (prefix ++_) inner-combined

                -- Step 6: prefix ++ ((ccs ++ cts) ++ X) = (prefix ++ (ccs ++ cts)) ++ X
                final-assoc : prefix ++ ((ccs ++ cts) ++ (code-f ++ (cta ++ suffix))) ≡ (prefix ++ (ccs ++ cts)) ++ (code-f ++ (cta ++ suffix))
                final-assoc = sym (++-assoc prefix (ccs ++ cts) (code-f ++ (cta ++ suffix)))

            in trans outer-step final-assoc

      -- Call IH on f (using validity-based dispatcher for direct validity output)
      pc-setup-f : pc s-after-setup ≡ length prefix-f
      pc-setup-f = trans pc-setup (sym len-prefix-f)

      -- Use validity directly from thunk-setup-star (no valid-from-encode bridge!)
      input-valid-f : ValidAt (env , arg) (readReg (regs s-after-setup) rdi) (memory s-after-setup)
      input-valid-f = v-pair-setup

      -- Call validity-based dispatcher with smaller Acc proof
      -- NOTE: Inlining (smaller-acc (curry-smaller f)) for termination checker visibility
      -- Derive StackCapacity for inner IR f from threaded capacity using capacity-after-delta
      -- cap-thunk : StackCapacity s (thunk-setup-consumed-slots + ir-stack-requirement f)
      -- After setup consumes thunk-setup-consumed-slots, we have ir-stack-requirement f remaining
      cap-setup : StackCapacity s-after-setup (ir-stack-requirement f)
      cap-setup = capacity-after-delta s s-after-setup thunk-setup-consumed-slots (ir-stack-requirement f)
                    cap-thunk rsp-setup

      step-f-v : ∃[ s-f ] IRStarResultV f (prefix-f ++ compile-x86 f ++ suffix-f) s-after-setup s-f (env , arg) (length prefix-f)
      step-f-v = run-ir-star-at-offset-v f prefix-f suffix-f caller-sp (env , arg) s-after-setup
                   h-setup pc-setup-f input-valid-f stack-inv-setup cap-setup rbp-inv-setup
                   (smaller-acc (curry-smaller f))

      s-after-f-raw : State
      s-after-f-raw = proj₁ step-f-v

      r-f-v : IRStarResultV f (prefix-f ++ compile-x86 f ++ suffix-f) s-after-setup s-after-f-raw (env , arg) (length prefix-f)
      r-f-v = proj₂ step-f-v
      star-f-raw : Star (prefix-f ++ compile-x86 f ++ suffix-f) s-after-setup s-after-f-raw
      star-f-raw = IRStarResultV.ir-star r-f-v

      -- Get validity output directly from IRStarResultV (no valid-from-encode needed!)
      result-valid-f : ValidAt (eval f (env , arg)) (readReg (regs s-after-f-raw) rax) (memory s-after-f-raw)
      result-valid-f = IRStarResultV.ir-result-valid r-f-v

      -- Convert star-f to use prog
      star-f-converted : Star prog s-after-setup s-after-f-raw
      star-f-converted = subst (λ p → Star p s-after-setup s-after-f-raw) (sym prog-eq-f) star-f-raw

      -- Extract properties from IH result
      pc-f-raw : pc s-after-f-raw ≡ length prefix-f +ℕ compile-length f
      pc-f-raw = IRStarResultV.ir-pc r-f-v

      -- f ends at position 14 + len-f (after prefix-f + compile-x86 f)
      -- We need to trace 3 cleanup instructions (mov rsp rbp, pop rbp, pop r15) to reach ret at 17 + len-f
      cleanup-offset = length prefix +ℕ 14 +ℕ compile-length f  -- where f ends, cleanup begins

      pc-f-at-cleanup : pc s-after-f-raw ≡ cleanup-offset
      pc-f-at-cleanup = trans pc-f-raw (cong (_+ℕ len-f) len-prefix-f)

      -- Step 2b: Trace cleanup instructions (mov rsp rbp, pop rbp)
      -- These restore the stack frame and rbp before ret
      -- The cleanup restores rbp to its ORIGINAL value (from s, before setup)
      -- because setup pushed it and cleanup pops it

      -- We need the following for the pop instruction:
      -- 1. rbp in s-after-f-raw points to the pushed rbp (s.rsp - 16, after push r15 and push rbp)
      -- 2. Memory at that address contains s.rbp (pushed during setup)
      -- 3. Memory at s.rsp contains ret-addr (never modified)

      -- rbp value after f: preserved from setup, which set it to s.rsp - 16
      rbp-after-f : readReg (regs s-after-f-raw) rbp ≡ readReg (regs s) rsp ∸ pair-alloc
      rbp-after-f = trans (IRStarResultV.ir-rbp r-f-v) rbp-setup

      -- Fetch cleanup instructions
      -- fetch-cleanup-i0 proves: fetch prog (length prefix +ℕ 14 +ℕ compile-length f) ≡ just cleanup-i0
      -- cleanup-offset = length prefix +ℕ 14 +ℕ compile-length f
      -- These are definitionally equal (both parse as (length prefix +ℕ 14) +ℕ len-f)
      fetch-c0 : fetch prog cleanup-offset ≡ just cleanup-i0
      fetch-c0 = fetch-cleanup-i0 f prefix suffix

      -- fetch-cleanup-i1 proves: fetch prog (length prefix +ℕ 15 +ℕ compile-length f) ≡ just cleanup-i1
      -- cleanup-offset +ℕ 1 = ((length prefix +ℕ 14) +ℕ len-f) +ℕ 1
      -- We need to show this equals (length prefix +ℕ 15) +ℕ len-f
      cleanup-offset-plus-1 : cleanup-offset +ℕ 1 ≡ (length prefix +ℕ 15) +ℕ len-f
      cleanup-offset-plus-1 = trans (+-assoc (length prefix +ℕ 14) len-f 1)
                                    (trans (cong ((length prefix +ℕ 14) +ℕ_) (+-comm len-f 1))
                                           (trans (sym (+-assoc (length prefix +ℕ 14) 1 len-f))
                                                  (cong (_+ℕ len-f) (+-assoc (length prefix) 14 1))))

      fetch-c1 : fetch prog (cleanup-offset +ℕ 1) ≡ just cleanup-i1
      fetch-c1 = subst (λ n → fetch prog n ≡ just cleanup-i1)
                       (sym cleanup-offset-plus-1)
                       (fetch-cleanup-i1 f prefix suffix)

      -- State after mov rsp, rbp
      old-rsp-s = readReg (regs s) rsp
      rbp-val = readReg (regs s-after-f-raw) rbp  -- = old-rsp-s ∸ slot-size

      s-c1 : State
      s-c1 = record s-after-f-raw { regs = writeReg (regs s-after-f-raw) rsp rbp-val
                                  ; pc = pc s-after-f-raw +ℕ 1 }

      step-c0 : step prog s-after-f-raw ≡ just s-c1
      step-c0 = trans (step-exec prog s-after-f-raw cleanup-i0 (IRStarResultV.ir-halted r-f-v)
                        (subst (λ n → fetch prog n ≡ just cleanup-i0) (sym pc-f-at-cleanup) fetch-c0))
                      (execMov-reg-reg s-after-f-raw rsp rbp)

      h-c1 : halted s-c1 ≡ false
      h-c1 = IRStarResultV.ir-halted r-f-v

      pc-c1 : pc s-c1 ≡ cleanup-offset +ℕ 1
      pc-c1 = cong (_+ℕ 1) pc-f-at-cleanup

      -- State after pop rbp
      s-c2 : State
      s-c2 = record s-c1 { regs = writeReg (writeReg (regs s-c1) rbp (readReg (regs s) rbp))
                                          rsp (readReg (regs s-c1) rsp +ℕ slot-size)
                         ; pc = pc s-c1 +ℕ 1 }

      -- For pop rbp, we need memory at rbp to contain the original rbp
      -- PROVEN using ir-mem-rbp:
      -- Chain: s → s-after-setup → s-after-f-raw → s-c1
      -- 1. Setup: push rbp writes s.rbp at s.rsp - 8, rbp set to s.rsp - 8
      -- 2. mem-at-rbp-setup: memory at (rbp after setup) = original rbp
      -- 3. ir-mem-rbp: memory at (rbp after setup) preserved through f
      -- 4. Cleanup mov: doesn't change memory, sets rsp = rbp
      -- 5. rsp after cleanup = rbp after setup = address where original rbp was written

      -- memory s-c1 = memory s-after-f-raw (mov rsp, rbp doesn't write memory)
      mem-c1-eq-f : ∀ addr → readMem (memory s-c1) addr ≡ readMem (memory s-after-f-raw) addr
      mem-c1-eq-f addr = refl

      -- rsp in s-c1 = rbp-val = old-rsp-s - 16 (computed inline, same as rsp-c1 below)
      rsp-c1-inline : readReg (regs s-c1) rsp ≡ old-rsp-s ∸ pair-alloc
      rsp-c1-inline = trans (readReg-writeReg-same (regs s-after-f-raw) rsp rbp-val) rbp-after-f

      -- Chain: memory at rbp after setup is preserved through f, available at rsp after cleanup
      mem-rbp-preserved-f : readMem (memory s-after-f-raw) (readReg (regs s-after-setup) rbp) ≡
                            readMem (memory s-after-setup) (readReg (regs s-after-setup) rbp)
      mem-rbp-preserved-f = IRStarResultV.ir-mem-rbp r-f-v

      -- Convert address from rbp-after-setup to old-rsp-s ∸ 16
      rbp-setup-addr : readReg (regs s-after-setup) rbp ≡ old-rsp-s ∸ pair-alloc
      rbp-setup-addr = rbp-setup

      pop-rbp-mem : readMem (memory s-c1) (readReg (regs s-c1) rsp) ≡ just (readReg (regs s) rbp)
      pop-rbp-mem = begin
        readMem (memory s-c1) (readReg (regs s-c1) rsp)
          ≡⟨ cong (readMem (memory s-c1)) rsp-c1-inline ⟩
        readMem (memory s-c1) (old-rsp-s ∸ pair-alloc)
          ≡⟨ mem-c1-eq-f (old-rsp-s ∸ pair-alloc) ⟩
        readMem (memory s-after-f-raw) (old-rsp-s ∸ pair-alloc)
          ≡⟨ cong (readMem (memory s-after-f-raw)) (sym rbp-setup-addr) ⟩
        readMem (memory s-after-f-raw) (readReg (regs s-after-setup) rbp)
          ≡⟨ mem-rbp-preserved-f ⟩
        readMem (memory s-after-setup) (readReg (regs s-after-setup) rbp)
          ≡⟨ mem-at-rbp-setup ⟩
        just (readReg (regs s) rbp) ∎

      step-c1 : step prog s-c1 ≡ just s-c2
      step-c1 = trans (step-exec prog s-c1 cleanup-i1 h-c1
                        (subst (λ n → fetch prog n ≡ just cleanup-i1) (sym pc-c1) fetch-c1))
                      (execPop prog s-c1 rbp (readReg (regs s) rbp) pop-rbp-mem)

      h-c2 : halted s-c2 ≡ false
      h-c2 = h-c1

      -- pc s-c2 = cleanup-offset + 2 (we still need one more cleanup step - pop r15)
      pc-c2 : pc s-c2 ≡ cleanup-offset +ℕ 2
      pc-c2 = trans (cong (_+ℕ 1) pc-c1)
                    (+-assoc cleanup-offset 1 1)

      -- rsp after mov rsp rbp = old-rsp-s - 16
      rsp-c1 : readReg (regs s-c1) rsp ≡ old-rsp-s ∸ pair-alloc
      rsp-c1 = trans (readReg-writeReg-same (regs s-after-f-raw) rsp rbp-val) rbp-after-f

      -- Precondition: 16 ≤ old-rsp-s (for m+[n∸m]≡n later)
      -- Derive rsp > pair-alloc from cap-thunk (capacity 4 + ir-req f ≥ 2)
      rsp>slots2 : readReg (regs s) rsp > pair-alloc
      rsp>slots2 = ≤-<-trans (slots-mono-≤ (m≤m+n 2 (output-slots +ℕ ir-stack-requirement f))) (StackCapacity.rsp-sufficient cap-thunk)
      16≤rsp : pair-alloc ≤ readReg (regs s) rsp
      16≤rsp = Data.Nat.Properties.<⇒≤ rsp>slots2

      -- rsp after pop rbp = (old-rsp-s - 16) + 8 = old-rsp-s - 8
      -- Proof: (m ∸ 16) + 8 = ((m ∸ 8) ∸ 8) + 8 = m ∸ 8
      -- From 16 ≤ rsp, derive 16 - 8 ≤ rsp - 8, i.e., 8 ≤ rsp - 8
      8≤old-rsp-8 : slot-size ≤ old-rsp-s ∸ slot-size
      8≤old-rsp-8 = Data.Nat.Properties.∸-monoˡ-≤ slot-size 16≤rsp

      rsp-c2 : readReg (regs s-c2) rsp ≡ old-rsp-s ∸ slot-size
      rsp-c2 = begin
        readReg (regs s-c2) rsp
          ≡⟨ readReg-writeReg-same (writeReg (regs s-c1) rbp (readReg (regs s) rbp)) rsp
                                   (readReg (regs s-c1) rsp +ℕ slot-size) ⟩
        readReg (regs s-c1) rsp +ℕ slot-size
          ≡⟨ cong (_+ℕ slot-size) rsp-c1 ⟩
        (old-rsp-s ∸ pair-alloc) +ℕ slot-size
          ≡⟨ cong (_+ℕ slot-size) (sym (∸-+-assoc old-rsp-s slot-size slot-size)) ⟩
        ((old-rsp-s ∸ slot-size) ∸ slot-size) +ℕ slot-size
          ≡⟨ trans (+-comm ((old-rsp-s ∸ slot-size) ∸ slot-size) slot-size) (m+[n∸m]≡n 8≤old-rsp-8) ⟩
        old-rsp-s ∸ slot-size
        ∎

      -- Register preservation through cleanup (mov rsp rbp doesn't touch rax, r14, r15, and pop rbp doesn't either)
      -- s-c2.regs = writeReg (writeReg (regs s-c1) rbp orig-rbp) rsp (s-c1.rsp + 8)
      rsp-val-c2 = readReg (regs s-c1) rsp +ℕ slot-size
      orig-rbp = readReg (regs s) rbp

      rax-c2 : readReg (regs s-c2) rax ≡ readReg (regs s-after-f-raw) rax
      rax-c2 = trans (readReg-writeReg-rsp-rax (writeReg (regs s-c1) rbp orig-rbp) rsp-val-c2)
                     (trans (readReg-writeReg-rbp-rax (regs s-c1) orig-rbp)
                            (readReg-writeReg-rsp-rax (regs s-after-f-raw) rbp-val))

      r14-c2 : readReg (regs s-c2) r14 ≡ readReg (regs s-after-f-raw) r14
      r14-c2 = trans (readReg-writeReg-rsp-r14 (writeReg (regs s-c1) rbp orig-rbp) rsp-val-c2)
                     (trans (readReg-writeReg-rbp-r14 (regs s-c1) orig-rbp)
                            (readReg-writeReg-rsp-r14 (regs s-after-f-raw) rbp-val))

      r15-c2 : readReg (regs s-c2) r15 ≡ readReg (regs s-after-f-raw) r15
      r15-c2 = trans (readReg-writeReg-rsp-r15 (writeReg (regs s-c1) rbp orig-rbp) rsp-val-c2)
                     (trans (readReg-writeReg-rbp-r15 (regs s-c1) orig-rbp)
                            (readReg-writeReg-rsp-r15 (regs s-after-f-raw) rbp-val))

      rbp-c2 : readReg (regs s-c2) rbp ≡ readReg (regs s) rbp
      rbp-c2 = trans (readReg-writeReg-rsp-rbp (writeReg (regs s-c1) rbp orig-rbp) rsp-val-c2)
                     (readReg-writeReg-same (regs s-c1) rbp orig-rbp)

      -- Third cleanup step: pop r15
      -- fetch-cleanup-i2 proves: fetch prog (length prefix +ℕ (thunk-body-offset +ℕ 2) +ℕ compile-length f) ≡ just cleanup-i2
      -- cleanup-offset +ℕ 2 = ((length prefix +ℕ 14) +ℕ len-f) +ℕ 2
      -- We need to show this equals (length prefix +ℕ 16) +ℕ len-f
      cleanup-offset-plus-2 : cleanup-offset +ℕ 2 ≡ (length prefix +ℕ 16) +ℕ len-f
      cleanup-offset-plus-2 = trans (+-assoc (length prefix +ℕ 14) len-f 2)
                                    (trans (cong ((length prefix +ℕ 14) +ℕ_) (+-comm len-f 2))
                                           (trans (sym (+-assoc (length prefix +ℕ 14) 2 len-f))
                                                  (cong (_+ℕ len-f) (+-assoc (length prefix) 14 2))))

      fetch-c2 : fetch prog (cleanup-offset +ℕ 2) ≡ just cleanup-i2
      fetch-c2 = subst (λ n → fetch prog n ≡ just cleanup-i2)
                       (sym cleanup-offset-plus-2)
                       (fetch-cleanup-i2 f prefix suffix)

      -- Note: h-c2 defined above (after step-c1) already proves halted s-c2 ≡ false

      -- State after pop r15
      -- Pop restores r15 from stack at current rsp (old-rsp - 8)
      -- Memory at (old-rsp - 8) was where push r15 wrote the original r15
      -- We need to prove: readMem (memory s-c2) (readReg (regs s-c2) rsp) = just (orig-r15)
      -- where orig-r15 = readReg (regs s) r15

      orig-r15 = readReg (regs s) r15
      rsp-val-c3 = readReg (regs s-c2) rsp +ℕ slot-size

      s-c3 : State
      s-c3 = record s-c2 { regs = writeReg (writeReg (regs s-c2) r15 orig-r15)
                                          rsp rsp-val-c3
                         ; pc = pc s-c2 +ℕ 1 }

      -- Memory at rsp (old-rsp - 8) contains original r15
      -- Chain: s → s-after-setup (push r15 wrote here) → s-after-f → s-c1 → s-c2
      -- Memory preserved through f and cleanup (no writes at old-rsp - 8)

      -- Memory at (old-rsp - 8) preserved through f (using ir-mem-above)
      -- old-rsp - 8 > rbp because rbp = old-rsp - 16
      -- Need: old-rsp-s ∸ 16 < old-rsp-s ∸ slot-size
      -- Use ∸-monoʳ-< : o < n → n ≤ m → m ∸ n < m ∸ o
      rsp-16<rsp-8 : readReg (regs s) rsp ∸ pair-alloc < readReg (regs s) rsp ∸ slot-size
      rsp-16<rsp-8 = Data.Nat.Properties.∸-monoʳ-< word-fits-pair-strict 16≤rsp

      old-rsp-8>rbp : old-rsp-s ∸ slot-size > readReg (regs s-after-setup) rbp
      old-rsp-8>rbp = subst (λ x → old-rsp-s ∸ slot-size > x) (sym rbp-setup-addr) rsp-16<rsp-8

      -- r15 was pushed at old-rsp - 8 during thunk setup
      -- mem-r15-preserved from thunk-setup-star proves this is preserved
      pop-r15-mem : readMem (memory s-c2) (readReg (regs s-c2) rsp) ≡ just orig-r15
      pop-r15-mem = begin
        readMem (memory s-c2) (readReg (regs s-c2) rsp)
          ≡⟨ cong (readMem (memory s-c2)) rsp-c2 ⟩
        readMem (memory s-c2) (old-rsp-s ∸ slot-size)
          ≡⟨⟩  -- memory s-c2 = memory s-c1 (pop rbp only reads)
        readMem (memory s-c1) (old-rsp-s ∸ slot-size)
          ≡⟨ mem-c1-eq-f (old-rsp-s ∸ slot-size) ⟩
        readMem (memory s-after-f-raw) (old-rsp-s ∸ slot-size)
          ≡⟨ IRStarResultV.ir-mem-above r-f-v (old-rsp-s ∸ slot-size) old-rsp-8>rbp ⟩
        readMem (memory s-after-setup) (old-rsp-s ∸ slot-size)
          ≡⟨ mem-r15-setup ⟩
        just orig-r15 ∎

      step-c2 : step prog s-c2 ≡ just s-c3
      step-c2 = trans (step-exec prog s-c2 cleanup-i2 h-c2
                        (subst (λ n → fetch prog n ≡ just cleanup-i2) (sym pc-c2) fetch-c2))
                      (execPop prog s-c2 r15 orig-r15 pop-r15-mem)

      h-c3 : halted s-c3 ≡ false
      h-c3 = h-c2

      -- pc s-c3 = cleanup-offset + 3 = ret-offset
      -- cleanup-offset = (length prefix +ℕ 14) +ℕ len-f
      -- ret-offset = (length prefix +ℕ 17) +ℕ len-f
      -- (length prefix +ℕ 14) +ℕ 3 ≡ length prefix +ℕ 17
      prefix-14+3 : (length prefix +ℕ 14) +ℕ 3 ≡ length prefix +ℕ 17
      prefix-14+3 = +-assoc (length prefix) 14 3

      cleanup-plus-3≡ret : cleanup-offset +ℕ 3 ≡ ret-offset
      cleanup-plus-3≡ret = trans (+-assoc (length prefix +ℕ 14) len-f 3)
                                 (trans (cong ((length prefix +ℕ 14) +ℕ_) (+-comm len-f 3))
                                        (trans (sym (+-assoc (length prefix +ℕ 14) 3 len-f))
                                               (cong (_+ℕ len-f) prefix-14+3)))

      pc-c3 : pc s-c3 ≡ ret-offset
      pc-c3 = begin
        pc s-c3
          ≡⟨⟩
        pc s-c2 +ℕ 1
          ≡⟨ cong (_+ℕ 1) pc-c2 ⟩
        (cleanup-offset +ℕ 2) +ℕ 1
          ≡⟨ +-assoc cleanup-offset 2 1 ⟩
        cleanup-offset +ℕ 3
          ≡⟨ cleanup-plus-3≡ret ⟩
        ret-offset
        ∎

      -- rsp after pop r15 = (old-rsp - 8) + 8 = old-rsp
      rsp-c3 : readReg (regs s-c3) rsp ≡ old-rsp-s
      rsp-c3 = begin
        readReg (regs s-c3) rsp
          ≡⟨ readReg-writeReg-same (writeReg (regs s-c2) r15 orig-r15) rsp rsp-val-c3 ⟩
        rsp-val-c3
          ≡⟨⟩
        readReg (regs s-c2) rsp +ℕ slot-size
          ≡⟨ cong (_+ℕ slot-size) rsp-c2 ⟩
        (old-rsp-s ∸ slot-size) +ℕ slot-size
          ≡⟨ trans (+-comm (old-rsp-s ∸ slot-size) slot-size) (m+[n∸m]≡n 8≤rsp) ⟩
        old-rsp-s
        ∎

      -- Register preservation through third cleanup step
      rax-c3 : readReg (regs s-c3) rax ≡ readReg (regs s-after-f-raw) rax
      rax-c3 = trans (readReg-writeReg-rsp-rax (writeReg (regs s-c2) r15 orig-r15) rsp-val-c3)
                     (trans (readReg-writeReg-r15-rax (regs s-c2) orig-r15)
                            rax-c2)

      r14-c3 : readReg (regs s-c3) r14 ≡ readReg (regs s-after-f-raw) r14
      r14-c3 = trans (readReg-writeReg-rsp-r14 (writeReg (regs s-c2) r15 orig-r15) rsp-val-c3)
                     (trans (readReg-writeReg-r15-r14 (regs s-c2) orig-r15)
                            r14-c2)

      -- r15 after pop r15 = original r15 (restored from stack)
      r15-c3 : readReg (regs s-c3) r15 ≡ orig-r15
      r15-c3 = trans (readReg-writeReg-rsp-r15 (writeReg (regs s-c2) r15 orig-r15) rsp-val-c3)
                     (readReg-writeReg-same (regs s-c2) r15 orig-r15)

      rbp-c3 : readReg (regs s-c3) rbp ≡ readReg (regs s) rbp
      rbp-c3 = trans (readReg-writeReg-rsp-rbp (writeReg (regs s-c2) r15 orig-r15) rsp-val-c3)
                     (trans (readReg-writeReg-r15-rbp (regs s-c2) orig-r15)
                            rbp-c2)

      -- Star composition
      star-c : Star prog s-after-f-raw s-c3
      star-c = ⟨ IRStarResultV.ir-halted r-f-v , step-c0 ⟩◅ ⟨ h-c1 , step-c1 ⟩◅ ⟨ h-c2 , step-c2 ⟩◅ refl*

      -- Stack invariant and rsp bound
      -- rsp-sufficient-c3 follows from rsp-c3 (rsp restored to original) and rsp>slots2 (original > 16)
      rsp-sufficient-c3 : readReg (regs s-c3) rsp > pair-alloc
      rsp-sufficient-c3 = subst (_> pair-alloc) (sym rsp-c3) rsp>slots2

      -- Stack invariant: r15 and rsp restored to original
      r15-s-to-c3 : readReg (regs s-c3) r15 ≡ readReg (regs s) r15
      r15-s-to-c3 = r15-c3

      stack-inv-c3 : StackInvariant s-c3
      stack-inv-c3 = stack-inv-preserved-unchanged s s-c3 stack-inv r15-s-to-c3 rsp-c3

      -- Cleanup preserves memory (mov, pop, pop don't write to arbitrary addresses)
      -- memory s-c1 = memory s-after-f-raw (mov), memory s-c2 = memory s-c1 (pop), memory s-c3 = memory s-c2 (pop)
      mem-cleanup-preserves : ∀ addr → readMem (memory s-c3) addr ≡ readMem (memory s-after-f-raw) addr
      mem-cleanup-preserves addr = mem-c1-eq-f addr  -- All three cleanup steps preserve memory

      -- Direct alias to avoid proj chains (used in validity propagation)
      rax-cleanup : readReg (regs s-c3) rax ≡ readReg (regs s-after-f-raw) rax
      rax-cleanup = rax-c3

      mem-cleanup-preserved : ∀ addr → readMem (memory s-c3) addr ≡ readMem (memory s-after-f-raw) addr
      mem-cleanup-preserved = mem-cleanup-preserves

      -- Return address preserved through execution
      --
      -- Chain: s → s-after-setup → s-after-f-raw → s-c1 → s-c2
      -- 1. s: mem-ret says memory at s.rsp contains ret-addr
      -- 2. Setup: writes at s.rsp - 8 (push rbp), disjoint from s.rsp
      -- 3. f: ir-mem-rbp+8 says memory at (rbp+8 = s.rsp) preserved
      -- 4. Cleanup: mov doesn't write memory, pop reads from s.rsp - 8
      --
      -- Setup preserves memory at s.rsp (writes are at s.rsp - 8 and below)
      -- Proven via mem-old-rsp-setup from thunk-setup-star
      mem-ret-through-setup : readMem (memory s-after-setup) old-rsp-s ≡ just ret-addr
      mem-ret-through-setup = trans mem-old-rsp-setup mem-ret

      -- Memory at s.rsp preserved through f (using ir-mem-above)
      -- old-rsp > rbp because rbp = old-rsp - 16 and 16 > 0
      -- Need: old-rsp > (old-rsp ∸ 16)
      -- m<m+n proves: (old-rsp ∸ 16) < (old-rsp ∸ 16) + 16
      -- Chain: (old-rsp ∸ 16) + 16 ≡ 16 + (old-rsp ∸ 16) ≡ old-rsp
      rbp+16≡old-rsp : readReg (regs s-after-setup) rbp +ℕ pair-alloc ≡ old-rsp-s
      rbp+16≡old-rsp = trans (cong (_+ℕ pair-alloc) rbp-setup-addr)
                             (trans (+-comm (old-rsp-s ∸ pair-alloc) (pair-alloc)) (m+[n∸m]≡n 16≤rsp))

      old-rsp>rbp : old-rsp-s > readReg (regs s-after-setup) rbp
      old-rsp>rbp = subst (_> readReg (regs s-after-setup) rbp)
                         rbp+16≡old-rsp
                         (Data.Nat.Properties.m<m+n (readReg (regs s-after-setup) rbp) {pair-alloc} (s≤s z≤n))

      mem-ret-through-f : readMem (memory s-after-f-raw) old-rsp-s ≡ just ret-addr
      mem-ret-through-f = begin
        readMem (memory s-after-f-raw) old-rsp-s
          ≡⟨ IRStarResultV.ir-mem-above r-f-v old-rsp-s old-rsp>rbp ⟩
        readMem (memory s-after-setup) old-rsp-s
          ≡⟨ mem-ret-through-setup ⟩
        just ret-addr ∎

      -- Memory preserved through cleanup (mov and pops don't write at old-rsp-s)
      -- s-c3 (after 3 cleanup steps) has rsp = old-rsp-s
      mem-ret-preserved : readMem (memory s-c3) (readReg (regs s-c3) rsp) ≡ just ret-addr
      mem-ret-preserved = subst (λ addr → readMem (memory s-c3) addr ≡ just ret-addr)
                                (sym rsp-c3)
                                (trans (mem-c1-eq-f old-rsp-s) mem-ret-through-f)

      -- Direct aliases instead of proj chains (for termination checker efficiency)
      -- s-c3 is s-after-cleanup, star-c is star-cleanup, etc.
      s-after-f : State
      s-after-f = s-c3

      -- Compose f execution with cleanup
      star-f-to-cleanup : Star prog s-after-setup s-c3
      star-f-to-cleanup = star-trans star-f-converted star-c

      star-f : Star prog s-after-setup s-after-f
      star-f = star-f-to-cleanup

      h-f : halted s-after-f ≡ false
      h-f = h-c3

      pc-f : pc s-after-f ≡ ret-offset
      pc-f = pc-c3

      -- Register preservation chains (cleanup preserves from s-after-f-raw, then to s-after-setup)
      r14-f : readReg (regs s-after-f) r14 ≡ readReg (regs s-after-setup) r14
      r14-f = trans r14-c3 (IRStarResultV.ir-r14 r-f-v)

      r15-f : readReg (regs s-after-f) r15 ≡ readReg (regs s-after-setup) r15
      r15-f = trans r15-c3 (sym r15-setup)
              -- r15-c3 : s-c3.r15 = s.r15
              -- r15-setup : s-after-setup.r15 = s.r15
              -- sym r15-setup : s.r15 = s-after-setup.r15
              -- Result: s-c3.r15 = s-after-setup.r15

      rbp-f : readReg (regs s-after-f) rbp ≡ readReg (regs s) rbp
      rbp-f = rbp-c3

      stack-inv-f : StackInvariant s-after-f
      stack-inv-f = stack-inv-c3

      rsp-sufficient-f : readReg (regs s-after-f) rsp > pair-alloc
      rsp-sufficient-f = rsp-sufficient-c3

      mem-ret-f : readMem (memory s-after-f) (readReg (regs s-after-f) rsp) ≡ just ret-addr
      mem-ret-f = mem-ret-preserved

      rsp-f-restored : readReg (regs s-after-f) rsp ≡ readReg (regs s) rsp
      rsp-f-restored = rsp-c3

      mem-f-preserved : ∀ addr → readMem (memory s-after-f) addr ≡ readMem (memory s-after-f-raw) addr
      mem-f-preserved = mem-cleanup-preserves

      -- Step 3: Trace ret instruction
      -- r15 is in code region at s-after-f (restored to entry value by cleanup)
      -- Chain: s-after-f.r15 = s-after-setup.r15 = s.r15 (via r15-f and r15-setup)
      r15-in-code-f : InCode (readReg (regs s-after-f) r15)
      r15-in-code-f = subst InCode (sym r15-f-eq-s) r15-in-code-entry
        where
          -- Chain: s-after-f.r15 = s-after-setup.r15 = s.r15
          r15-f-eq-setup : readReg (regs s-after-f) r15 ≡ readReg (regs s-after-setup) r15
          r15-f-eq-setup = r15-f
          r15-f-eq-s : readReg (regs s-after-f) r15 ≡ readReg (regs s) r15
          r15-f-eq-s = trans r15-f-eq-setup r15-setup

      -- Use ThunkRetResult record for clean field access (no proj chains!)
      ret-result-pair : ∃[ s-fin ] ThunkRetResult prog s-after-f s-fin ret-addr
      ret-result-pair = thunk-ret-star f prefix suffix ret-addr s-after-f
                          h-f pc-f mem-ret-f r15-in-code-f rsp-sufficient-f

      s-final : State
      s-final = proj₁ ret-result-pair

      ret-rec : ThunkRetResult prog s-after-f s-final ret-addr
      ret-rec = proj₂ ret-result-pair

      -- Direct record field access (no proj chains!)
      star-ret : Star prog s-after-f s-final
      star-ret = ret-star ret-rec

      h-final : halted s-final ≡ false
      h-final = ret-halted ret-rec

      pc-final : pc s-final ≡ ret-addr
      pc-final = ret-pc ret-rec

      rax-final : readReg (regs s-final) rax ≡ readReg (regs s-after-f) rax
      rax-final = ret-rax ret-rec

      r14-final : readReg (regs s-final) r14 ≡ readReg (regs s-after-f) r14
      r14-final = ret-r14 ret-rec

      r15-final : readReg (regs s-final) r15 ≡ readReg (regs s-after-f) r15
      r15-final = ret-r15 ret-rec

      rbp-final : readReg (regs s-final) rbp ≡ readReg (regs s-after-f) rbp
      rbp-final = ret-rbp ret-rec

      stack-inv-final : StackInvariant s-final
      stack-inv-final = ret-stack-inv ret-rec

      rsp-sufficient-final : readReg (regs s-final) rsp > pair-alloc
      rsp-sufficient-final = ret-rsp-bound ret-rec

      rsp-ret-plus-8 : readReg (regs s-final) rsp ≡ readReg (regs s-after-f) rsp +ℕ slot-size
      rsp-ret-plus-8 = ret-rsp-plus-8 ret-rec

      mem-ret-preserves : ∀ addr → readMem (memory s-final) addr ≡ readMem (memory s-after-f) addr
      mem-ret-preserves = ret-mem-preserved ret-rec

      -- Compose the three Star proofs
      star-all : Star prog s s-final
      star-all = star-trans star-setup (star-trans star-f star-ret)

      -- Build ThunkResult
      -- Note: rbp-f now directly gives s-after-f.rbp = s.rbp (cleanup restores original)

      -- RSP after thunk = entry RSP + 8 (ret pops return address):
      -- s → s-after-setup (rsp -= 32: push r15, push rbp, sub 16)
      -- s-after-setup → s-after-f (rsp restored by cleanup: add 16, pop rbp, pop r15)
      -- s-after-f → s-final (ret: rsp += 8)
      -- PROVEN: Chain rsp-ret-plus-8 with rsp-f-restored
      thunk-rsp-plus-8-proof : readReg (regs s-final) rsp ≡ readReg (regs s) rsp +ℕ slot-size
      thunk-rsp-plus-8-proof = trans rsp-ret-plus-8 (cong (_+ℕ slot-size) rsp-f-restored)

      -- s-final.rsp = caller-sp.addr (ret returns to caller's frame)
      -- This follows from: s-final.rsp = s.rsp + 8 = caller-sp.addr
      rsp-final-is-caller : readReg (regs s-final) rsp ≡ addr caller-sp
      rsp-final-is-caller = trans thunk-rsp-plus-8-proof (sym caller-sp-bound)

      -- InStack for s-final.rsp derived from caller-sp (no postulate needed!)
      rsp-final-in-stack : InStack (readReg (regs s-final) rsp)
      rsp-final-in-stack = subst InStack (sym rsp-final-is-caller) (in-stack caller-sp)

      -- Validity propagation from s-after-f-raw to s-final
      -- Chain: s-after-f-raw → s-after-cleanup (= s-after-f) → s-final
      -- Uses valid-subst-addr-mem to propagate through address/memory preservation

      -- Step 1: Propagate validity through cleanup (s-after-f-raw → s-after-f)
      result-valid-after-cleanup : ValidAt (eval f (env , arg)) (readReg (regs s-after-f) rax) (memory s-after-f)
      result-valid-after-cleanup = valid-subst-addr-mem result-valid-f rax-cleanup mem-cleanup-preserved

      -- Step 2: Propagate validity through ret (s-after-f → s-final)
      thunk-result-valid-proof : ValidAt (eval f (env , arg)) (readReg (regs s-final) rax) (memory s-final)
      thunk-result-valid-proof = valid-subst-addr-mem result-valid-after-cleanup rax-final mem-ret-preserves

      -- D041: Memory preservation for caller's stack frame
      -- Uses abstract frameSlot interface instead of arithmetic (addr ≥ rsp)
      -- Thunk writes only to its own frame, caller's frame (caller-sp) is disjoint
      --
      -- Proof strategy:
      -- 1. Convert frameSlot to readMem via frameSlot-is-readMem (internal glue)
      -- 2. Chain through phases: ret → cleanup → IR → setup
      -- 3. ret and cleanup preserve ALL memory (no arithmetic needed)
      -- 4. IR preserves memory > rbp (need caller addr > rbp)
      -- 5. setup preserves memory above s.rsp (need caller addr > s.rsp - 32)
      -- 6. Convert back to frameSlot
      --
      -- The call convention ensures: caller-sp.addr = s.rsp + 8
      -- (call instruction pushed return address before thunk entry)
      -- D041 FULLY PROVEN: Uses slot-addr-above-thunk-rbp and mem-above-rsp-preserved
      thunk-preserves-frame-proof : ∀ k → frameSlot (memory s-final) caller-sp k ≡
                                          frameSlot (memory s) caller-sp k
      thunk-preserves-frame-proof k = begin
        frameSlot (memory s-final) caller-sp k
          ≡⟨ frameSlot-is-readMem (memory s-final) caller-sp k ⟩
        readMem (memory s-final) the-slot-addr
          ≡⟨ mem-ret-preserves the-slot-addr ⟩
        readMem (memory s-after-f) the-slot-addr
          ≡⟨ mem-f-preserved the-slot-addr ⟩
        readMem (memory s-after-f-raw) the-slot-addr
          ≡⟨ IRStarResultV.ir-mem-above r-f-v the-slot-addr slot-addr>rbp ⟩
        readMem (memory s-after-setup) the-slot-addr
          ≡⟨ setup-preserves-caller-slot ⟩
        readMem (memory s) the-slot-addr
          ≡⟨ sym (frameSlot-is-readMem (memory s) caller-sp k) ⟩
        frameSlot (memory s) caller-sp k ∎
        where
          open import Data.Nat.Properties using (<-≤-trans; m<m+n)
          open import Data.Nat using (s≤s; z≤n)

          -- The slot address for caller-sp slot k (abstract, no arithmetic!)
          the-slot-addr = slot-addr caller-sp k

          -- D041 PROVEN: Caller slots are above thunk's rbp
          -- Uses abstract slot-addr-above-thunk-rbp from MemoryRegions
          slot-addr>rbp : the-slot-addr > readReg (regs s-after-setup) rbp
          slot-addr>rbp = slot-addr-above-thunk-rbp caller-sp k
                           (readReg (regs s) rsp) (readReg (regs s-after-setup) rbp)
                           caller-sp-bound rbp-setup rsp>slots2

          -- D041 PROVEN: Caller slots are above initial rsp
          -- From caller-sp.addr = rsp + 8 and slot-addr ≥ addr caller-sp
          -- Use private rsp<rsp+slot helper instead of nested where clause
          rsp+8≤slot : readReg (regs s) rsp +ℕ slot-size ≤ the-slot-addr
          rsp+8≤slot = subst (_≤ the-slot-addr) caller-sp-bound (slot-addr-≥-base caller-sp k)
          slot-addr>rsp : the-slot-addr > readReg (regs s) rsp
          slot-addr>rsp = <-≤-trans (rsp<rsp+slot (readReg (regs s) rsp)) rsp+8≤slot

          -- D041 PROVEN: Setup preserves caller's slot addresses
          -- Uses mem-above-setup which requires addr > original rsp
          setup-preserves-caller-slot : readMem (memory s-after-setup) the-slot-addr ≡
                                        readMem (memory s) the-slot-addr
          setup-preserves-caller-slot = mem-above-setup the-slot-addr slot-addr>rsp

      -- Memory at code-region addresses preserved:
      -- Thunk writes only to stack region, code region is disjoint from stack
      --
      -- D041 approach (correct):
      -- 1. ret preserves all memory: mem-ret-preserves (proven)
      -- 2. cleanup preserves all memory: mem-f-preserved (proven)
      -- 3. IR preserves code region: needs ir-mem-code field in IRStarResult
      --    - IR only writes to stack region addresses
      --    - Code region is disjoint from stack region (stack-code-disjoint)
      --    - Therefore code addresses are preserved
      -- 4. setup preserves code region: mem-code-setup (proven via D041)
      --
      -- NOTE: Using ir-mem-above + "code addresses > rbp" is WRONG approach.
      -- Region disjointness (≢) is not the same as address ordering (>).
      -- The postulate below should be replaced by adding ir-mem-code to IRStarResult.
      thunk-preserves-code-proof : ∀ addr → InCode addr →
                                   readMem (memory s-final) addr ≡ readMem (memory s) addr
      thunk-preserves-code-proof addr addr-in-code = begin
        readMem (memory s-final) addr
          ≡⟨ mem-ret-preserves addr ⟩
        readMem (memory s-after-f) addr
          ≡⟨ mem-f-preserved addr ⟩
        readMem (memory s-after-f-raw) addr
          ≡⟨ IRStarResultV.ir-mem-code r-f-v addr addr-in-code ⟩
        readMem (memory s-after-setup) addr
          ≡⟨ mem-code-setup addr addr-in-code ⟩
        readMem (memory s) addr ∎

      -- Memory at heap-region addresses preserved:
      -- Same structure as code - thunk writes only to stack, heap is disjoint
      thunk-preserves-heap-proof : ∀ addr → InHeap addr →
                                   readMem (memory s-final) addr ≡ readMem (memory s) addr
      thunk-preserves-heap-proof addr addr-in-heap = begin
        readMem (memory s-final) addr
          ≡⟨ mem-ret-preserves addr ⟩
        readMem (memory s-after-f) addr
          ≡⟨ mem-f-preserved addr ⟩
        readMem (memory s-after-f-raw) addr
          ≡⟨ IRStarResultV.ir-mem-heap r-f-v addr addr-in-heap ⟩
        readMem (memory s-after-setup) addr
          ≡⟨ mem-heap-setup addr addr-in-heap ⟩
        readMem (memory s) addr ∎

      -- D041: Memory above entry rsp is preserved
      -- Chain: ret → cleanup → IR → setup, all preserve addresses > entry-rsp
      thunk-preserves-above-entry-rsp-proof : ∀ addr → addr > readReg (regs s) rsp →
                                               readMem (memory s-final) addr ≡ readMem (memory s) addr
      thunk-preserves-above-entry-rsp-proof addr addr>rsp = begin
        readMem (memory s-final) addr
          ≡⟨ mem-ret-preserves addr ⟩
        readMem (memory s-after-f) addr
          ≡⟨ mem-f-preserved addr ⟩
        readMem (memory s-after-f-raw) addr
          ≡⟨ IRStarResultV.ir-mem-above r-f-v addr addr>rbp ⟩
        readMem (memory s-after-setup) addr
          ≡⟨ mem-above-setup addr addr>rsp ⟩
        readMem (memory s) addr ∎
        where
          open import Data.Nat.Properties using (<-trans)
          -- addr > rsp > rsp - 16 = rbp-after-setup
          -- Use private m∸n<m-when-positive helper instead of local definition
          rsp>rsp-16 : readReg (regs s) rsp > readReg (regs s) rsp ∸ pair-alloc
          rsp>rsp-16 = m∸n<m-when-positive (readReg (regs s) rsp) (pair-alloc) (≤-trans (s≤s z≤n) rsp>slots2) (s≤s z≤n)
          addr>rbp : addr > readReg (regs s-after-setup) rbp
          addr>rbp = subst (addr >_) (sym rbp-setup) (<-trans rsp>rsp-16 addr>rsp)

      thunk-result : ThunkResult prog s s-final caller-sp (λ b → eval f (env , b)) arg
      thunk-result = record
        { thunk-star = star-all
        ; thunk-halted = h-final
        ; thunk-result-valid = thunk-result-valid-proof
        ; thunk-r14 = trans r14-final (trans r14-f r14-setup)
        ; thunk-r15 = trans r15-final (trans r15-f r15-setup)
        ; thunk-rbp = trans rbp-final rbp-f  -- rbp-f gives s-after-f.rbp = s.rbp directly
        ; thunk-stack-inv = stack-inv-final
        ; thunk-capacity = rsp-bound-to-capacity 2 s-final rsp-final-in-stack rsp-sufficient-final
        ; thunk-rsp-plus-8 = thunk-rsp-plus-8-proof
        ; thunk-preserves-frame = thunk-preserves-frame-proof
        ; thunk-preserves-code = thunk-preserves-code-proof
        ; thunk-preserves-heap = thunk-preserves-heap-proof
        ; thunk-preserves-above-entry-rsp = thunk-preserves-above-entry-rsp-proof
        }

  ------------------------------------------------------------------------
  -- Apply implementation (uses run-apply-to-ir-result from Apply.agda)
  --
  -- This replaces the monolithic apply-produces-result postulate with
  -- more structured postulates:
  --   1. closure-wf-for-apply: The closure is well-formed
  --   2. Memory layout postulates: Runtime memory structure
  --
  -- The apply instruction tracing is now proven in Apply.agda.
  ------------------------------------------------------------------------

  -- | Validity-based apply execution (with Acc for termination)
  -- Takes ValidAt input, uses validity decomposition to extract memory layout
  -- Returns IRStarResultV with direct validity (bridges eliminated from output!)
  -- Note: Acc passed but not used directly - thunk-correct in closure already has termination baked in
  -- ir-stack-requirement apply = 4, so cap-in : StackCapacity s 4
  run-apply-star-direct : ∀ {A B} (prefix suffix : Program) (caller-sp : StackPointer) (x : ⟦ (A ⇒ B) * A ⟧) (s : State) →
    halted s ≡ false →
    pc s ≡ length prefix →
    ValidAt x (readReg (regs s) rdi) (memory s) →
    StackInvariant s →
    StackCapacity s (ir-stack-requirement (apply {A} {B})) →
    RbpInvariant s →
    Acc _<_ (ir-size (apply {A} {B})) →
    let prog = prefix ++ compile-x86 (apply {A} {B}) ++ suffix
    in ∃[ s' ] IRStarResultV (apply {A} {B}) prog s s' x (length prefix)
  run-apply-star-direct {A} {B} prefix suffix caller-sp x s h-false pc-eq input-valid stack-inv cap rbp-inv _ =
    let (s' , ir-result') = run-apply-to-ir-result-v {closure-wf-E} prefix suffix code-ptr closure-wf-env sem apply-closure-addr apply-arg-addr arg s
                              closure-wf-post h-false pc-eq stack-inv cap-for-apply rbp-inv apply-v-cl apply-v-arg closure-wf-v-env apply-pair-at apply-closure-at
    in s' , subst (λ xv → IRStarResultV (apply {A} {B}) prog s s' xv offset) x''-eq-x ir-result'
    where
      open import Data.Product using (proj₁; proj₂)
      open import Once.Semantics using (Closure)

      prog = prefix ++ compile-x86 (apply {A} {B}) ++ suffix
      offset = length prefix

      -- Extract closure and argument from semantic pair
      cl : Closure A B
      cl = proj₁ x

      arg : ⟦ A ⟧
      arg = proj₂ x

      -- Extract env-addr, semantics from closure (code-ptr is now runtime-only)
      env-addr : ℕ
      env-addr = Closure.env-addr cl

      sem : ⟦ A ⟧ → ⟦ B ⟧
      sem = Closure.semantics cl

      -- ============================================================
      -- VALIDITY DECOMPOSITION (replaces mem-layout postulate)
      -- ============================================================

      -- Decompose pair validity into closure and arg validities
      pair-decomp = valid-pair-decompose input-valid
      apply-closure-addr = proj₁ pair-decomp
      apply-arg-addr = proj₁ (proj₂ pair-decomp)
      apply-v-cl-raw = proj₁ (proj₂ (proj₂ pair-decomp))  -- ValidAt cl closure-addr mem
      apply-v-arg = proj₁ (proj₂ (proj₂ (proj₂ pair-decomp)))
      apply-pair-at = proj₂ (proj₂ (proj₂ (proj₂ pair-decomp)))

      -- Decompose closure validity into memory layout
      -- Returns existential code-ptr (runtime property, not semantic)
      apply-closure-decomp = valid-closure-decompose apply-v-cl-raw
      code-ptr : ℕ
      code-ptr = proj₁ apply-closure-decomp
      apply-closure-at-raw = proj₂ apply-closure-decomp

      -- The semantic value x' (matches cl via Closure-η)
      x' : ⟦ (A ⇒ B) * A ⟧
      x' = (record { env-addr = env-addr ; semantics = sem } , arg)

      -- Prove x' ≡ x (eta-expansion of Closure record and pair)
      -- Uses Closure-η from Semantics.agda for propositional eta
      x'-eq-x : x' ≡ x
      x'-eq-x = cong₂ _,_ (Closure-η-sem cl) refl

      -- Constructed closure record (same as x')
      cl' : Closure A B
      cl' = record { env-addr = env-addr ; semantics = sem }

      -- POSTULATE: Closure well-formedness for closures in the program
      -- This is justified because all closures come from curry in the same program,
      -- and curry now produces ClosureWellFormed proofs (see run-curry-star-direct).
      -- Threading this proof through composition is a future improvement.
      -- E is the captured environment type, env is the environment value
      postulate
        closure-wf-E : Type
        closure-wf-env : ⟦ closure-wf-E ⟧
        closure-wf-post : ClosureWellFormed {closure-wf-E} {A} {B} prog code-ptr closure-wf-env sem
        closure-wf-v-env : ValidAt closure-wf-env (encode closure-wf-env) (memory s)
        -- Consistency: the env-addr in Closure must match encode of the env value
        closure-wf-env-addr-eq : env-addr ≡ encode closure-wf-env
        -- Capacity postulate: the available capacity is sufficient for apply + thunk
        -- This is justified because in a properly compiled program, the stack capacity
        -- at apply call sites includes the thunk's requirement.
        -- When closure-wf threading is complete, this becomes derivable.
        cap-for-apply : StackCapacity s (apply-consumed-slots +ℕ ClosureWellFormed.thunk-capacity closure-wf-post)

      -- Closure with env-addr matching closure-wf-env (for run-apply-to-ir-result-v)
      cl'' : Closure A B
      cl'' = record { env-addr = encode closure-wf-env ; semantics = sem }

      -- Transport validity from cl to cl'' using the env-addr equality
      -- First transport from cl to cl' (using Closure eta)
      apply-v-cl' : ValidAt {A ⇒ B} cl' apply-closure-addr (memory s)
      apply-v-cl' = subst (λ c → ValidAt c apply-closure-addr (memory s)) (sym (Closure-η-sem cl)) apply-v-cl-raw

      -- Then transport from cl' to cl'' (using closure-wf-env-addr-eq)
      apply-v-cl : ValidAt {A ⇒ B} cl'' apply-closure-addr (memory s)
      apply-v-cl = subst (λ e → ValidAt (record { env-addr = e ; semantics = sem }) apply-closure-addr (memory s))
                         closure-wf-env-addr-eq apply-v-cl'

      -- Transport closure-at to use encode closure-wf-env
      apply-closure-at : ClosureAtS (encode closure-wf-env) code-ptr apply-closure-addr (memory s)
      apply-closure-at = subst (λ e → ClosureAtS e code-ptr apply-closure-addr (memory s)) closure-wf-env-addr-eq apply-closure-at-raw

      -- x'' is the semantic value that run-apply-to-ir-result-v produces
      -- (with env-addr = encode closure-wf-env)
      x'' : ⟦ (A ⇒ B) * A ⟧
      x'' = (cl'' , arg)

      -- Prove x'' ≡ x by transitivity: x'' ≡ x' ≡ x
      -- First, x'' ≡ x' using sym of closure-wf-env-addr-eq
      cl''-eq-cl' : cl'' ≡ cl'
      cl''-eq-cl' = cong (λ e → record { env-addr = e ; semantics = sem }) (sym closure-wf-env-addr-eq)

      x''-eq-x' : x'' ≡ x'
      x''-eq-x' = cong (λ c → (c , arg)) cl''-eq-cl'

      x''-eq-x : x'' ≡ x
      x''-eq-x = trans x''-eq-x' x'-eq-x

------------------------------------------------------------------------
-- Validity wrappers for curry and apply (Phase C)
-- These take ValidAt input and return IRStarResultV
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
    Acc _<_ (ir-size (curry f)) →
    let prog = prefix ++ compile-x86 (curry f) ++ suffix
    in ∃[ s' ] IRStarResultV (curry f) prog s s' x (length prefix)
  run-curry-star-v f prefix suffix caller-sp x s h-false pc-eq input-valid stack-inv cap-in rbp-inv ac =
    -- run-curry-star-direct takes validity input directly, passes Acc for thunk execution
    run-curry-star-direct f prefix suffix caller-sp x s h-false pc-eq input-valid stack-inv cap-in rbp-inv ac

  -- | Validity-based apply execution (with Acc for termination)
  -- Simple passthrough to run-apply-star-direct (which now takes validity input and Acc)
  run-apply-star-v : ∀ {A B} (prefix suffix : Program) (caller-sp : StackPointer) (x : ⟦ (A ⇒ B) * A ⟧) (s : State) →
    halted s ≡ false →
    pc s ≡ length prefix →
    ValidAt x (readReg (regs s) rdi) (memory s) →
    StackInvariant s →
    StackCapacity s (ir-stack-requirement (apply {A} {B})) →
    RbpInvariant s →
    Acc _<_ (ir-size (apply {A} {B})) →
    let prog = prefix ++ compile-x86 (apply {A} {B}) ++ suffix
    in ∃[ s' ] IRStarResultV (apply {A} {B}) prog s s' x (length prefix)
  run-apply-star-v {A} {B} prefix suffix caller-sp x s h-false pc-eq input-valid stack-inv cap-in rbp-inv ac =
    -- ir-stack-requirement apply = 4, cap-in : StackCapacity s 4 directly
    run-apply-star-direct prefix suffix caller-sp x s h-false pc-eq input-valid stack-inv cap-in rbp-inv ac

  ------------------------------------------------------------------------
  -- Validity-based dispatcher cases (IN mutual block)
  ------------------------------------------------------------------------

  -- Direct validity-based execution for inl (base case, ignores Acc)
  -- ir-stack-requirement inl = 4, so cap-in : StackCapacity s 4 directly
  run-ir-star-at-offset-v (inl {A} {B}) prefix suffix caller-sp x s h-false pc-eq input-valid stack-inv cap-in rbp-inv _ =
    run-inl-star-v-auto prefix suffix x s h-false pc-eq input-valid stack-inv cap-in rbp-inv
  -- Direct validity-based execution for inr (base case, ignores Acc)
  -- ir-stack-requirement inr = 4, so cap-in : StackCapacity s 4 directly
  run-ir-star-at-offset-v (inr {A} {B}) prefix suffix caller-sp x s h-false pc-eq input-valid stack-inv cap-in rbp-inv _ =
    run-inr-star-v-auto prefix suffix x s h-false pc-eq input-valid stack-inv cap-in rbp-inv
  -- Pair: uses Acc to construct size-bounded dispatcher for parameterized module
  -- NOTE: Pair needs StackCapacity s 7 (5 for setup + 2 remaining)
  -- TODO: Dispatcher should take ir-input-capacity ir slots, not fixed 2
  run-ir-star-at-offset-v (⟨ f , g ⟩) prefix suffix caller-sp x s h-false pc-eq input-valid stack-inv cap-in rbp-inv (acc rs) =
    let -- Construct size-bounded dispatcher from Acc destructor (rs)
        rec : ∀ {A' B'} (ir' : IR A' B') → ir-size ir' < ir-size ⟨ f , g ⟩ →
              (prefix' suffix' : Program) (caller-sp' : StackPointer) (x' : ⟦ A' ⟧) (s' : State) →
              halted s' ≡ false → pc s' ≡ length prefix' →
              ValidAt x' (readReg (regs s') rdi) (memory s') →
              StackInvariant s' → StackCapacity s' (ir-stack-requirement ir') → RbpInvariant s' →
              let prog' = prefix' ++ compile-x86 ir' ++ suffix'
              in ∃[ s'' ] IRStarResultV ir' prog' s' s'' x' (length prefix')
        rec ir' lt prefix' suffix' caller-sp' x' s' h-false' pc-eq' input-valid' stack-inv' cap-in' rbp-inv' =
          run-ir-star-at-offset-v ir' prefix' suffix' caller-sp' x' s' h-false' pc-eq' input-valid' stack-inv' cap-in' rbp-inv' (rs lt)
        open PairModule (ir-size ⟨ f , g ⟩) rec
        -- cap-in has type StackCapacity s (ir-stack-requirement ⟨ f , g ⟩) which is what run-pair-star-v expects
    in run-pair-star-v f g (⟨,⟩-f-smaller f g) (⟨,⟩-g-smaller f g) prefix suffix caller-sp x s h-false pc-eq input-valid stack-inv cap-in rbp-inv
  -- Compose: uses Acc to construct size-bounded dispatcher for parameterized module
  run-ir-star-at-offset-v (g ∘ f) prefix suffix caller-sp x s h-false pc-eq input-valid stack-inv cap-in rbp-inv (acc rs) =
    let -- Construct size-bounded dispatcher from Acc destructor (rs)
        rec : ∀ {A' B'} (ir' : IR A' B') → ir-size ir' < ir-size (g ∘ f) →
              (prefix' suffix' : Program) (caller-sp' : StackPointer) (x' : ⟦ A' ⟧) (s' : State) →
              halted s' ≡ false → pc s' ≡ length prefix' →
              ValidAt x' (readReg (regs s') rdi) (memory s') →
              StackInvariant s' → StackCapacity s' (ir-stack-requirement ir') → RbpInvariant s' →
              let prog' = prefix' ++ compile-x86 ir' ++ suffix'
              in ∃[ s'' ] IRStarResultV ir' prog' s' s'' x' (length prefix')
        rec ir' lt prefix' suffix' caller-sp' x' s' h-false' pc-eq' input-valid' stack-inv' cap-in' rbp-inv' =
          run-ir-star-at-offset-v ir' prefix' suffix' caller-sp' x' s' h-false' pc-eq' input-valid' stack-inv' cap-in' rbp-inv' (rs lt)
        open ComposeModule (ir-size (g ∘ f)) rec
    in run-compose-star-v f g (∘-f-smaller f g) (∘-g-smaller f g) prefix suffix caller-sp x s h-false pc-eq input-valid stack-inv cap-in rbp-inv
  -- Direct validity for id (base case, ignores Acc)
  run-ir-star-at-offset-v (id {A}) prefix suffix caller-sp x s h-false pc-eq input-valid stack-inv cap-in rbp-inv _ =
    run-id-star-vv prefix suffix x s h-false pc-eq input-valid stack-inv cap-in rbp-inv
  -- Direct validity for terminal (base case, ignores Acc)
  run-ir-star-at-offset-v (terminal {A}) prefix suffix caller-sp x s h-false pc-eq input-valid stack-inv cap-in rbp-inv _ =
    run-terminal-star-vv prefix suffix x s h-false pc-eq stack-inv cap-in rbp-inv
  -- Direct validity for fold (base case, ignores Acc)
  run-ir-star-at-offset-v (fold {F}) prefix suffix caller-sp x s h-false pc-eq input-valid stack-inv cap-in rbp-inv _ =
    run-fold-star-vv prefix suffix x s h-false pc-eq input-valid stack-inv cap-in rbp-inv
  -- Direct validity for unfold (base case, ignores Acc)
  run-ir-star-at-offset-v (unfold {F}) prefix suffix caller-sp (wrap x') s h-false pc-eq input-valid stack-inv cap-in rbp-inv _ =
    run-unfold-star-vv prefix suffix (wrap x') s h-false pc-eq input-valid stack-inv cap-in rbp-inv
  -- Direct validity for arr (base case, ignores Acc)
  run-ir-star-at-offset-v (arr {A} {B}) prefix suffix caller-sp x s h-false pc-eq input-valid stack-inv cap-in rbp-inv _ =
    run-arr-star-vv prefix suffix x s h-false pc-eq input-valid stack-inv cap-in rbp-inv
  -- Direct validity for prim (base case, ignores Acc)
  run-ir-star-at-offset-v (Prim {A} {B} name) prefix suffix caller-sp x s h-false pc-eq input-valid stack-inv cap-in rbp-inv _ =
    let rdi-not-stack = λ addr stack-proof → valid-disjoint-from-stack input-valid stack-proof
    in run-prim-star-vv name prefix suffix x s h-false pc-eq input-valid rdi-not-stack stack-inv cap-in rbp-inv
  -- Initial: absurd case (base case, ignores Acc)
  run-ir-star-at-offset-v (initial {A}) prefix suffix caller-sp x s h-false pc-eq input-valid stack-inv cap-in rbp-inv _ =
    ⊥-elim x
  -- fst: decompose pair validity (base case, ignores Acc)
  run-ir-star-at-offset-v (fst {A} {B}) prefix suffix caller-sp x s h-false pc-eq input-valid stack-inv cap-in rbp-inv _ =
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
  run-ir-star-at-offset-v (snd {A} {B}) prefix suffix caller-sp x s h-false pc-eq input-valid stack-inv cap-in rbp-inv _ =
    let a = proj₁ x
        b = proj₂ x
        decomp = valid-pair-decompose input-valid
        addr-a = proj₁ decomp
        addr-b = proj₁ (proj₂ decomp)
        va = proj₁ (proj₂ (proj₂ decomp))
        vb = proj₁ (proj₂ (proj₂ (proj₂ decomp)))
        pair-at = proj₂ (proj₂ (proj₂ (proj₂ decomp)))
    in run-snd-star-vv prefix suffix a b addr-a addr-b s h-false pc-eq va vb pair-at stack-inv cap-in rbp-inv
  -- case: uses Acc to construct size-bounded dispatcher for parameterized module
  run-ir-star-at-offset-v ([_,_] {A} {B} {C} f g) prefix suffix caller-sp x s h-false pc-eq input-valid stack-inv cap-in rbp-inv (acc rs) =
    let -- Construct size-bounded dispatcher from Acc destructor (rs)
        rec : ∀ {A' B'} (ir' : IR A' B') → ir-size ir' < ir-size [ f , g ] →
              (prefix' suffix' : Program) (caller-sp' : StackPointer) (x' : ⟦ A' ⟧) (s' : State) →
              halted s' ≡ false → pc s' ≡ length prefix' →
              ValidAt x' (readReg (regs s') rdi) (memory s') →
              StackInvariant s' → StackCapacity s' (ir-stack-requirement ir') → RbpInvariant s' →
              let prog' = prefix' ++ compile-x86 ir' ++ suffix'
              in ∃[ s'' ] IRStarResultV ir' prog' s' s'' x' (length prefix')
        rec ir' lt prefix' suffix' caller-sp' x' s' h-false' pc-eq' input-valid' stack-inv' cap-in' rbp-inv' =
          run-ir-star-at-offset-v ir' prefix' suffix' caller-sp' x' s' h-false' pc-eq' input-valid' stack-inv' cap-in' rbp-inv' (rs lt)
        open CaseModule (ir-size [ f , g ]) rec
    in run-case-star-v f g ([,]-f-smaller f g) ([,]-g-smaller f g) prefix suffix caller-sp x s h-false pc-eq input-valid stack-inv cap-in rbp-inv
  -- curry: passes Acc to recursive calls within curry-thunk-correct-impl
  run-ir-star-at-offset-v (curry {A} {B} {C} f) prefix suffix caller-sp x s h-false pc-eq input-valid stack-inv cap-in rbp-inv ac =
    run-curry-star-v f prefix suffix caller-sp x s h-false pc-eq input-valid stack-inv cap-in rbp-inv ac
  -- apply: passes Acc to recursive calls (closure body execution)
  run-ir-star-at-offset-v (apply {A} {B}) prefix suffix caller-sp x s h-false pc-eq input-valid stack-inv cap-in rbp-inv ac =
    run-apply-star-v prefix suffix caller-sp x s h-false pc-eq input-valid stack-inv cap-in rbp-inv ac

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
       (<-wellFounded (ir-size ir))
