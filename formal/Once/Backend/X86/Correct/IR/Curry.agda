------------------------------------------------------------------------
-- Once.Backend.X86.Correct.IR.Curry
--
-- Star-based curry proof: curry-thunk-correct-v (recursive thunk impl).
-- Non-recursive parts (run-curry-star) in CurryInstr.agda.
------------------------------------------------------------------------

module Once.Backend.X86.Correct.IR.Curry where

-- Import consolidated Foundation module
open import Once.Backend.X86.Correct.Foundation

-- Additional imports not in Foundation
open import Once.Backend.X86.Correct.CompileLength hiding (length-++)
open import Once.Backend.X86.Correct.StackInstantiation
open import Once.Backend.X86.Correct.StackInstantiation
  using (rsp-bound-to-capacity; StackCapacity; capacity-after-alloc-2-slots; capacity-2-to-rsp-bound;
         alloc-2-slots-addrs-in-stack; slots-mono-≤;
         ir-stack-requirement; ir-rsp-delta; ir-output-capacity;
         curry-rsp-delta≤curry-req;
         -- D041: Abstract helpers that encapsulate arithmetic
         curry-frame-disjoint-from-rbp; curry-rbp-inv-update; curry-stack-inv-frame-bound-update;
         curry-alloc-below-rbp; curry-alloc-nonzero;
         -- For thunk implementation
         thunk-setup-consumed-slots; capacity-from-larger; thunk-setup-capacity;
         thunk-setup-cap≤thunk-consumed+ir-req; capacity-after-delta;
         output-slots; stack-inv-preserved-unchanged)
open import Data.Nat.Properties using (≤-<-trans)
open import Once.Backend.X86.Layout
  using (InStack; InHeap; InCode; stack-code-addr-disjoint; stack-heap-addr-disjoint;
         stackAddr-write-preserves-heap; slot-addr; StackPointer;
         slot-addr-above-thunk-rbp; slot-addr-≥-base; in-stack; frameSlot)
open import Once.Backend.X86.Layout using () renaming (addr to sp-addr)
-- Internal glue for abstraction boundary (implementation use only!)
open import Once.Backend.X86.Layout using (module FrameSlotInternal)
open FrameSlotInternal using (frameSlot-is-readMem)
open import Once.Backend.X86.Correct.ExecLemmas
open import Once.Backend.X86.Correct.FetchStep using (step-exec)
open import Once.Backend.X86.Correct.InstrExec using (execMov-reg-reg; execPop)
open import Once.Backend.X86.Correct.RegisterLemmas
open import Once.Backend.X86.Correct.ArithmeticLemmas using (word-fits-pair-strict)
open import Once.Backend.X86.Correct.Star
  using (Star; refl*; step*; ⟨_,_⟩◅_; star-trans)
open import Once.Backend.X86.Correct.StarBase
  using (IRStarResult; ClosureWFOutput; no-closure; has-closure;
         ir-star; ir-halted; ir-pc; ir-rax; ir-r14; ir-r15; ir-rbp;
         ir-mem; ir-mem-rbp; ir-mem-rbp+8; ir-stack-inv; ir-rsp-bound; ir-rbp-inv; ir-mem-above; ir-mem-code; ir-mem-heap; ir-closure-wf;
         ir-entry-rsp; ir-entry-rsp-eq; ir-mem-preserved;
         IRStarResultV; ir-result-valid; ir-capacity; ir-rsp-bound-v)
  renaming (ir-rsp-v to ir-rsp)

-- Import thunk execution proofs
open import Once.Backend.X86.Correct.IR.ThunkExec
  using (thunk-setup-star; thunk-ret-star; ThunkSetupResult; ThunkRetResult)
import Once.Backend.X86.Correct.IR.ThunkExec as TE
open ThunkRetResult

-- Import thunk structure lemmas
open import Once.Backend.X86.Correct.IR.ThunkStructure
  using (cleanup-i0; cleanup-i1; cleanup-i2;
         fetch-cleanup-i0; fetch-cleanup-i1; fetch-cleanup-i2)

-- Import closure well-formedness infrastructure
open import Once.Backend.X86.Correct.ClosureWellFormed
  using (ClosureWellFormed; ThunkResult;
         thunk-star; thunk-halted; thunk-result-valid;
         thunk-r14; thunk-r15; thunk-rbp; thunk-stack-inv; thunk-capacity)
open import Once.Backend.X86.Correct.MemoryValid
  using (ValidAt; valid-closure-env; ClosureAtS; closure-at-s;
         valid-subst-addr-mem)

-- Import IRSize for size proofs
open import Once.Backend.Common.IRSize
  using (ir-size; curry-smaller)
-- Import RecDispatcher from central location
open import Once.Backend.X86.Correct.RecDispatcher using (RecDispatcher)

open import Data.Nat using (_>_; _≥_; _<_; _≤_; s≤s; z≤n)
-- D041: Arithmetic moved to abstract helpers in StackInvariant.agda
-- m≤m+n kept for simple numeric constant facts
open import Data.Nat.Properties using (+-assoc; +-comm; ≤-trans; <-trans; ≤-<-trans; <-≤-trans;
                                        m<m+n; 0<1+n; m≤m+n; <⇒≤; m+[n∸m]≡n; ∸-+-assoc; m∸n≤m) renaming (<⇒≢ to Nat-<⇒≢)
open import Data.List.Properties using (++-assoc) renaming (length-++ to List-length-++)
open import Relation.Binary.PropositionalEquality using (_≢_; subst₂)
open import Relation.Binary.PropositionalEquality.Properties using (module ≡-Reasoning)
open ≡-Reasoning


open import Once.Backend.X86.Correct.IR.CurryInstr public

-- Helper: m ∸ n < m when both positive (used in thunk memory preservation proof)
m∸n<m-when-positive : ∀ m n → m > 0 → n > 0 → m ∸ n < m
m∸n<m-when-positive (suc m') (suc n') _ _ = s≤s (m∸n≤m m' n')

curry-thunk-correct-v : ∀ {A B C} (f : IR (A * B) C)
                        (bound : ℕ)
                        (rec : RecDispatcher bound)
                        (f<bound : ir-size f < bound)
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
  sp-addr caller-sp ≡ readReg (regs s) rsp +ℕ slot-size →  -- D041: caller-sp bound
  InCode (readReg (regs s) r15) →  -- r15 in code region (from Apply)
  ∃[ s' ] (ThunkResult prog s s' caller-sp (λ b → eval f (env , b)) arg
          × pc s' ≡ ret-addr)
curry-thunk-correct-v {A} {B} {C} f bound rec f<bound prefix suffix caller-sp env arg s ret-addr
                      h-eq pc-eq v-arg v-env mem-ret stack-inv cap-thunk caller-sp-bound r15-in-code-entry =
    s-final , thunk-result , pc-final
    where
      -- Local imports (some may duplicate module-level imports)
      open import Data.List.Properties using (++-assoc) renaming (length-++ to List-length-++)
      open import Data.Nat.Properties using (≤-trans; m≤m+n; ∸-monoˡ-≤; ∸-monoʳ-<) renaming (+-comm to Data-Nat-+-comm)

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

      -- Derive StackCapacity for thunk-setup-star from threaded capacity
      cap-thunk-setup : StackCapacity s thunk-setup-capacity
      cap-thunk-setup = capacity-from-larger s thunk-setup-capacity
                          (thunk-setup-consumed-slots +ℕ ir-stack-requirement f)
                          cap-thunk (thunk-setup-cap≤thunk-consumed+ir-req f)

      -- Step 1: Trace 8 setup instructions
      setup-result = thunk-setup-star f prefix suffix env arg s
                       h-eq pc-eq v-arg v-env stack-inv cap-thunk-setup
      s-after-setup = proj₁ setup-result
      setup-rec = proj₂ setup-result
      open TE.ThunkSetupResult setup-rec

      -- Step 2: Call rec on f
      len-f = compile-length f
      end-label = 18 +ℕ len-f
      end-offset-curry = 12 +ℕ len-f

      curry-closure-setup : Program
      curry-closure-setup =
        sub (reg rsp) (imm (pair-alloc)) ∷
        mov (mem (base rsp)) (reg rdi) ∷
        lea r9 (rip+disp 4) ∷
        mov (mem (base+disp rsp slot-size)) (reg r9) ∷
        mov (reg rax) (reg rsp) ∷
        jmp end-offset-curry ∷ []

      curry-thunk-setup-prog : Program
      curry-thunk-setup-prog =
        label 6 ∷
        push (reg r15) ∷
        push (reg rbp) ∷
        mov (reg rbp) (reg rsp) ∷
        sub (reg rsp) (imm (pair-alloc)) ∷
        mov (mem (base rsp)) (reg r12) ∷
        mov (mem (base+disp rsp slot-size)) (reg rdi) ∷
        mov (reg rdi) (reg rsp) ∷ []

      prefix-f : Program
      prefix-f = prefix ++ curry-closure-setup ++ curry-thunk-setup-prog

      curry-tail : Program
      curry-tail = mov (reg rsp) (reg rbp) ∷
                   pop rbp ∷
                   pop r15 ∷
                   ret ∷ label end-label ∷ []

      suffix-f : Program
      suffix-f = curry-tail ++ suffix

      len-prefix-f : length prefix-f ≡ length prefix +ℕ 14
      len-prefix-f = trans (List-length-++ prefix {curry-closure-setup ++ curry-thunk-setup-prog})
                           (cong (length prefix +ℕ_) (List-length-++ curry-closure-setup {curry-thunk-setup-prog}))

      curry-structure : compile-x86 (curry f) ≡
                        curry-closure-setup ++ curry-thunk-setup-prog ++ compile-x86 f ++ curry-tail
      curry-structure = refl

      prog-eq-f : prog ≡ prefix-f ++ compile-x86 f ++ suffix-f
      prog-eq-f = trans (cong (λ x → prefix ++ x ++ suffix) curry-structure) prog-reassoc
        where
          ccs = curry-closure-setup
          cts = curry-thunk-setup-prog
          code-f = compile-x86 f
          cta = curry-tail
          prog-reassoc : prefix ++ (ccs ++ cts ++ code-f ++ cta) ++ suffix ≡ prefix-f ++ code-f ++ suffix-f
          prog-reassoc =
            let inner-assoc1 : ccs ++ (cts ++ (code-f ++ cta)) ≡ (ccs ++ cts) ++ (code-f ++ cta)
                inner-assoc1 = sym (++-assoc ccs cts (code-f ++ cta))
                inner-assoc2 : ((ccs ++ cts) ++ (code-f ++ cta)) ++ suffix ≡ (ccs ++ cts) ++ ((code-f ++ cta) ++ suffix)
                inner-assoc2 = ++-assoc (ccs ++ cts) (code-f ++ cta) suffix
                inner-assoc3 : (code-f ++ cta) ++ suffix ≡ code-f ++ (cta ++ suffix)
                inner-assoc3 = ++-assoc code-f cta suffix
                inner-combined : (ccs ++ (cts ++ (code-f ++ cta))) ++ suffix ≡ (ccs ++ cts) ++ (code-f ++ (cta ++ suffix))
                inner-combined = trans (cong (_++ suffix) inner-assoc1)
                                 (trans inner-assoc2 (cong ((ccs ++ cts) ++_) inner-assoc3))
                outer-step : prefix ++ ((ccs ++ (cts ++ (code-f ++ cta))) ++ suffix) ≡ prefix ++ ((ccs ++ cts) ++ (code-f ++ (cta ++ suffix)))
                outer-step = cong (prefix ++_) inner-combined
                final-assoc : prefix ++ ((ccs ++ cts) ++ (code-f ++ (cta ++ suffix))) ≡ (prefix ++ (ccs ++ cts)) ++ (code-f ++ (cta ++ suffix))
                final-assoc = sym (++-assoc prefix (ccs ++ cts) (code-f ++ (cta ++ suffix)))
            in trans outer-step final-assoc

      pc-setup-f : pc s-after-setup ≡ length prefix-f
      pc-setup-f = trans pc-setup (sym len-prefix-f)

      input-valid-f : ValidAt (env , arg) (readReg (regs s-after-setup) rdi) (memory s-after-setup)
      input-valid-f = v-pair-setup

      cap-setup : StackCapacity s-after-setup (ir-stack-requirement f)
      cap-setup = capacity-after-delta s s-after-setup thunk-setup-consumed-slots (ir-stack-requirement f)
                    cap-thunk rsp-setup

      -- Recursive call via rec (replaces run-ir-star-at-offset-v ... (smaller-acc ...))
      step-f-v : ∃[ s-f ] IRStarResultV f (prefix-f ++ compile-x86 f ++ suffix-f) s-after-setup s-f (env , arg) (length prefix-f)
      step-f-v = rec f f<bound prefix-f suffix-f caller-sp (env , arg) s-after-setup
                   h-setup pc-setup-f input-valid-f stack-inv-setup cap-setup rbp-inv-setup

      s-after-f-raw : State
      s-after-f-raw = proj₁ step-f-v

      r-f-v : IRStarResultV f (prefix-f ++ compile-x86 f ++ suffix-f) s-after-setup s-after-f-raw (env , arg) (length prefix-f)
      r-f-v = proj₂ step-f-v

      star-f-raw : Star (prefix-f ++ compile-x86 f ++ suffix-f) s-after-setup s-after-f-raw
      star-f-raw = IRStarResultV.ir-star r-f-v

      result-valid-f : ValidAt (eval f (env , arg)) (readReg (regs s-after-f-raw) rax) (memory s-after-f-raw)
      result-valid-f = IRStarResultV.ir-result-valid r-f-v

      star-f-converted : Star prog s-after-setup s-after-f-raw
      star-f-converted = subst (λ p → Star p s-after-setup s-after-f-raw) (sym prog-eq-f) star-f-raw

      pc-f-raw : pc s-after-f-raw ≡ length prefix-f +ℕ compile-length f
      pc-f-raw = IRStarResultV.ir-pc r-f-v

      cleanup-offset = length prefix +ℕ 14 +ℕ compile-length f

      pc-f-at-cleanup : pc s-after-f-raw ≡ cleanup-offset
      pc-f-at-cleanup = trans pc-f-raw (cong (_+ℕ len-f) len-prefix-f)

      -- Cleanup phase: mov rsp rbp, pop rbp, pop r15
      old-rsp-s = readReg (regs s) rsp
      rbp-val = readReg (regs s-after-f-raw) rbp

      rbp-after-f : readReg (regs s-after-f-raw) rbp ≡ readReg (regs s) rsp ∸ pair-alloc
      rbp-after-f = trans (IRStarResultV.ir-rbp r-f-v) rbp-setup

      -- State after mov rsp, rbp
      s-c1 : State
      s-c1 = record s-after-f-raw { regs = writeReg (regs s-after-f-raw) rsp rbp-val
                                  ; pc = pc s-after-f-raw +ℕ 1 }

      fetch-c0 : fetch prog cleanup-offset ≡ just cleanup-i0
      fetch-c0 = fetch-cleanup-i0 f prefix suffix

      step-c0 : step prog s-after-f-raw ≡ just s-c1
      step-c0 = trans (step-exec prog s-after-f-raw cleanup-i0 (IRStarResultV.ir-halted r-f-v)
                        (subst (λ n → fetch prog n ≡ just cleanup-i0) (sym pc-f-at-cleanup) fetch-c0))
                      (execMov-reg-reg s-after-f-raw rsp rbp)

      h-c1 : halted s-c1 ≡ false
      h-c1 = IRStarResultV.ir-halted r-f-v

      pc-c1 : pc s-c1 ≡ cleanup-offset +ℕ 1
      pc-c1 = cong (_+ℕ 1) pc-f-at-cleanup

      mem-c1-eq-f : ∀ addr → readMem (memory s-c1) addr ≡ readMem (memory s-after-f-raw) addr
      mem-c1-eq-f addr = refl

      rsp-c1-inline : readReg (regs s-c1) rsp ≡ old-rsp-s ∸ pair-alloc
      rsp-c1-inline = trans (readReg-writeReg-same (regs s-after-f-raw) rsp rbp-val) rbp-after-f

      -- Derive rsp > pair-alloc from cap-thunk
      rsp>slots2 : readReg (regs s) rsp > pair-alloc
      rsp>slots2 = ≤-<-trans (slots-mono-≤ (m≤m+n 2 (output-slots +ℕ ir-stack-requirement f))) (StackCapacity.rsp-sufficient cap-thunk)

      16≤rsp : pair-alloc ≤ readReg (regs s) rsp
      16≤rsp = <⇒≤ rsp>slots2

      -- Memory at rbp preserved through f
      mem-rbp-preserved-f : readMem (memory s-after-f-raw) (readReg (regs s-after-setup) rbp) ≡
                            readMem (memory s-after-setup) (readReg (regs s-after-setup) rbp)
      mem-rbp-preserved-f = IRStarResultV.ir-mem-rbp r-f-v

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

      -- State after pop rbp
      s-c2 : State
      s-c2 = record s-c1 { regs = writeReg (writeReg (regs s-c1) rbp (readReg (regs s) rbp))
                                          rsp (readReg (regs s-c1) rsp +ℕ slot-size)
                         ; pc = pc s-c1 +ℕ 1 }

      cleanup-offset-plus-1 : cleanup-offset +ℕ 1 ≡ (length prefix +ℕ 15) +ℕ len-f
      cleanup-offset-plus-1 = trans (+-assoc (length prefix +ℕ 14) len-f 1)
                                    (trans (cong ((length prefix +ℕ 14) +ℕ_) (Data-Nat-+-comm len-f 1))
                                           (trans (sym (+-assoc (length prefix +ℕ 14) 1 len-f))
                                                  (cong (_+ℕ len-f) (+-assoc (length prefix) 14 1))))

      fetch-c1 : fetch prog (cleanup-offset +ℕ 1) ≡ just cleanup-i1
      fetch-c1 = subst (λ n → fetch prog n ≡ just cleanup-i1)
                       (sym cleanup-offset-plus-1)
                       (fetch-cleanup-i1 f prefix suffix)

      step-c1 : step prog s-c1 ≡ just s-c2
      step-c1 = trans (step-exec prog s-c1 cleanup-i1 h-c1
                        (subst (λ n → fetch prog n ≡ just cleanup-i1) (sym pc-c1) fetch-c1))
                      (execPop prog s-c1 rbp (readReg (regs s) rbp) pop-rbp-mem)

      h-c2 : halted s-c2 ≡ false
      h-c2 = h-c1

      pc-c2 : pc s-c2 ≡ cleanup-offset +ℕ 2
      pc-c2 = trans (cong (_+ℕ 1) pc-c1) (+-assoc cleanup-offset 1 1)

      rsp-c1 : readReg (regs s-c1) rsp ≡ old-rsp-s ∸ pair-alloc
      rsp-c1 = trans (readReg-writeReg-same (regs s-after-f-raw) rsp rbp-val) rbp-after-f

      8≤old-rsp-8 : slot-size ≤ old-rsp-s ∸ slot-size
      8≤old-rsp-8 = ∸-monoˡ-≤ slot-size 16≤rsp

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
          ≡⟨ trans (Data-Nat-+-comm ((old-rsp-s ∸ slot-size) ∸ slot-size) slot-size) (m+[n∸m]≡n 8≤old-rsp-8) ⟩
        old-rsp-s ∸ slot-size
        ∎

      -- Register preservation through cleanup
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
      cleanup-offset-plus-2 : cleanup-offset +ℕ 2 ≡ (length prefix +ℕ 16) +ℕ len-f
      cleanup-offset-plus-2 = trans (+-assoc (length prefix +ℕ 14) len-f 2)
                                    (trans (cong ((length prefix +ℕ 14) +ℕ_) (Data-Nat-+-comm len-f 2))
                                           (trans (sym (+-assoc (length prefix +ℕ 14) 2 len-f))
                                                  (cong (_+ℕ len-f) (+-assoc (length prefix) 14 2))))

      fetch-c2 : fetch prog (cleanup-offset +ℕ 2) ≡ just cleanup-i2
      fetch-c2 = subst (λ n → fetch prog n ≡ just cleanup-i2)
                       (sym cleanup-offset-plus-2)
                       (fetch-cleanup-i2 f prefix suffix)

      orig-r15 = readReg (regs s) r15
      rsp-val-c3 = readReg (regs s-c2) rsp +ℕ slot-size

      s-c3 : State
      s-c3 = record s-c2 { regs = writeReg (writeReg (regs s-c2) r15 orig-r15)
                                          rsp rsp-val-c3
                         ; pc = pc s-c2 +ℕ 1 }

      rsp-16<rsp-8 : readReg (regs s) rsp ∸ pair-alloc < readReg (regs s) rsp ∸ slot-size
      rsp-16<rsp-8 = ∸-monoʳ-< word-fits-pair-strict 16≤rsp

      old-rsp-8>rbp : old-rsp-s ∸ slot-size > readReg (regs s-after-setup) rbp
      old-rsp-8>rbp = subst (λ x → old-rsp-s ∸ slot-size > x) (sym rbp-setup-addr) rsp-16<rsp-8

      pop-r15-mem : readMem (memory s-c2) (readReg (regs s-c2) rsp) ≡ just orig-r15
      pop-r15-mem = begin
        readMem (memory s-c2) (readReg (regs s-c2) rsp)
          ≡⟨ cong (readMem (memory s-c2)) rsp-c2 ⟩
        readMem (memory s-c2) (old-rsp-s ∸ slot-size)
          ≡⟨⟩
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

      prefix-14+3 : (length prefix +ℕ 14) +ℕ 3 ≡ length prefix +ℕ 17
      prefix-14+3 = +-assoc (length prefix) 14 3

      cleanup-plus-3≡ret : cleanup-offset +ℕ 3 ≡ ret-offset
      cleanup-plus-3≡ret = trans (+-assoc (length prefix +ℕ 14) len-f 3)
                                 (trans (cong ((length prefix +ℕ 14) +ℕ_) (Data-Nat-+-comm len-f 3))
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

      rsp-c3 : readReg (regs s-c3) rsp ≡ old-rsp-s
      rsp-c3 = begin
        readReg (regs s-c3) rsp
          ≡⟨ readReg-writeReg-same (writeReg (regs s-c2) r15 orig-r15) rsp rsp-val-c3 ⟩
        rsp-val-c3
          ≡⟨⟩
        readReg (regs s-c2) rsp +ℕ slot-size
          ≡⟨ cong (_+ℕ slot-size) rsp-c2 ⟩
        (old-rsp-s ∸ slot-size) +ℕ slot-size
          ≡⟨ trans (Data-Nat-+-comm (old-rsp-s ∸ slot-size) slot-size) (m+[n∸m]≡n 8≤rsp) ⟩
        old-rsp-s
        ∎

      rax-c3 : readReg (regs s-c3) rax ≡ readReg (regs s-after-f-raw) rax
      rax-c3 = trans (readReg-writeReg-rsp-rax (writeReg (regs s-c2) r15 orig-r15) rsp-val-c3)
                     (trans (readReg-writeReg-r15-rax (regs s-c2) orig-r15) rax-c2)

      r14-c3 : readReg (regs s-c3) r14 ≡ readReg (regs s-after-f-raw) r14
      r14-c3 = trans (readReg-writeReg-rsp-r14 (writeReg (regs s-c2) r15 orig-r15) rsp-val-c3)
                     (trans (readReg-writeReg-r15-r14 (regs s-c2) orig-r15) r14-c2)

      r15-c3 : readReg (regs s-c3) r15 ≡ orig-r15
      r15-c3 = trans (readReg-writeReg-rsp-r15 (writeReg (regs s-c2) r15 orig-r15) rsp-val-c3)
                     (readReg-writeReg-same (regs s-c2) r15 orig-r15)

      rbp-c3 : readReg (regs s-c3) rbp ≡ readReg (regs s) rbp
      rbp-c3 = trans (readReg-writeReg-rsp-rbp (writeReg (regs s-c2) r15 orig-r15) rsp-val-c3)
                     (trans (readReg-writeReg-r15-rbp (regs s-c2) orig-r15) rbp-c2)

      star-c : Star prog s-after-f-raw s-c3
      star-c = ⟨ IRStarResultV.ir-halted r-f-v , step-c0 ⟩◅ ⟨ h-c1 , step-c1 ⟩◅ ⟨ h-c2 , step-c2 ⟩◅ refl*

      rsp-sufficient-c3 : readReg (regs s-c3) rsp > pair-alloc
      rsp-sufficient-c3 = subst (_> pair-alloc) (sym rsp-c3) rsp>slots2

      r15-s-to-c3 : readReg (regs s-c3) r15 ≡ readReg (regs s) r15
      r15-s-to-c3 = r15-c3

      stack-inv-c3 : StackInvariant s-c3
      stack-inv-c3 = stack-inv-preserved-unchanged s s-c3 stack-inv r15-s-to-c3 rsp-c3

      mem-cleanup-preserves : ∀ addr → readMem (memory s-c3) addr ≡ readMem (memory s-after-f-raw) addr
      mem-cleanup-preserves addr = mem-c1-eq-f addr

      rax-cleanup : readReg (regs s-c3) rax ≡ readReg (regs s-after-f-raw) rax
      rax-cleanup = rax-c3

      mem-cleanup-preserved : ∀ addr → readMem (memory s-c3) addr ≡ readMem (memory s-after-f-raw) addr
      mem-cleanup-preserved = mem-cleanup-preserves

      -- Return address preserved
      mem-ret-through-setup : readMem (memory s-after-setup) old-rsp-s ≡ just ret-addr
      mem-ret-through-setup = trans mem-old-rsp-setup mem-ret

      rbp+16≡old-rsp : readReg (regs s-after-setup) rbp +ℕ pair-alloc ≡ old-rsp-s
      rbp+16≡old-rsp = trans (cong (_+ℕ pair-alloc) rbp-setup-addr)
                             (trans (Data-Nat-+-comm (old-rsp-s ∸ pair-alloc) (pair-alloc)) (m+[n∸m]≡n 16≤rsp))

      old-rsp>rbp : old-rsp-s > readReg (regs s-after-setup) rbp
      old-rsp>rbp = subst (_> readReg (regs s-after-setup) rbp)
                         rbp+16≡old-rsp
                         (m<m+n (readReg (regs s-after-setup) rbp) {pair-alloc} (s≤s z≤n))

      mem-ret-through-f : readMem (memory s-after-f-raw) old-rsp-s ≡ just ret-addr
      mem-ret-through-f = begin
        readMem (memory s-after-f-raw) old-rsp-s
          ≡⟨ IRStarResultV.ir-mem-above r-f-v old-rsp-s old-rsp>rbp ⟩
        readMem (memory s-after-setup) old-rsp-s
          ≡⟨ mem-ret-through-setup ⟩
        just ret-addr ∎

      mem-ret-preserved : readMem (memory s-c3) (readReg (regs s-c3) rsp) ≡ just ret-addr
      mem-ret-preserved = subst (λ addr → readMem (memory s-c3) addr ≡ just ret-addr)
                                (sym rsp-c3)
                                (trans (mem-c1-eq-f old-rsp-s) mem-ret-through-f)

      s-after-f : State
      s-after-f = s-c3

      star-f-to-cleanup : Star prog s-after-setup s-c3
      star-f-to-cleanup = star-trans star-f-converted star-c

      star-f : Star prog s-after-setup s-after-f
      star-f = star-f-to-cleanup

      h-f : halted s-after-f ≡ false
      h-f = h-c3

      pc-f : pc s-after-f ≡ ret-offset
      pc-f = pc-c3

      r14-f : readReg (regs s-after-f) r14 ≡ readReg (regs s-after-setup) r14
      r14-f = trans r14-c3 (IRStarResultV.ir-r14 r-f-v)

      r15-f : readReg (regs s-after-f) r15 ≡ readReg (regs s-after-setup) r15
      r15-f = trans r15-c3 (sym r15-setup)

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
      r15-in-code-f : InCode (readReg (regs s-after-f) r15)
      r15-in-code-f = subst InCode (sym r15-f-eq-s) r15-in-code-entry
        where
          r15-f-eq-setup : readReg (regs s-after-f) r15 ≡ readReg (regs s-after-setup) r15
          r15-f-eq-setup = r15-f
          r15-f-eq-s : readReg (regs s-after-f) r15 ≡ readReg (regs s) r15
          r15-f-eq-s = trans r15-f-eq-setup r15-setup

      ret-result-pair : ∃[ s-fin ] ThunkRetResult prog s-after-f s-fin ret-addr
      ret-result-pair = thunk-ret-star f prefix suffix ret-addr s-after-f
                          h-f pc-f mem-ret-f r15-in-code-f rsp-sufficient-f

      s-final : State
      s-final = proj₁ ret-result-pair

      ret-rec : ThunkRetResult prog s-after-f s-final ret-addr
      ret-rec = proj₂ ret-result-pair

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

      star-all : Star prog s s-final
      star-all = star-trans star-setup (star-trans star-f star-ret)

      thunk-rsp-plus-8-proof : readReg (regs s-final) rsp ≡ readReg (regs s) rsp +ℕ slot-size
      thunk-rsp-plus-8-proof = trans rsp-ret-plus-8 (cong (_+ℕ slot-size) rsp-f-restored)

      rsp-final-is-caller : readReg (regs s-final) rsp ≡ sp-addr caller-sp
      rsp-final-is-caller = trans thunk-rsp-plus-8-proof (sym caller-sp-bound)

      rsp-final-in-stack : InStack (readReg (regs s-final) rsp)
      rsp-final-in-stack = subst InStack (sym rsp-final-is-caller) (in-stack caller-sp)

      result-valid-after-cleanup : ValidAt (eval f (env , arg)) (readReg (regs s-after-f) rax) (memory s-after-f)
      result-valid-after-cleanup = valid-subst-addr-mem result-valid-f rax-cleanup mem-cleanup-preserved

      thunk-result-valid-proof : ValidAt (eval f (env , arg)) (readReg (regs s-final) rax) (memory s-final)
      thunk-result-valid-proof = valid-subst-addr-mem result-valid-after-cleanup rax-final mem-ret-preserves

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
          the-slot-addr = slot-addr caller-sp k
          slot-addr>rbp : the-slot-addr > readReg (regs s-after-setup) rbp
          slot-addr>rbp = slot-addr-above-thunk-rbp caller-sp k
                           (readReg (regs s) rsp) (readReg (regs s-after-setup) rbp)
                           caller-sp-bound rbp-setup rsp>slots2
          rsp+8≤slot : readReg (regs s) rsp +ℕ slot-size ≤ the-slot-addr
          rsp+8≤slot = subst (_≤ the-slot-addr) caller-sp-bound (slot-addr-≥-base caller-sp k)
          rsp<rsp+slot : readReg (regs s) rsp < readReg (regs s) rsp +ℕ slot-size
          rsp<rsp+slot = m<m+n (readReg (regs s) rsp) (s≤s z≤n)
          slot-addr>rsp : the-slot-addr > readReg (regs s) rsp
          slot-addr>rsp = <-≤-trans rsp<rsp+slot rsp+8≤slot
          setup-preserves-caller-slot : readMem (memory s-after-setup) the-slot-addr ≡
                                        readMem (memory s) the-slot-addr
          setup-preserves-caller-slot = mem-above-setup the-slot-addr slot-addr>rsp

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
        ; thunk-rbp = trans rbp-final rbp-f
        ; thunk-stack-inv = stack-inv-final
        ; thunk-capacity = rsp-bound-to-capacity 2 s-final rsp-final-in-stack rsp-sufficient-final
        ; thunk-rsp-plus-8 = thunk-rsp-plus-8-proof
        ; thunk-preserves-frame = thunk-preserves-frame-proof
        ; thunk-preserves-code = thunk-preserves-code-proof
        ; thunk-preserves-heap = thunk-preserves-heap-proof
        ; thunk-preserves-above-entry-rsp = thunk-preserves-above-entry-rsp-proof
        }
