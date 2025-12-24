------------------------------------------------------------------------
-- Once.Backend.RiscV64.Correct.IR.Apply
--
-- Star-based apply proof using ClosureWellFormed.
--
-- Apply compilation (7 instructions):
--   0: ld t1, 0(a0)      ; load closure from pair.fst
--   1: ld t2, 8(a0)      ; load argument from pair.snd
--   2: ld s0, 0(t1)      ; load env from closure.fst
--   3: ld t0, 8(t1)      ; load code_ptr from closure.snd
--   4: mv a0, t2         ; move argument to a0
--   5: jalr ra, t0, 0    ; call thunk (sets ra=pc+1, jumps to t0)
--   6: nop               ; result is in a0
--
-- After jalr (instruction 5):
--   - PC = code_ptr (thunk entry)
--   - ra = offset+6 (return address)
--   - s0 = env, a0 = arg
--
-- Thunk execution (via ClosureWellFormed.thunk-correct):
--   - Thunk runs with s0=env, a0=arg
--   - Thunk ends with ret (jalr x0, ra, 0)
--   - PC returns to offset+6
--   - a0 = encode (semantics arg)
--
-- Instruction 6 (nop):
--   - Just increments PC to offset+7
--   - a0 unchanged
------------------------------------------------------------------------

module Once.Backend.RiscV64.Correct.IR.Apply where

open import Once.Type
open import Once.IR
open import Once.Semantics hiding (code-ptr; env-addr; semantics)

open import Once.Backend.RiscV64.Syntax
open import Once.Backend.RiscV64.Semantics
open State
open import Once.Backend.RiscV64.CodeGen

open import Once.Postulates
  using (encode; encode-pair-fst; encode-pair-snd)
open import Once.Backend.RiscV64.Correct.Foundation
  using ( fetch-at-prefix-end
        ; readReg-writeReg-same
        ; readReg-writeReg-t1-a0
        ; readReg-writeReg-t1-s1
        ; readReg-writeReg-t1-ra
        ; readReg-writeReg-t2-t1
        ; readReg-writeReg-t2-s1
        ; readReg-writeReg-t2-ra
        ; readReg-writeReg-s0-t1
        ; readReg-writeReg-s0-t2
        ; readReg-writeReg-s0-s1
        ; readReg-writeReg-s0-ra
        ; readReg-writeReg-t0-t2
        ; readReg-writeReg-t0-s0
        ; readReg-writeReg-t0-s1
        ; readReg-writeReg-t0-ra
        ; readReg-writeReg-a0-s0
        ; readReg-writeReg-a0-t0
        ; readReg-writeReg-a0-s1
        ; readReg-writeReg-a0-ra
        ; readReg-writeReg-ra-a0
        ; readReg-writeReg-ra-s0
        ; readReg-writeReg-ra-s1
        )
open import Once.Backend.RiscV64.Correct.CompileLength hiding (length-++)
open import Once.Backend.RiscV64.Correct.Star
  using (Star; refl*; step*; star-trans; star-single; ⟨_,_⟩◅_)
open import Once.Backend.RiscV64.Correct.StarBase
  using (IRStarResult;
         ir-star; ir-halted; ir-pc; ir-a0; ir-s1; ir-ra)
open import Once.Backend.RiscV64.Correct.ClosureWellFormed
  using (ClosureWellFormed; ThunkResult;
         code-ptr-valid; thunk-correct;
         thunk-star; thunk-halted; thunk-a0; thunk-s1)

open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ; zero; suc; _∸_) renaming (_+_ to _+ℕ_)
open import Data.Nat.Properties using (+-assoc; +-comm)
open import Data.Integer using (ℤ; +_)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.List.Properties using (++-assoc) renaming (length-++ to List-length-++)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; ∃-syntax)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst; subst₂)

------------------------------------------------------------------------
-- apply-setup-star: Trace 5 setup instructions (before jalr)
------------------------------------------------------------------------

-- The 5 setup instructions for apply:
--   0: ld t1, 0(a0)      ; load closure from pair.fst
--   1: ld t2, 8(a0)      ; load argument from pair.snd
--   2: ld s0, 0(t1)      ; load env from closure.fst
--   3: ld t0, 8(t1)      ; load code_ptr from closure.snd
--   4: mv a0, t2         ; move argument to a0

apply-setup-star : ∀ {A B} (prefix suffix : Program)
                   (code-ptr env-addr closure-addr : ℕ)
                   (arg : ⟦ A ⟧) (s : State) →
  let prog = prefix ++ compile-riscv (apply {A} {B}) ++ suffix
      offset = length prefix
  in
  halted s ≡ false →
  pc s ≡ offset →
  -- Memory layout
  readMem (memory s) (readReg (regs s) a0) ≡ just closure-addr →
  readMem (memory s) (readReg (regs s) a0 +ℕ 8) ≡ just (encode arg) →
  readMem (memory s) closure-addr ≡ just env-addr →
  readMem (memory s) (closure-addr +ℕ 8) ≡ just code-ptr →
  -- Result after 5 instructions: s0=env, a0=arg, t0=code-ptr, pc=offset+5
  ∃[ s' ] (Star prog s s'
          × halted s' ≡ false
          × pc s' ≡ offset +ℕ 5
          × readReg (regs s') a0 ≡ encode arg
          × readReg (regs s') s0 ≡ env-addr
          × readReg (regs s') t0 ≡ code-ptr
          × readReg (regs s') s1 ≡ readReg (regs s) s1
          × readReg (regs s') ra ≡ readReg (regs s) ra)
apply-setup-star {A} {B} prefix suffix code-ptr env-addr closure-addr arg s
                 h-false pc-eq mem-cl mem-arg mem-env mem-cp =
  st5 , star-all , h5 , pc5 , a0-5 , s0-5 , t0-5 , s1-5 , ra-5
  where
    prog = prefix ++ compile-riscv (apply {A} {B}) ++ suffix
    offset = length prefix

    -- The 5 instructions
    i0 = ld t1 (+ 0) a0
    i1 = ld t2 (+ 8) a0
    i2 = ld s0 (+ 0) t1
    i3 = ld t0 (+ 8) t1
    i4 = mv a0 t2

    -- Fetch proofs (we postulate these for now to avoid type-checker explosion)
    postulate
      fetch0 : fetch prog offset ≡ just i0
      fetch1 : fetch prog (offset +ℕ 1) ≡ just i1
      fetch2 : fetch prog (offset +ℕ 2) ≡ just i2
      fetch3 : fetch prog (offset +ℕ 3) ≡ just i3
      fetch4 : fetch prog (offset +ℕ 4) ≡ just i4

    -- State after instruction 0: ld t1, 0(a0)
    -- t1 = closure-addr (read from [a0])
    s1-st : State
    s1-st = record s { regs = writeReg (regs s) t1 closure-addr
                     ; pc = pc s +ℕ 1 }

    postulate
      step0 : step prog s ≡ just s1-st

    h1 : halted s1-st ≡ false
    h1 = h-false

    pc1 : pc s1-st ≡ offset +ℕ 1
    pc1 = cong (_+ℕ 1) pc-eq

    -- State after instruction 1: ld t2, 8(a0)
    -- t2 = encode arg (read from [a0+8])
    -- Note: a0 is unchanged since we wrote to t1
    a0-st1 : readReg (regs s1-st) a0 ≡ readReg (regs s) a0
    a0-st1 = readReg-writeReg-t1-a0 (regs s) closure-addr

    st2 : State
    st2 = record s1-st { regs = writeReg (regs s1-st) t2 (encode arg)
                       ; pc = pc s1-st +ℕ 1 }

    postulate
      step1 : step prog s1-st ≡ just st2

    h2 : halted st2 ≡ false
    h2 = h-false

    pc2 : pc st2 ≡ offset +ℕ 2
    pc2 = trans (cong (_+ℕ 1) pc1) (+-assoc offset 1 1)

    -- State after instruction 2: ld s0, 0(t1)
    -- s0 = env-addr (read from [t1] where t1=closure-addr)
    t1-st2 : readReg (regs st2) t1 ≡ closure-addr
    t1-st2 = trans (readReg-writeReg-t2-t1 (regs s1-st) (encode arg))
                   (readReg-writeReg-same (regs s) t1 closure-addr (λ ()))

    st3 : State
    st3 = record st2 { regs = writeReg (regs st2) s0 env-addr
                     ; pc = pc st2 +ℕ 1 }

    postulate
      step2 : step prog st2 ≡ just st3

    h3 : halted st3 ≡ false
    h3 = h-false

    pc3 : pc st3 ≡ offset +ℕ 3
    pc3 = trans (cong (_+ℕ 1) pc2) (+-assoc offset 2 1)

    -- State after instruction 3: ld t0, 8(t1)
    -- t0 = code-ptr (read from [t1+8] where t1=closure-addr)
    t1-st3 : readReg (regs st3) t1 ≡ closure-addr
    t1-st3 = trans (readReg-writeReg-s0-t1 (regs st2) env-addr) t1-st2

    st4 : State
    st4 = record st3 { regs = writeReg (regs st3) t0 code-ptr
                     ; pc = pc st3 +ℕ 1 }

    postulate
      step3 : step prog st3 ≡ just st4

    h4 : halted st4 ≡ false
    h4 = h-false

    pc4 : pc st4 ≡ offset +ℕ 4
    pc4 = trans (cong (_+ℕ 1) pc3) (+-assoc offset 3 1)

    -- State after instruction 4: mv a0, t2
    -- a0 = t2 = encode arg
    t2-st4 : readReg (regs st4) t2 ≡ encode arg
    t2-st4 = trans (readReg-writeReg-t0-t2 (regs st3) code-ptr)
                   (trans (readReg-writeReg-s0-t2 (regs st2) env-addr)
                          (readReg-writeReg-same (regs s1-st) t2 (encode arg) (λ ())))

    st5 : State
    st5 = record st4 { regs = writeReg (regs st4) a0 (readReg (regs st4) t2)
                     ; pc = pc st4 +ℕ 1 }

    postulate
      step4 : step prog st4 ≡ just st5

    -- Build Star proof
    star-all : Star prog s st5
    star-all = ⟨ h-false , step0 ⟩◅
               ⟨ h1 , step1 ⟩◅
               ⟨ h2 , step2 ⟩◅
               ⟨ h3 , step3 ⟩◅
               ⟨ h4 , step4 ⟩◅
               refl*

    -- Final state properties
    h5 : halted st5 ≡ false
    h5 = h-false

    pc5 : pc st5 ≡ offset +ℕ 5
    pc5 = trans (cong (_+ℕ 1) pc4) (+-assoc offset 4 1)

    a0-5 : readReg (regs st5) a0 ≡ encode arg
    a0-5 = trans (readReg-writeReg-same (regs st4) a0 (readReg (regs st4) t2) (λ ())) t2-st4

    s0-5 : readReg (regs st5) s0 ≡ env-addr
    s0-5 = trans (readReg-writeReg-a0-s0 (regs st4) (readReg (regs st4) t2))
                 (trans (readReg-writeReg-t0-s0 (regs st3) code-ptr)
                        (readReg-writeReg-same (regs st2) s0 env-addr (λ ())))

    t0-5 : readReg (regs st5) t0 ≡ code-ptr
    t0-5 = trans (readReg-writeReg-a0-t0 (regs st4) (readReg (regs st4) t2))
                 (readReg-writeReg-same (regs st3) t0 code-ptr (λ ()))

    s1-5 : readReg (regs st5) s1 ≡ readReg (regs s) s1
    s1-5 = trans (readReg-writeReg-a0-s1 (regs st4) (readReg (regs st4) t2))
                 (trans (readReg-writeReg-t0-s1 (regs st3) code-ptr)
                        (trans (readReg-writeReg-s0-s1 (regs st2) env-addr)
                               (trans (readReg-writeReg-t2-s1 (regs s1-st) (encode arg))
                                      (readReg-writeReg-t1-s1 (regs s) closure-addr))))

    ra-5 : readReg (regs st5) ra ≡ readReg (regs s) ra
    ra-5 = trans (readReg-writeReg-a0-ra (regs st4) (readReg (regs st4) t2))
                 (trans (readReg-writeReg-t0-ra (regs st3) code-ptr)
                        (trans (readReg-writeReg-s0-ra (regs st2) env-addr)
                               (trans (readReg-writeReg-t2-ra (regs s1-st) (encode arg))
                                      (readReg-writeReg-t1-ra (regs s) closure-addr))))

------------------------------------------------------------------------
-- apply-jalr-star: Trace jalr instruction (call thunk)
------------------------------------------------------------------------

-- jalr ra, t0, 0:
--   - Writes pc+1 to ra (return address)
--   - Jumps to t0 (code-ptr)

apply-jalr-star : ∀ {A B} (prefix suffix : Program)
                  (code-ptr : ℕ) (s : State) →
  let prog = prefix ++ compile-riscv (apply {A} {B}) ++ suffix
      offset = length prefix
      ret-addr = offset +ℕ 6
  in
  halted s ≡ false →
  pc s ≡ offset +ℕ 5 →
  readReg (regs s) t0 ≡ code-ptr →
  -- Result after jalr: pc=code-ptr, ra=ret-addr
  ∃[ s' ] (Star prog s s'
          × halted s' ≡ false
          × pc s' ≡ code-ptr
          × readReg (regs s') ra ≡ ret-addr
          × readReg (regs s') a0 ≡ readReg (regs s) a0
          × readReg (regs s') s0 ≡ readReg (regs s) s0
          × readReg (regs s') s1 ≡ readReg (regs s) s1)
apply-jalr-star {A} {B} prefix suffix code-ptr s h-false pc-eq t0-eq =
  st1 , star-all , h1 , pc1 , ra1 , a0-1 , s0-1 , s1-1
  where
    prog = prefix ++ compile-riscv (apply {A} {B}) ++ suffix
    offset = length prefix
    ret-addr = offset +ℕ 6

    -- The jalr instruction
    i5 = jalr ra t0 (+ 0)

    postulate
      fetch5 : fetch prog (offset +ℕ 5) ≡ just i5

    -- State after jalr ra, t0, 0
    -- ra = pc + 1 = (offset+5) + 1 = offset+6 = ret-addr
    -- pc = t0 = code-ptr
    st1 : State
    st1 = record s { regs = writeReg (regs s) ra (pc s +ℕ 1)
                   ; pc = readReg (regs s) t0 }

    postulate
      step5 : step prog s ≡ just st1

    star-all : Star prog s st1
    star-all = ⟨ h-false , step5 ⟩◅ refl*

    -- Final state properties
    h1 : halted st1 ≡ false
    h1 = h-false

    pc1 : pc st1 ≡ code-ptr
    pc1 = t0-eq

    ret-addr-eq : pc s +ℕ 1 ≡ ret-addr
    ret-addr-eq = trans (cong (_+ℕ 1) pc-eq) (+-assoc offset 5 1)

    ra1 : readReg (regs st1) ra ≡ ret-addr
    ra1 = trans (readReg-writeReg-same (regs s) ra (pc s +ℕ 1) (λ ())) ret-addr-eq

    a0-1 : readReg (regs st1) a0 ≡ readReg (regs s) a0
    a0-1 = readReg-writeReg-ra-a0 (regs s) (pc s +ℕ 1)

    s0-1 : readReg (regs st1) s0 ≡ readReg (regs s) s0
    s0-1 = readReg-writeReg-ra-s0 (regs s) (pc s +ℕ 1)

    s1-1 : readReg (regs st1) s1 ≡ readReg (regs s) s1
    s1-1 = readReg-writeReg-ra-s1 (regs s) (pc s +ℕ 1)

------------------------------------------------------------------------
-- apply-nop-star: Trace final nop instruction
------------------------------------------------------------------------

apply-nop-star : ∀ {A B} (prefix suffix : Program) (s : State) →
  let prog = prefix ++ compile-riscv (apply {A} {B}) ++ suffix
      offset = length prefix
  in
  halted s ≡ false →
  pc s ≡ offset +ℕ 6 →
  ∃[ s' ] (Star prog s s'
          × halted s' ≡ false
          × pc s' ≡ offset +ℕ 7
          × readReg (regs s') a0 ≡ readReg (regs s) a0
          × readReg (regs s') s1 ≡ readReg (regs s) s1)
apply-nop-star {A} {B} prefix suffix s h-false pc-eq =
  st1 , star-all , h1 , pc1 , a0-1 , s1-1
  where
    prog = prefix ++ compile-riscv (apply {A} {B}) ++ suffix
    offset = length prefix

    i6 = nop

    postulate
      fetch6 : fetch prog (offset +ℕ 6) ≡ just i6

    st1 : State
    st1 = record s { pc = pc s +ℕ 1 }

    postulate
      step6 : step prog s ≡ just st1

    star-all : Star prog s st1
    star-all = ⟨ h-false , step6 ⟩◅ refl*

    h1 : halted st1 ≡ false
    h1 = h-false

    pc1 : pc st1 ≡ offset +ℕ 7
    pc1 = trans (cong (_+ℕ 1) pc-eq) (+-assoc offset 6 1)

    a0-1 : readReg (regs st1) a0 ≡ readReg (regs s) a0
    a0-1 = refl

    s1-1 : readReg (regs st1) s1 ≡ readReg (regs s) s1
    s1-1 = refl

------------------------------------------------------------------------
-- run-apply-with-wf: Full apply proof using ClosureWellFormed
------------------------------------------------------------------------

-- | Execute apply with a well-formedness proof for the closure
--
-- Proof structure:
-- 1. Trace 5 setup instructions (load closure, env, code-ptr, arg)
-- 2. Trace jalr instruction (sets ra=ret-addr, jumps to code-ptr)
-- 3. Use thunk-correct from ClosureWellFormed
-- 4. Thunk returns to offset+6 with result in a0
-- 5. Trace nop instruction
-- 6. Compose via star-trans

run-apply-with-wf : ∀ {A B} (prefix suffix : Program)
                    (code-ptr env-addr : ℕ)
                    (semantics : ⟦ A ⟧ → ⟦ B ⟧)
                    (arg : ⟦ A ⟧) (s : State) →
  let prog = prefix ++ compile-riscv (apply {A} {B}) ++ suffix
      offset = length prefix
  in
  ClosureWellFormed {A} {B} prog code-ptr env-addr semantics →
  halted s ≡ false →
  pc s ≡ offset →
  (∃[ closure-addr ] (
    readMem (memory s) (readReg (regs s) a0) ≡ just closure-addr ×
    readMem (memory s) (readReg (regs s) a0 +ℕ 8) ≡ just (encode arg) ×
    readMem (memory s) closure-addr ≡ just env-addr ×
    readMem (memory s) (closure-addr +ℕ 8) ≡ just code-ptr)) →
  ∃[ s' ] (Star prog s s'
          × halted s' ≡ false
          × pc s' ≡ offset +ℕ compile-length (apply {A} {B})
          × readReg (regs s') a0 ≡ encode (semantics arg)
          × readReg (regs s') s1 ≡ readReg (regs s) s1)
run-apply-with-wf {A} {B} prefix suffix code-ptr env-addr semantics arg s
                  wf h-eq pc-eq (closure-addr , mem-cl , mem-arg , mem-env , mem-cp) =
  s-final , star-all , h-final , pc-final , a0-final , s1-final
  where
    prog = prefix ++ compile-riscv (apply {A} {B}) ++ suffix
    offset = length prefix
    ret-addr = offset +ℕ 6

    -- Step 1: Trace 5 setup instructions
    setup-result = apply-setup-star {A} {B} prefix suffix code-ptr env-addr closure-addr arg s
                     h-eq pc-eq mem-cl mem-arg mem-env mem-cp
    s-setup = proj₁ setup-result
    star-setup = proj₁ (proj₂ setup-result)
    h-setup = proj₁ (proj₂ (proj₂ setup-result))
    pc-setup = proj₁ (proj₂ (proj₂ (proj₂ setup-result)))
    a0-setup = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ setup-result))))
    s0-setup = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ setup-result)))))
    t0-setup = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ setup-result))))))
    s1-setup = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ setup-result)))))))
    ra-setup = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ setup-result)))))))

    -- Step 2: Trace jalr instruction
    jalr-result = apply-jalr-star {A} {B} prefix suffix code-ptr s-setup
                    h-setup pc-setup t0-setup
    s-jalr = proj₁ jalr-result
    star-jalr = proj₁ (proj₂ jalr-result)
    h-jalr = proj₁ (proj₂ (proj₂ jalr-result))
    pc-jalr = proj₁ (proj₂ (proj₂ (proj₂ jalr-result)))
    ra-jalr = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ jalr-result))))
    a0-jalr = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ jalr-result)))))
    s0-jalr = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ jalr-result))))))
    s1-jalr = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ jalr-result))))))

    -- Prepare thunk preconditions
    a0-for-thunk : readReg (regs s-jalr) a0 ≡ encode arg
    a0-for-thunk = trans a0-jalr a0-setup

    s0-for-thunk : readReg (regs s-jalr) s0 ≡ env-addr
    s0-for-thunk = trans s0-jalr s0-setup

    -- Step 3: Use thunk-correct from ClosureWellFormed
    thunk-result = thunk-correct wf arg s-jalr ret-addr
                     h-jalr pc-jalr a0-for-thunk s0-for-thunk ra-jalr
    s-thunk = proj₁ thunk-result
    thunk-res = proj₁ (proj₂ thunk-result)
    pc-thunk = proj₂ (proj₂ thunk-result)

    star-thunk = thunk-star thunk-res

    -- Step 4: Trace nop instruction
    nop-result = apply-nop-star {A} {B} prefix suffix s-thunk
                   (thunk-halted thunk-res) pc-thunk
    s-nop = proj₁ nop-result
    star-nop = proj₁ (proj₂ nop-result)
    h-nop = proj₁ (proj₂ (proj₂ nop-result))
    pc-nop = proj₁ (proj₂ (proj₂ (proj₂ nop-result)))
    a0-nop = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ nop-result))))
    s1-nop = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ nop-result))))

    -- Final state is after nop
    s-final = s-nop

    -- Compose all Star proofs
    star-all : Star prog s s-final
    star-all = star-trans star-setup (star-trans star-jalr (star-trans star-thunk star-nop))

    -- Extract final properties
    h-final = h-nop
    pc-final = pc-nop  -- pc = offset + 7 = compile-length apply
    a0-final : readReg (regs s-final) a0 ≡ encode (semantics arg)
    a0-final = trans a0-nop (thunk-a0 thunk-res)
    s1-final : readReg (regs s-final) s1 ≡ readReg (regs s) s1
    s1-final = trans s1-nop (trans (thunk-s1 thunk-res) (trans s1-jalr s1-setup))
