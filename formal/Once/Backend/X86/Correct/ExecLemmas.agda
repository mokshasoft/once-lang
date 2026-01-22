------------------------------------------------------------------------
-- Once.Backend.X86.Correct.ExecLemmas
--
-- Execution lemmas for x86-64 code generation proofs.
-- Level 2 - depends on Foundation (which includes FetchStep, InstrExec, RegisterLemmas).
------------------------------------------------------------------------

module Once.Backend.X86.Correct.ExecLemmas where

-- Import consolidated Foundation module
open import Once.Backend.X86.Correct.Foundation

-- Import helpers from Star module (re-exported publicly)
open import Once.Backend.X86.Correct.Star
  using (just-injective)
  public

-- Additional imports not in Foundation
open import Data.Nat using (_≟_; _≥_; _>_)
open import Data.Nat.Properties using (∸-+-assoc; +-assoc; +-comm)
open import Data.List.Properties using (++-assoc) renaming (length-++ to List-length-++)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≢_; cong₂; subst₂) renaming ([_] to Reveal[_])
open import Once.Backend.X86.Correct.CompileLength using (compile-length-correct)

------------------------------------------------------------------------
-- Exec Lemmas
------------------------------------------------------------------------

-- | Helper for just-injective
just-inj : ∀ {A : Set} {x y : A} → just x ≡ just y → x ≡ y
just-inj refl = refl

-- | Helper: derive halted s ≡ false from step and result halted status
-- If step prog s = just s' and halted s' = false, then halted s = false
-- PROVEN: By case split on halted s. In the true case, step reduces to just s,
-- so s' = s and halted s' = true, contradicting the hypothesis.
step-implies-not-halted : ∀ (prog : List Instr) (s s' : State) →
  step prog s ≡ just s' →
  halted s' ≡ false →
  halted s ≡ false
step-implies-not-halted prog s s' step-eq h'-eq with halted s | inspect halted s
... | false | _ = refl
-- In true case: step prog s = just s, so step-eq : just s ≡ just s'
-- This means s ≡ s' (by just-inj). Then halted s' = halted s = true.
-- But h'-eq says halted s' = false. Contradiction.
... | true | Reveal[ h-eq ] = ⊥-elim (true≢false (trans (sym h-eq) halted-s-is-false))
  where
    -- step-eq : just s ≡ just s', so s ≡ s'
    s≡s' : s ≡ s'
    s≡s' = just-inj step-eq
    -- halted s ≡ halted s' ≡ false
    halted-s-is-false : halted s ≡ false
    halted-s-is-false = trans (cong halted s≡s') h'-eq
    -- true≢false provided by Foundation

-- | Fetching at the end of a prefix returns the first element of suffix
-- fetch (prefix ++ i ∷ rest) (length prefix) ≡ just i
fetch-at-prefix-end : ∀ (prefix : Program) (i : Instr) (rest : Program) →
  fetch (prefix ++ i ∷ rest) (length prefix) ≡ just i
fetch-at-prefix-end [] i rest = refl
fetch-at-prefix-end (x ∷ prefix) i rest = fetch-at-prefix-end prefix i rest

-- | Execute transfer instruction (mov rdi, rax) at position N in a program
-- Used between sub-programs in compose to transfer result to input
transfer-star : ∀ (prefix : Program) (suffix : Program) (s : State) →
  halted s ≡ false →
  pc s ≡ length prefix →
  ∃[ s' ] (step (prefix ++ mov (reg rdi) (reg rax) ∷ suffix) s ≡ just s'
         × halted s' ≡ false
         × pc s' ≡ length prefix +ℕ 1
         × readReg (regs s') rdi ≡ readReg (regs s) rax
         × readReg (regs s') rax ≡ readReg (regs s) rax)
transfer-star prefix suffix s h-false pc-eq = s' , step-eq , h' , pc' , rdi-eq , rax-eq
  where
    prog : Program
    prog = prefix ++ mov (reg rdi) (reg rax) ∷ suffix

    s' : State
    s' = record s { regs = writeReg (regs s) rdi (readReg (regs s) rax)
                  ; pc = pc s +ℕ 1 }

    fetch-eq : fetch prog (pc s) ≡ just (mov (reg rdi) (reg rax))
    fetch-eq = subst (λ p → fetch prog p ≡ just (mov (reg rdi) (reg rax)))
                     (sym pc-eq) (fetch-at-prefix-end prefix (mov (reg rdi) (reg rax)) suffix)

    step-eq : step prog s ≡ just s'
    step-eq = trans (step-exec prog s (mov (reg rdi) (reg rax)) h-false fetch-eq)
                    (execMov-reg-reg s rdi rax)

    h' : halted s' ≡ false
    h' = h-false

    pc' : pc s' ≡ length prefix +ℕ 1
    pc' = cong (λ p → p +ℕ 1) pc-eq

    rdi-eq : readReg (regs s') rdi ≡ readReg (regs s) rax
    rdi-eq = readReg-writeReg-same (regs s) rdi (readReg (regs s) rax)

    rax-eq : readReg (regs s') rax ≡ readReg (regs s) rax
    rax-eq = readReg-writeReg-rdi-rax (regs s) (readReg (regs s) rax)

-- | Extended transfer-star with full register and memory preservation
-- Used for implementing compose-run-transfer in ArchInstantiation
transfer-star-full : ∀ (prefix : Program) (suffix : Program) (s : State) →
  halted s ≡ false →
  pc s ≡ length prefix →
  ∃[ s' ] (step (prefix ++ mov (reg rdi) (reg rax) ∷ suffix) s ≡ just s'
         × halted s' ≡ false
         × pc s' ≡ length prefix +ℕ 1
         × readReg (regs s') rdi ≡ readReg (regs s) rax
         × readReg (regs s') rax ≡ readReg (regs s) rax
         × readReg (regs s') r14 ≡ readReg (regs s) r14
         × readReg (regs s') r15 ≡ readReg (regs s) r15
         × readReg (regs s') rsp ≡ readReg (regs s) rsp
         × readReg (regs s') rbp ≡ readReg (regs s) rbp
         × (∀ addr → readMem (memory s') addr ≡ readMem (memory s) addr))
transfer-star-full prefix suffix s h-false pc-eq = s' , step-eq , h' , pc' , rdi-eq , rax-eq , r14-eq , r15-eq , rsp-eq , rbp-eq , mem-eq
  where
    prog : Program
    prog = prefix ++ mov (reg rdi) (reg rax) ∷ suffix

    s' : State
    s' = record s { regs = writeReg (regs s) rdi (readReg (regs s) rax)
                  ; pc = pc s +ℕ 1 }

    fetch-eq : fetch prog (pc s) ≡ just (mov (reg rdi) (reg rax))
    fetch-eq = subst (λ p → fetch prog p ≡ just (mov (reg rdi) (reg rax)))
                     (sym pc-eq) (fetch-at-prefix-end prefix (mov (reg rdi) (reg rax)) suffix)

    step-eq : step prog s ≡ just s'
    step-eq = trans (step-exec prog s (mov (reg rdi) (reg rax)) h-false fetch-eq)
                    (execMov-reg-reg s rdi rax)

    h' : halted s' ≡ false
    h' = h-false

    pc' : pc s' ≡ length prefix +ℕ 1
    pc' = cong (λ p → p +ℕ 1) pc-eq

    rdi-eq : readReg (regs s') rdi ≡ readReg (regs s) rax
    rdi-eq = readReg-writeReg-same (regs s) rdi (readReg (regs s) rax)

    rax-eq : readReg (regs s') rax ≡ readReg (regs s) rax
    rax-eq = readReg-writeReg-rdi-rax (regs s) (readReg (regs s) rax)

    r14-eq : readReg (regs s') r14 ≡ readReg (regs s) r14
    r14-eq = readReg-writeReg-rdi-r14 (regs s) (readReg (regs s) rax)

    r15-eq : readReg (regs s') r15 ≡ readReg (regs s) r15
    r15-eq = readReg-writeReg-rdi-r15 (regs s) (readReg (regs s) rax)

    rsp-eq : readReg (regs s') rsp ≡ readReg (regs s) rsp
    rsp-eq = readReg-writeReg-rdi-rsp (regs s) (readReg (regs s) rax)

    rbp-eq : readReg (regs s') rbp ≡ readReg (regs s) rbp
    rbp-eq = readReg-writeReg-rdi-rbp (regs s) (readReg (regs s) rax)

    mem-eq : ∀ addr → readMem (memory s') addr ≡ readMem (memory s) addr
    mem-eq _ = refl

------------------------------------------------------------------------
-- Single-IR execution at offset lemmas
------------------------------------------------------------------------

-- | Execute id at arbitrary offset in a program (non-halting)
-- This is the general case of run-id-nonhalt where id code can be at any position
-- Program structure: prefix ++ [mov rax, rdi] ++ suffix
run-id-at-offset : ∀ {A} (prefix suffix : Program) (x : ⟦ A ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ length prefix →
  readReg (regs s) rdi ≡ encode x →
  ∃[ s' ] (step (prefix ++ compile-x86 (id {A}) ++ suffix) s ≡ just s'
         × halted s' ≡ false
         × pc s' ≡ length prefix +ℕ 1
         × readReg (regs s') rax ≡ encode x)
run-id-at-offset {A} prefix suffix x s h-false pc-eq rdi-eq = s' , step-eq , h' , pc' , rax-eq
  where
    prog : Program
    prog = prefix ++ compile-x86 (id {A}) ++ suffix

    s' : State
    s' = record s { regs = writeReg (regs s) rax (readReg (regs s) rdi)
                  ; pc = pc s +ℕ 1 }

    fetch-eq : fetch prog (pc s) ≡ just (mov (reg rax) (reg rdi))
    fetch-eq = subst (λ p → fetch prog p ≡ just (mov (reg rax) (reg rdi)))
                     (sym pc-eq) (fetch-at-prefix-end prefix (mov (reg rax) (reg rdi)) suffix)

    step-eq : step prog s ≡ just s'
    step-eq = trans (step-exec prog s (mov (reg rax) (reg rdi)) h-false fetch-eq)
                    (execMov-reg-reg s rax rdi)

    h' : halted s' ≡ false
    h' = h-false

    pc' : pc s' ≡ length prefix +ℕ 1
    pc' = cong (λ p → p +ℕ 1) pc-eq

    rax-eq : readReg (regs s') rax ≡ encode x
    rax-eq = trans (readReg-writeReg-same (regs s) rax (readReg (regs s) rdi)) rdi-eq

-- | Execute terminal at arbitrary offset in a program (non-halting)
-- Program structure: prefix ++ [mov rax, 0] ++ suffix
run-terminal-at-offset : ∀ {A} (prefix suffix : Program) (x : ⟦ A ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ length prefix →
  ∃[ s' ] (step (prefix ++ compile-x86 (terminal {A}) ++ suffix) s ≡ just s'
         × halted s' ≡ false
         × pc s' ≡ length prefix +ℕ 1
         × readReg (regs s') rax ≡ encode {Unit} tt)
run-terminal-at-offset {A} prefix suffix x s h-false pc-eq = s' , step-eq , h' , pc' , rax-eq
  where
    prog : Program
    prog = prefix ++ compile-x86 (terminal {A}) ++ suffix

    s' : State
    s' = record s { regs = writeReg (regs s) rax 0
                  ; pc = pc s +ℕ 1 }

    fetch-eq : fetch prog (pc s) ≡ just (mov (reg rax) (imm 0))
    fetch-eq = subst (λ p → fetch prog p ≡ just (mov (reg rax) (imm 0)))
                     (sym pc-eq) (fetch-at-prefix-end prefix (mov (reg rax) (imm 0)) suffix)

    step-eq : step prog s ≡ just s'
    step-eq = trans (step-exec prog s (mov (reg rax) (imm 0)) h-false fetch-eq)
                    (execMov-reg-imm s rax 0)

    h' : halted s' ≡ false
    h' = h-false

    pc' : pc s' ≡ length prefix +ℕ 1
    pc' = cong (λ p → p +ℕ 1) pc-eq

    rax-eq : readReg (regs s') rax ≡ encode {Unit} tt
    rax-eq = trans (readReg-writeReg-same (regs s) rax 0) (sym encode-unit)

-- | Execute fold at arbitrary offset in a program (non-halting)
-- compile-x86 fold = [mov rax, rdi] (same as id)
-- Result is encode (wrap x) = encode x by encode-fix-wrap
run-fold-at-offset : ∀ {F} (prefix suffix : Program) (x : ⟦ F ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ length prefix →
  readReg (regs s) rdi ≡ encode x →
  ∃[ s' ] (step (prefix ++ compile-x86 (fold {F}) ++ suffix) s ≡ just s'
         × halted s' ≡ false
         × pc s' ≡ length prefix +ℕ 1
         × readReg (regs s') rax ≡ encode (wrap x))
run-fold-at-offset {F} prefix suffix x s h-false pc-eq rdi-eq = s' , step-eq , h' , pc' , rax-eq
  where
    prog : Program
    prog = prefix ++ compile-x86 (fold {F}) ++ suffix

    s' : State
    s' = record s { regs = writeReg (regs s) rax (readReg (regs s) rdi)
                  ; pc = pc s +ℕ 1 }

    fetch-eq : fetch prog (pc s) ≡ just (mov (reg rax) (reg rdi))
    fetch-eq = subst (λ p → fetch prog p ≡ just (mov (reg rax) (reg rdi)))
                     (sym pc-eq) (fetch-at-prefix-end prefix (mov (reg rax) (reg rdi)) suffix)

    step-eq : step prog s ≡ just s'
    step-eq = trans (step-exec prog s (mov (reg rax) (reg rdi)) h-false fetch-eq)
                    (execMov-reg-reg s rax rdi)

    h' : halted s' ≡ false
    h' = h-false

    pc' : pc s' ≡ length prefix +ℕ 1
    pc' = cong (λ p → p +ℕ 1) pc-eq

    rax-eq : readReg (regs s') rax ≡ encode (wrap x)
    rax-eq = trans (readReg-writeReg-same (regs s) rax (readReg (regs s) rdi))
                   (trans rdi-eq (encode-fix-wrap x))

-- | Execute unfold at arbitrary offset in a program (non-halting)
-- compile-x86 unfold = [mov rax, rdi] (same as id)
-- Result is encode (eval unfold x) by encode-fix-unwrap
run-unfold-at-offset : ∀ {F} (prefix suffix : Program) (x : ⟦ Fix F ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ length prefix →
  readReg (regs s) rdi ≡ encode x →
  ∃[ s' ] (step (prefix ++ compile-x86 (unfold {F}) ++ suffix) s ≡ just s'
         × halted s' ≡ false
         × pc s' ≡ length prefix +ℕ 1
         × readReg (regs s') rax ≡ encode (eval unfold x))
run-unfold-at-offset {F} prefix suffix x s h-false pc-eq rdi-eq = s' , step-eq , h' , pc' , rax-eq
  where
    prog : Program
    prog = prefix ++ compile-x86 (unfold {F}) ++ suffix

    s' : State
    s' = record s { regs = writeReg (regs s) rax (readReg (regs s) rdi)
                  ; pc = pc s +ℕ 1 }

    fetch-eq : fetch prog (pc s) ≡ just (mov (reg rax) (reg rdi))
    fetch-eq = subst (λ p → fetch prog p ≡ just (mov (reg rax) (reg rdi)))
                     (sym pc-eq) (fetch-at-prefix-end prefix (mov (reg rax) (reg rdi)) suffix)

    step-eq : step prog s ≡ just s'
    step-eq = trans (step-exec prog s (mov (reg rax) (reg rdi)) h-false fetch-eq)
                    (execMov-reg-reg s rax rdi)

    h' : halted s' ≡ false
    h' = h-false

    pc' : pc s' ≡ length prefix +ℕ 1
    pc' = cong (λ p → p +ℕ 1) pc-eq

    -- eval unfold x = unwrap x, encode (unwrap x) = encode x by encode-fix-unwrap
    rax-eq : readReg (regs s') rax ≡ encode (eval unfold x)
    rax-eq = trans (readReg-writeReg-same (regs s) rax (readReg (regs s) rdi))
                   (trans rdi-eq (encode-fix-unwrap x))

-- | Execute arr at arbitrary offset in a program (non-halting)
-- compile-x86 arr = [mov rax, rdi] (same as id)
-- arr : IR (A ⇒ B) (Eff A B), eval arr f = f (identity)
-- encode (eval arr f) = encode f
run-arr-at-offset : ∀ {A B} (prefix suffix : Program) (f : ⟦ A ⇒ B ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ length prefix →
  readReg (regs s) rdi ≡ encode {A ⇒ B} f →
  ∃[ s' ] (step (prefix ++ compile-x86 (arr {A} {B}) ++ suffix) s ≡ just s'
         × halted s' ≡ false
         × pc s' ≡ length prefix +ℕ 1
         × readReg (regs s') rax ≡ encode {Eff A B} f)
run-arr-at-offset {A} {B} prefix suffix f s h-false pc-eq rdi-eq = s' , step-eq , h' , pc' , rax-eq
  where
    prog : Program
    prog = prefix ++ compile-x86 (arr {A} {B}) ++ suffix

    s' : State
    s' = record s { regs = writeReg (regs s) rax (readReg (regs s) rdi)
                  ; pc = pc s +ℕ 1 }

    fetch-eq : fetch prog (pc s) ≡ just (mov (reg rax) (reg rdi))
    fetch-eq = subst (λ p → fetch prog p ≡ just (mov (reg rax) (reg rdi)))
                     (sym pc-eq) (fetch-at-prefix-end prefix (mov (reg rax) (reg rdi)) suffix)

    step-eq : step prog s ≡ just s'
    step-eq = trans (step-exec prog s (mov (reg rax) (reg rdi)) h-false fetch-eq)
                    (execMov-reg-reg s rax rdi)

    h' : halted s' ≡ false
    h' = h-false

    pc' : pc s' ≡ length prefix +ℕ 1
    pc' = cong (λ p → p +ℕ 1) pc-eq

    -- eval arr f = f, and encode-arr-identity says encode {A ⇒ B} f ≡ encode {Eff A B} f
    rax-eq : readReg (regs s') rax ≡ encode {Eff A B} f
    rax-eq = trans (readReg-writeReg-same (regs s) rax (readReg (regs s) rdi))
                   (trans rdi-eq (encode-arr-identity f))

-- | Execute fst at arbitrary offset in a program (non-halting)
-- compile-x86 fst = [mov rax, [rdi]] (1 instruction)
run-fst-at-offset : ∀ {A B} (prefix suffix : Program) (a : ⟦ A ⟧) (b : ⟦ B ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ length prefix →
  readReg (regs s) rdi ≡ encode (a , b) →
  readMem (memory s) (encode (a , b)) ≡ just (encode a) →
  ∃[ s' ] (step (prefix ++ compile-x86 (fst {A} {B}) ++ suffix) s ≡ just s'
         × halted s' ≡ false
         × pc s' ≡ length prefix +ℕ 1
         × readReg (regs s') rax ≡ encode a)
run-fst-at-offset {A} {B} prefix suffix a b s h-false pc-eq rdi-eq mem-eq = s' , step-eq , h' , pc' , rax-eq
  where
    prog : Program
    prog = prefix ++ compile-x86 (fst {A} {B}) ++ suffix

    s' : State
    s' = record s { regs = writeReg (regs s) rax (encode a)
                  ; pc = pc s +ℕ 1 }

    fetch-eq : fetch prog (pc s) ≡ just (mov (reg rax) (mem (base rdi)))
    fetch-eq = subst (λ p → fetch prog p ≡ just (mov (reg rax) (mem (base rdi))))
                     (sym pc-eq) (fetch-at-prefix-end prefix (mov (reg rax) (mem (base rdi))) suffix)

    step-eq : step prog s ≡ just s'
    step-eq = trans (step-exec prog s (mov (reg rax) (mem (base rdi))) h-false fetch-eq)
                    (execMov-reg-mem-base s rax rdi (encode a)
                      (trans (cong (λ addr → readMem (memory s) addr) rdi-eq) mem-eq))

    h' : halted s' ≡ false
    h' = h-false

    pc' : pc s' ≡ length prefix +ℕ 1
    pc' = cong (λ p → p +ℕ 1) pc-eq

    rax-eq : readReg (regs s') rax ≡ encode a
    rax-eq = readReg-writeReg-same (regs s) rax (encode a)

-- | Execute snd at arbitrary offset in a program (non-halting)
-- compile-x86 snd = [mov rax, [rdi+8]] (1 instruction)
run-snd-at-offset : ∀ {A B} (prefix suffix : Program) (a : ⟦ A ⟧) (b : ⟦ B ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ length prefix →
  readReg (regs s) rdi ≡ encode (a , b) →
  readMem (memory s) (encode (a , b) +ℕ 8) ≡ just (encode b) →
  ∃[ s' ] (step (prefix ++ compile-x86 (snd {A} {B}) ++ suffix) s ≡ just s'
         × halted s' ≡ false
         × pc s' ≡ length prefix +ℕ 1
         × readReg (regs s') rax ≡ encode b)
run-snd-at-offset {A} {B} prefix suffix a b s h-false pc-eq rdi-eq mem-eq = s' , step-eq , h' , pc' , rax-eq
  where
    prog : Program
    prog = prefix ++ compile-x86 (snd {A} {B}) ++ suffix

    s' : State
    s' = record s { regs = writeReg (regs s) rax (encode b)
                  ; pc = pc s +ℕ 1 }

    fetch-eq : fetch prog (pc s) ≡ just (mov (reg rax) (mem (base+disp rdi 8)))
    fetch-eq = subst (λ p → fetch prog p ≡ just (mov (reg rax) (mem (base+disp rdi 8))))
                     (sym pc-eq) (fetch-at-prefix-end prefix (mov (reg rax) (mem (base+disp rdi 8))) suffix)

    step-eq : step prog s ≡ just s'
    step-eq = trans (step-exec prog s (mov (reg rax) (mem (base+disp rdi 8))) h-false fetch-eq)
                    (execMov-reg-mem-disp s rax rdi 8 (encode b)
                      (trans (cong (λ addr → readMem (memory s) (addr +ℕ 8)) rdi-eq) mem-eq))

    h' : halted s' ≡ false
    h' = h-false

    pc' : pc s' ≡ length prefix +ℕ 1
    pc' = cong (λ p → p +ℕ 1) pc-eq

    rax-eq : readReg (regs s') rax ≡ encode b
    rax-eq = readReg-writeReg-same (regs s) rax (encode b)

------------------------------------------------------------------------
-- Stateful fst/snd: use explicit addresses instead of encode
--
-- These versions eliminate the dependency on encoding postulates by:
-- 1. Taking explicit addresses (addr-pair, addr-a, addr-b) instead of values
-- 2. Taking memory layout preconditions instead of encoding axioms
-- 3. Returning explicit addresses instead of encode results
------------------------------------------------------------------------

-- | Execute fst at offset with EXPLICIT addresses (stateful, no encode)
-- Precondition: memory at addr-pair contains addr-a
-- Result: rax = addr-a
run-fst-at-offset-s : ∀ {A B : Type} (prefix suffix : Program)
    (addr-pair addr-a : Word) (s : State) →
  halted s ≡ false →
  pc s ≡ length prefix →
  readReg (regs s) rdi ≡ addr-pair →
  readMem (memory s) addr-pair ≡ just addr-a →
  ∃[ s' ] (step (prefix ++ compile-x86 (fst {A} {B}) ++ suffix) s ≡ just s'
         × halted s' ≡ false
         × pc s' ≡ length prefix +ℕ 1
         × readReg (regs s') rax ≡ addr-a)
run-fst-at-offset-s {A} {B} prefix suffix addr-pair addr-a s h-false pc-eq rdi-eq mem-eq =
  s' , step-eq , h' , pc' , rax-eq
  where
    prog : Program
    prog = prefix ++ compile-x86 (fst {A} {B}) ++ suffix

    s' : State
    s' = record s { regs = writeReg (regs s) rax addr-a
                  ; pc = pc s +ℕ 1 }

    fetch-eq : fetch prog (pc s) ≡ just (mov (reg rax) (mem (base rdi)))
    fetch-eq = subst (λ p → fetch prog p ≡ just (mov (reg rax) (mem (base rdi))))
                     (sym pc-eq) (fetch-at-prefix-end prefix (mov (reg rax) (mem (base rdi))) suffix)

    step-eq : step prog s ≡ just s'
    step-eq = trans (step-exec prog s (mov (reg rax) (mem (base rdi))) h-false fetch-eq)
                    (execMov-reg-mem-base s rax rdi addr-a
                      (trans (cong (λ addr → readMem (memory s) addr) rdi-eq) mem-eq))

    h' : halted s' ≡ false
    h' = h-false

    pc' : pc s' ≡ length prefix +ℕ 1
    pc' = cong (λ p → p +ℕ 1) pc-eq

    rax-eq : readReg (regs s') rax ≡ addr-a
    rax-eq = readReg-writeReg-same (regs s) rax addr-a

-- | Execute snd at offset with EXPLICIT addresses (stateful, no encode)
-- Precondition: memory at addr-pair+8 contains addr-b
-- Result: rax = addr-b
run-snd-at-offset-s : ∀ {A B : Type} (prefix suffix : Program)
    (addr-pair addr-b : Word) (s : State) →
  halted s ≡ false →
  pc s ≡ length prefix →
  readReg (regs s) rdi ≡ addr-pair →
  readMem (memory s) (addr-pair +ℕ 8) ≡ just addr-b →
  ∃[ s' ] (step (prefix ++ compile-x86 (snd {A} {B}) ++ suffix) s ≡ just s'
         × halted s' ≡ false
         × pc s' ≡ length prefix +ℕ 1
         × readReg (regs s') rax ≡ addr-b)
run-snd-at-offset-s {A} {B} prefix suffix addr-pair addr-b s h-false pc-eq rdi-eq mem-eq =
  s' , step-eq , h' , pc' , rax-eq
  where
    prog : Program
    prog = prefix ++ compile-x86 (snd {A} {B}) ++ suffix

    s' : State
    s' = record s { regs = writeReg (regs s) rax addr-b
                  ; pc = pc s +ℕ 1 }

    fetch-eq : fetch prog (pc s) ≡ just (mov (reg rax) (mem (base+disp rdi 8)))
    fetch-eq = subst (λ p → fetch prog p ≡ just (mov (reg rax) (mem (base+disp rdi 8))))
                     (sym pc-eq) (fetch-at-prefix-end prefix (mov (reg rax) (mem (base+disp rdi 8))) suffix)

    step-eq : step prog s ≡ just s'
    step-eq = trans (step-exec prog s (mov (reg rax) (mem (base+disp rdi 8))) h-false fetch-eq)
                    (execMov-reg-mem-disp s rax rdi 8 addr-b
                      (trans (cong (λ addr → readMem (memory s) (addr +ℕ 8)) rdi-eq) mem-eq))

    h' : halted s' ≡ false
    h' = h-false

    pc' : pc s' ≡ length prefix +ℕ 1
    pc' = cong (λ p → p +ℕ 1) pc-eq

    rax-eq : readReg (regs s') rax ≡ addr-b
    rax-eq = readReg-writeReg-same (regs s) rax addr-b

-- | Execute mov rdi, rax at arbitrary offset (transfer result to input register)
-- This is the glue instruction between composed programs
run-mov-rdi-rax-at-offset : ∀ (prefix suffix : Program) (s : State) →
  halted s ≡ false →
  pc s ≡ length prefix →
  ∃[ s' ] (step (prefix ++ mov (reg rdi) (reg rax) ∷ suffix) s ≡ just s'
         × halted s' ≡ false
         × pc s' ≡ length prefix +ℕ 1
         × readReg (regs s') rdi ≡ readReg (regs s) rax
         × readReg (regs s') rax ≡ readReg (regs s) rax)
run-mov-rdi-rax-at-offset prefix suffix s h-false pc-eq = s' , step-eq , h' , pc' , rdi-eq , rax-eq
  where
    prog : Program
    prog = prefix ++ mov (reg rdi) (reg rax) ∷ suffix

    s' : State
    s' = record s { regs = writeReg (regs s) rdi (readReg (regs s) rax)
                  ; pc = pc s +ℕ 1 }

    fetch-eq : fetch prog (pc s) ≡ just (mov (reg rdi) (reg rax))
    fetch-eq = subst (λ p → fetch prog p ≡ just (mov (reg rdi) (reg rax)))
                     (sym pc-eq) (fetch-at-prefix-end prefix (mov (reg rdi) (reg rax)) suffix)

    step-eq : step prog s ≡ just s'
    step-eq = trans (step-exec prog s (mov (reg rdi) (reg rax)) h-false fetch-eq)
                    (execMov-reg-reg s rdi rax)

    h' : halted s' ≡ false
    h' = h-false

    pc' : pc s' ≡ length prefix +ℕ 1
    pc' = cong (λ p → p +ℕ 1) pc-eq

    rdi-eq : readReg (regs s') rdi ≡ readReg (regs s) rax
    rdi-eq = readReg-writeReg-same (regs s) rdi (readReg (regs s) rax)

    -- rax is preserved (we only wrote to rdi)
    rax-eq : readReg (regs s') rax ≡ readReg (regs s) rax
    rax-eq = readReg-writeReg-rdi-rax (regs s) (readReg (regs s) rax)

------------------------------------------------------------------------
-- compile-length properties
------------------------------------------------------------------------

-- | compile-length is always positive (at least 1)
-- PROVEN: By structural induction on IR. All base cases are ≥ 1.
compile-length>0 : ∀ {A B} (ir : IR A B) → compile-length ir > 0
compile-length>0 id = s≤s z≤n
compile-length>0 (g ∘ f) = comp-pos (compile-length f) (compile-length g)
  where
    -- n + suc m = suc (n + m) > 0 (definitionally!)
    n+suc-pos : (n m : ℕ) → n +ℕ suc m > 0
    n+suc-pos zero m = s≤s z≤n
    n+suc-pos (suc n) m = s≤s z≤n
    -- (n + 1) + m > 0 via +-assoc
    comp-pos : (n m : ℕ) → (n +ℕ 1) +ℕ m > 0
    comp-pos n m = subst (_> 0) (sym (+-assoc n 1 m)) (n+suc-pos n m)
compile-length>0 fst = s≤s z≤n
compile-length>0 snd = s≤s z≤n
compile-length>0 ⟨ f , g ⟩ = pair-pos (compile-length f) (compile-length g)
  where
    pair-pos : (n m : ℕ) → (pair-overhead +ℕ n) +ℕ m > 0
    pair-pos n m = s≤s z≤n
compile-length>0 inl = s≤s z≤n
compile-length>0 inr = s≤s z≤n
compile-length>0 [ f , g ] = case-pos (compile-length f) (compile-length g)
  where
    case-pos : (n m : ℕ) → (case-overhead +ℕ n) +ℕ m > 0
    case-pos n m = s≤s z≤n
compile-length>0 terminal = s≤s z≤n
compile-length>0 initial = s≤s z≤n
compile-length>0 (curry f) = curry-pos (compile-length f)
  where
    curry-pos : (n : ℕ) → curry-overhead +ℕ n > 0
    curry-pos n = s≤s z≤n
compile-length>0 apply = s≤s z≤n
compile-length>0 fold = s≤s z≤n
compile-length>0 unfold = s≤s z≤n
compile-length>0 arr = s≤s z≤n
compile-length>0 (Prim _) = s≤s z≤n

------------------------------------------------------------------------
-- Case cleanup fetch lemmas
--
-- Proves fetch at cleanup position by stepping through the code structure:
-- skip setup (6) → skip compile-x86 f → skip middle (3) → skip compile-x86 g → head
------------------------------------------------------------------------

-- | Fetch cleanup-mov at case-cleanup-position
-- Position = 6 + len-f + 3 + len-g (computed symbolically in CodeGen)
fetch-case-cleanup-mov : ∀ {A B C} (f : IR A C) (g : IR B C) (suffix : Program) →
  fetch (compile-x86 [ f , g ] ++ suffix) (case-cleanup-position f g) ≡
  just (mov (reg rsp) (reg rbp))
fetch-case-cleanup-mov f g suffix =
  trans (cong (λ n → fetch code n) pos-expand)
        (trans skip-setup
               (trans skip-f
                      (trans skip-middle
                             (trans skip-g refl))))
  where
    len-f = compile-length f
    len-g = compile-length g
    code = compile-x86 [ f , g ] ++ suffix

    -- Expand case-cleanup-position to 6 + (len-f + (3 + len-g))
    -- case-cleanup-position f g = ((6 + len-f) + 3) + len-g  (left-assoc)
    -- = (6 + len-f) + (3 + len-g)  [+-assoc]
    -- = 6 + (len-f + (3 + len-g))  [+-assoc]
    pos-expand : case-cleanup-position f g ≡ 6 +ℕ (len-f +ℕ (3 +ℕ len-g))
    pos-expand = trans (+-assoc (6 +ℕ len-f) 3 len-g)
                       (+-assoc 6 len-f (3 +ℕ len-g))

    -- The code segments inside compile-x86 [ f , g ]
    -- rest = compile-x86 f ++ (jmp ∷ label ∷ mov ∷ (compile-x86 g ++ (mov rsp rbp ∷ pop ∷ [])))
    rest-inner = jmp (case-jmp-base +ℕ len-g) ∷
                 label (case-right-label-base +ℕ len-f) ∷
                 mov (reg rdi) (mem (base+disp rdi slot-size)) ∷
                 compile-x86 g ++
                 mov (reg rsp) (reg rbp) ∷ pop rbp ∷ []

    rest = compile-x86 f ++ rest-inner

    -- after-setup = rest ++ suffix (correctly structured)
    after-setup = rest ++ suffix

    -- Skip 6 setup instructions (definitional - just list indexing)
    skip-setup : fetch code (6 +ℕ (len-f +ℕ (3 +ℕ len-g))) ≡
                 fetch after-setup (len-f +ℕ (3 +ℕ len-g))
    skip-setup = refl

    -- Use ++-assoc to rewrite after-setup for the next step
    -- after-setup = (compile-x86 f ++ rest-inner) ++ suffix
    --             = compile-x86 f ++ (rest-inner ++ suffix)
    after-f-inner = rest-inner ++ suffix

    after-setup-assoc : after-setup ≡ compile-x86 f ++ after-f-inner
    after-setup-assoc = ++-assoc (compile-x86 f) rest-inner suffix

    -- Skip compile-x86 f using fetch-append-right
    skip-f : fetch after-setup (len-f +ℕ (3 +ℕ len-g)) ≡ fetch after-f-inner (3 +ℕ len-g)
    skip-f = trans (cong (λ xs → fetch xs (len-f +ℕ (3 +ℕ len-g))) after-setup-assoc)
                   (trans (cong (λ n → fetch (compile-x86 f ++ after-f-inner) (n +ℕ (3 +ℕ len-g)))
                                (sym (compile-length-correct f)))
                          (fetch-append-right (compile-x86 f) after-f-inner (3 +ℕ len-g)))

    -- The code after middle (3 instructions)
    -- after-f-inner = (jmp ∷ label ∷ mov ∷ (compile-x86 g ++ [mov, pop])) ++ suffix
    -- By ++-assoc: = jmp ∷ label ∷ mov ∷ ((compile-x86 g ++ [mov, pop]) ++ suffix)
    g-cleanup = compile-x86 g ++ mov (reg rsp) (reg rbp) ∷ pop rbp ∷ []
    after-middle = g-cleanup ++ suffix

    -- Skip 3 middle instructions (definitional after the ++ distributes through ∷)
    skip-middle : fetch after-f-inner (3 +ℕ len-g) ≡ fetch after-middle len-g
    skip-middle = refl

    -- Use ++-assoc again for compile-x86 g
    cleanup = mov (reg rsp) (reg rbp) ∷ pop rbp ∷ suffix

    after-middle-assoc : after-middle ≡ compile-x86 g ++ cleanup
    after-middle-assoc = ++-assoc (compile-x86 g) (mov (reg rsp) (reg rbp) ∷ pop rbp ∷ []) suffix

    -- Skip compile-x86 g using fetch-append-right
    skip-g : fetch after-middle len-g ≡ fetch cleanup 0
    skip-g = trans (cong (λ xs → fetch xs len-g) after-middle-assoc)
                   (trans (cong (λ n → fetch (compile-x86 g ++ cleanup) n)
                                (trans (sym (compile-length-correct g))
                                       (sym (+-identityʳ (length (compile-x86 g))))))
                          (fetch-append-right (compile-x86 g) cleanup 0))
      where
        open import Data.Nat.Properties using (+-identityʳ)

-- | Fetch cleanup-pop at case-cleanup-position + 1
fetch-case-cleanup-pop : ∀ {A B C} (f : IR A C) (g : IR B C) (suffix : Program) →
  fetch (compile-x86 [ f , g ] ++ suffix) (case-cleanup-position f g +ℕ 1) ≡
  just (pop rbp)
fetch-case-cleanup-pop f g suffix =
  trans (cong (λ n → fetch code n) pos-expand)
        (trans skip-setup
               (trans skip-f
                      (trans skip-middle
                             (trans skip-g refl))))
  where
    len-f = compile-length f
    len-g = compile-length g
    code = compile-x86 [ f , g ] ++ suffix

    -- Expand case-cleanup-position + 1 to 6 + (len-f + (3 + (len-g + 1)))
    -- case-cleanup-position f g + 1 = (((6 + len-f) + 3) + len-g) + 1
    -- Step 1: (((6 + len-f) + 3) + len-g) + 1 = ((6 + len-f) + 3) + (len-g + 1)
    -- Step 2: ((6 + len-f) + 3) + (len-g + 1) = (6 + len-f) + (3 + (len-g + 1))
    -- Step 3: (6 + len-f) + (3 + (len-g + 1)) = 6 + (len-f + (3 + (len-g + 1)))
    pos-expand : case-cleanup-position f g +ℕ 1 ≡ 6 +ℕ (len-f +ℕ (3 +ℕ (len-g +ℕ 1)))
    pos-expand = trans (+-assoc ((6 +ℕ len-f) +ℕ 3) len-g 1)
                       (trans (+-assoc (6 +ℕ len-f) 3 (len-g +ℕ 1))
                              (+-assoc 6 len-f (3 +ℕ (len-g +ℕ 1))))

    -- Structure: same as fetch-case-cleanup-mov but fetch index is len-g + 1 instead of len-g
    rest-inner = jmp (case-jmp-base +ℕ len-g) ∷
                 label (case-right-label-base +ℕ len-f) ∷
                 mov (reg rdi) (mem (base+disp rdi slot-size)) ∷
                 compile-x86 g ++
                 mov (reg rsp) (reg rbp) ∷ pop rbp ∷ []

    rest = compile-x86 f ++ rest-inner
    after-setup = rest ++ suffix

    skip-setup : fetch code (6 +ℕ (len-f +ℕ (3 +ℕ (len-g +ℕ 1)))) ≡
                 fetch after-setup (len-f +ℕ (3 +ℕ (len-g +ℕ 1)))
    skip-setup = refl

    -- Use ++-assoc to rewrite after-setup for the next step
    after-f-inner = rest-inner ++ suffix

    after-setup-assoc : after-setup ≡ compile-x86 f ++ after-f-inner
    after-setup-assoc = ++-assoc (compile-x86 f) rest-inner suffix

    skip-f : fetch after-setup (len-f +ℕ (3 +ℕ (len-g +ℕ 1))) ≡ fetch after-f-inner (3 +ℕ (len-g +ℕ 1))
    skip-f = trans (cong (λ xs → fetch xs (len-f +ℕ (3 +ℕ (len-g +ℕ 1)))) after-setup-assoc)
                   (trans (cong (λ n → fetch (compile-x86 f ++ after-f-inner) (n +ℕ (3 +ℕ (len-g +ℕ 1))))
                                (sym (compile-length-correct f)))
                          (fetch-append-right (compile-x86 f) after-f-inner (3 +ℕ (len-g +ℕ 1))))

    -- The code after middle (3 instructions)
    g-cleanup = compile-x86 g ++ mov (reg rsp) (reg rbp) ∷ pop rbp ∷ []
    after-middle = g-cleanup ++ suffix

    skip-middle : fetch after-f-inner (3 +ℕ (len-g +ℕ 1)) ≡ fetch after-middle (len-g +ℕ 1)
    skip-middle = refl

    -- Use ++-assoc again for compile-x86 g
    cleanup = mov (reg rsp) (reg rbp) ∷ pop rbp ∷ suffix

    after-middle-assoc : after-middle ≡ compile-x86 g ++ cleanup
    after-middle-assoc = ++-assoc (compile-x86 g) (mov (reg rsp) (reg rbp) ∷ pop rbp ∷ []) suffix

    skip-g : fetch after-middle (len-g +ℕ 1) ≡ fetch cleanup 1
    skip-g = trans (cong (λ xs → fetch xs (len-g +ℕ 1)) after-middle-assoc)
                   (trans (cong (λ n → fetch (compile-x86 g ++ cleanup) (n +ℕ 1))
                                (sym (compile-length-correct g)))
                          (fetch-append-right (compile-x86 g) cleanup 1))
