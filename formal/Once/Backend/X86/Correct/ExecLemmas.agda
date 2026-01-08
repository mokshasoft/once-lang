------------------------------------------------------------------------
-- Once.Backend.X86.Correct.ExecLemmas
--
-- Execution lemmas for x86-64 code generation proofs.
-- Level 2 - depends on Foundation (which includes FetchStep, InstrExec, RegisterLemmas).
------------------------------------------------------------------------

module Once.Backend.X86.Correct.ExecLemmas where

-- Import consolidated Foundation module
open import Once.Backend.X86.Correct.Foundation

-- Import helpers from Star module (exec-step-helper re-exported publicly)
open import Once.Backend.X86.Correct.Star
  using (exec-step-helper; exec-on-halted; just-injective; step-on-non-halted)
  public

-- Additional imports not in Foundation
open import Data.Nat using (_≟_; _≥_; _>_)
open import Data.Nat.Properties using (∸-+-assoc; +-assoc; +-comm)
open import Data.List.Properties using (++-assoc) renaming (length-++ to List-length-++)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≢_; cong₂; subst₂) renaming ([_] to Reveal[_])

------------------------------------------------------------------------
-- Exec Lemmas
------------------------------------------------------------------------

-- | Exec returns immediately when step returns halted state
-- Now requires halted s ≡ false since exec checks halted s first
-- PROVEN: Uses exec-step-helper and the fact that exec on halted state returns immediately
exec-on-halted-step : ∀ (n : ℕ) (prog : List Instr) (s s' : State) →
  halted s ≡ false →
  step prog s ≡ just s' →
  halted s' ≡ true →
  exec (suc n) prog s ≡ just s'
exec-on-halted-step n prog s s' h-eq step-eq halt-eq =
  exec-step-helper h-eq step-eq (exec-n-halted n prog s' halt-eq)
  where
    -- When halted s' = true, exec n prog s' = just s'
    exec-n-halted : ∀ m prog s → halted s ≡ true → exec m prog s ≡ just s
    exec-n-halted zero _ s _ = refl
    exec-n-halted (suc m) prog s h with halted s | h
    ... | true | refl = refl

-- | Exec continues recursively when step returns non-halted state
-- Now requires halted s ≡ false since exec checks halted s first
-- PROVEN: Uses rewrite to reduce exec, matching the pattern from exec-step-helper.
exec-on-non-halted-step : ∀ (n : ℕ) (prog : List Instr) (s s' : State) →
  halted s ≡ false →
  step prog s ≡ just s' →
  halted s' ≡ false →
  exec (suc n) prog s ≡ exec n prog s'
exec-on-non-halted-step n prog s s' h-false step-eq h'-false
  rewrite h-false | step-on-non-halted {prog} {s} h-false | step-eq | h'-false = refl

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

-- | Single-step non-halting execution: execute exactly 1 step without halting
-- Key lemma for sub-program execution where we don't want to halt
exec-one-step-nonhalt : ∀ (prog : List Instr) (s s' : State) →
  step prog s ≡ just s' →
  halted s' ≡ false →
  exec 1 prog s ≡ just s'
exec-one-step-nonhalt prog s s' step-eq halt-eq =
  trans (exec-on-non-halted-step 0 prog s s' h-eq step-eq halt-eq) refl
  where
    h-eq : halted s ≡ false
    h-eq = step-implies-not-halted prog s s' step-eq halt-eq

-- | Auxiliary for exec-one-step: takes halted value explicitly
-- Using rewrite sym h-eq substitutes halted s with h in the goal
exec-one-step-aux : ∀ prog (s s' : State) (h : Bool) → h ≡ halted s → step prog s ≡ just s' → exec 1 prog s ≡ just s'
exec-one-step-aux prog s s' true  h-eq step-eq rewrite sym h-eq = step-eq
exec-one-step-aux prog s s' false h-eq step-eq
  rewrite sym h-eq | step-on-non-halted {prog} {s} (sym h-eq) | step-eq with halted s' | inspect halted s'
... | true  | _ = refl
... | false | _ = refl

-- | Single-step execution: execute exactly 1 step (works for both halted and non-halted results)
-- PROVEN: By case split on halted s.
--   - If halted s = true: step prog s = just s, and exec 1 prog s = just s
--   - If halted s = false: exec-step-helper chains the step to exec 0
exec-one-step : ∀ (prog : List Instr) (s s' : State) →
  step prog s ≡ just s' →
  exec 1 prog s ≡ just s'
exec-one-step prog s s' step-eq = exec-one-step-aux prog s s' (halted s) refl step-eq

-- | Two-step non-halting execution: execute exactly 2 steps without halting
exec-two-steps-nonhalt : ∀ (prog : List Instr) (s s1 s2 : State) →
  step prog s ≡ just s1 →
  halted s1 ≡ false →
  step prog s1 ≡ just s2 →
  halted s2 ≡ false →
  exec 2 prog s ≡ just s2
exec-two-steps-nonhalt prog s s1 s2 step1 h1 step2 h2 =
  trans (exec-on-non-halted-step 1 prog s s1 h0 step1 h1)
        (exec-one-step-nonhalt prog s1 s2 step2 h2)
  where h0 = step-implies-not-halted prog s s1 step1 h1

-- | Three-step non-halting execution
exec-three-steps-nonhalt : ∀ (prog : List Instr) (s s1 s2 s3 : State) →
  step prog s ≡ just s1 → halted s1 ≡ false →
  step prog s1 ≡ just s2 → halted s2 ≡ false →
  step prog s2 ≡ just s3 → halted s3 ≡ false →
  exec 3 prog s ≡ just s3
exec-three-steps-nonhalt prog s s1 s2 s3 step1 h1 step2 h2 step3 h3 =
  trans (exec-on-non-halted-step 2 prog s s1 h0 step1 h1)
        (exec-two-steps-nonhalt prog s1 s2 s3 step2 h2 step3 h3)
  where h0 = step-implies-not-halted prog s s1 step1 h1

exec-four-steps-nonhalt : ∀ (prog : List Instr) (s s1 s2 s3 s4 : State) →
  step prog s ≡ just s1 → halted s1 ≡ false →
  step prog s1 ≡ just s2 → halted s2 ≡ false →
  step prog s2 ≡ just s3 → halted s3 ≡ false →
  step prog s3 ≡ just s4 → halted s4 ≡ false →
  exec 4 prog s ≡ just s4
exec-four-steps-nonhalt prog s s1 s2 s3 s4 step1 h1 step2 h2 step3 h3 step4 h4 =
  trans (exec-on-non-halted-step 3 prog s s1 h0 step1 h1)
        (exec-three-steps-nonhalt prog s1 s2 s3 s4 step2 h2 step3 h3 step4 h4)
  where h0 = step-implies-not-halted prog s s1 step1 h1

exec-five-steps-nonhalt : ∀ (prog : List Instr) (s s1 s2 s3 s4 s5 : State) →
  step prog s ≡ just s1 → halted s1 ≡ false →
  step prog s1 ≡ just s2 → halted s2 ≡ false →
  step prog s2 ≡ just s3 → halted s3 ≡ false →
  step prog s3 ≡ just s4 → halted s4 ≡ false →
  step prog s4 ≡ just s5 → halted s5 ≡ false →
  exec 5 prog s ≡ just s5
exec-five-steps-nonhalt prog s s1 s2 s3 s4 s5 step1 h1 step2 h2 step3 h3 step4 h4 step5 h5 =
  trans (exec-on-non-halted-step 4 prog s s1 h0 step1 h1)
        (exec-four-steps-nonhalt prog s1 s2 s3 s4 s5 step2 h2 step3 h3 step4 h4 step5 h5)
  where h0 = step-implies-not-halted prog s s1 step1 h1

exec-six-steps-nonhalt : ∀ (prog : List Instr) (s s1 s2 s3 s4 s5 s6 : State) →
  step prog s ≡ just s1 → halted s1 ≡ false →
  step prog s1 ≡ just s2 → halted s2 ≡ false →
  step prog s2 ≡ just s3 → halted s3 ≡ false →
  step prog s3 ≡ just s4 → halted s4 ≡ false →
  step prog s4 ≡ just s5 → halted s5 ≡ false →
  step prog s5 ≡ just s6 → halted s6 ≡ false →
  exec 6 prog s ≡ just s6
exec-six-steps-nonhalt prog s s1 s2 s3 s4 s5 s6 step1 h1 step2 h2 step3 h3 step4 h4 step5 h5 step6 h6 =
  trans (exec-on-non-halted-step 5 prog s s1 h0 step1 h1)
        (exec-five-steps-nonhalt prog s1 s2 s3 s4 s5 s6 step2 h2 step3 h3 step4 h4 step5 h5 step6 h6)
  where h0 = step-implies-not-halted prog s s1 step1 h1

exec-seven-steps-nonhalt : ∀ (prog : List Instr) (s s1 s2 s3 s4 s5 s6 s7 : State) →
  step prog s ≡ just s1 → halted s1 ≡ false →
  step prog s1 ≡ just s2 → halted s2 ≡ false →
  step prog s2 ≡ just s3 → halted s3 ≡ false →
  step prog s3 ≡ just s4 → halted s4 ≡ false →
  step prog s4 ≡ just s5 → halted s5 ≡ false →
  step prog s5 ≡ just s6 → halted s6 ≡ false →
  step prog s6 ≡ just s7 → halted s7 ≡ false →
  exec 7 prog s ≡ just s7
exec-seven-steps-nonhalt prog s s1 s2 s3 s4 s5 s6 s7 step1 h1 step2 h2 step3 h3 step4 h4 step5 h5 step6 h6 step7 h7 =
  trans (exec-on-non-halted-step 6 prog s s1 h0 step1 h1)
        (exec-six-steps-nonhalt prog s1 s2 s3 s4 s5 s6 s7 step2 h2 step3 h3 step4 h4 step5 h5 step6 h6 step7 h7)
  where h0 = step-implies-not-halted prog s s1 step1 h1

-- | Fetching at the end of a prefix returns the first element of suffix
-- fetch (prefix ++ i ∷ rest) (length prefix) ≡ just i
fetch-at-prefix-end : ∀ (prefix : Program) (i : Instr) (rest : Program) →
  fetch (prefix ++ i ∷ rest) (length prefix) ≡ just i
fetch-at-prefix-end [] i rest = refl
fetch-at-prefix-end (x ∷ prefix) i rest = fetch-at-prefix-end prefix i rest

-- | Execute transfer instruction (mov rdi, rax) at position N in a program
-- Used between sub-programs in compose to transfer result to input
exec-transfer-at : ∀ (prefix : Program) (suffix : Program) (s : State) →
  halted s ≡ false →
  pc s ≡ length prefix →
  ∃[ s' ] (step (prefix ++ mov (reg rdi) (reg rax) ∷ suffix) s ≡ just s'
         × halted s' ≡ false
         × pc s' ≡ length prefix +ℕ 1
         × readReg (regs s') rdi ≡ readReg (regs s) rax
         × readReg (regs s') rax ≡ readReg (regs s) rax)
exec-transfer-at prefix suffix s h-false pc-eq = s' , step-eq , h' , pc' , rdi-eq , rax-eq
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
-- N-step execution with halting (replaces Common.Exec)
--
-- These lemmas use exec-step-helper (from Star.agda) to chain steps,
-- and exec-n-halted to handle the final halted state.
-- This avoids the signature mismatch issues with Common.Exec.
------------------------------------------------------------------------

-- | Helper: exec returns unchanged state when halted
-- (Copied from exec-on-halted-step's where clause)
exec-n-halted : ∀ m prog (s : State) → halted s ≡ true → exec m prog s ≡ just s
exec-n-halted zero _ s _ = refl
exec-n-halted (suc m) prog s h with halted s | h
... | true | refl = refl

-- | Execute 2 steps with final halt
exec-two-steps : ∀ (n : ℕ) (prog : List Instr) (s s₁ s₂ : State) →
  step prog s ≡ just s₁ → halted s₁ ≡ false →
  step prog s₁ ≡ just s₂ → halted s₂ ≡ true →
  exec (suc (suc n)) prog s ≡ just s₂
exec-two-steps n prog s s₁ s₂ step₁ h₁ step₂ h₂ =
  exec-step-helper h₀ step₁ (exec-step-helper h₁ step₂ (exec-n-halted n prog s₂ h₂))
  where
    h₀ = step-implies-not-halted prog s s₁ step₁ h₁

-- | Execute 3 steps with final halt
exec-three-steps : ∀ (n : ℕ) (prog : List Instr) (s s₁ s₂ s₃ : State) →
  step prog s ≡ just s₁ → halted s₁ ≡ false →
  step prog s₁ ≡ just s₂ → halted s₂ ≡ false →
  step prog s₂ ≡ just s₃ → halted s₃ ≡ true →
  exec (suc (suc (suc n))) prog s ≡ just s₃
exec-three-steps n prog s s₁ s₂ s₃ step₁ h₁ step₂ h₂ step₃ h₃ =
  exec-step-helper h₀ step₁ (exec-two-steps n prog s₁ s₂ s₃ step₂ h₂ step₃ h₃)
  where
    h₀ = step-implies-not-halted prog s s₁ step₁ h₁

-- | Execute 4 steps with final halt
exec-four-steps : ∀ (n : ℕ) (prog : List Instr) (s s₁ s₂ s₃ s₄ : State) →
  step prog s ≡ just s₁ → halted s₁ ≡ false →
  step prog s₁ ≡ just s₂ → halted s₂ ≡ false →
  step prog s₂ ≡ just s₃ → halted s₃ ≡ false →
  step prog s₃ ≡ just s₄ → halted s₄ ≡ true →
  exec (suc (suc (suc (suc n)))) prog s ≡ just s₄
exec-four-steps n prog s s₁ s₂ s₃ s₄ step₁ h₁ step₂ h₂ step₃ h₃ step₄ h₄ =
  exec-step-helper h₀ step₁ (exec-three-steps n prog s₁ s₂ s₃ s₄ step₂ h₂ step₃ h₃ step₄ h₄)
  where
    h₀ = step-implies-not-halted prog s s₁ step₁ h₁

-- | Execute 5 steps with final halt
exec-five-steps : ∀ (n : ℕ) (prog : List Instr) (s s₁ s₂ s₃ s₄ s₅ : State) →
  step prog s ≡ just s₁ → halted s₁ ≡ false →
  step prog s₁ ≡ just s₂ → halted s₂ ≡ false →
  step prog s₂ ≡ just s₃ → halted s₃ ≡ false →
  step prog s₃ ≡ just s₄ → halted s₄ ≡ false →
  step prog s₄ ≡ just s₅ → halted s₅ ≡ true →
  exec (suc (suc (suc (suc (suc n))))) prog s ≡ just s₅
exec-five-steps n prog s s₁ s₂ s₃ s₄ s₅ step₁ h₁ step₂ h₂ step₃ h₃ step₄ h₄ step₅ h₅ =
  exec-step-helper h₀ step₁ (exec-four-steps n prog s₁ s₂ s₃ s₄ s₅ step₂ h₂ step₃ h₃ step₄ h₄ step₅ h₅)
  where
    h₀ = step-implies-not-halted prog s s₁ step₁ h₁

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
    pair-pos : (n m : ℕ) → (15 +ℕ n) +ℕ m > 0
    pair-pos n m = s≤s z≤n
compile-length>0 inl = s≤s z≤n
compile-length>0 inr = s≤s z≤n
compile-length>0 [ f , g ] = case-pos (compile-length f) (compile-length g)
  where
    case-pos : (n m : ℕ) → (8 +ℕ n) +ℕ m > 0
    case-pos n m = s≤s z≤n
compile-length>0 terminal = s≤s z≤n
compile-length>0 initial = s≤s z≤n
compile-length>0 (curry f) = curry-pos (compile-length f)
  where
    curry-pos : (n : ℕ) → 19 +ℕ n > 0
    curry-pos n = s≤s z≤n
compile-length>0 apply = s≤s z≤n
compile-length>0 fold = s≤s z≤n
compile-length>0 unfold = s≤s z≤n
compile-length>0 arr = s≤s z≤n
compile-length>0 (Prim _) = s≤s z≤n
