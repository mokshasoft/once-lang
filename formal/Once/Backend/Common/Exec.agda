------------------------------------------------------------------------
-- Once.Backend.Common.Exec
--
-- Parameterized module for N-step execution lemmas.
-- Backends instantiate this with their specific types and base lemmas,
-- getting exec-two-steps through exec-nine-steps for free.
--
-- Usage in backend:
--   open import Once.Backend.Common.Exec
--     State Instr halted step exec
--     exec-step-continue exec-halt-step
------------------------------------------------------------------------

open import Data.Bool using (Bool; true; false)
open import Data.List using (List)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans)

module Once.Backend.Common.Exec
  {State : Set}
  {Instr : Set}
  (halted : State → Bool)
  (step : List Instr → State → Maybe State)
  (exec : ℕ → List Instr → State → Maybe State)
  -- Base lemma: stepping when result is not halted
  (exec-step-continue : ∀ (n : ℕ) (prog : List Instr) (s s' : State) →
    step prog s ≡ just s' → halted s' ≡ false →
    exec (suc n) prog s ≡ exec n prog s')
  -- Base lemma: stepping when result is halted
  (exec-halt-step : ∀ (n : ℕ) (prog : List Instr) (s s' : State) →
    step prog s ≡ just s' → halted s' ≡ true →
    exec (suc n) prog s ≡ just s')
  where

------------------------------------------------------------------------
-- N-step execution lemmas
-- Each builds on the previous using the base lemmas
------------------------------------------------------------------------

-- | Execute 2 steps and halt
exec-two-steps : ∀ (n : ℕ) (prog : List Instr) (s s₁ s₂ : State) →
  step prog s ≡ just s₁ → halted s₁ ≡ false →
  step prog s₁ ≡ just s₂ → halted s₂ ≡ true →
  exec (suc (suc n)) prog s ≡ just s₂
exec-two-steps n prog s s₁ s₂ step₁ h₁ step₂ h₂ =
  trans (exec-step-continue (suc n) prog s s₁ step₁ h₁)
        (exec-halt-step n prog s₁ s₂ step₂ h₂)

-- | Execute 3 steps and halt
exec-three-steps : ∀ (n : ℕ) (prog : List Instr) (s s₁ s₂ s₃ : State) →
  step prog s ≡ just s₁ → halted s₁ ≡ false →
  step prog s₁ ≡ just s₂ → halted s₂ ≡ false →
  step prog s₂ ≡ just s₃ → halted s₃ ≡ true →
  exec (suc (suc (suc n))) prog s ≡ just s₃
exec-three-steps n prog s s₁ s₂ s₃ step₁ h₁ step₂ h₂ step₃ h₃ =
  trans (exec-step-continue (suc (suc n)) prog s s₁ step₁ h₁)
        (exec-two-steps n prog s₁ s₂ s₃ step₂ h₂ step₃ h₃)

-- | Execute 4 steps and halt
exec-four-steps : ∀ (n : ℕ) (prog : List Instr) (s s₁ s₂ s₃ s₄ : State) →
  step prog s ≡ just s₁ → halted s₁ ≡ false →
  step prog s₁ ≡ just s₂ → halted s₂ ≡ false →
  step prog s₂ ≡ just s₃ → halted s₃ ≡ false →
  step prog s₃ ≡ just s₄ → halted s₄ ≡ true →
  exec (suc (suc (suc (suc n)))) prog s ≡ just s₄
exec-four-steps n prog s s₁ s₂ s₃ s₄ step₁ h₁ step₂ h₂ step₃ h₃ step₄ h₄ =
  trans (exec-step-continue (suc (suc (suc n))) prog s s₁ step₁ h₁)
        (exec-three-steps n prog s₁ s₂ s₃ s₄ step₂ h₂ step₃ h₃ step₄ h₄)

-- | Execute 5 steps and halt
exec-five-steps : ∀ (n : ℕ) (prog : List Instr) (s s₁ s₂ s₃ s₄ s₅ : State) →
  step prog s ≡ just s₁ → halted s₁ ≡ false →
  step prog s₁ ≡ just s₂ → halted s₂ ≡ false →
  step prog s₂ ≡ just s₃ → halted s₃ ≡ false →
  step prog s₃ ≡ just s₄ → halted s₄ ≡ false →
  step prog s₄ ≡ just s₅ → halted s₅ ≡ true →
  exec (suc (suc (suc (suc (suc n))))) prog s ≡ just s₅
exec-five-steps n prog s s₁ s₂ s₃ s₄ s₅ step₁ h₁ step₂ h₂ step₃ h₃ step₄ h₄ step₅ h₅ =
  trans (exec-step-continue (suc (suc (suc (suc n)))) prog s s₁ step₁ h₁)
        (exec-four-steps n prog s₁ s₂ s₃ s₄ s₅ step₂ h₂ step₃ h₃ step₄ h₄ step₅ h₅)

-- | Execute 6 steps and halt
exec-six-steps : ∀ (n : ℕ) (prog : List Instr) (s s₁ s₂ s₃ s₄ s₅ s₆ : State) →
  step prog s ≡ just s₁ → halted s₁ ≡ false →
  step prog s₁ ≡ just s₂ → halted s₂ ≡ false →
  step prog s₂ ≡ just s₃ → halted s₃ ≡ false →
  step prog s₃ ≡ just s₄ → halted s₄ ≡ false →
  step prog s₄ ≡ just s₅ → halted s₅ ≡ false →
  step prog s₅ ≡ just s₆ → halted s₆ ≡ true →
  exec (suc (suc (suc (suc (suc (suc n)))))) prog s ≡ just s₆
exec-six-steps n prog s s₁ s₂ s₃ s₄ s₅ s₆ step₁ h₁ step₂ h₂ step₃ h₃ step₄ h₄ step₅ h₅ step₆ h₆ =
  trans (exec-step-continue (suc (suc (suc (suc (suc n))))) prog s s₁ step₁ h₁)
        (exec-five-steps n prog s₁ s₂ s₃ s₄ s₅ s₆ step₂ h₂ step₃ h₃ step₄ h₄ step₅ h₅ step₆ h₆)

-- | Execute 7 steps and halt
exec-seven-steps : ∀ (n : ℕ) (prog : List Instr) (s s₁ s₂ s₃ s₄ s₅ s₆ s₇ : State) →
  step prog s ≡ just s₁ → halted s₁ ≡ false →
  step prog s₁ ≡ just s₂ → halted s₂ ≡ false →
  step prog s₂ ≡ just s₃ → halted s₃ ≡ false →
  step prog s₃ ≡ just s₄ → halted s₄ ≡ false →
  step prog s₄ ≡ just s₅ → halted s₅ ≡ false →
  step prog s₅ ≡ just s₆ → halted s₆ ≡ false →
  step prog s₆ ≡ just s₇ → halted s₇ ≡ true →
  exec (suc (suc (suc (suc (suc (suc (suc n))))))) prog s ≡ just s₇
exec-seven-steps n prog s s₁ s₂ s₃ s₄ s₅ s₆ s₇ step₁ h₁ step₂ h₂ step₃ h₃ step₄ h₄ step₅ h₅ step₆ h₆ step₇ h₇ =
  trans (exec-step-continue (suc (suc (suc (suc (suc (suc n)))))) prog s s₁ step₁ h₁)
        (exec-six-steps n prog s₁ s₂ s₃ s₄ s₅ s₆ s₇ step₂ h₂ step₃ h₃ step₄ h₄ step₅ h₅ step₆ h₆ step₇ h₇)

-- | Execute 8 steps and halt
exec-eight-steps : ∀ (n : ℕ) (prog : List Instr) (s s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ : State) →
  step prog s ≡ just s₁ → halted s₁ ≡ false →
  step prog s₁ ≡ just s₂ → halted s₂ ≡ false →
  step prog s₂ ≡ just s₃ → halted s₃ ≡ false →
  step prog s₃ ≡ just s₄ → halted s₄ ≡ false →
  step prog s₄ ≡ just s₅ → halted s₅ ≡ false →
  step prog s₅ ≡ just s₆ → halted s₆ ≡ false →
  step prog s₆ ≡ just s₇ → halted s₇ ≡ false →
  step prog s₇ ≡ just s₈ → halted s₈ ≡ true →
  exec (suc (suc (suc (suc (suc (suc (suc (suc n)))))))) prog s ≡ just s₈
exec-eight-steps n prog s s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ step₁ h₁ step₂ h₂ step₃ h₃ step₄ h₄ step₅ h₅ step₆ h₆ step₇ h₇ step₈ h₈ =
  trans (exec-step-continue (suc (suc (suc (suc (suc (suc (suc n))))))) prog s s₁ step₁ h₁)
        (exec-seven-steps n prog s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ step₂ h₂ step₃ h₃ step₄ h₄ step₅ h₅ step₆ h₆ step₇ h₇ step₈ h₈)

-- | Execute 9 steps and halt
exec-nine-steps : ∀ (n : ℕ) (prog : List Instr) (s s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ : State) →
  step prog s ≡ just s₁ → halted s₁ ≡ false →
  step prog s₁ ≡ just s₂ → halted s₂ ≡ false →
  step prog s₂ ≡ just s₃ → halted s₃ ≡ false →
  step prog s₃ ≡ just s₄ → halted s₄ ≡ false →
  step prog s₄ ≡ just s₅ → halted s₅ ≡ false →
  step prog s₅ ≡ just s₆ → halted s₆ ≡ false →
  step prog s₆ ≡ just s₇ → halted s₇ ≡ false →
  step prog s₇ ≡ just s₈ → halted s₈ ≡ false →
  step prog s₈ ≡ just s₉ → halted s₉ ≡ true →
  exec (suc (suc (suc (suc (suc (suc (suc (suc (suc n))))))))) prog s ≡ just s₉
exec-nine-steps n prog s s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ step₁ h₁ step₂ h₂ step₃ h₃ step₄ h₄ step₅ h₅ step₆ h₆ step₇ h₇ step₈ h₈ step₉ h₉ =
  trans (exec-step-continue (suc (suc (suc (suc (suc (suc (suc (suc n)))))))) prog s s₁ step₁ h₁)
        (exec-eight-steps n prog s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ step₂ h₂ step₃ h₃ step₄ h₄ step₅ h₅ step₆ h₆ step₇ h₇ step₈ h₈ step₉ h₉)
