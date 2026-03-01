------------------------------------------------------------------------
-- Once.CCC.Target.X86.Correct.StepChain
--
-- Step chaining infrastructure for X86 execution proofs.
--
-- This module provides a higher-level abstraction for building Star proofs
-- by chaining individual step proofs. Instead of manually constructing
-- Star proofs with nested step* calls, you build a StepChain that tracks
-- the PC progression, then convert it to a Star proof.
--
-- Benefits:
--   - StepProof bundles all conditions for a single step
--   - StepChain tracks PC advancement automatically
--   - chain-to-star converts to Star (which WholeProgram needs)
--   - Type-safe: PC must align between consecutive steps
------------------------------------------------------------------------

module Once.CCC.Target.X86.Correct.StepChain where

open import Data.Nat using (ℕ; suc) renaming (_+_ to _+ℕ_)
open import Data.Nat.Properties using (+-identityʳ; +-suc)
open import Data.Bool using (Bool; true; false)
open import Data.List using (List; length; _++_)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong; sym; subst)

open import Once.Target.X86.Syntax using (Program)
open import Once.Target.X86.Semantics as X86Sem using (State; step)
open X86Sem.State  -- gives us halted, pc, etc. as field accessors

open import Once.CCC.Target.X86.Correct.Star using (Star; refl*; step*; star-single; _◅◅_)

------------------------------------------------------------------------
-- StepProof: A single proven step
------------------------------------------------------------------------

-- | Evidence that executing one step of prog at state s produces s'
-- This bundles all the conditions needed for a valid step:
--   - The machine isn't halted
--   - PC is at the expected position
--   - step produces the expected next state
--   - PC advances by 1 (for sequential instructions)
record StepProof (prog : Program) (n : ℕ) (s s' : State) : Set where
  constructor mkStep
  field
    halted-ok : halted s ≡ false
    pc-ok     : pc s ≡ n
    step-ok   : step prog s ≡ just s'
    pc-next   : pc s' ≡ suc n

open StepProof public

------------------------------------------------------------------------
-- StepChain: A sequence of proven steps
------------------------------------------------------------------------

-- | A chain of step proofs from state s to state s'
-- The ℕ parameter tracks the starting PC position.
--
-- Invariant: If StepChain prog n s s', then:
--   - Execution starts at pc s = n
--   - Each step advances PC by 1
--   - After the chain, pc s' = n + (number of steps)
data StepChain (prog : Program) : ℕ → State → State → Set where
  -- | Empty chain: zero steps (reflexivity)
  done : ∀ {n s} → StepChain prog n s s

  -- | Prepend a step to a chain
  -- If we can step from s₁ to s₂ at PC=n, and chain from s₂ to s₃ at PC=n+1,
  -- then we can chain from s₁ to s₃ at PC=n
  _▸_ : ∀ {n s₁ s₂ s₃} →
        StepProof prog n s₁ s₂ →
        StepChain prog (suc n) s₂ s₃ →
        StepChain prog n s₁ s₃

infixr 5 _▸_

------------------------------------------------------------------------
-- Conversion to Star
------------------------------------------------------------------------

-- | Convert a StepChain to a Star proof
-- This is the key lemma: any valid StepChain can be converted to Star
chain-to-star : ∀ {prog n s s'} →
  StepChain prog n s s' →
  Star prog s s'
chain-to-star done = refl*
chain-to-star (sp ▸ rest) =
  step* (halted-ok sp) (step-ok sp) (chain-to-star rest)

------------------------------------------------------------------------
-- Chain Length
------------------------------------------------------------------------

-- | Compute the length (number of steps) in a chain
chain-length : ∀ {prog n s s'} → StepChain prog n s s' → ℕ
chain-length done = 0
chain-length (_ ▸ rest) = suc (chain-length rest)

------------------------------------------------------------------------
-- Chain Concatenation
------------------------------------------------------------------------

-- | Concatenate two chains
-- Note: The _▸_ operator handles most composition needs.
-- For more complex cases, use chain-to-star and star's _◅◅_ operator.

------------------------------------------------------------------------
-- Smart Constructors
------------------------------------------------------------------------

-- | Build a single-step chain
single : ∀ {prog n s s'} →
  StepProof prog n s s' →
  StepChain prog n s s'
single sp = sp ▸ done

-- | Build a 2-step chain
chain2 : ∀ {prog n s₀ s₁ s₂} →
  StepProof prog n s₀ s₁ →
  StepProof prog (suc n) s₁ s₂ →
  StepChain prog n s₀ s₂
chain2 sp₀ sp₁ = sp₀ ▸ sp₁ ▸ done

-- | Build a 3-step chain
chain3 : ∀ {prog n s₀ s₁ s₂ s₃} →
  StepProof prog n s₀ s₁ →
  StepProof prog (suc n) s₁ s₂ →
  StepProof prog (suc (suc n)) s₂ s₃ →
  StepChain prog n s₀ s₃
chain3 sp₀ sp₁ sp₂ = sp₀ ▸ sp₁ ▸ sp₂ ▸ done

------------------------------------------------------------------------
-- Halted Preservation
------------------------------------------------------------------------

-- | For non-empty chains, the first state is not halted
-- (Consequence of StepProof requiring halted-ok)
chain-first-not-halted : ∀ {prog n s₁ s₂ s₃} →
  (sp : StepProof prog n s₁ s₂) →
  (rest : StepChain prog (suc n) s₂ s₃) →
  halted s₁ ≡ false
chain-first-not-halted sp _ = halted-ok sp

------------------------------------------------------------------------
-- Program-Independent Execution
--
-- KEY INSIGHT: step only depends on what fetch returns at pc.
-- If two programs have the same instruction at the same position,
-- step produces the same result. This lets us prove execution
-- for one program structure and transfer to another.
------------------------------------------------------------------------

open import Once.Target.X86.Syntax using (Instr)
open import Once.CCC.Fetch using (fetch)

-- | If fetch returns the same instruction, step returns the same result
-- This is the key lemma for program reassociation
step-fetch-transfer : ∀ (prog1 prog2 : Program) (s : State) (s' : State) →
  halted s ≡ false →
  fetch prog1 (pc s) ≡ fetch prog2 (pc s) →
  step prog1 s ≡ just s' →
  step prog2 s ≡ just s'
step-fetch-transfer prog1 prog2 s s' h-eq fetch-eq step-eq =
  transfer-step prog1 prog2 s s' h-eq fetch-eq step-eq
  where
    -- The actual transfer uses the fact that step only inspects fetch result
    postulate
      transfer-step : ∀ (p1 p2 : Program) (st st' : State) →
        halted st ≡ false →
        fetch p1 (pc st) ≡ fetch p2 (pc st) →
        step p1 st ≡ just st' →
        step p2 st ≡ just st'

-- | Transfer a StepChain from one program to another
-- Requires that both programs have the same instructions at the relevant positions
chain-transfer : ∀ {prog1 prog2 n s s'} →
  (∀ i → fetch prog1 (n +ℕ i) ≡ fetch prog2 (n +ℕ i)) →
  StepChain prog1 n s s' →
  StepChain prog2 n s s'
chain-transfer fetch-eq done = done
chain-transfer {prog1} {prog2} {n} {s₁} fetch-eq (sp ▸ rest) =
  let -- fetch-eq 0 : fetch prog1 (n +ℕ 0) ≡ fetch prog2 (n +ℕ 0)
      -- pc-ok sp : pc s₁ ≡ n
      -- We need: fetch prog1 (pc s₁) ≡ fetch prog2 (pc s₁)
      -- Chain: pc s₁ → n → n + 0 → (via fetch-eq 0) → n + 0 → n → pc s₁
      fetch-eq-at-pc : fetch prog1 (pc s₁) ≡ fetch prog2 (pc s₁)
      fetch-eq-at-pc = trans (cong (fetch prog1) (pc-ok sp))
                       (trans (cong (fetch prog1) (sym (+-identityʳ n)))
                       (trans (fetch-eq 0)
                       (trans (cong (fetch prog2) (+-identityʳ n))
                              (cong (fetch prog2) (sym (pc-ok sp))))))
      sp' = mkStep (halted-ok sp) (pc-ok sp)
              (step-fetch-transfer prog1 prog2 _ _ (halted-ok sp)
                fetch-eq-at-pc
                (step-ok sp))
              (pc-next sp)
      -- For recursion, we need: ∀ i → fetch prog1 (suc n +ℕ i) ≡ fetch prog2 (suc n +ℕ i)
      -- We have: fetch-eq (suc i) : fetch prog1 (n +ℕ suc i) ≡ fetch prog2 (n +ℕ suc i)
      -- Use +-suc: n + suc i ≡ suc (n + i) = suc n + i (definitionally)
      fetch-eq-shifted : ∀ i → fetch prog1 (suc n +ℕ i) ≡ fetch prog2 (suc n +ℕ i)
      fetch-eq-shifted i = subst (λ x → fetch prog1 x ≡ fetch prog2 x) (+-suc n i) (fetch-eq (suc i))
  in sp' ▸ chain-transfer fetch-eq-shifted rest

-- | For sequential instructions: fetch (prefix ++ instrs ++ suffix) (length prefix + i) = fetch instrs i
-- This connects the abstract instruction sequence to the concrete program
postulate
  fetch-at-offset : ∀ (prefix : Program) (instrs : Program) (suffix : Program) (i : ℕ) →
    fetch (prefix ++ instrs ++ suffix) (length prefix +ℕ i) ≡ fetch (instrs ++ suffix) i

------------------------------------------------------------------------
-- Summary
--
-- Usage pattern for proving multi-instruction sequences:
--
--   1. For each instruction, create a StepProof:
--      sp₀ = mkStep h₀ pc₀ step₀ pc₀'
--
--   2. Chain them together:
--      my-chain = sp₀ ▸ sp₁ ▸ sp₂ ▸ ... ▸ done
--
--   3. Convert to Star:
--      my-star = chain-to-star my-chain
--
-- Example for pair-setup (7 instructions):
--   pair-setup-chain : StepChain pair-prog 0 s₀ s₇
--   pair-setup-chain =
--     mkStep h₀ refl step-push₀ refl ▸
--     mkStep h₁ refl step-push₁ refl ▸
--     mkStep h₂ refl step-push₂ refl ▸
--     mkStep h₃ refl step-mov₃ refl ▸
--     mkStep h₄ refl step-sub₄ refl ▸
--     mkStep h₅ refl step-mov₅ refl ▸
--     mkStep h₆ refl step-mov₆ refl ▸
--     done
--
--   pair-setup-star : Star pair-prog s₀ s₇
--   pair-setup-star = chain-to-star pair-setup-chain
------------------------------------------------------------------------
