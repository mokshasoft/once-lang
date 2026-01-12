------------------------------------------------------------------------
-- Once.Backend.X86.Correct.FetchStep
--
-- Fetch and step lemmas for x86-64 execution.
-- These are independent (Level 0) - no dependencies on other Correct/* modules.
------------------------------------------------------------------------

module Once.Backend.X86.Correct.FetchStep where

open import Once.Backend.X86.Syntax
open import Once.Backend.X86.Semantics
open Once.Backend.X86.Semantics.State

-- Import common fetch lemmas
open import Once.Backend.Common.Fetch
  using (fetch-0; fetch-1; fetch-2; fetch-3; fetch-append-left; fetch-append-right)

open import Data.Nat using (ℕ; zero; suc) renaming (_+_ to _+ℕ_)
open import Data.Nat.Properties using (+-identityʳ)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.Bool using (Bool; true; false)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans; subst)

------------------------------------------------------------------------
-- Fetch Lemmas
------------------------------------------------------------------------

-- | Fetching at index 4 returns the fifth instruction
fetch-4 : ∀ (i0 i1 i2 i3 i4 : Instr) (is : List Instr) → fetch (i0 ∷ i1 ∷ i2 ∷ i3 ∷ i4 ∷ is) 4 ≡ just i4
fetch-4 i0 i1 i2 i3 i4 is = refl

-- | Fetching at index 5 returns the sixth instruction
fetch-5 : ∀ (i0 i1 i2 i3 i4 i5 : Instr) (is : List Instr) → fetch (i0 ∷ i1 ∷ i2 ∷ i3 ∷ i4 ∷ i5 ∷ is) 5 ≡ just i5
fetch-5 i0 i1 i2 i3 i4 i5 is = refl

-- | Fetching at index 6 returns the seventh instruction
fetch-6 : ∀ (i0 i1 i2 i3 i4 i5 i6 : Instr) (is : List Instr) → fetch (i0 ∷ i1 ∷ i2 ∷ i3 ∷ i4 ∷ i5 ∷ i6 ∷ is) 6 ≡ just i6
fetch-6 i0 i1 i2 i3 i4 i5 i6 is = refl

-- | Fetching at index 7 returns the eighth instruction
fetch-7 : ∀ (i0 i1 i2 i3 i4 i5 i6 i7 : Instr) (is : List Instr) → fetch (i0 ∷ i1 ∷ i2 ∷ i3 ∷ i4 ∷ i5 ∷ i6 ∷ i7 ∷ is) 7 ≡ just i7
fetch-7 i0 i1 i2 i3 i4 i5 i6 i7 is = refl

-- | Fetching at index 8 returns the ninth instruction
fetch-8 : ∀ (i0 i1 i2 i3 i4 i5 i6 i7 i8 : Instr) (is : List Instr) → fetch (i0 ∷ i1 ∷ i2 ∷ i3 ∷ i4 ∷ i5 ∷ i6 ∷ i7 ∷ i8 ∷ is) 8 ≡ just i8
fetch-8 i0 i1 i2 i3 i4 i5 i6 i7 i8 is = refl

-- | Fetching at index 9 returns the tenth instruction
fetch-9 : ∀ (i0 i1 i2 i3 i4 i5 i6 i7 i8 i9 : Instr) (is : List Instr) → fetch (i0 ∷ i1 ∷ i2 ∷ i3 ∷ i4 ∷ i5 ∷ i6 ∷ i7 ∷ i8 ∷ i9 ∷ is) 9 ≡ just i9
fetch-9 i0 i1 i2 i3 i4 i5 i6 i7 i8 i9 is = refl

------------------------------------------------------------------------
-- Fetch Lemmas for List Concatenation
------------------------------------------------------------------------

-- | Fetching past a prefix goes into the suffix
fetch-append-skip : ∀ (xs ys : List Instr) (n : ℕ) →
  fetch (xs ++ ys) (length xs +ℕ n) ≡ fetch ys n
fetch-append-skip [] ys n = refl
fetch-append-skip (x ∷ xs) ys n = fetch-append-skip xs ys n

-- | Fetching past the end of a list returns nothing
fetch-past-length : ∀ (xs : List Instr) (n : ℕ) →
  fetch xs (length xs +ℕ n) ≡ nothing
fetch-past-length [] n = refl
fetch-past-length (x ∷ xs) n = fetch-past-length xs n

-- | Length of concatenated lists
length-++ : ∀ (xs ys : List Instr) → length (xs ++ ys) ≡ length xs +ℕ length ys
length-++ [] ys = refl
length-++ (x ∷ xs) ys = cong suc (length-++ xs ys)

------------------------------------------------------------------------
-- Step Lemmas
------------------------------------------------------------------------

-- | Step on non-halted state executes the instruction at pc
step-exec : ∀ (prog : List Instr) (s : State) (i : Instr) →
  halted s ≡ false →
  fetch prog (pc s) ≡ just i →
  step prog s ≡ execInstr prog s i
step-exec prog s i h-false fetch-ok with halted s | h-false
... | false | refl with fetch prog (pc s) | fetch-ok
...   | just .i | refl = refl


-- | Step on non-halted state where fetch fails sets halted=true
step-halt-on-fetch-fail : ∀ (prog : List Instr) (s : State) →
  halted s ≡ false →
  fetch prog (pc s) ≡ nothing →
  step prog s ≡ just (record s { halted = true })
step-halt-on-fetch-fail prog s h-false fetch-fail with halted s | h-false
... | false | refl with fetch prog (pc s) | fetch-fail
...   | nothing | refl = refl

-- | Step on already halted state returns the same state
step-on-halted : ∀ (prog : List Instr) (s : State) →
  halted s ≡ true →
  step prog s ≡ just s
step-on-halted prog s h-true with halted s
step-on-halted prog s refl | true = refl

