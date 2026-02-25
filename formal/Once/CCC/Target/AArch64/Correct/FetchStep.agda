------------------------------------------------------------------------
-- Once.CCC.Target.AArch64.Correct.FetchStep
--
-- Fetch and step lemmas for AArch64 execution.
-- These are independent (Level 0) - no dependencies on other Correct/* modules.
------------------------------------------------------------------------

module Once.CCC.Target.AArch64.Correct.FetchStep where

open import Once.Target.AArch64.Syntax
open import Once.Target.AArch64.Semantics
open Once.Target.AArch64.Semantics.State

-- Import common fetch lemmas
open import Once.CCC.Fetch
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

-- | Fetching at index 10 returns the eleventh instruction
fetch-10 : ∀ (i0 i1 i2 i3 i4 i5 i6 i7 i8 i9 i10 : Instr) (is : List Instr) → fetch (i0 ∷ i1 ∷ i2 ∷ i3 ∷ i4 ∷ i5 ∷ i6 ∷ i7 ∷ i8 ∷ i9 ∷ i10 ∷ is) 10 ≡ just i10
fetch-10 i0 i1 i2 i3 i4 i5 i6 i7 i8 i9 i10 is = refl

-- | Fetching at index 11 returns the twelfth instruction
fetch-11 : ∀ (i0 i1 i2 i3 i4 i5 i6 i7 i8 i9 i10 i11 : Instr) (is : List Instr) → fetch (i0 ∷ i1 ∷ i2 ∷ i3 ∷ i4 ∷ i5 ∷ i6 ∷ i7 ∷ i8 ∷ i9 ∷ i10 ∷ i11 ∷ is) 11 ≡ just i11
fetch-11 i0 i1 i2 i3 i4 i5 i6 i7 i8 i9 i10 i11 is = refl

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

-- | Step on non-halted state with pc=0 executes the first instruction
step-exec-0 : ∀ (i : Instr) (is : List Instr) (s : State) →
  halted s ≡ false →
  pc s ≡ 0 →
  step (i ∷ is) s ≡ execInstr (i ∷ is) s i
step-exec-0 i is s h-false pc-0 =
  step-exec (i ∷ is) s i h-false (subst (λ p → fetch (i ∷ is) p ≡ just i) (sym pc-0) refl)

-- | Step on non-halted state with pc=1 executes the second instruction
step-exec-1 : ∀ (i0 i1 : Instr) (is : List Instr) (s : State) →
  halted s ≡ false →
  pc s ≡ 1 →
  step (i0 ∷ i1 ∷ is) s ≡ execInstr (i0 ∷ i1 ∷ is) s i1
step-exec-1 i0 i1 is s h-false pc-1 =
  step-exec (i0 ∷ i1 ∷ is) s i1 h-false (subst (λ p → fetch (i0 ∷ i1 ∷ is) p ≡ just i1) (sym pc-1) refl)

-- | Step on non-halted state with pc=2 executes the third instruction
step-exec-2 : ∀ (i0 i1 i2 : Instr) (is : List Instr) (s : State) →
  halted s ≡ false →
  pc s ≡ 2 →
  step (i0 ∷ i1 ∷ i2 ∷ is) s ≡ execInstr (i0 ∷ i1 ∷ i2 ∷ is) s i2
step-exec-2 i0 i1 i2 is s h-false pc-2 =
  step-exec (i0 ∷ i1 ∷ i2 ∷ is) s i2 h-false (subst (λ p → fetch (i0 ∷ i1 ∷ i2 ∷ is) p ≡ just i2) (sym pc-2) refl)

-- | Step on non-halted state with pc=3 executes the fourth instruction
step-exec-3 : ∀ (i0 i1 i2 i3 : Instr) (is : List Instr) (s : State) →
  halted s ≡ false →
  pc s ≡ 3 →
  step (i0 ∷ i1 ∷ i2 ∷ i3 ∷ is) s ≡ execInstr (i0 ∷ i1 ∷ i2 ∷ i3 ∷ is) s i3
step-exec-3 i0 i1 i2 i3 is s h-false pc-3 =
  step-exec (i0 ∷ i1 ∷ i2 ∷ i3 ∷ is) s i3 h-false (subst (λ p → fetch (i0 ∷ i1 ∷ i2 ∷ i3 ∷ is) p ≡ just i3) (sym pc-3) refl)

-- | Step on non-halted state with pc=4 executes the fifth instruction
step-exec-4 : ∀ (i0 i1 i2 i3 i4 : Instr) (is : List Instr) (s : State) →
  halted s ≡ false →
  pc s ≡ 4 →
  step (i0 ∷ i1 ∷ i2 ∷ i3 ∷ i4 ∷ is) s ≡ execInstr (i0 ∷ i1 ∷ i2 ∷ i3 ∷ i4 ∷ is) s i4
step-exec-4 i0 i1 i2 i3 i4 is s h-false pc-4 =
  step-exec (i0 ∷ i1 ∷ i2 ∷ i3 ∷ i4 ∷ is) s i4 h-false (subst (λ p → fetch (i0 ∷ i1 ∷ i2 ∷ i3 ∷ i4 ∷ is) p ≡ just i4) (sym pc-4) refl)

-- | Step on non-halted state with pc=5 executes the sixth instruction
step-exec-5 : ∀ (i0 i1 i2 i3 i4 i5 : Instr) (is : List Instr) (s : State) →
  halted s ≡ false →
  pc s ≡ 5 →
  step (i0 ∷ i1 ∷ i2 ∷ i3 ∷ i4 ∷ i5 ∷ is) s ≡ execInstr (i0 ∷ i1 ∷ i2 ∷ i3 ∷ i4 ∷ i5 ∷ is) s i5
step-exec-5 i0 i1 i2 i3 i4 i5 is s h-false pc-5 =
  step-exec (i0 ∷ i1 ∷ i2 ∷ i3 ∷ i4 ∷ i5 ∷ is) s i5 h-false (subst (λ p → fetch (i0 ∷ i1 ∷ i2 ∷ i3 ∷ i4 ∷ i5 ∷ is) p ≡ just i5) (sym pc-5) refl)

-- | Step on non-halted state with pc=6 executes the seventh instruction
step-exec-6 : ∀ (i0 i1 i2 i3 i4 i5 i6 : Instr) (is : List Instr) (s : State) →
  halted s ≡ false →
  pc s ≡ 6 →
  step (i0 ∷ i1 ∷ i2 ∷ i3 ∷ i4 ∷ i5 ∷ i6 ∷ is) s ≡ execInstr (i0 ∷ i1 ∷ i2 ∷ i3 ∷ i4 ∷ i5 ∷ i6 ∷ is) s i6
step-exec-6 i0 i1 i2 i3 i4 i5 i6 is s h-false pc-6 =
  step-exec (i0 ∷ i1 ∷ i2 ∷ i3 ∷ i4 ∷ i5 ∷ i6 ∷ is) s i6 h-false (subst (λ p → fetch (i0 ∷ i1 ∷ i2 ∷ i3 ∷ i4 ∷ i5 ∷ i6 ∷ is) p ≡ just i6) (sym pc-6) refl)

-- | Step on non-halted state with pc=7 executes the eighth instruction
step-exec-7 : ∀ (i0 i1 i2 i3 i4 i5 i6 i7 : Instr) (is : List Instr) (s : State) →
  halted s ≡ false →
  pc s ≡ 7 →
  step (i0 ∷ i1 ∷ i2 ∷ i3 ∷ i4 ∷ i5 ∷ i6 ∷ i7 ∷ is) s ≡ execInstr (i0 ∷ i1 ∷ i2 ∷ i3 ∷ i4 ∷ i5 ∷ i6 ∷ i7 ∷ is) s i7
step-exec-7 i0 i1 i2 i3 i4 i5 i6 i7 is s h-false pc-7 =
  step-exec (i0 ∷ i1 ∷ i2 ∷ i3 ∷ i4 ∷ i5 ∷ i6 ∷ i7 ∷ is) s i7 h-false (subst (λ p → fetch (i0 ∷ i1 ∷ i2 ∷ i3 ∷ i4 ∷ i5 ∷ i6 ∷ i7 ∷ is) p ≡ just i7) (sym pc-7) refl)

step-exec-8 : ∀ (i0 i1 i2 i3 i4 i5 i6 i7 i8 : Instr) (is : List Instr) (s : State) →
  halted s ≡ false →
  pc s ≡ 8 →
  step (i0 ∷ i1 ∷ i2 ∷ i3 ∷ i4 ∷ i5 ∷ i6 ∷ i7 ∷ i8 ∷ is) s ≡ execInstr (i0 ∷ i1 ∷ i2 ∷ i3 ∷ i4 ∷ i5 ∷ i6 ∷ i7 ∷ i8 ∷ is) s i8
step-exec-8 i0 i1 i2 i3 i4 i5 i6 i7 i8 is s h-false pc-8 =
  step-exec (i0 ∷ i1 ∷ i2 ∷ i3 ∷ i4 ∷ i5 ∷ i6 ∷ i7 ∷ i8 ∷ is) s i8 h-false (subst (λ p → fetch (i0 ∷ i1 ∷ i2 ∷ i3 ∷ i4 ∷ i5 ∷ i6 ∷ i7 ∷ i8 ∷ is) p ≡ just i8) (sym pc-8) refl)

step-exec-9 : ∀ (i0 i1 i2 i3 i4 i5 i6 i7 i8 i9 : Instr) (is : List Instr) (s : State) →
  halted s ≡ false →
  pc s ≡ 9 →
  step (i0 ∷ i1 ∷ i2 ∷ i3 ∷ i4 ∷ i5 ∷ i6 ∷ i7 ∷ i8 ∷ i9 ∷ is) s ≡ execInstr (i0 ∷ i1 ∷ i2 ∷ i3 ∷ i4 ∷ i5 ∷ i6 ∷ i7 ∷ i8 ∷ i9 ∷ is) s i9
step-exec-9 i0 i1 i2 i3 i4 i5 i6 i7 i8 i9 is s h-false pc-9 =
  step-exec (i0 ∷ i1 ∷ i2 ∷ i3 ∷ i4 ∷ i5 ∷ i6 ∷ i7 ∷ i8 ∷ i9 ∷ is) s i9 h-false (subst (λ p → fetch (i0 ∷ i1 ∷ i2 ∷ i3 ∷ i4 ∷ i5 ∷ i6 ∷ i7 ∷ i8 ∷ i9 ∷ is) p ≡ just i9) (sym pc-9) refl)

step-exec-10 : ∀ (i0 i1 i2 i3 i4 i5 i6 i7 i8 i9 i10 : Instr) (is : List Instr) (s : State) →
  halted s ≡ false →
  pc s ≡ 10 →
  step (i0 ∷ i1 ∷ i2 ∷ i3 ∷ i4 ∷ i5 ∷ i6 ∷ i7 ∷ i8 ∷ i9 ∷ i10 ∷ is) s ≡ execInstr (i0 ∷ i1 ∷ i2 ∷ i3 ∷ i4 ∷ i5 ∷ i6 ∷ i7 ∷ i8 ∷ i9 ∷ i10 ∷ is) s i10
step-exec-10 i0 i1 i2 i3 i4 i5 i6 i7 i8 i9 i10 is s h-false pc-10 =
  step-exec (i0 ∷ i1 ∷ i2 ∷ i3 ∷ i4 ∷ i5 ∷ i6 ∷ i7 ∷ i8 ∷ i9 ∷ i10 ∷ is) s i10 h-false (subst (λ p → fetch (i0 ∷ i1 ∷ i2 ∷ i3 ∷ i4 ∷ i5 ∷ i6 ∷ i7 ∷ i8 ∷ i9 ∷ i10 ∷ is) p ≡ just i10) (sym pc-10) refl)

step-exec-11 : ∀ (i0 i1 i2 i3 i4 i5 i6 i7 i8 i9 i10 i11 : Instr) (is : List Instr) (s : State) →
  halted s ≡ false →
  pc s ≡ 11 →
  step (i0 ∷ i1 ∷ i2 ∷ i3 ∷ i4 ∷ i5 ∷ i6 ∷ i7 ∷ i8 ∷ i9 ∷ i10 ∷ i11 ∷ is) s ≡ execInstr (i0 ∷ i1 ∷ i2 ∷ i3 ∷ i4 ∷ i5 ∷ i6 ∷ i7 ∷ i8 ∷ i9 ∷ i10 ∷ i11 ∷ is) s i11
step-exec-11 i0 i1 i2 i3 i4 i5 i6 i7 i8 i9 i10 i11 is s h-false pc-11 =
  step-exec (i0 ∷ i1 ∷ i2 ∷ i3 ∷ i4 ∷ i5 ∷ i6 ∷ i7 ∷ i8 ∷ i9 ∷ i10 ∷ i11 ∷ is) s i11 h-false (subst (λ p → fetch (i0 ∷ i1 ∷ i2 ∷ i3 ∷ i4 ∷ i5 ∷ i6 ∷ i7 ∷ i8 ∷ i9 ∷ i10 ∷ i11 ∷ is) p ≡ just i11) (sym pc-11) refl)

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

-- | Step at arbitrary offset within combined program
step-exec-at-offset : ∀ (prefix : Program) (instr : Instr) (suffix : Program) (s : State) →
  halted s ≡ false →
  pc s ≡ length prefix →
  step (prefix ++ instr ∷ suffix) s ≡ execInstr (prefix ++ instr ∷ suffix) s instr
step-exec-at-offset prefix instr suffix s h-false pc-eq =
  step-exec (prefix ++ instr ∷ suffix) s instr h-false fetch-eq
  where
    -- Step 1: fetch (prefix ++ instr ∷ suffix) (length prefix +ℕ 0) ≡ just instr
    fetch-with-plus-0 : fetch (prefix ++ instr ∷ suffix) (length prefix +ℕ 0) ≡ just instr
    fetch-with-plus-0 = fetch-append-right prefix (instr ∷ suffix) 0

    -- Step 2: Use +-identityʳ to rewrite (length prefix +ℕ 0) to (length prefix)
    fetch-at-prefix-len : fetch (prefix ++ instr ∷ suffix) (length prefix) ≡ just instr
    fetch-at-prefix-len = subst (λ n → fetch (prefix ++ instr ∷ suffix) n ≡ just instr)
                                (+-identityʳ (length prefix))
                                fetch-with-plus-0

    -- Step 3: Use pc-eq to rewrite (length prefix) to (pc s)
    fetch-eq : fetch (prefix ++ instr ∷ suffix) (pc s) ≡ just instr
    fetch-eq = subst (λ n → fetch (prefix ++ instr ∷ suffix) n ≡ just instr)
                     (sym pc-eq)
                     fetch-at-prefix-len
