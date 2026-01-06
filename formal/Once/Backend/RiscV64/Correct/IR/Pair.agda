------------------------------------------------------------------------
-- Once.Backend.RiscV64.Correct.IR.Pair
--
-- Helper records and functions for pair proofs.
-- Extracts non-recursive parts to reduce mutual block compilation time.
-- The recursive calls stay in MutualIR.agda.
--
-- Pair structure for RISC-V (frame pointer approach):
--   Phase 1: Setup     (5 instr) - addi sp sp -32; sd s2 24(sp); sd s1 16(sp); mv s2 sp; mv s1 a0
--   Phase 2: Execute f (recursive) - sp may change, s2 remains stable
--   Phase 3: Middle    (2 instr) - sd a0 0(s2); mv a0 s1
--   Phase 4: Execute g (recursive) - sp may change, s2 remains stable
--   Phase 5: Final     (5 instr) - sd a0 8(s2); mv a0 s2; ld s1 16(s2); ld t0 24(s2); mv s2 t0
--
-- Total: 12 + len-f + len-g instructions
-- Stack: 32 bytes (16 for pair + 8 for s1 + 8 for s2)
-- Frame pointer s2 allows f and g to use arbitrary stack space.
------------------------------------------------------------------------

{-# OPTIONS --sized-types #-}

module Once.Backend.RiscV64.Correct.IR.Pair where

open import Size

open import Once.Type
open import Once.IRS
open import Once.SemanticsS

open import Once.Backend.RiscV64.Syntax
open import Once.Backend.RiscV64.Semantics
open State
open import Once.Backend.RiscV64.CodeGen

open import Once.Backend.RiscV64.Correct.CompileLength
open import Once.Backend.RiscV64.Correct.Foundation
open import Once.Backend.RiscV64.Correct.Star
  using (Star; refl*; step*; ⟨_,_⟩◅_; star-trans)
open import Once.Backend.RiscV64.Correct.StarBase
  using (IRStarResult;
         ir-star; ir-halted; ir-pc; ir-a0; ir-s1; ir-s2; ir-ra; ir-sp;
         ir-mem-preserved; ir-sp-delta; ir-sp-delta-leq)

open import Once.Backend.Common.Memory
  using (readMem-writeMem-same; readMem-writeMem-diff; n≢n+suc)

open import Data.Bool using (false)
open import Data.Nat using (ℕ; zero; suc; _∸_; _≤_; s≤s; z≤n) renaming (_+_ to _+ℕ_)
open import Data.Nat.Properties using (+-assoc; +-comm; +-identityʳ; m+n∸n≡m; m∸n+n≡m; ≤-trans; m≤m+n)
open import Data.Integer using (+_)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.List.Properties using (++-assoc) renaming (length-++ to List-length-++)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; ∃-syntax)
open import Data.Maybe using (just)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; subst; subst₂; cong; cong₂)
open import Relation.Binary.PropositionalEquality.Properties using (module ≡-Reasoning)
open ≡-Reasoning

------------------------------------------------------------------------
-- Result Records for Pair Phases
--
-- These records replace nested tuple returns to improve typechecking
-- performance. Using records allows Agda to handle field access more
-- efficiently than deeply nested proj₁/proj₂ chains.
------------------------------------------------------------------------

-- | Result of pair-setup-star: 5 instructions executed
-- Entry: pc = offset, a0 = encode x, 32 ≤ sp
-- Exit: pc = offset + 5, sp = orig-sp - 32, s1 = encode x, s2 = frame pointer
record PairSetupResult (prog : Program) (s s' : State)
                       (offset : ℕ) (x-enc orig-s1 orig-s2 orig-ra : Word) (orig-sp : ℕ) : Set where
  field
    star-setup    : Star prog s s'
    h-setup       : halted s' ≡ false
    pc-setup      : pc s' ≡ offset +ℕ 5
    a0-setup      : readReg (regs s') a0 ≡ x-enc
    s1-setup      : readReg (regs s') s1 ≡ x-enc
    sp-setup      : readReg (regs s') sp ≡ orig-sp ∸ 32
    s2-setup      : readReg (regs s') s2 ≡ orig-sp ∸ 32
    ra-setup      : readReg (regs s') ra ≡ orig-ra
    mem-s1-setup  : readMem (memory s') (readReg (regs s') s2 +ℕ 16) ≡ just orig-s1
    mem-s2-setup  : readMem (memory s') (readReg (regs s') s2 +ℕ 24) ≡ just orig-s2
    mem-preserved-setup : ∀ n → readMem (memory s') (orig-sp +ℕ n) ≡ readMem (memory s) (orig-sp +ℕ n)

-- | Result of pair-middle-star: 2 instructions executed
-- Stores f's result at frame pointer, restores x to a0
record PairMiddleResult (prog : Program) (sf s' : State)
                        (mid-offset : ℕ) (x-enc f-result-enc : Word)
                        (orig-sp : ℕ) : Set where
  field
    star-mid        : Star prog sf s'
    h-mid           : halted s' ≡ false
    pc-mid          : pc s' ≡ mid-offset +ℕ 2
    a0-mid          : readReg (regs s') a0 ≡ x-enc
    s1-mid          : readReg (regs s') s1 ≡ x-enc
    sp-mid          : readReg (regs s') sp ≡ readReg (regs sf) sp
    s2-mid          : readReg (regs s') s2 ≡ readReg (regs sf) s2
    ra-mid          : readReg (regs s') ra ≡ readReg (regs sf) ra
    mem-f-stored    : readMem (memory s') (readReg (regs sf) s2) ≡ just f-result-enc
    mem-s2+16-mid   : readMem (memory s') (readReg (regs sf) s2 +ℕ 16) ≡ readMem (memory sf) (readReg (regs sf) s2 +ℕ 16)
    mem-s2+24-mid   : readMem (memory s') (readReg (regs sf) s2 +ℕ 24) ≡ readMem (memory sf) (readReg (regs sf) s2 +ℕ 24)
    mem-preserved-mid : ∀ n → readMem (memory s') (orig-sp +ℕ n) ≡ readMem (memory sf) (orig-sp +ℕ n)

-- | Result of pair-final-star: 5 instructions executed
-- Stores g's result, constructs pair, restores s1 and s2
record PairFinalResult (prog : Program) (sg s' : State)
                       (final-offset : ℕ) (pair-enc orig-s1 orig-s2 : Word)
                       (orig-sp : ℕ) : Set where
  field
    star-final      : Star prog sg s'
    h-final         : halted s' ≡ false
    pc-final        : pc s' ≡ final-offset +ℕ 5
    a0-final        : readReg (regs s') a0 ≡ pair-enc
    s1-final        : readReg (regs s') s1 ≡ orig-s1
    s2-final        : readReg (regs s') s2 ≡ orig-s2
    ra-final        : readReg (regs s') ra ≡ readReg (regs sg) ra
    sp-final        : readReg (regs s') sp ≡ readReg (regs sg) sp
    mem-preserved-final : ∀ n → readMem (memory s') (orig-sp +ℕ n) ≡ readMem (memory sg) (orig-sp +ℕ n)

------------------------------------------------------------------------
-- Address Disjointness Lemmas
--
-- Key insight for pair memory preservation with frame pointer approach:
-- Setup allocates 32 bytes by doing sp' = sp - 32, then sets s2 = sp'.
-- The frame pointer s2 stays fixed throughout f and g execution.
-- Writes occur at s2 + k for k ∈ {0, 8, 16, 24} = orig-sp - {32, 24, 16, 8}.
-- These are all strictly less than orig-sp.
-- Therefore they're disjoint from orig-sp + k for any k ≥ 0.
------------------------------------------------------------------------

-- Helper: m < n → m ≢ n
<-implies-≢ : ∀ {m n} → suc m ≤ n → m ≢ n
<-implies-≢ {zero} {zero} () _
<-implies-≢ {zero} {suc n} _ ()
<-implies-≢ {suc m} {suc n} (s≤s p) eq = <-implies-≢ p (suc-injective eq)
  where
    suc-injective : ∀ {a b} → suc a ≡ suc b → a ≡ b
    suc-injective refl = refl

-- Lemma: n ∸ k + k ≡ n when k ≤ n (re-exports from Data.Nat.Properties as m∸n+n≡m)

-- Key insight: when 32 ≤ n, any address n - k (for k ≥ 8) is strictly less than n.
-- We only need the inequality, not the exact arithmetic.

-- Helper: (n ∸ 32) + 24 < (n ∸ 32) + 32 = n when n ≥ 32
-- So (n ∸ 32) + 24 < n, hence ≢ n + k for any k ≥ 0
-- This covers setup write at frame + 24 (saved s2)
setup-s2-addr-lt-orig : ∀ n → 32 ≤ n → suc ((n ∸ 32) +ℕ 24) ≤ n
setup-s2-addr-lt-orig n n≥32 =
  let restored : (n ∸ 32) +ℕ 32 ≡ n
      restored = m∸n+n≡m n≥32
      step1 : suc ((n ∸ 32) +ℕ 24) ≤ (n ∸ 32) +ℕ 32
      step1 = lemma (n ∸ 32)
  in subst (λ x → suc ((n ∸ 32) +ℕ 24) ≤ x) restored step1
  where
    -- suc (m + 24) ≤ m + 32, i.e., m + 25 ≤ m + 32
    lemma : ∀ m → suc (m +ℕ 24) ≤ (m +ℕ 32)
    lemma zero = s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))))))))))))))))))))
    lemma (suc m) = s≤s (lemma m)

-- Helper: (n ∸ 32) + 16 < n when n ≥ 32
-- This covers setup write at frame + 16 (saved s1)
setup-s1-addr-lt-orig : ∀ n → 32 ≤ n → suc ((n ∸ 32) +ℕ 16) ≤ n
setup-s1-addr-lt-orig n n≥32 =
  let restored : (n ∸ 32) +ℕ 32 ≡ n
      restored = m∸n+n≡m n≥32
      step1 : suc ((n ∸ 32) +ℕ 16) ≤ (n ∸ 32) +ℕ 32
      step1 = lemma (n ∸ 32)
  in subst (λ x → suc ((n ∸ 32) +ℕ 16) ≤ x) restored step1
  where
    -- suc (m + 16) ≤ m + 32, i.e., m + 17 ≤ m + 32
    lemma : ∀ m → suc (m +ℕ 16) ≤ (m +ℕ 32)
    lemma zero = s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))))))))))))
    lemma (suc m) = s≤s (lemma m)

-- Main lemmas for setup phase: write at new-sp + 16 ≢ orig-sp + k (for s1 save)
setup-write-s1-addr≢orig-sp : ∀ (orig-sp : ℕ) → 32 ≤ orig-sp →
  (orig-sp ∸ 32) +ℕ 16 ≢ orig-sp
setup-write-s1-addr≢orig-sp n n≥32 = <-implies-≢ (setup-s1-addr-lt-orig n n≥32)

setup-write-s1-addr≢orig-sp+8 : ∀ (orig-sp : ℕ) → 32 ≤ orig-sp →
  (orig-sp ∸ 32) +ℕ 16 ≢ orig-sp +ℕ 8
setup-write-s1-addr≢orig-sp+8 n n≥32 =
  <-implies-≢ (≤-trans (setup-s1-addr-lt-orig n n≥32) (m≤m+n n 8))

setup-write-s1-addr≢orig-sp+16 : ∀ (orig-sp : ℕ) → 32 ≤ orig-sp →
  (orig-sp ∸ 32) +ℕ 16 ≢ orig-sp +ℕ 16
setup-write-s1-addr≢orig-sp+16 n n≥32 =
  <-implies-≢ (≤-trans (setup-s1-addr-lt-orig n n≥32) (m≤m+n n 16))

setup-write-s1-addr≢orig-sp+24 : ∀ (orig-sp : ℕ) → 32 ≤ orig-sp →
  (orig-sp ∸ 32) +ℕ 16 ≢ orig-sp +ℕ 24
setup-write-s1-addr≢orig-sp+24 n n≥32 =
  <-implies-≢ (≤-trans (setup-s1-addr-lt-orig n n≥32) (m≤m+n n 24))

setup-write-s1-addr≢orig-sp+32 : ∀ (orig-sp : ℕ) → 32 ≤ orig-sp →
  (orig-sp ∸ 32) +ℕ 16 ≢ orig-sp +ℕ 32
setup-write-s1-addr≢orig-sp+32 n n≥32 =
  <-implies-≢ (≤-trans (setup-s1-addr-lt-orig n n≥32) (m≤m+n n 32))

-- Main lemmas for setup phase: write at new-sp + 24 ≢ orig-sp + k (for s2 save)
setup-write-s2-addr≢orig-sp : ∀ (orig-sp : ℕ) → 32 ≤ orig-sp →
  (orig-sp ∸ 32) +ℕ 24 ≢ orig-sp
setup-write-s2-addr≢orig-sp n n≥32 = <-implies-≢ (setup-s2-addr-lt-orig n n≥32)

setup-write-s2-addr≢orig-sp+8 : ∀ (orig-sp : ℕ) → 32 ≤ orig-sp →
  (orig-sp ∸ 32) +ℕ 24 ≢ orig-sp +ℕ 8
setup-write-s2-addr≢orig-sp+8 n n≥32 =
  <-implies-≢ (≤-trans (setup-s2-addr-lt-orig n n≥32) (m≤m+n n 8))

setup-write-s2-addr≢orig-sp+16 : ∀ (orig-sp : ℕ) → 32 ≤ orig-sp →
  (orig-sp ∸ 32) +ℕ 24 ≢ orig-sp +ℕ 16
setup-write-s2-addr≢orig-sp+16 n n≥32 =
  <-implies-≢ (≤-trans (setup-s2-addr-lt-orig n n≥32) (m≤m+n n 16))

setup-write-s2-addr≢orig-sp+24 : ∀ (orig-sp : ℕ) → 32 ≤ orig-sp →
  (orig-sp ∸ 32) +ℕ 24 ≢ orig-sp +ℕ 24
setup-write-s2-addr≢orig-sp+24 n n≥32 =
  <-implies-≢ (≤-trans (setup-s2-addr-lt-orig n n≥32) (m≤m+n n 24))

setup-write-s2-addr≢orig-sp+32 : ∀ (orig-sp : ℕ) → 32 ≤ orig-sp →
  (orig-sp ∸ 32) +ℕ 24 ≢ orig-sp +ℕ 32
setup-write-s2-addr≢orig-sp+32 n n≥32 =
  <-implies-≢ (≤-trans (setup-s2-addr-lt-orig n n≥32) (m≤m+n n 32))

-- Generic helpers for arbitrary offset k
setup-write-s1-addr≢orig-sp+any : ∀ (orig-sp k : ℕ) → 32 ≤ orig-sp →
  (orig-sp ∸ 32) +ℕ 16 ≢ orig-sp +ℕ k
setup-write-s1-addr≢orig-sp+any n k n≥32 =
  <-implies-≢ (≤-trans (setup-s1-addr-lt-orig n n≥32) (m≤m+n n k))

setup-write-s2-addr≢orig-sp+any : ∀ (orig-sp k : ℕ) → 32 ≤ orig-sp →
  (orig-sp ∸ 32) +ℕ 24 ≢ orig-sp +ℕ k
setup-write-s2-addr≢orig-sp+any n k n≥32 =
  <-implies-≢ (≤-trans (setup-s2-addr-lt-orig n n≥32) (m≤m+n n k))

-- Middle phase lemmas: write at frame + 0 = orig-sp - 32
-- When n ≥ 32, n - 32 < n, so n - 32 ≢ n + k for any k ≥ 0

-- Lemma: suc (n ∸ 32) ≤ n when 32 ≤ n
sp-minus-32-lt-sp : ∀ n → 32 ≤ n → suc (n ∸ 32) ≤ n
sp-minus-32-lt-sp n n≥32 =
  let restored : (n ∸ 32) +ℕ 32 ≡ n
      restored = m∸n+n≡m n≥32
      step1 : suc (n ∸ 32) ≤ (n ∸ 32) +ℕ 32
      step1 = lemma (n ∸ 32)
  in subst (λ x → suc (n ∸ 32) ≤ x) restored step1
  where
    -- suc m ≤ m + 32
    lemma : ∀ m → suc m ≤ (m +ℕ 32)
    lemma zero = s≤s z≤n
    lemma (suc m) = s≤s (lemma m)

middle-write-addr≢orig-sp : ∀ (orig-sp : ℕ) → 32 ≤ orig-sp →
  orig-sp ∸ 32 ≢ orig-sp
middle-write-addr≢orig-sp n n≥32 = <-implies-≢ (sp-minus-32-lt-sp n n≥32)

middle-write-addr≢orig-sp+8 : ∀ (orig-sp : ℕ) → 32 ≤ orig-sp →
  orig-sp ∸ 32 ≢ orig-sp +ℕ 8
middle-write-addr≢orig-sp+8 n n≥32 eq =
  <-implies-≢ (≤-trans (sp-minus-32-lt-sp n n≥32) (m≤m+n n 8)) eq

middle-write-addr≢orig-sp+16 : ∀ (orig-sp : ℕ) → 32 ≤ orig-sp →
  orig-sp ∸ 32 ≢ orig-sp +ℕ 16
middle-write-addr≢orig-sp+16 n n≥32 eq =
  <-implies-≢ (≤-trans (sp-minus-32-lt-sp n n≥32) (m≤m+n n 16)) eq

middle-write-addr≢orig-sp+24 : ∀ (orig-sp : ℕ) → 32 ≤ orig-sp →
  orig-sp ∸ 32 ≢ orig-sp +ℕ 24
middle-write-addr≢orig-sp+24 n n≥32 eq =
  <-implies-≢ (≤-trans (sp-minus-32-lt-sp n n≥32) (m≤m+n n 24)) eq

middle-write-addr≢orig-sp+32 : ∀ (orig-sp : ℕ) → 32 ≤ orig-sp →
  orig-sp ∸ 32 ≢ orig-sp +ℕ 32
middle-write-addr≢orig-sp+32 n n≥32 eq =
  <-implies-≢ (≤-trans (sp-minus-32-lt-sp n n≥32) (m≤m+n n 32)) eq

-- Generic helper for middle phase: write at (orig-sp - 32) ≢ orig-sp + k for any k
middle-write-addr≢orig-sp+any : ∀ (orig-sp k : ℕ) → 32 ≤ orig-sp →
  orig-sp ∸ 32 ≢ orig-sp +ℕ k
middle-write-addr≢orig-sp+any n k n≥32 eq =
  <-implies-≢ (≤-trans (sp-minus-32-lt-sp n n≥32) (m≤m+n n k)) eq

-- Final phase lemmas: write at frame + 8 = (orig-sp ∸ 32) + 8 ≢ orig-sp + k
-- When n ≥ 32, (n ∸ 32) + 8 < n, so it's ≢ n + k for any k ≥ 0

-- Helper: (n ∸ 32) + 8 < (n ∸ 32) + 32 = n when n ≥ 32
final-addr-lt-orig : ∀ n → 32 ≤ n → suc ((n ∸ 32) +ℕ 8) ≤ n
final-addr-lt-orig n n≥32 =
  let restored : (n ∸ 32) +ℕ 32 ≡ n
      restored = m∸n+n≡m n≥32
      step1 : suc ((n ∸ 32) +ℕ 8) ≤ (n ∸ 32) +ℕ 32
      step1 = lemma (n ∸ 32)
  in subst (λ x → suc ((n ∸ 32) +ℕ 8) ≤ x) restored step1
  where
    -- suc (m + 8) ≤ m + 32, i.e., m + 9 ≤ m + 32
    lemma : ∀ m → suc (m +ℕ 8) ≤ (m +ℕ 32)
    lemma zero = s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))))
    lemma (suc m) = s≤s (lemma m)

final-write-addr≢orig-sp : ∀ (orig-sp : ℕ) → 32 ≤ orig-sp →
  (orig-sp ∸ 32) +ℕ 8 ≢ orig-sp
final-write-addr≢orig-sp n n≥32 = <-implies-≢ (final-addr-lt-orig n n≥32)

final-write-addr≢orig-sp+8 : ∀ (orig-sp : ℕ) → 32 ≤ orig-sp →
  (orig-sp ∸ 32) +ℕ 8 ≢ orig-sp +ℕ 8
final-write-addr≢orig-sp+8 n n≥32 =
  <-implies-≢ (≤-trans (final-addr-lt-orig n n≥32) (m≤m+n n 8))

final-write-addr≢orig-sp+16 : ∀ (orig-sp : ℕ) → 32 ≤ orig-sp →
  (orig-sp ∸ 32) +ℕ 8 ≢ orig-sp +ℕ 16
final-write-addr≢orig-sp+16 n n≥32 =
  <-implies-≢ (≤-trans (final-addr-lt-orig n n≥32) (m≤m+n n 16))

final-write-addr≢orig-sp+24 : ∀ (orig-sp : ℕ) → 32 ≤ orig-sp →
  (orig-sp ∸ 32) +ℕ 8 ≢ orig-sp +ℕ 24
final-write-addr≢orig-sp+24 n n≥32 =
  <-implies-≢ (≤-trans (final-addr-lt-orig n n≥32) (m≤m+n n 24))

final-write-addr≢orig-sp+32 : ∀ (orig-sp : ℕ) → 32 ≤ orig-sp →
  (orig-sp ∸ 32) +ℕ 8 ≢ orig-sp +ℕ 32
final-write-addr≢orig-sp+32 n n≥32 =
  <-implies-≢ (≤-trans (final-addr-lt-orig n n≥32) (m≤m+n n 32))

-- Generic helper for final phase: write at (orig-sp - 32) + 8 ≢ orig-sp + k for any k
final-write-addr≢orig-sp+any : ∀ (orig-sp k : ℕ) → 32 ≤ orig-sp →
  (orig-sp ∸ 32) +ℕ 8 ≢ orig-sp +ℕ k
final-write-addr≢orig-sp+any n k n≥32 =
  <-implies-≢ (≤-trans (final-addr-lt-orig n n≥32) (m≤m+n n k))

------------------------------------------------------------------------
-- Pair Context: computed values that don't depend on execution
--
-- Frame pointer approach (12 instructions total):
--   Setup (5):  addi sp sp -32; sd s2 24(sp); sd s1 16(sp); mv s2 sp; mv s1 a0
--   Middle (2): sd a0 0(s2); mv a0 s1
--   Final (5):  sd a0 8(s2); mv a0 s2; ld s1 16(s2); ld t0 24(s2); mv s2 t0
------------------------------------------------------------------------

record PairContext {i : Size} {A B C : Type} (f : IR i C A) (g : IR i C B)
                   (prefix suffix : Program) : Set where
  field
    -- Computed lengths
    len-f : ℕ
    len-g : ℕ

    -- Computed programs
    code-f : Program
    code-g : Program
    prog : Program

    -- Setup instructions (5)
    setup-alloc : Instr      -- addi sp sp -32
    setup-save-s2 : Instr    -- sd s2 24(sp)
    setup-save-s1 : Instr    -- sd s1 16(sp)
    setup-set-fp : Instr     -- mv s2 sp
    setup-copy : Instr       -- mv s1 a0

    -- Middle instructions (2)
    middle-store : Instr   -- sd a0 0(s2)
    middle-restore : Instr -- mv a0 s1

    -- Final instructions (5)
    final-store : Instr      -- sd a0 8(s2)
    final-result : Instr     -- mv a0 s2
    final-restore-s1 : Instr -- ld s1 16(s2)
    final-load-s2 : Instr    -- ld t0 24(s2)
    final-restore-s2 : Instr -- mv s2 t0

    -- Derived prefixes/suffixes
    prefix-f : Program     -- prefix ++ setup (5 instructions)
    suffix-f : Program     -- middle ++ code-g ++ final ++ suffix
    prefix-g : Program     -- prefix-f ++ code-f ++ middle
    suffix-g : Program     -- final ++ suffix (5 instructions)
    prefix-mid : Program   -- prefix-f ++ code-f
    prefix-final : Program -- prefix-g ++ code-g

    -- Length equalities (updated for 5-instr setup and final)
    len-prefix-f : length prefix-f ≡ length prefix +ℕ 5
    len-prefix-g : length prefix-g ≡ length prefix +ℕ 7 +ℕ len-f
    len-prefix-mid : length prefix-mid ≡ length prefix +ℕ 5 +ℕ len-f
    len-prefix-final : length prefix-final ≡ length prefix +ℕ 7 +ℕ len-f +ℕ len-g

    -- Program equalities for each phase
    prog-eq-f : prog ≡ prefix-f ++ code-f ++ suffix-f
    prog-eq-g : prog ≡ prefix-g ++ code-g ++ suffix-g

-- | Compute the pair context
make-pair-context : ∀ {i A B C} (f : IR i C A) (g : IR i C B) (prefix suffix : Program) →
  PairContext f g prefix suffix
make-pair-context {_} {A} {B} {C} f g prefix suffix = record
  { len-f = len-f
  ; len-g = len-g
  ; code-f = code-f
  ; code-g = code-g
  ; prog = prog
  ; setup-alloc = setup-alloc
  ; setup-save-s2 = setup-save-s2
  ; setup-save-s1 = setup-save-s1
  ; setup-set-fp = setup-set-fp
  ; setup-copy = setup-copy
  ; middle-store = middle-store
  ; middle-restore = middle-restore
  ; final-store = final-store
  ; final-result = final-result
  ; final-restore-s1 = final-restore-s1
  ; final-load-s2 = final-load-s2
  ; final-restore-s2 = final-restore-s2
  ; prefix-f = prefix-f
  ; suffix-f = suffix-f
  ; prefix-g = prefix-g
  ; suffix-g = suffix-g
  ; prefix-mid = prefix-mid
  ; prefix-final = prefix-final
  ; len-prefix-f = len-prefix-f
  ; len-prefix-g = len-prefix-g
  ; len-prefix-mid = len-prefix-mid
  ; len-prefix-final = len-prefix-final
  ; prog-eq-f = prog-eq-f
  ; prog-eq-g = prog-eq-g
  }
  where
    len-f = compile-length f
    len-g = compile-length g
    code-f = compile-riscv f
    code-g = compile-riscv g
    prog = prefix ++ compile-riscv ⟨ f , g ⟩ ++ suffix

    -- Setup instructions (5) - frame pointer approach
    setup-alloc = addi sp sp neg32
    setup-save-s2 = sd s2 (+ 24) sp
    setup-save-s1 = sd s1 (+ 16) sp
    setup-set-fp = mv s2 sp
    setup-copy = mv s1 a0

    -- Middle instructions (2) - store to frame pointer
    middle-store = sd a0 (+ 0) s2
    middle-restore = mv a0 s1

    -- Final instructions (5) - restore via frame pointer
    final-store = sd a0 (+ 8) s2
    final-result = mv a0 s2
    final-restore-s1 = ld s1 (+ 16) s2
    final-load-s2 = ld t0 (+ 24) s2
    final-restore-s2 = mv s2 t0

    -- Final instruction sequence
    final-instrs = final-store ∷ final-result ∷ final-restore-s1 ∷ final-load-s2 ∷ final-restore-s2 ∷ []

    -- Derived programs (setup now has 5 instructions)
    prefix-f : Program
    prefix-f = prefix ++ setup-alloc ∷ setup-save-s2 ∷ setup-save-s1 ∷ setup-set-fp ∷ setup-copy ∷ []

    suffix-f : Program
    suffix-f = middle-store ∷ middle-restore ∷ code-g ++ final-store ∷ final-result ∷ final-restore-s1 ∷ final-load-s2 ∷ final-restore-s2 ∷ suffix

    prefix-mid : Program
    prefix-mid = prefix-f ++ code-f

    prefix-g : Program
    prefix-g = (prefix-f ++ code-f) ++ middle-store ∷ middle-restore ∷ []

    suffix-g : Program
    suffix-g = final-store ∷ final-result ∷ final-restore-s1 ∷ final-load-s2 ∷ final-restore-s2 ∷ suffix

    prefix-final : Program
    prefix-final = prefix-g ++ code-g

    -- Length equalities (updated for 5-instruction setup)
    len-prefix-f : length prefix-f ≡ length prefix +ℕ 5
    len-prefix-f = List-length-++ prefix

    len-prefix-mid : length prefix-mid ≡ length prefix +ℕ 5 +ℕ len-f
    len-prefix-mid = begin
      length prefix-mid
        ≡⟨ List-length-++ prefix-f ⟩
      length prefix-f +ℕ length code-f
        ≡⟨ cong (_+ℕ length code-f) len-prefix-f ⟩
      (length prefix +ℕ 5) +ℕ length code-f
        ≡⟨ cong ((length prefix +ℕ 5) +ℕ_) (compile-length-correct f) ⟩
      (length prefix +ℕ 5) +ℕ len-f
        ∎

    len-prefix-g : length prefix-g ≡ length prefix +ℕ 7 +ℕ len-f
    len-prefix-g = begin
      length prefix-g
        ≡⟨ List-length-++ (prefix-f ++ code-f) ⟩
      length (prefix-f ++ code-f) +ℕ 2
        ≡⟨ cong (_+ℕ 2) len-prefix-mid ⟩
      (length prefix +ℕ 5 +ℕ len-f) +ℕ 2
        ≡⟨ +-assoc (length prefix +ℕ 5) len-f 2 ⟩
      (length prefix +ℕ 5) +ℕ (len-f +ℕ 2)
        ≡⟨ +-assoc (length prefix) 5 (len-f +ℕ 2) ⟩
      length prefix +ℕ (5 +ℕ (len-f +ℕ 2))
        ≡⟨ cong (length prefix +ℕ_) (sym (+-assoc 5 len-f 2)) ⟩
      length prefix +ℕ ((5 +ℕ len-f) +ℕ 2)
        ≡⟨ cong (λ x → length prefix +ℕ (x +ℕ 2)) (+-comm 5 len-f) ⟩
      length prefix +ℕ ((len-f +ℕ 5) +ℕ 2)
        ≡⟨ cong (length prefix +ℕ_) (+-assoc len-f 5 2) ⟩
      length prefix +ℕ (len-f +ℕ 7)
        ≡⟨ sym (+-assoc (length prefix) len-f 7) ⟩
      (length prefix +ℕ len-f) +ℕ 7
        ≡⟨ cong (_+ℕ 7) (+-comm (length prefix) len-f) ⟩
      (len-f +ℕ length prefix) +ℕ 7
        ≡⟨ +-assoc len-f (length prefix) 7 ⟩
      len-f +ℕ (length prefix +ℕ 7)
        ≡⟨ +-comm len-f (length prefix +ℕ 7) ⟩
      (length prefix +ℕ 7) +ℕ len-f
        ∎

    len-prefix-final : length prefix-final ≡ length prefix +ℕ 7 +ℕ len-f +ℕ len-g
    len-prefix-final = begin
      length prefix-final
        ≡⟨ List-length-++ prefix-g ⟩
      length prefix-g +ℕ length code-g
        ≡⟨ cong₂ _+ℕ_ len-prefix-g (compile-length-correct g) ⟩
      ((length prefix +ℕ 7) +ℕ len-f) +ℕ len-g
        ∎
      where
        open import Relation.Binary.PropositionalEquality using (cong₂)

    -- Program equality for f
    -- prog = prefix ++ (setup ++ code-f ++ middle ++ code-g ++ final-instrs) ++ suffix
    -- Need: prog = prefix-f ++ code-f ++ suffix-f

    -- Helper: code-g ++ final-instrs ++ suffix = code-g ++ final ++ suffix
    final-suffix-eq : (code-g ++ final-instrs) ++ suffix ≡ code-g ++ (final-store ∷ final-result ∷ final-restore-s1 ∷ final-load-s2 ∷ final-restore-s2 ∷ suffix)
    final-suffix-eq = ++-assoc code-g final-instrs suffix

    -- Helper: middle with code-g and final
    middle-suffix-eq : (middle-store ∷ middle-restore ∷ code-g ++ final-instrs) ++ suffix
                     ≡ middle-store ∷ middle-restore ∷ (code-g ++ final-store ∷ final-result ∷ final-restore-s1 ∷ final-load-s2 ∷ final-restore-s2 ∷ suffix)
    middle-suffix-eq = cong (middle-store ∷_) (cong (middle-restore ∷_) final-suffix-eq)

    -- Helper: code-f with middle, code-g and final
    f-suffix-eq : (code-f ++ middle-store ∷ middle-restore ∷ code-g ++ final-instrs) ++ suffix
                ≡ code-f ++ suffix-f
    f-suffix-eq = trans (++-assoc code-f (middle-store ∷ middle-restore ∷ code-g ++ final-instrs) suffix)
                        (cong (code-f ++_) middle-suffix-eq)

    -- Full program equality for f (now 5 setup instructions)
    full-suffix-eq : compile-riscv ⟨ f , g ⟩ ++ suffix
                   ≡ setup-alloc ∷ setup-save-s2 ∷ setup-save-s1 ∷ setup-set-fp ∷ setup-copy ∷ (code-f ++ suffix-f)
    full-suffix-eq = cong (setup-alloc ∷_) (cong (setup-save-s2 ∷_) (cong (setup-save-s1 ∷_) (cong (setup-set-fp ∷_) (cong (setup-copy ∷_) f-suffix-eq))))

    prog-eq-f : prog ≡ prefix-f ++ code-f ++ suffix-f
    prog-eq-f = trans (cong (prefix ++_) full-suffix-eq)
                      (sym (++-assoc prefix (setup-alloc ∷ setup-save-s2 ∷ setup-save-s1 ∷ setup-set-fp ∷ setup-copy ∷ []) (code-f ++ suffix-f)))

    -- Program equality for g (derived from f equality)
    prog-eq-g : prog ≡ prefix-g ++ code-g ++ suffix-g
    prog-eq-g = trans prog-eq-f (begin
      prefix-f ++ code-f ++ suffix-f
        ≡⟨ sym (++-assoc prefix-f code-f suffix-f) ⟩
      (prefix-f ++ code-f) ++ suffix-f
        ≡⟨ refl ⟩  -- suffix-f = middle-store ∷ middle-restore ∷ code-g ++ suffix-g
      prefix-mid ++ middle-store ∷ middle-restore ∷ code-g ++ suffix-g
        ≡⟨ sym (++-assoc prefix-mid (middle-store ∷ middle-restore ∷ []) (code-g ++ suffix-g)) ⟩
      (prefix-mid ++ middle-store ∷ middle-restore ∷ []) ++ (code-g ++ suffix-g)
        ≡⟨ refl ⟩
      prefix-g ++ code-g ++ suffix-g
        ∎)

------------------------------------------------------------------------
-- Phase 1: Setup - trace 5 instructions (frame pointer approach)
--   1. addi sp sp -32  (allocate stack space)
--   2. sd s2 24(sp)    (save original s2)
--   3. sd s1 16(sp)    (save original s1)
--   4. mv s2 sp        (set frame pointer)
--   5. mv s1 a0        (copy input to s1)
------------------------------------------------------------------------

-- | Setup phase: allocate pair space, save s1 and s2, set frame pointer
-- Entry: pc = offset, a0 = encode x, 32 ≤ sp
-- Exit: pc = offset + 5, sp = orig-sp - 32, s1 = encode x, s2 = frame pointer
--       mem[s2+16] = orig-s1, mem[s2+24] = orig-s2
pair-setup-star : ∀ {i A B C} (f : IR i C A) (g : IR i C B)
                  (prefix suffix : Program) (x : ⟦ C ⟧) (s : State) →
  let ctx = make-pair-context f g prefix suffix
      open PairContext ctx
      offset = length prefix
  in
  halted s ≡ false →
  pc s ≡ offset →
  readReg (regs s) a0 ≡ encode x →
  32 ≤ readReg (regs s) sp →  -- Stack bound precondition
  ∃[ s' ] PairSetupResult prog s s' offset (encode x)
            (readReg (regs s) s1) (readReg (regs s) s2) (readReg (regs s) ra)
            (readReg (regs s) sp)
pair-setup-star {i} {A} {B} {C} f g prefix suffix x s h-false pc-eq a0-eq sp-bound =
  st5 , record
    { star-setup = star-all
    ; h-setup = h5
    ; pc-setup = pc5
    ; a0-setup = a0-st5
    ; s1-setup = s1-st5
    ; sp-setup = sp-st5
    ; s2-setup = s2-st5
    ; ra-setup = ra-st5
    ; mem-s1-setup = mem-s1-saved
    ; mem-s2-setup = mem-s2-saved
    ; mem-preserved-setup = mem-preserved-generic
    }
  where
    ctx = make-pair-context f g prefix suffix
    open PairContext ctx
    offset = length prefix

    -- Original values we need to track
    orig-sp-val = readReg (regs s) sp
    orig-s1-val = readReg (regs s) s1
    orig-s2-val = readReg (regs s) s2
    orig-ra-val = readReg (regs s) ra
    orig-a0-val = readReg (regs s) a0
    new-sp = orig-sp-val ∸ 32

    -- Fetch lemmas for setup instructions
    -- prog = prefix ++ (setup-alloc ∷ setup-save-s2 ∷ setup-save-s1 ∷ setup-set-fp ∷ setup-copy ∷ code-f ++ ...)

    -- Program decomposition at each instruction position
    -- First, show prog can be written as prefix ++ setup-alloc ∷ rest
    -- prog-eq-f : prog ≡ prefix-f ++ code-f ++ suffix-f
    -- Since ++ is right-associative (infixr 5), this is prog ≡ prefix-f ++ (code-f ++ suffix-f)
    -- And prefix-f = prefix ++ setup-instrs, so we just need one ++-assoc
    setup-instrs : List Instr
    setup-instrs = setup-alloc ∷ setup-save-s2 ∷ setup-save-s1 ∷ setup-set-fp ∷ setup-copy ∷ []

    assoc-step : prefix-f ++ (code-f ++ suffix-f) ≡ prefix ++ (setup-instrs ++ (code-f ++ suffix-f))
    assoc-step = ++-assoc prefix setup-instrs (code-f ++ suffix-f)

    prog-setup : prog ≡ prefix ++ (setup-alloc ∷ setup-save-s2 ∷ setup-save-s1 ∷ setup-set-fp ∷ setup-copy ∷ code-f ++ suffix-f)
    prog-setup = trans prog-eq-f assoc-step

    fetch0 : fetch prog offset ≡ just setup-alloc
    fetch0 = subst₂ (λ p n → fetch p n ≡ just setup-alloc) (sym prog-setup) refl
               (fetch-at-prefix-end prefix setup-alloc _)

    prog-at-1 : prog ≡ (prefix ++ setup-alloc ∷ []) ++ setup-save-s2 ∷ setup-save-s1 ∷ setup-set-fp ∷ setup-copy ∷ code-f ++ suffix-f
    prog-at-1 = trans prog-setup (sym (++-assoc prefix (setup-alloc ∷ []) _))

    len-prefix-1 : length (prefix ++ setup-alloc ∷ []) ≡ offset +ℕ 1
    len-prefix-1 = List-length-++ prefix

    fetch1 : fetch prog (offset +ℕ 1) ≡ just setup-save-s2
    fetch1 = subst₂ (λ p n → fetch p n ≡ just setup-save-s2) (sym prog-at-1) len-prefix-1
               (fetch-at-prefix-end (prefix ++ setup-alloc ∷ []) setup-save-s2 _)

    prog-at-2 : prog ≡ (prefix ++ setup-alloc ∷ setup-save-s2 ∷ []) ++ setup-save-s1 ∷ setup-set-fp ∷ setup-copy ∷ code-f ++ suffix-f
    prog-at-2 = trans prog-setup (sym (++-assoc prefix (setup-alloc ∷ setup-save-s2 ∷ []) _))

    len-prefix-2 : length (prefix ++ setup-alloc ∷ setup-save-s2 ∷ []) ≡ offset +ℕ 2
    len-prefix-2 = List-length-++ prefix

    fetch2 : fetch prog (offset +ℕ 2) ≡ just setup-save-s1
    fetch2 = subst₂ (λ p n → fetch p n ≡ just setup-save-s1) (sym prog-at-2) len-prefix-2
               (fetch-at-prefix-end (prefix ++ setup-alloc ∷ setup-save-s2 ∷ []) setup-save-s1 _)

    prog-at-3 : prog ≡ (prefix ++ setup-alloc ∷ setup-save-s2 ∷ setup-save-s1 ∷ []) ++ setup-set-fp ∷ setup-copy ∷ code-f ++ suffix-f
    prog-at-3 = trans prog-setup (sym (++-assoc prefix (setup-alloc ∷ setup-save-s2 ∷ setup-save-s1 ∷ []) _))

    len-prefix-3 : length (prefix ++ setup-alloc ∷ setup-save-s2 ∷ setup-save-s1 ∷ []) ≡ offset +ℕ 3
    len-prefix-3 = List-length-++ prefix

    fetch3 : fetch prog (offset +ℕ 3) ≡ just setup-set-fp
    fetch3 = subst₂ (λ p n → fetch p n ≡ just setup-set-fp) (sym prog-at-3) len-prefix-3
               (fetch-at-prefix-end (prefix ++ setup-alloc ∷ setup-save-s2 ∷ setup-save-s1 ∷ []) setup-set-fp _)

    prog-at-4 : prog ≡ (prefix ++ setup-alloc ∷ setup-save-s2 ∷ setup-save-s1 ∷ setup-set-fp ∷ []) ++ setup-copy ∷ code-f ++ suffix-f
    prog-at-4 = trans prog-setup (sym (++-assoc prefix (setup-alloc ∷ setup-save-s2 ∷ setup-save-s1 ∷ setup-set-fp ∷ []) _))

    len-prefix-4 : length (prefix ++ setup-alloc ∷ setup-save-s2 ∷ setup-save-s1 ∷ setup-set-fp ∷ []) ≡ offset +ℕ 4
    len-prefix-4 = List-length-++ prefix

    fetch4 : fetch prog (offset +ℕ 4) ≡ just setup-copy
    fetch4 = subst₂ (λ p n → fetch p n ≡ just setup-copy) (sym prog-at-4) len-prefix-4
               (fetch-at-prefix-end (prefix ++ setup-alloc ∷ setup-save-s2 ∷ setup-save-s1 ∷ setup-set-fp ∷ []) setup-copy _)

    -- Step 0: addi sp sp -32 (allocate stack space)
    st1 : State
    st1 = record s { regs = writeReg (regs s) sp new-sp
                   ; pc = pc s +ℕ 1 }

    step0 : step prog s ≡ just st1
    step0 = trans (step-exec prog s setup-alloc h-false
                    (subst (λ p → fetch prog p ≡ just setup-alloc) (sym pc-eq) fetch0))
                  (execAddiNeg prog s sp sp 31)

    h1 : halted st1 ≡ false
    h1 = h-false

    pc1 : pc st1 ≡ offset +ℕ 1
    pc1 = cong (_+ℕ 1) pc-eq

    -- Step 1: sd s2 24(sp) (save original s2)
    -- Now sp = new-sp, and we store orig-s2-val at new-sp + 24
    st2 : State
    st2 = record st1 { memory = writeMem (memory st1) (new-sp +ℕ 24) orig-s2-val
                     ; pc = pc st1 +ℕ 1 }

    -- Need to show s2 value in st1 is still orig-s2-val
    s2-st1 : readReg (regs st1) s2 ≡ orig-s2-val
    s2-st1 = readReg-writeReg-sp-s2 (regs s) new-sp

    -- Need to show sp value in st1 is new-sp
    sp-st1-eq : readReg (regs st1) sp ≡ new-sp
    sp-st1-eq = readReg-writeReg-same (regs s) sp new-sp (λ ())

    step1 : step prog st1 ≡ just st2
    step1 = trans (step-exec prog st1 setup-save-s2 h1
                    (subst (λ p → fetch prog p ≡ just setup-save-s2) (sym pc1) fetch1))
                  (trans (execSd prog st1 s2 24 sp)
                         (cong just (cong₂ (λ sp-v s2-v → record st1 { memory = writeMem (memory st1) (sp-v +ℕ 24) s2-v ; pc = pc st1 +ℕ 1 })
                                           sp-st1-eq s2-st1)))

    h2 : halted st2 ≡ false
    h2 = h-false

    pc2 : pc st2 ≡ offset +ℕ 2
    pc2 = trans (cong (_+ℕ 1) pc1) (+-assoc offset 1 1)

    -- Step 2: sd s1 16(sp) (save original s1)
    -- sp = new-sp, s1 = orig-s1-val
    st3 : State
    st3 = record st2 { memory = writeMem (memory st2) (new-sp +ℕ 16) orig-s1-val
                     ; pc = pc st2 +ℕ 1 }

    s1-st2 : readReg (regs st2) s1 ≡ orig-s1-val
    s1-st2 = readReg-writeReg-sp-s1 (regs s) new-sp  -- sd doesn't change regs

    sp-st2-eq : readReg (regs st2) sp ≡ new-sp
    sp-st2-eq = sp-st1-eq  -- sd doesn't change regs

    step2 : step prog st2 ≡ just st3
    step2 = trans (step-exec prog st2 setup-save-s1 h2
                    (subst (λ p → fetch prog p ≡ just setup-save-s1) (sym pc2) fetch2))
                  (trans (execSd prog st2 s1 16 sp)
                         (cong just (cong₂ (λ sp-v s1-v → record st2 { memory = writeMem (memory st2) (sp-v +ℕ 16) s1-v ; pc = pc st2 +ℕ 1 })
                                           sp-st2-eq s1-st2)))

    h3 : halted st3 ≡ false
    h3 = h-false

    pc3 : pc st3 ≡ offset +ℕ 3
    pc3 = trans (cong (_+ℕ 1) pc2) (+-assoc offset 2 1)

    -- Step 3: mv s2 sp (set frame pointer)
    st4 : State
    st4 = record st3 { regs = writeReg (regs st3) s2 (readReg (regs st3) sp)
                     ; pc = pc st3 +ℕ 1 }

    sp-st3-eq : readReg (regs st3) sp ≡ new-sp
    sp-st3-eq = sp-st2-eq  -- sd doesn't change regs

    step3 : step prog st3 ≡ just st4
    step3 = trans (step-exec prog st3 setup-set-fp h3
                    (subst (λ p → fetch prog p ≡ just setup-set-fp) (sym pc3) fetch3))
                  (execMv prog st3 s2 sp)

    h4 : halted st4 ≡ false
    h4 = h-false

    pc4 : pc st4 ≡ offset +ℕ 4
    pc4 = trans (cong (_+ℕ 1) pc3) (+-assoc offset 3 1)

    -- Step 4: mv s1 a0 (copy input to s1)
    st5 : State
    st5 = record st4 { regs = writeReg (regs st4) s1 (readReg (regs st4) a0)
                     ; pc = pc st4 +ℕ 1 }

    a0-st4 : readReg (regs st4) a0 ≡ encode x
    a0-st4 = trans (readReg-writeReg-s2-a0 (regs st3) (readReg (regs st3) sp))
                   (trans (readReg-writeReg-sp-a0 (regs s) new-sp) a0-eq)

    step4 : step prog st4 ≡ just st5
    step4 = trans (step-exec prog st4 setup-copy h4
                    (subst (λ p → fetch prog p ≡ just setup-copy) (sym pc4) fetch4))
                  (execMv prog st4 s1 a0)

    -- Star proof: chain all 5 steps
    star-all : Star prog s st5
    star-all = ⟨ h-false , step0 ⟩◅ ⟨ h1 , step1 ⟩◅ ⟨ h2 , step2 ⟩◅ ⟨ h3 , step3 ⟩◅ ⟨ h4 , step4 ⟩◅ refl*

    -- Final state properties
    h5 : halted st5 ≡ false
    h5 = h-false

    pc5 : pc st5 ≡ offset +ℕ 5
    pc5 = trans (cong (_+ℕ 1) pc4) (+-assoc offset 4 1)

    -- a0 is preserved through all 5 steps (only modified sp, s2, s1)
    a0-st5 : readReg (regs st5) a0 ≡ encode x
    a0-st5 = trans (readReg-writeReg-s1-a0 (regs st4) (readReg (regs st4) a0)) a0-st4

    -- s1 = encode x (from mv s1 a0)
    s1-st5 : readReg (regs st5) s1 ≡ encode x
    s1-st5 = trans (readReg-writeReg-same (regs st4) s1 (readReg (regs st4) a0) (λ ())) a0-st4

    -- sp = new-sp (preserved through mv instructions)
    sp-st4 : readReg (regs st4) sp ≡ new-sp
    sp-st4 = trans (readReg-writeReg-s2-sp (regs st3) (readReg (regs st3) sp)) sp-st3-eq

    sp-st5 : readReg (regs st5) sp ≡ orig-sp-val ∸ 32
    sp-st5 = trans (readReg-writeReg-s1-sp (regs st4) (readReg (regs st4) a0)) sp-st4

    -- s2 = new-sp (from mv s2 sp)
    s2-st4 : readReg (regs st4) s2 ≡ new-sp
    s2-st4 = trans (readReg-writeReg-same (regs st3) s2 (readReg (regs st3) sp) (λ ())) sp-st3-eq

    s2-st5 : readReg (regs st5) s2 ≡ orig-sp-val ∸ 32
    s2-st5 = trans (readReg-writeReg-s1-s2 (regs st4) (readReg (regs st4) a0)) s2-st4

    -- ra is preserved
    ra-st1 : readReg (regs st1) ra ≡ orig-ra-val
    ra-st1 = readReg-writeReg-sp-ra (regs s) new-sp

    ra-st4 : readReg (regs st4) ra ≡ orig-ra-val
    ra-st4 = trans (readReg-writeReg-s2-ra (regs st3) (readReg (regs st3) sp)) ra-st1

    ra-st5 : readReg (regs st5) ra ≡ orig-ra-val
    ra-st5 = trans (readReg-writeReg-s1-ra (regs st4) (readReg (regs st4) a0)) ra-st4

    -- Memory: s1 saved at frame+16 (= new-sp+16)
    -- The last write was s1 at new-sp+16, so this should be readable

    -- Memory at frame+16 = memory at new-sp+16 = orig-s1-val
    -- st5 has same memory as st4 (mv doesn't change memory)
    -- st4 has same memory as st3 (mv doesn't change memory)
    -- st3 wrote orig-s1-val at new-sp+16
    mem-s1-at-st3 : readMem (memory st3) (new-sp +ℕ 16) ≡ just orig-s1-val
    mem-s1-at-st3 = readMem-writeMem-same (memory st2) (new-sp +ℕ 16) orig-s1-val

    mem-s1-saved : readMem (memory st5) (readReg (regs st5) s2 +ℕ 16) ≡ just orig-s1-val
    mem-s1-saved = subst (λ addr → readMem (memory st5) (addr +ℕ 16) ≡ just orig-s1-val)
                         (sym s2-st5) mem-s1-at-st3

    -- Memory: s2 saved at frame+24 (= new-sp+24)
    -- st2 wrote orig-s2-val at new-sp+24
    -- st3 wrote at new-sp+16, which is ≢ new-sp+24
    -- Proof: n≢n+suc gives (new-sp + 16) ≢ (new-sp + 16) + 8
    --        +-assoc gives (new-sp + 16) + 8 = new-sp + 24
    --        subst transports along that equality
    16≢24 : (new-sp +ℕ 16) ≢ (new-sp +ℕ 24)
    16≢24 = subst (λ k → new-sp +ℕ 16 ≢ k) (+-assoc new-sp 16 8) (n≢n+suc (new-sp +ℕ 16) 7)

    mem-s2-at-st2 : readMem (memory st2) (new-sp +ℕ 24) ≡ just orig-s2-val
    mem-s2-at-st2 = readMem-writeMem-same (memory st1) (new-sp +ℕ 24) orig-s2-val

    mem-s2-at-st3 : readMem (memory st3) (new-sp +ℕ 24) ≡ just orig-s2-val
    mem-s2-at-st3 = trans (readMem-writeMem-diff (memory st2) (new-sp +ℕ 16) (new-sp +ℕ 24) orig-s1-val 16≢24)
                          mem-s2-at-st2

    mem-s2-saved : readMem (memory st5) (readReg (regs st5) s2 +ℕ 24) ≡ just orig-s2-val
    mem-s2-saved = subst (λ addr → readMem (memory st5) (addr +ℕ 24) ≡ just orig-s2-val)
                         (sym s2-st5) mem-s2-at-st3

    -- Memory preservation at orig-sp and above (generic for any n)
    -- All writes are at new-sp+16 and new-sp+24, which are both < orig-sp
    -- using the generic address disjointness lemmas

    -- st1: memory same as s (addi doesn't change memory)
    -- st2: wrote at new-sp+24
    -- st3: wrote at new-sp+16
    -- st4, st5: memory same as st3 (mv doesn't change memory)

    mem-preserved-generic : ∀ n → readMem (memory st5) (orig-sp-val +ℕ n) ≡ readMem (memory s) (orig-sp-val +ℕ n)
    mem-preserved-generic n =
      let
        -- Writes at new-sp+24 and new-sp+16 are disjoint from orig-sp+n
        write-s2-addr≢ : (new-sp +ℕ 24) ≢ (orig-sp-val +ℕ n)
        write-s2-addr≢ = setup-write-s2-addr≢orig-sp+any orig-sp-val n sp-bound

        write-s1-addr≢ : (new-sp +ℕ 16) ≢ (orig-sp-val +ℕ n)
        write-s1-addr≢ = setup-write-s1-addr≢orig-sp+any orig-sp-val n sp-bound

        -- st1 has same memory as s (addi doesn't change memory)
        -- st2 wrote at new-sp+24, which is ≢ orig-sp+n
        mem-at-st2 : readMem (memory st2) (orig-sp-val +ℕ n) ≡ readMem (memory s) (orig-sp-val +ℕ n)
        mem-at-st2 = readMem-writeMem-diff (memory st1) (new-sp +ℕ 24) (orig-sp-val +ℕ n) orig-s2-val write-s2-addr≢

        -- st3 wrote at new-sp+16, which is ≢ orig-sp+n
        mem-at-st3 : readMem (memory st3) (orig-sp-val +ℕ n) ≡ readMem (memory s) (orig-sp-val +ℕ n)
        mem-at-st3 = trans (readMem-writeMem-diff (memory st2) (new-sp +ℕ 16) (orig-sp-val +ℕ n) orig-s1-val write-s1-addr≢)
                           mem-at-st2

      in mem-at-st3  -- st4, st5 have same memory as st3 (mv doesn't change memory)

------------------------------------------------------------------------
-- Phase 3: Middle - trace 2 instructions (sd a0 0(s2); mv a0 s1)
-- Frame pointer approach: store to s2 (frame pointer), not sp
------------------------------------------------------------------------

-- | Middle phase: store f result at frame pointer and restore original input
-- Entry: pc = offset + 5 + len-f, a0 = encode (eval f x), s1 = encode x
--        s2 = frame pointer (orig-sp ∸ 32), 32 ≤ orig-sp
-- Exit: pc = offset + 7 + len-f, a0 = encode x, memory[s2] = encode (eval f x)
pair-middle-star : ∀ {i A B C} (f : IR i C A) (g : IR i C B)
                   (prefix suffix : Program) (x : ⟦ C ⟧) (orig-sp : ℕ) (sf : State) →
  let ctx = make-pair-context f g prefix suffix
      open PairContext ctx
      mid-offset = length prefix +ℕ 5 +ℕ len-f
  in
  halted sf ≡ false →
  pc sf ≡ mid-offset →
  readReg (regs sf) a0 ≡ encode (eval f x) →
  readReg (regs sf) s1 ≡ encode x →
  32 ≤ orig-sp →  -- Stack bound precondition
  readReg (regs sf) s2 ≡ orig-sp ∸ 32 →  -- s2 = frame pointer
  ∃[ s' ] PairMiddleResult prog sf s' mid-offset (encode x) (encode (eval f x)) orig-sp
pair-middle-star {_} {A} {B} {C} f g prefix suffix x orig-sp sf h-false pc-eq a0-eq s1-eq sp-bound frame-ptr-eq =
  st2 , record
    { star-mid = star-all
    ; h-mid = h2
    ; pc-mid = pc2
    ; a0-mid = a0-st2
    ; s1-mid = s1-st2
    ; sp-mid = sp-st2
    ; s2-mid = s2-st2
    ; ra-mid = ra-st2
    ; mem-f-stored = mem-st2
    ; mem-s2+16-mid = mem-s2+16-st2
    ; mem-s2+24-mid = mem-s2+24-st2
    ; mem-preserved-mid = mem-preserved-generic
    }
  where
    ctx = make-pair-context f g prefix suffix
    open PairContext ctx
    mid-offset = length prefix +ℕ 5 +ℕ len-f

    frame-ptr = readReg (regs sf) s2  -- frame pointer

    -- Fetch lemmas (proven using fetch-at-prefix-end)
    -- prog = prefix-f ++ code-f ++ suffix-f
    --      = prefix-mid ++ middle-store ∷ middle-restore ∷ rest
    -- mid-offset = length prefix-mid

    prog-eq-mid : prog ≡ prefix-mid ++ suffix-f
    prog-eq-mid = trans prog-eq-f (sym (++-assoc prefix-f code-f suffix-f))

    fetch-mid0 : fetch prog mid-offset ≡ just middle-store
    fetch-mid0 = subst₂ (λ p n → fetch p n ≡ just middle-store) (sym prog-eq-mid) len-prefix-mid
                        (fetch-at-prefix-end prefix-mid middle-store _)

    prog-eq-mid1 : prog ≡ (prefix-mid ++ middle-store ∷ []) ++ _
    prog-eq-mid1 = trans prog-eq-mid (sym (++-assoc prefix-mid (middle-store ∷ []) _))

    len-prefix-mid1 : length (prefix-mid ++ middle-store ∷ []) ≡ mid-offset +ℕ 1
    len-prefix-mid1 = trans (List-length-++ prefix-mid) (cong (_+ℕ 1) len-prefix-mid)

    fetch-mid1 : fetch prog (mid-offset +ℕ 1) ≡ just middle-restore
    fetch-mid1 = subst₂ (λ p n → fetch p n ≡ just middle-restore) (sym prog-eq-mid1) len-prefix-mid1
                        (fetch-at-prefix-end (prefix-mid ++ middle-store ∷ []) middle-restore _)

    -- State after step 0: sd a0 0(s2) - store at frame pointer
    st1 : State
    st1 = record sf { memory = writeMem (memory sf) (frame-ptr +ℕ 0) (readReg (regs sf) a0)
                    ; pc = pc sf +ℕ 1 }

    step0 : step prog sf ≡ just st1
    step0 = trans (step-exec prog sf middle-store h-false
                    (subst (λ p → fetch prog p ≡ just middle-store) (sym pc-eq) fetch-mid0))
                  (execSd prog sf a0 0 s2)

    h1 : halted st1 ≡ false
    h1 = h-false

    pc1 : pc st1 ≡ mid-offset +ℕ 1
    pc1 = cong (_+ℕ 1) pc-eq

    -- State after step 1: mv a0 s1
    st2 : State
    st2 = record st1 { regs = writeReg (regs st1) a0 (readReg (regs st1) s1)
                     ; pc = pc st1 +ℕ 1 }

    step1 : step prog st1 ≡ just st2
    step1 = trans (step-exec prog st1 middle-restore h1
                    (subst (λ p → fetch prog p ≡ just middle-restore) (sym pc1) fetch-mid1))
                  (execMv prog st1 a0 s1)

    -- Star proof
    star-all : Star prog sf st2
    star-all = ⟨ h-false , step0 ⟩◅ ⟨ h1 , step1 ⟩◅ refl*

    -- Final state properties
    h2 : halted st2 ≡ false
    h2 = h-false

    pc2 : pc st2 ≡ mid-offset +ℕ 2
    pc2 = trans (cong (_+ℕ 1) pc1) (+-assoc mid-offset 1 1)

    s1-st1 : readReg (regs st1) s1 ≡ encode x
    s1-st1 = s1-eq  -- memory write doesn't change regs

    a0-st2 : readReg (regs st2) a0 ≡ encode x
    a0-st2 = trans (readReg-writeReg-same (regs st1) a0 (readReg (regs st1) s1) (λ ())) s1-st1

    s1-st2 : readReg (regs st2) s1 ≡ encode x
    s1-st2 = trans (readReg-writeReg-a0-s1 (regs st1) (readReg (regs st1) s1)) s1-st1

    sp-st1 : readReg (regs st1) sp ≡ readReg (regs sf) sp
    sp-st1 = refl  -- memory write doesn't change regs

    sp-st2 : readReg (regs st2) sp ≡ readReg (regs sf) sp
    sp-st2 = trans (readReg-writeReg-a0-sp (regs st1) (readReg (regs st1) s1)) sp-st1

    ra-st1 : readReg (regs st1) ra ≡ readReg (regs sf) ra
    ra-st1 = refl  -- memory write doesn't change regs

    ra-st2 : readReg (regs st2) ra ≡ readReg (regs sf) ra
    ra-st2 = trans (readReg-writeReg-a0-ra (regs st1) (readReg (regs st1) s1)) ra-st1

    -- s2 preservation: middle instructions don't modify s2
    s2-st1 : readReg (regs st1) s2 ≡ readReg (regs sf) s2
    s2-st1 = refl  -- memory write doesn't change regs

    s2-st2 : readReg (regs st2) s2 ≡ readReg (regs sf) s2
    s2-st2 = trans (readReg-writeReg-a0-s2 (regs st1) (readReg (regs st1) s1)) s2-st1

    -- Memory tracking - store at frame pointer (s2)
    mem-write-addr : frame-ptr +ℕ 0 ≡ frame-ptr
    mem-write-addr = +-identityʳ frame-ptr
      where open import Data.Nat.Properties using (+-identityʳ)

    mem-st1-at-plus-zero : readMem (memory st1) (frame-ptr +ℕ 0) ≡ just (encode (eval f x))
    mem-st1-at-plus-zero = trans (readMem-writeMem-same (memory sf) (frame-ptr +ℕ 0) (readReg (regs sf) a0))
                                 (cong just a0-eq)

    mem-st1 : readMem (memory st1) frame-ptr ≡ just (encode (eval f x))
    mem-st1 = subst (λ a → readMem (memory st1) a ≡ just (encode (eval f x)))
                    mem-write-addr
                    mem-st1-at-plus-zero

    mem-st2 : readMem (memory st2) frame-ptr ≡ just (encode (eval f x))
    mem-st2 = mem-st1  -- mv doesn't change memory

    -- Memory at s2+16 is preserved (write is at s2+0, not s2+16)
    s2+0≢s2+16 : (frame-ptr +ℕ 0) ≢ (frame-ptr +ℕ 16)
    s2+0≢s2+16 eq = n≢n+suc frame-ptr 15 (trans (sym (+-identityʳ frame-ptr)) eq)
      where open import Data.Nat.Properties using (+-identityʳ)

    mem-s2+16-st1 : readMem (memory st1) (frame-ptr +ℕ 16) ≡ readMem (memory sf) (frame-ptr +ℕ 16)
    mem-s2+16-st1 = readMem-writeMem-diff (memory sf) (frame-ptr +ℕ 0) (frame-ptr +ℕ 16)
                      (readReg (regs sf) a0) s2+0≢s2+16

    mem-s2+16-st2 : readMem (memory st2) (frame-ptr +ℕ 16) ≡ readMem (memory sf) (frame-ptr +ℕ 16)
    mem-s2+16-st2 = mem-s2+16-st1  -- mv doesn't change memory

    -- Memory at s2+24 is preserved (write is at s2+0, not s2+24)
    s2+0≢s2+24 : (frame-ptr +ℕ 0) ≢ (frame-ptr +ℕ 24)
    s2+0≢s2+24 eq = n≢n+suc frame-ptr 23 (trans (sym (+-identityʳ frame-ptr)) eq)
      where open import Data.Nat.Properties using (+-identityʳ)

    mem-s2+24-st1 : readMem (memory st1) (frame-ptr +ℕ 24) ≡ readMem (memory sf) (frame-ptr +ℕ 24)
    mem-s2+24-st1 = readMem-writeMem-diff (memory sf) (frame-ptr +ℕ 0) (frame-ptr +ℕ 24)
                      (readReg (regs sf) a0) s2+0≢s2+24

    mem-s2+24-st2 : readMem (memory st2) (frame-ptr +ℕ 24) ≡ readMem (memory sf) (frame-ptr +ℕ 24)
    mem-s2+24-st2 = mem-s2+24-st1  -- mv doesn't change memory

    -- Memory preservation at orig-sp and above (generic for any n)
    -- Middle phase writes at frame-ptr = s2 = orig-sp - 32
    -- So writes are disjoint from orig-sp + n for any n

    -- Proven address disjointness using middle-write-addr≢orig-sp+any lemma
    -- Key: frame-ptr = orig-sp ∸ 32 (from frame-ptr-eq), and write is at frame-ptr + 0 = frame-ptr
    write-addr-is-frame-ptr : frame-ptr +ℕ 0 ≡ frame-ptr
    write-addr-is-frame-ptr = +-identityʳ frame-ptr

    write-addr-is-orig-sp-minus-32 : frame-ptr +ℕ 0 ≡ orig-sp ∸ 32
    write-addr-is-orig-sp-minus-32 = trans write-addr-is-frame-ptr frame-ptr-eq

    mem-preserved-generic : ∀ n → readMem (memory st2) (orig-sp +ℕ n) ≡ readMem (memory sf) (orig-sp +ℕ n)
    mem-preserved-generic n =
      let
        write-addr≢ : (frame-ptr +ℕ 0) ≢ (orig-sp +ℕ n)
        write-addr≢ eq = middle-write-addr≢orig-sp+any orig-sp n sp-bound
                           (trans (sym write-addr-is-orig-sp-minus-32) eq)
      in readMem-writeMem-diff (memory sf) (frame-ptr +ℕ 0) (orig-sp +ℕ n)
           (readReg (regs sf) a0) write-addr≢

------------------------------------------------------------------------
-- Phase 5: Final - trace 5 instructions (frame pointer approach)
--   1. sd a0 8(s2)     (store g result at frame+8)
--   2. mv a0 s2        (return pair pointer = frame)
--   3. ld s1 16(s2)    (restore original s1 from frame+16)
--   4. ld t0 24(s2)    (load original s2 from frame+24)
--   5. mv s2 t0        (restore original s2)
------------------------------------------------------------------------

-- | Final phase: store g result, return pair pointer, restore s1 and s2
-- Entry: pc = offset + 7 + len-f + len-g, a0 = encode (eval g x)
--        s2 = frame pointer (orig-sp ∸ 32)
--        memory[s2] = encode (eval f x) (stored during middle)
--        memory[s2+16] = orig-s1 (saved during setup)
--        memory[s2+24] = orig-s2 (saved during setup)
--        32 ≤ orig-sp
-- Exit: pc = offset + 12 + len-f + len-g, a0 = encode (eval f x, eval g x)
--       s1 = orig-s1, s2 = orig-s2
pair-final-star : ∀ {i A B C} (f : IR i C A) (g : IR i C B)
                  (prefix suffix : Program) (x : ⟦ C ⟧) (orig-s1 orig-s2 : Word) (orig-sp : ℕ) (sg : State) →
  let ctx = make-pair-context f g prefix suffix
      open PairContext ctx
      final-offset = length prefix +ℕ 7 +ℕ len-f +ℕ len-g
      frame-ptr = readReg (regs sg) s2  -- frame pointer
  in
  halted sg ≡ false →
  pc sg ≡ final-offset →
  readReg (regs sg) a0 ≡ encode (eval g x) →          -- g result in a0
  readMem (memory sg) frame-ptr ≡ just (encode (eval f x)) →  -- f result at frame
  -- Note: g result will be stored at frame+8 by first instruction (sd a0, 8(s2))
  readMem (memory sg) (frame-ptr +ℕ 16) ≡ just orig-s1 →  -- saved s1
  readMem (memory sg) (frame-ptr +ℕ 24) ≡ just orig-s2 →  -- saved s2
  32 ≤ orig-sp →  -- Stack bound precondition
  readReg (regs sg) s2 ≡ orig-sp ∸ 32 →  -- s2 = frame pointer
  ∃[ s' ] PairFinalResult prog sg s' final-offset
            (encode (eval f x , eval g x)) orig-s1 orig-s2 orig-sp
pair-final-star {i} {A} {B} {C} f g prefix suffix x orig-s1 orig-s2 orig-sp sg h-false pc-eq a0-eq mem-f mem-s1 mem-s2 sp-bound frame-ptr-eq =
  st5 , record
    { star-final = star-all
    ; h-final = h5
    ; pc-final = pc5
    ; a0-final = a0-st5
    ; s1-final = s1-st5
    ; s2-final = s2-st5
    ; ra-final = ra-st5
    ; sp-final = sp-st5
    ; mem-preserved-final = mem-preserved-generic
    }
  where
    ctx = make-pair-context f g prefix suffix
    open PairContext ctx
    final-offset = length prefix +ℕ 7 +ℕ len-f +ℕ len-g
    frame-ptr = readReg (regs sg) s2

    -- Program decomposition for final phase
    -- prog = prefix-g ++ code-g ++ suffix-g = prefix-final ++ suffix-g
    -- prefix-final = prefix-g ++ code-g
    -- suffix-g = final-store ∷ final-result ∷ final-restore-s1 ∷ final-load-s2 ∷ final-restore-s2 ∷ suffix

    prog-at-final : prog ≡ prefix-final ++ suffix-g
    prog-at-final = trans prog-eq-g (sym (++-assoc prefix-g code-g suffix-g))

    fetch0 : fetch prog final-offset ≡ just final-store
    fetch0 = subst₂ (λ p n → fetch p n ≡ just final-store) (sym prog-at-final) len-prefix-final
               (fetch-at-prefix-end prefix-final final-store _)

    prog-at-1 : prog ≡ (prefix-final ++ final-store ∷ []) ++ final-result ∷ final-restore-s1 ∷ final-load-s2 ∷ final-restore-s2 ∷ suffix
    prog-at-1 = trans prog-at-final (sym (++-assoc prefix-final (final-store ∷ []) _))

    len-prefix-final-1 : length (prefix-final ++ final-store ∷ []) ≡ final-offset +ℕ 1
    len-prefix-final-1 = trans (List-length-++ prefix-final) (cong (_+ℕ 1) len-prefix-final)

    fetch1 : fetch prog (final-offset +ℕ 1) ≡ just final-result
    fetch1 = subst₂ (λ p n → fetch p n ≡ just final-result) (sym prog-at-1) len-prefix-final-1
               (fetch-at-prefix-end (prefix-final ++ final-store ∷ []) final-result _)

    prog-at-2 : prog ≡ (prefix-final ++ final-store ∷ final-result ∷ []) ++ final-restore-s1 ∷ final-load-s2 ∷ final-restore-s2 ∷ suffix
    prog-at-2 = trans prog-at-final (sym (++-assoc prefix-final (final-store ∷ final-result ∷ []) _))

    len-prefix-final-2 : length (prefix-final ++ final-store ∷ final-result ∷ []) ≡ final-offset +ℕ 2
    len-prefix-final-2 = trans (List-length-++ prefix-final) (cong (_+ℕ 2) len-prefix-final)

    fetch2 : fetch prog (final-offset +ℕ 2) ≡ just final-restore-s1
    fetch2 = subst₂ (λ p n → fetch p n ≡ just final-restore-s1) (sym prog-at-2) len-prefix-final-2
               (fetch-at-prefix-end (prefix-final ++ final-store ∷ final-result ∷ []) final-restore-s1 _)

    prog-at-3 : prog ≡ (prefix-final ++ final-store ∷ final-result ∷ final-restore-s1 ∷ []) ++ final-load-s2 ∷ final-restore-s2 ∷ suffix
    prog-at-3 = trans prog-at-final (sym (++-assoc prefix-final (final-store ∷ final-result ∷ final-restore-s1 ∷ []) _))

    len-prefix-final-3 : length (prefix-final ++ final-store ∷ final-result ∷ final-restore-s1 ∷ []) ≡ final-offset +ℕ 3
    len-prefix-final-3 = trans (List-length-++ prefix-final) (cong (_+ℕ 3) len-prefix-final)

    fetch3 : fetch prog (final-offset +ℕ 3) ≡ just final-load-s2
    fetch3 = subst₂ (λ p n → fetch p n ≡ just final-load-s2) (sym prog-at-3) len-prefix-final-3
               (fetch-at-prefix-end (prefix-final ++ final-store ∷ final-result ∷ final-restore-s1 ∷ []) final-load-s2 _)

    prog-at-4 : prog ≡ (prefix-final ++ final-store ∷ final-result ∷ final-restore-s1 ∷ final-load-s2 ∷ []) ++ final-restore-s2 ∷ suffix
    prog-at-4 = trans prog-at-final (sym (++-assoc prefix-final (final-store ∷ final-result ∷ final-restore-s1 ∷ final-load-s2 ∷ []) _))

    len-prefix-final-4 : length (prefix-final ++ final-store ∷ final-result ∷ final-restore-s1 ∷ final-load-s2 ∷ []) ≡ final-offset +ℕ 4
    len-prefix-final-4 = trans (List-length-++ prefix-final) (cong (_+ℕ 4) len-prefix-final)

    fetch4 : fetch prog (final-offset +ℕ 4) ≡ just final-restore-s2
    fetch4 = subst₂ (λ p n → fetch p n ≡ just final-restore-s2) (sym prog-at-4) len-prefix-final-4
               (fetch-at-prefix-end (prefix-final ++ final-store ∷ final-result ∷ final-restore-s1 ∷ final-load-s2 ∷ []) final-restore-s2 _)

    -- Step 0: sd a0 8(s2) - store g result at frame+8
    st1 : State
    st1 = record sg { memory = writeMem (memory sg) (frame-ptr +ℕ 8) (readReg (regs sg) a0)
                    ; pc = pc sg +ℕ 1 }

    step0 : step prog sg ≡ just st1
    step0 = trans (step-exec prog sg final-store h-false
                    (subst (λ p → fetch prog p ≡ just final-store) (sym pc-eq) fetch0))
                  (execSd prog sg a0 8 s2)

    h1 : halted st1 ≡ false
    h1 = h-false

    pc1 : pc st1 ≡ final-offset +ℕ 1
    pc1 = cong (_+ℕ 1) pc-eq

    -- Step 1: mv a0 s2 - return pair pointer
    st2 : State
    st2 = record st1 { regs = writeReg (regs st1) a0 (readReg (regs st1) s2)
                     ; pc = pc st1 +ℕ 1 }

    step1 : step prog st1 ≡ just st2
    step1 = trans (step-exec prog st1 final-result h1
                    (subst (λ p → fetch prog p ≡ just final-result) (sym pc1) fetch1))
                  (execMv prog st1 a0 s2)

    h2 : halted st2 ≡ false
    h2 = h-false

    pc2 : pc st2 ≡ final-offset +ℕ 2
    pc2 = trans (cong (_+ℕ 1) pc1) (+-assoc final-offset 1 1)

    -- s2 is preserved through sd and mv a0 s2
    s2-st1 : readReg (regs st1) s2 ≡ frame-ptr
    s2-st1 = refl  -- sd doesn't change regs

    s2-st2 : readReg (regs st2) s2 ≡ frame-ptr
    s2-st2 = readReg-writeReg-a0-s2 (regs st1) (readReg (regs st1) s2)

    -- Memory at s2+16 contains orig-s1 (preserved through sd at s2+8)
    8≢16 : (frame-ptr +ℕ 8) ≢ (frame-ptr +ℕ 16)
    8≢16 = subst (λ k → frame-ptr +ℕ 8 ≢ k) (+-assoc frame-ptr 8 8) (n≢n+suc (frame-ptr +ℕ 8) 7)

    mem-s1-st1 : readMem (memory st1) (frame-ptr +ℕ 16) ≡ just orig-s1
    mem-s1-st1 = trans (readMem-writeMem-diff (memory sg) (frame-ptr +ℕ 8) (frame-ptr +ℕ 16)
                          (readReg (regs sg) a0) 8≢16)
                       mem-s1

    -- Step 2: ld s1 16(s2) - restore s1
    st3 : State
    st3 = record st2 { regs = writeReg (regs st2) s1 orig-s1
                     ; pc = pc st2 +ℕ 1 }

    -- Need to show the load reads orig-s1
    s2-st2-eq : readReg (regs st2) s2 ≡ frame-ptr
    s2-st2-eq = s2-st2

    mem-s1-st2 : readMem (memory st2) (readReg (regs st2) s2 +ℕ 16) ≡ just orig-s1
    mem-s1-st2 = subst (λ addr → readMem (memory st2) (addr +ℕ 16) ≡ just orig-s1) (sym s2-st2-eq) mem-s1-st1

    step2 : step prog st2 ≡ just st3
    step2 = trans (step-exec prog st2 final-restore-s1 h2
                    (subst (λ p → fetch prog p ≡ just final-restore-s1) (sym pc2) fetch2))
                  (execLd prog st2 s1 16 s2 orig-s1 mem-s1-st2)

    h3 : halted st3 ≡ false
    h3 = h-false

    pc3 : pc st3 ≡ final-offset +ℕ 3
    pc3 = trans (cong (_+ℕ 1) pc2) (+-assoc final-offset 2 1)

    -- Memory at s2+24 contains orig-s2 (preserved through sd at s2+8)
    8≢24 : (frame-ptr +ℕ 8) ≢ (frame-ptr +ℕ 24)
    8≢24 = subst (λ k → frame-ptr +ℕ 8 ≢ k) (+-assoc frame-ptr 8 16) (n≢n+suc (frame-ptr +ℕ 8) 15)

    mem-s2-st1 : readMem (memory st1) (frame-ptr +ℕ 24) ≡ just orig-s2
    mem-s2-st1 = trans (readMem-writeMem-diff (memory sg) (frame-ptr +ℕ 8) (frame-ptr +ℕ 24)
                          (readReg (regs sg) a0) 8≢24)
                       mem-s2

    -- s2 is preserved through ld s1
    s2-st3 : readReg (regs st3) s2 ≡ frame-ptr
    s2-st3 = trans (readReg-writeReg-s1-s2 (regs st2) orig-s1) s2-st2

    mem-s2-st3 : readMem (memory st3) (readReg (regs st3) s2 +ℕ 24) ≡ just orig-s2
    mem-s2-st3 = subst (λ addr → readMem (memory st3) (addr +ℕ 24) ≡ just orig-s2) (sym s2-st3) mem-s2-st1

    -- Step 3: ld t0 24(s2) - load orig-s2 into t0
    st4 : State
    st4 = record st3 { regs = writeReg (regs st3) t0 orig-s2
                     ; pc = pc st3 +ℕ 1 }

    step3 : step prog st3 ≡ just st4
    step3 = trans (step-exec prog st3 final-load-s2 h3
                    (subst (λ p → fetch prog p ≡ just final-load-s2) (sym pc3) fetch3))
                  (execLd prog st3 t0 24 s2 orig-s2 mem-s2-st3)

    h4 : halted st4 ≡ false
    h4 = h-false

    pc4 : pc st4 ≡ final-offset +ℕ 4
    pc4 = trans (cong (_+ℕ 1) pc3) (+-assoc final-offset 3 1)

    -- Step 4: mv s2 t0 - restore s2
    st5 : State
    st5 = record st4 { regs = writeReg (regs st4) s2 (readReg (regs st4) t0)
                     ; pc = pc st4 +ℕ 1 }

    t0-st4 : readReg (regs st4) t0 ≡ orig-s2
    t0-st4 = readReg-writeReg-same (regs st3) t0 orig-s2 (λ ())

    step4 : step prog st4 ≡ just st5
    step4 = trans (step-exec prog st4 final-restore-s2 h4
                    (subst (λ p → fetch prog p ≡ just final-restore-s2) (sym pc4) fetch4))
                  (execMv prog st4 s2 t0)

    -- Star proof
    star-all : Star prog sg st5
    star-all = ⟨ h-false , step0 ⟩◅ ⟨ h1 , step1 ⟩◅ ⟨ h2 , step2 ⟩◅ ⟨ h3 , step3 ⟩◅ ⟨ h4 , step4 ⟩◅ refl*

    -- Final state properties
    h5 : halted st5 ≡ false
    h5 = h-false

    pc5 : pc st5 ≡ final-offset +ℕ 5
    pc5 = trans (cong (_+ℕ 1) pc4) (+-assoc final-offset 4 1)

    -- a0 = encode (eval f x, eval g x) using encode-pair-construct
    -- After mv a0 s2, a0 = frame-ptr
    -- frame-ptr is a pointer to the pair in memory:
    --   memory[frame-ptr] = encode (eval f x)
    --   memory[frame-ptr + 8] = encode (eval g x)
    -- The encode-pair-construct axiom says this gives encode (eval f x, eval g x)
    a0-st2-val : readReg (regs st2) a0 ≡ frame-ptr
    a0-st2-val = trans (readReg-writeReg-same (regs st1) a0 (readReg (regs st1) s2) (λ ())) s2-st1

    -- a0 is preserved through ld s1, ld t0, mv s2 t0
    a0-st3 : readReg (regs st3) a0 ≡ frame-ptr
    a0-st3 = trans (readReg-writeReg-s1-a0 (regs st2) orig-s1) a0-st2-val

    a0-st4 : readReg (regs st4) a0 ≡ frame-ptr
    a0-st4 = trans (readReg-writeReg-t0-a0 (regs st3) orig-s2) a0-st3

    a0-st5-is-frame : readReg (regs st5) a0 ≡ frame-ptr
    a0-st5-is-frame = trans (readReg-writeReg-s2-a0 (regs st4) (readReg (regs st4) t0)) a0-st4

    -- Memory at frame contains f result (preserved through sd at frame+8)
    8≢0 : (frame-ptr +ℕ 8) ≢ frame-ptr
    8≢0 eq = n≢n+suc frame-ptr 7 (sym eq)

    mem-f-st1 : readMem (memory st1) frame-ptr ≡ just (encode (eval f x))
    mem-f-st1 = trans (readMem-writeMem-diff (memory sg) (frame-ptr +ℕ 8) frame-ptr
                         (readReg (regs sg) a0) 8≢0)
                      mem-f

    -- Memory at frame+8 now contains g result
    mem-g-st1 : readMem (memory st1) (frame-ptr +ℕ 8) ≡ just (encode (eval g x))
    mem-g-st1 = trans (readMem-writeMem-same (memory sg) (frame-ptr +ℕ 8) (readReg (regs sg) a0))
                      (cong just a0-eq)

    -- Use encode-pair-construct: if mem[ptr] = encode a and mem[ptr+8] = encode b
    -- then ptr encodes the pair (a, b)
    a0-st5 : readReg (regs st5) a0 ≡ encode (eval f x , eval g x)
    a0-st5 = trans a0-st5-is-frame (encode-pair-construct (eval f x) (eval g x) frame-ptr (memory st5) mem-f-st1 mem-g-st1)

    -- s1 = orig-s1 (from ld s1 16(s2), preserved through ld t0 and mv s2 t0)
    s1-st3 : readReg (regs st3) s1 ≡ orig-s1
    s1-st3 = readReg-writeReg-same (regs st2) s1 orig-s1 (λ ())

    s1-st4 : readReg (regs st4) s1 ≡ orig-s1
    s1-st4 = trans (readReg-writeReg-t0-s1 (regs st3) orig-s2) s1-st3

    s1-st5 : readReg (regs st5) s1 ≡ orig-s1
    s1-st5 = trans (readReg-writeReg-s2-s1 (regs st4) (readReg (regs st4) t0)) s1-st4

    -- s2 = orig-s2 (from mv s2 t0)
    s2-st5 : readReg (regs st5) s2 ≡ orig-s2
    s2-st5 = trans (readReg-writeReg-same (regs st4) s2 (readReg (regs st4) t0) (λ ())) t0-st4

    -- ra preserved
    ra-st1 : readReg (regs st1) ra ≡ readReg (regs sg) ra
    ra-st1 = refl  -- sd doesn't change regs

    ra-st2 : readReg (regs st2) ra ≡ readReg (regs sg) ra
    ra-st2 = trans (readReg-writeReg-a0-ra (regs st1) (readReg (regs st1) s2)) ra-st1

    ra-st3 : readReg (regs st3) ra ≡ readReg (regs sg) ra
    ra-st3 = trans (readReg-writeReg-s1-ra (regs st2) orig-s1) ra-st2

    ra-st4 : readReg (regs st4) ra ≡ readReg (regs sg) ra
    ra-st4 = trans (readReg-writeReg-t0-ra (regs st3) orig-s2) ra-st3

    ra-st5 : readReg (regs st5) ra ≡ readReg (regs sg) ra
    ra-st5 = trans (readReg-writeReg-s2-ra (regs st4) (readReg (regs st4) t0)) ra-st4

    -- sp preserved
    sp-st1 : readReg (regs st1) sp ≡ readReg (regs sg) sp
    sp-st1 = refl  -- sd doesn't change regs

    sp-st2 : readReg (regs st2) sp ≡ readReg (regs sg) sp
    sp-st2 = trans (readReg-writeReg-a0-sp (regs st1) (readReg (regs st1) s2)) sp-st1

    sp-st3 : readReg (regs st3) sp ≡ readReg (regs sg) sp
    sp-st3 = trans (readReg-writeReg-s1-sp (regs st2) orig-s1) sp-st2

    sp-st4 : readReg (regs st4) sp ≡ readReg (regs sg) sp
    sp-st4 = trans (readReg-writeReg-t0-sp (regs st3) orig-s2) sp-st3

    sp-st5 : readReg (regs st5) sp ≡ readReg (regs sg) sp
    sp-st5 = trans (readReg-writeReg-s2-sp (regs st4) (readReg (regs st4) t0)) sp-st4

    -- Memory preservation at orig-sp and above (generic for any n)
    -- The only write is at frame-ptr + 8 = (orig-sp - 32) + 8, which is < orig-sp
    -- frame-ptr = orig-sp - 32 (from frame-ptr-eq)
    frame-ptr-is-orig-sp-32 : frame-ptr ≡ orig-sp ∸ 32
    frame-ptr-is-orig-sp-32 = frame-ptr-eq

    mem-preserved-generic : ∀ n → readMem (memory st5) (orig-sp +ℕ n) ≡ readMem (memory sg) (orig-sp +ℕ n)
    mem-preserved-generic n =
      let
        write-addr≢ : (frame-ptr +ℕ 8) ≢ (orig-sp +ℕ n)
        write-addr≢ = subst (λ x → (x +ℕ 8) ≢ (orig-sp +ℕ n)) (sym frame-ptr-is-orig-sp-32)
                        (final-write-addr≢orig-sp+any orig-sp n sp-bound)

        mem-at-st1 : readMem (memory st1) (orig-sp +ℕ n) ≡ readMem (memory sg) (orig-sp +ℕ n)
        mem-at-st1 = readMem-writeMem-diff (memory sg) (frame-ptr +ℕ 8) (orig-sp +ℕ n)
                       (readReg (regs sg) a0) write-addr≢
      in mem-at-st1  -- st2-st5 don't modify memory (loads and register moves)

------------------------------------------------------------------------
-- Helper for assembling pair result from f and g results
------------------------------------------------------------------------

-- This will be used by MutualIR to combine the recursive results
