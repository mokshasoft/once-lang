------------------------------------------------------------------------
-- Once.Backend.RiscV64.Correct.IR.Pair
--
-- Helper records and functions for pair proofs.
-- Extracts non-recursive parts to reduce mutual block compilation time.
-- The recursive calls stay in MutualIR.agda.
--
-- Pair structure for RISC-V:
--   Phase 1: Setup     (3 instr) - addi sp sp -24; sd s1 16(sp); mv s1 a0
--   Phase 2: Execute f (recursive)
--   Phase 3: Middle    (2 instr) - sd a0 0(sp); mv a0 s1
--   Phase 4: Execute g (recursive)
--   Phase 5: Final     (3 instr) - sd a0 8(sp); mv a0 sp; ld s1 16(sp)
--
-- Total: 8 + len-f + len-g instructions
-- Note: s1 is saved/restored to preserve it as a callee-saved register
------------------------------------------------------------------------

{-# OPTIONS --sized-types #-}

module Once.Backend.RiscV64.Correct.IR.Pair where

open import Size

open import Once.Type
open import Once.IR
open import Once.Semantics

open import Once.Backend.RiscV64.Syntax
open import Once.Backend.RiscV64.Semantics
open State
open import Once.Backend.RiscV64.CodeGen

open import Once.Postulates using (encode; encode-pair-construct)
open import Once.Backend.RiscV64.Correct.CompileLength
open import Once.Backend.RiscV64.Correct.Foundation
open import Once.Backend.RiscV64.Correct.Star
  using (Star; refl*; step*; ⟨_,_⟩◅_; star-trans)
open import Once.Backend.RiscV64.Correct.StarBase
  using (IRStarResult;
         ir-star; ir-halted; ir-pc; ir-a0; ir-s1; ir-s2; ir-ra; ir-sp;
         ir-mem-sp; ir-mem-sp+8; ir-mem-sp+16)

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
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; subst; subst₂; cong)
open import Relation.Binary.PropositionalEquality.Properties using (module ≡-Reasoning)
open ≡-Reasoning

------------------------------------------------------------------------
-- Address Disjointness Lemmas
--
-- Key insight for pair memory preservation:
-- Setup allocates 24 bytes by doing sp' = sp - 24.
-- Writes occur at sp' + k for k ∈ {0, 8, 16} = orig-sp - {24, 16, 8}.
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

-- Helper: (sp ∸ 24) + 16 ≡ sp ∸ 8 when sp ≥ 24
-- But actually we need: (sp ∸ 24) + 16 < sp when sp ≥ 24
-- Key: sp - 24 + 16 = sp - 8, and sp - 8 < sp (for sp > 8)

-- When sp ≥ 24, we have new-sp = sp - 24, and write-addr = new-sp + 16 = sp - 8.
-- We need: sp - 8 ≢ sp, sp + 8, sp + 16, sp + 24
-- All follow from sp - 8 < sp (when sp ≥ 8).

-- Lemma: n ∸ k + k ≡ n when k ≤ n (re-exports from Data.Nat.Properties as m∸n+n≡m)

-- Key insight: when 24 ≤ n, any address n - k (for k ≥ 8) is strictly less than n.
-- We only need the inequality, not the exact arithmetic.

-- Helper: (n ∸ 24) + 16 < (n ∸ 24) + 24 = n when n ≥ 24
-- So (n ∸ 24) + 16 < n, hence ≢ n + k for any k ≥ 0
setup-addr-lt-orig : ∀ n → 24 ≤ n → suc ((n ∸ 24) +ℕ 16) ≤ n
setup-addr-lt-orig n n≥24 =
  let restored : (n ∸ 24) +ℕ 24 ≡ n
      restored = m∸n+n≡m n≥24
      -- suc ((n ∸ 24) + 16) ≤ (n ∸ 24) + 24
      -- i.e., (n ∸ 24) + 17 ≤ (n ∸ 24) + 24
      step1 : suc ((n ∸ 24) +ℕ 16) ≤ (n ∸ 24) +ℕ 24
      step1 = lemma (n ∸ 24)
  in subst (λ x → suc ((n ∸ 24) +ℕ 16) ≤ x) restored step1
  where
    -- suc (m + 16) ≤ m + 24, i.e., m + 17 ≤ m + 24
    lemma : ∀ m → suc (m +ℕ 16) ≤ (m +ℕ 24)
    lemma zero = s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))))))))))))
    lemma (suc m) = s≤s (lemma m)

-- Main lemmas for setup phase: write at new-sp + 16 ≢ orig-sp + k
setup-write-addr≢orig-sp : ∀ (orig-sp : ℕ) → 24 ≤ orig-sp →
  (orig-sp ∸ 24) +ℕ 16 ≢ orig-sp
setup-write-addr≢orig-sp n n≥24 = <-implies-≢ (setup-addr-lt-orig n n≥24)

setup-write-addr≢orig-sp+8 : ∀ (orig-sp : ℕ) → 24 ≤ orig-sp →
  (orig-sp ∸ 24) +ℕ 16 ≢ orig-sp +ℕ 8
setup-write-addr≢orig-sp+8 n n≥24 =
  <-implies-≢ (≤-trans (setup-addr-lt-orig n n≥24) (m≤m+n n 8))

setup-write-addr≢orig-sp+16 : ∀ (orig-sp : ℕ) → 24 ≤ orig-sp →
  (orig-sp ∸ 24) +ℕ 16 ≢ orig-sp +ℕ 16
setup-write-addr≢orig-sp+16 n n≥24 =
  <-implies-≢ (≤-trans (setup-addr-lt-orig n n≥24) (m≤m+n n 16))

setup-write-addr≢orig-sp+24 : ∀ (orig-sp : ℕ) → 24 ≤ orig-sp →
  (orig-sp ∸ 24) +ℕ 16 ≢ orig-sp +ℕ 24
setup-write-addr≢orig-sp+24 n n≥24 =
  <-implies-≢ (≤-trans (setup-addr-lt-orig n n≥24) (m≤m+n n 24))

-- Middle phase lemmas: write at (orig-sp ∸ 24) + 0 = orig-sp - 24
-- When n ≥ 24, n - 24 < n, so n - 24 ≢ n + k for any k ≥ 0

-- Lemma: suc (n ∸ 24) ≤ n when 24 ≤ n
-- Proof: suc (n ∸ 24) ≤ (n ∸ 24) + 24 = n
sp-minus-24-lt-sp : ∀ n → 24 ≤ n → suc (n ∸ 24) ≤ n
sp-minus-24-lt-sp n n≥24 =
  let restored : (n ∸ 24) +ℕ 24 ≡ n
      restored = m∸n+n≡m n≥24
      -- suc (n ∸ 24) ≤ (n ∸ 24) + 24, i.e., (n ∸ 24) + 1 ≤ (n ∸ 24) + 24
      step1 : suc (n ∸ 24) ≤ (n ∸ 24) +ℕ 24
      step1 = lemma (n ∸ 24)
  in subst (λ x → suc (n ∸ 24) ≤ x) restored step1
  where
    -- suc m ≤ m + 24
    lemma : ∀ m → suc m ≤ (m +ℕ 24)
    lemma zero = s≤s z≤n
    lemma (suc m) = s≤s (lemma m)

middle-write-addr≢orig-sp : ∀ (orig-sp : ℕ) → 24 ≤ orig-sp →
  orig-sp ∸ 24 ≢ orig-sp
middle-write-addr≢orig-sp n n≥24 = <-implies-≢ (sp-minus-24-lt-sp n n≥24)

middle-write-addr≢orig-sp+8 : ∀ (orig-sp : ℕ) → 24 ≤ orig-sp →
  orig-sp ∸ 24 ≢ orig-sp +ℕ 8
middle-write-addr≢orig-sp+8 n n≥24 eq =
  <-implies-≢ (≤-trans (sp-minus-24-lt-sp n n≥24) (m≤m+n n 8)) eq

middle-write-addr≢orig-sp+16 : ∀ (orig-sp : ℕ) → 24 ≤ orig-sp →
  orig-sp ∸ 24 ≢ orig-sp +ℕ 16
middle-write-addr≢orig-sp+16 n n≥24 eq =
  <-implies-≢ (≤-trans (sp-minus-24-lt-sp n n≥24) (m≤m+n n 16)) eq

middle-write-addr≢orig-sp+24 : ∀ (orig-sp : ℕ) → 24 ≤ orig-sp →
  orig-sp ∸ 24 ≢ orig-sp +ℕ 24
middle-write-addr≢orig-sp+24 n n≥24 eq =
  <-implies-≢ (≤-trans (sp-minus-24-lt-sp n n≥24) (m≤m+n n 24)) eq

-- Final phase lemmas: write at (orig-sp ∸ 24) + 8 ≢ orig-sp + k
-- When n ≥ 24, (n ∸ 24) + 8 < n, so it's ≢ n + k for any k ≥ 0

-- Helper: (n ∸ 24) + 8 < (n ∸ 24) + 24 = n when n ≥ 24
final-addr-lt-orig : ∀ n → 24 ≤ n → suc ((n ∸ 24) +ℕ 8) ≤ n
final-addr-lt-orig n n≥24 =
  let restored : (n ∸ 24) +ℕ 24 ≡ n
      restored = m∸n+n≡m n≥24
      -- suc ((n ∸ 24) + 8) ≤ (n ∸ 24) + 24
      step1 : suc ((n ∸ 24) +ℕ 8) ≤ (n ∸ 24) +ℕ 24
      step1 = lemma (n ∸ 24)
  in subst (λ x → suc ((n ∸ 24) +ℕ 8) ≤ x) restored step1
  where
    -- suc (m + 8) ≤ m + 24, i.e., m + 9 ≤ m + 24
    lemma : ∀ m → suc (m +ℕ 8) ≤ (m +ℕ 24)
    lemma zero = s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))))
    lemma (suc m) = s≤s (lemma m)

final-write-addr≢orig-sp : ∀ (orig-sp : ℕ) → 24 ≤ orig-sp →
  (orig-sp ∸ 24) +ℕ 8 ≢ orig-sp
final-write-addr≢orig-sp n n≥24 = <-implies-≢ (final-addr-lt-orig n n≥24)

final-write-addr≢orig-sp+8 : ∀ (orig-sp : ℕ) → 24 ≤ orig-sp →
  (orig-sp ∸ 24) +ℕ 8 ≢ orig-sp +ℕ 8
final-write-addr≢orig-sp+8 n n≥24 =
  <-implies-≢ (≤-trans (final-addr-lt-orig n n≥24) (m≤m+n n 8))

final-write-addr≢orig-sp+16 : ∀ (orig-sp : ℕ) → 24 ≤ orig-sp →
  (orig-sp ∸ 24) +ℕ 8 ≢ orig-sp +ℕ 16
final-write-addr≢orig-sp+16 n n≥24 =
  <-implies-≢ (≤-trans (final-addr-lt-orig n n≥24) (m≤m+n n 16))

final-write-addr≢orig-sp+24 : ∀ (orig-sp : ℕ) → 24 ≤ orig-sp →
  (orig-sp ∸ 24) +ℕ 8 ≢ orig-sp +ℕ 24
final-write-addr≢orig-sp+24 n n≥24 =
  <-implies-≢ (≤-trans (final-addr-lt-orig n n≥24) (m≤m+n n 24))

------------------------------------------------------------------------
-- Pair Context: computed values that don't depend on execution
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

    -- Setup instructions (3)
    setup-alloc : Instr      -- addi sp sp -24
    setup-save-s1 : Instr    -- sd s1 16(sp)
    setup-copy : Instr       -- mv s1 a0

    -- Middle instructions (2)
    middle-store : Instr   -- sd a0 0(sp)
    middle-restore : Instr -- mv a0 s1

    -- Final instructions (3)
    final-store : Instr      -- sd a0 8(sp)
    final-result : Instr     -- mv a0 sp
    final-restore-s1 : Instr -- ld s1 16(sp)

    -- Derived prefixes/suffixes
    prefix-f : Program     -- prefix ++ setup (3 instructions)
    suffix-f : Program     -- middle ++ code-g ++ final ++ suffix
    prefix-g : Program     -- prefix-f ++ code-f ++ middle
    suffix-g : Program     -- final ++ suffix (3 instructions)
    prefix-mid : Program   -- prefix-f ++ code-f
    prefix-final : Program -- prefix-g ++ code-g

    -- Length equalities (updated for 3-instr setup and final)
    len-prefix-f : length prefix-f ≡ length prefix +ℕ 3
    len-prefix-g : length prefix-g ≡ length prefix +ℕ 5 +ℕ len-f
    len-prefix-mid : length prefix-mid ≡ length prefix +ℕ 3 +ℕ len-f
    len-prefix-final : length prefix-final ≡ length prefix +ℕ 5 +ℕ len-f +ℕ len-g

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
  ; setup-save-s1 = setup-save-s1
  ; setup-copy = setup-copy
  ; middle-store = middle-store
  ; middle-restore = middle-restore
  ; final-store = final-store
  ; final-result = final-result
  ; final-restore-s1 = final-restore-s1
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

    -- Setup instructions (3)
    setup-alloc = addi sp sp neg24
    setup-save-s1 = sd s1 (+ 16) sp
    setup-copy = mv s1 a0

    -- Middle instructions (2)
    middle-store = sd a0 (+ 0) sp
    middle-restore = mv a0 s1

    -- Final instructions (3)
    final-store = sd a0 (+ 8) sp
    final-result = mv a0 sp
    final-restore-s1 = ld s1 (+ 16) sp

    -- Final instruction sequence
    final-instrs = final-store ∷ final-result ∷ final-restore-s1 ∷ []

    -- Derived programs (setup now has 3 instructions)
    prefix-f : Program
    prefix-f = prefix ++ setup-alloc ∷ setup-save-s1 ∷ setup-copy ∷ []

    suffix-f : Program
    suffix-f = middle-store ∷ middle-restore ∷ code-g ++ final-store ∷ final-result ∷ final-restore-s1 ∷ suffix

    prefix-mid : Program
    prefix-mid = prefix-f ++ code-f

    prefix-g : Program
    prefix-g = (prefix-f ++ code-f) ++ middle-store ∷ middle-restore ∷ []

    suffix-g : Program
    suffix-g = final-store ∷ final-result ∷ final-restore-s1 ∷ suffix

    prefix-final : Program
    prefix-final = prefix-g ++ code-g

    -- Length equalities (updated for 3-instruction setup)
    len-prefix-f : length prefix-f ≡ length prefix +ℕ 3
    len-prefix-f = List-length-++ prefix

    len-prefix-mid : length prefix-mid ≡ length prefix +ℕ 3 +ℕ len-f
    len-prefix-mid = begin
      length prefix-mid
        ≡⟨ List-length-++ prefix-f ⟩
      length prefix-f +ℕ length code-f
        ≡⟨ cong (_+ℕ length code-f) len-prefix-f ⟩
      (length prefix +ℕ 3) +ℕ length code-f
        ≡⟨ cong ((length prefix +ℕ 3) +ℕ_) (compile-length-correct f) ⟩
      (length prefix +ℕ 3) +ℕ len-f
        ∎

    len-prefix-g : length prefix-g ≡ length prefix +ℕ 5 +ℕ len-f
    len-prefix-g = begin
      length prefix-g
        ≡⟨ List-length-++ (prefix-f ++ code-f) ⟩
      length (prefix-f ++ code-f) +ℕ 2
        ≡⟨ cong (_+ℕ 2) len-prefix-mid ⟩
      (length prefix +ℕ 3 +ℕ len-f) +ℕ 2
        ≡⟨ +-assoc (length prefix +ℕ 3) len-f 2 ⟩
      (length prefix +ℕ 3) +ℕ (len-f +ℕ 2)
        ≡⟨ +-assoc (length prefix) 3 (len-f +ℕ 2) ⟩
      length prefix +ℕ (3 +ℕ (len-f +ℕ 2))
        ≡⟨ cong (length prefix +ℕ_) (sym (+-assoc 3 len-f 2)) ⟩
      length prefix +ℕ ((3 +ℕ len-f) +ℕ 2)
        ≡⟨ cong (λ x → length prefix +ℕ (x +ℕ 2)) (+-comm 3 len-f) ⟩
      length prefix +ℕ ((len-f +ℕ 3) +ℕ 2)
        ≡⟨ cong (length prefix +ℕ_) (+-assoc len-f 3 2) ⟩
      length prefix +ℕ (len-f +ℕ 5)
        ≡⟨ sym (+-assoc (length prefix) len-f 5) ⟩
      (length prefix +ℕ len-f) +ℕ 5
        ≡⟨ cong (_+ℕ 5) (+-comm (length prefix) len-f) ⟩
      (len-f +ℕ length prefix) +ℕ 5
        ≡⟨ +-assoc len-f (length prefix) 5 ⟩
      len-f +ℕ (length prefix +ℕ 5)
        ≡⟨ +-comm len-f (length prefix +ℕ 5) ⟩
      (length prefix +ℕ 5) +ℕ len-f
        ∎

    len-prefix-final : length prefix-final ≡ length prefix +ℕ 5 +ℕ len-f +ℕ len-g
    len-prefix-final = begin
      length prefix-final
        ≡⟨ List-length-++ prefix-g ⟩
      length prefix-g +ℕ length code-g
        ≡⟨ cong₂ _+ℕ_ len-prefix-g (compile-length-correct g) ⟩
      ((length prefix +ℕ 5) +ℕ len-f) +ℕ len-g
        ∎
      where
        open import Relation.Binary.PropositionalEquality using (cong₂)

    -- Program equality for f
    -- prog = prefix ++ (addi ∷ sd ∷ mv ∷ code-f ++ middle ++ code-g ++ final-instrs) ++ suffix
    -- Need: prog = prefix-f ++ code-f ++ suffix-f
    --     = (prefix ++ addi ∷ sd ∷ mv ∷ []) ++ code-f ++ (middle-store ∷ middle-restore ∷ code-g ++ final)

    -- Helper: code-g ++ final-instrs ++ suffix = code-g ++ final-store ∷ final-result ∷ final-restore-s1 ∷ suffix
    final-suffix-eq : (code-g ++ final-instrs) ++ suffix ≡ code-g ++ (final-store ∷ final-result ∷ final-restore-s1 ∷ suffix)
    final-suffix-eq = ++-assoc code-g final-instrs suffix

    -- Helper: middle with code-g and final
    middle-suffix-eq : (middle-store ∷ middle-restore ∷ code-g ++ final-instrs) ++ suffix
                     ≡ middle-store ∷ middle-restore ∷ (code-g ++ final-store ∷ final-result ∷ final-restore-s1 ∷ suffix)
    middle-suffix-eq = cong (middle-store ∷_) (cong (middle-restore ∷_) final-suffix-eq)

    -- Helper: code-f with middle, code-g and final
    f-suffix-eq : (code-f ++ middle-store ∷ middle-restore ∷ code-g ++ final-instrs) ++ suffix
                ≡ code-f ++ suffix-f
    f-suffix-eq = trans (++-assoc code-f (middle-store ∷ middle-restore ∷ code-g ++ final-instrs) suffix)
                        (cong (code-f ++_) middle-suffix-eq)

    -- Full program equality for f (now 3 setup instructions)
    full-suffix-eq : compile-riscv ⟨ f , g ⟩ ++ suffix
                   ≡ setup-alloc ∷ setup-save-s1 ∷ setup-copy ∷ (code-f ++ suffix-f)
    full-suffix-eq = cong (setup-alloc ∷_) (cong (setup-save-s1 ∷_) (cong (setup-copy ∷_) f-suffix-eq))

    prog-eq-f : prog ≡ prefix-f ++ code-f ++ suffix-f
    prog-eq-f = trans (cong (prefix ++_) full-suffix-eq)
                      (sym (++-assoc prefix (setup-alloc ∷ setup-save-s1 ∷ setup-copy ∷ []) (code-f ++ suffix-f)))

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
-- Phase 1: Setup - trace 3 instructions
--   1. addi sp sp -24  (allocate stack space)
--   2. sd s1 16(sp)    (save original s1)
--   3. mv s1 a0        (copy input to s1)
------------------------------------------------------------------------

-- | Setup phase: allocate pair space, save s1, copy input to s1
-- Entry: pc = offset, a0 = encode x, s1 = original-s1, 24 ≤ sp
-- Exit: pc = offset + 3, sp = sp - 24, s1 = encode x, mem[sp+16] = original-s1
pair-setup-star : ∀ {i A B C} (f : IR i C A) (g : IR i C B)
                  (prefix suffix : Program) (x : ⟦ C ⟧) (s : State) →
  let ctx = make-pair-context f g prefix suffix
      open PairContext ctx
      offset = length prefix
  in
  halted s ≡ false →
  pc s ≡ offset →
  readReg (regs s) a0 ≡ encode x →
  24 ≤ readReg (regs s) sp →  -- Stack bound precondition
  ∃[ s' ] (Star prog s s'
          × halted s' ≡ false
          × pc s' ≡ offset +ℕ 3
          × readReg (regs s') a0 ≡ encode x
          × readReg (regs s') s1 ≡ encode x
          × readReg (regs s') sp ≡ readReg (regs s) sp ∸ 24
          × readReg (regs s') s2 ≡ readReg (regs s) s2
          × readReg (regs s') ra ≡ readReg (regs s) ra
          × readMem (memory s') (readReg (regs s') sp +ℕ 16) ≡ just (readReg (regs s) s1)
          -- Memory preservation at orig-sp and above (setup writes at new-sp+16 = orig-sp-8)
          × readMem (memory s') (readReg (regs s) sp) ≡ readMem (memory s) (readReg (regs s) sp)
          × readMem (memory s') (readReg (regs s) sp +ℕ 8) ≡ readMem (memory s) (readReg (regs s) sp +ℕ 8)
          × readMem (memory s') (readReg (regs s) sp +ℕ 16) ≡ readMem (memory s) (readReg (regs s) sp +ℕ 16)
          × readMem (memory s') (readReg (regs s) sp +ℕ 24) ≡ readMem (memory s) (readReg (regs s) sp +ℕ 24))
pair-setup-star {_} {A} {B} {C} f g prefix suffix x s h-false pc-eq a0-eq sp-bound =
  st3 , star-all , h3 , pc3 , a0-st3 , s1-st3 , sp-st3 , s2-st3 , ra-st3 , mem-s1-saved ,
  mem-orig-sp , mem-orig-sp+8 , mem-orig-sp+16 , mem-orig-sp+24
  where
    ctx = make-pair-context f g prefix suffix
    open PairContext ctx
    offset = length prefix

    orig-sp = readReg (regs s) sp
    new-sp = orig-sp ∸ 24
    orig-s1 = readReg (regs s) s1

    -- Fetch lemmas for 3 instructions
    fetch0 : fetch prog offset ≡ just setup-alloc
    fetch0 = fetch-at-prefix-end prefix setup-alloc _

    prog-eq1 : prog ≡ (prefix ++ setup-alloc ∷ []) ++ _
    prog-eq1 = sym (++-assoc prefix (setup-alloc ∷ []) _)

    len-prefix-1 : length (prefix ++ setup-alloc ∷ []) ≡ offset +ℕ 1
    len-prefix-1 = List-length-++ prefix

    fetch1 : fetch prog (offset +ℕ 1) ≡ just setup-save-s1
    fetch1 = subst₂ (λ p n → fetch p n ≡ just setup-save-s1) (sym prog-eq1) len-prefix-1
                    (fetch-at-prefix-end (prefix ++ setup-alloc ∷ []) setup-save-s1 _)

    prog-eq2 : prog ≡ (prefix ++ setup-alloc ∷ setup-save-s1 ∷ []) ++ _
    prog-eq2 = sym (++-assoc prefix (setup-alloc ∷ setup-save-s1 ∷ []) _)

    len-prefix-2 : length (prefix ++ setup-alloc ∷ setup-save-s1 ∷ []) ≡ offset +ℕ 2
    len-prefix-2 = List-length-++ prefix

    fetch2 : fetch prog (offset +ℕ 2) ≡ just setup-copy
    fetch2 = subst₂ (λ p n → fetch p n ≡ just setup-copy) (sym prog-eq2) len-prefix-2
                    (fetch-at-prefix-end (prefix ++ setup-alloc ∷ setup-save-s1 ∷ []) setup-copy _)

    -- State after step 0: addi sp sp -24
    st1 : State
    st1 = record s { regs = writeReg (regs s) sp new-sp
                   ; pc = pc s +ℕ 1 }

    step0 : step prog s ≡ just st1
    step0 = trans (step-exec prog s setup-alloc h-false
                    (subst (λ p → fetch prog p ≡ just setup-alloc) (sym pc-eq) fetch0))
                  (execAddiNeg prog s sp sp 23)

    h1 : halted st1 ≡ false
    h1 = h-false

    pc1 : pc st1 ≡ offset +ℕ 1
    pc1 = cong (_+ℕ 1) pc-eq

    -- State after step 1: sd s1 16(sp)
    st2 : State
    st2 = record st1 { memory = writeMem (memory st1) (readReg (regs st1) sp +ℕ 16) (readReg (regs st1) s1)
                     ; pc = pc st1 +ℕ 1 }

    step1 : step prog st1 ≡ just st2
    step1 = trans (step-exec prog st1 setup-save-s1 h1
                    (subst (λ p → fetch prog p ≡ just setup-save-s1) (sym pc1) fetch1))
                  (execSd prog st1 s1 16 sp)

    h2 : halted st2 ≡ false
    h2 = h-false

    pc2 : pc st2 ≡ offset +ℕ 2
    pc2 = trans (cong (_+ℕ 1) pc1) (+-assoc offset 1 1)

    -- State after step 2: mv s1 a0
    st3 : State
    st3 = record st2 { regs = writeReg (regs st2) s1 (readReg (regs st2) a0)
                     ; pc = pc st2 +ℕ 1 }

    step2 : step prog st2 ≡ just st3
    step2 = trans (step-exec prog st2 setup-copy h2
                    (subst (λ p → fetch prog p ≡ just setup-copy) (sym pc2) fetch2))
                  (execMv prog st2 s1 a0)

    -- Star proof (3 steps)
    star-all : Star prog s st3
    star-all = ⟨ h-false , step0 ⟩◅ ⟨ h1 , step1 ⟩◅ ⟨ h2 , step2 ⟩◅ refl*

    -- Final state properties
    h3 : halted st3 ≡ false
    h3 = h-false

    pc3 : pc st3 ≡ offset +ℕ 3
    pc3 = trans (cong (_+ℕ 1) pc2) (+-assoc offset 2 1)

    -- Register tracking through states
    sp-st1 : readReg (regs st1) sp ≡ new-sp
    sp-st1 = readReg-writeReg-same (regs s) sp new-sp (λ ())

    s1-st1 : readReg (regs st1) s1 ≡ orig-s1
    s1-st1 = readReg-writeReg-sp-s1 (regs s) new-sp

    a0-st1 : readReg (regs st1) a0 ≡ encode x
    a0-st1 = trans (readReg-writeReg-sp-a0 (regs s) new-sp) a0-eq

    a0-st2 : readReg (regs st2) a0 ≡ encode x
    a0-st2 = a0-st1  -- memory write doesn't change regs

    s1-st2 : readReg (regs st2) s1 ≡ orig-s1
    s1-st2 = s1-st1  -- memory write doesn't change regs

    a0-st3 : readReg (regs st3) a0 ≡ encode x
    a0-st3 = trans (readReg-writeReg-s1-a0 (regs st2) (readReg (regs st2) a0)) a0-st2

    s1-st3 : readReg (regs st3) s1 ≡ encode x
    s1-st3 = trans (readReg-writeReg-same (regs st2) s1 (readReg (regs st2) a0) (λ ())) a0-st2

    sp-st2 : readReg (regs st2) sp ≡ new-sp
    sp-st2 = sp-st1  -- memory write doesn't change regs

    sp-st3 : readReg (regs st3) sp ≡ new-sp
    sp-st3 = trans (readReg-writeReg-s1-sp (regs st2) (readReg (regs st2) a0)) sp-st2

    -- s2 preservation: none of the setup instructions modify s2
    s2-st1 : readReg (regs st1) s2 ≡ readReg (regs s) s2
    s2-st1 = readReg-writeReg-sp-s2 (regs s) new-sp

    s2-st2 : readReg (regs st2) s2 ≡ readReg (regs s) s2
    s2-st2 = s2-st1  -- memory write doesn't change regs

    s2-st3 : readReg (regs st3) s2 ≡ readReg (regs s) s2
    s2-st3 = trans (readReg-writeReg-s1-s2 (regs st2) (readReg (regs st2) a0)) s2-st2

    ra-st1 : readReg (regs st1) ra ≡ readReg (regs s) ra
    ra-st1 = readReg-writeReg-sp-ra (regs s) new-sp

    ra-st2 : readReg (regs st2) ra ≡ readReg (regs s) ra
    ra-st2 = ra-st1  -- memory write doesn't change regs

    ra-st3 : readReg (regs st3) ra ≡ readReg (regs s) ra
    ra-st3 = trans (readReg-writeReg-s1-ra (regs st2) (readReg (regs st2) a0)) ra-st2

    -- Memory: s1 was saved at sp+16
    mem-st2 : readMem (memory st2) (new-sp +ℕ 16) ≡ just orig-s1
    mem-st2 = trans (cong (λ addr → readMem (memory st2) addr) (cong (_+ℕ 16) (sym sp-st1)))
                    (trans (readMem-writeMem-same (memory st1) (readReg (regs st1) sp +ℕ 16) (readReg (regs st1) s1))
                           (cong just s1-st1))

    mem-s1-saved : readMem (memory st3) (new-sp +ℕ 16) ≡ just orig-s1
    mem-s1-saved = trans (cong (λ addr → readMem (memory st3) addr) (cong (_+ℕ 16) (sym sp-st3))) mem-st2

    -- Memory preservation at orig-sp and above
    -- Setup only writes at new-sp + 16 = (orig-sp - 24) + 16 = orig-sp - 8
    -- This is different from orig-sp, orig-sp+8, orig-sp+16, orig-sp+24
    -- st1: no memory write (only register change)
    -- st2: writes at st1.sp + 16 = new-sp + 16 = orig-sp - 8
    -- st3: no memory write (only register change)

    -- The write address is always 8 less than orig-sp (when orig-sp ≥ 24)
    -- Since write is at orig-sp - 8, and we check orig-sp, orig-sp+8, orig-sp+16, orig-sp+24,
    -- all these are > orig-sp - 8 (by 8, 16, 24, 32 respectively), so they're different.

    -- Proven address disjointness using setup-write-addr≢* lemmas
    -- Key: st1.sp = new-sp = orig-sp ∸ 24, and we have sp-bound : 24 ≤ orig-sp
    write-addr-eq : readReg (regs st1) sp +ℕ 16 ≡ (orig-sp ∸ 24) +ℕ 16
    write-addr-eq = cong (_+ℕ 16) sp-st1

    write-addr≢orig-sp : (readReg (regs st1) sp +ℕ 16) ≢ orig-sp
    write-addr≢orig-sp eq = setup-write-addr≢orig-sp orig-sp sp-bound
                              (trans (sym write-addr-eq) eq)

    write-addr≢orig-sp+8 : (readReg (regs st1) sp +ℕ 16) ≢ (orig-sp +ℕ 8)
    write-addr≢orig-sp+8 eq = setup-write-addr≢orig-sp+8 orig-sp sp-bound
                                (trans (sym write-addr-eq) eq)

    write-addr≢orig-sp+16 : (readReg (regs st1) sp +ℕ 16) ≢ (orig-sp +ℕ 16)
    write-addr≢orig-sp+16 eq = setup-write-addr≢orig-sp+16 orig-sp sp-bound
                                 (trans (sym write-addr-eq) eq)

    write-addr≢orig-sp+24 : (readReg (regs st1) sp +ℕ 16) ≢ (orig-sp +ℕ 24)
    write-addr≢orig-sp+24 eq = setup-write-addr≢orig-sp+24 orig-sp sp-bound
                                 (trans (sym write-addr-eq) eq)

    mem-orig-sp : readMem (memory st3) orig-sp ≡ readMem (memory s) orig-sp
    mem-orig-sp = readMem-writeMem-diff (memory st1) (readReg (regs st1) sp +ℕ 16) orig-sp
                    (readReg (regs st1) s1) write-addr≢orig-sp

    mem-orig-sp+8 : readMem (memory st3) (orig-sp +ℕ 8) ≡ readMem (memory s) (orig-sp +ℕ 8)
    mem-orig-sp+8 = readMem-writeMem-diff (memory st1) (readReg (regs st1) sp +ℕ 16) (orig-sp +ℕ 8)
                      (readReg (regs st1) s1) write-addr≢orig-sp+8

    mem-orig-sp+16 : readMem (memory st3) (orig-sp +ℕ 16) ≡ readMem (memory s) (orig-sp +ℕ 16)
    mem-orig-sp+16 = readMem-writeMem-diff (memory st1) (readReg (regs st1) sp +ℕ 16) (orig-sp +ℕ 16)
                       (readReg (regs st1) s1) write-addr≢orig-sp+16

    mem-orig-sp+24 : readMem (memory st3) (orig-sp +ℕ 24) ≡ readMem (memory s) (orig-sp +ℕ 24)
    mem-orig-sp+24 = readMem-writeMem-diff (memory st1) (readReg (regs st1) sp +ℕ 16) (orig-sp +ℕ 24)
                       (readReg (regs st1) s1) write-addr≢orig-sp+24

------------------------------------------------------------------------
-- Phase 3: Middle - trace 2 instructions (sd a0 0(sp); mv a0 s1)
------------------------------------------------------------------------

-- | Middle phase: store f result and restore original input
-- Entry: pc = offset + 3 + len-f, a0 = encode (eval f x), s1 = encode x
--        curr-sp = orig-sp ∸ 24, 24 ≤ orig-sp
-- Exit: pc = offset + 5 + len-f, a0 = encode x, memory[sp] = encode (eval f x)
pair-middle-star : ∀ {i A B C} (f : IR i C A) (g : IR i C B)
                   (prefix suffix : Program) (x : ⟦ C ⟧) (s sf : State) →
  let ctx = make-pair-context f g prefix suffix
      open PairContext ctx
      mid-offset = length prefix +ℕ 3 +ℕ len-f
  in
  halted sf ≡ false →
  pc sf ≡ mid-offset →
  readReg (regs sf) a0 ≡ encode (eval f x) →
  readReg (regs sf) s1 ≡ encode x →
  24 ≤ readReg (regs s) sp →  -- Stack bound precondition
  readReg (regs sf) sp ≡ readReg (regs s) sp ∸ 24 →  -- Relationship from setup
  ∃[ s' ] (Star prog sf s'
          × halted s' ≡ false
          × pc s' ≡ mid-offset +ℕ 2
          × readReg (regs s') a0 ≡ encode x
          × readReg (regs s') s1 ≡ encode x
          × readReg (regs s') sp ≡ readReg (regs sf) sp
          × readReg (regs s') s2 ≡ readReg (regs sf) s2
          × readReg (regs s') ra ≡ readReg (regs sf) ra
          × readMem (memory s') (readReg (regs sf) sp) ≡ just (encode (eval f x))
          × readMem (memory s') (readReg (regs sf) sp +ℕ 16) ≡ readMem (memory sf) (readReg (regs sf) sp +ℕ 16)
          -- Memory preservation at original sp and above (middle writes at sf.sp, not at s.sp)
          × readMem (memory s') (readReg (regs s) sp) ≡ readMem (memory sf) (readReg (regs s) sp)
          × readMem (memory s') (readReg (regs s) sp +ℕ 8) ≡ readMem (memory sf) (readReg (regs s) sp +ℕ 8)
          × readMem (memory s') (readReg (regs s) sp +ℕ 16) ≡ readMem (memory sf) (readReg (regs s) sp +ℕ 16)
          × readMem (memory s') (readReg (regs s) sp +ℕ 24) ≡ readMem (memory sf) (readReg (regs s) sp +ℕ 24))
pair-middle-star {_} {A} {B} {C} f g prefix suffix x s sf h-false pc-eq a0-eq s1-eq sp-bound curr-sp-eq =
  st2 , star-all , h2 , pc2 , a0-st2 , s1-st2 , sp-st2 , s2-st2 , ra-st2 , mem-st2 , mem-sp+16-st2 ,
  mem-orig-sp , mem-orig-sp+8 , mem-orig-sp+16 , mem-orig-sp+24
  where
    ctx = make-pair-context f g prefix suffix
    open PairContext ctx
    mid-offset = length prefix +ℕ 3 +ℕ len-f

    curr-sp = readReg (regs sf) sp

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

    -- State after step 0: sd a0 0(sp)
    st1 : State
    st1 = record sf { memory = writeMem (memory sf) (curr-sp +ℕ 0) (readReg (regs sf) a0)
                    ; pc = pc sf +ℕ 1 }

    step0 : step prog sf ≡ just st1
    step0 = trans (step-exec prog sf middle-store h-false
                    (subst (λ p → fetch prog p ≡ just middle-store) (sym pc-eq) fetch-mid0))
                  (execSd prog sf a0 0 sp)

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

    sp-st1 : readReg (regs st1) sp ≡ curr-sp
    sp-st1 = refl  -- memory write doesn't change regs

    sp-st2 : readReg (regs st2) sp ≡ curr-sp
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

    -- Memory tracking
    mem-write-addr : curr-sp +ℕ 0 ≡ curr-sp
    mem-write-addr = +-identityʳ curr-sp
      where open import Data.Nat.Properties using (+-identityʳ)

    mem-st1-at-plus-zero : readMem (memory st1) (curr-sp +ℕ 0) ≡ just (encode (eval f x))
    mem-st1-at-plus-zero = trans (readMem-writeMem-same (memory sf) (curr-sp +ℕ 0) (readReg (regs sf) a0))
                                 (cong just a0-eq)

    mem-st1 : readMem (memory st1) curr-sp ≡ just (encode (eval f x))
    mem-st1 = subst (λ a → readMem (memory st1) a ≡ just (encode (eval f x)))
                    mem-write-addr
                    mem-st1-at-plus-zero

    mem-st2 : readMem (memory st2) curr-sp ≡ just (encode (eval f x))
    mem-st2 = mem-st1  -- mv doesn't change memory

    -- Memory at sp+16 is preserved (write is at sp+0, not sp+16)
    -- Use n≢n+suc curr-sp 15 : curr-sp ≢ curr-sp + 16
    sp+0≢sp+16 : (curr-sp +ℕ 0) ≢ (curr-sp +ℕ 16)
    sp+0≢sp+16 eq = n≢n+suc curr-sp 15 (trans (sym (+-identityʳ curr-sp)) eq)
      where open import Data.Nat.Properties using (+-identityʳ)

    mem-sp+16-st1 : readMem (memory st1) (curr-sp +ℕ 16) ≡ readMem (memory sf) (curr-sp +ℕ 16)
    mem-sp+16-st1 = readMem-writeMem-diff (memory sf) (curr-sp +ℕ 0) (curr-sp +ℕ 16)
                      (readReg (regs sf) a0) sp+0≢sp+16

    mem-sp+16-st2 : readMem (memory st2) (curr-sp +ℕ 16) ≡ readMem (memory sf) (curr-sp +ℕ 16)
    mem-sp+16-st2 = mem-sp+16-st1  -- mv doesn't change memory

    -- Memory preservation at orig-sp and above
    -- Middle phase writes at curr-sp = sf.sp = orig-sp - 24
    -- So writes are disjoint from orig-sp, orig-sp+8, orig-sp+16, orig-sp+24
    orig-sp = readReg (regs s) sp

    -- Proven address disjointness using middle-write-addr≢* lemmas
    -- Key: curr-sp = orig-sp ∸ 24 (from curr-sp-eq), and write is at curr-sp + 0 = curr-sp
    write-addr-is-curr-sp : curr-sp +ℕ 0 ≡ curr-sp
    write-addr-is-curr-sp = +-identityʳ curr-sp

    write-addr-is-orig-sp-minus-24 : curr-sp +ℕ 0 ≡ orig-sp ∸ 24
    write-addr-is-orig-sp-minus-24 = trans write-addr-is-curr-sp curr-sp-eq

    write-addr≢orig-sp : (curr-sp +ℕ 0) ≢ orig-sp
    write-addr≢orig-sp eq = middle-write-addr≢orig-sp orig-sp sp-bound
                              (trans (sym write-addr-is-orig-sp-minus-24) eq)

    write-addr≢orig-sp+8 : (curr-sp +ℕ 0) ≢ (orig-sp +ℕ 8)
    write-addr≢orig-sp+8 eq = middle-write-addr≢orig-sp+8 orig-sp sp-bound
                                (trans (sym write-addr-is-orig-sp-minus-24) eq)

    write-addr≢orig-sp+16 : (curr-sp +ℕ 0) ≢ (orig-sp +ℕ 16)
    write-addr≢orig-sp+16 eq = middle-write-addr≢orig-sp+16 orig-sp sp-bound
                                 (trans (sym write-addr-is-orig-sp-minus-24) eq)

    write-addr≢orig-sp+24 : (curr-sp +ℕ 0) ≢ (orig-sp +ℕ 24)
    write-addr≢orig-sp+24 eq = middle-write-addr≢orig-sp+24 orig-sp sp-bound
                                 (trans (sym write-addr-is-orig-sp-minus-24) eq)

    mem-orig-sp : readMem (memory st2) orig-sp ≡ readMem (memory sf) orig-sp
    mem-orig-sp = readMem-writeMem-diff (memory sf) (curr-sp +ℕ 0) orig-sp
                    (readReg (regs sf) a0) write-addr≢orig-sp

    mem-orig-sp+8 : readMem (memory st2) (orig-sp +ℕ 8) ≡ readMem (memory sf) (orig-sp +ℕ 8)
    mem-orig-sp+8 = readMem-writeMem-diff (memory sf) (curr-sp +ℕ 0) (orig-sp +ℕ 8)
                      (readReg (regs sf) a0) write-addr≢orig-sp+8

    mem-orig-sp+16 : readMem (memory st2) (orig-sp +ℕ 16) ≡ readMem (memory sf) (orig-sp +ℕ 16)
    mem-orig-sp+16 = readMem-writeMem-diff (memory sf) (curr-sp +ℕ 0) (orig-sp +ℕ 16)
                       (readReg (regs sf) a0) write-addr≢orig-sp+16

    mem-orig-sp+24 : readMem (memory st2) (orig-sp +ℕ 24) ≡ readMem (memory sf) (orig-sp +ℕ 24)
    mem-orig-sp+24 = readMem-writeMem-diff (memory sf) (curr-sp +ℕ 0) (orig-sp +ℕ 24)
                       (readReg (regs sf) a0) write-addr≢orig-sp+24

------------------------------------------------------------------------
-- Phase 5: Final - trace 3 instructions
--   1. sd a0 8(sp)     (store g result)
--   2. mv a0 sp        (return pair pointer)
--   3. ld s1 16(sp)    (restore original s1)
------------------------------------------------------------------------

-- | Final phase: store g result, return pair pointer, restore s1
-- Entry: pc = offset + 5 + len-f + len-g, a0 = encode (eval g x)
--        memory[sp+16] = orig-s1 (saved during setup)
--        24 ≤ orig-sp, curr-sp = orig-sp ∸ 24
-- Exit: pc = offset + 8 + len-f + len-g, a0 = encode (eval f x, eval g x), s1 = orig-s1
pair-final-star : ∀ {i A B C} (f : IR i C A) (g : IR i C B)
                  (prefix suffix : Program) (x : ⟦ C ⟧) (orig-s1 : Word) (orig-sp : ℕ) (sf sg : State) →
  let ctx = make-pair-context f g prefix suffix
      open PairContext ctx
      final-offset = length prefix +ℕ 5 +ℕ len-f +ℕ len-g
      curr-sp = readReg (regs sg) sp
  in
  halted sg ≡ false →
  pc sg ≡ final-offset →
  readReg (regs sg) a0 ≡ encode (eval g x) →
  readMem (memory sg) curr-sp ≡ just (encode (eval f x)) →
  readMem (memory sg) (curr-sp +ℕ 16) ≡ just orig-s1 →
  24 ≤ orig-sp →  -- Stack bound precondition
  readReg (regs sg) sp ≡ orig-sp ∸ 24 →  -- Relationship from setup
  ∃[ s' ] (Star prog sg s'
          × halted s' ≡ false
          × pc s' ≡ final-offset +ℕ 3
          × readReg (regs s') a0 ≡ encode (eval f x , eval g x)
          × readReg (regs s') s1 ≡ orig-s1
          × readReg (regs s') s2 ≡ readReg (regs sg) s2
          × readReg (regs s') ra ≡ readReg (regs sg) ra
          × readReg (regs s') sp ≡ readReg (regs sg) sp
          -- Memory preservation at orig-sp and above (final writes at sp+8, not at orig-sp)
          × readMem (memory s') orig-sp ≡ readMem (memory sg) orig-sp
          × readMem (memory s') (orig-sp +ℕ 8) ≡ readMem (memory sg) (orig-sp +ℕ 8)
          × readMem (memory s') (orig-sp +ℕ 16) ≡ readMem (memory sg) (orig-sp +ℕ 16)
          × readMem (memory s') (orig-sp +ℕ 24) ≡ readMem (memory sg) (orig-sp +ℕ 24))
pair-final-star {_} {A} {B} {C} f g prefix suffix x orig-s1 orig-sp sf sg h-false pc-eq a0-eq mem-f mem-s1 sp-bound curr-sp-eq =
  st3 , star-all , h3 , pc3 , a0-final , s1-st3 , s2-st3 , ra-st3 , sp-st3 ,
  mem-orig-sp , mem-orig-sp+8 , mem-orig-sp+16 , mem-orig-sp+24
  where
    ctx = make-pair-context f g prefix suffix
    open PairContext ctx
    final-offset = length prefix +ℕ 5 +ℕ len-f +ℕ len-g
    curr-sp = readReg (regs sg) sp

    -- Fetch lemmas for 3 instructions
    prog-eq-final : prog ≡ prefix-final ++ suffix-g
    prog-eq-final = trans prog-eq-g (sym (++-assoc prefix-g code-g suffix-g))

    fetch-final0 : fetch prog final-offset ≡ just final-store
    fetch-final0 = subst₂ (λ p n → fetch p n ≡ just final-store) (sym prog-eq-final) len-prefix-final
                          (fetch-at-prefix-end prefix-final final-store _)

    prog-eq-final1 : prog ≡ (prefix-final ++ final-store ∷ []) ++ _
    prog-eq-final1 = trans prog-eq-final (sym (++-assoc prefix-final (final-store ∷ []) _))

    len-prefix-final1 : length (prefix-final ++ final-store ∷ []) ≡ final-offset +ℕ 1
    len-prefix-final1 = trans (List-length-++ prefix-final) (cong (_+ℕ 1) len-prefix-final)

    fetch-final1 : fetch prog (final-offset +ℕ 1) ≡ just final-result
    fetch-final1 = subst₂ (λ p n → fetch p n ≡ just final-result) (sym prog-eq-final1) len-prefix-final1
                          (fetch-at-prefix-end (prefix-final ++ final-store ∷ []) final-result _)

    prog-eq-final2 : prog ≡ (prefix-final ++ final-store ∷ final-result ∷ []) ++ _
    prog-eq-final2 = trans prog-eq-final (sym (++-assoc prefix-final (final-store ∷ final-result ∷ []) _))

    len-prefix-final2 : length (prefix-final ++ final-store ∷ final-result ∷ []) ≡ final-offset +ℕ 2
    len-prefix-final2 = trans (List-length-++ prefix-final) (cong (_+ℕ 2) len-prefix-final)

    fetch-final2 : fetch prog (final-offset +ℕ 2) ≡ just final-restore-s1
    fetch-final2 = subst₂ (λ p n → fetch p n ≡ just final-restore-s1) (sym prog-eq-final2) len-prefix-final2
                          (fetch-at-prefix-end (prefix-final ++ final-store ∷ final-result ∷ []) final-restore-s1 _)

    -- State after step 0: sd a0 8(sp)
    st1 : State
    st1 = record sg { memory = writeMem (memory sg) (curr-sp +ℕ 8) (readReg (regs sg) a0)
                    ; pc = pc sg +ℕ 1 }

    step0 : step prog sg ≡ just st1
    step0 = trans (step-exec prog sg final-store h-false
                    (subst (λ p → fetch prog p ≡ just final-store) (sym pc-eq) fetch-final0))
                  (execSd prog sg a0 8 sp)

    h1 : halted st1 ≡ false
    h1 = h-false

    pc1 : pc st1 ≡ final-offset +ℕ 1
    pc1 = cong (_+ℕ 1) pc-eq

    -- State after step 1: mv a0 sp
    st2 : State
    st2 = record st1 { regs = writeReg (regs st1) a0 (readReg (regs st1) sp)
                     ; pc = pc st1 +ℕ 1 }

    step1 : step prog st1 ≡ just st2
    step1 = trans (step-exec prog st1 final-result h1
                    (subst (λ p → fetch prog p ≡ just final-result) (sym pc1) fetch-final1))
                  (execMv prog st1 a0 sp)

    h2 : halted st2 ≡ false
    h2 = h-false

    pc2 : pc st2 ≡ final-offset +ℕ 2
    pc2 = trans (cong (_+ℕ 1) pc1) (+-assoc final-offset 1 1)

    -- Register tracking for sp (needed for memory address calculation)
    sp-st1 : readReg (regs st1) sp ≡ curr-sp
    sp-st1 = refl  -- memory write doesn't change regs

    sp-st2 : readReg (regs st2) sp ≡ curr-sp
    sp-st2 = trans (readReg-writeReg-a0-sp (regs st1) (readReg (regs st1) sp)) sp-st1

    -- Inequality proof: curr-sp + 8 ≢ curr-sp + 16
    -- n≢n+suc produces (n ≢ n + 8), we need (n ≢ curr-sp + 16) where n = curr-sp + 8
    sp+8≢sp+16 : (curr-sp +ℕ 8) ≢ (curr-sp +ℕ 16)
    sp+8≢sp+16 eq = n≢n+suc (curr-sp +ℕ 8) 7 (trans eq (sym (+-assoc curr-sp 8 8)))

    -- Memory at sp+16 is preserved through st1 and st2 (needed for load)
    mem-s1-st1 : readMem (memory st1) (curr-sp +ℕ 16) ≡ just orig-s1
    mem-s1-st1 = trans (readMem-writeMem-diff (memory sg) (curr-sp +ℕ 8) (curr-sp +ℕ 16)
                         (readReg (regs sg) a0) sp+8≢sp+16)
                       mem-s1

    mem-s1-st2 : readMem (memory st2) (curr-sp +ℕ 16) ≡ just orig-s1
    mem-s1-st2 = mem-s1-st1  -- mv doesn't change memory

    -- Memory read for s1 uses sp in st2 which equals curr-sp
    mem-read-addr-eq : readReg (regs st2) sp +ℕ 16 ≡ curr-sp +ℕ 16
    mem-read-addr-eq = cong (_+ℕ 16) sp-st2

    mem-s1-at-st2-sp : readMem (memory st2) (readReg (regs st2) sp +ℕ 16) ≡ just orig-s1
    mem-s1-at-st2-sp = subst (λ a → readMem (memory st2) a ≡ just orig-s1) (sym mem-read-addr-eq) mem-s1-st2

    -- State after step 2: ld s1 16(sp)
    st3 : State
    st3 = record st2 { regs = writeReg (regs st2) s1 orig-s1
                     ; pc = pc st2 +ℕ 1 }

    step2 : step prog st2 ≡ just st3
    step2 = trans (step-exec prog st2 final-restore-s1 h2
                    (subst (λ p → fetch prog p ≡ just final-restore-s1) (sym pc2) fetch-final2))
                  (execLd prog st2 s1 16 sp orig-s1 mem-s1-at-st2-sp)

    -- Star proof (3 steps)
    star-all : Star prog sg st3
    star-all = ⟨ h-false , step0 ⟩◅ ⟨ h1 , step1 ⟩◅ ⟨ h2 , step2 ⟩◅ refl*

    -- Final state properties
    h3 : halted st3 ≡ false
    h3 = h-false

    pc3 : pc st3 ≡ final-offset +ℕ 3
    pc3 = trans (cong (_+ℕ 1) pc2) (+-assoc final-offset 2 1)

    -- Register tracking for ra
    ra-st1 : readReg (regs st1) ra ≡ readReg (regs sg) ra
    ra-st1 = refl  -- memory write doesn't change regs

    ra-st2 : readReg (regs st2) ra ≡ readReg (regs sg) ra
    ra-st2 = trans (readReg-writeReg-a0-ra (regs st1) (readReg (regs st1) sp)) ra-st1

    ra-st3 : readReg (regs st3) ra ≡ readReg (regs sg) ra
    ra-st3 = trans (readReg-writeReg-s1-ra (regs st2) orig-s1) ra-st2

    -- sp tracking through all states
    sp-st3 : readReg (regs st3) sp ≡ readReg (regs sg) sp
    sp-st3 = trans (readReg-writeReg-s1-sp (regs st2) orig-s1) sp-st2

    -- s2 preservation: final instructions don't modify s2
    s2-st1 : readReg (regs st1) s2 ≡ readReg (regs sg) s2
    s2-st1 = refl  -- memory write doesn't change regs

    s2-st2 : readReg (regs st2) s2 ≡ readReg (regs sg) s2
    s2-st2 = trans (readReg-writeReg-a0-s2 (regs st1) (readReg (regs st1) sp)) s2-st1

    s2-st3 : readReg (regs st3) s2 ≡ readReg (regs sg) s2
    s2-st3 = trans (readReg-writeReg-s1-s2 (regs st2) orig-s1) s2-st2

    -- s1 gets the value orig-s1 directly from writeReg
    s1-st3 : readReg (regs st3) s1 ≡ orig-s1
    s1-st3 = readReg-writeReg-same (regs st2) s1 orig-s1 (λ ())

    -- Memory at curr-sp (first element) - preserved from before
    curr-sp≢curr-sp+8 : curr-sp ≢ curr-sp +ℕ 8
    curr-sp≢curr-sp+8 = n≢n+suc curr-sp 7

    mem-at-sp-st1 : readMem (memory st1) curr-sp ≡ just (encode (eval f x))
    mem-at-sp-st1 = trans (readMem-writeMem-diff (memory sg) (curr-sp +ℕ 8) curr-sp
                            (readReg (regs sg) a0)
                            (λ eq → curr-sp≢curr-sp+8 (sym eq)))
                          mem-f

    mem-at-sp-st2 : readMem (memory st2) curr-sp ≡ just (encode (eval f x))
    mem-at-sp-st2 = mem-at-sp-st1  -- mv doesn't change memory

    -- Memory at curr-sp+8 (second element)
    mem-at-sp+8-st1 : readMem (memory st1) (curr-sp +ℕ 8) ≡ just (encode (eval g x))
    mem-at-sp+8-st1 = trans (readMem-writeMem-same (memory sg) (curr-sp +ℕ 8) (readReg (regs sg) a0))
                            (cong just a0-eq)

    mem-at-sp+8-st2 : readMem (memory st2) (curr-sp +ℕ 8) ≡ just (encode (eval g x))
    mem-at-sp+8-st2 = mem-at-sp+8-st1  -- mv doesn't change memory

    -- Use encode-pair-construct to show curr-sp = encode (f-result, g-result)
    pair-encoding : curr-sp ≡ encode (eval f x , eval g x)
    pair-encoding = encode-pair-construct (eval f x) (eval g x) curr-sp (memory st2)
                      mem-at-sp-st2 mem-at-sp+8-st2

    -- a0 in st2 = sp in st1 = curr-sp = encode (f-result, g-result)
    a0-st2-is-sp : readReg (regs st2) a0 ≡ curr-sp
    a0-st2-is-sp = trans (readReg-writeReg-same (regs st1) a0 (readReg (regs st1) sp) (λ ())) sp-st1

    a0-st2 : readReg (regs st2) a0 ≡ encode (eval f x , eval g x)
    a0-st2 = trans a0-st2-is-sp pair-encoding

    -- a0 in st3 = a0 in st2 (s1 write doesn't affect a0)
    a0-final : readReg (regs st3) a0 ≡ encode (eval f x , eval g x)
    a0-final = trans (readReg-writeReg-s1-a0 (regs st2) orig-s1) a0-st2

    -- Memory preservation at orig-sp and above
    -- Final phase writes at curr-sp + 8 (= orig-sp - 16 if curr-sp = orig-sp - 24)
    -- This is disjoint from orig-sp, orig-sp+8, orig-sp+16, orig-sp+24

    -- Proven address disjointness using sp-bound and curr-sp-eq
    write-addr-eq : curr-sp +ℕ 8 ≡ (orig-sp ∸ 24) +ℕ 8
    write-addr-eq = cong (_+ℕ 8) curr-sp-eq

    write-addr≢orig-sp : (curr-sp +ℕ 8) ≢ orig-sp
    write-addr≢orig-sp eq = final-write-addr≢orig-sp orig-sp sp-bound
                              (trans (sym write-addr-eq) eq)

    write-addr≢orig-sp+8 : (curr-sp +ℕ 8) ≢ (orig-sp +ℕ 8)
    write-addr≢orig-sp+8 eq = final-write-addr≢orig-sp+8 orig-sp sp-bound
                                (trans (sym write-addr-eq) eq)

    write-addr≢orig-sp+16 : (curr-sp +ℕ 8) ≢ (orig-sp +ℕ 16)
    write-addr≢orig-sp+16 eq = final-write-addr≢orig-sp+16 orig-sp sp-bound
                                 (trans (sym write-addr-eq) eq)

    write-addr≢orig-sp+24 : (curr-sp +ℕ 8) ≢ (orig-sp +ℕ 24)
    write-addr≢orig-sp+24 eq = final-write-addr≢orig-sp+24 orig-sp sp-bound
                                 (trans (sym write-addr-eq) eq)

    mem-orig-sp : readMem (memory st3) orig-sp ≡ readMem (memory sg) orig-sp
    mem-orig-sp = readMem-writeMem-diff (memory sg) (curr-sp +ℕ 8) orig-sp
                    (readReg (regs sg) a0) write-addr≢orig-sp

    mem-orig-sp+8 : readMem (memory st3) (orig-sp +ℕ 8) ≡ readMem (memory sg) (orig-sp +ℕ 8)
    mem-orig-sp+8 = readMem-writeMem-diff (memory sg) (curr-sp +ℕ 8) (orig-sp +ℕ 8)
                      (readReg (regs sg) a0) write-addr≢orig-sp+8

    mem-orig-sp+16 : readMem (memory st3) (orig-sp +ℕ 16) ≡ readMem (memory sg) (orig-sp +ℕ 16)
    mem-orig-sp+16 = readMem-writeMem-diff (memory sg) (curr-sp +ℕ 8) (orig-sp +ℕ 16)
                       (readReg (regs sg) a0) write-addr≢orig-sp+16

    mem-orig-sp+24 : readMem (memory st3) (orig-sp +ℕ 24) ≡ readMem (memory sg) (orig-sp +ℕ 24)
    mem-orig-sp+24 = readMem-writeMem-diff (memory sg) (curr-sp +ℕ 8) (orig-sp +ℕ 24)
                       (readReg (regs sg) a0) write-addr≢orig-sp+24

------------------------------------------------------------------------
-- Helper for assembling pair result from f and g results
------------------------------------------------------------------------

-- This will be used by MutualIR to combine the recursive results
