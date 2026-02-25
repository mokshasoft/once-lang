{-# OPTIONS --sized-types #-}
------------------------------------------------------------------------
-- Once.CCC.Target.AArch64.Correct.IR.Compose
--
-- Helper records and functions for compose proofs.
-- Extracts non-recursive parts to reduce mutual block compilation time.
-- The recursive calls stay in MutualIR.agda.
------------------------------------------------------------------------

module Once.CCC.Target.AArch64.Correct.IR.Compose where

open import Size
open import Once.Type
open import Once.IR
open import Once.Semantics hiding (code-ptr; env-addr; semantics)

open import Once.Target.AArch64.Syntax
open import Once.Target.AArch64.Semantics
open State
open import Once.CCC.Target.AArch64.CodeGen

open import Once.CCC.Target.AArch64.Correct.Foundation using (encode)
open import Once.CCC.Target.AArch64.Correct.CompileLength using (compile-length-correct)
open import Once.CCC.Target.AArch64.Correct.Star using (Star; star-trans)
open import Once.CCC.Target.AArch64.Correct.StarBase using (IRStarResultS)
open import Once.CCC.Target.AArch64.Correct.StackInvariant using (StackInvariant; X29Invariant)
open import Once.CCC.Target.AArch64.Correct.MemoryValid using (ClosureAtS)
open import Once.CCC.Target.AArch64.Correct.ClosureWellFormed using (ClosureWellFormedS)

open import Data.Bool using (false)
open import Data.Nat using (ℕ; zero; suc; _∸_; _>_; _≤_) renaming (_+_ to _+ℕ_)
open import Data.Nat.Properties using (+-assoc; +-comm; ≤-refl; ≤-trans; ≤-reflexive)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.List.Properties using (++-assoc) renaming (length-++ to List-length-++)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; ∃-syntax)
open import Data.Maybe using (just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)
open import Relation.Binary.PropositionalEquality.Properties using (module ≡-Reasoning)
open ≡-Reasoning

------------------------------------------------------------------------
-- List helpers
------------------------------------------------------------------------

-- | Length of concatenation
length-++ : ∀ {A : Set} (xs ys : List A) → length (xs ++ ys) ≡ length xs +ℕ length ys
length-++ [] ys = refl
length-++ (x ∷ xs) ys = cong suc (length-++ xs ys)

------------------------------------------------------------------------
-- Compose Context: computed values for compose proof
------------------------------------------------------------------------
--
-- The compose (g ∘ f) code structure for AArch64:
--   compile-aarch64 (g ∘ f) = compile-aarch64 f ++ nop ∷ compile-aarch64 g
--
-- Execution phases:
--   1. Execute f (len-f instructions)
--   2. Execute nop (1 instruction)
--   3. Execute g (len-g instructions)
--
-- Total: (len-f + 1) + len-g = compile-length (g ∘ f)

record ComposeContext {A B C : Type} (f : IR A B) (g : IR B C)
                      (prefix suffix : Program) : Set where
  field
    -- Computed lengths
    len-f : ℕ
    len-g : ℕ

    -- Computed programs
    code-f : Program
    code-g : Program
    prog : Program

    -- Derived prefixes/suffixes for f execution
    prefix-f : Program    -- = prefix
    suffix-f : Program    -- = nop ∷ code-g ++ suffix

    -- Derived prefixes/suffixes for nop execution
    prefix-nop : Program  -- = prefix ++ code-f
    suffix-nop : Program  -- = code-g ++ suffix

    -- Derived prefixes/suffixes for g execution
    prefix-g : Program    -- = prefix ++ code-f ++ nop ∷ []
    suffix-g : Program    -- = suffix

    -- Length equalities
    len-prefix-f   : length prefix-f ≡ length prefix
    len-prefix-nop : length prefix-nop ≡ length prefix +ℕ len-f
    len-prefix-g   : length prefix-g ≡ length prefix +ℕ len-f +ℕ 1

    -- Program equalities for rewriting
    prog-eq-f   : prefix-f ++ code-f ++ suffix-f ≡ prog
    prog-eq-nop : prefix-nop ++ nop ∷ suffix-nop ≡ prog
    prog-eq-g   : prefix-g ++ code-g ++ suffix-g ≡ prog

open ComposeContext public

-- | Construct ComposeContext from IR terms and prefix/suffix
mkComposeContext : ∀ {A B C : Type} (f : IR A B) (g : IR B C)
                   (prefix suffix : Program) → ComposeContext f g prefix suffix
mkComposeContext {A} {B} {C} f g prefix suffix = record
  { len-f = the-len-f
  ; len-g = the-len-g
  ; code-f = the-code-f
  ; code-g = the-code-g
  ; prog = the-prog
  ; prefix-f = prefix
  ; suffix-f = the-suffix-f
  ; prefix-nop = the-prefix-nop
  ; suffix-nop = the-suffix-nop
  ; prefix-g = the-prefix-g
  ; suffix-g = suffix
  ; len-prefix-f = refl
  ; len-prefix-nop = the-len-prefix-nop
  ; len-prefix-g = the-len-prefix-g
  ; prog-eq-f = the-prog-eq-f
  ; prog-eq-nop = the-prog-eq-nop
  ; prog-eq-g = the-prog-eq-g
  }
  where
    the-len-f = compile-length f
    the-len-g = compile-length g
    the-code-f = compile-aarch64 f
    the-code-g = compile-aarch64 g
    the-prog = prefix ++ compile-aarch64 (g ∘ f) ++ suffix

    the-suffix-f : Program
    the-suffix-f = nop ∷ the-code-g ++ suffix

    the-prefix-nop : Program
    the-prefix-nop = prefix ++ the-code-f

    the-suffix-nop : Program
    the-suffix-nop = the-code-g ++ suffix

    the-prefix-g : Program
    the-prefix-g = prefix ++ the-code-f ++ nop ∷ []

    the-len-prefix-nop : length the-prefix-nop ≡ length prefix +ℕ the-len-f
    the-len-prefix-nop = trans (length-++ prefix the-code-f)
                               (cong (length prefix +ℕ_) (compile-length-correct f))

    the-len-prefix-g : length the-prefix-g ≡ length prefix +ℕ the-len-f +ℕ 1
    the-len-prefix-g = begin
      length the-prefix-g
        ≡⟨ length-++ prefix _ ⟩
      length prefix +ℕ length (the-code-f ++ nop ∷ [])
        ≡⟨ cong (length prefix +ℕ_) (length-++ the-code-f _) ⟩
      length prefix +ℕ (length the-code-f +ℕ 1)
        ≡⟨ cong (length prefix +ℕ_) (cong (_+ℕ 1) (compile-length-correct f)) ⟩
      length prefix +ℕ (the-len-f +ℕ 1)
        ≡⟨ sym (+-assoc (length prefix) the-len-f 1) ⟩
      length prefix +ℕ the-len-f +ℕ 1
      ∎

    -- prog-eq-f: prefix ++ code-f ++ suffix-f ≡ prog
    -- suffix-f = nop ∷ code-g ++ suffix
    -- code-f ++ suffix-f = code-f ++ nop ∷ code-g ++ suffix
    -- But compile-aarch64 (g ∘ f) = code-f ++ nop ∷ code-g by definition
    -- So prog = prefix ++ (code-f ++ nop ∷ code-g) ++ suffix
    the-prog-eq-f : prefix ++ the-code-f ++ the-suffix-f ≡ the-prog
    the-prog-eq-f = cong (prefix ++_) (sym (++-assoc the-code-f (nop ∷ the-code-g) suffix))

    -- prog-eq-nop: prefix-nop ++ nop ∷ suffix-nop ≡ prog
    -- prefix-nop = prefix ++ code-f
    -- suffix-nop = code-g ++ suffix
    -- (prefix ++ code-f) ++ nop ∷ (code-g ++ suffix)
    the-prog-eq-nop : the-prefix-nop ++ nop ∷ the-suffix-nop ≡ the-prog
    the-prog-eq-nop = begin
      (prefix ++ the-code-f) ++ nop ∷ (the-code-g ++ suffix)
        ≡⟨ ++-assoc prefix the-code-f _ ⟩
      prefix ++ the-code-f ++ nop ∷ the-code-g ++ suffix
        ≡⟨ cong (prefix ++_) (sym (++-assoc the-code-f (nop ∷ the-code-g) suffix)) ⟩
      prefix ++ (the-code-f ++ nop ∷ the-code-g) ++ suffix
        ≡⟨ refl ⟩  -- compile-aarch64 (g ∘ f) = code-f ++ nop ∷ code-g
      the-prog
      ∎

    -- prog-eq-g: prefix-g ++ code-g ++ suffix ≡ prog
    -- prefix-g = prefix ++ code-f ++ nop ∷ []
    -- Proof: associativity + nop ∷ [] ++ code-g = nop ∷ code-g
    the-prog-eq-g : the-prefix-g ++ the-code-g ++ suffix ≡ the-prog
    the-prog-eq-g = begin
      (prefix ++ the-code-f ++ nop ∷ []) ++ the-code-g ++ suffix
        ≡⟨ ++-assoc prefix (the-code-f ++ nop ∷ []) _ ⟩
      prefix ++ (the-code-f ++ nop ∷ []) ++ the-code-g ++ suffix
        ≡⟨ cong (prefix ++_) (++-assoc the-code-f (nop ∷ []) _) ⟩
      prefix ++ the-code-f ++ (nop ∷ []) ++ the-code-g ++ suffix
        ≡⟨ refl ⟩  -- (nop ∷ []) ++ xs = nop ∷ xs
      prefix ++ the-code-f ++ nop ∷ the-code-g ++ suffix
        ≡⟨ cong (prefix ++_) (sym (++-assoc the-code-f (nop ∷ the-code-g) suffix)) ⟩
      prefix ++ (the-code-f ++ nop ∷ the-code-g) ++ suffix
        ≡⟨ refl ⟩  -- compile-aarch64 (g ∘ f) = code-f ++ nop ∷ code-g
      the-prog
      ∎

------------------------------------------------------------------------
-- Compose Result Assembly: combine f, nop, and g results into final result
--
-- AArch64 has a nop between f and g, so we compose 3 stars: f → nop → g
------------------------------------------------------------------------

-- | Assemble the final compose result from f, nop, and g results
--
-- Given:
--   res-f : IRStarResultS f prog s sf addr-in (length prefix)
--   star-nop : Star prog sf s-nop  (nop execution)
--   res-g : IRStarResultS g prog s-nop sg addr-out (length prefix-g)
-- Produce:
--   IRStarResultS (g ∘ f) prog s sg addr-out (length prefix)
--
-- Key differences from RISC-V:
--   1. 3-way star composition (f → nop → g) instead of 2-way
--   2. Uses IRStarResultS (not IRStarResult) with StackInvariant
--   3. Uses readSP instead of readReg sp
--   4. Chains memory invariants (ir-mem-x21, ir-mem-x29, ir-mem-x29+8)
assemble-compose-result : ∀ {A B C} (f : IR A B) (g : IR B C)
                          (prefix suffix : Program) (addr-in : Word)
                          (s sf s-nop sg : State) →
  let ctx = mkComposeContext f g prefix suffix
      theProg = ComposeContext.prog ctx
      thePrefixG = ComposeContext.prefix-g ctx
  in
  (res-f : IRStarResultS f theProg s sf addr-in (length prefix)) →
  (star-nop : Star theProg sf s-nop) →
  (res-g : IRStarResultS g theProg s-nop sg addr-in (length thePrefixG)) →
  -- Nop register preservation properties
  (nop-x20 : readReg (regs s-nop) x20 ≡ readReg (regs sf) x20) →
  (nop-x21 : readReg (regs s-nop) x21 ≡ readReg (regs sf) x21) →
  (nop-x29 : readReg (regs s-nop) x29 ≡ readReg (regs sf) x29) →
  (nop-x30 : readReg (regs s-nop) x30 ≡ readReg (regs sf) x30) →
  (nop-sp : readSP (regs s-nop) ≡ readSP (regs sf)) →
  -- Nop memory preservation properties
  (nop-mem-x21 : ∀ addr → readMem (memory s-nop) addr ≡ readMem (memory sf) addr) →
  (nop-mem-x29 : ∀ addr → readMem (memory s-nop) addr ≡ readMem (memory sf) addr) →
  IRStarResultS (g ∘ f) theProg s sg addr-in (length prefix)
assemble-compose-result {A} {B} {C} f g prefix suffix addr-in s sf s-nop sg
  res-f star-nop res-g nop-x20 nop-x21 nop-x29 nop-x30 nop-sp nop-mem-x21 nop-mem-x29 = record
  { ir-star = star-all
  ; ir-halted = hg
  ; ir-pc = pcg
  ; ir-x0-s = x0-g
  ; ir-x20 = x20-final
  ; ir-x21 = x21-final
  ; ir-x29 = x29-final
  ; ir-x30 = x30-final
  ; ir-sp = sp-final
  ; ir-mem-x21 = mem-x21-final
  ; ir-mem-x29 = mem-x29-final
  ; ir-mem-x29+8 = mem-x29+8-final
  ; ir-stack-inv = IRStarResultS.ir-stack-inv res-g
  ; ir-x29-inv = IRStarResultS.ir-x29-inv res-g
  ; ir-sp-bound = IRStarResultS.ir-sp-bound res-g
  ; ir-closure-entry = nothing
  }
  where
    ctx = mkComposeContext f g prefix suffix
    theProg = ComposeContext.prog ctx
    theLen-f = ComposeContext.len-f ctx
    theLen-g = ComposeContext.len-g ctx
    thePrefix-g = ComposeContext.prefix-g ctx
    theLen-prefix-g = ComposeContext.len-prefix-g ctx
    open IRStarResultS

    -- From res-f (f result)
    star-f : Star theProg s sf
    star-f = ir-star res-f
    x20-f : readReg (regs sf) x20 ≡ readReg (regs s) x20
    x20-f = ir-x20 res-f
    x21-f : readReg (regs sf) x21 ≡ readReg (regs s) x21
    x21-f = ir-x21 res-f
    x29-f : readReg (regs sf) x29 ≡ readReg (regs s) x29
    x29-f = ir-x29 res-f
    x30-f : readReg (regs sf) x30 ≡ readReg (regs s) x30
    x30-f = ir-x30 res-f

    -- From res-g (g result)
    star-g : Star theProg s-nop sg
    star-g = ir-star res-g
    hg : halted sg ≡ false
    hg = ir-halted res-g
    x0-g : readReg (regs sg) x0 ≡ addr-in
    x0-g = ir-x0-s res-g
    x20-g : readReg (regs sg) x20 ≡ readReg (regs s-nop) x20
    x20-g = ir-x20 res-g
    x21-g : readReg (regs sg) x21 ≡ readReg (regs s-nop) x21
    x21-g = ir-x21 res-g
    x29-g : readReg (regs sg) x29 ≡ readReg (regs s-nop) x29
    x29-g = ir-x29 res-g
    x30-g : readReg (regs sg) x30 ≡ readReg (regs s-nop) x30
    x30-g = ir-x30 res-g

    -- Compose Star proofs (3-way: f → nop → g)
    star-f-nop : Star theProg s s-nop
    star-f-nop = star-trans star-f star-nop

    star-all : Star theProg s sg
    star-all = star-trans star-f-nop star-g

    -- Final pc
    pcg : pc sg ≡ length prefix +ℕ compile-length (g ∘ f)
    pcg = begin
      pc sg
        ≡⟨ ir-pc res-g ⟩
      length thePrefix-g +ℕ theLen-g
        ≡⟨ cong (_+ℕ theLen-g) theLen-prefix-g ⟩
      (length prefix +ℕ theLen-f +ℕ 1) +ℕ theLen-g
        ≡⟨ cong (_+ℕ theLen-g) (+-assoc (length prefix) theLen-f 1) ⟩
      (length prefix +ℕ (theLen-f +ℕ 1)) +ℕ theLen-g
        ≡⟨ +-assoc (length prefix) (theLen-f +ℕ 1) theLen-g ⟩
      length prefix +ℕ ((theLen-f +ℕ 1) +ℕ theLen-g)
        ≡⟨ refl ⟩  -- compile-length (g ∘ f) = (theLen-f + 1) + theLen-g
      length prefix +ℕ compile-length (g ∘ f)
        ∎

    -- x20 preservation: chain through f, nop, and g
    x20-final : readReg (regs sg) x20 ≡ readReg (regs s) x20
    x20-final = trans x20-g (trans nop-x20 x20-f)

    -- x21 preservation: chain through f, nop, and g
    x21-final : readReg (regs sg) x21 ≡ readReg (regs s) x21
    x21-final = trans x21-g (trans nop-x21 x21-f)

    -- x29 preservation: chain through f, nop, and g
    x29-final : readReg (regs sg) x29 ≡ readReg (regs s) x29
    x29-final = trans x29-g (trans nop-x29 x29-f)

    -- x30 preservation: chain through f, nop, and g
    x30-final : readReg (regs sg) x30 ≡ readReg (regs s) x30
    x30-final = trans x30-g (trans nop-x30 x30-f)

    -- sp preservation: chain through f, nop, and g
    sp-final : readSP (regs sg) ≤ readSP (regs s)
    sp-final =
      let sp-g-nop : readSP (regs sg) ≤ readSP (regs s-nop)
          sp-g-nop = ir-sp res-g
          sp-nop-f : readSP (regs s-nop) ≡ readSP (regs sf)
          sp-nop-f = nop-sp
          sp-f-s : readSP (regs sf) ≤ readSP (regs s)
          sp-f-s = ir-sp res-f
      in ≤-trans sp-g-nop (≤-trans (≤-reflexive sp-nop-f) sp-f-s)

    -- Memory preservation at x21
    mem-x21-final : readMem (memory sg) (readReg (regs s) x21) ≡ readMem (memory s) (readReg (regs s) x21)
    mem-x21-final = begin
      readMem (memory sg) (readReg (regs s) x21)
        ≡⟨ cong (readMem (memory sg)) (sym x21-final) ⟩
      readMem (memory sg) (readReg (regs sg) x21)
        ≡⟨ cong (readMem (memory sg)) x21-g ⟩
      readMem (memory sg) (readReg (regs s-nop) x21)
        ≡⟨ ir-mem-x21 res-g ⟩
      readMem (memory s-nop) (readReg (regs s-nop) x21)
        ≡⟨ nop-mem-x21 (readReg (regs s-nop) x21) ⟩
      readMem (memory sf) (readReg (regs s-nop) x21)
        ≡⟨ cong (readMem (memory sf)) nop-x21 ⟩
      readMem (memory sf) (readReg (regs sf) x21)
        ≡⟨ cong (readMem (memory sf)) x21-f ⟩
      readMem (memory sf) (readReg (regs s) x21)
        ≡⟨ ir-mem-x21 res-f ⟩
      readMem (memory s) (readReg (regs s) x21)
        ∎

    -- Memory preservation at x29
    mem-x29-final : readMem (memory sg) (readReg (regs s) x29) ≡ readMem (memory s) (readReg (regs s) x29)
    mem-x29-final = begin
      readMem (memory sg) (readReg (regs s) x29)
        ≡⟨ cong (readMem (memory sg)) (sym x29-final) ⟩
      readMem (memory sg) (readReg (regs sg) x29)
        ≡⟨ cong (readMem (memory sg)) x29-g ⟩
      readMem (memory sg) (readReg (regs s-nop) x29)
        ≡⟨ ir-mem-x29 res-g ⟩
      readMem (memory s-nop) (readReg (regs s-nop) x29)
        ≡⟨ nop-mem-x29 (readReg (regs s-nop) x29) ⟩
      readMem (memory sf) (readReg (regs s-nop) x29)
        ≡⟨ cong (readMem (memory sf)) nop-x29 ⟩
      readMem (memory sf) (readReg (regs sf) x29)
        ≡⟨ cong (readMem (memory sf)) x29-f ⟩
      readMem (memory sf) (readReg (regs s) x29)
        ≡⟨ ir-mem-x29 res-f ⟩
      readMem (memory s) (readReg (regs s) x29)
        ∎

    -- Memory preservation at x29+8
    mem-x29+8-final : readMem (memory sg) (readReg (regs s) x29 +ℕ 8) ≡ readMem (memory s) (readReg (regs s) x29 +ℕ 8)
    mem-x29+8-final = begin
      readMem (memory sg) (readReg (regs s) x29 +ℕ 8)
        ≡⟨ cong (λ x → readMem (memory sg) (x +ℕ 8)) (sym x29-final) ⟩
      readMem (memory sg) (readReg (regs sg) x29 +ℕ 8)
        ≡⟨ cong (λ x → readMem (memory sg) (x +ℕ 8)) x29-g ⟩
      readMem (memory sg) (readReg (regs s-nop) x29 +ℕ 8)
        ≡⟨ ir-mem-x29+8 res-g ⟩
      readMem (memory s-nop) (readReg (regs s-nop) x29 +ℕ 8)
        ≡⟨ nop-mem-x29 (readReg (regs s-nop) x29 +ℕ 8) ⟩
      readMem (memory sf) (readReg (regs s-nop) x29 +ℕ 8)
        ≡⟨ cong (λ x → readMem (memory sf) (x +ℕ 8)) nop-x29 ⟩
      readMem (memory sf) (readReg (regs sf) x29 +ℕ 8)
        ≡⟨ cong (λ x → readMem (memory sf) (x +ℕ 8)) x29-f ⟩
      readMem (memory sf) (readReg (regs s) x29 +ℕ 8)
        ≡⟨ ir-mem-x29+8 res-f ⟩
      readMem (memory s) (readReg (regs s) x29 +ℕ 8)
        ∎

------------------------------------------------------------------------
-- Arithmetic Lemmas
------------------------------------------------------------------------

-- | (len-f + 1) + len-g = compile-length (g ∘ f)
-- This is immediate from the definition of compile-length for compose
arith-compose-total : ∀ {A B C : Type} (f : IR A B) (g : IR B C) →
  (compile-length f +ℕ 1) +ℕ compile-length g ≡ compile-length (g ∘ f)
arith-compose-total f g = refl

-- | length prefix + len-f + 1 + len-g = length prefix + compile-length (g ∘ f)
arith-compose-pc : ∀ p len-f len-g →
  p +ℕ len-f +ℕ 1 +ℕ len-g ≡ p +ℕ ((len-f +ℕ 1) +ℕ len-g)
arith-compose-pc p len-f len-g = begin
  p +ℕ len-f +ℕ 1 +ℕ len-g
    ≡⟨ +-assoc (p +ℕ len-f) 1 len-g ⟩
  (p +ℕ len-f) +ℕ (1 +ℕ len-g)
    ≡⟨ cong ((p +ℕ len-f) +ℕ_) (+-comm 1 len-g) ⟩
  (p +ℕ len-f) +ℕ (len-g +ℕ 1)
    ≡⟨ sym (+-assoc (p +ℕ len-f) len-g 1) ⟩
  p +ℕ len-f +ℕ len-g +ℕ 1
    ≡⟨ cong (_+ℕ 1) (+-assoc p len-f len-g) ⟩
  p +ℕ (len-f +ℕ len-g) +ℕ 1
    ≡⟨ cong (_+ℕ 1) (cong (p +ℕ_) (+-comm len-f len-g)) ⟩
  p +ℕ (len-g +ℕ len-f) +ℕ 1
    ≡⟨ cong (_+ℕ 1) (sym (+-assoc p len-g len-f)) ⟩
  p +ℕ len-g +ℕ len-f +ℕ 1
    ≡⟨ +-assoc (p +ℕ len-g) len-f 1 ⟩
  (p +ℕ len-g) +ℕ (len-f +ℕ 1)
    ≡⟨ +-comm (p +ℕ len-g) (len-f +ℕ 1) ⟩
  (len-f +ℕ 1) +ℕ (p +ℕ len-g)
    ≡⟨ sym (+-assoc (len-f +ℕ 1) p len-g) ⟩
  (len-f +ℕ 1) +ℕ p +ℕ len-g
    ≡⟨ cong (_+ℕ len-g) (+-comm (len-f +ℕ 1) p) ⟩
  p +ℕ (len-f +ℕ 1) +ℕ len-g
    ≡⟨ +-assoc p (len-f +ℕ 1) len-g ⟩
  p +ℕ ((len-f +ℕ 1) +ℕ len-g)
  ∎

------------------------------------------------------------------------
-- ComposeResultS: Stateful version with optional WF threading
------------------------------------------------------------------------

-- | Stateful compose result with optional closure well-formedness
-- Like assemble-compose-result but includes optional ClosureWellFormedS.
-- This threads well-formedness from g (or f if g doesn't produce a closure).
--
-- Key differences:
-- 1. Returns explicit address (not encode)
-- 2. Optionally threads ClosureWellFormedS if g produces a closure
-- 3. Matches IRStarResultS structure for uniform composition
record ComposeResultS {A B C} (f : IR A B) (g : IR B C)
                      (prefix suffix : Program)
                      (s s' : State) (addr-out : Word) : Set where
  field
    -- All IRStarResultS fields
    compose-star       : Star (prefix ++ compile-aarch64 (g ∘ f) ++ suffix) s s'
    compose-halted     : halted s' ≡ false
    compose-pc         : pc s' ≡ length prefix +ℕ compile-length (g ∘ f)
    compose-x0-s       : readReg (regs s') x0 ≡ addr-out

    -- Register preservation
    compose-x20        : readReg (regs s') x20 ≡ readReg (regs s) x20
    compose-x21        : readReg (regs s') x21 ≡ readReg (regs s) x21
    compose-x29        : readReg (regs s') x29 ≡ readReg (regs s) x29
    compose-x30        : readReg (regs s') x30 ≡ readReg (regs s) x30
    compose-sp         : readSP (regs s') ≤ readSP (regs s)

    -- Memory preservation
    compose-mem-x21    : readMem (memory s') (readReg (regs s) x21) ≡
                         readMem (memory s) (readReg (regs s) x21)
    compose-mem-x29    : readMem (memory s') (readReg (regs s) x29) ≡
                         readMem (memory s) (readReg (regs s) x29)
    compose-mem-x29+8  : readMem (memory s') (readReg (regs s) x29 +ℕ 8) ≡
                         readMem (memory s) (readReg (regs s) x29 +ℕ 8)

    -- Invariants
    compose-stack-inv  : StackInvariant s'
    compose-x29-inv    : X29Invariant s'
    compose-sp-bound   : readSP (regs s') > 16

    -- Phase 1: WF threading is optional and postulated
    -- In Phase 2, we'll implement actual WF propagation if g produces a closure
    -- For now, this is a placeholder to enable the type structure

open ComposeResultS public
