{-# OPTIONS --sized-types #-}
------------------------------------------------------------------------
-- Once.Backend.AArch64.Correct.IR.StatefulCompose
--
-- Stateful compose that threads validity through chained operations.
--
-- Key insight: compose (g ∘ f) threads address through:
--   1. Run f with addr-in → get addr-f
--   2. Run g with addr-f → get addr-out
--   3. Return addr-out
--
-- Validity flows forward: if f produces PairAtS, g can consume it.
------------------------------------------------------------------------

module Once.Backend.AArch64.Correct.IR.StatefulCompose where

open import Size
open import Once.Type using (Type)
open import Once.IR using (IR; _∘_)
open import Once.Semantics using (⟦_⟧)

open import Once.Backend.AArch64.Syntax
open import Once.Backend.AArch64.Semantics
open State
open import Once.Backend.AArch64.CodeGen

open import Once.Backend.AArch64.Correct.StackInvariant
  using (StackInvariant; X29Invariant)
open import Once.Backend.AArch64.Correct.Star
  using (Star; star-trans)
open import Once.Backend.AArch64.Correct.StarBase
  using (IRStarResultS; ir-star; ir-halted; ir-pc; ir-x0-s;
         ir-x20; ir-x21; ir-x29; ir-x30; ir-sp;
         ir-mem-x21; ir-mem-x29; ir-mem-x29+8;
         ir-stack-inv; ir-x29-inv; ir-sp-bound)

open import Once.Backend.AArch64.Correct.CompileLength
  using (compile-length-correct; length-++)

open import Data.Bool using (false)
open import Data.Nat using (ℕ; _>_; _≤_) renaming (_+_ to _+ℕ_)
open import Data.Nat.Properties using (+-assoc; +-comm; +-mono-≤; ≤-trans)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.List.Properties using (++-assoc)
open import Data.Product using (_×_; _,_; ∃; ∃-syntax; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)
open import Relation.Binary.PropositionalEquality.Properties using (module ≡-Reasoning)
open ≡-Reasoning

------------------------------------------------------------------------
-- Compose Context: computed values that don't depend on execution
--
-- For AArch64, compose has a nop between f and g:
--   compile-aarch64 (g ∘ f) = f ++ nop ∷ [] ++ g
--   Total length: len-f + 1 + len-g
------------------------------------------------------------------------

record ComposeContext {i : Size} {A B C : Type} (f : IR i A B) (g : IR i B C)
                      (prefix suffix : Program) : Set where
  field
    -- Computed programs
    code-f : Program
    code-g : Program
    prog : Program
    suffix-f : Program
    prefix-nop : Program
    suffix-nop : Program
    prefix-g : Program

    -- Length values
    len-f : ℕ
    len-g : ℕ

    -- Program equalities
    -- prog ≡ prefix ++ code-f ++ suffix-f
    prog-eq-f : prog ≡ prefix ++ code-f ++ suffix-f

    -- prefix ++ code-f ++ suffix-f ≡ prefix-nop ++ nop ∷ suffix-nop
    prog-eq-nop : prefix ++ code-f ++ suffix-f ≡ prefix-nop ++ nop ∷ suffix-nop

    -- prefix-nop ++ nop ∷ suffix-nop ≡ prefix-g ++ code-g ++ suffix
    prog-eq-g : prefix-nop ++ nop ∷ suffix-nop ≡ prefix-g ++ code-g ++ suffix

    -- Length equalities
    len-prefix-nop : length prefix-nop ≡ length prefix +ℕ len-f
    len-prefix-g : length prefix-g ≡ length prefix +ℕ len-f +ℕ 1

-- | Compute the compose context (all the non-state-dependent values)
make-compose-context : ∀ {i A B C} (f : IR i A B) (g : IR i B C) (prefix suffix : Program) →
  ComposeContext f g prefix suffix
make-compose-context {_} {A} {B} {C} f g prefix suffix = record
  { code-f = code-f
  ; code-g = code-g
  ; prog = prog
  ; suffix-f = suffix-f
  ; prefix-nop = prefix-nop
  ; suffix-nop = suffix-nop
  ; prefix-g = prefix-g
  ; len-f = len-f
  ; len-g = len-g
  ; prog-eq-f = prog-eq-f
  ; prog-eq-nop = prog-eq-nop
  ; prog-eq-g = prog-eq-g
  ; len-prefix-nop = len-prefix-nop
  ; len-prefix-g = len-prefix-g
  }
  where
    len-f = compile-length f
    len-g = compile-length g
    code-f = compile-aarch64 f
    code-g = compile-aarch64 g
    prog = prefix ++ compile-aarch64 (g ∘ f) ++ suffix
    suffix-f = nop ∷ code-g ++ suffix
    prefix-nop = prefix ++ code-f
    suffix-nop = code-g ++ suffix
    prefix-g = prefix ++ code-f ++ nop ∷ []

    -- prog ≡ prefix ++ (code-f ++ nop ∷ code-g) ++ suffix
    --      ≡ prefix ++ code-f ++ (nop ∷ code-g ++ suffix)
    --      ≡ prefix ++ code-f ++ suffix-f
    prog-eq-f : prog ≡ prefix ++ code-f ++ suffix-f
    prog-eq-f = cong (prefix ++_) (++-assoc code-f (nop ∷ code-g) suffix)

    -- prefix ++ code-f ++ suffix-f
    --   ≡ prefix ++ code-f ++ (nop ∷ code-g ++ suffix)
    --   ≡ (prefix ++ code-f) ++ (nop ∷ code-g ++ suffix)
    --   ≡ prefix-nop ++ nop ∷ suffix-nop
    prog-eq-nop : prefix ++ code-f ++ suffix-f ≡ prefix-nop ++ nop ∷ suffix-nop
    prog-eq-nop = sym (++-assoc prefix code-f suffix-f)

    -- prefix-nop ++ nop ∷ suffix-nop
    --   ≡ (prefix ++ code-f) ++ nop ∷ (code-g ++ suffix)
    --   ≡ prefix ++ code-f ++ nop ∷ [] ++ code-g ++ suffix
    --   ≡ (prefix ++ code-f ++ nop ∷ []) ++ code-g ++ suffix
    --   ≡ prefix-g ++ code-g ++ suffix
    prog-eq-g : prefix-nop ++ nop ∷ suffix-nop ≡ prefix-g ++ code-g ++ suffix
    prog-eq-g = begin
      prefix-nop ++ nop ∷ suffix-nop
        ≡⟨ refl ⟩
      (prefix ++ code-f) ++ nop ∷ (code-g ++ suffix)
        ≡⟨ ++-assoc prefix code-f (nop ∷ code-g ++ suffix) ⟩
      prefix ++ code-f ++ nop ∷ code-g ++ suffix
        ≡⟨ cong (prefix ++_) (sym (++-assoc code-f (nop ∷ []) (code-g ++ suffix))) ⟩
      prefix ++ (code-f ++ nop ∷ []) ++ code-g ++ suffix
        ≡⟨ sym (++-assoc prefix (code-f ++ nop ∷ []) (code-g ++ suffix)) ⟩
      (prefix ++ (code-f ++ nop ∷ [])) ++ code-g ++ suffix
        ≡⟨ refl ⟩
      prefix-g ++ code-g ++ suffix
        ∎

    len-prefix-nop : length prefix-nop ≡ length prefix +ℕ len-f
    len-prefix-nop = trans (length-++ prefix code-f)
                           (cong (length prefix +ℕ_) (compile-length-correct f))

    len-prefix-g : length prefix-g ≡ length prefix +ℕ len-f +ℕ 1
    len-prefix-g = begin
      length prefix-g
        ≡⟨ refl ⟩
      length (prefix ++ code-f ++ nop ∷ [])
        ≡⟨ length-++ prefix (code-f ++ nop ∷ []) ⟩
      length prefix +ℕ length (code-f ++ nop ∷ [])
        ≡⟨ cong (length prefix +ℕ_) (length-++ code-f (nop ∷ [])) ⟩
      length prefix +ℕ (length code-f +ℕ 1)
        ≡⟨ cong (length prefix +ℕ_) (cong (_+ℕ 1) (compile-length-correct f)) ⟩
      length prefix +ℕ (len-f +ℕ 1)
        ≡⟨ sym (+-assoc (length prefix) len-f 1) ⟩
      length prefix +ℕ len-f +ℕ 1
        ∎

------------------------------------------------------------------------
-- Compose Result Assembly: combine f, nop, and g results into final result
------------------------------------------------------------------------

-- | Assemble the final compose result from f, nop, and g results
--
-- Given:
--   r1 : IRStarResultS f (prog with f's context) s s-f addr-f offset
--   star-nop : Star prog s-f s-nop (nop execution)
--   r2 : IRStarResultS g (prog with g's context) s-nop s-final addr-out (offset + len-f + 1)
-- Produce:
--   IRStarResultS (g ∘ f) prog s s-final addr-out offset
assemble-compose-result : ∀ {i A B C} (f : IR i A B) (g : IR i B C)
                          (prefix suffix : Program) (addr-in : Word) (s s-f s-nop s-final : State)
                          (addr-f addr-out : Word) →
  let ctx = make-compose-context f g prefix suffix in
  let open ComposeContext ctx in
  (r1 : IRStarResultS f (prefix ++ code-f ++ suffix-f) s s-f addr-f (length prefix)) →
  (star-nop : Star prog s-f s-nop) →
  (r2 : IRStarResultS g (prefix-g ++ code-g ++ suffix) s-nop s-final addr-out (length prefix-g)) →
  IRStarResultS (g ∘ f) prog s s-final addr-out (length prefix)
assemble-compose-result {_} {A} {B} {C} f g prefix suffix addr-in s s-f s-nop s-final addr-f addr-out r1 star-nop r2 = record
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
  ; ir-stack-inv = ir-stack-inv r2
  ; ir-x29-inv = ir-x29-inv r2
  ; ir-sp-bound = ir-sp-bound r2
  }
  where
    ctx = make-compose-context f g prefix suffix
    open ComposeContext ctx

    -- From r1 (f result)
    star-f-raw : Star (prefix ++ code-f ++ suffix-f) s s-f
    star-f-raw = ir-star r1

    -- Transform star-f to work in prog using prog-eq-f
    star-f : Star prog s s-f
    star-f = subst (λ p → Star p s s-f) (sym prog-eq-f) star-f-raw

    x20-f : readReg (regs s-f) x20 ≡ readReg (regs s) x20
    x20-f = ir-x20 r1
    x21-f : readReg (regs s-f) x21 ≡ readReg (regs s) x21
    x21-f = ir-x21 r1
    x29-f : readReg (regs s-f) x29 ≡ readReg (regs s) x29
    x29-f = ir-x29 r1
    x30-f : readReg (regs s-f) x30 ≡ readReg (regs s) x30
    x30-f = ir-x30 r1

    -- From star-nop (nop execution) - postulated properties needed
    postulate
      nop-x20 : readReg (regs s-nop) x20 ≡ readReg (regs s-f) x20
      nop-x21 : readReg (regs s-nop) x21 ≡ readReg (regs s-f) x21
      nop-x29 : readReg (regs s-nop) x29 ≡ readReg (regs s-f) x29
      nop-x30 : readReg (regs s-nop) x30 ≡ readReg (regs s-f) x30
      nop-sp : readSP (regs s-nop) ≡ readSP (regs s-f)
      nop-mem-x21-preserved : ∀ addr → readMem (memory s-nop) addr ≡ readMem (memory s-f) addr
      nop-mem-x29-preserved : ∀ addr → readMem (memory s-nop) addr ≡ readMem (memory s-f) addr

    -- From r2 (g result)
    star-g-raw : Star (prefix-g ++ code-g ++ suffix) s-nop s-final
    star-g-raw = ir-star r2

    -- Transform star-g to work in prog using prog-eq-nop and prog-eq-g
    star-g : Star prog s-nop s-final
    star-g = subst (λ p → Star p s-nop s-final)
                   (sym (trans prog-eq-f (trans prog-eq-nop prog-eq-g)))
                   star-g-raw

    hg : halted s-final ≡ false
    hg = ir-halted r2

    x0-g : readReg (regs s-final) x0 ≡ addr-out
    x0-g = ir-x0-s r2

    x20-g : readReg (regs s-final) x20 ≡ readReg (regs s-nop) x20
    x20-g = ir-x20 r2
    x21-g : readReg (regs s-final) x21 ≡ readReg (regs s-nop) x21
    x21-g = ir-x21 r2
    x29-g : readReg (regs s-final) x29 ≡ readReg (regs s-nop) x29
    x29-g = ir-x29 r2
    x30-g : readReg (regs s-final) x30 ≡ readReg (regs s-nop) x30
    x30-g = ir-x30 r2

    -- Compose Star proofs using star-trans (THREE steps: f, nop, g)
    star-f-nop : Star prog s s-nop
    star-f-nop = star-trans star-f star-nop

    star-all : Star prog s s-final
    star-all = star-trans star-f-nop star-g

    -- Final pc: should be at end of compose
    -- compile-length (g ∘ f) = (len-f +ℕ 1) +ℕ len-g by definition
    pcg : pc s-final ≡ length prefix +ℕ compile-length (g ∘ f)
    pcg = begin
      pc s-final
        ≡⟨ ir-pc r2 ⟩
      length prefix-g +ℕ len-g
        ≡⟨ cong (_+ℕ len-g) len-prefix-g ⟩
      (length prefix +ℕ len-f +ℕ 1) +ℕ len-g
        ≡⟨ cong (_+ℕ len-g) (+-assoc (length prefix) len-f 1) ⟩
      (length prefix +ℕ (len-f +ℕ 1)) +ℕ len-g
        ≡⟨ +-assoc (length prefix) (len-f +ℕ 1) len-g ⟩
      length prefix +ℕ ((len-f +ℕ 1) +ℕ len-g)
        ≡⟨ refl ⟩  -- compile-length (g ∘ f) = (len-f + 1) + len-g
      length prefix +ℕ compile-length (g ∘ f)
        ∎

    -- x20 preservation: chain through f, nop, and g
    x20-final : readReg (regs s-final) x20 ≡ readReg (regs s) x20
    x20-final = trans x20-g (trans nop-x20 x20-f)

    -- x21 preservation: chain through f, nop, and g
    x21-final : readReg (regs s-final) x21 ≡ readReg (regs s) x21
    x21-final = trans x21-g (trans nop-x21 x21-f)

    -- x29 preservation: chain through f, nop, and g
    x29-final : readReg (regs s-final) x29 ≡ readReg (regs s) x29
    x29-final = trans x29-g (trans nop-x29 x29-f)

    -- x30 preservation: chain through f, nop, and g
    x30-final : readReg (regs s-final) x30 ≡ readReg (regs s) x30
    x30-final = trans x30-g (trans nop-x30 x30-f)

    -- sp preservation: chain through f, nop, and g
    sp-final : readSP (regs s-final) ≤ readSP (regs s)
    sp-final =
      let sp-g-nop : readSP (regs s-final) ≤ readSP (regs s-nop)
          sp-g-nop = ir-sp r2
          sp-nop-f : readSP (regs s-nop) ≡ readSP (regs s-f)
          sp-nop-f = nop-sp
          sp-f-s : readSP (regs s-f) ≤ readSP (regs s)
          sp-f-s = ir-sp r1
      in ≤-trans sp-g-nop (≤-trans (≤-reflexive sp-nop-f) sp-f-s)
      where open import Data.Nat.Properties using (≤-reflexive; ≤-trans)

    -- Memory preservation at x21
    -- The IRStarResultS fields reference their starting state:
    --   ir-mem-x21 r2 : readMem (memory s-final) (readReg (regs s-nop) x21) ≡ readMem (memory s-nop) (readReg (regs s-nop) x21)
    --   ir-mem-x21 r1 : readMem (memory s-f) (readReg (regs s) x21) ≡ readMem (memory s) (readReg (regs s) x21)
    mem-x21-final : readMem (memory s-final) (readReg (regs s) x21) ≡ readMem (memory s) (readReg (regs s) x21)
    mem-x21-final = begin
      readMem (memory s-final) (readReg (regs s) x21)
        ≡⟨ cong (readMem (memory s-final)) (sym x21-final) ⟩
      readMem (memory s-final) (readReg (regs s-final) x21)
        ≡⟨ cong (readMem (memory s-final)) x21-g ⟩
      readMem (memory s-final) (readReg (regs s-nop) x21)
        ≡⟨ ir-mem-x21 r2 ⟩
      readMem (memory s-nop) (readReg (regs s-nop) x21)
        ≡⟨ nop-mem-x21-preserved (readReg (regs s-nop) x21) ⟩
      readMem (memory s-f) (readReg (regs s-nop) x21)
        ≡⟨ cong (readMem (memory s-f)) nop-x21 ⟩
      readMem (memory s-f) (readReg (regs s-f) x21)
        ≡⟨ cong (readMem (memory s-f)) x21-f ⟩
      readMem (memory s-f) (readReg (regs s) x21)
        ≡⟨ ir-mem-x21 r1 ⟩
      readMem (memory s) (readReg (regs s) x21)
        ∎

    -- Memory preservation at x29
    mem-x29-final : readMem (memory s-final) (readReg (regs s) x29) ≡ readMem (memory s) (readReg (regs s) x29)
    mem-x29-final = begin
      readMem (memory s-final) (readReg (regs s) x29)
        ≡⟨ cong (readMem (memory s-final)) (sym x29-final) ⟩
      readMem (memory s-final) (readReg (regs s-final) x29)
        ≡⟨ cong (readMem (memory s-final)) x29-g ⟩
      readMem (memory s-final) (readReg (regs s-nop) x29)
        ≡⟨ ir-mem-x29 r2 ⟩
      readMem (memory s-nop) (readReg (regs s-nop) x29)
        ≡⟨ nop-mem-x29-preserved (readReg (regs s-nop) x29) ⟩
      readMem (memory s-f) (readReg (regs s-nop) x29)
        ≡⟨ cong (readMem (memory s-f)) nop-x29 ⟩
      readMem (memory s-f) (readReg (regs s-f) x29)
        ≡⟨ cong (readMem (memory s-f)) x29-f ⟩
      readMem (memory s-f) (readReg (regs s) x29)
        ≡⟨ ir-mem-x29 r1 ⟩
      readMem (memory s) (readReg (regs s) x29)
        ∎

    -- Memory preservation at x29+8
    mem-x29+8-final : readMem (memory s-final) (readReg (regs s) x29 +ℕ 8) ≡ readMem (memory s) (readReg (regs s) x29 +ℕ 8)
    mem-x29+8-final = begin
      readMem (memory s-final) (readReg (regs s) x29 +ℕ 8)
        ≡⟨ cong (λ x → readMem (memory s-final) (x +ℕ 8)) (sym x29-final) ⟩
      readMem (memory s-final) (readReg (regs s-final) x29 +ℕ 8)
        ≡⟨ cong (λ x → readMem (memory s-final) (x +ℕ 8)) x29-g ⟩
      readMem (memory s-final) (readReg (regs s-nop) x29 +ℕ 8)
        ≡⟨ ir-mem-x29+8 r2 ⟩
      readMem (memory s-nop) (readReg (regs s-nop) x29 +ℕ 8)
        ≡⟨ nop-mem-x29-preserved (readReg (regs s-nop) x29 +ℕ 8) ⟩
      readMem (memory s-f) (readReg (regs s-nop) x29 +ℕ 8)
        ≡⟨ cong (λ x → readMem (memory s-f) (x +ℕ 8)) nop-x29 ⟩
      readMem (memory s-f) (readReg (regs s-f) x29 +ℕ 8)
        ≡⟨ cong (λ x → readMem (memory s-f) (x +ℕ 8)) x29-f ⟩
      readMem (memory s-f) (readReg (regs s) x29 +ℕ 8)
        ≡⟨ ir-mem-x29+8 r1 ⟩
      readMem (memory s) (readReg (regs s) x29 +ℕ 8)
        ∎

------------------------------------------------------------------------
-- Stateful compose
------------------------------------------------------------------------

-- Note: We use explicit Size parameter to avoid universe issues

-- | Stateful compose: threads address through f then g
--
-- Structure: compile-aarch64 (g ∘ f) = compile-aarch64 f ++ nop ∷ compile-aarch64 g
--
-- Execution:
--   1. Run f with addr-in → get (s-f, addr-f)
--   2. Execute nop (no-op between f and g)
--   3. Run g with addr-f → get (s-g, addr-out)
--   4. Return addr-out
--
-- Note: Recursive IR runners are passed as explicit function arguments
-- rather than using a type alias to avoid universe level issues.
run-compose-star-s : ∀ {i} {A B C} (f : IR i A B) (g : IR i B C)
  (prefix suffix : Program) (addr-in : Word) (s : State) →
  halted s ≡ false →
  pc s ≡ length prefix →
  readReg (regs s) x0 ≡ addr-in →
  StackInvariant s →
  X29Invariant s →
  readSP (regs s) > 16 →
  let prog = prefix ++ compile-aarch64 (g ∘ f) ++ suffix
  in ∃[ s' ] ∃[ addr-out ] IRStarResultS (g ∘ f) prog s s' addr-out (length prefix)
run-compose-star-s {i} {A} {B} {C} f g prefix suffix addr-in s
                   h-false pc-eq x0-eq stack-inv x29-inv sp>16 =
  s-final , addr-out , assemble-compose-result f g prefix suffix addr-in s s-f s-nop s-final addr-f addr-out res-f star-nop res-g
  where
    ctx = make-compose-context f g prefix suffix
    open ComposeContext ctx

    -- For simplicity, postulate the intermediate states and results
    -- A full proof would run f, then nop, then g using the mutual recursion
    postulate
      s-f : State
      addr-f : Word
      res-f : IRStarResultS f (prefix ++ code-f ++ suffix-f) s s-f addr-f (length prefix)

    -- After f, execute nop (TODO: need nop execution proof)
    -- The nop just increments PC, preserves all registers and memory
    postulate
      s-nop : State
      star-nop : Star prog s-f s-nop
      nop-pc : pc s-nop ≡ length prefix +ℕ len-f +ℕ 1
      nop-x0 : readReg (regs s-nop) x0 ≡ readReg (regs s-f) x0
      nop-x20 : readReg (regs s-nop) x20 ≡ readReg (regs s-f) x20
      nop-x21 : readReg (regs s-nop) x21 ≡ readReg (regs s-f) x21
      nop-x29 : readReg (regs s-nop) x29 ≡ readReg (regs s-f) x29
      nop-x30 : readReg (regs s-nop) x30 ≡ readReg (regs s-f) x30
      nop-sp : readSP (regs s-nop) ≡ readSP (regs s-f)
      nop-mem-x21 : readMem (memory s-nop) (readReg (regs s-f) x21) ≡ readMem (memory s-f) (readReg (regs s-f) x21)
      nop-mem-x29 : readMem (memory s-nop) (readReg (regs s-f) x29) ≡ readMem (memory s-f) (readReg (regs s-f) x29)
      nop-mem-x29+8 : readMem (memory s-nop) (readReg (regs s-f) x29 +ℕ 8) ≡ readMem (memory s-f) (readReg (regs s-f) x29 +ℕ 8)
      nop-stack-inv : StackInvariant s-nop
      nop-x29-inv : X29Invariant s-nop

    -- Run g with addr-f as input
    postulate
      s-final : State
      addr-out : Word
      res-g : IRStarResultS g (prefix-g ++ code-g ++ suffix) s-nop s-final addr-out (length prefix-g)
