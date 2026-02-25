------------------------------------------------------------------------
-- Once.CCC.Target.RiscV64.Correct.IR.Compose
--
-- Helper records and functions for compose proofs.
-- Extracts non-recursive parts to reduce mutual block compilation time.
-- The recursive calls stay in MutualIR.agda.
--
-- RISC-V simplification over X86:
--   a0 is BOTH input and output, so NO transfer instruction needed!
--   compile-riscv (g ∘ f) = compile-riscv f ++ compile-riscv g
------------------------------------------------------------------------

{-# OPTIONS --sized-types #-}

module Once.CCC.Target.RiscV64.Correct.IR.Compose where

open import Size
open import Once.Type
open import Once.IRS
open import Once.SemanticsS

open import Once.Target.RiscV64.Syntax
open import Once.Target.RiscV64.Semantics
open State
open import Once.CCC.Target.RiscV64.CodeGen

open import Once.CCC.Target.RiscV64.Correct.CompileLength
open import Once.CCC.Target.RiscV64.Correct.Star
  using (Star; star-trans)
open import Once.CCC.Target.RiscV64.Correct.StarBase
  using (IRStarResult;
         ir-star; ir-halted; ir-pc; ir-a0; ir-s1; ir-s2; ir-ra; ir-sp-delta; ir-sp-delta-leq; ir-sp;
         ir-mem-preserved; ir-output-wf)

open import Data.Bool using (false)
open import Data.Nat using (ℕ; zero; suc; _≤_) renaming (_+_ to _+ℕ_)
open import Data.Nat.Properties using (+-assoc; +-comm; +-mono-≤)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.List.Properties using (++-assoc) renaming (length-++ to List-length-++)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; ∃-syntax)
open import Data.Maybe using (just)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong; cong₂)
open import Relation.Binary.PropositionalEquality.Properties using (module ≡-Reasoning)
open ≡-Reasoning

------------------------------------------------------------------------
-- Compose Context: computed values that don't depend on execution
--
-- For RISC-V, compose is simpler than X86:
--   compile-riscv (g ∘ f) = compile-riscv f ++ compile-riscv g
--   No transfer instruction needed!
------------------------------------------------------------------------

record ComposeContext {i : Size} {A B C : Type} (f : IR i A B) (g : IR i B C)
                      (prefix suffix : Program) : Set where
  field
    -- Computed programs
    code-f : Program
    code-g : Program
    prog : Program
    suffix-f : Program
    prefix-g : Program

    -- Length values
    len-f : ℕ
    len-g : ℕ

    -- Program equalities
    -- prog ≡ prefix ++ code-f ++ suffix-f
    prog-eq-f : prog ≡ prefix ++ code-f ++ suffix-f

    -- prefix ++ code-f ++ suffix-f ≡ prefix-g ++ code-g ++ suffix
    prog-eq-g : prefix ++ code-f ++ suffix-f ≡ prefix-g ++ code-g ++ suffix

    -- Length equalities
    len-prefix-g : length prefix-g ≡ length prefix +ℕ len-f

-- | Compute the compose context (all the non-state-dependent values)
make-compose-context : ∀ {i A B C} (f : IR i A B) (g : IR i B C) (prefix suffix : Program) →
  ComposeContext f g prefix suffix
make-compose-context {_} {A} {B} {C} f g prefix suffix = record
  { code-f = code-f
  ; code-g = code-g
  ; prog = prog
  ; suffix-f = suffix-f
  ; prefix-g = prefix-g
  ; len-f = len-f
  ; len-g = len-g
  ; prog-eq-f = prog-eq-f
  ; prog-eq-g = prog-eq-g
  ; len-prefix-g = len-prefix-g
  }
  where
    len-f = compile-length f
    len-g = compile-length g
    code-f = compile-riscv f
    code-g = compile-riscv g
    prog = prefix ++ compile-riscv (g ∘ f) ++ suffix
    suffix-f = code-g ++ suffix
    prefix-g = prefix ++ code-f

    -- prog ≡ prefix ++ (code-f ++ code-g) ++ suffix
    --      ≡ prefix ++ code-f ++ (code-g ++ suffix)
    --      ≡ prefix ++ code-f ++ suffix-f
    prog-eq-f : prog ≡ prefix ++ code-f ++ suffix-f
    prog-eq-f = cong (prefix ++_) (++-assoc code-f code-g suffix)

    -- prefix ++ code-f ++ suffix-f
    --   ≡ prefix ++ code-f ++ (code-g ++ suffix)
    --   ≡ (prefix ++ code-f) ++ (code-g ++ suffix)
    --   ≡ prefix-g ++ code-g ++ suffix
    prog-eq-g : prefix ++ code-f ++ suffix-f ≡ prefix-g ++ code-g ++ suffix
    prog-eq-g = sym (++-assoc prefix code-f suffix-f)

    len-prefix-g : length prefix-g ≡ length prefix +ℕ len-f
    len-prefix-g = trans (List-length-++ prefix {code-f})
                         (cong (length prefix +ℕ_) (compile-length-correct f))

------------------------------------------------------------------------
-- Compose Result Assembly: combine f and g results into final result
--
-- Given:
--   r1 : IRStarResult f prog s sf x offset
--   r2 : IRStarResult g prog sf sg (eval f x) (offset + len-f)
-- Produce:
--   IRStarResult (g ∘ f) prog s sg x offset
------------------------------------------------------------------------

-- | Assemble the final compose result from f and g results
assemble-compose-result : ∀ {i A B C} (f : IR i A B) (g : IR i B C)
                          (prefix suffix : Program) (x : ⟦ A ⟧) (s sf sg : State) →
  let ctx = make-compose-context f g prefix suffix in
  let open ComposeContext ctx in
  (r1 : IRStarResult f prog s sf x (length prefix)) →
  (r2 : IRStarResult g prog sf sg (eval f x) (length prefix-g)) →
  IRStarResult (g ∘ f) prog s sg x (length prefix)
assemble-compose-result {_} {A} {B} {C} f g prefix suffix x s sf sg r1 r2 = record
  { ir-star = star-all
  ; ir-halted = hg
  ; ir-pc = pcg
  ; ir-a0 = a0-g
  ; ir-s1 = s1-final
  ; ir-s2 = s2-final
  ; ir-ra = ra-final
  ; ir-sp-delta = ir-sp-delta r1 +ℕ ir-sp-delta r2
  ; ir-sp-delta-leq = sp-delta-leq
  ; ir-sp = sp-final
  ; ir-mem-preserved = mem-preserved-final
  ; ir-output-wf = ir-output-wf r2  -- g's output WF is the compose output WF
  }
  where
    ctx = make-compose-context f g prefix suffix
    open ComposeContext ctx

    -- Stack delta: ir-sp-delta ≤ StackDelta (g ∘ f) = StackDelta f + StackDelta g
    sp-delta-leq : ir-sp-delta r1 +ℕ ir-sp-delta r2 ≤ StackDelta (g ∘ f)
    sp-delta-leq = +-mono-≤ (ir-sp-delta-leq r1) (ir-sp-delta-leq r2)

    -- From r1 (f result)
    star-f : Star prog s sf
    star-f = ir-star r1
    s1-f : readReg (regs sf) s1 ≡ readReg (regs s) s1
    s1-f = ir-s1 r1
    s2-f : readReg (regs sf) s2 ≡ readReg (regs s) s2
    s2-f = ir-s2 r1
    ra-f : readReg (regs sf) ra ≡ readReg (regs s) ra
    ra-f = ir-ra r1

    -- From r2 (g result)
    star-g : Star prog sf sg
    star-g = ir-star r2
    hg : halted sg ≡ false
    hg = ir-halted r2
    a0-g : readReg (regs sg) a0 ≡ encode (eval g (eval f x))
    a0-g = ir-a0 r2
    s1-g : readReg (regs sg) s1 ≡ readReg (regs sf) s1
    s1-g = ir-s1 r2
    s2-g : readReg (regs sg) s2 ≡ readReg (regs sf) s2
    s2-g = ir-s2 r2
    ra-g : readReg (regs sg) ra ≡ readReg (regs sf) ra
    ra-g = ir-ra r2

    -- Compose Star proofs (trivial with Star - just transitivity!)
    star-all : Star prog s sg
    star-all = star-trans star-f star-g

    -- Final pc
    pcg : pc sg ≡ length prefix +ℕ compile-length (g ∘ f)
    pcg = begin
      pc sg
        ≡⟨ ir-pc r2 ⟩
      length prefix-g +ℕ len-g
        ≡⟨ cong (_+ℕ len-g) len-prefix-g ⟩
      (length prefix +ℕ len-f) +ℕ len-g
        ≡⟨ +-assoc (length prefix) len-f len-g ⟩
      length prefix +ℕ (len-f +ℕ len-g)
        ∎

    -- s1 preservation: chain through f and g
    s1-final : readReg (regs sg) s1 ≡ readReg (regs s) s1
    s1-final = trans s1-g s1-f

    -- s2 preservation: chain through f and g
    s2-final : readReg (regs sg) s2 ≡ readReg (regs s) s2
    s2-final = trans s2-g s2-f

    -- ra preservation: chain through f and g
    ra-final : readReg (regs sg) ra ≡ readReg (regs s) ra
    ra-final = trans ra-g ra-f

    -- sp with delta: f allocates delta_f, g allocates delta_g
    -- f: sf.sp + delta_f ≡ s.sp
    -- g: sg.sp + delta_g ≡ sf.sp
    -- compose: sg.sp + (delta_f + delta_g) ≡ s.sp
    delta-f = ir-sp-delta r1
    delta-g = ir-sp-delta r2

    sp-final : readReg (regs sg) sp +ℕ (delta-f +ℕ delta-g) ≡ readReg (regs s) sp
    sp-final = begin
      readReg (regs sg) sp +ℕ (delta-f +ℕ delta-g)
        ≡⟨ cong (readReg (regs sg) sp +ℕ_) (+-comm delta-f delta-g) ⟩
      readReg (regs sg) sp +ℕ (delta-g +ℕ delta-f)
        ≡⟨ sym (+-assoc (readReg (regs sg) sp) delta-g delta-f) ⟩
      (readReg (regs sg) sp +ℕ delta-g) +ℕ delta-f
        ≡⟨ cong (_+ℕ delta-f) (ir-sp r2) ⟩
      readReg (regs sf) sp +ℕ delta-f
        ≡⟨ ir-sp r1 ⟩
      readReg (regs s) sp
        ∎

    -- Memory preservation at sp and above (universally quantified)
    -- Key insight: s.sp = sf.sp + delta-f (from ir-sp r1)
    -- So s.sp + n = sf.sp + (delta-f + n)
    -- Chain: ir-mem-preserved r2 (delta-f + n) then ir-mem-preserved r1 n
    mem-preserved-final : ∀ n → readMem (memory sg) (readReg (regs s) sp +ℕ n) ≡ readMem (memory s) (readReg (regs s) sp +ℕ n)
    mem-preserved-final n = begin
      readMem (memory sg) (readReg (regs s) sp +ℕ n)
        ≡⟨ cong (readMem (memory sg)) (sym (cong (_+ℕ n) (ir-sp r1))) ⟩
      readMem (memory sg) ((readReg (regs sf) sp +ℕ delta-f) +ℕ n)
        ≡⟨ cong (readMem (memory sg)) (+-assoc (readReg (regs sf) sp) delta-f n) ⟩
      readMem (memory sg) (readReg (regs sf) sp +ℕ (delta-f +ℕ n))
        ≡⟨ ir-mem-preserved r2 (delta-f +ℕ n) ⟩
      readMem (memory sf) (readReg (regs sf) sp +ℕ (delta-f +ℕ n))
        ≡⟨ cong (readMem (memory sf)) (sym (+-assoc (readReg (regs sf) sp) delta-f n)) ⟩
      readMem (memory sf) ((readReg (regs sf) sp +ℕ delta-f) +ℕ n)
        ≡⟨ cong (λ x → readMem (memory sf) (x +ℕ n)) (ir-sp r1) ⟩
      readMem (memory sf) (readReg (regs s) sp +ℕ n)
        ≡⟨ ir-mem-preserved r1 n ⟩
      readMem (memory s) (readReg (regs s) sp +ℕ n)
        ∎

------------------------------------------------------------------------
-- Helper for getting f's result in the right program
------------------------------------------------------------------------

-- | Transform an IRStarResult for f in (prefix ++ code-f ++ suffix-f)
--   to one in prog
transform-f-result : ∀ {i A B C} (f : IR i A B) (g : IR i B C)
                     (prefix suffix : Program) (x : ⟦ A ⟧) (s sf : State) →
  let ctx = make-compose-context f g prefix suffix in
  let open ComposeContext ctx in
  IRStarResult f (prefix ++ code-f ++ suffix-f) s sf x (length prefix) →
  IRStarResult f prog s sf x (length prefix)
transform-f-result {_} {A} {B} {C} f g prefix suffix x s sf r = record
  { ir-star = subst (λ p → Star p s sf) (sym prog-eq-f) (ir-star r)
  ; ir-halted = ir-halted r
  ; ir-pc = ir-pc r
  ; ir-a0 = ir-a0 r
  ; ir-s1 = ir-s1 r
  ; ir-s2 = ir-s2 r
  ; ir-ra = ir-ra r
  ; ir-sp-delta = ir-sp-delta r
  ; ir-sp-delta-leq = ir-sp-delta-leq r
  ; ir-sp = ir-sp r
  ; ir-mem-preserved = ir-mem-preserved r
  ; ir-output-wf = subst (ClosuresWF B) (sym prog-eq-f) (ir-output-wf r)
  }
  where
    ctx = make-compose-context f g prefix suffix
    open ComposeContext ctx
    open import Once.CCC.Target.RiscV64.Correct.ClosureWellFormed using (ClosuresWF)

-- | Transform an IRStarResult for g in (prefix-g ++ code-g ++ suffix)
--   to one in prog
transform-g-result : ∀ {i A B C} (f : IR i A B) (g : IR i B C)
                     (prefix suffix : Program) (x : ⟦ A ⟧) (sf sg : State) →
  let ctx = make-compose-context f g prefix suffix in
  let open ComposeContext ctx in
  IRStarResult g (prefix-g ++ code-g ++ suffix) sf sg (eval f x) (length prefix-g) →
  IRStarResult g prog sf sg (eval f x) (length prefix-g)
transform-g-result {_} {A} {B} {C} f g prefix suffix x sf sg r = record
  { ir-star = subst (λ p → Star p sf sg) (sym (trans prog-eq-f prog-eq-g)) (ir-star r)
  ; ir-halted = ir-halted r
  ; ir-pc = ir-pc r
  ; ir-a0 = ir-a0 r
  ; ir-s1 = ir-s1 r
  ; ir-s2 = ir-s2 r
  ; ir-ra = ir-ra r
  ; ir-sp-delta = ir-sp-delta r
  ; ir-sp-delta-leq = ir-sp-delta-leq r
  ; ir-sp = ir-sp r
  ; ir-mem-preserved = ir-mem-preserved r
  ; ir-output-wf = subst (ClosuresWF C) (sym (trans prog-eq-f prog-eq-g)) (ir-output-wf r)
  }
  where
    ctx = make-compose-context f g prefix suffix
    open ComposeContext ctx
    open import Once.CCC.Target.RiscV64.Correct.ClosureWellFormed using (ClosuresWF)
