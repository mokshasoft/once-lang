------------------------------------------------------------------------
-- Once.Backend.RiscV64.Correct.IR.Pair
--
-- Helper records and functions for pair proofs.
-- Extracts non-recursive parts to reduce mutual block compilation time.
-- The recursive calls stay in MutualIR.agda.
--
-- Pair structure for RISC-V:
--   Phase 1: Setup     (2 instr) - addi sp sp -16; mv s1 a0
--   Phase 2: Execute f (recursive)
--   Phase 3: Middle    (2 instr) - sd a0 0(sp); mv a0 s1
--   Phase 4: Execute g (recursive)
--   Phase 5: Final     (2 instr) - sd a0 8(sp); mv a0 sp
--
-- Total: 6 + len-f + len-g instructions
------------------------------------------------------------------------

module Once.Backend.RiscV64.Correct.IR.Pair where

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
         ir-star; ir-halted; ir-pc; ir-a0; ir-s1; ir-ra)

open import Once.Backend.Common.Memory
  using (readMem-writeMem-same; readMem-writeMem-diff; n≢n+suc)

open import Data.Bool using (false)
open import Data.Nat using (ℕ; zero; suc; _∸_) renaming (_+_ to _+ℕ_)
open import Data.Nat.Properties using (+-assoc; +-comm)
open import Data.Integer using (+_)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.List.Properties using (++-assoc) renaming (length-++ to List-length-++)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; ∃-syntax)
open import Data.Maybe using (just)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; subst; subst₂; cong)
open import Relation.Binary.PropositionalEquality.Properties using (module ≡-Reasoning)
open ≡-Reasoning

------------------------------------------------------------------------
-- Pair Context: computed values that don't depend on execution
------------------------------------------------------------------------

record PairContext {A B C : Type} (f : IR C A) (g : IR C B)
                   (prefix suffix : Program) : Set where
  field
    -- Computed lengths
    len-f : ℕ
    len-g : ℕ

    -- Computed programs
    code-f : Program
    code-g : Program
    prog : Program

    -- Setup instructions (2)
    setup-alloc : Instr    -- addi sp sp -16
    setup-save : Instr     -- mv s1 a0

    -- Middle instructions (2)
    middle-store : Instr   -- sd a0 0(sp)
    middle-restore : Instr -- mv a0 s1

    -- Final instructions (2)
    final-store : Instr    -- sd a0 8(sp)
    final-result : Instr   -- mv a0 sp

    -- Derived prefixes/suffixes
    prefix-f : Program     -- prefix ++ setup
    suffix-f : Program     -- middle ++ code-g ++ final ++ suffix
    prefix-g : Program     -- prefix-f ++ code-f ++ middle
    suffix-g : Program     -- final ++ suffix
    prefix-mid : Program   -- prefix-f ++ code-f
    prefix-final : Program -- prefix-g ++ code-g

    -- Length equalities
    len-prefix-f : length prefix-f ≡ length prefix +ℕ 2
    len-prefix-g : length prefix-g ≡ length prefix +ℕ 4 +ℕ len-f
    len-prefix-mid : length prefix-mid ≡ length prefix +ℕ 2 +ℕ len-f
    len-prefix-final : length prefix-final ≡ length prefix +ℕ 4 +ℕ len-f +ℕ len-g

    -- Program equalities for each phase
    prog-eq-f : prog ≡ prefix-f ++ code-f ++ suffix-f
    prog-eq-g : prog ≡ prefix-g ++ code-g ++ suffix-g

-- | Compute the pair context
make-pair-context : ∀ {A B C} (f : IR C A) (g : IR C B) (prefix suffix : Program) →
  PairContext f g prefix suffix
make-pair-context {A} {B} {C} f g prefix suffix = record
  { len-f = len-f
  ; len-g = len-g
  ; code-f = code-f
  ; code-g = code-g
  ; prog = prog
  ; setup-alloc = setup-alloc
  ; setup-save = setup-save
  ; middle-store = middle-store
  ; middle-restore = middle-restore
  ; final-store = final-store
  ; final-result = final-result
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

    -- Setup instructions (2)
    setup-alloc = addi sp sp neg16
    setup-save = mv s1 a0

    -- Middle instructions (2)
    middle-store = sd a0 (+ 0) sp
    middle-restore = mv a0 s1

    -- Final instructions (2)
    final-store = sd a0 (+ 8) sp
    final-result = mv a0 sp

    -- Final instruction sequence
    final-instrs = final-store ∷ final-result ∷ []

    -- Derived programs
    prefix-f : Program
    prefix-f = prefix ++ setup-alloc ∷ setup-save ∷ []

    suffix-f : Program
    suffix-f = middle-store ∷ middle-restore ∷ code-g ++ final-store ∷ final-result ∷ suffix

    prefix-mid : Program
    prefix-mid = prefix-f ++ code-f

    prefix-g : Program
    prefix-g = (prefix-f ++ code-f) ++ middle-store ∷ middle-restore ∷ []

    suffix-g : Program
    suffix-g = final-store ∷ final-result ∷ suffix

    prefix-final : Program
    prefix-final = prefix-g ++ code-g

    -- Length equalities
    len-prefix-f : length prefix-f ≡ length prefix +ℕ 2
    len-prefix-f = List-length-++ prefix

    len-prefix-mid : length prefix-mid ≡ length prefix +ℕ 2 +ℕ len-f
    len-prefix-mid = begin
      length prefix-mid
        ≡⟨ List-length-++ prefix-f ⟩
      length prefix-f +ℕ length code-f
        ≡⟨ cong (_+ℕ length code-f) len-prefix-f ⟩
      (length prefix +ℕ 2) +ℕ length code-f
        ≡⟨ cong ((length prefix +ℕ 2) +ℕ_) (compile-length-correct f) ⟩
      (length prefix +ℕ 2) +ℕ len-f
        ∎

    len-prefix-g : length prefix-g ≡ length prefix +ℕ 4 +ℕ len-f
    len-prefix-g = begin
      length prefix-g
        ≡⟨ List-length-++ (prefix-f ++ code-f) ⟩
      length (prefix-f ++ code-f) +ℕ 2
        ≡⟨ cong (_+ℕ 2) len-prefix-mid ⟩
      (length prefix +ℕ 2 +ℕ len-f) +ℕ 2
        ≡⟨ +-assoc (length prefix +ℕ 2) len-f 2 ⟩
      (length prefix +ℕ 2) +ℕ (len-f +ℕ 2)
        ≡⟨ +-assoc (length prefix) 2 (len-f +ℕ 2) ⟩
      length prefix +ℕ (2 +ℕ (len-f +ℕ 2))
        ≡⟨ cong (length prefix +ℕ_) (sym (+-assoc 2 len-f 2)) ⟩
      length prefix +ℕ ((2 +ℕ len-f) +ℕ 2)
        ≡⟨ cong (λ x → length prefix +ℕ (x +ℕ 2)) (+-comm 2 len-f) ⟩
      length prefix +ℕ ((len-f +ℕ 2) +ℕ 2)
        ≡⟨ cong (length prefix +ℕ_) (+-assoc len-f 2 2) ⟩
      length prefix +ℕ (len-f +ℕ 4)
        ≡⟨ sym (+-assoc (length prefix) len-f 4) ⟩
      (length prefix +ℕ len-f) +ℕ 4
        ≡⟨ cong (_+ℕ 4) (+-comm (length prefix) len-f) ⟩
      (len-f +ℕ length prefix) +ℕ 4
        ≡⟨ +-assoc len-f (length prefix) 4 ⟩
      len-f +ℕ (length prefix +ℕ 4)
        ≡⟨ +-comm len-f (length prefix +ℕ 4) ⟩
      (length prefix +ℕ 4) +ℕ len-f
        ∎

    len-prefix-final : length prefix-final ≡ length prefix +ℕ 4 +ℕ len-f +ℕ len-g
    len-prefix-final = begin
      length prefix-final
        ≡⟨ List-length-++ prefix-g ⟩
      length prefix-g +ℕ length code-g
        ≡⟨ cong₂ _+ℕ_ len-prefix-g (compile-length-correct g) ⟩
      ((length prefix +ℕ 4) +ℕ len-f) +ℕ len-g
        ∎
      where
        open import Relation.Binary.PropositionalEquality using (cong₂)

    -- Program equality for f
    -- prog = prefix ++ (addi ∷ mv ∷ code-f ++ middle-store ∷ middle-restore ∷ code-g ++ final-instrs) ++ suffix
    -- Need: prog = prefix-f ++ code-f ++ suffix-f
    --     = (prefix ++ addi ∷ mv ∷ []) ++ code-f ++ (middle-store ∷ middle-restore ∷ code-g ++ final-store ∷ final-result ∷ suffix)

    -- Helper: code-g ++ final-instrs ++ suffix = code-g ++ final-store ∷ final-result ∷ suffix
    final-suffix-eq : (code-g ++ final-instrs) ++ suffix ≡ code-g ++ (final-store ∷ final-result ∷ suffix)
    final-suffix-eq = ++-assoc code-g final-instrs suffix

    -- Helper: middle with code-g and final
    middle-suffix-eq : (middle-store ∷ middle-restore ∷ code-g ++ final-instrs) ++ suffix
                     ≡ middle-store ∷ middle-restore ∷ (code-g ++ final-store ∷ final-result ∷ suffix)
    middle-suffix-eq = cong (middle-store ∷_) (cong (middle-restore ∷_) final-suffix-eq)

    -- Helper: code-f with middle, code-g and final
    f-suffix-eq : (code-f ++ middle-store ∷ middle-restore ∷ code-g ++ final-instrs) ++ suffix
                ≡ code-f ++ suffix-f
    f-suffix-eq = trans (++-assoc code-f (middle-store ∷ middle-restore ∷ code-g ++ final-instrs) suffix)
                        (cong (code-f ++_) middle-suffix-eq)

    -- Full program equality for f
    full-suffix-eq : compile-riscv ⟨ f , g ⟩ ++ suffix
                   ≡ setup-alloc ∷ setup-save ∷ (code-f ++ suffix-f)
    full-suffix-eq = cong (setup-alloc ∷_) (cong (setup-save ∷_) f-suffix-eq)

    prog-eq-f : prog ≡ prefix-f ++ code-f ++ suffix-f
    prog-eq-f = trans (cong (prefix ++_) full-suffix-eq)
                      (sym (++-assoc prefix (setup-alloc ∷ setup-save ∷ []) (code-f ++ suffix-f)))

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
-- Phase 1: Setup - trace 2 instructions (addi sp sp -16; mv s1 a0)
------------------------------------------------------------------------

-- | Setup phase: allocate pair space and save input
-- Entry: pc = offset, a0 = encode x
-- Exit: pc = offset + 2, sp = sp - 16, s1 = encode x
pair-setup-star : ∀ {A B C} (f : IR C A) (g : IR C B)
                  (prefix suffix : Program) (x : ⟦ C ⟧) (s : State) →
  let ctx = make-pair-context f g prefix suffix
      open PairContext ctx
      offset = length prefix
  in
  halted s ≡ false →
  pc s ≡ offset →
  readReg (regs s) a0 ≡ encode x →
  ∃[ s' ] (Star prog s s'
          × halted s' ≡ false
          × pc s' ≡ offset +ℕ 2
          × readReg (regs s') a0 ≡ encode x
          × readReg (regs s') s1 ≡ encode x
          × readReg (regs s') sp ≡ readReg (regs s) sp ∸ 16
          × readReg (regs s') ra ≡ readReg (regs s) ra)
pair-setup-star {A} {B} {C} f g prefix suffix x s h-false pc-eq a0-eq =
  st2 , star-all , h2 , pc2 , a0-st2 , s1-st2 , sp-st2 , ra-st2
  where
    ctx = make-pair-context f g prefix suffix
    open PairContext ctx
    offset = length prefix

    orig-sp = readReg (regs s) sp
    new-sp = orig-sp ∸ 16

    -- Fetch lemmas (proven using fetch-at-prefix-end)
    -- prog = prefix ++ (setup-alloc ∷ setup-save ∷ rest) ++ suffix
    --      = prefix ++ setup-alloc ∷ (setup-save ∷ rest ++ suffix)
    fetch0 : fetch prog offset ≡ just setup-alloc
    fetch0 = fetch-at-prefix-end prefix setup-alloc _

    prog-eq1 : prog ≡ (prefix ++ setup-alloc ∷ []) ++ _
    prog-eq1 = sym (++-assoc prefix (setup-alloc ∷ []) _)

    len-prefix-1 : length (prefix ++ setup-alloc ∷ []) ≡ offset +ℕ 1
    len-prefix-1 = List-length-++ prefix

    fetch1 : fetch prog (offset +ℕ 1) ≡ just setup-save
    fetch1 = subst₂ (λ p n → fetch p n ≡ just setup-save) (sym prog-eq1) len-prefix-1
                    (fetch-at-prefix-end (prefix ++ setup-alloc ∷ []) setup-save _)

    -- State after step 0: addi sp sp -16
    st1 : State
    st1 = record s { regs = writeReg (regs s) sp new-sp
                   ; pc = pc s +ℕ 1 }

    step0 : step prog s ≡ just st1
    step0 = trans (step-exec prog s setup-alloc h-false
                    (subst (λ p → fetch prog p ≡ just setup-alloc) (sym pc-eq) fetch0))
                  (execAddiNeg prog s sp sp 15)

    h1 : halted st1 ≡ false
    h1 = h-false

    pc1 : pc st1 ≡ offset +ℕ 1
    pc1 = cong (_+ℕ 1) pc-eq

    -- State after step 1: mv s1 a0
    a0-st1 : readReg (regs st1) a0 ≡ encode x
    a0-st1 = trans (readReg-writeReg-sp-a0 (regs s) new-sp) a0-eq

    st2 : State
    st2 = record st1 { regs = writeReg (regs st1) s1 (readReg (regs st1) a0)
                     ; pc = pc st1 +ℕ 1 }

    step1 : step prog st1 ≡ just st2
    step1 = trans (step-exec prog st1 setup-save h1
                    (subst (λ p → fetch prog p ≡ just setup-save) (sym pc1) fetch1))
                  (execMv prog st1 s1 a0)

    -- Star proof
    star-all : Star prog s st2
    star-all = ⟨ h-false , step0 ⟩◅ ⟨ h1 , step1 ⟩◅ refl*

    -- Final state properties
    h2 : halted st2 ≡ false
    h2 = h-false

    pc2 : pc st2 ≡ offset +ℕ 2
    pc2 = trans (cong (_+ℕ 1) pc1) (+-assoc offset 1 1)

    a0-st2 : readReg (regs st2) a0 ≡ encode x
    a0-st2 = trans (readReg-writeReg-s1-a0 (regs st1) (readReg (regs st1) a0)) a0-st1

    s1-st2 : readReg (regs st2) s1 ≡ encode x
    s1-st2 = trans (readReg-writeReg-same (regs st1) s1 (readReg (regs st1) a0) (λ ())) a0-st1

    sp-st1 : readReg (regs st1) sp ≡ new-sp
    sp-st1 = readReg-writeReg-same (regs s) sp new-sp (λ ())

    sp-st2 : readReg (regs st2) sp ≡ new-sp
    sp-st2 = trans (readReg-writeReg-s1-sp (regs st1) (readReg (regs st1) a0)) sp-st1

    ra-st1 : readReg (regs st1) ra ≡ readReg (regs s) ra
    ra-st1 = readReg-writeReg-sp-ra (regs s) new-sp

    ra-st2 : readReg (regs st2) ra ≡ readReg (regs s) ra
    ra-st2 = trans (readReg-writeReg-s1-ra (regs st1) (readReg (regs st1) a0)) ra-st1

------------------------------------------------------------------------
-- Phase 3: Middle - trace 2 instructions (sd a0 0(sp); mv a0 s1)
------------------------------------------------------------------------

-- | Middle phase: store f result and restore original input
-- Entry: pc = offset + 2 + len-f, a0 = encode (eval f x), s1 = encode x
-- Exit: pc = offset + 4 + len-f, a0 = encode x, memory[sp] = encode (eval f x)
pair-middle-star : ∀ {A B C} (f : IR C A) (g : IR C B)
                   (prefix suffix : Program) (x : ⟦ C ⟧) (s sf : State) →
  let ctx = make-pair-context f g prefix suffix
      open PairContext ctx
      mid-offset = length prefix +ℕ 2 +ℕ len-f
  in
  halted sf ≡ false →
  pc sf ≡ mid-offset →
  readReg (regs sf) a0 ≡ encode (eval f x) →
  readReg (regs sf) s1 ≡ encode x →
  ∃[ s' ] (Star prog sf s'
          × halted s' ≡ false
          × pc s' ≡ mid-offset +ℕ 2
          × readReg (regs s') a0 ≡ encode x
          × readReg (regs s') s1 ≡ encode x
          × readReg (regs s') sp ≡ readReg (regs sf) sp
          × readReg (regs s') ra ≡ readReg (regs sf) ra
          × readMem (memory s') (readReg (regs sf) sp) ≡ just (encode (eval f x)))
pair-middle-star {A} {B} {C} f g prefix suffix x s sf h-false pc-eq a0-eq s1-eq =
  st2 , star-all , h2 , pc2 , a0-st2 , s1-st2 , sp-st2 , ra-st2 , mem-st2
  where
    ctx = make-pair-context f g prefix suffix
    open PairContext ctx
    mid-offset = length prefix +ℕ 2 +ℕ len-f

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

------------------------------------------------------------------------
-- Phase 5: Final - trace 2 instructions (sd a0 8(sp); mv a0 sp)
------------------------------------------------------------------------

-- | Final phase: store g result and return pair pointer
-- Entry: pc = offset + 4 + len-f + len-g, a0 = encode (eval g x)
-- Exit: pc = offset + 6 + len-f + len-g, a0 = encode (eval f x, eval g x)
pair-final-star : ∀ {A B C} (f : IR C A) (g : IR C B)
                  (prefix suffix : Program) (x : ⟦ C ⟧) (sf sg : State) →
  let ctx = make-pair-context f g prefix suffix
      open PairContext ctx
      final-offset = length prefix +ℕ 4 +ℕ len-f +ℕ len-g
      curr-sp = readReg (regs sg) sp
  in
  halted sg ≡ false →
  pc sg ≡ final-offset →
  readReg (regs sg) a0 ≡ encode (eval g x) →
  readMem (memory sg) curr-sp ≡ just (encode (eval f x)) →
  ∃[ s' ] (Star prog sg s'
          × halted s' ≡ false
          × pc s' ≡ final-offset +ℕ 2
          × readReg (regs s') a0 ≡ encode (eval f x , eval g x)
          × readReg (regs s') s1 ≡ readReg (regs sg) s1
          × readReg (regs s') ra ≡ readReg (regs sg) ra)
pair-final-star {A} {B} {C} f g prefix suffix x sf sg h-false pc-eq a0-eq mem-f =
  st2 , star-all , h2 , pc2 , a0-final , s1-st2 , ra-st2
  where
    ctx = make-pair-context f g prefix suffix
    open PairContext ctx
    final-offset = length prefix +ℕ 4 +ℕ len-f +ℕ len-g
    curr-sp = readReg (regs sg) sp

    -- Fetch lemmas (proven using fetch-at-prefix-end)
    -- prog = prefix-g ++ code-g ++ suffix-g
    --      = prefix-final ++ final-store ∷ final-result ∷ suffix
    -- final-offset = length prefix-final

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

    -- Star proof
    star-all : Star prog sg st2
    star-all = ⟨ h-false , step0 ⟩◅ ⟨ h1 , step1 ⟩◅ refl*

    -- Final state properties
    h2 : halted st2 ≡ false
    h2 = h-false

    pc2 : pc st2 ≡ final-offset +ℕ 2
    pc2 = trans (cong (_+ℕ 1) pc1) (+-assoc final-offset 1 1)

    s1-st1 : readReg (regs st1) s1 ≡ readReg (regs sg) s1
    s1-st1 = refl  -- memory write doesn't change regs

    s1-st2 : readReg (regs st2) s1 ≡ readReg (regs sg) s1
    s1-st2 = trans (readReg-writeReg-a0-s1 (regs st1) (readReg (regs st1) sp)) s1-st1

    ra-st1 : readReg (regs st1) ra ≡ readReg (regs sg) ra
    ra-st1 = refl  -- memory write doesn't change regs

    ra-st2 : readReg (regs st2) ra ≡ readReg (regs sg) ra
    ra-st2 = trans (readReg-writeReg-a0-ra (regs st1) (readReg (regs st1) sp)) ra-st1

    -- Memory tracking for pair encoding
    sp-st1 : readReg (regs st1) sp ≡ curr-sp
    sp-st1 = refl  -- memory write doesn't change regs

    sp-st2 : readReg (regs st2) sp ≡ curr-sp
    sp-st2 = trans (readReg-writeReg-a0-sp (regs st1) (readReg (regs st1) sp)) sp-st1

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

    a0-final : readReg (regs st2) a0 ≡ encode (eval f x , eval g x)
    a0-final = trans a0-st2-is-sp pair-encoding

------------------------------------------------------------------------
-- Helper for assembling pair result from f and g results
------------------------------------------------------------------------

-- This will be used by MutualIR to combine the recursive results
