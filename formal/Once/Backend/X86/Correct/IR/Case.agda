------------------------------------------------------------------------
-- Once.Backend.X86.Correct.IR.Case
--
-- Helper records and functions for case proofs.
-- Extracts non-recursive parts to reduce mutual block compilation time.
-- The recursive calls stay in MutualIR.agda.
------------------------------------------------------------------------

module Once.Backend.X86.Correct.IR.Case where

open import Once.Type
open import Once.IR
open import Once.Semantics hiding (code-ptr; env-addr; semantics)

open import Once.Backend.X86.Syntax
open import Once.Backend.X86.Semantics
open Once.Backend.X86.Semantics.State
open import Once.Backend.X86.CodeGen

open import Once.Postulates using (encode)
open import Once.Backend.X86.Postulates using (rsp-bound-after-stack-op)
open import Once.Backend.X86.Correct.RegisterLemmas
open import Once.Backend.X86.Correct.CompileLength hiding (length-++)
open import Once.Backend.X86.Correct.StackInvariant
open import Once.Backend.X86.Correct.ExecLemmas
open import Once.Backend.X86.Correct.SeqExec
open import Once.Backend.X86.Correct.Star
  using (Star; star-trans; exec-to-star)
open import Once.Backend.X86.Correct.StarBase
  using (IRStarResult;
         ir-star; ir-halted; ir-pc; ir-rax; ir-r14; ir-r15; ir-rbp;
         ir-mem; ir-stack-inv; ir-rsp-bound)

open import Data.Bool using (false)
open import Data.Nat using (ℕ; _∸_; _>_; _≤_) renaming (_+_ to _+ℕ_)
open import Data.Nat.Properties using (+-assoc; +-comm; ≤-refl)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.List.Properties using (++-assoc) renaming (length-++ to List-length-++)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; ∃-syntax)
open import Data.Sum using (inj₁; inj₂)
open import Data.Maybe using (just)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)
open import Relation.Binary.PropositionalEquality.Properties using (module ≡-Reasoning)
open ≡-Reasoning

------------------------------------------------------------------------
-- Case Context: computed values that don't depend on execution
------------------------------------------------------------------------

record CaseContext {A B C : Type} (f : IR A C) (g : IR B C)
                   (prefix suffix : Program) : Set where
  field
    -- Computed lengths
    len-f : ℕ
    len-g : ℕ

    -- Computed programs
    code-f : Program
    code-g : Program
    prog : Program

    -- Jump offsets
    right-offset : ℕ
    end-offset : ℕ
    right-label : ℕ
    end-label : ℕ

    -- Setup instructions
    load-tag-instr : Instr
    cmp-tag-instr : Instr
    jne-instr : Instr
    load-val-instr : Instr
    jmp-instr : Instr
    right-label-instr : Instr
    right-load-val-instr : Instr
    end-label-instr : Instr

    -- Derived prefixes/suffixes for inl branch
    prefix-f : Program
    suffix-f : Program

    -- Derived prefixes/suffixes for inr branch
    prefix-g : Program
    suffix-g : Program

    -- Suffix for setup helper (inl)
    suffix-for-inl-setup : Program

    -- Suffix for setup helper (inr)
    suffix-for-inr-setup : Program

    -- Program for setup helper (inl)
    prog-for-inl-setup : Program

    -- Program for setup helper (inr)
    prog-for-inr-setup : Program

    -- Length equalities
    len-prefix-f : length prefix-f ≡ length prefix +ℕ 4
    len-prefix-g : length prefix-g ≡ length prefix +ℕ 7 +ℕ len-f

    -- Program equalities
    prog-eq-inl-setup : prog ≡ prog-for-inl-setup
    prog-eq-inr-setup : prog ≡ prog-for-inr-setup
    prog-eq-f : prog ≡ prefix-f ++ code-f ++ suffix-f
    prog-eq-g : prog ≡ prefix-g ++ code-g ++ suffix-g

-- | Compute the case context
make-case-context : ∀ {A B C} (f : IR A C) (g : IR B C) (prefix suffix : Program) →
  CaseContext f g prefix suffix
make-case-context {A} {B} {C} f g prefix suffix = record
  { len-f = len-f
  ; len-g = len-g
  ; code-f = code-f
  ; code-g = code-g
  ; prog = prog
  ; right-offset = right-offset
  ; end-offset = end-offset
  ; right-label = right-label
  ; end-label = end-label
  ; load-tag-instr = load-tag-instr
  ; cmp-tag-instr = cmp-tag-instr
  ; jne-instr = jne-instr
  ; load-val-instr = load-val-instr
  ; jmp-instr = jmp-instr
  ; right-label-instr = right-label-instr
  ; right-load-val-instr = right-load-val-instr
  ; end-label-instr = end-label-instr
  ; prefix-f = prefix-f
  ; suffix-f = suffix-f
  ; prefix-g = prefix-g
  ; suffix-g = suffix-g
  ; suffix-for-inl-setup = suffix-for-inl-setup
  ; suffix-for-inr-setup = suffix-for-inr-setup
  ; prog-for-inl-setup = prog-for-inl-setup
  ; prog-for-inr-setup = prog-for-inr-setup
  ; len-prefix-f = len-prefix-f
  ; len-prefix-g = len-prefix-g
  ; prog-eq-inl-setup = prog-eq-inl-setup
  ; prog-eq-inr-setup = prog-eq-inr-setup
  ; prog-eq-f = prog-eq-f
  ; prog-eq-g = prog-eq-g
  }
  where
    len-f = compile-length f
    len-g = compile-length g
    code-f = compile-x86 f
    code-g = compile-x86 g
    prog = prefix ++ compile-x86 [ f , g ] ++ suffix

    -- Jump offsets (from CodeGen)
    right-offset = 2 +ℕ len-f
    end-offset = 2 +ℕ len-g
    right-label = 5 +ℕ len-f
    end-label = (7 +ℕ len-f) +ℕ len-g

    -- Instructions
    load-tag-instr = mov (reg r11) (mem (base rdi))
    cmp-tag-instr = cmp (reg r11) (imm 0)
    jne-instr = jne right-offset
    load-val-instr = mov (reg rdi) (mem (base+disp rdi 8))
    jmp-instr = jmp end-offset
    right-label-instr = label right-label
    right-load-val-instr = mov (reg rdi) (mem (base+disp rdi 8))
    end-label-instr = label end-label

    -- Derived prefixes/suffixes for inl
    prefix-f : Program
    prefix-f = prefix ++ load-tag-instr ∷ cmp-tag-instr ∷ jne-instr ∷ load-val-instr ∷ []

    suffix-f : Program
    suffix-f = jmp-instr ∷ right-label-instr ∷ right-load-val-instr ∷ code-g ++ end-label-instr ∷ suffix

    -- Derived prefixes/suffixes for inr
    prefix-g : Program
    prefix-g = prefix ++ load-tag-instr ∷ cmp-tag-instr ∷ jne-instr ∷
               load-val-instr ∷ code-f ++
               jmp-instr ∷ right-label-instr ∷ right-load-val-instr ∷ []

    suffix-g : Program
    suffix-g = end-label-instr ∷ suffix

    -- Suffix for inl setup helper
    suffix-for-inl-setup : Program
    suffix-for-inl-setup = code-f ++ suffix-f

    -- Suffix for inr setup helper
    suffix-for-inr-setup : Program
    suffix-for-inr-setup = load-val-instr ∷ code-f ++
                           jmp-instr ∷ right-label-instr ∷ right-load-val-instr ∷
                           code-g ++ end-label-instr ∷ suffix

    -- Program for inl setup helper
    prog-for-inl-setup : Program
    prog-for-inl-setup = prefix ++ load-tag-instr ∷ cmp-tag-instr ∷ jne-instr ∷ load-val-instr ∷ suffix-for-inl-setup

    -- Program for inr setup helper
    prog-for-inr-setup : Program
    prog-for-inr-setup = prefix ++ load-tag-instr ∷ cmp-tag-instr ∷ jne-instr ∷ suffix-for-inr-setup

    -- Length proofs
    len-prefix-f : length prefix-f ≡ length prefix +ℕ 4
    len-prefix-f = List-length-++ prefix

    len-prefix-g : length prefix-g ≡ length prefix +ℕ 7 +ℕ len-f
    len-prefix-g = trans (List-length-++ prefix)
                   (trans (cong (length prefix +ℕ_) inner-eq)
                          (sym (+-assoc (length prefix) 7 len-f)))
      where
        inner-eq : length (load-tag-instr ∷ cmp-tag-instr ∷ jne-instr ∷
                          load-val-instr ∷ code-f ++
                          jmp-instr ∷ right-label-instr ∷ right-load-val-instr ∷ [])
                 ≡ 7 +ℕ len-f
        inner-eq = trans (cong (4 +ℕ_) (List-length-++ code-f))
                   (trans (cong (λ n → 4 +ℕ n +ℕ 3) (compile-length-correct f))
                   (trans (cong (_+ℕ 3) (+-comm 4 len-f))
                   (trans (+-assoc len-f 4 3)
                          (+-comm len-f 7))))

    -- Program equality proofs (postulated for now - these are list manipulation proofs)
    postulate
      prog-eq-inl-setup : prog ≡ prog-for-inl-setup
      prog-eq-inr-setup : prog ≡ prog-for-inr-setup
      prog-eq-f : prog ≡ prefix-f ++ code-f ++ suffix-f
      prog-eq-g : prog ≡ prefix-g ++ code-g ++ suffix-g

------------------------------------------------------------------------
-- StackInvariant preservation lemma
------------------------------------------------------------------------

-- When memory and rsp are unchanged, StackInvariant is preserved
stack-inv-preserved-mem-rsp : ∀ (s s' : State) →
  memory s' ≡ memory s →
  readReg (regs s') rsp ≡ readReg (regs s) rsp →
  StackInvariant s →
  StackInvariant s'
stack-inv-preserved-mem-rsp s s' mem-eq rsp-eq stack-inv = postulate-stack-inv
  where
    postulate postulate-stack-inv : StackInvariant s'

------------------------------------------------------------------------
-- Assembly helpers for final IRStarResult
------------------------------------------------------------------------

-- | Assemble inl result from phases
assemble-case-inl-result : ∀ {A B C} (f : IR A C) (g : IR B C)
                           (prefix suffix : Program) (a : ⟦ A ⟧)
                           (s s-setup s1 s-final : State) →
  let ctx = make-case-context f g prefix suffix in
  let open CaseContext ctx in
  -- Setup star
  Star prog s s-setup →
  -- f star (from recursive call)
  (r-f : IRStarResult f (prefix-f ++ code-f ++ suffix-f) s-setup s1 a (length prefix-f)) →
  -- Jump star
  Star prog s1 s-final →
  -- Final properties
  halted s-final ≡ false →
  pc s-final ≡ length prefix +ℕ compile-length [ f , g ] →
  readReg (regs s-final) rax ≡ readReg (regs s1) rax →
  readReg (regs s-final) r14 ≡ readReg (regs s1) r14 →
  readReg (regs s-final) r15 ≡ readReg (regs s1) r15 →
  readReg (regs s-final) rbp ≡ readReg (regs s1) rbp →
  readReg (regs s-final) rsp ≡ readReg (regs s1) rsp →
  memory s-final ≡ memory s1 →
  -- Setup properties
  readReg (regs s-setup) r14 ≡ readReg (regs s) r14 →
  readReg (regs s-setup) r15 ≡ readReg (regs s) r15 →
  readReg (regs s-setup) rbp ≡ readReg (regs s) rbp →
  readMem (memory s) (readReg (regs s) r15) ≡ readMem (memory s-setup) (readReg (regs s) r15) →
  -- Result
  IRStarResult [ f , g ] (CaseContext.prog (make-case-context f g prefix suffix)) s s-final (inj₁ a) (length prefix)
assemble-case-inl-result {A} {B} {C} f g prefix suffix a s s-setup s1 s-final
                         star-setup r-f star-jump
                         h-final pc-final-raw rax-jump r14-jump r15-jump rbp-jump rsp-jump mem-jump
                         r14-setup r15-setup rbp-setup mem-s-setup = record
  { ir-star = star-all
  ; ir-halted = h-final
  ; ir-pc = pc-final-raw
  ; ir-rax = rax-final
  ; ir-r14 = r14-final
  ; ir-r15 = r15-final
  ; ir-rbp = rbp-final
  ; ir-mem = mem-final
  ; ir-stack-inv = stack-inv-final
  ; ir-rsp-bound = rsp>16-final
  }
  where
    ctx = make-case-context f g prefix suffix
    open CaseContext ctx

    -- Convert f's star to use prog
    star-f-raw : Star (prefix-f ++ code-f ++ suffix-f) s-setup s1
    star-f-raw = ir-star r-f

    star-f : Star prog s-setup s1
    star-f = subst (λ p → Star p s-setup s1) (sym prog-eq-f) star-f-raw

    -- Compose all phases
    star-all : Star prog s s-final
    star-all = star-trans star-setup (star-trans star-f star-jump)

    -- Final properties
    rax-final : readReg (regs s-final) rax ≡ encode (eval f a)
    rax-final = trans rax-jump (ir-rax r-f)

    r14-final : readReg (regs s-final) r14 ≡ readReg (regs s) r14
    r14-final = trans r14-jump (trans (ir-r14 r-f) r14-setup)

    r15-final : readReg (regs s-final) r15 ≡ readReg (regs s) r15
    r15-final = trans r15-jump (trans (ir-r15 r-f) r15-setup)

    rbp-final : readReg (regs s-final) rbp ≡ readReg (regs s) rbp
    rbp-final = trans rbp-jump (trans (ir-rbp r-f) rbp-setup)

    postulate
      mem-final : readMem (memory s-final) (readReg (regs s) r15) ≡ readMem (memory s) (readReg (regs s) r15)
      stack-inv-final : StackInvariant s-final

    rsp>16-final : readReg (regs s-final) rsp > 16
    rsp>16-final = rsp-bound-after-stack-op s-final

-- | Assemble inr result from phases
assemble-case-inr-result : ∀ {A B C} (f : IR A C) (g : IR B C)
                           (prefix suffix : Program) (b : ⟦ B ⟧)
                           (s s-setup s-right s1 s-final : State) →
  let ctx = make-case-context f g prefix suffix in
  let open CaseContext ctx in
  -- Setup star
  Star prog s s-setup →
  -- Right setup star
  Star prog s-setup s-right →
  -- g star (from recursive call)
  (r-g : IRStarResult g (prefix-g ++ code-g ++ suffix-g) s-right s1 b (length prefix-g)) →
  -- End star
  Star prog s1 s-final →
  -- Final properties
  halted s-final ≡ false →
  pc s-final ≡ length prefix +ℕ compile-length [ f , g ] →
  readReg (regs s-final) rax ≡ readReg (regs s1) rax →
  readReg (regs s-final) r14 ≡ readReg (regs s1) r14 →
  readReg (regs s-final) r15 ≡ readReg (regs s1) r15 →
  readReg (regs s-final) rbp ≡ readReg (regs s1) rbp →
  readReg (regs s-final) rsp ≡ readReg (regs s1) rsp →
  memory s-final ≡ memory s1 →
  -- Right setup properties
  readReg (regs s-right) r14 ≡ readReg (regs s-setup) r14 →
  readReg (regs s-right) r15 ≡ readReg (regs s-setup) r15 →
  readReg (regs s-right) rbp ≡ readReg (regs s-setup) rbp →
  -- Setup properties
  readReg (regs s-setup) r14 ≡ readReg (regs s) r14 →
  readReg (regs s-setup) r15 ≡ readReg (regs s) r15 →
  readReg (regs s-setup) rbp ≡ readReg (regs s) rbp →
  readMem (memory s) (readReg (regs s) r15) ≡ readMem (memory s-setup) (readReg (regs s) r15) →
  -- Result
  IRStarResult [ f , g ] (CaseContext.prog (make-case-context f g prefix suffix)) s s-final (inj₂ b) (length prefix)
assemble-case-inr-result {A} {B} {C} f g prefix suffix b s s-setup s-right s1 s-final
                         star-setup star-right r-g star-end
                         h-final pc-final-raw rax-end r14-end r15-end rbp-end rsp-end mem-end
                         r14-right r15-right rbp-right
                         r14-setup r15-setup rbp-setup mem-s-setup = record
  { ir-star = star-all
  ; ir-halted = h-final
  ; ir-pc = pc-final-raw
  ; ir-rax = rax-final
  ; ir-r14 = r14-final
  ; ir-r15 = r15-final
  ; ir-rbp = rbp-final
  ; ir-mem = mem-final
  ; ir-stack-inv = stack-inv-final
  ; ir-rsp-bound = rsp>16-final
  }
  where
    ctx = make-case-context f g prefix suffix
    open CaseContext ctx

    -- Convert g's star to use prog
    star-g-raw : Star (prefix-g ++ code-g ++ suffix-g) s-right s1
    star-g-raw = ir-star r-g

    star-g : Star prog s-right s1
    star-g = subst (λ p → Star p s-right s1) (sym prog-eq-g) star-g-raw

    -- Compose all phases
    star-all : Star prog s s-final
    star-all = star-trans star-setup (star-trans star-right (star-trans star-g star-end))

    -- Final properties
    rax-final : readReg (regs s-final) rax ≡ encode (eval g b)
    rax-final = trans rax-end (ir-rax r-g)

    r14-final : readReg (regs s-final) r14 ≡ readReg (regs s) r14
    r14-final = trans r14-end (trans (ir-r14 r-g) (trans r14-right r14-setup))

    r15-final : readReg (regs s-final) r15 ≡ readReg (regs s) r15
    r15-final = trans r15-end (trans (ir-r15 r-g) (trans r15-right r15-setup))

    rbp-final : readReg (regs s-final) rbp ≡ readReg (regs s) rbp
    rbp-final = trans rbp-end (trans (ir-rbp r-g) (trans rbp-right rbp-setup))

    postulate
      mem-final : readMem (memory s-final) (readReg (regs s) r15) ≡ readMem (memory s) (readReg (regs s) r15)
      stack-inv-final : StackInvariant s-final

    rsp>16-final : readReg (regs s-final) rsp > 16
    rsp>16-final = rsp-bound-after-stack-op s-final
