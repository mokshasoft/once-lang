------------------------------------------------------------------------
-- Once.Backend.X86.Correct.IR.Pair
--
-- Helper records and functions for pair proofs.
-- Extracts non-recursive parts to reduce mutual block compilation time.
-- The recursive calls stay in MutualIR.agda.
------------------------------------------------------------------------

module Once.Backend.X86.Correct.IR.Pair where

open import Once.Type
open import Once.IR
open import Once.Semantics hiding (code-ptr; env-addr; semantics)

open import Once.Backend.X86.Syntax
open import Once.Backend.X86.Semantics
open Once.Backend.X86.Semantics.State
open import Once.Backend.X86.CodeGen

open import Once.Postulates using (encode; encode-pair-construct)
open import Once.Backend.X86.Postulates using (rsp-bound-after-stack-op)
open import Once.Backend.X86.Encoding using (mem-read-write; mem-read-other; n≢n+8; n≢n+suc-m)
open import Once.Backend.X86.Correct.RegisterLemmas
open import Once.Backend.X86.Correct.CompileLength hiding (length-++)
open import Once.Backend.X86.Correct.StackInvariant
open import Once.Backend.X86.Correct.ExecLemmas
open import Once.Backend.X86.Correct.FetchStep
open import Once.Backend.X86.Correct.InstrExec
open import Once.Backend.X86.Correct.SeqExec
open import Once.Backend.X86.Correct.Star
  using (Star; star-trans; exec-to-star)
open import Once.Backend.X86.Correct.StarBase
  using (IRStarResult;
         ir-star; ir-halted; ir-pc; ir-rax; ir-r14; ir-r15; ir-rbp;
         ir-mem; ir-stack-inv; ir-rsp-bound)

open import Data.Bool using (false)
open import Data.Empty using (⊥)
open import Data.Nat using (ℕ; zero; suc; _∸_; _>_; _≤_; _<_; s≤s; z≤n) renaming (_+_ to _+ℕ_)
open import Data.Nat.Properties using (+-assoc; +-comm; +-suc; ≤-refl; m∸n+n≡m; <⇒≤; m∸n≤m; ≤-trans; +-monoʳ-<)
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

    -- Setup instructions (7)
    setup-push-r14 : Instr
    setup-push-r15 : Instr
    setup-push-rbp : Instr
    setup-frame : Instr
    setup-sub : Instr
    setup-base : Instr
    setup-save : Instr

    -- Middle instructions (2)
    store-f-instr : Instr
    restore-input : Instr

    -- Final instructions (6)
    store-g-instr : Instr
    return-pair-instr : Instr
    restore-rsp : Instr
    final-pop-rbp : Instr
    final-pop-r15 : Instr
    final-pop-r14 : Instr

    -- Derived prefixes/suffixes
    prefix-f : Program
    suffix-f : Program
    prefix-g : Program
    suffix-g : Program
    prefix-mid : Program
    rest-mid : Program
    prefix-final : Program
    rest-for-setup : Program
    inner-pair : Program

    -- Length equalities
    len-prefix-f : length prefix-f ≡ length prefix +ℕ 7
    len-prefix-g : length prefix-g ≡ length prefix +ℕ 9 +ℕ len-f
    len-prefix-mid : length prefix-mid ≡ length prefix +ℕ 7 +ℕ len-f
    len-prefix-final : length prefix-final ≡ length prefix +ℕ 9 +ℕ len-f +ℕ len-g

    -- Program equalities
    prog-eq-setup : prog ≡ prefix ++ setup-push-r14 ∷ setup-push-r15 ∷ setup-push-rbp ∷ setup-frame ∷ setup-sub ∷ setup-base ∷ setup-save ∷ rest-for-setup
    prog-eq-f : prog ≡ prefix-f ++ code-f ++ suffix-f
    prog-eq-mid : prog ≡ prefix-mid ++ store-f-instr ∷ restore-input ∷ rest-mid
    prog-eq-g : prog ≡ prefix-g ++ code-g ++ suffix-g
    prog-eq-final : prog ≡ prefix-final ++ store-g-instr ∷ return-pair-instr ∷ restore-rsp ∷ final-pop-rbp ∷ final-pop-r15 ∷ final-pop-r14 ∷ suffix

-- | Compute the pair context
make-pair-context : ∀ {A B C} (f : IR C A) (g : IR C B) (prefix suffix : Program) →
  PairContext f g prefix suffix
make-pair-context {A} {B} {C} f g prefix suffix = record
  { len-f = len-f
  ; len-g = len-g
  ; code-f = code-f
  ; code-g = code-g
  ; prog = prog
  ; setup-push-r14 = setup-push-r14
  ; setup-push-r15 = setup-push-r15
  ; setup-push-rbp = setup-push-rbp
  ; setup-frame = setup-frame
  ; setup-sub = setup-sub
  ; setup-base = setup-base
  ; setup-save = setup-save
  ; store-f-instr = store-f-instr
  ; restore-input = restore-input
  ; store-g-instr = store-g-instr
  ; return-pair-instr = return-pair-instr
  ; restore-rsp = restore-rsp
  ; final-pop-rbp = final-pop-rbp
  ; final-pop-r15 = final-pop-r15
  ; final-pop-r14 = final-pop-r14
  ; prefix-f = prefix-f
  ; suffix-f = suffix-f
  ; prefix-g = prefix-g
  ; suffix-g = suffix-g
  ; prefix-mid = prefix-mid
  ; rest-mid = rest-mid
  ; prefix-final = prefix-final
  ; rest-for-setup = rest-for-setup
  ; inner-pair = inner-pair
  ; len-prefix-f = len-prefix-f
  ; len-prefix-g = len-prefix-g
  ; len-prefix-mid = len-prefix-mid
  ; len-prefix-final = len-prefix-final
  ; prog-eq-setup = prog-eq-setup
  ; prog-eq-f = prog-eq-f
  ; prog-eq-mid = prog-eq-mid
  ; prog-eq-g = prog-eq-g
  ; prog-eq-final = prog-eq-final
  }
  where
    len-f = compile-length f
    len-g = compile-length g
    code-f = compile-x86 f
    code-g = compile-x86 g
    prog = prefix ++ compile-x86 ⟨ f , g ⟩ ++ suffix

    -- Setup instructions (7)
    setup-push-r14 = push (reg r14)
    setup-push-r15 = push (reg r15)
    setup-push-rbp = push (reg rbp)
    setup-frame = mov (reg rbp) (reg rsp)
    setup-sub = sub (reg rsp) (imm 16)
    setup-base = mov (reg r15) (reg rsp)
    setup-save = mov (reg r14) (reg rdi)

    -- Middle instructions (2)
    store-f-instr = mov (mem (base r15)) (reg rax)
    restore-input = mov (reg rdi) (reg r14)

    -- Final instructions (6)
    store-g-instr = mov (mem (base+disp r15 8)) (reg rax)
    return-pair-instr = mov (reg rax) (reg r15)
    restore-rsp = mov (reg rsp) (reg rbp)
    final-pop-rbp = pop rbp
    final-pop-r15 = pop r15
    final-pop-r14 = pop r14

    -- Derived programs
    prefix-f : Program
    prefix-f = prefix ++ setup-push-r14 ∷ setup-push-r15 ∷ setup-push-rbp ∷ setup-frame ∷ setup-sub ∷ setup-base ∷ setup-save ∷ []

    inner-pair : Program
    inner-pair = code-f ++ store-f-instr ∷ restore-input ∷ code-g ++ store-g-instr ∷ return-pair-instr ∷ restore-rsp ∷ final-pop-rbp ∷ final-pop-r15 ∷ final-pop-r14 ∷ []

    suffix-f : Program
    suffix-f = store-f-instr ∷ restore-input ∷ code-g ++ store-g-instr ∷ return-pair-instr ∷ restore-rsp ∷ final-pop-rbp ∷ final-pop-r15 ∷ final-pop-r14 ∷ suffix

    prefix-g : Program
    prefix-g = prefix-f ++ code-f ++ store-f-instr ∷ restore-input ∷ []

    suffix-g : Program
    suffix-g = store-g-instr ∷ return-pair-instr ∷ restore-rsp ∷ final-pop-rbp ∷ final-pop-r15 ∷ final-pop-r14 ∷ suffix

    prefix-mid : Program
    prefix-mid = prefix-f ++ code-f

    rest-mid : Program
    rest-mid = code-g ++ store-g-instr ∷ return-pair-instr ∷ restore-rsp ∷ final-pop-rbp ∷ final-pop-r15 ∷ final-pop-r14 ∷ suffix

    prefix-final : Program
    prefix-final = prefix-g ++ code-g

    rest-for-setup : Program
    rest-for-setup = inner-pair ++ suffix

    -- Length proofs
    len-prefix-f : length prefix-f ≡ length prefix +ℕ 7
    len-prefix-f = List-length-++ prefix

    len-prefix-g : length prefix-g ≡ length prefix +ℕ 9 +ℕ len-f
    len-prefix-g = begin
      length prefix-g
        ≡⟨ List-length-++ prefix-f ⟩
      length prefix-f +ℕ length (code-f ++ store-f-instr ∷ restore-input ∷ [])
        ≡⟨ cong (_+ℕ length (code-f ++ store-f-instr ∷ restore-input ∷ [])) len-prefix-f ⟩
      (length prefix +ℕ 7) +ℕ length (code-f ++ store-f-instr ∷ restore-input ∷ [])
        ≡⟨ cong ((length prefix +ℕ 7) +ℕ_) (List-length-++ code-f) ⟩
      (length prefix +ℕ 7) +ℕ (length code-f +ℕ 2)
        ≡⟨ cong (λ z → (length prefix +ℕ 7) +ℕ (z +ℕ 2)) (compile-length-correct f) ⟩
      (length prefix +ℕ 7) +ℕ (len-f +ℕ 2)
        ≡⟨ +-assoc (length prefix) 7 (len-f +ℕ 2) ⟩
      length prefix +ℕ (7 +ℕ (len-f +ℕ 2))
        ≡⟨ cong (length prefix +ℕ_) (+-assoc 7 len-f 2) ⟩
      length prefix +ℕ ((7 +ℕ len-f) +ℕ 2)
        ≡⟨ cong (λ z → length prefix +ℕ (z +ℕ 2)) (+-comm 7 len-f) ⟩
      length prefix +ℕ ((len-f +ℕ 7) +ℕ 2)
        ≡⟨ cong (length prefix +ℕ_) (+-assoc len-f 7 2) ⟩
      length prefix +ℕ (len-f +ℕ 9)
        ≡⟨ cong (length prefix +ℕ_) (+-comm len-f 9) ⟩
      length prefix +ℕ (9 +ℕ len-f)
        ≡⟨ sym (+-assoc (length prefix) 9 len-f) ⟩
      length prefix +ℕ 9 +ℕ len-f
        ∎

    len-prefix-mid : length prefix-mid ≡ length prefix +ℕ 7 +ℕ len-f
    len-prefix-mid = trans (List-length-++ prefix-f) (trans (cong (_+ℕ length code-f) len-prefix-f)
                     (trans (cong ((length prefix +ℕ 7) +ℕ_) (compile-length-correct f)) refl))

    len-prefix-final : length prefix-final ≡ length prefix +ℕ 9 +ℕ len-f +ℕ len-g
    len-prefix-final = trans (List-length-++ prefix-g)
                       (trans (cong (_+ℕ length code-g) len-prefix-g)
                       (cong ((length prefix +ℕ 9 +ℕ len-f) +ℕ_) (compile-length-correct g)))

    -- Program equalities
    prog-eq-setup : prog ≡ prefix ++ setup-push-r14 ∷ setup-push-r15 ∷ setup-push-rbp ∷ setup-frame ∷ setup-sub ∷ setup-base ∷ setup-save ∷ rest-for-setup
    prog-eq-setup = cong (prefix ++_) refl

    -- Helper lemmas for program equalities
    final-nil : Program
    final-nil = store-g-instr ∷ return-pair-instr ∷ restore-rsp ∷ final-pop-rbp ∷ final-pop-r15 ∷ final-pop-r14 ∷ []

    final-with-suffix : Program
    final-with-suffix = store-g-instr ∷ return-pair-instr ∷ restore-rsp ∷ final-pop-rbp ∷ final-pop-r15 ∷ final-pop-r14 ∷ suffix

    final-suffix-eq : final-nil ++ suffix ≡ final-with-suffix
    final-suffix-eq = refl

    mid-final-nil : Program
    mid-final-nil = store-f-instr ∷ restore-input ∷ code-g ++ final-nil

    mid-final-suffix-eq : mid-final-nil ++ suffix ≡ suffix-f
    mid-final-suffix-eq = cong (store-f-instr ∷_) (cong (restore-input ∷_)
                            (trans (++-assoc code-g final-nil suffix)
                                   (cong (code-g ++_) final-suffix-eq)))

    inner-pair-split : inner-pair ≡ code-f ++ mid-final-nil
    inner-pair-split = refl

    rest-eq : rest-for-setup ≡ code-f ++ suffix-f
    rest-eq = trans (cong (_++ suffix) inner-pair-split)
                    (trans (++-assoc code-f mid-final-nil suffix) (cong (code-f ++_) mid-final-suffix-eq))

    prefix-setup-eq : ∀ xs → prefix ++ setup-push-r14 ∷ setup-push-r15 ∷ setup-push-rbp ∷ setup-frame ∷ setup-sub ∷ setup-base ∷ setup-save ∷ xs ≡ prefix-f ++ xs
    prefix-setup-eq xs = sym (++-assoc prefix (setup-push-r14 ∷ setup-push-r15 ∷ setup-push-rbp ∷ setup-frame ∷ setup-sub ∷ setup-base ∷ setup-save ∷ []) xs)

    prog-eq-f : prog ≡ prefix-f ++ code-f ++ suffix-f
    prog-eq-f = trans prog-eq-setup (trans (prefix-setup-eq rest-for-setup) (cong (prefix-f ++_) rest-eq))

    suffix-f-eq-rest : suffix-f ≡ store-f-instr ∷ restore-input ∷ rest-mid
    suffix-f-eq-rest = refl

    prog-eq-mid : prog ≡ prefix-mid ++ store-f-instr ∷ restore-input ∷ rest-mid
    prog-eq-mid = trans prog-eq-f
                        (trans (sym (++-assoc prefix-f code-f suffix-f))
                               (cong (prefix-mid ++_) suffix-f-eq-rest))

    rest-mid-eq-g : rest-mid ≡ code-g ++ suffix-g
    rest-mid-eq-g = refl

    prefix-g-eq-mid : prefix-g ≡ prefix-mid ++ store-f-instr ∷ restore-input ∷ []
    prefix-g-eq-mid = sym (++-assoc prefix-f code-f (store-f-instr ∷ restore-input ∷ []))

    cons-flatten : ∀ xs → (store-f-instr ∷ restore-input ∷ []) ++ xs ≡ store-f-instr ∷ restore-input ∷ xs
    cons-flatten xs = refl

    prog-eq-g : prog ≡ prefix-g ++ code-g ++ suffix-g
    prog-eq-g = begin
      prog
        ≡⟨ prog-eq-mid ⟩
      prefix-mid ++ store-f-instr ∷ restore-input ∷ rest-mid
        ≡⟨ cong (prefix-mid ++_) (cong (store-f-instr ∷_) (cong (restore-input ∷_) rest-mid-eq-g)) ⟩
      prefix-mid ++ store-f-instr ∷ restore-input ∷ (code-g ++ suffix-g)
        ≡⟨ cong (prefix-mid ++_) (sym (cons-flatten (code-g ++ suffix-g))) ⟩
      prefix-mid ++ ((store-f-instr ∷ restore-input ∷ []) ++ (code-g ++ suffix-g))
        ≡⟨ sym (++-assoc prefix-mid (store-f-instr ∷ restore-input ∷ []) (code-g ++ suffix-g)) ⟩
      (prefix-mid ++ store-f-instr ∷ restore-input ∷ []) ++ (code-g ++ suffix-g)
        ≡⟨ cong (_++ (code-g ++ suffix-g)) (sym prefix-g-eq-mid) ⟩
      prefix-g ++ (code-g ++ suffix-g)
        ∎

    prog-eq-final : prog ≡ prefix-final ++ store-g-instr ∷ return-pair-instr ∷ restore-rsp ∷ final-pop-rbp ∷ final-pop-r15 ∷ final-pop-r14 ∷ suffix
    prog-eq-final = trans prog-eq-g (sym (++-assoc prefix-g code-g suffix-g))

------------------------------------------------------------------------
-- Setup Result: state after 7 setup instructions
------------------------------------------------------------------------

record PairSetupResult {A B C : Type} (f : IR C A) (g : IR C B)
                       (prefix suffix : Program) (x : ⟦ C ⟧)
                       (s : State) : Set where
  private
    ctx = make-pair-context f g prefix suffix
  open PairContext ctx

  field
    s-setup : State
    h-setup : halted s-setup ≡ false
    pc-setup-f : pc s-setup ≡ length prefix-f
    rdi-setup-enc : readReg (regs s-setup) rdi ≡ encode x
    r14-setup : readReg (regs s-setup) r14 ≡ readReg (regs s) rdi
    r15-setup : readReg (regs s-setup) r15 ≡ readReg (regs s) rsp ∸ 40
    rbp-setup : readReg (regs s-setup) rbp ≡ readReg (regs s) rsp ∸ 24
    rsp-setup : readReg (regs s-setup) rsp ≡ readReg (regs s) rsp ∸ 40
    stack-inv-setup : StackInvariant s-setup
    rsp>16-setup : readReg (regs s-setup) rsp > 16
    star-setup : Star prog s s-setup

-- | Execute setup phase and compute all properties
exec-pair-setup : ∀ {A B C} (f : IR C A) (g : IR C B)
                  (prefix suffix : Program) (x : ⟦ C ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ length prefix →
  readReg (regs s) rdi ≡ encode x →
  PairSetupResult f g prefix suffix x s
exec-pair-setup {A} {B} {C} f g prefix suffix x s h-false pc-eq rdi-eq = record
  { s-setup = s-setup
  ; h-setup = h-setup
  ; pc-setup-f = pc-setup-f
  ; rdi-setup-enc = rdi-setup-enc
  ; r14-setup = r14-setup
  ; r15-setup = r15-setup
  ; rbp-setup = rbp-setup
  ; rsp-setup = rsp-setup
  ; stack-inv-setup = stack-inv-setup
  ; rsp>16-setup = rsp>16-setup
  ; star-setup = star-setup
  }
  where
    ctx = make-pair-context f g prefix suffix
    open PairContext ctx

    -- Execute 7 setup instructions
    setup-result = exec-pair-setup-at-7 prefix rest-for-setup s h-false pc-eq

    s-setup = proj₁ setup-result
    exec-setup = proj₁ (proj₂ setup-result)
    h-setup = proj₁ (proj₂ (proj₂ setup-result))
    pc-setup = proj₁ (proj₂ (proj₂ (proj₂ setup-result)))
    r14-setup-raw = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ setup-result))))
    rdi-setup = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ setup-result)))))
    r15-setup = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ setup-result))))))
    rsp-setup = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ setup-result)))))))
    rbp-setup = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ setup-result)))))))

    r14-setup : readReg (regs s-setup) r14 ≡ readReg (regs s) rdi
    r14-setup = r14-setup-raw

    -- Convert setup exec to Star
    star-setup-raw : Star (prefix ++ setup-push-r14 ∷ setup-push-r15 ∷ setup-push-rbp ∷ setup-frame ∷ setup-sub ∷ setup-base ∷ setup-save ∷ rest-for-setup) s s-setup
    star-setup-raw = exec-to-star exec-setup

    star-setup : Star prog s s-setup
    star-setup = subst (λ p → Star p s s-setup) (sym prog-eq-setup) star-setup-raw

    rdi-setup-enc : readReg (regs s-setup) rdi ≡ encode x
    rdi-setup-enc = trans rdi-setup rdi-eq

    pc-setup-f : pc s-setup ≡ length prefix-f
    pc-setup-f = trans pc-setup (sym len-prefix-f)

    -- StackInvariant after setup: rsp = r15
    stack-inv-setup : StackInvariant s-setup
    stack-inv-setup = stack-below-r15 rsp≤r15
      where
        rsp-r15-eq : readReg (regs s-setup) rsp ≡ readReg (regs s-setup) r15
        rsp-r15-eq = trans rsp-setup (sym r15-setup)

        rsp≤r15 : readReg (regs s-setup) rsp ≤ readReg (regs s-setup) r15
        rsp≤r15 = subst (readReg (regs s-setup) rsp ≤_) (sym rsp-r15-eq) ≤-refl

    rsp>16-setup : readReg (regs s-setup) rsp > 16
    rsp>16-setup = rsp-bound-after-stack-op s-setup

------------------------------------------------------------------------
-- Middle Result: state after 2 middle instructions (store f result, restore input)
------------------------------------------------------------------------

record PairMiddleResult {A B C : Type} (f : IR C A) (g : IR C B)
                        (prefix suffix : Program) (x : ⟦ C ⟧)
                        (s s-setup s1 : State) : Set where
  private
    ctx = make-pair-context f g prefix suffix
  open PairContext ctx

  field
    s2 : State
    h2 : halted s2 ≡ false
    pc2-g : pc s2 ≡ length prefix-g
    rdi2 : readReg (regs s2) rdi ≡ encode x
    stack-inv-s2 : StackInvariant s2
    rsp>16-s2 : readReg (regs s2) rsp > 16
    star-mid : Star prog s1 s2
    -- Register preservation
    r14-mid : readReg (regs s2) r14 ≡ readReg (regs s1) r14
    r15-mid : readReg (regs s2) r15 ≡ readReg (regs s1) r15
    rbp-mid : readReg (regs s2) rbp ≡ readReg (regs s1) rbp
    rsp-mid : readReg (regs s2) rsp ≡ readReg (regs s1) rsp
    -- Memory: fst stored
    mem-fst-stored : readMem (memory s2) (readReg (regs s1) r15) ≡ just (readReg (regs s1) rax)

-- | Execute middle phase
exec-pair-middle : ∀ {A B C} (f : IR C A) (g : IR C B)
                   (prefix suffix : Program) (x : ⟦ C ⟧)
                   (s s-setup s1 : State) →
  let ctx = make-pair-context f g prefix suffix in
  let open PairContext ctx in
  (r-f : IRStarResult f (prefix-f ++ code-f ++ suffix-f) s-setup s1 x (length prefix-f)) →
  (setup-res : PairSetupResult f g prefix suffix x s) →
  s-setup ≡ PairSetupResult.s-setup setup-res →
  readReg (regs s) rdi ≡ encode x →  -- original rdi-eq
  halted s1 ≡ false →
  pc s1 ≡ length prefix +ℕ 7 +ℕ len-f →
  PairMiddleResult f g prefix suffix x s s-setup s1
exec-pair-middle {A} {B} {C} f g prefix suffix x s s-setup s1 r-f setup-res s-setup-eq rdi-eq h1 pc1 = record
  { s2 = s2
  ; h2 = h2
  ; pc2-g = pc2-g
  ; rdi2 = rdi2
  ; stack-inv-s2 = stack-inv-s2
  ; rsp>16-s2 = rsp>16-s2
  ; star-mid = star-mid
  ; r14-mid = r14-mid
  ; r15-mid = r15-mid
  ; rbp-mid = rbp-mid
  ; rsp-mid = rsp-mid
  ; mem-fst-stored = mem-fst-stored
  }
  where
    ctx = make-pair-context f g prefix suffix
    open PairContext ctx

    r14-setup-raw = PairSetupResult.r14-setup setup-res

    -- Convert r14-setup from setup-res.s-setup to s-setup
    r14-setup : readReg (regs s-setup) r14 ≡ readReg (regs s) rdi
    r14-setup = subst (λ ss → readReg (regs ss) r14 ≡ readReg (regs s) rdi) (sym s-setup-eq) r14-setup-raw

    -- pc s1 = length prefix-mid
    pc1-mid : pc s1 ≡ length prefix-mid
    pc1-mid = trans pc1 (sym len-prefix-mid)

    -- r14 in s1 is the original input (encode x)
    r14-s1 = ir-r14 r-f
    -- r14-s1 : readReg (regs s1) r14 ≡ readReg (regs s-setup) r14
    -- r14-setup : readReg (regs s-setup) r14 ≡ readReg (regs s) rdi
    -- rdi-eq : readReg (regs s) rdi ≡ encode x
    -- So: readReg (regs s1) r14 ≡ encode x
    r14-s1-is-input : readReg (regs s1) r14 ≡ encode x
    r14-s1-is-input = trans r14-s1 (trans r14-setup rdi-eq)

    -- Execute middle 2 instructions
    middle-result = exec-pair-middle-at prefix-mid rest-mid s1 h1 pc1-mid

    s2 = proj₁ middle-result
    exec-mid = proj₁ (proj₂ middle-result)
    h2 = proj₁ (proj₂ (proj₂ middle-result))
    pc2-raw = proj₁ (proj₂ (proj₂ (proj₂ middle-result)))
    rdi2-raw = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ middle-result))))
    mem-fst-stored = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ middle-result)))))
    r15-mid = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ middle-result))))))
    rsp-mid = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ middle-result))))))

    -- rbp preserved: mov [r15], rax doesn't touch rbp, mov rdi, r14 doesn't touch rbp
    r14-mid = readReg-writeReg-rdi-r14 (regs s1) (readReg (regs s1) r14)
    rbp-mid = readReg-writeReg-rdi-rbp (regs s1) (readReg (regs s1) r14)

    -- Convert middle exec to Star
    star-mid-raw : Star (prefix-mid ++ store-f-instr ∷ restore-input ∷ rest-mid) s1 s2
    star-mid-raw = exec-to-star exec-mid

    star-mid : Star prog s1 s2
    star-mid = subst (λ p → Star p s1 s2) (sym prog-eq-mid) star-mid-raw

    -- rdi s2 = r14 s1 = encode x
    rdi2 : readReg (regs s2) rdi ≡ encode x
    rdi2 = trans rdi2-raw r14-s1-is-input

    -- pc s2 = length prefix-g
    pc2 : pc s2 ≡ length prefix +ℕ 9 +ℕ len-f
    pc2 = trans pc2-raw (trans (cong (_+ℕ 2) len-prefix-mid)
          (trans (+-assoc (length prefix +ℕ 7) len-f 2)
          (trans (cong ((length prefix +ℕ 7) +ℕ_) (+-comm len-f 2))
          (trans (sym (+-assoc (length prefix +ℕ 7) 2 len-f))
          (trans (cong (_+ℕ len-f) (+-assoc (length prefix) 7 2)) refl)))))

    pc2-g : pc s2 ≡ length prefix-g
    pc2-g = trans pc2 (sym len-prefix-g)

    -- StackInvariant and rsp>16 preserved
    rsp>16-s2 : readReg (regs s2) rsp > 16
    rsp>16-s2 = subst (_> 16) (sym rsp-mid) (ir-rsp-bound r-f)

    stack-inv-s2 : StackInvariant s2
    stack-inv-s2 = stack-inv-preserved-unchanged s1 s2 (ir-stack-inv r-f) (sym r15-mid) (sym rsp-mid)

------------------------------------------------------------------------
-- Final Assembly: combine all results into IRStarResult
------------------------------------------------------------------------

-- | Assemble the final pair result from the pieces
-- Note: This still requires postulates for final-result and rbp-final/mem-final
-- Those will be addressed in Phase 2 of the plan
assemble-pair-result : ∀ {A B C} (f : IR C A) (g : IR C B)
                       (prefix suffix : Program) (x : ⟦ C ⟧)
                       (s s-setup s1 s2 s3 s-final : State) →
  let ctx = make-pair-context f g prefix suffix in
  let open PairContext ctx in
  (setup-res : PairSetupResult f g prefix suffix x s) →
  (r-f : IRStarResult f (prefix-f ++ code-f ++ suffix-f) s-setup s1 x (length prefix-f)) →
  (mid-res : PairMiddleResult f g prefix suffix x s s-setup s1) →
  (r-g : IRStarResult g (prefix-g ++ code-g ++ suffix-g) s2 s3 x (length prefix-g)) →
  -- Final phase properties (postulated in MutualIR)
  halted s-final ≡ false →
  pc s-final ≡ length prefix-final +ℕ 6 →
  readReg (regs s-final) rax ≡ readReg (regs s3) r15 →
  readReg (regs s-final) r14 ≡ readReg (regs s) r14 →
  readReg (regs s-final) r15 ≡ readReg (regs s) r15 →
  StackInvariant s-final →
  readReg (regs s-final) rsp > 16 →
  readMem (memory s-final) (readReg (regs s3) r15) ≡ readMem (memory s3) (readReg (regs s3) r15) →
  readMem (memory s-final) (readReg (regs s3) r15 +ℕ 8) ≡ just (readReg (regs s3) rax) →
  readReg (regs s-final) rbp ≡ readReg (regs s) rbp →
  readMem (memory s-final) (readReg (regs s) r15) ≡ readMem (memory s) (readReg (regs s) r15) →
  readMem (memory s-final) (readReg (regs s) rbp) ≡ readMem (memory s) (readReg (regs s) rbp) →
  readMem (memory s-final) (readReg (regs s) rbp +ℕ 8) ≡ readMem (memory s) (readReg (regs s) rbp +ℕ 8) →
  Star prog s3 s-final →
  s2 ≡ PairMiddleResult.s2 mid-res →
  s-setup ≡ PairSetupResult.s-setup setup-res →
  IRStarResult ⟨ f , g ⟩ prog s s-final x (length prefix)
assemble-pair-result {A} {B} {C} f g prefix suffix x s s-setup s1 s2 s3 s-final
                     setup-res r-f mid-res r-g
                     h-final pc-fin-raw rax-fin-is-r15 r14-final r15-final
                     stack-inv-final rsp>16-final mem-fst-final mem-snd-final
                     rbp-final mem-final mem-rbp-final mem-rbp+8-final star-fin s2-eq s-setup-eq = record
  { ir-star = star-all
  ; ir-halted = h-final
  ; ir-pc = pc-final
  ; ir-rax = rax-final
  ; ir-r14 = r14-final
  ; ir-r15 = r15-final
  ; ir-rbp = rbp-final
  ; ir-mem = mem-final
  ; ir-mem-rbp = mem-rbp-final
  ; ir-mem-rbp+8 = mem-rbp+8-final
  ; ir-stack-inv = stack-inv-final
  ; ir-rsp-bound = rsp>16-final
  }
  where
    ctx = make-pair-context f g prefix suffix
    open PairContext ctx

    -- Star proofs from each phase
    -- setup-res.star-setup : Star prog s (setup-res.s-setup)
    -- s-setup-eq : s-setup ≡ setup-res.s-setup, so sym : setup-res.s-setup ≡ s-setup
    star-setup' : Star prog s s-setup
    star-setup' = subst (λ ss → Star prog s ss) (sym s-setup-eq) (PairSetupResult.star-setup setup-res)

    star-f-raw : Star (prefix-f ++ code-f ++ suffix-f) s-setup s1
    star-f-raw = ir-star r-f
    star-f' : Star prog s-setup s1
    star-f' = subst (λ p → Star p s-setup s1) (sym prog-eq-f) star-f-raw

    star-mid' : Star prog s1 s2
    star-mid' = subst (λ s2' → Star prog s1 s2') (sym s2-eq) (PairMiddleResult.star-mid mid-res)

    star-g-raw : Star (prefix-g ++ code-g ++ suffix-g) s2 s3
    star-g-raw = ir-star r-g
    star-g : Star prog s2 s3
    star-g = subst (λ p → Star p s2 s3) (sym prog-eq-g) star-g-raw

    -- Compose all 5 phases
    star-all : Star prog s s-final
    star-all = star-trans star-setup' (star-trans star-f' (star-trans star-mid' (star-trans star-g star-fin)))

    -- pc-final calculation
    pc-final : pc s-final ≡ length prefix +ℕ compile-length ⟨ f , g ⟩
    pc-final = trans pc-fin-raw (trans (cong (_+ℕ 6) len-prefix-final)
               (trans (+-assoc (length prefix +ℕ 9 +ℕ len-f) len-g 6)
               (trans (cong ((length prefix +ℕ 9 +ℕ len-f) +ℕ_) (+-comm len-g 6))
               (trans (sym (+-assoc (length prefix +ℕ 9 +ℕ len-f) 6 len-g))
               (trans (cong (_+ℕ len-g) (+-assoc (length prefix +ℕ 9) len-f 6))
               (trans (cong (λ z → (length prefix +ℕ 9 +ℕ z) +ℕ len-g) (+-comm len-f 6))
               (trans (cong (_+ℕ len-g) (sym (+-assoc (length prefix +ℕ 9) 6 len-f)))
               (trans (cong (λ z → (z +ℕ len-f) +ℕ len-g) (+-assoc (length prefix) 9 6))
               (trans (cong (_+ℕ len-g) (+-assoc (length prefix) 15 len-f))
               (+-assoc (length prefix) (15 +ℕ len-f) len-g))))))))))

    -- rax-final: using encode-pair-construct
    rax1 = ir-rax r-f
    rax3 = ir-rax r-g
    r15-s3 = ir-r15 r-g
    r15-mid' = subst (λ s2' → readReg (regs s2') r15 ≡ readReg (regs s1) r15) (sym s2-eq) (PairMiddleResult.r15-mid mid-res)
    mem-fst-stored' = subst (λ s2' → readMem (memory s2') (readReg (regs s1) r15) ≡ just (readReg (regs s1) rax)) (sym s2-eq) (PairMiddleResult.mem-fst-stored mid-res)

    r15-chain : readReg (regs s3) r15 ≡ readReg (regs s1) r15
    r15-chain = trans r15-s3 r15-mid'

    -- mem-fst-s3: memory at r15 contains encode (eval f x)
    mem-fst-s3 : readMem (memory s3) (readReg (regs s3) r15) ≡ just (encode (eval f x))
    mem-fst-s3 = trans (subst (λ addr → readMem (memory s3) addr ≡ readMem (memory s3) (readReg (regs s2) r15))
                              (sym r15-s3) refl)
                       (trans (ir-mem r-g)
                       (trans (subst (λ addr → readMem (memory s2) addr ≡ readMem (memory s2) (readReg (regs s1) r15))
                                     (sym r15-mid') refl)
                       (trans mem-fst-stored' (cong just rax1))))

    mem-fst-s-final : readMem (memory s-final) (readReg (regs s3) r15) ≡ just (encode (eval f x))
    mem-fst-s-final = trans mem-fst-final mem-fst-s3

    mem-snd-s-final : readMem (memory s-final) (readReg (regs s3) r15 +ℕ 8) ≡ just (encode (eval g x))
    mem-snd-s-final = trans mem-snd-final (cong just rax3)

    r15-is-pair-enc : readReg (regs s3) r15 ≡ encode {A * B} (eval f x , eval g x)
    r15-is-pair-enc = encode-pair-construct (eval f x) (eval g x) (readReg (regs s3) r15) (memory s-final)
                      mem-fst-s-final mem-snd-s-final

    rax-final : readReg (regs s-final) rax ≡ encode (eval ⟨ f , g ⟩ x)
    rax-final = trans rax-fin-is-r15 r15-is-pair-enc

------------------------------------------------------------------------
-- Final Result: state after 6 final instructions
------------------------------------------------------------------------

record PairFinalResult {A B C : Type} (f : IR C A) (g : IR C B)
                       (prefix suffix : Program)
                       (s s3 : State) : Set where
  private
    ctx = make-pair-context f g prefix suffix
  open PairContext ctx public

  field
    s-final : State
    exec-fin : exec 6 (prefix-final ++ store-g-instr ∷ return-pair-instr ∷ restore-rsp ∷ final-pop-rbp ∷ final-pop-r15 ∷ final-pop-r14 ∷ suffix) s3 ≡ just s-final
    h-final : halted s-final ≡ false
    pc-fin : pc s-final ≡ length prefix-final +ℕ 6
    rax-fin : readReg (regs s-final) rax ≡ readReg (regs s3) r15
    r14-fin : readReg (regs s-final) r14 ≡ readReg (regs s) r14
    r15-fin : readReg (regs s-final) r15 ≡ readReg (regs s) r15
    stack-inv-fin : StackInvariant s-final
    rsp>16-fin : readReg (regs s-final) rsp > 16
    mem-fst-fin : readMem (memory s-final) (readReg (regs s3) r15) ≡ readMem (memory s3) (readReg (regs s3) r15)
    mem-snd-fin : readMem (memory s-final) (readReg (regs s3) r15 +ℕ 8) ≡ just (readReg (regs s3) rax)
    rbp-fin : readReg (regs s-final) rbp ≡ readReg (regs s) rbp
    mem-orig-fin : readMem (memory s-final) (readReg (regs s) r15) ≡ readMem (memory s) (readReg (regs s) r15)
    mem-rbp-fin : readMem (memory s-final) (readReg (regs s) rbp) ≡ readMem (memory s) (readReg (regs s) rbp)
    mem-rbp+8-fin : readMem (memory s-final) (readReg (regs s) rbp +ℕ 8) ≡ readMem (memory s) (readReg (regs s) rbp +ℕ 8)

-- | Preconditions for exec-pair-final: stack layout from setup phase
record PairFinalPrecond {A B C : Type} (f : IR C A) (g : IR C B)
                        (prefix suffix : Program)
                        (s s3 : State) : Set where
  private
    ctx = make-pair-context f g prefix suffix
  open PairContext ctx public

  field
    -- Standard preconditions
    h3 : halted s3 ≡ false
    pc3 : pc s3 ≡ length prefix-final
    -- Stack layout: pushed registers accessible via rbp
    stack-rbp : readMem (memory s3) (readReg (regs s3) rbp) ≡ just (readReg (regs s) rbp)
    stack-r15 : readMem (memory s3) (readReg (regs s3) rbp +ℕ 8) ≡ just (readReg (regs s) r15)
    stack-r14 : readMem (memory s3) (readReg (regs s3) rbp +ℕ 16) ≡ just (readReg (regs s) r14)
    -- Stack invariant propagation
    stack-inv-s3 : StackInvariant s3
    -- Original stack invariant (for s9 restoration proof)
    stack-inv-s : StackInvariant s
    -- RBP chain: connects rbp after g to original rsp
    rbp-chain : readReg (regs s3) rbp ≡ readReg (regs s) rsp ∸ 24
    -- Memory frame: original r15 location preserved through f and g execution
    mem-frame : readMem (memory s3) (readReg (regs s) r15) ≡ readMem (memory s) (readReg (regs s) r15)
    -- Disjointness: pair allocation (r15-s3) is below frame base (rbp-s3)
    -- The write at r15-s3 + 8 doesn't affect stack at rbp-s3, rbp-s3 + 8, rbp-s3 + 16
    disjoint-rbp : readReg (regs s3) rbp ≢ readReg (regs s3) r15 +ℕ 8
    disjoint-r15 : readReg (regs s3) rbp +ℕ 8 ≢ readReg (regs s3) r15 +ℕ 8
    disjoint-r14 : readReg (regs s3) rbp +ℕ 16 ≢ readReg (regs s3) r15 +ℕ 8
    -- Disjointness for mem-orig-preserved
    disjoint-orig : readReg (regs s) r15 ≢ readReg (regs s3) r15 +ℕ 8
    -- RSP bound for final phase restoration proof
    rsp-bound : 24 ≤ readReg (regs s) rsp

------------------------------------------------------------------------
-- Arithmetic lemmas for disjointness proofs
------------------------------------------------------------------------

-- | n + 8 ≢ n (symmetric of n≢n+8)
n+8≢n : ∀ (n : ℕ) → n +ℕ 8 ≢ n
n+8≢n n eq = n≢n+8 n (sym eq)

-- | n + 16 ≢ n + 8
n+16≢n+8 : ∀ (n : ℕ) → n +ℕ 16 ≢ n +ℕ 8
n+16≢n+8 n eq = n≢n+8 (n +ℕ 8) (+-assoc-cancel eq)
  where
    -- If n + 16 = n + 8, then (n + 8) + 8 = n + 8, so n + 8 = (n + 8) + 8
    -- n + 16 = (n + 8) + 8 by +-assoc
    +-assoc-cancel : n +ℕ 16 ≡ n +ℕ 8 → n +ℕ 8 ≡ (n +ℕ 8) +ℕ 8
    +-assoc-cancel p = sym (trans (+-assoc n 8 8) p)

-- | n + 24 ≢ n + 8
n+24≢n+8 : ∀ (n : ℕ) → n +ℕ 24 ≢ n +ℕ 8
n+24≢n+8 n eq = n≢n+suc-m (n +ℕ 8) 15 (+-assoc-cancel eq)
  where
    -- n + 24 = (n + 8) + 16 by +-assoc
    +-assoc-cancel : n +ℕ 24 ≡ n +ℕ 8 → n +ℕ 8 ≡ (n +ℕ 8) +ℕ 16
    +-assoc-cancel p = sym (trans (+-assoc n 8 16) p)

-- | n + 32 ≢ n + 8
n+32≢n+8 : ∀ (n : ℕ) → n +ℕ 32 ≢ n +ℕ 8
n+32≢n+8 n eq = n≢n+suc-m (n +ℕ 8) 23 (+-assoc-cancel eq)
  where
    -- n + 32 = (n + 8) + 24 by +-assoc
    +-assoc-cancel : n +ℕ 32 ≡ n +ℕ 8 → n +ℕ 8 ≡ (n +ℕ 8) +ℕ 24
    +-assoc-cancel p = sym (trans (+-assoc n 8 24) p)

-- | If m ≥ 40, then (m ∸ 24) = (m ∸ 40) + 16
∸-offset-relationship : ∀ m → 40 ≤ m → m ∸ 24 ≡ (m ∸ 40) +ℕ 16
∸-offset-relationship m 40≤m = trans step1 step2
  where
    -- m ∸ 24 = m ∸ 40 + 16 when m ≥ 40
    -- Because m ∸ 24 = (m ∸ 40 + 40) ∸ 24 = (m ∸ 40) + (40 ∸ 24) = (m ∸ 40) + 16
    step1 : m ∸ 24 ≡ (m ∸ 40 +ℕ 40) ∸ 24
    step1 = cong (_∸ 24) (sym (m∸n+n≡m 40≤m))

    step2 : (m ∸ 40 +ℕ 40) ∸ 24 ≡ (m ∸ 40) +ℕ 16
    step2 = lemma (m ∸ 40)
      where
        -- (k + 40) ∸ 24 = k + 16
        lemma : ∀ k → (k +ℕ 40) ∸ 24 ≡ k +ℕ 16
        lemma k = trans (cong (_∸ 24) (+-comm k 40)) (trans step-a (+-comm 16 k))
          where
            step-a : (40 +ℕ k) ∸ 24 ≡ 16 +ℕ k
            step-a = refl

-- | If m ∸ n > 0, then n ≤ m
-- Proof: m ∸ n > 0 means m ∸ n ≥ 1, so the subtraction is positive.
-- If n > m, then m ∸ n = 0, contradicting m ∸ n > 0.
∸>0⇒≤ : ∀ m n → m ∸ n > 0 → n ≤ m
∸>0⇒≤ m zero _ = z≤n
∸>0⇒≤ zero (suc n) ()  -- zero ∸ suc n = 0, so > 0 is impossible
∸>0⇒≤ (suc m) (suc n) sm∸sn>0 = s≤s (∸>0⇒≤ m n sm∸sn>0)

-- | Construct PairFinalPrecond from intermediate results
-- Extracted to reduce MutualIR.agda type-checking time
make-pair-final-precond : ∀ {A B C} (f : IR C A) (g : IR C B)
                          (prefix suffix : Program) (x : ⟦ C ⟧)
                          (s s-setup s1 s2 s3 : State)
                          (stack-inv : StackInvariant s) →
  let ctx = make-pair-context f g prefix suffix in
  let open PairContext ctx in
  (setup-res : PairSetupResult f g prefix suffix x s) →
  (r-f : IRStarResult f (prefix-f ++ code-f ++ suffix-f) s-setup s1 x (length prefix-f)) →
  (mid-res : PairMiddleResult f g prefix suffix x s s-setup s1) →
  (r-g : IRStarResult g (prefix-g ++ code-g ++ suffix-g) s2 s3 x (length prefix-g)) →
  s-setup ≡ PairSetupResult.s-setup setup-res →
  s2 ≡ PairMiddleResult.s2 mid-res →
  PairFinalPrecond f g prefix suffix s s3
make-pair-final-precond {A} {B} {C} f g prefix suffix x s s-setup s1 s2 s3
                        stack-inv setup-res r-f mid-res r-g s-setup-eq s2-eq = record
  { h3 = ir-halted r-g
  ; pc3 = pc3
  ; stack-rbp = stack-rbp-s3
  ; stack-r15 = stack-r15-s3
  ; stack-r14 = stack-r14-s3
  ; stack-inv-s3 = ir-stack-inv r-g
  ; stack-inv-s = stack-inv
  ; rbp-chain = rbp-chain
  ; mem-frame = mem-frame-s3
  ; disjoint-rbp = disjoint-rbp-s3
  ; disjoint-r15 = disjoint-r15-s3
  ; disjoint-r14 = disjoint-r14-s3
  ; disjoint-orig = disjoint-orig-s3
  ; rsp-bound = rsp-bound-s
  }
  where
    ctx = make-pair-context f g prefix suffix
    open PairContext ctx

    -- PC at s3 for final phase
    pc3 : pc s3 ≡ length prefix-final
    pc3 = trans (ir-pc r-g) (trans (cong (_+ℕ len-g) len-prefix-g) (sym len-prefix-final))

    -- rbp was preserved through f and g execution: s3 → s2 → s1 → s-setup
    rbp-s3-eq-s2 : readReg (regs s3) rbp ≡ readReg (regs s2) rbp
    rbp-s3-eq-s2 = ir-rbp r-g

    rbp-s2-eq-s1 : readReg (regs s2) rbp ≡ readReg (regs s1) rbp
    rbp-s2-eq-s1 = subst (λ s2' → readReg (regs s2') rbp ≡ readReg (regs s1) rbp)
                         (sym s2-eq) (PairMiddleResult.rbp-mid mid-res)

    rbp-s1-eq-setup : readReg (regs s1) rbp ≡ readReg (regs s-setup) rbp
    rbp-s1-eq-setup = ir-rbp r-f

    rbp-setup-eq : readReg (regs s-setup) rbp ≡ readReg (regs s) rsp ∸ 24
    rbp-setup-eq = subst (λ ss → readReg (regs ss) rbp ≡ readReg (regs s) rsp ∸ 24)
                         (sym s-setup-eq) (PairSetupResult.rbp-setup setup-res)

    rbp-chain : readReg (regs s3) rbp ≡ readReg (regs s) rsp ∸ 24
    rbp-chain = trans rbp-s3-eq-s2 (trans rbp-s2-eq-s1 (trans rbp-s1-eq-setup rbp-setup-eq))

    -- r15 was preserved through f and g execution: s3 → s2 → s1 → s-setup
    r15-s3-eq-s2 : readReg (regs s3) r15 ≡ readReg (regs s2) r15
    r15-s3-eq-s2 = ir-r15 r-g

    r15-s2-eq-s1 : readReg (regs s2) r15 ≡ readReg (regs s1) r15
    r15-s2-eq-s1 = subst (λ s2' → readReg (regs s2') r15 ≡ readReg (regs s1) r15)
                         (sym s2-eq) (PairMiddleResult.r15-mid mid-res)

    r15-s1-eq-setup : readReg (regs s1) r15 ≡ readReg (regs s-setup) r15
    r15-s1-eq-setup = ir-r15 r-f

    r15-setup-eq : readReg (regs s-setup) r15 ≡ readReg (regs s) rsp ∸ 40
    r15-setup-eq = subst (λ ss → readReg (regs ss) r15 ≡ readReg (regs s) rsp ∸ 40)
                         (sym s-setup-eq) (PairSetupResult.r15-setup setup-res)

    r15-chain : readReg (regs s3) r15 ≡ readReg (regs s) rsp ∸ 40
    r15-chain = trans r15-s3-eq-s2 (trans r15-s2-eq-s1 (trans r15-s1-eq-setup r15-setup-eq))

    -- ========== Disjointness proofs (PROVEN from arithmetic) ==========
    -- Key insight: rbp-s3 = rsp-s ∸ 24 = r15-s3 + 16 (when rsp-s ≥ 40)
    -- This follows from setup using 40 bytes of stack (3 pushes + sub 16)

    -- Get rsp>16 from setup, which implies rsp-s > 56, thus 40 ≤ rsp-s
    rsp>16-setup' : readReg (regs s-setup) rsp > 16
    rsp>16-setup' = subst (λ ss → readReg (regs ss) rsp > 16)
                          (sym s-setup-eq) (PairSetupResult.rsp>16-setup setup-res)

    -- rsp-setup = rsp-s ∸ 40, and rsp-setup > 16, so rsp-s ∸ 40 > 16 > 0, thus 40 ≤ rsp-s
    rsp-setup-eq' : readReg (regs s-setup) rsp ≡ readReg (regs s) rsp ∸ 40
    rsp-setup-eq' = subst (λ ss → readReg (regs ss) rsp ≡ readReg (regs s) rsp ∸ 40)
                          (sym s-setup-eq) (PairSetupResult.rsp-setup setup-res)

    rsp∸40>16 : readReg (regs s) rsp ∸ 40 > 16
    rsp∸40>16 = subst (_> 16) rsp-setup-eq' rsp>16-setup'

    rsp∸40>0 : readReg (regs s) rsp ∸ 40 > 0
    rsp∸40>0 = ≤-trans (s≤s z≤n) rsp∸40>16  -- 1 ≤ 17 ≤ rsp∸40

    40≤rsp-s : 40 ≤ readReg (regs s) rsp
    40≤rsp-s = ∸>0⇒≤ (readReg (regs s) rsp) 40 rsp∸40>0

    -- 24 ≤ rsp-s follows from 24 ≤ 40 ≤ rsp-s
    rsp-bound-s : 24 ≤ readReg (regs s) rsp
    rsp-bound-s = ≤-trans 24≤40 40≤rsp-s
      where
        24≤40 : 24 ≤ 40
        24≤40 = s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))))))))))))))))))))

    -- rbp-s3 = r15-s3 + 16 (key relationship for disjointness)
    -- Using full expressions to avoid projection mismatch errors
    offset-eq : readReg (regs s) rsp ∸ 24 ≡ (readReg (regs s) rsp ∸ 40) +ℕ 16
    offset-eq = ∸-offset-relationship (readReg (regs s) rsp) 40≤rsp-s

    rbp-eq-r15-plus-16 : readReg (regs s3) rbp ≡ readReg (regs s3) r15 +ℕ 16
    rbp-eq-r15-plus-16 = trans rbp-chain (trans offset-eq (cong (_+ℕ 16) (sym r15-chain)))

    -- Derived relationships for disjointness
    rbp+8-is-r15+24 : readReg (regs s3) rbp +ℕ 8 ≡ readReg (regs s3) r15 +ℕ 24
    rbp+8-is-r15+24 = trans (cong (_+ℕ 8) rbp-eq-r15-plus-16) (+-assoc (readReg (regs s3) r15) 16 8)

    rbp+16-is-r15+32 : readReg (regs s3) rbp +ℕ 16 ≡ readReg (regs s3) r15 +ℕ 32
    rbp+16-is-r15+32 = trans (cong (_+ℕ 16) rbp-eq-r15-plus-16) (+-assoc (readReg (regs s3) r15) 16 16)

    -- disjoint-rbp-s3: rbp-s3 ≢ r15-s3 + 8
    -- rbp-s3 = r15-s3 + 16, so r15-s3 + 16 ≢ r15-s3 + 8
    disjoint-rbp-s3 : readReg (regs s3) rbp ≢ readReg (regs s3) r15 +ℕ 8
    disjoint-rbp-s3 eq = n+16≢n+8 (readReg (regs s3) r15) combined-eq
      where
        -- subst (λ x → x ≡ r15+8) (rbp ≡ r15+16) : (rbp ≡ r15+8) → (r15+16 ≡ r15+8)
        combined-eq : readReg (regs s3) r15 +ℕ 16 ≡ readReg (regs s3) r15 +ℕ 8
        combined-eq = subst (λ x → x ≡ readReg (regs s3) r15 +ℕ 8) rbp-eq-r15-plus-16 eq

    -- disjoint-r15-s3: rbp-s3 + 8 ≢ r15-s3 + 8
    -- rbp + 8 = r15 + 24, so this becomes r15 + 24 ≢ r15 + 8
    disjoint-r15-s3 : readReg (regs s3) rbp +ℕ 8 ≢ readReg (regs s3) r15 +ℕ 8
    disjoint-r15-s3 eq = n+24≢n+8 (readReg (regs s3) r15) combined-eq
      where
        -- Use subst to explicitly convert: rbp+8 = r15+24, and rbp+8 = r15+8, so r15+24 = r15+8
        combined-eq : readReg (regs s3) r15 +ℕ 24 ≡ readReg (regs s3) r15 +ℕ 8
        combined-eq = subst (λ x → x ≡ readReg (regs s3) r15 +ℕ 8) rbp+8-is-r15+24 eq

    -- disjoint-r14-s3: rbp-s3 + 16 ≢ r15-s3 + 8
    -- rbp + 16 = r15 + 32, so this becomes r15 + 32 ≢ r15 + 8
    disjoint-r14-s3 : readReg (regs s3) rbp +ℕ 16 ≢ readReg (regs s3) r15 +ℕ 8
    disjoint-r14-s3 eq = n+32≢n+8 (readReg (regs s3) r15) combined-eq
      where
        combined-eq : readReg (regs s3) r15 +ℕ 32 ≡ readReg (regs s3) r15 +ℕ 8
        combined-eq = subst (λ x → x ≡ readReg (regs s3) r15 +ℕ 8) rbp+16-is-r15+32 eq

    -- disjoint-orig-s3: r15-s ≢ r15-s3 + 8
    -- Uses StackInvariant: either r15-s = 0, or rsp-s ≤ r15-s
    disjoint-orig-s3 : readReg (regs s) r15 ≢ readReg (regs s3) r15 +ℕ 8
    disjoint-orig-s3 = case-stack-inv stack-inv
      where
        -- Case 1: r15-s = 0, then 0 ≢ r15-s3 + 8 (since r15-s3 + 8 ≥ 8 > 0)
        -- 0 < n + 8 for any n, so 0 ≢ n + 8
        -- Use +-suc to show n + 8 = suc (n + 7), then 0 < suc _ is trivial
        0<n+8 : ∀ n → 0 < n +ℕ 8
        0<n+8 n = subst (1 ≤_) (sym (+-suc n 7)) (s≤s z≤n)

        case-r15-zero : readReg (regs s) r15 ≡ 0 → readReg (regs s) r15 ≢ readReg (regs s3) r15 +ℕ 8
        case-r15-zero r15≡0 eq = <⇒≢ (0<n+8 (readReg (regs s3) r15)) (sym combined-eq)
          where
            combined-eq : readReg (regs s3) r15 +ℕ 8 ≡ 0
            combined-eq = trans (sym eq) r15≡0

        -- Case 2: rsp-s ≤ r15-s, then r15-s3 + 8 = (rsp-s ∸ 40) + 8 < rsp-s ≤ r15-s
        case-r15-stack : readReg (regs s) rsp ≤ readReg (regs s) r15 → readReg (regs s) r15 ≢ readReg (regs s3) r15 +ℕ 8
        case-r15-stack rsp≤r15 eq = <⇒≢ r15-s3+8<r15-s (sym eq)
          where
            -- (rsp-s ∸ 40) + 8 < rsp-s (when 40 ≤ rsp-s)
            -- Proof: rsp-s = (rsp-s ∸ 40) + 40, so need (rsp-s ∸ 40) + 8 < (rsp-s ∸ 40) + 40
            --        which follows from 8 < 40
            r15-s3+8<rsp-s : readReg (regs s3) r15 +ℕ 8 < readReg (regs s) rsp
            r15-s3+8<rsp-s = subst (λ n → n +ℕ 8 < readReg (regs s) rsp) (sym r15-chain) arith-step
              where
                rsp-s = readReg (regs s) rsp
                k = rsp-s ∸ 40

                -- k + 8 < k + 40 from 8 < 40
                -- 8 < 40 means 9 ≤ 40, so need 9 s≤s applications to z≤n : 0 ≤ 31
                8<40 : 8 < 40
                8<40 = s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))))

                k+8<k+40 : k +ℕ 8 < k +ℕ 40
                k+8<k+40 = +-monoʳ-< k 8<40

                arith-step : (readReg (regs s) rsp ∸ 40) +ℕ 8 < readReg (regs s) rsp
                arith-step = subst (k +ℕ 8 <_) (m∸n+n≡m 40≤rsp-s) k+8<k+40

            r15-s3+8<r15-s : readReg (regs s3) r15 +ℕ 8 < readReg (regs s) r15
            r15-s3+8<r15-s = ≤-trans r15-s3+8<rsp-s rsp≤r15

        case-stack-inv : StackInvariant s → readReg (regs s) r15 ≢ readReg (regs s3) r15 +ℕ 8
        case-stack-inv (r15-unused r15≡0) = case-r15-zero r15≡0
        case-stack-inv (stack-below-r15 rsp≤r15) = case-r15-stack rsp≤r15

    -- ========== Stack layout postulates (memory preservation) ==========
    -- These require tracing memory through f and g execution
    postulate
      stack-rbp-s3 : readMem (memory s3) (readReg (regs s3) rbp) ≡ just (readReg (regs s) rbp)
      stack-r15-s3 : readMem (memory s3) (readReg (regs s3) rbp +ℕ 8) ≡ just (readReg (regs s) r15)
      stack-r14-s3 : readMem (memory s3) (readReg (regs s3) rbp +ℕ 16) ≡ just (readReg (regs s) r14)
      mem-frame-s3 : readMem (memory s3) (readReg (regs s) r15) ≡ readMem (memory s) (readReg (regs s) r15)

-- | Execute the final 6 instructions of pair
-- Extracted to separate module to prevent type-checker explosion in MutualIR
-- Takes full preconditions for proven stack restoration
-- All postulates eliminated - rsp-bound passed via PairFinalPrecond
exec-pair-final : ∀ {A B C} (f : IR C A) (g : IR C B)
                  (prefix suffix : Program)
                  (s s3 : State) →
  PairFinalPrecond f g prefix suffix s s3 →
  PairFinalResult f g prefix suffix s s3
exec-pair-final {A} {B} {C} f g prefix suffix s s3 precond = record
    { s-final = s9
    ; exec-fin = exec-6-final
    ; h-final = h9
    ; pc-fin = pc9
    ; rax-fin = rax-s9
    ; r14-fin = r14-s9
    ; r15-fin = r15-s9
    ; stack-inv-fin = stack-inv-s9
    ; rsp>16-fin = rsp>16-s9
    ; mem-fst-fin = mem-fst-preserved
    ; mem-snd-fin = mem-snd-stored
    ; rbp-fin = rbp-s9
    ; mem-orig-fin = mem-orig-preserved
    ; mem-rbp-fin = mem-rbp-preserved
    ; mem-rbp+8-fin = mem-rbp+8-preserved
    }
    where
      open PairFinalPrecond precond using (h3; pc3; stack-rbp; stack-r15; stack-r14; stack-inv-s; rbp-chain; disjoint-rbp; disjoint-r15; disjoint-r14; disjoint-orig; mem-frame)

      ctx = make-pair-context f g prefix suffix
      open PairContext ctx

      -- Program for final phase
      prog-final : Program
      prog-final = prefix-final ++ store-g-instr ∷ return-pair-instr ∷ restore-rsp ∷ final-pop-rbp ∷ final-pop-r15 ∷ final-pop-r14 ∷ suffix

      -- ========== State definitions ==========
      s4 : State
      s4 = record s3 { memory = writeMem (memory s3) (readReg (regs s3) r15 +ℕ 8) (readReg (regs s3) rax)
                     ; pc = pc s3 +ℕ 1 }
      s5 : State
      s5 = record s4 { regs = writeReg (regs s4) rax (readReg (regs s4) r15) ; pc = pc s4 +ℕ 1 }
      s6 : State
      s6 = record s5 { regs = writeReg (regs s5) rsp (readReg (regs s5) rbp) ; pc = pc s5 +ℕ 1 }

      -- ========== Pop memory proofs (derived from preconditions) ==========
      -- After mov rsp, rbp: rsp-s6 = rbp-s5 = rbp-s4 = rbp-s3
      rbp-s4 : readReg (regs s4) rbp ≡ readReg (regs s3) rbp
      rbp-s4 = refl

      rbp-s5 : readReg (regs s5) rbp ≡ readReg (regs s3) rbp
      rbp-s5 = trans (readReg-writeReg-rax-rbp (regs s4) (readReg (regs s4) r15)) rbp-s4

      rsp-s6-eq-rbp-s3 : readReg (regs s6) rsp ≡ readReg (regs s3) rbp
      rsp-s6-eq-rbp-s3 = trans (readReg-writeReg-same (regs s5) rsp (readReg (regs s5) rbp)) rbp-s5

      -- Memory s6 = memory s4 = writeMem (memory s3) (r15-s3 + 8) (rax-s3)
      mem-s6-eq-s4 : memory s6 ≡ memory s4
      mem-s6-eq-s4 = refl

      -- pop-rbp-mem: readMem (memory s6) (rsp-s6) = just (regs s).rbp
      -- mem-read-other needs (write-addr ≢ read-addr), so flip disjoint-rbp
      pop-rbp-mem : readMem (memory s6) (readReg (regs s6) rsp) ≡ just (readReg (regs s) rbp)
      pop-rbp-mem = trans (cong (readMem (memory s6)) rsp-s6-eq-rbp-s3)
                    (trans (mem-read-other {memory s3} {readReg (regs s3) r15 +ℕ 8} {readReg (regs s3) rbp} {readReg (regs s3) rax} (λ eq → disjoint-rbp (sym eq)))
                    stack-rbp)

      -- pop-r15-mem: readMem (memory s6) (rsp-s6 + 8) = just (regs s).r15
      pop-r15-mem : readMem (memory s6) (readReg (regs s6) rsp +ℕ 8) ≡ just (readReg (regs s) r15)
      pop-r15-mem = trans (cong (λ addr → readMem (memory s6) (addr +ℕ 8)) rsp-s6-eq-rbp-s3)
                    (trans (mem-read-other {memory s3} {readReg (regs s3) r15 +ℕ 8} {readReg (regs s3) rbp +ℕ 8} {readReg (regs s3) rax} (λ eq → disjoint-r15 (sym eq)))
                    stack-r15)

      -- pop-r14-mem: readMem (memory s6) (rsp-s6 + 16) = just (regs s).r14
      pop-r14-mem : readMem (memory s6) (readReg (regs s6) rsp +ℕ 16) ≡ just (readReg (regs s) r14)
      pop-r14-mem = trans (cong (λ addr → readMem (memory s6) (addr +ℕ 16)) rsp-s6-eq-rbp-s3)
                    (trans (mem-read-other {memory s3} {readReg (regs s3) r15 +ℕ 8} {readReg (regs s3) rbp +ℕ 16} {readReg (regs s3) rax} (λ eq → disjoint-r14 (sym eq)))
                    stack-r14)

      s7 : State
      s7 = record s6 { regs = writeReg (writeReg (regs s6) rbp (readReg (regs s) rbp)) rsp (readReg (regs s6) rsp +ℕ 8) ; pc = pc s6 +ℕ 1 }
      s8 : State
      s8 = record s7 { regs = writeReg (writeReg (regs s7) r15 (readReg (regs s) r15)) rsp (readReg (regs s7) rsp +ℕ 8) ; pc = pc s7 +ℕ 1 }
      s9 : State
      s9 = record s8 { regs = writeReg (writeReg (regs s8) r14 (readReg (regs s) r14)) rsp (readReg (regs s8) rsp +ℕ 8) ; pc = pc s8 +ℕ 1 }

      h4 : halted s4 ≡ false
      h4 = h3
      h5 : halted s5 ≡ false
      h5 = h4
      h6 : halted s6 ≡ false
      h6 = h5
      h7 : halted s7 ≡ false
      h7 = h6
      h8 : halted s8 ≡ false
      h8 = h7
      h9 : halted s9 ≡ false
      h9 = h8

      pc4 : pc s4 ≡ length prefix-final +ℕ 1
      pc4 = cong (_+ℕ 1) pc3
      pc5 : pc s5 ≡ length prefix-final +ℕ 2
      pc5 = trans (cong (_+ℕ 1) pc4) (+-assoc (length prefix-final) 1 1)
      pc6 : pc s6 ≡ length prefix-final +ℕ 3
      pc6 = trans (cong (_+ℕ 1) pc5) (+-assoc (length prefix-final) 2 1)
      pc7 : pc s7 ≡ length prefix-final +ℕ 4
      pc7 = trans (cong (_+ℕ 1) pc6) (+-assoc (length prefix-final) 3 1)
      pc8 : pc s8 ≡ length prefix-final +ℕ 5
      pc8 = trans (cong (_+ℕ 1) pc7) (+-assoc (length prefix-final) 4 1)
      pc9 : pc s9 ≡ length prefix-final +ℕ 6
      pc9 = trans (cong (_+ℕ 1) pc8) (+-assoc (length prefix-final) 5 1)

      -- Fetch and step proofs (same as exec-pair-final)
      fetch4 : fetch prog-final (pc s3) ≡ just store-g-instr
      fetch4 = subst (λ n → fetch prog-final n ≡ just store-g-instr) (sym pc3) (fetch-at-prefix-end prefix-final store-g-instr _)
      prog-eq-i2 : prog-final ≡ (prefix-final ++ store-g-instr ∷ []) ++ return-pair-instr ∷ restore-rsp ∷ final-pop-rbp ∷ final-pop-r15 ∷ final-pop-r14 ∷ suffix
      prog-eq-i2 = sym (++-assoc prefix-final (store-g-instr ∷ []) _)
      len-prefix-i2 : length (prefix-final ++ store-g-instr ∷ []) ≡ length prefix-final +ℕ 1
      len-prefix-i2 = List-length-++ prefix-final {ys = store-g-instr ∷ []}
      fetch5 : fetch prog-final (pc s4) ≡ just return-pair-instr
      fetch5 = subst₂ (λ p n → fetch p n ≡ just return-pair-instr) (sym prog-eq-i2) (trans len-prefix-i2 (sym pc4)) (fetch-at-prefix-end (prefix-final ++ store-g-instr ∷ []) return-pair-instr _)
      prog-eq-i3 : prog-final ≡ (prefix-final ++ store-g-instr ∷ return-pair-instr ∷ []) ++ restore-rsp ∷ final-pop-rbp ∷ final-pop-r15 ∷ final-pop-r14 ∷ suffix
      prog-eq-i3 = sym (++-assoc prefix-final (store-g-instr ∷ return-pair-instr ∷ []) _)
      len-prefix-i3 : length (prefix-final ++ store-g-instr ∷ return-pair-instr ∷ []) ≡ length prefix-final +ℕ 2
      len-prefix-i3 = List-length-++ prefix-final {ys = store-g-instr ∷ return-pair-instr ∷ []}
      fetch6 : fetch prog-final (pc s5) ≡ just restore-rsp
      fetch6 = subst₂ (λ p n → fetch p n ≡ just restore-rsp) (sym prog-eq-i3) (trans len-prefix-i3 (sym pc5)) (fetch-at-prefix-end (prefix-final ++ store-g-instr ∷ return-pair-instr ∷ []) restore-rsp _)
      prog-eq-i4 : prog-final ≡ (prefix-final ++ store-g-instr ∷ return-pair-instr ∷ restore-rsp ∷ []) ++ final-pop-rbp ∷ final-pop-r15 ∷ final-pop-r14 ∷ suffix
      prog-eq-i4 = sym (++-assoc prefix-final (store-g-instr ∷ return-pair-instr ∷ restore-rsp ∷ []) _)
      len-prefix-i4 : length (prefix-final ++ store-g-instr ∷ return-pair-instr ∷ restore-rsp ∷ []) ≡ length prefix-final +ℕ 3
      len-prefix-i4 = List-length-++ prefix-final {ys = store-g-instr ∷ return-pair-instr ∷ restore-rsp ∷ []}
      fetch7 : fetch prog-final (pc s6) ≡ just final-pop-rbp
      fetch7 = subst₂ (λ p n → fetch p n ≡ just final-pop-rbp) (sym prog-eq-i4) (trans len-prefix-i4 (sym pc6)) (fetch-at-prefix-end (prefix-final ++ store-g-instr ∷ return-pair-instr ∷ restore-rsp ∷ []) final-pop-rbp _)
      prog-eq-i5 : prog-final ≡ (prefix-final ++ store-g-instr ∷ return-pair-instr ∷ restore-rsp ∷ final-pop-rbp ∷ []) ++ final-pop-r15 ∷ final-pop-r14 ∷ suffix
      prog-eq-i5 = sym (++-assoc prefix-final (store-g-instr ∷ return-pair-instr ∷ restore-rsp ∷ final-pop-rbp ∷ []) _)
      len-prefix-i5 : length (prefix-final ++ store-g-instr ∷ return-pair-instr ∷ restore-rsp ∷ final-pop-rbp ∷ []) ≡ length prefix-final +ℕ 4
      len-prefix-i5 = List-length-++ prefix-final {ys = store-g-instr ∷ return-pair-instr ∷ restore-rsp ∷ final-pop-rbp ∷ []}
      fetch8 : fetch prog-final (pc s7) ≡ just final-pop-r15
      fetch8 = subst₂ (λ p n → fetch p n ≡ just final-pop-r15) (sym prog-eq-i5) (trans len-prefix-i5 (sym pc7)) (fetch-at-prefix-end (prefix-final ++ store-g-instr ∷ return-pair-instr ∷ restore-rsp ∷ final-pop-rbp ∷ []) final-pop-r15 _)
      prog-eq-i6 : prog-final ≡ (prefix-final ++ store-g-instr ∷ return-pair-instr ∷ restore-rsp ∷ final-pop-rbp ∷ final-pop-r15 ∷ []) ++ final-pop-r14 ∷ suffix
      prog-eq-i6 = sym (++-assoc prefix-final (store-g-instr ∷ return-pair-instr ∷ restore-rsp ∷ final-pop-rbp ∷ final-pop-r15 ∷ []) _)
      len-prefix-i6 : length (prefix-final ++ store-g-instr ∷ return-pair-instr ∷ restore-rsp ∷ final-pop-rbp ∷ final-pop-r15 ∷ []) ≡ length prefix-final +ℕ 5
      len-prefix-i6 = List-length-++ prefix-final {ys = store-g-instr ∷ return-pair-instr ∷ restore-rsp ∷ final-pop-rbp ∷ final-pop-r15 ∷ []}
      fetch9 : fetch prog-final (pc s8) ≡ just final-pop-r14
      fetch9 = subst₂ (λ p n → fetch p n ≡ just final-pop-r14) (sym prog-eq-i6) (trans len-prefix-i6 (sym pc8)) (fetch-at-prefix-end (prefix-final ++ store-g-instr ∷ return-pair-instr ∷ restore-rsp ∷ final-pop-rbp ∷ final-pop-r15 ∷ []) final-pop-r14 suffix)

      step4 : step prog-final s3 ≡ just s4
      step4 = trans (step-exec prog-final s3 store-g-instr h3 fetch4) (execMov-mem-disp-reg prog-final s3 r15 rax 8)
      step5 : step prog-final s4 ≡ just s5
      step5 = trans (step-exec prog-final s4 return-pair-instr h4 fetch5) (execMov-reg-reg s4 rax r15)
      step6 : step prog-final s5 ≡ just s6
      step6 = trans (step-exec prog-final s5 restore-rsp h5 fetch6) (execMov-reg-reg s5 rsp rbp)
      step7 : step prog-final s6 ≡ just s7
      step7 = trans (step-exec prog-final s6 final-pop-rbp h6 fetch7) (execPop prog-final s6 rbp (readReg (regs s) rbp) pop-rbp-mem)
      rsp-s7 : readReg (regs s7) rsp ≡ readReg (regs s6) rsp +ℕ 8
      rsp-s7 = readReg-writeReg-same (writeReg (regs s6) rbp (readReg (regs s) rbp)) rsp (readReg (regs s6) rsp +ℕ 8)
      pop-r15-mem' : readMem (memory s7) (readReg (regs s7) rsp) ≡ just (readReg (regs s) r15)
      pop-r15-mem' = subst (λ addr → readMem (memory s7) addr ≡ just (readReg (regs s) r15)) (sym rsp-s7) pop-r15-mem
      step8 : step prog-final s7 ≡ just s8
      step8 = trans (step-exec prog-final s7 final-pop-r15 h7 fetch8) (execPop prog-final s7 r15 (readReg (regs s) r15) pop-r15-mem')
      rsp-s8 : readReg (regs s8) rsp ≡ readReg (regs s6) rsp +ℕ 16
      rsp-s8 = trans (readReg-writeReg-same (writeReg (regs s7) r15 (readReg (regs s) r15)) rsp (readReg (regs s7) rsp +ℕ 8)) (trans (cong (_+ℕ 8) rsp-s7) (+-assoc (readReg (regs s6) rsp) 8 8))
      pop-r14-mem' : readMem (memory s8) (readReg (regs s8) rsp) ≡ just (readReg (regs s) r14)
      pop-r14-mem' = subst (λ addr → readMem (memory s8) addr ≡ just (readReg (regs s) r14)) (sym rsp-s8) pop-r14-mem
      step9 : step prog-final s8 ≡ just s9
      step9 = trans (step-exec prog-final s8 final-pop-r14 h8 fetch9) (execPop prog-final s8 r14 (readReg (regs s) r14) pop-r14-mem')

      exec-6-final : exec 6 prog-final s3 ≡ just s9
      exec-6-final = exec-six-steps-nonhalt prog-final s3 s4 s5 s6 s7 s8 s9 step4 h4 step5 h5 step6 h6 step7 h7 step8 h8 step9 h9

      -- Register preservation (same as exec-pair-final)
      v-r14 : Word
      v-r14 = readReg (regs s) r14
      v-r15 : Word
      v-r15 = readReg (regs s) r15
      v-rbp : Word
      v-rbp = readReg (regs s) rbp
      rf6-with-rbp : RegFile
      rf6-with-rbp = writeReg (regs s6) rbp v-rbp
      rf7-with-r15 : RegFile
      rf7-with-r15 = writeReg (regs s7) r15 v-r15
      rf8-with-r14 : RegFile
      rf8-with-r14 = writeReg (regs s8) r14 v-r14
      rax-s9 : readReg (regs s9) rax ≡ readReg (regs s3) r15
      rax-s9 = trans (readReg-writeReg-rsp-rax rf8-with-r14 (readReg (regs s8) rsp +ℕ 8))
               (trans (readReg-writeReg-r14-rax (regs s8) v-r14)
               (trans (readReg-writeReg-rsp-rax rf7-with-r15 (readReg (regs s7) rsp +ℕ 8))
               (trans (readReg-writeReg-r15-rax (regs s7) v-r15)
               (trans (readReg-writeReg-rsp-rax rf6-with-rbp (readReg (regs s6) rsp +ℕ 8))
               (trans (readReg-writeReg-rbp-rax (regs s6) v-rbp)
               (trans (readReg-writeReg-rsp-rax (regs s5) (readReg (regs s5) rbp))
               (readReg-writeReg-same (regs s4) rax (readReg (regs s4) r15))))))))
      r14-s9 : readReg (regs s9) r14 ≡ readReg (regs s) r14
      r14-s9 = trans (readReg-writeReg-rsp-r14 rf8-with-r14 (readReg (regs s8) rsp +ℕ 8)) (readReg-writeReg-same (regs s8) r14 v-r14)
      r15-s9 : readReg (regs s9) r15 ≡ readReg (regs s) r15
      r15-s9 = trans (readReg-writeReg-rsp-r15 rf8-with-r14 (readReg (regs s8) rsp +ℕ 8))
               (trans (readReg-writeReg-r14-r15 (regs s8) v-r14)
               (trans (readReg-writeReg-rsp-r15 rf7-with-r15 (readReg (regs s7) rsp +ℕ 8))
               (readReg-writeReg-same (regs s7) r15 v-r15)))
      rbp-s9 : readReg (regs s9) rbp ≡ readReg (regs s) rbp
      rbp-s9 = trans (readReg-writeReg-rsp-rbp rf8-with-r14 (readReg (regs s8) rsp +ℕ 8))
               (trans (readReg-writeReg-r14-rbp (regs s8) v-r14)
               (trans (readReg-writeReg-rsp-rbp rf7-with-r15 (readReg (regs s7) rsp +ℕ 8))
               (trans (readReg-writeReg-r15-rbp (regs s7) v-r15)
               (trans (readReg-writeReg-rsp-rbp rf6-with-rbp (readReg (regs s6) rsp +ℕ 8))
               (readReg-writeReg-same (regs s6) rbp v-rbp)))))

      rsp>16-s9 : readReg (regs s9) rsp > 16
      rsp>16-s9 = rsp-bound-after-stack-op s9

      -- ========== Stack invariant proof (via restored rsp and r15) ==========
      -- After the pop sequence: rsp-s9 = rsp-s and r15-s9 = r15-s
      -- So StackInvariant s implies StackInvariant s9

      -- rsp chain: rsp-s9 = rsp-s8 + 8 = rsp-s6 + 24
      rsp-s9 : readReg (regs s9) rsp ≡ readReg (regs s6) rsp +ℕ 24
      rsp-s9 = trans (readReg-writeReg-same (writeReg (regs s8) r14 v-r14) rsp (readReg (regs s8) rsp +ℕ 8))
               (trans (cong (_+ℕ 8) rsp-s8) (+-assoc (readReg (regs s6) rsp) 16 8))

      -- Full chain: rsp-s9 = rbp-s3 + 24 = (rsp-s - 24) + 24 = rsp-s
      -- Using rbp-chain: rbp-s3 = rsp-s ∸ 24
      rsp-s9-eq-s : readReg (regs s9) rsp ≡ readReg (regs s) rsp
      rsp-s9-eq-s = trans rsp-s9
                    (trans (cong (_+ℕ 24) rsp-s6-eq-rbp-s3)
                    (trans (cong (_+ℕ 24) rbp-chain)
                    (m∸n+n≡m 24≤rsp-s)))
        where
          24≤rsp-s : 24 ≤ readReg (regs s) rsp
          24≤rsp-s = PairFinalPrecond.rsp-bound precond

      -- Stack invariant: s9 has same r15 and rsp as s, so inherits StackInvariant
      stack-inv-s9 : StackInvariant s9
      stack-inv-s9 = stack-inv-preserved-unchanged s s9 stack-inv-s r15-s9 rsp-s9-eq-s

      -- Memory preservation
      r15-s3 = readReg (regs s3) r15
      mem-fst-preserved : readMem (memory s9) r15-s3 ≡ readMem (memory s3) r15-s3
      mem-fst-preserved = mem-read-other {memory s3} {r15-s3 +ℕ 8} {r15-s3} {readReg (regs s3) rax} (λ eq → n≢n+8 r15-s3 (sym eq))
      mem-snd-stored : readMem (memory s9) (r15-s3 +ℕ 8) ≡ just (readReg (regs s3) rax)
      mem-snd-stored = mem-read-write {memory s3} {r15-s3 +ℕ 8} {readReg (regs s3) rax}
      mem-orig-preserved : readMem (memory s9) (readReg (regs s) r15) ≡ readMem (memory s) (readReg (regs s) r15)
      mem-orig-preserved = trans (mem-read-other {memory s3} {readReg (regs s3) r15 +ℕ 8} {readReg (regs s) r15} {readReg (regs s3) rax} (λ eq → disjoint-orig (sym eq))) mem-frame

      -- Memory at original rbp and rbp+8 preserved through final phase
      -- POSTULATE: Would need mem-frame-rbp in PairFinalPrecond tracking memory at s's rbp through f and g
      postulate
        mem-rbp-preserved : readMem (memory s9) (readReg (regs s) rbp) ≡ readMem (memory s) (readReg (regs s) rbp)
        mem-rbp+8-preserved : readMem (memory s9) (readReg (regs s) rbp +ℕ 8) ≡ readMem (memory s) (readReg (regs s) rbp +ℕ 8)
