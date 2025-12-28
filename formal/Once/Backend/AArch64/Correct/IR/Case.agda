{-# OPTIONS --sized-types #-}
------------------------------------------------------------------------
-- Once.Backend.AArch64.Correct.IR.Case
--
-- Helper records and functions for case proofs.
-- Extracts non-recursive parts to reduce mutual block compilation time.
-- The recursive calls stay in MutualIR.agda.
------------------------------------------------------------------------

module Once.Backend.AArch64.Correct.IR.Case where

open import Once.Type
open import Once.IR
open import Once.Semantics hiding (code-ptr; env-addr; semantics)

open import Once.Backend.AArch64.Syntax
open import Once.Backend.AArch64.Semantics
open State
open import Once.Backend.AArch64.CodeGen

open import Once.Backend.AArch64.Correct.Foundation using (encode)
open import Once.Backend.AArch64.Correct.CompileLength using (compile-length-correct)

open import Data.Bool using (false)
open import Data.Nat using (ℕ; zero; suc; _∸_; _>_; _≤_) renaming (_+_ to _+ℕ_)
open import Data.Nat.Properties using (+-assoc; +-comm; +-identityʳ; ≤-refl)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.List.Properties using (++-assoc; ++-identityʳ) renaming (length-++ to List-length-++)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; ∃-syntax)
open import Data.Sum using (inj₁; inj₂)
open import Data.Maybe using (just)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; subst₂; cong)
open import Relation.Binary.PropositionalEquality.Properties using (module ≡-Reasoning)
open ≡-Reasoning

------------------------------------------------------------------------
-- List helpers
------------------------------------------------------------------------

-- | Key helper: (xs ++ x ∷ []) ++ ys ≡ xs ++ x ∷ ys
snoc-append : ∀ {A : Set} (xs : List A) (x : A) (ys : List A) →
              (xs ++ x ∷ []) ++ ys ≡ xs ++ x ∷ ys
snoc-append xs x ys = trans (++-assoc xs (x ∷ []) ys) refl

-- | Length of concatenation
length-++ : ∀ {A : Set} (xs ys : List A) → length (xs ++ ys) ≡ length xs +ℕ length ys
length-++ [] ys = refl
length-++ (x ∷ xs) ys = cong suc (length-++ xs ys)

------------------------------------------------------------------------
-- Case Context: computed values that don't depend on execution
------------------------------------------------------------------------
--
-- The case [ f , g ] code structure for AArch64:
--   0: ldr x9, [x0]         -- load tag
--   1: cmp x9, #0           -- compare with 0
--   2: b.ne right-branch    -- branch if not zero (inr)
--   3: ldr x0, [x0, #8]     -- load value for left case (inl)
--   4 to 3+|f|: code-f      -- execute f
--   4+|f|: b end            -- skip right branch
--   5+|f|: label            -- right-branch label
--   6+|f|: ldr x0, [x0, #8] -- load value for right case
--   7+|f| to 6+|f|+|g|: code-g  -- execute g
--   7+|f|+|g|: label        -- end label

record CaseContext {i} {A B C : Type} (f : IR i A C) (g : IR i B C)
                   (prefix suffix : Program) : Set where
  field
    -- Computed lengths
    len-f : ℕ
    len-g : ℕ

    -- Computed programs
    code-f : Program
    code-g : Program
    prog : Program

    -- Jump targets
    right-branch : ℕ
    end-label : ℕ

    -- Individual instructions
    load-tag-instr : Instr      -- ldr x9, [x0]
    cmp-instr : Instr           -- cmp x9, #0
    bne-instr : Instr           -- b.ne right-branch
    load-val-left : Instr       -- ldr x0, [x0, #8]
    branch-end : Instr          -- b end
    right-label-instr : Instr   -- label right-branch
    load-val-right : Instr      -- ldr x0, [x0, #8]
    end-label-instr : Instr     -- label end

    -- Derived prefixes/suffixes for inl branch (executing f)
    prefix-f : Program
    suffix-f : Program

    -- Derived prefixes/suffixes for inr branch (executing g)
    prefix-g : Program
    suffix-g : Program

    -- Length equalities
    len-prefix-f : length prefix-f ≡ length prefix +ℕ 4
    len-prefix-g : length prefix-g ≡ length prefix +ℕ (7 +ℕ len-f)

    -- Program equalities for rewriting
    prog-eq-f : prog ≡ prefix-f ++ code-f ++ suffix-f
    prog-eq-g : prog ≡ prefix-g ++ code-g ++ suffix-g

open CaseContext public

-- | Construct CaseContext from IR terms and prefix/suffix
mkCaseContext : ∀ {i} {A B C : Type} (f : IR i A C) (g : IR i B C)
                (prefix suffix : Program) → CaseContext f g prefix suffix
mkCaseContext {A} {B} {C} f g prefix suffix = record
  { len-f = the-len-f
  ; len-g = the-len-g
  ; code-f = the-code-f
  ; code-g = the-code-g
  ; prog = the-prog
  ; right-branch = the-right-branch
  ; end-label = the-end-label
  ; load-tag-instr = the-load-tag-instr
  ; cmp-instr = the-cmp-instr
  ; bne-instr = the-bne-instr
  ; load-val-left = the-load-val-left
  ; branch-end = the-branch-end
  ; right-label-instr = the-right-label-instr
  ; load-val-right = the-load-val-right
  ; end-label-instr = the-end-label-instr
  ; prefix-f = the-prefix-f
  ; suffix-f = the-suffix-f
  ; prefix-g = the-prefix-g
  ; suffix-g = the-suffix-g
  ; len-prefix-f = the-len-prefix-f
  ; len-prefix-g = the-len-prefix-g
  ; prog-eq-f = the-prog-eq-f
  ; prog-eq-g = the-prog-eq-g
  }
  where
    the-len-f = compile-length f
    the-len-g = compile-length g
    the-code-f = compile-aarch64 f
    the-code-g = compile-aarch64 g
    the-prog = prefix ++ compile-aarch64 [ f , g ] ++ suffix

    -- Jump targets
    the-right-branch = 5 +ℕ the-len-f
    the-end-label = (7 +ℕ the-len-f) +ℕ the-len-g

    -- Instructions
    the-load-tag-instr = ldr x9 (base x0)
    the-cmp-instr = cmp x9 (imm 0)
    the-bne-instr = b-ne the-right-branch
    the-load-val-left = ldr x0 (base+imm x0 8)
    the-branch-end = b the-end-label
    the-right-label-instr = label the-right-branch
    the-load-val-right = ldr x0 (base+imm x0 8)
    the-end-label-instr = label the-end-label

    -- Prefix for f (left branch): first 4 instructions
    the-prefix-f : Program
    the-prefix-f = prefix ++ the-load-tag-instr ∷ the-cmp-instr ∷ the-bne-instr ∷ the-load-val-left ∷ []

    -- Suffix for f (left branch): branch + right code + labels
    the-suffix-f : Program
    the-suffix-f = the-branch-end ∷ the-right-label-instr ∷ the-load-val-right ∷ the-code-g ++ the-end-label-instr ∷ suffix

    -- Prefix for g (right branch): skip through left code
    the-prefix-g : Program
    the-prefix-g = prefix ++ the-load-tag-instr ∷ the-cmp-instr ∷ the-bne-instr ∷
               the-load-val-left ∷ the-code-f ++
               the-branch-end ∷ the-right-label-instr ∷ the-load-val-right ∷ []

    -- Suffix for g (right branch): just end label
    the-suffix-g : Program
    the-suffix-g = the-end-label-instr ∷ suffix

    -- Length proof for prefix-f
    the-len-prefix-f : length the-prefix-f ≡ length prefix +ℕ 4
    the-len-prefix-f = length-++ prefix _

    -- Length proof for prefix-g
    the-len-prefix-g : length the-prefix-g ≡ length prefix +ℕ (7 +ℕ the-len-f)
    the-len-prefix-g = begin
      length the-prefix-g
        ≡⟨ length-++ prefix _ ⟩
      length prefix +ℕ length (the-load-tag-instr ∷ the-cmp-instr ∷ the-bne-instr ∷
                              the-load-val-left ∷ the-code-f ++
                              the-branch-end ∷ the-right-label-instr ∷ the-load-val-right ∷ [])
        ≡⟨ cong (length prefix +ℕ_) inner-eq ⟩
      length prefix +ℕ (7 +ℕ the-len-f)
      ∎
      where
        inner-eq : length (the-load-tag-instr ∷ the-cmp-instr ∷ the-bne-instr ∷
                          the-load-val-left ∷ the-code-f ++
                          the-branch-end ∷ the-right-label-instr ∷ the-load-val-right ∷ [])
                 ≡ 7 +ℕ the-len-f
        inner-eq = begin
          4 +ℕ length (the-code-f ++ the-branch-end ∷ the-right-label-instr ∷ the-load-val-right ∷ [])
            ≡⟨ cong (4 +ℕ_) (length-++ the-code-f _) ⟩
          4 +ℕ (length the-code-f +ℕ 3)
            ≡⟨ cong (λ n → 4 +ℕ (n +ℕ 3)) (compile-length-correct f) ⟩
          4 +ℕ (the-len-f +ℕ 3)
            ≡⟨ sym (+-assoc 4 the-len-f 3) ⟩
          (4 +ℕ the-len-f) +ℕ 3
            ≡⟨ cong (_+ℕ 3) (+-comm 4 the-len-f) ⟩
          (the-len-f +ℕ 4) +ℕ 3
            ≡⟨ +-assoc the-len-f 4 3 ⟩
          the-len-f +ℕ 7
            ≡⟨ +-comm the-len-f 7 ⟩
          7 +ℕ the-len-f
          ∎

    -- Intermediate structures for program equality proofs
    -- Following Pair.agda pattern: define structures that match code generator output

    -- Post-f code: i4 ∷ i5 ∷ i6 ∷ code-g ++ i7 ∷ []
    the-post-f : Program
    the-post-f = the-branch-end ∷ the-right-label-instr ∷ the-load-val-right ∷ the-code-g ++ the-end-label-instr ∷ []

    -- Inner case: i0 ∷ i1 ∷ i2 ∷ i3 ∷ code-f ++ post-f
    the-inner-case : Program
    the-inner-case = the-load-tag-instr ∷ the-cmp-instr ∷ the-bne-instr ∷ the-load-val-left ∷ the-code-f ++ the-post-f

    -- rest-for-f: inner-case ++ suffix
    the-rest-for-f : Program
    the-rest-for-f = the-inner-case ++ suffix

    -- Setup part (first 4 instructions)
    the-setup-left : Program
    the-setup-left = the-load-tag-instr ∷ the-cmp-instr ∷ the-bne-instr ∷ the-load-val-left ∷ []

    -- Helper: prog = prefix ++ inner-case ++ suffix
    prog-eq-inner : the-prog ≡ prefix ++ the-inner-case ++ suffix
    prog-eq-inner = cong (prefix ++_) refl

    -- Helper: suffix-f relates to post-f
    -- Note: suffix-f = i4 ∷ i5 ∷ i6 ∷ code-g ++ (i7 ∷ suffix)
    --       post-f   = i4 ∷ i5 ∷ i6 ∷ code-g ++ (i7 ∷ [])
    --       post-f ++ suffix = i4 ∷ i5 ∷ i6 ∷ (code-g ++ i7 ∷ []) ++ suffix
    --                        = i4 ∷ i5 ∷ i6 ∷ code-g ++ (i7 ∷ []) ++ suffix   via ++-assoc
    --                        = i4 ∷ i5 ∷ i6 ∷ code-g ++ (i7 ∷ suffix)         by (i7 ∷ []) ++ suffix = i7 ∷ suffix
    suffix-f-eq-post : the-suffix-f ≡ the-post-f ++ suffix
    suffix-f-eq-post = sym (cong (the-branch-end ∷_) (cong (the-right-label-instr ∷_)
                       (cong (the-load-val-right ∷_) inner-eq)))
      where
        -- (code-g ++ i7 ∷ []) ++ suffix ≡ code-g ++ (i7 ∷ suffix)
        inner-eq : (the-code-g ++ the-end-label-instr ∷ []) ++ suffix ≡ the-code-g ++ the-end-label-instr ∷ suffix
        inner-eq = ++-assoc the-code-g (the-end-label-instr ∷ []) suffix

    -- Helper: inner-case = setup-left ++ code-f ++ post-f
    inner-case-split : the-inner-case ≡ the-setup-left ++ the-code-f ++ the-post-f
    inner-case-split = sym (++-assoc the-setup-left the-code-f the-post-f)

    -- Helper: prefix ++ setup-left ++ xs = prefix-f ++ xs
    prefix-setup-eq : ∀ xs → prefix ++ the-setup-left ++ xs ≡ the-prefix-f ++ xs
    prefix-setup-eq xs = sym (++-assoc prefix the-setup-left xs)

    -- Program equality for f branch
    the-prog-eq-f : the-prog ≡ the-prefix-f ++ the-code-f ++ the-suffix-f
    the-prog-eq-f = begin
      the-prog
        ≡⟨ prog-eq-inner ⟩
      prefix ++ the-inner-case ++ suffix
        ≡⟨ cong (prefix ++_) (cong (_++ suffix) inner-case-split) ⟩
      prefix ++ (the-setup-left ++ the-code-f ++ the-post-f) ++ suffix
        ≡⟨ cong (prefix ++_) (++-assoc (the-setup-left ++ the-code-f) the-post-f suffix) ⟩
      prefix ++ ((the-setup-left ++ the-code-f) ++ (the-post-f ++ suffix))
        ≡⟨ cong (prefix ++_) (cong ((the-setup-left ++ the-code-f) ++_) (sym suffix-f-eq-post)) ⟩
      prefix ++ ((the-setup-left ++ the-code-f) ++ the-suffix-f)
        ≡⟨ cong (prefix ++_) (sym (++-assoc the-setup-left the-code-f the-suffix-f)) ⟩
      prefix ++ (the-setup-left ++ (the-code-f ++ the-suffix-f))
        ≡⟨ sym (++-assoc prefix the-setup-left (the-code-f ++ the-suffix-f)) ⟩
      (prefix ++ the-setup-left) ++ (the-code-f ++ the-suffix-f)
        ≡⟨ refl ⟩
      the-prefix-f ++ (the-code-f ++ the-suffix-f)
      ∎

    -- For g branch: need prefix-g = prefix-f ++ code-f ++ [i4, i5, i6]
    -- suffix-g = i7 ∷ suffix

    -- Helper: post-f = i4 ∷ i5 ∷ i6 ∷ code-g ++ i7 ∷ []
    -- Middle between f and g: [i4, i5, i6]
    the-mid-g : Program
    the-mid-g = the-branch-end ∷ the-right-label-instr ∷ the-load-val-right ∷ []

    -- Helper: post-f ++ suffix = mid-g ++ code-g ++ suffix-g
    -- Note: post-f ends with i7 ∷ [], while suffix-g = i7 ∷ suffix
    -- So we need to include suffix on LHS to get equality
    post-f-suffix-eq : the-post-f ++ suffix ≡ the-mid-g ++ the-code-g ++ the-suffix-g
    post-f-suffix-eq = begin
      the-post-f ++ suffix
        ≡⟨ refl ⟩
      (the-branch-end ∷ the-right-label-instr ∷ the-load-val-right ∷ the-code-g ++ the-end-label-instr ∷ []) ++ suffix
        ≡⟨ cong (the-branch-end ∷_) (cong (the-right-label-instr ∷_) (cong (the-load-val-right ∷_)
           (++-assoc the-code-g (the-end-label-instr ∷ []) suffix))) ⟩
      the-branch-end ∷ the-right-label-instr ∷ the-load-val-right ∷ the-code-g ++ (the-end-label-instr ∷ suffix)
        ≡⟨ sym (++-assoc the-mid-g the-code-g (the-end-label-instr ∷ suffix)) ⟩
      (the-mid-g ++ the-code-g) ++ (the-end-label-instr ∷ suffix)
        ≡⟨ ++-assoc the-mid-g the-code-g (the-end-label-instr ∷ suffix) ⟩
      the-mid-g ++ the-code-g ++ the-suffix-g
      ∎

    -- Helper: prefix-g = prefix-f ++ code-f ++ mid-g
    -- Key insight: setup-left ++ code-f ++ mid-g = i0 ∷ ... ∷ i3 ∷ code-f ++ i4 ∷ ... ∷ []
    -- by computation (++ on concrete list reduces)
    prefix-g-expand : the-prefix-g ≡ the-prefix-f ++ the-code-f ++ the-mid-g
    prefix-g-expand = begin
      the-prefix-g
        ≡⟨ refl ⟩
      -- the-prefix-g expands to:
      -- prefix ++ i0 ∷ i1 ∷ i2 ∷ i3 ∷ code-f ++ i4 ∷ i5 ∷ i6 ∷ []
      -- which equals prefix ++ (setup-left ++ code-f ++ mid-g) by computation
      prefix ++ the-setup-left ++ the-code-f ++ the-mid-g
        ≡⟨ sym (++-assoc prefix the-setup-left (the-code-f ++ the-mid-g)) ⟩
      (prefix ++ the-setup-left) ++ (the-code-f ++ the-mid-g)
        ≡⟨ refl ⟩
      the-prefix-f ++ (the-code-f ++ the-mid-g)
        ≡⟨ sym (++-assoc the-prefix-f the-code-f the-mid-g) ⟩
      (the-prefix-f ++ the-code-f) ++ the-mid-g
        ≡⟨ ++-assoc the-prefix-f the-code-f the-mid-g ⟩
      the-prefix-f ++ the-code-f ++ the-mid-g
      ∎

    -- Program equality for g branch
    -- Goal: the-prog ≡ the-prefix-g ++ the-code-g ++ the-suffix-g
    -- where the-prefix-g = the-prefix-f ++ the-code-f ++ the-mid-g
    the-prog-eq-g : the-prog ≡ the-prefix-g ++ the-code-g ++ the-suffix-g
    the-prog-eq-g = begin
      the-prog
        ≡⟨ the-prog-eq-f ⟩
      the-prefix-f ++ (the-code-f ++ the-suffix-f)
        ≡⟨ cong (the-prefix-f ++_) (cong (the-code-f ++_) suffix-f-eq-post) ⟩
      the-prefix-f ++ (the-code-f ++ (the-post-f ++ suffix))
        ≡⟨ cong (the-prefix-f ++_) (cong (the-code-f ++_) post-f-suffix-eq) ⟩
      the-prefix-f ++ (the-code-f ++ (the-mid-g ++ the-code-g ++ the-suffix-g))
        -- Now we need to reassociate to get (prefix-f ++ code-f ++ mid-g) ++ code-g ++ suffix-g
        -- Step 1: Push code-f inside: code-f ++ (mid-g ++ (code-g ++ suffix-g))
        ≡⟨ cong (the-prefix-f ++_) (cong (the-code-f ++_) (sym (++-assoc the-mid-g the-code-g the-suffix-g))) ⟩
      the-prefix-f ++ (the-code-f ++ ((the-mid-g ++ the-code-g) ++ the-suffix-g))
        ≡⟨ cong (the-prefix-f ++_) (cong (the-code-f ++_) (++-assoc the-mid-g the-code-g the-suffix-g)) ⟩
      the-prefix-f ++ (the-code-f ++ (the-mid-g ++ (the-code-g ++ the-suffix-g)))
        -- Step 2: Reassociate code-f ++ mid-g
        ≡⟨ cong (the-prefix-f ++_) (sym (++-assoc the-code-f the-mid-g (the-code-g ++ the-suffix-g))) ⟩
      the-prefix-f ++ ((the-code-f ++ the-mid-g) ++ (the-code-g ++ the-suffix-g))
        -- Step 3: Push prefix-f in
        ≡⟨ sym (++-assoc the-prefix-f (the-code-f ++ the-mid-g) (the-code-g ++ the-suffix-g)) ⟩
      (the-prefix-f ++ (the-code-f ++ the-mid-g)) ++ (the-code-g ++ the-suffix-g)
        -- Step 4: Reassociate prefix-f ++ code-f ++ mid-g
        ≡⟨ cong (_++ (the-code-g ++ the-suffix-g)) (sym (++-assoc the-prefix-f the-code-f the-mid-g)) ⟩
      ((the-prefix-f ++ the-code-f) ++ the-mid-g) ++ (the-code-g ++ the-suffix-g)
        ≡⟨ cong (_++ (the-code-g ++ the-suffix-g)) (++-assoc the-prefix-f the-code-f the-mid-g) ⟩
      (the-prefix-f ++ (the-code-f ++ the-mid-g)) ++ (the-code-g ++ the-suffix-g)
        -- Now apply prefix-g-expand
        ≡⟨ cong (_++ (the-code-g ++ the-suffix-g)) (sym prefix-g-expand) ⟩
      the-prefix-g ++ (the-code-g ++ the-suffix-g)
        ≡⟨ sym (++-assoc the-prefix-g the-code-g the-suffix-g) ⟩
      (the-prefix-g ++ the-code-g) ++ the-suffix-g
        ≡⟨ ++-assoc the-prefix-g the-code-g the-suffix-g ⟩
      the-prefix-g ++ the-code-g ++ the-suffix-g
      ∎

------------------------------------------------------------------------
-- Case Setup Results: intermediate state after setup instructions
------------------------------------------------------------------------

-- | Result after setup for inl branch (4 instructions)
-- ldr x9, [x0] ; cmp x9, #0 ; b.ne right ; ldr x0, [x0, #8]
record CaseInlSetupResult {i} {A B C : Type} (f : IR i A C) (g : IR i B C)
                          (prefix suffix : Program)
                          (ctx : CaseContext f g prefix suffix)
                          (s s-after : State) (a : ⟦ A ⟧) : Set where
  field
    -- Execution reached s-after
    setup-exec : exec 4 (prog ctx) s ≡ just s-after

    -- Not halted
    setup-halted : halted s-after ≡ false

    -- PC at start of f code
    setup-pc : pc s-after ≡ length (prefix-f ctx)

    -- x0 contains value from sum (unpacked)
    setup-x0 : readReg (regs s-after) x0 ≡ encode a

open CaseInlSetupResult public

-- | Result after setup for inr branch (7 + |f| instructions to reach g)
-- Need to skip through the inl branch code
record CaseInrSetupResult {i} {A B C : Type} (f : IR i A C) (g : IR i B C)
                          (prefix suffix : Program)
                          (ctx : CaseContext f g prefix suffix)
                          (s s-after : State) (b : ⟦ B ⟧) : Set where
  field
    -- Execution reached s-after (3 setup + skip f code + 3 more setup = 7 + |f|)
    setup-exec : exec (7 +ℕ len-f ctx) (prog ctx) s ≡ just s-after

    -- Not halted
    setup-halted : halted s-after ≡ false

    -- PC at start of g code
    setup-pc : pc s-after ≡ length (prefix-g ctx)

    -- x0 contains value from sum (unpacked)
    setup-x0 : readReg (regs s-after) x0 ≡ encode b

open CaseInrSetupResult public

------------------------------------------------------------------------
-- Case Final Results: state after executing the branch
------------------------------------------------------------------------

-- | Result after executing f for inl case
record CaseInlFinalResult {i} {A B C : Type} (f : IR i A C) (g : IR i B C)
                          (prefix suffix : Program)
                          (ctx : CaseContext f g prefix suffix)
                          (s-setup s-final : State) (a : ⟦ A ⟧) : Set where
  field
    -- Execution from setup to final (|f| + 1 for branch)
    final-exec : exec (len-f ctx +ℕ 1) (prog ctx) s-setup ≡ just s-final

    -- Not halted
    final-halted : halted s-final ≡ false

    -- PC at end of case code
    final-pc : pc s-final ≡ length prefix +ℕ compile-length [ f , g ]

    -- x0 is result
    final-x0 : readReg (regs s-final) x0 ≡ encode (eval f a)

open CaseInlFinalResult public

-- | Result after executing g for inr case
record CaseInrFinalResult {i} {A B C : Type} (f : IR i A C) (g : IR i B C)
                          (prefix suffix : Program)
                          (ctx : CaseContext f g prefix suffix)
                          (s-setup s-final : State) (b : ⟦ B ⟧) : Set where
  field
    -- Execution from setup to final (|g| + 1 for label)
    final-exec : exec (len-g ctx +ℕ 1) (prog ctx) s-setup ≡ just s-final

    -- Not halted
    final-halted : halted s-final ≡ false

    -- PC at end of case code
    final-pc : pc s-final ≡ length prefix +ℕ compile-length [ f , g ]

    -- x0 is result
    final-x0 : readReg (regs s-final) x0 ≡ encode (eval g b)

open CaseInrFinalResult public

------------------------------------------------------------------------
-- Arithmetic Lemmas
------------------------------------------------------------------------

-- | 4 + |f| + 3 = 7 + |f| (setup steps for inr)
arith-case-inr-setup : ∀ len-f → 4 +ℕ len-f +ℕ 3 ≡ 7 +ℕ len-f
arith-case-inr-setup len-f = begin
  4 +ℕ len-f +ℕ 3
    ≡⟨ +-assoc 4 len-f 3 ⟩
  4 +ℕ (len-f +ℕ 3)
    ≡⟨ cong (4 +ℕ_) (+-comm len-f 3) ⟩
  4 +ℕ (3 +ℕ len-f)
    ≡⟨ sym (+-assoc 4 3 len-f) ⟩
  7 +ℕ len-f
  ∎

-- | (p + 4) + (len-f + 1) = p + 5 + len-f
arith-case-inl-pc : ∀ p len-f → (p +ℕ 4) +ℕ (len-f +ℕ 1) ≡ p +ℕ 5 +ℕ len-f
arith-case-inl-pc p len-f = begin
  (p +ℕ 4) +ℕ (len-f +ℕ 1)
    ≡⟨ +-assoc p 4 (len-f +ℕ 1) ⟩
  p +ℕ (4 +ℕ (len-f +ℕ 1))
    ≡⟨ cong (p +ℕ_) (sym (+-assoc 4 len-f 1)) ⟩
  p +ℕ ((4 +ℕ len-f) +ℕ 1)
    ≡⟨ cong (p +ℕ_) (cong (_+ℕ 1) (+-comm 4 len-f)) ⟩
  p +ℕ ((len-f +ℕ 4) +ℕ 1)
    ≡⟨ cong (p +ℕ_) (+-assoc len-f 4 1) ⟩
  p +ℕ (len-f +ℕ 5)
    ≡⟨ sym (+-assoc p len-f 5) ⟩
  (p +ℕ len-f) +ℕ 5
    ≡⟨ cong (_+ℕ 5) (+-comm p len-f) ⟩
  (len-f +ℕ p) +ℕ 5
    ≡⟨ +-assoc len-f p 5 ⟩
  len-f +ℕ (p +ℕ 5)
    ≡⟨ +-comm len-f (p +ℕ 5) ⟩
  (p +ℕ 5) +ℕ len-f
    ≡⟨ cong (_+ℕ len-f) (+-comm p 5) ⟩
  (5 +ℕ p) +ℕ len-f
    ≡⟨ +-assoc 5 p len-f ⟩
  5 +ℕ (p +ℕ len-f)
    ≡⟨ cong (5 +ℕ_) (+-comm p len-f) ⟩
  5 +ℕ (len-f +ℕ p)
    ≡⟨ sym (+-assoc 5 len-f p) ⟩
  (5 +ℕ len-f) +ℕ p
    ≡⟨ +-comm (5 +ℕ len-f) p ⟩
  p +ℕ (5 +ℕ len-f)
    ≡⟨ sym (+-assoc p 5 len-f) ⟩
  p +ℕ 5 +ℕ len-f
  ∎
