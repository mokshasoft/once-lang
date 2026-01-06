{-# OPTIONS --sized-types #-}
------------------------------------------------------------------------
-- Once.Backend.AArch64.Correct.IR.Case
--
-- Helper records and functions for case proofs.
-- Extracts non-recursive parts to reduce mutual block compilation time.
-- The recursive calls stay in MutualIR.agda.
------------------------------------------------------------------------

module Once.Backend.AArch64.Correct.IR.Case where

open import Size
open import Once.Type
open import Once.IR
open import Once.Semantics hiding (code-ptr; env-addr; semantics)

open import Once.Backend.AArch64.Syntax
open import Once.Backend.AArch64.Semantics
open State
open import Once.Backend.AArch64.CodeGen

open import Once.Backend.AArch64.Correct.Foundation using (encode)
open import Once.Backend.AArch64.Correct.CompileLength using (compile-length-correct)
open import Once.Backend.AArch64.Correct.Star using (Star; star-trans)
open import Once.Backend.AArch64.Correct.StarBase using (IRStarResultS)
open import Once.Backend.AArch64.Correct.StackInvariant using (StackInvariant; X29Invariant)

open import Data.Bool using (false)
open import Data.Nat using (ℕ; zero; suc; _∸_; _>_; _≤_) renaming (_+_ to _+ℕ_)
open import Data.Nat.Properties using (+-assoc; +-comm; +-identityʳ; ≤-refl; ≤-trans; ≤-reflexive)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.List.Properties using (++-assoc; ++-identityʳ) renaming (length-++ to List-length-++)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; ∃-syntax)
open import Data.Sum using (inj₁; inj₂)
open import Data.Maybe using (just; nothing)
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

    -- PC-relative branch offsets
    right-offset : ℕ            -- b-ne jumps forward by this
    end-offset : ℕ              -- b jumps forward by this

    -- Label positions (for label instructions)
    right-label : ℕ
    end-label : ℕ

    -- Individual instructions
    load-tag-instr : Instr      -- ldr x9, [x0]
    cmp-instr : Instr           -- cmp x9, #0
    bne-instr : Instr           -- b.ne right-offset (PC-relative)
    load-val-left : Instr       -- ldr x0, [x0, #8]
    branch-end : Instr          -- b end-offset (PC-relative)
    right-label-instr : Instr   -- label right-label
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
mkCaseContext : ∀ {A B C : Type} (f : IR A C) (g : IR B C)
                (prefix suffix : Program) → CaseContext f g prefix suffix
mkCaseContext {A} {B} {C} f g prefix suffix = record
  { len-f = the-len-f
  ; len-g = the-len-g
  ; code-f = the-code-f
  ; code-g = the-code-g
  ; prog = the-prog
  ; right-offset = the-right-offset
  ; end-offset = the-end-offset
  ; right-label = the-right-label
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

    -- PC-relative offsets for branches
    the-right-offset = 3 +ℕ the-len-f    -- b-ne jumps forward by this
    the-end-offset = 3 +ℕ the-len-g      -- b jumps forward by this

    -- Label positions (for label pseudo-instructions)
    the-right-label = 5 +ℕ the-len-f
    the-end-label = (7 +ℕ the-len-f) +ℕ the-len-g

    -- Instructions (now using PC-relative offsets)
    the-load-tag-instr = ldr x9 (base x0)
    the-cmp-instr = cmp x9 (imm 0)
    the-bne-instr = b-ne the-right-offset      -- PC-relative
    the-load-val-left = ldr x0 (base+imm x0 8)
    the-branch-end = b the-end-offset          -- PC-relative
    the-right-label-instr = label the-right-label
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
-- Case Result Assembly: combine setup, branch, and cleanup results
--
-- AArch64 case has two execution paths:
--   inl: setup (4 instr) → f → jump (1 instr) → end label (1 instr)
--   inr: setup (7+|f| instr to reach g) → g → end label (1 instr)
------------------------------------------------------------------------

-- | Assemble the final case result for inl branch
--
-- Given:
--   res-f : IRStarResultS f prog s-setup sf addr-out (length prefix-f)
--   star-jump : Star prog sf s-final  (b end + label execution)
-- Produce:
--   Full case result with proper PC and invariants
--
-- The inl path executes:
--   1. Setup (4 instructions): load tag, cmp, b.ne (not taken), load left value
--   2. Execute f
--   3. Jump to end (2 instructions): b end-offset, label end
assemble-case-inl-result : ∀ {A B C} (f : IR A C) (g : IR B C)
                           (prefix suffix : Program) (addr-val : Word)
                           (s s-setup sf s-final : State) →
  let ctx = mkCaseContext f g prefix suffix
      theProg = CaseContext.prog ctx
      thePrefixF = CaseContext.prefix-f ctx
      theLen-f = CaseContext.len-f ctx
  in
  -- Setup result (Star from s to s-setup for 4 instructions)
  (star-setup : Star theProg s s-setup) →
  (h-setup : halted s-setup ≡ false) →
  (pc-setup : pc s-setup ≡ length thePrefixF) →
  (x0-setup : readReg (regs s-setup) x0 ≡ addr-val) →
  (x20-setup : readReg (regs s-setup) x20 ≡ readReg (regs s) x20) →
  (x21-setup : readReg (regs s-setup) x21 ≡ readReg (regs s) x21) →
  (x29-setup : readReg (regs s-setup) x29 ≡ readReg (regs s) x29) →
  (x30-setup : readReg (regs s-setup) x30 ≡ readReg (regs s) x30) →
  (sp-setup : readSP (regs s-setup) ≤ readSP (regs s)) →
  (mem-x21-setup : readMem (memory s-setup) (readReg (regs s) x21) ≡ readMem (memory s) (readReg (regs s) x21)) →
  (mem-x29-setup : readMem (memory s-setup) (readReg (regs s) x29) ≡ readMem (memory s) (readReg (regs s) x29)) →
  (mem-x29+8-setup : readMem (memory s-setup) (readReg (regs s) x29 +ℕ 8) ≡ readMem (memory s) (readReg (regs s) x29 +ℕ 8)) →
  -- f execution result
  (res-f : IRStarResultS f theProg s-setup sf addr-val (length thePrefixF)) →
  -- Jump and label result (Star from sf to s-final for 2 instructions)
  (star-jump : Star theProg sf s-final) →
  (h-jump : halted s-final ≡ false) →
  (pc-jump : pc s-final ≡ length prefix +ℕ compile-length [ f , g ]) →
  (x0-jump : readReg (regs s-final) x0 ≡ readReg (regs sf) x0) →
  (x20-jump : readReg (regs s-final) x20 ≡ readReg (regs sf) x20) →
  (x21-jump : readReg (regs s-final) x21 ≡ readReg (regs sf) x21) →
  (x29-jump : readReg (regs s-final) x29 ≡ readReg (regs sf) x29) →
  (x30-jump : readReg (regs s-final) x30 ≡ readReg (regs sf) x30) →
  (sp-jump : readSP (regs s-final) ≤ readSP (regs sf)) →
  (mem-x21-jump : ∀ addr → readMem (memory s-final) addr ≡ readMem (memory sf) addr) →
  (mem-x29-jump : ∀ addr → readMem (memory s-final) addr ≡ readMem (memory sf) addr) →
  (stack-inv-jump : StackInvariant s-final) →
  (x29-inv-jump : X29Invariant s-final) →
  (sp>16-jump : readSP (regs s-final) > 16) →
  -- Result: Full case execution
  ∃[ addr-out ] (IRStarResultS [ f , g ] theProg s s-final addr-out (length prefix) ×
                 readReg (regs s-final) x0 ≡ addr-out)
assemble-case-inl-result {A} {B} {C} f g prefix suffix addr-val s s-setup sf s-final
  star-setup h-setup pc-setup x0-setup x20-setup x21-setup x29-setup x30-setup sp-setup mem-x21-setup mem-x29-setup mem-x29+8-setup
  res-f star-jump h-jump pc-jump x0-jump x20-jump x21-jump x29-jump x30-jump sp-jump mem-x21-jump mem-x29-jump stack-inv-jump x29-inv-jump sp>16-jump =
  addr-out , result , refl
  where
    ctx = mkCaseContext f g prefix suffix
    theProg = CaseContext.prog ctx
    theLen-f = CaseContext.len-f ctx
    theLen-g = CaseContext.len-g ctx
    thePrefixF = CaseContext.prefix-f ctx
    open IRStarResultS

    -- Extract results from f
    star-f : Star theProg s-setup sf
    star-f = ir-star res-f

    addr-out : Word
    addr-out = readReg (regs s-final) x0

    -- Compose stars: setup → f → jump
    star-setup-f : Star theProg s sf
    star-setup-f = star-trans star-setup star-f

    star-all : Star theProg s s-final
    star-all = star-trans star-setup-f star-jump

    -- Chain register preservation: x20
    x20-final : readReg (regs s-final) x20 ≡ readReg (regs s) x20
    x20-final = trans x20-jump (trans (ir-x20 res-f) x20-setup)

    -- Chain register preservation: x21
    x21-final : readReg (regs s-final) x21 ≡ readReg (regs s) x21
    x21-final = trans x21-jump (trans (ir-x21 res-f) x21-setup)

    -- Chain register preservation: x29
    x29-final : readReg (regs s-final) x29 ≡ readReg (regs s) x29
    x29-final = trans x29-jump (trans (ir-x29 res-f) x29-setup)

    -- Chain register preservation: x30
    x30-final : readReg (regs s-final) x30 ≡ readReg (regs s) x30
    x30-final = trans x30-jump (trans (ir-x30 res-f) x30-setup)

    -- Chain sp preservation
    sp-final : readSP (regs s-final) ≤ readSP (regs s)
    sp-final = ≤-trans sp-jump (≤-trans (ir-sp res-f) sp-setup)

    -- Chain memory preservation at x21
    mem-x21-final : readMem (memory s-final) (readReg (regs s) x21) ≡ readMem (memory s) (readReg (regs s) x21)
    mem-x21-final = begin
      readMem (memory s-final) (readReg (regs s) x21)
        ≡⟨ cong (readMem (memory s-final)) (sym x21-final) ⟩
      readMem (memory s-final) (readReg (regs s-final) x21)
        ≡⟨ cong (readMem (memory s-final)) x21-jump ⟩
      readMem (memory s-final) (readReg (regs sf) x21)
        ≡⟨ mem-x21-jump (readReg (regs sf) x21) ⟩
      readMem (memory sf) (readReg (regs sf) x21)
        ≡⟨ cong (readMem (memory sf)) (ir-x21 res-f) ⟩
      readMem (memory sf) (readReg (regs s-setup) x21)
        ≡⟨ ir-mem-x21 res-f ⟩
      readMem (memory s-setup) (readReg (regs s-setup) x21)
        ≡⟨ cong (readMem (memory s-setup)) x21-setup ⟩
      readMem (memory s-setup) (readReg (regs s) x21)
        ≡⟨ mem-x21-setup ⟩
      readMem (memory s) (readReg (regs s) x21)
        ∎

    -- Chain memory preservation at x29
    mem-x29-final : readMem (memory s-final) (readReg (regs s) x29) ≡ readMem (memory s) (readReg (regs s) x29)
    mem-x29-final = begin
      readMem (memory s-final) (readReg (regs s) x29)
        ≡⟨ cong (readMem (memory s-final)) (sym x29-final) ⟩
      readMem (memory s-final) (readReg (regs s-final) x29)
        ≡⟨ cong (readMem (memory s-final)) x29-jump ⟩
      readMem (memory s-final) (readReg (regs sf) x29)
        ≡⟨ mem-x29-jump (readReg (regs sf) x29) ⟩
      readMem (memory sf) (readReg (regs sf) x29)
        ≡⟨ cong (readMem (memory sf)) (ir-x29 res-f) ⟩
      readMem (memory sf) (readReg (regs s-setup) x29)
        ≡⟨ ir-mem-x29 res-f ⟩
      readMem (memory s-setup) (readReg (regs s-setup) x29)
        ≡⟨ cong (readMem (memory s-setup)) x29-setup ⟩
      readMem (memory s-setup) (readReg (regs s) x29)
        ≡⟨ mem-x29-setup ⟩
      readMem (memory s) (readReg (regs s) x29)
        ∎

    -- Chain memory preservation at x29+8
    mem-x29+8-final : readMem (memory s-final) (readReg (regs s) x29 +ℕ 8) ≡ readMem (memory s) (readReg (regs s) x29 +ℕ 8)
    mem-x29+8-final = begin
      readMem (memory s-final) (readReg (regs s) x29 +ℕ 8)
        ≡⟨ cong (λ x → readMem (memory s-final) (x +ℕ 8)) (sym x29-final) ⟩
      readMem (memory s-final) (readReg (regs s-final) x29 +ℕ 8)
        ≡⟨ cong (λ x → readMem (memory s-final) (x +ℕ 8)) x29-jump ⟩
      readMem (memory s-final) (readReg (regs sf) x29 +ℕ 8)
        ≡⟨ mem-x29-jump (readReg (regs sf) x29 +ℕ 8) ⟩
      readMem (memory sf) (readReg (regs sf) x29 +ℕ 8)
        ≡⟨ cong (λ x → readMem (memory sf) (x +ℕ 8)) (ir-x29 res-f) ⟩
      readMem (memory sf) (readReg (regs s-setup) x29 +ℕ 8)
        ≡⟨ ir-mem-x29+8 res-f ⟩
      readMem (memory s-setup) (readReg (regs s-setup) x29 +ℕ 8)
        ≡⟨ cong (λ x → readMem (memory s-setup) (x +ℕ 8)) x29-setup ⟩
      readMem (memory s-setup) (readReg (regs s) x29 +ℕ 8)
        ≡⟨ mem-x29+8-setup ⟩
      readMem (memory s) (readReg (regs s) x29 +ℕ 8)
        ∎

    -- x0 contains addr-out
    x0-final : readReg (regs s-final) x0 ≡ addr-out
    x0-final = refl

    result : IRStarResultS [ f , g ] theProg s s-final addr-out (length prefix)
    result = record
      { ir-star = star-all
      ; ir-halted = h-jump
      ; ir-pc = pc-jump
      ; ir-x0-s = x0-final
      ; ir-x20 = x20-final
      ; ir-x21 = x21-final
      ; ir-x29 = x29-final
      ; ir-x30 = x30-final
      ; ir-sp = sp-final
      ; ir-mem-x21 = mem-x21-final
      ; ir-mem-x29 = mem-x29-final
      ; ir-mem-x29+8 = mem-x29+8-final
      ; ir-stack-inv = stack-inv-jump
      ; ir-x29-inv = x29-inv-jump
      ; ir-sp-bound = sp>16-jump
      ; ir-closure-entry = nothing
      }

-- | Assemble the final case result for inr branch
--
-- Given:
--   res-g : IRStarResultS g prog s-setup sg addr-out (length prefix-g)
--   star-label : Star prog sg s-final  (label execution)
-- Produce:
--   Full case result with proper PC and invariants
--
-- The inr path executes:
--   1. Setup (7+|f| instructions): load tag, cmp, b.ne (taken), skip f code, reach right label, load right value
--   2. Execute g
--   3. End label (1 instruction)
assemble-case-inr-result : ∀ {A B C} (f : IR A C) (g : IR B C)
                           (prefix suffix : Program) (addr-val : Word)
                           (s s-setup sg s-final : State) →
  let ctx = mkCaseContext f g prefix suffix
      theProg = CaseContext.prog ctx
      thePrefixG = CaseContext.prefix-g ctx
      theLen-g = CaseContext.len-g ctx
  in
  -- Setup result (Star from s to s-setup)
  (star-setup : Star theProg s s-setup) →
  (h-setup : halted s-setup ≡ false) →
  (pc-setup : pc s-setup ≡ length thePrefixG) →
  (x0-setup : readReg (regs s-setup) x0 ≡ addr-val) →
  (x20-setup : readReg (regs s-setup) x20 ≡ readReg (regs s) x20) →
  (x21-setup : readReg (regs s-setup) x21 ≡ readReg (regs s) x21) →
  (x29-setup : readReg (regs s-setup) x29 ≡ readReg (regs s) x29) →
  (x30-setup : readReg (regs s-setup) x30 ≡ readReg (regs s) x30) →
  (sp-setup : readSP (regs s-setup) ≤ readSP (regs s)) →
  (mem-x21-setup : readMem (memory s-setup) (readReg (regs s) x21) ≡ readMem (memory s) (readReg (regs s) x21)) →
  (mem-x29-setup : readMem (memory s-setup) (readReg (regs s) x29) ≡ readMem (memory s) (readReg (regs s) x29)) →
  (mem-x29+8-setup : readMem (memory s-setup) (readReg (regs s) x29 +ℕ 8) ≡ readMem (memory s) (readReg (regs s) x29 +ℕ 8)) →
  -- g execution result
  (res-g : IRStarResultS g theProg s-setup sg addr-val (length thePrefixG)) →
  -- Label result (Star from sg to s-final for 1 instruction)
  (star-label : Star theProg sg s-final) →
  (h-label : halted s-final ≡ false) →
  (pc-label : pc s-final ≡ length prefix +ℕ compile-length [ f , g ]) →
  (x0-label : readReg (regs s-final) x0 ≡ readReg (regs sg) x0) →
  (x20-label : readReg (regs s-final) x20 ≡ readReg (regs sg) x20) →
  (x21-label : readReg (regs s-final) x21 ≡ readReg (regs sg) x21) →
  (x29-label : readReg (regs s-final) x29 ≡ readReg (regs sg) x29) →
  (x30-label : readReg (regs s-final) x30 ≡ readReg (regs sg) x30) →
  (sp-label : readSP (regs s-final) ≤ readSP (regs sg)) →
  (mem-x21-label : ∀ addr → readMem (memory s-final) addr ≡ readMem (memory sg) addr) →
  (mem-x29-label : ∀ addr → readMem (memory s-final) addr ≡ readMem (memory sg) addr) →
  (stack-inv-label : StackInvariant s-final) →
  (x29-inv-label : X29Invariant s-final) →
  (sp>16-label : readSP (regs s-final) > 16) →
  -- Result: Full case execution
  ∃[ addr-out ] (IRStarResultS [ f , g ] theProg s s-final addr-out (length prefix) ×
                 readReg (regs s-final) x0 ≡ addr-out)
assemble-case-inr-result {A} {B} {C} f g prefix suffix addr-val s s-setup sg s-final
  star-setup h-setup pc-setup x0-setup x20-setup x21-setup x29-setup x30-setup sp-setup mem-x21-setup mem-x29-setup mem-x29+8-setup
  res-g star-label h-label pc-label x0-label x20-label x21-label x29-label x30-label sp-label mem-x21-label mem-x29-label stack-inv-label x29-inv-label sp>16-label =
  addr-out , result , refl
  where
    ctx = mkCaseContext f g prefix suffix
    theProg = CaseContext.prog ctx
    theLen-f = CaseContext.len-f ctx
    theLen-g = CaseContext.len-g ctx
    thePrefixG = CaseContext.prefix-g ctx
    open IRStarResultS

    -- Extract results from g
    star-g : Star theProg s-setup sg
    star-g = ir-star res-g

    addr-out : Word
    addr-out = readReg (regs s-final) x0

    -- Compose stars: setup → g → label
    star-setup-g : Star theProg s sg
    star-setup-g = star-trans star-setup star-g

    star-all : Star theProg s s-final
    star-all = star-trans star-setup-g star-label

    -- Chain register preservation: x20
    x20-final : readReg (regs s-final) x20 ≡ readReg (regs s) x20
    x20-final = trans x20-label (trans (ir-x20 res-g) x20-setup)

    -- Chain register preservation: x21
    x21-final : readReg (regs s-final) x21 ≡ readReg (regs s) x21
    x21-final = trans x21-label (trans (ir-x21 res-g) x21-setup)

    -- Chain register preservation: x29
    x29-final : readReg (regs s-final) x29 ≡ readReg (regs s) x29
    x29-final = trans x29-label (trans (ir-x29 res-g) x29-setup)

    -- Chain register preservation: x30
    x30-final : readReg (regs s-final) x30 ≡ readReg (regs s) x30
    x30-final = trans x30-label (trans (ir-x30 res-g) x30-setup)

    -- Chain sp preservation
    sp-final : readSP (regs s-final) ≤ readSP (regs s)
    sp-final = ≤-trans sp-label (≤-trans (ir-sp res-g) sp-setup)

    -- Chain memory preservation at x21
    mem-x21-final : readMem (memory s-final) (readReg (regs s) x21) ≡ readMem (memory s) (readReg (regs s) x21)
    mem-x21-final = begin
      readMem (memory s-final) (readReg (regs s) x21)
        ≡⟨ cong (readMem (memory s-final)) (sym x21-final) ⟩
      readMem (memory s-final) (readReg (regs s-final) x21)
        ≡⟨ cong (readMem (memory s-final)) x21-label ⟩
      readMem (memory s-final) (readReg (regs sg) x21)
        ≡⟨ mem-x21-label (readReg (regs sg) x21) ⟩
      readMem (memory sg) (readReg (regs sg) x21)
        ≡⟨ cong (readMem (memory sg)) (ir-x21 res-g) ⟩
      readMem (memory sg) (readReg (regs s-setup) x21)
        ≡⟨ ir-mem-x21 res-g ⟩
      readMem (memory s-setup) (readReg (regs s-setup) x21)
        ≡⟨ cong (readMem (memory s-setup)) x21-setup ⟩
      readMem (memory s-setup) (readReg (regs s) x21)
        ≡⟨ mem-x21-setup ⟩
      readMem (memory s) (readReg (regs s) x21)
        ∎

    -- Chain memory preservation at x29
    mem-x29-final : readMem (memory s-final) (readReg (regs s) x29) ≡ readMem (memory s) (readReg (regs s) x29)
    mem-x29-final = begin
      readMem (memory s-final) (readReg (regs s) x29)
        ≡⟨ cong (readMem (memory s-final)) (sym x29-final) ⟩
      readMem (memory s-final) (readReg (regs s-final) x29)
        ≡⟨ cong (readMem (memory s-final)) x29-label ⟩
      readMem (memory s-final) (readReg (regs sg) x29)
        ≡⟨ mem-x29-label (readReg (regs sg) x29) ⟩
      readMem (memory sg) (readReg (regs sg) x29)
        ≡⟨ cong (readMem (memory sg)) (ir-x29 res-g) ⟩
      readMem (memory sg) (readReg (regs s-setup) x29)
        ≡⟨ ir-mem-x29 res-g ⟩
      readMem (memory s-setup) (readReg (regs s-setup) x29)
        ≡⟨ cong (readMem (memory s-setup)) x29-setup ⟩
      readMem (memory s-setup) (readReg (regs s) x29)
        ≡⟨ mem-x29-setup ⟩
      readMem (memory s) (readReg (regs s) x29)
        ∎

    -- Chain memory preservation at x29+8
    mem-x29+8-final : readMem (memory s-final) (readReg (regs s) x29 +ℕ 8) ≡ readMem (memory s) (readReg (regs s) x29 +ℕ 8)
    mem-x29+8-final = begin
      readMem (memory s-final) (readReg (regs s) x29 +ℕ 8)
        ≡⟨ cong (λ x → readMem (memory s-final) (x +ℕ 8)) (sym x29-final) ⟩
      readMem (memory s-final) (readReg (regs s-final) x29 +ℕ 8)
        ≡⟨ cong (λ x → readMem (memory s-final) (x +ℕ 8)) x29-label ⟩
      readMem (memory s-final) (readReg (regs sg) x29 +ℕ 8)
        ≡⟨ mem-x29-label (readReg (regs sg) x29 +ℕ 8) ⟩
      readMem (memory sg) (readReg (regs sg) x29 +ℕ 8)
        ≡⟨ cong (λ x → readMem (memory sg) (x +ℕ 8)) (ir-x29 res-g) ⟩
      readMem (memory sg) (readReg (regs s-setup) x29 +ℕ 8)
        ≡⟨ ir-mem-x29+8 res-g ⟩
      readMem (memory s-setup) (readReg (regs s-setup) x29 +ℕ 8)
        ≡⟨ cong (λ x → readMem (memory s-setup) (x +ℕ 8)) x29-setup ⟩
      readMem (memory s-setup) (readReg (regs s) x29 +ℕ 8)
        ≡⟨ mem-x29+8-setup ⟩
      readMem (memory s) (readReg (regs s) x29 +ℕ 8)
        ∎

    -- x0 contains addr-out
    x0-final : readReg (regs s-final) x0 ≡ addr-out
    x0-final = refl

    result : IRStarResultS [ f , g ] theProg s s-final addr-out (length prefix)
    result = record
      { ir-star = star-all
      ; ir-halted = h-label
      ; ir-pc = pc-label
      ; ir-x0-s = x0-final
      ; ir-x20 = x20-final
      ; ir-x21 = x21-final
      ; ir-x29 = x29-final
      ; ir-x30 = x30-final
      ; ir-sp = sp-final
      ; ir-mem-x21 = mem-x21-final
      ; ir-mem-x29 = mem-x29-final
      ; ir-mem-x29+8 = mem-x29+8-final
      ; ir-stack-inv = stack-inv-label
      ; ir-x29-inv = x29-inv-label
      ; ir-sp-bound = sp>16-label
      ; ir-closure-entry = nothing
      }

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
