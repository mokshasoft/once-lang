------------------------------------------------------------------------
-- Once.Backend.Common.Validity
--
-- Architecture-independent validity structures.
--
-- This module defines the STRUCTURE of memory validity predicates
-- using the shared Word/Memory types from Once.Memory.
--
-- Key abstractions:
--   - PairAtS, InlAtS, InrAtS, ClosureAtS: memory layout records
--   - ValidAtInterface: what validity implementations must provide
--   - Preservation lemmas for memory layout structures
------------------------------------------------------------------------

module Once.Backend.Common.Validity where

open import Data.Nat using (ℕ; zero; suc) renaming (_+_ to _+ℕ_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)

open import Once.Type using (Type; Unit; _*_; _+_; _⇒_; Eff; Fix)
open import Once.Semantics using (⟦_⟧; Closure; ⟦Fix⟧; wrap)
open import Once.Memory using (Word; Memory; readMem; word-size)
open ⟦Fix⟧

------------------------------------------------------------------------
-- Memory Layout Structures
--
-- These records describe how compound values are laid out in memory.
-- Shared across all architectures (all use Word = ℕ, word-size = 8).
------------------------------------------------------------------------

-- | Pair memory layout: [addr-a, addr-b] at addr
record PairAtS (addr-a addr-b addr : Word) (m : Memory) : Set where
  constructor pair-at-s
  field
    fst-valid : readMem m addr ≡ just addr-a
    snd-valid : readMem m (addr +ℕ word-size) ≡ just addr-b

open PairAtS public using () renaming (fst-valid to fst-valid-s; snd-valid to snd-valid-s)

-- | Left sum layout: [0, addr-val] at addr
record InlAtS (addr-val addr-sum : Word) (m : Memory) : Set where
  constructor inl-at-s
  field
    tag-valid : readMem m addr-sum ≡ just 0
    val-valid : readMem m (addr-sum +ℕ word-size) ≡ just addr-val

open InlAtS public using () renaming (tag-valid to tag-valid-inl-s; val-valid to val-valid-inl-s)

-- | Right sum layout: [1, addr-val] at addr
record InrAtS (addr-val addr-sum : Word) (m : Memory) : Set where
  constructor inr-at-s
  field
    tag-valid : readMem m addr-sum ≡ just 1
    val-valid : readMem m (addr-sum +ℕ word-size) ≡ just addr-val

open InrAtS public using () renaming (tag-valid to tag-valid-inr-s; val-valid to val-valid-inr-s)

-- | Closure layout: [env-addr, code-ptr] at addr
record ClosureAtS (env-addr code-ptr addr : Word) (m : Memory) : Set where
  constructor closure-at-s
  field
    env-valid : readMem m addr ≡ just env-addr
    code-valid : readMem m (addr +ℕ word-size) ≡ just code-ptr

open ClosureAtS public using () renaming (env-valid to env-valid-s; code-valid to code-valid-s)

------------------------------------------------------------------------
-- Structure Preservation under Memory Equality
--
-- These lemmas show that memory layout is preserved when memory
-- reads return the same values. Shared across architectures.
------------------------------------------------------------------------

PairAtS-preserved-under-mem-eq :
  ∀ {addr-a addr-b addr : Word} {m1 m2 : Memory} →
  PairAtS addr-a addr-b addr m1 →
  (∀ a → readMem m2 a ≡ readMem m1 a) →
  PairAtS addr-a addr-b addr m2
PairAtS-preserved-under-mem-eq {addr-a} {addr-b} {addr} pairS mem-eq =
  pair-at-s (trans (mem-eq addr) (fst-valid-s pairS))
            (trans (mem-eq (addr +ℕ word-size)) (snd-valid-s pairS))

InlAtS-preserved-under-mem-eq :
  ∀ {addr-val addr-sum : Word} {m1 m2 : Memory} →
  InlAtS addr-val addr-sum m1 →
  (∀ a → readMem m2 a ≡ readMem m1 a) →
  InlAtS addr-val addr-sum m2
InlAtS-preserved-under-mem-eq {addr-val} {addr-sum} inlS mem-eq =
  inl-at-s (trans (mem-eq addr-sum) (tag-valid-inl-s inlS))
           (trans (mem-eq (addr-sum +ℕ word-size)) (val-valid-inl-s inlS))

InrAtS-preserved-under-mem-eq :
  ∀ {addr-val addr-sum : Word} {m1 m2 : Memory} →
  InrAtS addr-val addr-sum m1 →
  (∀ a → readMem m2 a ≡ readMem m1 a) →
  InrAtS addr-val addr-sum m2
InrAtS-preserved-under-mem-eq {addr-val} {addr-sum} inrS mem-eq =
  inr-at-s (trans (mem-eq addr-sum) (tag-valid-inr-s inrS))
           (trans (mem-eq (addr-sum +ℕ word-size)) (val-valid-inr-s inrS))

ClosureAtS-preserved-under-mem-eq :
  ∀ {env-addr code-ptr addr : Word} {m1 m2 : Memory} →
  ClosureAtS env-addr code-ptr addr m1 →
  (∀ a → readMem m2 a ≡ readMem m1 a) →
  ClosureAtS env-addr code-ptr addr m2
ClosureAtS-preserved-under-mem-eq {env-addr} {code-ptr} {addr} closS mem-eq =
  closure-at-s (trans (mem-eq addr) (env-valid-s closS))
               (trans (mem-eq (addr +ℕ word-size)) (code-valid-s closS))

------------------------------------------------------------------------
-- ValidAt: The Core Validity Data Type
--
-- This is the shared definition of memory validity for all backends.
-- Says "value v is correctly represented at address a in memory m".
--
-- Key insight: Instead of proving "rax ≡ encode (eval ir x)" with postulates,
-- we prove "ValidAt (eval ir x) rax memory" directly from memory writes.
------------------------------------------------------------------------

open import Once.Semantics using (encode)

-- | Unified validity predicate for all types
-- Says "value v is correctly represented at address a in memory m"
data ValidAt : ∀ {A : Type} → ⟦ A ⟧ → Word → Memory → Set where
  -- Unit: value 0, no memory needed
  valid-unit : ∀ {m} → ValidAt {Unit} tt 0 m

  -- Pair: both components valid at their addresses, pair structure at addr
  valid-pair : ∀ {A B} {a : ⟦ A ⟧} {b : ⟦ B ⟧} {addr-a addr-b addr : Word} {m : Memory} →
    ValidAt a addr-a m →
    ValidAt b addr-b m →
    PairAtS addr-a addr-b addr m →
    ValidAt (a , b) addr m

  -- Left sum: tag=0, value valid
  valid-inl : ∀ {A B} {a : ⟦ A ⟧} {addr-a addr : Word} {m : Memory} →
    ValidAt a addr-a m →
    InlAtS addr-a addr m →
    ValidAt {A + B} (inj₁ a) addr m

  -- Right sum: tag=1, value valid
  valid-inr : ∀ {A B} {b : ⟦ B ⟧} {addr-b addr : Word} {m : Memory} →
    ValidAt b addr-b m →
    InrAtS addr-b addr m →
    ValidAt {A + B} (inj₂ b) addr m

  -- Closure: env and code-ptr at addr
  -- Note: Closures are abstract (env-addr and code-ptr are just words)
  -- code-ptr is a compilation artifact tracked in ClosureAtS/ClosureWellFormed
  valid-closure : ∀ {A B} {cl : Closure A B} {code-ptr addr : Word} {m : Memory} →
    ClosureAtS (Closure.env-addr cl) code-ptr addr m →
    ValidAt {A ⇒ B} cl addr m

  -- Closure from env validity: for curry-created closures
  -- When curry creates a closure, we have:
  --   1. Closure.env-addr cl ≡ encode env  (by eval definition for curry)
  --   2. ValidAt env env-addr m            (env validity from input)
  --   3. ClosureAtS layout                 (from memory writes)
  valid-closure-env : ∀ {A B E} {cl : Closure A B} {env : ⟦ E ⟧}
                      {env-addr code-ptr closure-addr : Word} {m : Memory} →
    Closure.env-addr cl ≡ encode env →  -- semantic property (refl for curry)
    ValidAt env env-addr m →             -- env validity at runtime address
    ClosureAtS env-addr code-ptr closure-addr m →  -- memory layout
    ValidAt {A ⇒ B} cl closure-addr m

  -- Eff: same as closure (Eff = Closure at runtime)
  -- code-ptr is a parameter (not from Closure record)
  valid-eff : ∀ {A B} {cl : Closure A B} {code-ptr addr : Word} {m : Memory} →
    ClosureAtS (Closure.env-addr cl) code-ptr addr m →
    ValidAt {Eff A B} cl addr m

  -- Eff from env validity: for curry-created effect closures
  valid-eff-env : ∀ {A B E} {cl : Closure A B} {env : ⟦ E ⟧}
                  {env-addr code-ptr closure-addr : Word} {m : Memory} →
    Closure.env-addr cl ≡ encode env →
    ValidAt env env-addr m →
    ClosureAtS env-addr code-ptr closure-addr m →
    ValidAt {Eff A B} cl closure-addr m

  -- Fix: validity of unwrapped value (Fix is identity at runtime)
  valid-fix : ∀ {F} {x : ⟦ F ⟧} {addr : Word} {m : Memory} →
    ValidAt x addr m →
    ValidAt {Fix F} (wrap x) addr m

------------------------------------------------------------------------
-- ValidAt Preservation under Memory Equality
--
-- If memory reads return the same values, validity is preserved.
-- This is the foundation for all preservation lemmas.
------------------------------------------------------------------------

-- | Propagate validity through address/memory substitution
-- If validity holds at addr1/mem1, and addr2=addr1 and mem2 agrees with mem1,
-- then validity holds at addr2/mem2.
-- Proven by induction on ValidAt structure.
valid-subst-addr-mem :
  ∀ {A} {v : ⟦ A ⟧} {addr1 addr2 : Word} {mem1 mem2 : Memory} →
  ValidAt v addr1 mem1 →
  addr2 ≡ addr1 →
  (∀ a → readMem mem2 a ≡ readMem mem1 a) →
  ValidAt v addr2 mem2
valid-subst-addr-mem valid-unit refl _ = valid-unit
valid-subst-addr-mem (valid-pair va vb pairS) refl mem-eq =
  valid-pair (valid-subst-addr-mem va refl mem-eq)
             (valid-subst-addr-mem vb refl mem-eq)
             (PairAtS-preserved-under-mem-eq pairS mem-eq)
valid-subst-addr-mem (valid-inl va inlS) refl mem-eq =
  valid-inl (valid-subst-addr-mem va refl mem-eq)
            (InlAtS-preserved-under-mem-eq inlS mem-eq)
valid-subst-addr-mem (valid-inr vb inrS) refl mem-eq =
  valid-inr (valid-subst-addr-mem vb refl mem-eq)
            (InrAtS-preserved-under-mem-eq inrS mem-eq)
valid-subst-addr-mem (valid-closure closS) refl mem-eq =
  valid-closure (ClosureAtS-preserved-under-mem-eq closS mem-eq)
valid-subst-addr-mem (valid-closure-env sem-eq venv closS) refl mem-eq =
  valid-closure-env sem-eq
    (valid-subst-addr-mem venv refl mem-eq)
    (ClosureAtS-preserved-under-mem-eq closS mem-eq)
valid-subst-addr-mem (valid-eff closS) refl mem-eq =
  valid-eff (ClosureAtS-preserved-under-mem-eq closS mem-eq)
valid-subst-addr-mem (valid-eff-env sem-eq venv closS) refl mem-eq =
  valid-eff-env sem-eq
    (valid-subst-addr-mem venv refl mem-eq)
    (ClosureAtS-preserved-under-mem-eq closS mem-eq)
valid-subst-addr-mem (valid-fix vx) refl mem-eq =
  valid-fix (valid-subst-addr-mem vx refl mem-eq)

------------------------------------------------------------------------
-- Proven lemmas from ValidAt structure
------------------------------------------------------------------------

-- | Left injection tag is 0 in memory
valid-inl-tag-is-0 :
  ∀ {A B} {a : ⟦ A ⟧} {addr : Word} {mem : Memory} →
  ValidAt {A + B} (inj₁ a) addr mem →
  readMem mem addr ≡ just 0
valid-inl-tag-is-0 (valid-inl _ inlS) = tag-valid-inl-s inlS

-- | Right injection tag is 1 in memory
valid-inr-tag-is-1 :
  ∀ {A B} {b : ⟦ B ⟧} {addr : Word} {mem : Memory} →
  ValidAt {A + B} (inj₂ b) addr mem →
  readMem mem addr ≡ just 1
valid-inr-tag-is-1 (valid-inr _ inrS) = tag-valid-inr-s inrS

-- | Left injection value pointer exists in memory
valid-inl-val-ptr :
  ∀ {A B} {a : ⟦ A ⟧} {addr : Word} {mem : Memory} →
  ValidAt {A + B} (inj₁ a) addr mem →
  ∃[ val-addr ] (readMem mem (addr +ℕ word-size) ≡ just val-addr × ValidAt a val-addr mem)
valid-inl-val-ptr (valid-inl {addr-a = addr-a} va inlS) = addr-a , val-valid-inl-s inlS , va

-- | Right injection value pointer exists in memory
valid-inr-val-ptr :
  ∀ {A B} {b : ⟦ B ⟧} {addr : Word} {mem : Memory} →
  ValidAt {A + B} (inj₂ b) addr mem →
  ∃[ val-addr ] (readMem mem (addr +ℕ word-size) ≡ just val-addr × ValidAt b val-addr mem)
valid-inr-val-ptr (valid-inr {addr-b = addr-b} vb inrS) = addr-b , val-valid-inr-s inrS , vb

-- | Extract fst component validity from pair validity
valid-pair-decompose :
  ∀ {A B} {a : ⟦ A ⟧} {b : ⟦ B ⟧} {addr : Word} {mem : Memory} →
  ValidAt {A * B} (a , b) addr mem →
  ∃[ addr-a ] ∃[ addr-b ]
    (ValidAt a addr-a mem × ValidAt b addr-b mem × PairAtS addr-a addr-b addr mem)
valid-pair-decompose (valid-pair {addr-a = addr-a} {addr-b = addr-b} va vb pairS) =
  addr-a , addr-b , va , vb , pairS

-- | Convert validity from (A ⇒ B) to (Eff A B)
-- These types have the same runtime representation (Closure A B), but
-- ValidAt uses Type as a type index, so conversion is needed.
valid-arrow-to-eff :
  ∀ {A B} {cl : Closure A B} {addr : Word} {m : Memory} →
  ValidAt {A ⇒ B} cl addr m →
  ValidAt {Eff A B} cl addr m
valid-arrow-to-eff (valid-closure closS) = valid-eff closS
valid-arrow-to-eff (valid-closure-env sem-eq venv closS) = valid-eff-env sem-eq venv closS

------------------------------------------------------------------------
-- ValidAt Interface (for compatibility with abstract proofs)
--
-- This allows proofs to work abstractly over validity if needed.
------------------------------------------------------------------------

record ValidAtInterface : Set₁ where
  field
    -- The validity predicate
    ValidAtF : ∀ {A : Type} → ⟦ A ⟧ → Word → Memory → Set

    -- Validity of unit (always at address 0)
    valid-unitI : ∀ {m} → ValidAtF {Unit} tt 0 m

    -- Validity of pairs
    valid-pairI : ∀ {A B} {a : ⟦ A ⟧} {b : ⟦ B ⟧} {addr-a addr-b addr : Word} {m : Memory} →
      ValidAtF a addr-a m →
      ValidAtF b addr-b m →
      PairAtS addr-a addr-b addr m →
      ValidAtF (a , b) addr m

    -- Validity of left sum
    valid-inlI : ∀ {A B} {a : ⟦ A ⟧} {addr-a addr : Word} {m : Memory} →
      ValidAtF a addr-a m →
      InlAtS addr-a addr m →
      ValidAtF {A + B} (inj₁ a) addr m

    -- Validity of right sum
    valid-inrI : ∀ {A B} {b : ⟦ B ⟧} {addr-b addr : Word} {m : Memory} →
      ValidAtF b addr-b m →
      InrAtS addr-b addr m →
      ValidAtF {A + B} (inj₂ b) addr m

    -- Validity of closures
    valid-closureI : ∀ {A B} {cl : Closure A B} {code-ptr addr : Word} {m : Memory} →
      ClosureAtS (Closure.env-addr cl) code-ptr addr m →
      ValidAtF {A ⇒ B} cl addr m

    -- Validity of Fix (wrapper is transparent)
    valid-fixI : ∀ {F} {x : ⟦ F ⟧} {addr : Word} {m : Memory} →
      ValidAtF x addr m →
      ValidAtF {Fix F} (wrap x) addr m

-- | The concrete ValidAt type satisfies the ValidAtInterface
concreteValidAtInterface : ValidAtInterface
concreteValidAtInterface = record
  { ValidAtF = ValidAt
  ; valid-unitI = valid-unit
  ; valid-pairI = valid-pair
  ; valid-inlI = valid-inl
  ; valid-inrI = valid-inr
  ; valid-closureI = valid-closure
  ; valid-fixI = valid-fix
  }

------------------------------------------------------------------------
-- Summary
--
-- This module provides:
--   1. Memory layout records (PairAtS, InlAtS, InrAtS, ClosureAtS)
--   2. Preservation lemmas for layouts under memory equality
--   3. ValidAt data type - the core validity predicate
--   4. valid-subst-addr-mem - validity preservation under memory equality
--   5. Derived lemmas (valid-inl-tag-is-0, valid-inr-tag-is-1, etc.)
--   6. ValidAtInterface - abstract interface for compatibility
--
-- Each architecture:
--   1. Imports ValidAt and AtS records from this module
--   2. Adds region-based preservation lemmas (using InHeap/InStack)
--   3. Provides any architecture-specific postulates (valid-in-heap, etc.)
--
-- NOTE: Region-based preservation lemmas (like valid-at-preserved-under-stack-write)
-- are NOT in this module because they require InHeap/InStack from Regions.agda,
-- which is parameterized over MemoryLayout. Those stay in X86/MemoryValid.agda.
------------------------------------------------------------------------
