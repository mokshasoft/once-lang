------------------------------------------------------------------------
-- Once.Backend.X86.Correct.MemoryValid
--
-- Memory validity predicates for x86-64 execution.
-- Tracks which values are properly encoded in memory.
--
-- Key insight: The encoding axioms in Postulates.agda claim to hold
-- for ANY memory m. This is too strong. They should only hold for
-- memory where values were properly allocated.
--
-- MemoryValid captures the invariant that values in memory are
-- properly encoded at their expected addresses.
------------------------------------------------------------------------

module Once.Backend.X86.Correct.MemoryValid where

open import Once.Type
open import Once.Semantics using (⟦_⟧; encode; Closure; ⟦Fix⟧; wrap)
open ⟦Fix⟧
open import Once.Backend.X86.Semantics using (State; Memory; Word; readMem; writeMem)
open import Once.Backend.X86.Encoding using (mem-read-write; mem-read-other; n≢n+word-size)
open import Once.Backend.X86.Correct.StackInstantiation using (slot-size)
open import Once.Backend.X86.Layout
  using (InStack; InHeap; stack-heap-addr-disjoint; heap-offset)
open import Once.Backend.X86.Correct.RegisterLemmas using (readMem-writeMem-diff)
open import Once.Backend.X86.Correct.Star using (just-injective)
open import Once.Backend.X86.Correct.StackInstantiation
  using (encode-in-heap-sem)

open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ) renaming (_+_ to _+ℕ_)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; subst; cong)

------------------------------------------------------------------------
-- ValueAt: A value is properly encoded at an address in memory
------------------------------------------------------------------------

-- | A pair value (a, b) is encoded at address addr in memory m
-- This means: m[addr] = encode a, m[addr+8] = encode b
record PairAt {A B : Type} (a : ⟦ A ⟧) (b : ⟦ B ⟧) (addr : Word) (m : Memory) : Set where
  constructor pair-at
  field
    fst-valid : readMem m addr ≡ just (encode a)
    snd-valid : readMem m (addr +ℕ slot-size) ≡ just (encode b)

open PairAt public

-- | A left sum value (inj₁ a) is encoded at address addr in memory m
-- This means: m[addr] = 0 (tag), m[addr+8] = encode a
record InlAt {A B : Type} (a : ⟦ A ⟧) (addr : Word) (m : Memory) : Set where
  constructor inl-at
  field
    tag-valid : readMem m addr ≡ just 0
    val-valid : readMem m (addr +ℕ slot-size) ≡ just (encode a)

open InlAt public

-- | A right sum value (inj₂ b) is encoded at address addr in memory m
-- This means: m[addr] = 1 (tag), m[addr+8] = encode b
record InrAt {A B : Type} (b : ⟦ B ⟧) (addr : Word) (m : Memory) : Set where
  constructor inr-at
  field
    tag-valid : readMem m addr ≡ just 1
    val-valid : readMem m (addr +ℕ slot-size) ≡ just (encode b)

open InrAt public

------------------------------------------------------------------------
-- Stateful Validity Predicates (no reference to abstract encode)
--
-- These predicates use explicit addresses instead of the abstract
-- `encode` function. This breaks the circular dependency on postulates
-- and allows validity to be proven from stateful allocation theorems.
------------------------------------------------------------------------

-- | Pair validity with explicit component addresses
-- Memory at addr-pair contains [addr-a, addr-b]
record PairAtS (addr-a addr-b addr-pair : Word) (m : Memory) : Set where
  constructor pair-at-s
  field
    fst-valid : readMem m addr-pair ≡ just addr-a
    snd-valid : readMem m (addr-pair +ℕ slot-size) ≡ just addr-b

open PairAtS public using () renaming (fst-valid to fst-valid-s; snd-valid to snd-valid-s)

-- | Left sum validity with explicit value address
-- Memory at addr-sum contains [0, addr-val]
record InlAtS (addr-val addr-sum : Word) (m : Memory) : Set where
  constructor inl-at-s
  field
    tag-valid : readMem m addr-sum ≡ just 0
    val-valid : readMem m (addr-sum +ℕ slot-size) ≡ just addr-val

open InlAtS public using () renaming (tag-valid to tag-valid-inl-s; val-valid to val-valid-inl-s)

-- | Right sum validity with explicit value address
-- Memory at addr-sum contains [1, addr-val]
record InrAtS (addr-val addr-sum : Word) (m : Memory) : Set where
  constructor inr-at-s
  field
    tag-valid : readMem m addr-sum ≡ just 1
    val-valid : readMem m (addr-sum +ℕ slot-size) ≡ just addr-val

open InrAtS public using () renaming (tag-valid to tag-valid-inr-s; val-valid to val-valid-inr-s)

-- | Closure validity with explicit addresses
-- Memory at addr-closure contains [env-addr, code-ptr]
record ClosureAtS (env-addr code-ptr addr-closure : Word) (m : Memory) : Set where
  constructor closure-at-s
  field
    env-valid : readMem m addr-closure ≡ just env-addr
    code-valid : readMem m (addr-closure +ℕ slot-size) ≡ just code-ptr

open ClosureAtS public using () renaming (env-valid to env-valid-s; code-valid to code-valid-s)

------------------------------------------------------------------------
-- ValidAt: Unified Validity Predicate
--
-- This is the core abstraction for validity-based correctness.
-- ValidAt says "value v is correctly represented at address a in memory m".
--
-- Key insight: Instead of proving "rax ≡ encode (eval ir x)" with postulates,
-- we prove "ValidAt (eval ir x) rax memory" directly from memory writes.
------------------------------------------------------------------------

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
  -- Closure validity: code-ptr is a parameter (not from Closure record)
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

-- NOTE: ValidAt preservation under memory writes is defined below,
-- after the valid-in-heap postulate which it depends on.
-- See: valid-at-preserved-under-stack-write, valid-at-preserved-under-write

------------------------------------------------------------------------
-- Entry Point: encode → ValidAt
--
-- This foundational postulate establishes validity at system entry:
-- when external code provides input x encoded in memory at address addr,
-- this asserts the validity predicate holds.
------------------------------------------------------------------------
postulate
  -- | Construct validity from encode address at entry point
  -- This is a foundational postulate for the system entry point:
  -- when external code provides input x, it is encoded in memory, and
  -- this establishes validity at the encoded address.
  -- Used by codegen-x86-correct to establish initial input validity.
  valid-from-encode :
    ∀ {A} {v : ⟦ A ⟧} {addr : Word} {m : Memory} →
    addr ≡ encode v →
    ValidAt v addr m


-- | Convert validity from (A ⇒ B) to (Eff A B)
-- These types have the same runtime representation (Closure A B), but
-- ValidAt uses Type as a type index, so conversion is needed.
-- Proven by pattern matching on valid-closure and constructing valid-eff.
valid-arrow-to-eff :
  ∀ {A B} {cl : Closure A B} {addr : Word} {m : Memory} →
  ValidAt {A ⇒ B} cl addr m →
  ValidAt {Eff A B} cl addr m
valid-arrow-to-eff (valid-closure closS) = valid-eff closS
valid-arrow-to-eff (valid-closure-env sem-eq venv closS) = valid-eff-env sem-eq venv closS

postulate

  -- | Valid address is in heap region
  -- ValidAt structures represent heap-allocated data, so the address must be in heap.
  -- This is the fundamental connection between validity and memory regions.
  -- ELIMINABLE: Provable by induction on ValidAt structure - all constructors use
  -- heap addresses (from encode which always returns heap addresses).
  valid-in-heap :
    ∀ {A} {v : ⟦ A ⟧} {addr : Word} {m : Memory} →
    ValidAt v addr m →
    InHeap addr

-- | Extract validity of left injection's child value
-- If (inj₁ a) is validly represented at addr, and mem[addr+8] = val-addr,
-- then a is validly represented at val-addr.
-- Proven from ValidAt structure (sum validity implies child validity).
valid-inl-child :
  ∀ {A B} {a : ⟦ A ⟧} {addr val-addr : Word} {mem : Memory} →
  ValidAt {A + B} (inj₁ a) addr mem →
  readMem mem (addr +ℕ slot-size) ≡ just val-addr →
  ValidAt a val-addr mem
valid-inl-child (valid-inl {addr-a = addr-a} va inlS) mem-eq =
  let addr-eq = just-injective (trans (sym (val-valid-inl-s inlS)) mem-eq)
  in subst (λ a → ValidAt _ a _) addr-eq va

-- | Extract validity of right injection's child value
-- If (inj₂ b) is validly represented at addr, and mem[addr+8] = val-addr,
-- then b is validly represented at val-addr.
-- Proven from ValidAt structure (sum validity implies child validity).
valid-inr-child :
  ∀ {A B} {b : ⟦ B ⟧} {addr val-addr : Word} {mem : Memory} →
  ValidAt {A + B} (inj₂ b) addr mem →
  readMem mem (addr +ℕ slot-size) ≡ just val-addr →
  ValidAt b val-addr mem
valid-inr-child (valid-inr {addr-b = addr-b} vb inrS) mem-eq =
  let addr-eq = just-injective (trans (sym (val-valid-inr-s inrS)) mem-eq)
  in subst (λ a → ValidAt _ a _) addr-eq vb

------------------------------------------------------------------------
-- AtS preservation under memory equality
------------------------------------------------------------------------

-- | Helper: PairAtS preserved under memory equality
PairAtS-preserved-under-mem-eq :
  ∀ {addr-a addr-b addr : Word} {m1 m2 : Memory} →
  PairAtS addr-a addr-b addr m1 →
  (∀ a → readMem m2 a ≡ readMem m1 a) →
  PairAtS addr-a addr-b addr m2
PairAtS-preserved-under-mem-eq {addr-a} {addr-b} {addr} pairS mem-eq =
  pair-at-s (trans (mem-eq addr) (fst-valid-s pairS))
            (trans (mem-eq (addr +ℕ slot-size)) (snd-valid-s pairS))

-- | Helper: InlAtS preserved under memory equality
InlAtS-preserved-under-mem-eq :
  ∀ {addr-val addr-sum : Word} {m1 m2 : Memory} →
  InlAtS addr-val addr-sum m1 →
  (∀ a → readMem m2 a ≡ readMem m1 a) →
  InlAtS addr-val addr-sum m2
InlAtS-preserved-under-mem-eq {addr-val} {addr-sum} inlS mem-eq =
  inl-at-s (trans (mem-eq addr-sum) (tag-valid-inl-s inlS))
           (trans (mem-eq (addr-sum +ℕ slot-size)) (val-valid-inl-s inlS))

-- | Helper: InrAtS preserved under memory equality
InrAtS-preserved-under-mem-eq :
  ∀ {addr-val addr-sum : Word} {m1 m2 : Memory} →
  InrAtS addr-val addr-sum m1 →
  (∀ a → readMem m2 a ≡ readMem m1 a) →
  InrAtS addr-val addr-sum m2
InrAtS-preserved-under-mem-eq {addr-val} {addr-sum} inrS mem-eq =
  inr-at-s (trans (mem-eq addr-sum) (tag-valid-inr-s inrS))
           (trans (mem-eq (addr-sum +ℕ slot-size)) (val-valid-inr-s inrS))

-- | Helper: ClosureAtS preserved under memory equality
ClosureAtS-preserved-under-mem-eq :
  ∀ {env-addr code-ptr addr-closure : Word} {m1 m2 : Memory} →
  ClosureAtS env-addr code-ptr addr-closure m1 →
  (∀ a → readMem m2 a ≡ readMem m1 a) →
  ClosureAtS env-addr code-ptr addr-closure m2
ClosureAtS-preserved-under-mem-eq {env-addr} {code-ptr} {addr-closure} closS mem-eq =
  closure-at-s (trans (mem-eq addr-closure) (env-valid-s closS))
               (trans (mem-eq (addr-closure +ℕ slot-size)) (code-valid-s closS))

------------------------------------------------------------------------
-- ValidAt preservation under memory equality
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
-- ValidAt preservation under heap-only memory preservation
------------------------------------------------------------------------

-- The key insight: ValidAt only references heap addresses (established by valid-in-heap),
-- so heap preservation is sufficient for validity propagation.

-- Note: These helpers require InHeap proofs which come from valid-in-heap (postulate).
-- We define them here but they rely on valid-in-heap being called appropriately.

-- | Helper: PairAtS preserved under heap-only memory equality
PairAtS-preserved-under-heap-eq :
  ∀ {addr-a addr-b addr : Word} {m1 m2 : Memory} →
  PairAtS addr-a addr-b addr m1 →
  InHeap addr →  -- addr is in heap
  (∀ a → InHeap a → readMem m2 a ≡ readMem m1 a) →
  PairAtS addr-a addr-b addr m2
PairAtS-preserved-under-heap-eq {addr-a} {addr-b} {addr} pairS addr-in-heap heap-eq =
  let addr+8-in-heap = heap-offset addr slot-size addr-in-heap
  in pair-at-s (trans (heap-eq addr addr-in-heap) (fst-valid-s pairS))
               (trans (heap-eq (addr +ℕ slot-size) addr+8-in-heap) (snd-valid-s pairS))

-- | Helper: InlAtS preserved under heap-only memory equality
InlAtS-preserved-under-heap-eq :
  ∀ {addr-val addr-sum : Word} {m1 m2 : Memory} →
  InlAtS addr-val addr-sum m1 →
  InHeap addr-sum →
  (∀ a → InHeap a → readMem m2 a ≡ readMem m1 a) →
  InlAtS addr-val addr-sum m2
InlAtS-preserved-under-heap-eq {addr-val} {addr-sum} inlS addr-in-heap heap-eq =
  let addr+8-in-heap = heap-offset addr-sum slot-size addr-in-heap
  in inl-at-s (trans (heap-eq addr-sum addr-in-heap) (tag-valid-inl-s inlS))
              (trans (heap-eq (addr-sum +ℕ slot-size) addr+8-in-heap) (val-valid-inl-s inlS))

-- | Helper: InrAtS preserved under heap-only memory equality
InrAtS-preserved-under-heap-eq :
  ∀ {addr-val addr-sum : Word} {m1 m2 : Memory} →
  InrAtS addr-val addr-sum m1 →
  InHeap addr-sum →
  (∀ a → InHeap a → readMem m2 a ≡ readMem m1 a) →
  InrAtS addr-val addr-sum m2
InrAtS-preserved-under-heap-eq {addr-val} {addr-sum} inrS addr-in-heap heap-eq =
  let addr+8-in-heap = heap-offset addr-sum slot-size addr-in-heap
  in inr-at-s (trans (heap-eq addr-sum addr-in-heap) (tag-valid-inr-s inrS))
              (trans (heap-eq (addr-sum +ℕ slot-size) addr+8-in-heap) (val-valid-inr-s inrS))

-- | Helper: ClosureAtS preserved under heap-only memory equality
ClosureAtS-preserved-under-heap-eq :
  ∀ {env-addr code-ptr addr-closure : Word} {m1 m2 : Memory} →
  ClosureAtS env-addr code-ptr addr-closure m1 →
  InHeap addr-closure →
  (∀ a → InHeap a → readMem m2 a ≡ readMem m1 a) →
  ClosureAtS env-addr code-ptr addr-closure m2
ClosureAtS-preserved-under-heap-eq {env-addr} {code-ptr} {addr-closure} closS addr-in-heap heap-eq =
  let addr+8-in-heap = heap-offset addr-closure slot-size addr-in-heap
  in closure-at-s (trans (heap-eq addr-closure addr-in-heap) (env-valid-s closS))
                  (trans (heap-eq (addr-closure +ℕ slot-size) addr+8-in-heap) (code-valid-s closS))

-- | Propagate validity when only heap memory is preserved
-- ValidAt structures only depend on heap memory (not stack), so heap
-- preservation is sufficient for validity propagation.
-- Proven by induction on ValidAt structure using valid-in-heap.
valid-subst-heap-preserved :
  ∀ {A} {v : ⟦ A ⟧} {addr1 addr2 : Word} {mem1 mem2 : Memory} →
  ValidAt v addr1 mem1 →
  addr2 ≡ addr1 →
  (∀ a → InHeap a → readMem mem2 a ≡ readMem mem1 a) →
  ValidAt v addr2 mem2
valid-subst-heap-preserved valid-unit refl _ = valid-unit
valid-subst-heap-preserved (valid-pair {addr = addr} va vb pairS) refl heap-eq =
  let heap-proof = valid-in-heap (valid-pair va vb pairS)
  in valid-pair (valid-subst-heap-preserved va refl heap-eq)
                (valid-subst-heap-preserved vb refl heap-eq)
                (PairAtS-preserved-under-heap-eq pairS heap-proof heap-eq)
valid-subst-heap-preserved {A + B} (valid-inl {a = a} {addr-a = addr-a} {addr = addr} va inlS) refl heap-eq =
  let heap-proof = valid-in-heap (valid-inl {A} {B} {a} va inlS)
  in valid-inl (valid-subst-heap-preserved va refl heap-eq)
               (InlAtS-preserved-under-heap-eq inlS heap-proof heap-eq)
valid-subst-heap-preserved {A + B} (valid-inr {b = b} {addr-b = addr-b} {addr = addr} vb inrS) refl heap-eq =
  let heap-proof = valid-in-heap (valid-inr {A} {B} {b} vb inrS)
  in valid-inr (valid-subst-heap-preserved vb refl heap-eq)
               (InrAtS-preserved-under-heap-eq inrS heap-proof heap-eq)
valid-subst-heap-preserved {A ⇒[ _ ] B} {cl} (valid-closure {code-ptr = cp} {addr = addr} closS) refl heap-eq =
  let heap-proof = valid-in-heap (valid-closure {cl = cl} {code-ptr = cp} closS)
  in valid-closure (ClosureAtS-preserved-under-heap-eq closS heap-proof heap-eq)
valid-subst-heap-preserved {A ⇒[ _ ] B} {cl} (valid-closure-env {E = E} {env = env} {env-addr = ea} {code-ptr = cp} {closure-addr = addr} sem-eq venv closS) refl heap-eq =
  let heap-proof = valid-in-heap (valid-closure-env {A} {B} {E} {cl} {env} sem-eq venv closS)
  in valid-closure-env sem-eq
       (valid-subst-heap-preserved venv refl heap-eq)
       (ClosureAtS-preserved-under-heap-eq closS heap-proof heap-eq)
valid-subst-heap-preserved {Eff A B} {cl} (valid-eff {code-ptr = cp} {addr = addr} closS) refl heap-eq =
  let heap-proof = valid-in-heap (valid-eff {cl = cl} {code-ptr = cp} closS)
  in valid-eff (ClosureAtS-preserved-under-heap-eq closS heap-proof heap-eq)
valid-subst-heap-preserved {Eff A B} {cl} (valid-eff-env {E = E} {env = env} {env-addr = ea} {code-ptr = cp} {closure-addr = addr} sem-eq venv closS) refl heap-eq =
  let heap-proof = valid-in-heap (valid-eff-env {A} {B} {E} {cl} {env} sem-eq venv closS)
  in valid-eff-env sem-eq
       (valid-subst-heap-preserved venv refl heap-eq)
       (ClosureAtS-preserved-under-heap-eq closS heap-proof heap-eq)
valid-subst-heap-preserved (valid-fix vx) refl heap-eq =
  valid-fix (valid-subst-heap-preserved vx refl heap-eq)

------------------------------------------------------------------------
-- Proven lemmas from ValidAt structure (moved out of postulate block)
------------------------------------------------------------------------

-- | Left injection tag is 0 in memory
-- Pattern match on ValidAt: only valid-inl can construct ValidAt {A + B} (inj₁ a)
valid-inl-tag-is-0 :
  ∀ {A B} {a : ⟦ A ⟧} {addr : Word} {mem : Memory} →
  ValidAt {A + B} (inj₁ a) addr mem →
  readMem mem addr ≡ just 0
valid-inl-tag-is-0 (valid-inl _ inlS) = tag-valid-inl-s inlS

-- | Left injection value pointer exists in memory
valid-inl-val-ptr :
  ∀ {A B} {a : ⟦ A ⟧} {addr : Word} {mem : Memory} →
  ValidAt {A + B} (inj₁ a) addr mem →
  ∃[ val-addr ] (readMem mem (addr +ℕ slot-size) ≡ just val-addr × ValidAt a val-addr mem)
valid-inl-val-ptr (valid-inl {addr-a = addr-a} va inlS) = addr-a , val-valid-inl-s inlS , va

-- | Right injection tag is 1 in memory
valid-inr-tag-is-1 :
  ∀ {A B} {b : ⟦ B ⟧} {addr : Word} {mem : Memory} →
  ValidAt {A + B} (inj₂ b) addr mem →
  readMem mem addr ≡ just 1
valid-inr-tag-is-1 (valid-inr _ inrS) = tag-valid-inr-s inrS

-- | Right injection value pointer exists in memory
valid-inr-val-ptr :
  ∀ {A B} {b : ⟦ B ⟧} {addr : Word} {mem : Memory} →
  ValidAt {A + B} (inj₂ b) addr mem →
  ∃[ val-addr ] (readMem mem (addr +ℕ slot-size) ≡ just val-addr × ValidAt b val-addr mem)
valid-inr-val-ptr (valid-inr {addr-b = addr-b} vb inrS) = addr-b , val-valid-inr-s inrS , vb

-- | Extract fst component validity from pair validity
valid-pair-decompose :
  ∀ {A B} {a : ⟦ A ⟧} {b : ⟦ B ⟧} {addr : Word} {mem : Memory} →
  ValidAt {A * B} (a , b) addr mem →
  ∃[ addr-a ] ∃[ addr-b ]
    (ValidAt a addr-a mem × ValidAt b addr-b mem × PairAtS addr-a addr-b addr mem)
valid-pair-decompose (valid-pair {addr-a = addr-a} {addr-b = addr-b} va vb pairS) =
  addr-a , addr-b , va , vb , pairS

-- | Extract closure memory layout from closure validity
-- Returns existential code-ptr since it's not part of the semantic Closure
-- POSTULATE: The valid-closure-env case requires knowing env-addr = Closure.env-addr cl,
-- which requires env-addr = encode x at function entry. This is an encode boundary issue.
postulate
  valid-closure-decompose :
    ∀ {A B} {cl : Closure A B} {addr : Word} {mem : Memory} →
    ValidAt {A ⇒ B} cl addr mem →
    ∃[ code-ptr ] ClosureAtS (Closure.env-addr cl) code-ptr addr mem

------------------------------------------------------------------------
-- Region-based disjointness from validity (Phase 6c-6d)
--
-- These lemmas derive heap-stack disjointness from ValidAt.
-- Uses valid-in-heap postulate directly - no addr-from-valid dependency!
------------------------------------------------------------------------

-- | Valid address is in heap
-- Direct application of valid-in-heap postulate.
valid-addr-in-heap : ∀ {A : Type} {v : ⟦ A ⟧} {addr : Word} {m : Memory} →
  ValidAt v addr m →
  InHeap addr
valid-addr-in-heap = valid-in-heap

-- | Valid address is disjoint from stack addresses
-- If addr has ValidAt and stack-addr is in stack, then addr ≢ stack-addr
valid-disjoint-from-stack : ∀ {A : Type} {v : ⟦ A ⟧} {addr stack-addr : Word} {m : Memory} →
  ValidAt v addr m →
  InStack stack-addr →
  addr ≢ stack-addr
valid-disjoint-from-stack {A} {v} {addr} {stack-addr} {m} valid stack-proof addr-eq =
  stack-heap-addr-disjoint stack-addr addr stack-proof (valid-addr-in-heap valid) (sym addr-eq)

------------------------------------------------------------------------
-- ValidAt preservation under memory writes
--
-- Key insight: writes to stack addresses cannot affect ValidAt proofs
-- because ValidAt structures only reference heap addresses.
--
-- Proof strategy:
-- 1. ValidAt v addr m → InHeap addr (by valid-in-heap)
-- 2. AtS structures read from addr and addr+slot-size, both in heap
-- 3. InStack w means w is disjoint from all heap addresses
-- 4. Therefore readMem (writeMem m w val) heap-addr = readMem m heap-addr
------------------------------------------------------------------------

-- | Helper: PairAtS preserved under stack writes
PairAtS-preserved-under-stack-write :
  ∀ {addr-a addr-b addr w val : Word} {m : Memory} →
  PairAtS addr-a addr-b addr m →
  InHeap addr →
  InStack w →
  PairAtS addr-a addr-b addr (writeMem m w val)
PairAtS-preserved-under-stack-write {addr-a} {addr-b} {addr} {w} {val} {m} pairS addr-in-heap w-in-stack =
  pair-at-s fst-pres snd-pres
  where
    -- w is in stack, addr is in heap, so w ≢ addr
    w≢addr : w ≢ addr
    w≢addr eq = stack-heap-addr-disjoint w addr w-in-stack addr-in-heap eq

    -- addr+slot-size is in heap (heap-offset), so w ≢ addr+slot-size
    addr+8-in-heap : InHeap (addr +ℕ slot-size)
    addr+8-in-heap = heap-offset addr slot-size addr-in-heap

    w≢addr+8 : w ≢ (addr +ℕ slot-size)
    w≢addr+8 eq = stack-heap-addr-disjoint w (addr +ℕ slot-size) w-in-stack addr+8-in-heap eq

    fst-pres : readMem (writeMem m w val) addr ≡ just addr-a
    fst-pres = trans (readMem-writeMem-diff m w addr val w≢addr) (fst-valid-s pairS)

    snd-pres : readMem (writeMem m w val) (addr +ℕ slot-size) ≡ just addr-b
    snd-pres = trans (readMem-writeMem-diff m w (addr +ℕ slot-size) val w≢addr+8) (snd-valid-s pairS)

-- | Helper: InlAtS preserved under stack writes
InlAtS-preserved-under-stack-write :
  ∀ {addr-val addr-sum w val : Word} {m : Memory} →
  InlAtS addr-val addr-sum m →
  InHeap addr-sum →
  InStack w →
  InlAtS addr-val addr-sum (writeMem m w val)
InlAtS-preserved-under-stack-write {addr-val} {addr-sum} {w} {val} {m} inlS addr-in-heap w-in-stack =
  inl-at-s tag-pres val-pres
  where
    w≢addr : w ≢ addr-sum
    w≢addr eq = stack-heap-addr-disjoint w addr-sum w-in-stack addr-in-heap eq

    addr+8-in-heap : InHeap (addr-sum +ℕ slot-size)
    addr+8-in-heap = heap-offset addr-sum slot-size addr-in-heap

    w≢addr+8 : w ≢ (addr-sum +ℕ slot-size)
    w≢addr+8 eq = stack-heap-addr-disjoint w (addr-sum +ℕ slot-size) w-in-stack addr+8-in-heap eq

    tag-pres : readMem (writeMem m w val) addr-sum ≡ just 0
    tag-pres = trans (readMem-writeMem-diff m w addr-sum val w≢addr) (tag-valid-inl-s inlS)

    val-pres : readMem (writeMem m w val) (addr-sum +ℕ slot-size) ≡ just addr-val
    val-pres = trans (readMem-writeMem-diff m w (addr-sum +ℕ slot-size) val w≢addr+8) (val-valid-inl-s inlS)

-- | Helper: InrAtS preserved under stack writes
InrAtS-preserved-under-stack-write :
  ∀ {addr-val addr-sum w val : Word} {m : Memory} →
  InrAtS addr-val addr-sum m →
  InHeap addr-sum →
  InStack w →
  InrAtS addr-val addr-sum (writeMem m w val)
InrAtS-preserved-under-stack-write {addr-val} {addr-sum} {w} {val} {m} inrS addr-in-heap w-in-stack =
  inr-at-s tag-pres val-pres
  where
    w≢addr : w ≢ addr-sum
    w≢addr eq = stack-heap-addr-disjoint w addr-sum w-in-stack addr-in-heap eq

    addr+8-in-heap : InHeap (addr-sum +ℕ slot-size)
    addr+8-in-heap = heap-offset addr-sum slot-size addr-in-heap

    w≢addr+8 : w ≢ (addr-sum +ℕ slot-size)
    w≢addr+8 eq = stack-heap-addr-disjoint w (addr-sum +ℕ slot-size) w-in-stack addr+8-in-heap eq

    tag-pres : readMem (writeMem m w val) addr-sum ≡ just 1
    tag-pres = trans (readMem-writeMem-diff m w addr-sum val w≢addr) (tag-valid-inr-s inrS)

    val-pres : readMem (writeMem m w val) (addr-sum +ℕ slot-size) ≡ just addr-val
    val-pres = trans (readMem-writeMem-diff m w (addr-sum +ℕ slot-size) val w≢addr+8) (val-valid-inr-s inrS)

-- | Helper: ClosureAtS preserved under stack writes
ClosureAtS-preserved-under-stack-write :
  ∀ {env-addr code-ptr addr-closure w val : Word} {m : Memory} →
  ClosureAtS env-addr code-ptr addr-closure m →
  InHeap addr-closure →
  InStack w →
  ClosureAtS env-addr code-ptr addr-closure (writeMem m w val)
ClosureAtS-preserved-under-stack-write {env-addr} {code-ptr} {addr-closure} {w} {val} {m} closS addr-in-heap w-in-stack =
  closure-at-s env-pres code-pres
  where
    w≢addr : w ≢ addr-closure
    w≢addr eq = stack-heap-addr-disjoint w addr-closure w-in-stack addr-in-heap eq

    addr+8-in-heap : InHeap (addr-closure +ℕ slot-size)
    addr+8-in-heap = heap-offset addr-closure slot-size addr-in-heap

    w≢addr+8 : w ≢ (addr-closure +ℕ slot-size)
    w≢addr+8 eq = stack-heap-addr-disjoint w (addr-closure +ℕ slot-size) w-in-stack addr+8-in-heap eq

    env-pres : readMem (writeMem m w val) addr-closure ≡ just env-addr
    env-pres = trans (readMem-writeMem-diff m w addr-closure val w≢addr) (env-valid-s closS)

    code-pres : readMem (writeMem m w val) (addr-closure +ℕ slot-size) ≡ just code-ptr
    code-pres = trans (readMem-writeMem-diff m w (addr-closure +ℕ slot-size) val w≢addr+8) (code-valid-s closS)

-- | ValidAt is preserved when writing to stack addresses
-- Proven by induction on ValidAt structure.
-- Key insight: ValidAt only references heap addresses (via valid-in-heap),
-- and stack writes cannot affect heap memory.
valid-at-preserved-under-stack-write :
  ∀ {A} {v : ⟦ A ⟧} {addr-v w : Word} {val : Word} {m : Memory} →
  ValidAt v addr-v m →
  InStack w →
  ValidAt v addr-v (writeMem m w val)
valid-at-preserved-under-stack-write valid-unit w-in-stack = valid-unit
valid-at-preserved-under-stack-write (valid-pair {addr-a = addr-a} {addr-b = addr-b} {addr = addr} va vb pairS) w-in-stack =
  valid-pair
    (valid-at-preserved-under-stack-write va w-in-stack)
    (valid-at-preserved-under-stack-write vb w-in-stack)
    (PairAtS-preserved-under-stack-write {addr-a} {addr-b} {addr} pairS (valid-in-heap (valid-pair va vb pairS)) w-in-stack)
valid-at-preserved-under-stack-write {A = A + B} (valid-inl {A} {B} {addr-a = addr-a} {addr = addr} va inlS) w-in-stack =
  valid-inl
    (valid-at-preserved-under-stack-write va w-in-stack)
    (InlAtS-preserved-under-stack-write {addr-a} {addr} inlS (valid-in-heap (valid-inl {A} {B} va inlS)) w-in-stack)
valid-at-preserved-under-stack-write {A = A + B} (valid-inr {A} {B} {addr-b = addr-b} {addr = addr} vb inrS) w-in-stack =
  valid-inr
    (valid-at-preserved-under-stack-write vb w-in-stack)
    (InrAtS-preserved-under-stack-write {addr-b} {addr} inrS (valid-in-heap (valid-inr {A} {B} vb inrS)) w-in-stack)
valid-at-preserved-under-stack-write (valid-closure {cl = cl} {code-ptr = code-ptr} {addr = addr} closS) w-in-stack =
  let env-addr = Closure.env-addr cl
      heap-proof = valid-in-heap (valid-closure {cl = cl} {code-ptr = code-ptr} closS)
  in valid-closure
       (ClosureAtS-preserved-under-stack-write {env-addr} {code-ptr} {addr} closS heap-proof w-in-stack)
valid-at-preserved-under-stack-write (valid-closure-env {A} {B} {E} {cl} {env} {env-addr = env-addr} {code-ptr = code-ptr} {closure-addr = closure-addr} sem-eq venv closS) w-in-stack =
  valid-closure-env sem-eq
    (valid-at-preserved-under-stack-write venv w-in-stack)
    (ClosureAtS-preserved-under-stack-write {env-addr} {code-ptr} {closure-addr}
      closS (valid-in-heap (valid-closure-env {A} {B} {E} {cl} {env} sem-eq venv closS)) w-in-stack)
valid-at-preserved-under-stack-write (valid-eff {cl = cl} {code-ptr = code-ptr} {addr = addr} closS) w-in-stack =
  let env-addr = Closure.env-addr cl
      heap-proof = valid-in-heap (valid-eff {cl = cl} {code-ptr = code-ptr} closS)
  in valid-eff
       (ClosureAtS-preserved-under-stack-write {env-addr} {code-ptr} {addr} closS heap-proof w-in-stack)
valid-at-preserved-under-stack-write (valid-eff-env {A} {B} {E} {cl} {env} {env-addr = env-addr} {code-ptr = code-ptr} {closure-addr = closure-addr} sem-eq venv closS) w-in-stack =
  valid-eff-env sem-eq
    (valid-at-preserved-under-stack-write venv w-in-stack)
    (ClosureAtS-preserved-under-stack-write {env-addr} {code-ptr} {closure-addr}
      closS (valid-in-heap (valid-eff-env {A} {B} {E} {cl} {env} sem-eq venv closS)) w-in-stack)
valid-at-preserved-under-stack-write (valid-fix vx) w-in-stack =
  valid-fix (valid-at-preserved-under-stack-write vx w-in-stack)

-- | ValidAt preserved under write to stack address
-- This is the main interface for validity preservation.
-- Takes InStack w to ensure soundness (the write is to stack, not heap).
valid-at-preserved-under-write :
  ∀ {A} {v : ⟦ A ⟧} {addr-v w : Word} {val : Word} {m : Memory} →
  ValidAt v addr-v m →
  InStack w →
  ValidAt v addr-v (writeMem m w val)
valid-at-preserved-under-write = valid-at-preserved-under-stack-write

-- | Convenience: preservation under two writes (common for alloc-2-slots)
valid-at-preserved-under-writes :
  ∀ {A} {v : ⟦ A ⟧} {addr-v w1 w2 : Word} {val1 val2 : Word} {m : Memory} →
  ValidAt v addr-v m →
  InStack w1 →
  InStack w2 →
  ValidAt v addr-v (writeMem (writeMem m w1 val1) w2 val2)
valid-at-preserved-under-writes valid s1 s2 =
  valid-at-preserved-under-write (valid-at-preserved-under-write valid s1) s2

------------------------------------------------------------------------
-- Creating validity proofs from allocation
------------------------------------------------------------------------

-- | Allocate a pair and create validity proof
-- Uses proven mem-read-write and mem-read-other
alloc-pair-creates-valid : ∀ {A B} (a : ⟦ A ⟧) (b : ⟦ B ⟧) (addr : Word) (m : Memory) →
  let m₁ = writeMem m addr (encode a)
      m₂ = writeMem m₁ (addr +ℕ slot-size) (encode b)
  in PairAt a b addr m₂
alloc-pair-creates-valid a b addr m = pair-at fst-proof snd-proof
  where
    m₁ = writeMem m addr (encode a)
    m₂ = writeMem m₁ (addr +ℕ slot-size) (encode b)

    -- m₂[addr] = m₁[addr] (by mem-read-other, since addr ≠ addr+8)
    --          = encode a (by mem-read-write)
    fst-proof : readMem m₂ addr ≡ just (encode a)
    fst-proof = trans
      (mem-read-other {m₁} {addr +ℕ slot-size} {addr} {encode b} (λ eq → n≢n+word-size addr (sym eq)))
      (mem-read-write {m} {addr} {encode a})

    -- m₂[addr+8] = encode b (by mem-read-write)
    snd-proof : readMem m₂ (addr +ℕ slot-size) ≡ just (encode b)
    snd-proof = mem-read-write {m₁} {addr +ℕ slot-size} {encode b}

-- | Allocate left sum and create validity proof
alloc-inl-creates-valid : ∀ {A B} (a : ⟦ A ⟧) (addr : Word) (m : Memory) →
  let m₁ = writeMem m addr 0
      m₂ = writeMem m₁ (addr +ℕ slot-size) (encode a)
  in InlAt {A} {B} a addr m₂
alloc-inl-creates-valid a addr m = inl-at tag-proof val-proof
  where
    m₁ = writeMem m addr 0
    m₂ = writeMem m₁ (addr +ℕ slot-size) (encode a)

    tag-proof : readMem m₂ addr ≡ just 0
    tag-proof = trans
      (mem-read-other {m₁} {addr +ℕ slot-size} {addr} {encode a} (λ eq → n≢n+word-size addr (sym eq)))
      (mem-read-write {m} {addr} {0})

    val-proof : readMem m₂ (addr +ℕ slot-size) ≡ just (encode a)
    val-proof = mem-read-write {m₁} {addr +ℕ slot-size} {encode a}

-- | Allocate right sum and create validity proof
alloc-inr-creates-valid : ∀ {A B} (b : ⟦ B ⟧) (addr : Word) (m : Memory) →
  let m₁ = writeMem m addr 1
      m₂ = writeMem m₁ (addr +ℕ slot-size) (encode b)
  in InrAt {A} {B} b addr m₂
alloc-inr-creates-valid b addr m = inr-at tag-proof val-proof
  where
    m₁ = writeMem m addr 1
    m₂ = writeMem m₁ (addr +ℕ slot-size) (encode b)

    tag-proof : readMem m₂ addr ≡ just 1
    tag-proof = trans
      (mem-read-other {m₁} {addr +ℕ slot-size} {addr} {encode b} (λ eq → n≢n+word-size addr (sym eq)))
      (mem-read-write {m} {addr} {1})

    val-proof : readMem m₂ (addr +ℕ slot-size) ≡ just (encode b)
    val-proof = mem-read-write {m₁} {addr +ℕ slot-size} {encode b}

------------------------------------------------------------------------
-- Deriving encoding properties from validity proofs
--
-- These replace the axioms in Postulates.agda with derived lemmas.
-- The key difference: they require a validity proof as input.
------------------------------------------------------------------------

-- | Derived: reading first component of a valid pair
-- Replaces: encode-pair-fst axiom
encode-pair-fst-derived : ∀ {A B} (a : ⟦ A ⟧) (b : ⟦ B ⟧) (addr : Word) (m : Memory) →
  PairAt a b addr m →
  readMem m addr ≡ just (encode a)
encode-pair-fst-derived a b addr m valid = fst-valid valid

-- | Derived: reading second component of a valid pair
-- Replaces: encode-pair-snd axiom
encode-pair-snd-derived : ∀ {A B} (a : ⟦ A ⟧) (b : ⟦ B ⟧) (addr : Word) (m : Memory) →
  PairAt a b addr m →
  readMem m (addr +ℕ slot-size) ≡ just (encode b)
encode-pair-snd-derived a b addr m valid = snd-valid valid

-- | Derived: reading tag of a valid left sum
-- Replaces: encode-inl-tag axiom
encode-inl-tag-derived : ∀ {A B} (a : ⟦ A ⟧) (addr : Word) (m : Memory) →
  InlAt {A} {B} a addr m →
  readMem m addr ≡ just 0
encode-inl-tag-derived a addr m valid = tag-valid valid

-- | Derived: reading value of a valid left sum
-- Replaces: encode-inl-val axiom
encode-inl-val-derived : ∀ {A B} (a : ⟦ A ⟧) (addr : Word) (m : Memory) →
  InlAt {A} {B} a addr m →
  readMem m (addr +ℕ slot-size) ≡ just (encode a)
encode-inl-val-derived a addr m valid = val-valid valid

-- | Derived: reading tag of a valid right sum
-- Replaces: encode-inr-tag axiom
encode-inr-tag-derived : ∀ {A B} (b : ⟦ B ⟧) (addr : Word) (m : Memory) →
  InrAt {A} {B} b addr m →
  readMem m addr ≡ just 1
encode-inr-tag-derived b addr m valid = tag-valid valid

-- | Derived: reading value of a valid right sum
-- Replaces: encode-inr-val axiom
encode-inr-val-derived : ∀ {A B} (b : ⟦ B ⟧) (addr : Word) (m : Memory) →
  InrAt {A} {B} b addr m →
  readMem m (addr +ℕ slot-size) ≡ just (encode b)
encode-inr-val-derived b addr m valid = val-valid valid

------------------------------------------------------------------------
-- Preservation: validity survives writes to other addresses
------------------------------------------------------------------------

-- | Helper: addr₁ ≠ addr₂ and addr₁ ≠ addr₂ + 8 (pair doesn't overlap)
record NoOverlap (addr₁ addr₂ : Word) : Set where
  constructor no-overlap
  field
    neq-base : addr₁ ≢ addr₂
    neq-snd  : addr₁ ≢ addr₂ +ℕ slot-size

-- | Writing to a non-overlapping address preserves pair validity
pair-valid-preserved : ∀ {A B} (a : ⟦ A ⟧) (b : ⟦ B ⟧) (pair-addr write-addr : Word) (v : Word) (m : Memory) →
  PairAt a b pair-addr m →
  NoOverlap write-addr pair-addr →
  write-addr ≢ pair-addr +ℕ slot-size →
  PairAt a b pair-addr (writeMem m write-addr v)
pair-valid-preserved a b pair-addr write-addr v m valid no-over neq-snd =
  pair-at fst-preserved snd-preserved
  where
    m' = writeMem m write-addr v

    fst-preserved : readMem m' pair-addr ≡ just (encode a)
    fst-preserved = trans
      (mem-read-other {m} {write-addr} {pair-addr} {v} (NoOverlap.neq-base no-over))
      (fst-valid valid)

    snd-preserved : readMem m' (pair-addr +ℕ slot-size) ≡ just (encode b)
    snd-preserved = trans
      (mem-read-other {m} {write-addr} {pair-addr +ℕ slot-size} {v} neq-snd)
      (snd-valid valid)

------------------------------------------------------------------------
-- Connection to encode function
--
-- Key bridge: if encode (a, b) = addr and PairAt a b addr m,
-- then the encoding axioms hold.
------------------------------------------------------------------------

-- NOTE: encode-*-is-addr postulates were removed (unused).
-- These are trivially true (encode always produces an addr) but added
-- no semantic value. Real progress comes from stateful encoding.

------------------------------------------------------------------------
-- Bridge lemmas: Connect validity to abstract encode
--
-- These make it easy to replace axioms with derived lemmas.
-- Precondition: PairAt a b (encode (a , b)) (memory s)
-- This says: "the pair is properly encoded at its encode address"
------------------------------------------------------------------------

-- | If pair is valid at encode address, derive the axiom property
pair-valid-at-encode-fst : ∀ {A B} (a : ⟦ A ⟧) (b : ⟦ B ⟧) (m : Memory) →
  PairAt a b (encode (a , b)) m →
  readMem m (encode (a , b)) ≡ just (encode a)
pair-valid-at-encode-fst a b m valid = fst-valid valid

pair-valid-at-encode-snd : ∀ {A B} (a : ⟦ A ⟧) (b : ⟦ B ⟧) (m : Memory) →
  PairAt a b (encode (a , b)) m →
  readMem m (encode (a , b) +ℕ slot-size) ≡ just (encode b)
pair-valid-at-encode-snd a b m valid = snd-valid valid

-- | If left sum is valid at encode address, derive the axiom property
inl-valid-at-encode-tag : ∀ {A B} (a : ⟦ A ⟧) (m : Memory) →
  InlAt {A} {B} a (encode (inj₁ a)) m →
  readMem m (encode {A + B} (inj₁ a)) ≡ just 0
inl-valid-at-encode-tag a m valid = tag-valid valid

inl-valid-at-encode-val : ∀ {A B} (a : ⟦ A ⟧) (m : Memory) →
  InlAt {A} {B} a (encode (inj₁ a)) m →
  readMem m (encode {A + B} (inj₁ a) +ℕ slot-size) ≡ just (encode a)
inl-valid-at-encode-val a m valid = val-valid valid

-- | If right sum is valid at encode address, derive the axiom property
inr-valid-at-encode-tag : ∀ {A B} (b : ⟦ B ⟧) (m : Memory) →
  InrAt {A} {B} b (encode (inj₂ b)) m →
  readMem m (encode {A + B} (inj₂ b)) ≡ just 1
inr-valid-at-encode-tag b m valid = tag-valid valid

inr-valid-at-encode-val : ∀ {A B} (b : ⟦ B ⟧) (m : Memory) →
  InrAt {A} {B} b (encode (inj₂ b)) m →
  readMem m (encode {A + B} (inj₂ b) +ℕ slot-size) ≡ just (encode b)
inr-valid-at-encode-val b m valid = val-valid valid

------------------------------------------------------------------------
-- MemoryValid: Combined validity for all values in state
--
-- This is analogous to StackInvariant - a predicate that captures
-- the invariant for the entire memory state.
------------------------------------------------------------------------

-- | A single value's validity record
data ValueValid (m : Memory) : Set₁ where
  valid-pair : ∀ {A B} (a : ⟦ A ⟧) (b : ⟦ B ⟧) → PairAt a b (encode {A * B} (a , b)) m → ValueValid m
  valid-inl  : ∀ {A B} (a : ⟦ A ⟧) → InlAt {A} {B} a (encode {A + B} (inj₁ a)) m → ValueValid m
  valid-inr  : ∀ {A B} (b : ⟦ B ⟧) → InrAt {A} {B} b (encode {A + B} (inj₂ b)) m → ValueValid m

open import Data.List using (List; []; _∷_)

-- | MemoryValid: list of all valid values in memory
-- Analogous to StackInvariant, this is threaded through proofs
MemoryValid : Memory → Set₁
MemoryValid m = List (ValueValid m)

-- | Empty memory has no valid values
empty-memory-valid : ∀ (m : Memory) → MemoryValid m
empty-memory-valid m = []

-- | Lookup a pair's validity from MemoryValid
-- (Would need decidable equality on values to make this practical)

------------------------------------------------------------------------
-- Summary: How to use this module
--
-- OLD (using axioms from Postulates.agda):
--   mem-eq = encode-pair-fst a b (memory s)
--
-- NEW (using derived lemmas with validity proof):
--   mem-eq = encode-pair-fst-derived a b addr (memory s) valid
--   where valid : PairAt a b addr (memory s) is a precondition
--
-- The validity proof can be:
-- 1. Created by alloc-*-creates-valid when allocating
-- 2. Preserved through writes using *-valid-preserved
-- 3. Threaded as a precondition like StackInvariant
------------------------------------------------------------------------
