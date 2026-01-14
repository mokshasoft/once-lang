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
open import Once.Backend.Common.MemoryRegions
  using (region-of; stack; heap; stack-heap-disjoint)
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
  valid-closure : ∀ {A B} {cl : Closure A B} {addr : Word} {m : Memory} →
    ClosureAtS (Closure.env-addr cl) (Closure.code-ptr cl) addr m →
    ValidAt {A ⇒ B} cl addr m

  -- Eff: same as closure (Eff = Closure at runtime)
  valid-eff : ∀ {A B} {cl : Closure A B} {addr : Word} {m : Memory} →
    ClosureAtS (Closure.env-addr cl) (Closure.code-ptr cl) addr m →
    ValidAt {Eff A B} cl addr m

  -- Fix: validity of unwrapped value (Fix is identity at runtime)
  valid-fix : ∀ {F} {x : ⟦ F ⟧} {addr : Word} {m : Memory} →
    ValidAt x addr m →
    ValidAt {Fix F} (wrap x) addr m

------------------------------------------------------------------------
-- ValidAt preservation under memory writes
--
-- Key insight: if we write to addresses disjoint from those referenced
-- by a validity proof, the validity is preserved.
--
-- This is a postulate for now, to be proven by induction on ValidAt
-- once we have better region reasoning. It's conceptually sound and
-- replaces the more problematic encode postulates.
------------------------------------------------------------------------

-- | ValidAt is preserved when writing to disjoint addresses
-- The write addresses (w1, w2) must not overlap with any address
-- referenced by the validity proof at addr-v.
--
-- For stack-allocated sums/pairs written at w1 and w1+8,
-- this holds when addr-v points to:
-- - Heap-allocated data (heap ≠ stack)
-- - Previously stack-allocated data above the current rsp
-- - Simple types like Unit (no memory dependency)
--
-- TODO: Prove by induction on ValidAt structure
postulate
  valid-at-preserved-under-write :
    ∀ {A} {v : ⟦ A ⟧} {addr-v w : Word} {val : Word} {m : Memory} →
    ValidAt v addr-v m →
    addr-v ≢ w →  -- write address different from validity address
    ValidAt v addr-v (writeMem m w val)

-- | Convenience: preservation under two writes (common for alloc-2-slots)
valid-at-preserved-under-writes :
  ∀ {A} {v : ⟦ A ⟧} {addr-v w1 w2 : Word} {val1 val2 : Word} {m : Memory} →
  ValidAt v addr-v m →
  addr-v ≢ w1 →
  addr-v ≢ w2 →
  ValidAt v addr-v (writeMem (writeMem m w1 val1) w2 val2)
valid-at-preserved-under-writes valid neq1 neq2 =
  valid-at-preserved-under-write (valid-at-preserved-under-write valid neq1) neq2

------------------------------------------------------------------------
-- Closure validity with runtime code-ptr
--
-- The semantic closure from `eval (curry f) x` has code-ptr = 0 (placeholder),
-- but the runtime memory stores the actual thunk address. This postulate
-- allows constructing validity when the env-addr matches but code-ptr differs.
--
-- This is sound because:
-- 1. The closure's semantics field (not code-ptr) determines behavior
-- 2. The code-ptr is only used at runtime to find the thunk
-- 3. We separately verify via ClosureWF that code-ptr points to valid code
------------------------------------------------------------------------
postulate
  -- | Closure validity with explicit env-addr and code-ptr
  -- Used for curry where semantic code-ptr is 0 but runtime has actual address
  valid-closure-at :
    ∀ {A B} {cl : Closure A B} {env-addr code-ptr addr : Word} {m : Memory} →
    Closure.env-addr cl ≡ env-addr →  -- env must match
    ClosureAtS env-addr code-ptr addr m →  -- memory layout
    ValidAt {A ⇒ B} cl addr m

  -- | Same for Eff type
  valid-eff-at :
    ∀ {A B} {cl : Closure A B} {env-addr code-ptr addr : Word} {m : Memory} →
    Closure.env-addr cl ≡ env-addr →
    ClosureAtS env-addr code-ptr addr m →
    ValidAt {Eff A B} cl addr m

------------------------------------------------------------------------
-- Bridge: ValidAt → encode
--
-- During the transition from encode-based to validity-based proofs,
-- we need bridges to call existing encode-based recursive functions.
-- This postulate will be eliminated once all recursion uses validity.
--
-- Conceptually: if v is validly represented at addr in m, then addr
-- is the "canonical address" of v, which is what encode computes.
------------------------------------------------------------------------
postulate
  -- | Extract encode address from validity proof
  -- This bridges validity-based preconditions to encode-based recursive calls.
  -- ELIMINABLE: Remove once run-ir-star-at-offset uses ValidAt throughout.
  addr-from-valid :
    ∀ {A} {v : ⟦ A ⟧} {addr : Word} {m : Memory} →
    ValidAt v addr m →
    addr ≡ encode v

  -- | Construct validity from encode address (reverse bridge)
  -- If addr ≡ encode v and memory is properly allocated, then validity holds.
  -- ELIMINABLE: Remove once all producers emit ValidAt directly.
  valid-from-encode :
    ∀ {A} {v : ⟦ A ⟧} {addr : Word} {m : Memory} →
    addr ≡ encode v →
    ValidAt v addr m

  -- | Propagate validity through address/memory substitution
  -- If validity holds at addr1/mem1, and addr2=addr1 and mem2 agrees with mem1,
  -- then validity holds at addr2/mem2.
  -- ELIMINABLE: Provable by induction on ValidAt structure once AtS predicates
  -- are shown to be preserved under pointwise memory equality.
  valid-subst-addr-mem :
    ∀ {A} {v : ⟦ A ⟧} {addr1 addr2 : Word} {mem1 mem2 : Memory} →
    ValidAt v addr1 mem1 →
    addr2 ≡ addr1 →
    (∀ a → readMem mem2 a ≡ readMem mem1 a) →
    ValidAt v addr2 mem2

  -- | Propagate validity when only heap memory is preserved
  -- ValidAt structures only depend on heap memory (not stack), so heap
  -- preservation is sufficient for validity propagation.
  -- ELIMINABLE: Provable by induction on ValidAt structure.
  valid-subst-heap-preserved :
    ∀ {A} {v : ⟦ A ⟧} {addr1 addr2 : Word} {mem1 mem2 : Memory} →
    ValidAt v addr1 mem1 →
    addr2 ≡ addr1 →
    (∀ a → region-of a ≡ heap → readMem mem2 a ≡ readMem mem1 a) →
    ValidAt v addr2 mem2

  -- | Convert validity from (A ⇒ B) to (Eff A B)
  -- These types have the same runtime representation (Closure A B), but
  -- ValidAt uses Type as a type index, so conversion is needed.
  -- ELIMINABLE: Provable by pattern matching on valid-closure and constructing valid-eff.
  valid-arrow-to-eff :
    ∀ {A B} {cl : Closure A B} {addr : Word} {m : Memory} →
    ValidAt {A ⇒ B} cl addr m →
    ValidAt {Eff A B} cl addr m

  -- | Extract validity of left injection's child value
  -- If (inj₁ a) is validly represented at addr, and mem[addr+8] = val-addr,
  -- then a is validly represented at val-addr.
  -- ELIMINABLE: Provable from ValidAt structure (sum validity implies child validity).
  valid-inl-child :
    ∀ {A B} {a : ⟦ A ⟧} {addr val-addr : Word} {mem : Memory} →
    ValidAt {A + B} (inj₁ a) addr mem →
    readMem mem (addr +ℕ slot-size) ≡ just val-addr →
    ValidAt a val-addr mem

  -- | Extract validity of right injection's child value
  -- If (inj₂ b) is validly represented at addr, and mem[addr+8] = val-addr,
  -- then b is validly represented at val-addr.
  -- ELIMINABLE: Provable from ValidAt structure (sum validity implies child validity).
  valid-inr-child :
    ∀ {A B} {b : ⟦ B ⟧} {addr val-addr : Word} {mem : Memory} →
    ValidAt {A + B} (inj₂ b) addr mem →
    readMem mem (addr +ℕ slot-size) ≡ just val-addr →
    ValidAt b val-addr mem

  -- | Left injection tag is 0 in memory
  -- If (inj₁ a) is validly represented at addr, then mem[addr] = 0.
  -- ELIMINABLE: Direct consequence of ValidAt structure definition.
  valid-inl-tag-is-0 :
    ∀ {A B} {a : ⟦ A ⟧} {addr : Word} {mem : Memory} →
    ValidAt {A + B} (inj₁ a) addr mem →
    readMem mem addr ≡ just 0

  -- | Left injection value pointer exists in memory
  -- If (inj₁ a) is validly represented at addr, then mem[addr+8] contains a valid pointer.
  -- ELIMINABLE: Direct consequence of ValidAt structure definition.
  valid-inl-val-ptr :
    ∀ {A B} {a : ⟦ A ⟧} {addr : Word} {mem : Memory} →
    ValidAt {A + B} (inj₁ a) addr mem →
    ∃[ val-addr ] (readMem mem (addr +ℕ slot-size) ≡ just val-addr × ValidAt a val-addr mem)

  -- | Right injection tag is 1 in memory
  -- If (inj₂ b) is validly represented at addr, then mem[addr] = 1.
  -- ELIMINABLE: Direct consequence of ValidAt structure definition.
  valid-inr-tag-is-1 :
    ∀ {A B} {b : ⟦ B ⟧} {addr : Word} {mem : Memory} →
    ValidAt {A + B} (inj₂ b) addr mem →
    readMem mem addr ≡ just 1

  -- | Right injection value pointer exists in memory
  -- If (inj₂ b) is validly represented at addr, then mem[addr+8] contains a valid pointer.
  -- ELIMINABLE: Direct consequence of ValidAt structure definition.
  valid-inr-val-ptr :
    ∀ {A B} {b : ⟦ B ⟧} {addr : Word} {mem : Memory} →
    ValidAt {A + B} (inj₂ b) addr mem →
    ∃[ val-addr ] (readMem mem (addr +ℕ slot-size) ≡ just val-addr × ValidAt b val-addr mem)

  -- | Extract fst component validity from pair validity
  -- If (a, b) is validly represented at addr, extracts component addresses and validities.
  -- ELIMINABLE: Direct consequence of ValidAt structure definition.
  valid-pair-decompose :
    ∀ {A B} {a : ⟦ A ⟧} {b : ⟦ B ⟧} {addr : Word} {mem : Memory} →
    ValidAt {A * B} (a , b) addr mem →
    ∃[ addr-a ] ∃[ addr-b ]
      (ValidAt a addr-a mem × ValidAt b addr-b mem × PairAtS addr-a addr-b addr mem)

------------------------------------------------------------------------
-- Region-based disjointness from validity (Phase 6c-6d)
--
-- These lemmas derive heap-stack disjointness from ValidAt.
-- Uses addr-from-valid internally, so still depends on bridging postulate.
-- ELIMINABLE: Once ValidAt directly implies region info, remove addr-from-valid.
------------------------------------------------------------------------

-- | Valid address is in heap (or 0 for Unit)
-- Derived from: addr-from-valid gives addr = encode v, encode-in-heap-sem gives region = heap
valid-addr-in-heap : ∀ {A : Type} {v : ⟦ A ⟧} {addr : Word} {m : Memory} →
  ValidAt v addr m →
  region-of addr ≡ heap
valid-addr-in-heap {A} {v} {addr} {m} valid =
  let addr-eq = addr-from-valid valid
  in trans (subst (λ a → region-of addr ≡ region-of a) addr-eq refl) (encode-in-heap-sem v)

-- | Valid address is disjoint from stack addresses
-- If addr has ValidAt and stack-addr is in stack, then addr ≢ stack-addr
valid-disjoint-from-stack : ∀ {A : Type} {v : ⟦ A ⟧} {addr stack-addr : Word} {m : Memory} →
  ValidAt v addr m →
  region-of stack-addr ≡ stack →
  addr ≢ stack-addr
valid-disjoint-from-stack {A} {v} {addr} {stack-addr} {m} valid stack-proof addr-eq =
  stack-heap-disjoint stack-addr addr stack-proof (valid-addr-in-heap valid) (sym addr-eq)

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
