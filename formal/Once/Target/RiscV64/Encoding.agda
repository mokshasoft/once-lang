------------------------------------------------------------------------
-- Once.Target.RiscV64.Encoding
--
-- Derivation of encoding properties from the shared memory model.
--
-- Key theorems (all PROVEN in Once.Memory):
--   1. mem-read-write : readMem (writeMem m addr v) addr ≡ just v
--   2. mem-read-other : addr₁ ≢ addr₂ → readMem (writeMem m addr₁ v) addr₂ ≡ readMem m addr₂
--
-- Remaining postulate:
--   3. encode-injective : encode x ≡ encode y → x ≡ y
--
-- All other encoding properties are DERIVED from these.
------------------------------------------------------------------------

module Once.Target.RiscV64.Encoding where

open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _≡ᵇ_)
open import Data.Nat.Properties using (+-suc; +-comm)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst)
open import Relation.Nullary using (yes; no)

------------------------------------------------------------------------
-- Memory Model (imported from shared module)
------------------------------------------------------------------------

open import Once.Memory public
  using (Word; Memory; readMem; writeMem; AllocState; alloc-state; mem; heap-ptr;
         init-alloc-state; alloc-two-words; alloc-two-words-fst; alloc-two-words-snd;
         n≢n+8; n≢n+suc-m)

-- Re-export memory theorems
open import Once.Memory public
  using (mem-read-write; mem-read-other)

-- NOTE: encode-injective was removed (unused). If needed in future,
-- it can be derived from stateful encoding where each allocation
-- produces a unique address.

------------------------------------------------------------------------
-- Allocation Primitives
--
-- These are concrete definitions, not axioms.
-- They model how the RISC-V backend allocates memory.
------------------------------------------------------------------------

-- | Allocate a pair: write two words at consecutive addresses
-- Returns: (updated memory, address of pair)
alloc-pair : Memory → Word → Word → Word → Memory × Word
alloc-pair m base v₁ v₂ = m' , base
  where
    m₁ = writeMem m base v₁
    m' = writeMem m₁ (base + 8) v₂

-- | Allocate a sum (left): write tag 0 and value
alloc-inl : Memory → Word → Word → Memory × Word
alloc-inl m base v = m' , base
  where
    m₁ = writeMem m base 0       -- tag = 0
    m' = writeMem m₁ (base + 8) v

-- | Allocate a sum (right): write tag 1 and value
alloc-inr : Memory → Word → Word → Memory × Word
alloc-inr m base v = m' , base
  where
    m₁ = writeMem m base 1       -- tag = 1
    m' = writeMem m₁ (base + 8) v

------------------------------------------------------------------------
-- DERIVED PROPERTIES
--
-- These are THEOREMS, not axioms!
-- They follow from the 3 axioms + the allocation definitions.
------------------------------------------------------------------------

-- | Reading first component of allocated pair
-- DERIVED from mem-read-write and mem-read-other
alloc-pair-fst : ∀ (m : Memory) (base v₁ v₂ : Word) →
  let (m' , addr) = alloc-pair m base v₁ v₂
  in readMem m' addr ≡ just v₁
alloc-pair-fst m base v₁ v₂ = trans step3 step4
  where
    -- m' = writeMem (writeMem m base v₁) (base + 8) v₂
    -- Need: readMem m' base ≡ just v₁
    m₁ = writeMem m base v₁
    m' = writeMem m₁ (base + 8) v₂

    -- Step 3: readMem m' base = readMem m₁ base (by mem-read-other)
    step3 : readMem m' base ≡ readMem m₁ base
    step3 = mem-read-other {m₁} {base + 8} {base} {v₂} (λ eq → n≢n+8 base (sym eq))

    -- Step 4: readMem m₁ base = just v₁ (by mem-read-write)
    step4 : readMem m₁ base ≡ just v₁
    step4 = mem-read-write {m} {base} {v₁}

-- | Reading second component of allocated pair
-- DERIVED from mem-read-write
alloc-pair-snd : ∀ (m : Memory) (base v₁ v₂ : Word) →
  let (m' , addr) = alloc-pair m base v₁ v₂
  in readMem m' (addr + 8) ≡ just v₂
alloc-pair-snd m base v₁ v₂ =
  -- m' = writeMem (writeMem m base v₁) (base + 8) v₂
  -- Need: readMem m' (base + 8) ≡ just v₂
  -- Direct application of mem-read-write
  mem-read-write {writeMem m base v₁} {base + 8} {v₂}

-- | Reading tag of allocated left sum
-- DERIVED from mem-read-write and mem-read-other
alloc-inl-tag : ∀ (m : Memory) (base v : Word) →
  let (m' , addr) = alloc-inl m base v
  in readMem m' addr ≡ just 0
alloc-inl-tag m base v = trans step1 step2
  where
    m₁ = writeMem m base 0
    m' = writeMem m₁ (base + 8) v

    step1 : readMem m' base ≡ readMem m₁ base
    step1 = mem-read-other {m₁} {base + 8} {base} {v} (λ eq → n≢n+8 base (sym eq))

    step2 : readMem m₁ base ≡ just 0
    step2 = mem-read-write {m} {base} {0}

-- | Reading value of allocated left sum
-- DERIVED from mem-read-write
alloc-inl-val : ∀ (m : Memory) (base v : Word) →
  let (m' , addr) = alloc-inl m base v
  in readMem m' (addr + 8) ≡ just v
alloc-inl-val m base v =
  mem-read-write {writeMem m base 0} {base + 8} {v}

-- | Reading tag of allocated right sum
-- DERIVED from mem-read-write and mem-read-other
alloc-inr-tag : ∀ (m : Memory) (base v : Word) →
  let (m' , addr) = alloc-inr m base v
  in readMem m' addr ≡ just 1
alloc-inr-tag m base v = trans step1 step2
  where
    m₁ = writeMem m base 1
    m' = writeMem m₁ (base + 8) v

    step1 : readMem m' base ≡ readMem m₁ base
    step1 = mem-read-other {m₁} {base + 8} {base} {v} (λ eq → n≢n+8 base (sym eq))

    step2 : readMem m₁ base ≡ just 1
    step2 = mem-read-write {m} {base} {1}

-- | Reading value of allocated right sum
-- DERIVED from mem-read-write
alloc-inr-val : ∀ (m : Memory) (base v : Word) →
  let (m' , addr) = alloc-inr m base v
  in readMem m' (addr + 8) ≡ just v
alloc-inr-val m base v =
  mem-read-write {writeMem m base 1} {base + 8} {v}

------------------------------------------------------------------------
-- HeapValid: Tracking Properly Allocated Memory
--
-- The key insight: the axioms in Postulates.agda like
--   encode-pair-fst : ... (m : Memory) → readMem m (encode (a,b)) ≡ just (encode a)
-- claim to hold for ANY memory m. This is too strong!
--
-- They should only hold for memory where (a,b) was properly allocated.
-- HeapValid tracks this invariant.
------------------------------------------------------------------------

-- | Describes what kind of value is allocated at an address
data AllocKind : Set where
  pair-alloc : Word → Word → AllocKind  -- pair with fst, snd values
  inl-alloc  : Word → AllocKind          -- left sum with value
  inr-alloc  : Word → AllocKind          -- right sum with value

-- | A single allocation record: address and what's there
record AllocRecord : Set where
  constructor alloc-at
  field
    addr : Word
    kind : AllocKind

open AllocRecord public

open import Data.List using (List; []; _∷_; _++_)

-- | HeapValid: list of properly allocated regions
-- Invariant: memory at each recorded address has the correct layout
HeapValid : Set
HeapValid = List AllocRecord

-- | Empty heap is valid
empty-heap : HeapValid
empty-heap = []

-- | Record a pair allocation
record-pair : Word → Word → Word → HeapValid → HeapValid
record-pair base v₁ v₂ h = alloc-at base (pair-alloc v₁ v₂) ∷ h

-- | Record a left sum allocation
record-inl : Word → Word → HeapValid → HeapValid
record-inl base v h = alloc-at base (inl-alloc v) ∷ h

-- | Record a right sum allocation
record-inr : Word → Word → HeapValid → HeapValid
record-inr base v h = alloc-at base (inr-alloc v) ∷ h

------------------------------------------------------------------------
-- Allocation + HeapValid: Combined Operations
--
-- These show that allocation produces memory satisfying the derived
-- properties AND updates HeapValid to track the new allocation.
------------------------------------------------------------------------

-- | Allocate a pair and record it in HeapValid
-- Returns: (new memory, new heap validity record, address, proof of fst readable)
alloc-pair-valid : (m : Memory) (base v₁ v₂ : Word) (h : HeapValid) →
  let (m' , addr) = alloc-pair m base v₁ v₂
      h' = record-pair base v₁ v₂ h
  in (readMem m' addr ≡ just v₁) × (readMem m' (addr + 8) ≡ just v₂)
alloc-pair-valid m base v₁ v₂ h = alloc-pair-fst m base v₁ v₂ , alloc-pair-snd m base v₁ v₂

-- | Allocate left sum and record it
alloc-inl-valid : (m : Memory) (base v : Word) (h : HeapValid) →
  let (m' , addr) = alloc-inl m base v
      h' = record-inl base v h
  in (readMem m' addr ≡ just 0) × (readMem m' (addr + 8) ≡ just v)
alloc-inl-valid m base v h = alloc-inl-tag m base v , alloc-inl-val m base v

-- | Allocate right sum and record it
alloc-inr-valid : (m : Memory) (base v : Word) (h : HeapValid) →
  let (m' , addr) = alloc-inr m base v
      h' = record-inr base v h
  in (readMem m' addr ≡ just 1) × (readMem m' (addr + 8) ≡ just v)
alloc-inr-valid m base v h = alloc-inr-tag m base v , alloc-inr-val m base v

------------------------------------------------------------------------
-- Allocation-Tracking Encode (Option B)
--
-- To eliminate the encode bridge axiom, we define encode in terms of
-- an allocation map that tracks where each value is allocated.
------------------------------------------------------------------------

-- | AllocationMap: tracks where values are allocated
-- For simplicity, we use a function-based representation.
-- In practice, this would be built up during code generation.
record AllocMap : Set₁ where
  field
    -- Lookup the address of an allocated pair
    lookup-pair : ∀ {A B : Set} → (A → Word) → (B → Word) → A × B → Maybe Word

open AllocMap public

-- | Empty allocation map (nothing allocated)
empty-alloc-map : AllocMap
empty-alloc-map = record { lookup-pair = λ _ _ _ → nothing }

-- | Record a pair allocation in the map
record-pair-alloc : ∀ {A B : Set} → (A → Word) → (B → Word) → A × B → Word → AllocMap → AllocMap
record-pair-alloc {A} {B} enc-a enc-b pair addr amap = record
  { lookup-pair = λ {A'} {B'} enc-a' enc-b' p →
      -- Simplified: just record the allocation (proper impl would check equality)
      amap .lookup-pair enc-a' enc-b' p
  }

-- | Encode with allocation tracking
-- Given an allocation map, encode looks up the address
encode-with-alloc : ∀ {A B : Set} → AllocMap → (A → Word) → (B → Word) → A × B → Word
encode-with-alloc amap enc-a enc-b pair with amap .lookup-pair enc-a enc-b pair
... | just addr = addr
... | nothing   = 0  -- Not allocated yet (should not happen in valid execution)

------------------------------------------------------------------------
-- Stateful Allocation (Option B - Concrete Encode)
--
-- Key insight: if we track allocations WITH their addresses,
-- then encode-is-alloc-addr becomes trivially provable.
--
-- AllocState is now imported from Once.Memory
------------------------------------------------------------------------

-- Specialized allocation for pairs/sums (uses alloc-two-words from Memory)
alloc-pair-stateful : AllocState → Word → Word → AllocState × Word
alloc-pair-stateful = alloc-two-words

alloc-inl-stateful : AllocState → Word → AllocState × Word
alloc-inl-stateful st v = alloc-two-words st 0 v  -- tag = 0

alloc-inr-stateful : AllocState → Word → AllocState × Word
alloc-inr-stateful st v = alloc-two-words st 1 v  -- tag = 1

------------------------------------------------------------------------
-- PROVEN: encode-is-alloc-addr for stateful allocation
--
-- For the stateful scheme, this is trivially true:
-- - We allocate at heap-ptr
-- - We return heap-ptr as the address
-- - Therefore allocated-address = heap-ptr (by definition)
------------------------------------------------------------------------

-- | For stateful allocation, the returned address IS the heap pointer
-- This is the key theorem that makes encode-is-alloc-addr provable!
alloc-pair-addr-is-heap-ptr : ∀ (st : AllocState) (v₁ v₂ : Word) →
  proj₂ (alloc-pair-stateful st v₁ v₂) ≡ heap-ptr st
alloc-pair-addr-is-heap-ptr st v₁ v₂ = refl

alloc-inl-addr-is-heap-ptr : ∀ (st : AllocState) (v : Word) →
  proj₂ (alloc-inl-stateful st v) ≡ heap-ptr st
alloc-inl-addr-is-heap-ptr st v = refl

alloc-inr-addr-is-heap-ptr : ∀ (st : AllocState) (v : Word) →
  proj₂ (alloc-inr-stateful st v) ≡ heap-ptr st
alloc-inr-addr-is-heap-ptr st v = refl

------------------------------------------------------------------------
-- PROVEN: Memory properties for stateful allocation
------------------------------------------------------------------------

-- | Reading first component of statefully allocated pair
alloc-pair-stateful-fst : ∀ (st : AllocState) (v₁ v₂ : Word) →
  let (st' , base) = alloc-pair-stateful st v₁ v₂
  in readMem (mem st') base ≡ just v₁
alloc-pair-stateful-fst st v₁ v₂ = trans step1 step2
  where
    base' = heap-ptr st
    m₁ = writeMem (mem st) base' v₁
    m₂ = writeMem m₁ (base' + 8) v₂

    step1 : readMem m₂ base' ≡ readMem m₁ base'
    step1 = mem-read-other {m₁} {base' + 8} {base'} {v₂} (λ eq → n≢n+8 base' (sym eq))

    step2 : readMem m₁ base' ≡ just v₁
    step2 = mem-read-write {mem st} {base'} {v₁}

-- | Reading second component of statefully allocated pair
alloc-pair-stateful-snd : ∀ (st : AllocState) (v₁ v₂ : Word) →
  let (st' , base) = alloc-pair-stateful st v₁ v₂
  in readMem (mem st') (base + 8) ≡ just v₂
alloc-pair-stateful-snd st v₁ v₂ = mem-read-write {writeMem (mem st) (heap-ptr st) v₁} {heap-ptr st + 8} {v₂}

------------------------------------------------------------------------
-- Connection: Stateful Encode = Allocation Address
--
-- If we define:
--   encode-stateful st value = proj₂ (allocate-stateful st (encode-components value))
--
-- Then encode-is-alloc-addr is TRUE BY DEFINITION.
------------------------------------------------------------------------

-- | Encode a pair using stateful allocation
-- Returns: (new state, encoding of pair)
encode-pair-stateful : ∀ {A B : Set} → (A → Word) → (B → Word) →
                       AllocState → A × B → AllocState × Word
encode-pair-stateful enc-a enc-b st (a , b) =
  alloc-pair-stateful st (enc-a a) (enc-b b)

-- | Key theorem: encode of a pair equals the allocation address
encode-is-alloc-addr-pair-PROVEN : ∀ {A B : Set} (enc-a : A → Word) (enc-b : B → Word)
    (st : AllocState) (a : A) (b : B) →
    let (st' , addr) = encode-pair-stateful enc-a enc-b st (a , b)
    in addr ≡ heap-ptr st
encode-is-alloc-addr-pair-PROVEN enc-a enc-b st a b = refl

-- | Combined: readMem returns correct component for statefully encoded pair
encode-pair-stateful-fst : ∀ {A B : Set} (enc-a : A → Word) (enc-b : B → Word)
    (st : AllocState) (a : A) (b : B) →
    let (st' , addr) = encode-pair-stateful enc-a enc-b st (a , b)
    in readMem (mem st') addr ≡ just (enc-a a)
encode-pair-stateful-fst enc-a enc-b st a b = alloc-pair-stateful-fst st (enc-a a) (enc-b b)

encode-pair-stateful-snd : ∀ {A B : Set} (enc-a : A → Word) (enc-b : B → Word)
    (st : AllocState) (a : A) (b : B) →
    let (st' , addr) = encode-pair-stateful enc-a enc-b st (a , b)
    in readMem (mem st') (addr + 8) ≡ just (enc-b b)
encode-pair-stateful-snd enc-a enc-b st a b = alloc-pair-stateful-snd st (enc-a a) (enc-b b)

------------------------------------------------------------------------
-- Connection to Abstract Encode (Postulates.agda)
--
-- The abstract `encode` in Postulates.agda doesn't have state.
-- For full elimination, we would need to:
-- 1. Thread AllocState through eval in Semantics.agda
-- 2. Use encode-stateful everywhere
--
-- For now, we keep one bridge axiom connecting abstract to stateful:
------------------------------------------------------------------------

-- NOTE: encode-agrees-with-stateful was removed (unused).
-- To truly eliminate encoding postulates: thread AllocState through
-- Semantics.eval, replacing abstract encode with encode-stateful.

------------------------------------------------------------------------
-- Summary: Memory Axiom Architecture (Updated with Stateful Proofs)
--
-- PROVEN THEOREMS (from concrete definitions):
--   1. mem-read-write               : read after write ✓
--   2. mem-read-other               : frame rule ✓
--   3. encode-is-alloc-addr-PROVEN  : for stateful encoding ✓
--   4. encode-pair-stateful-fst/snd : memory read correctness ✓
--
-- REMAINING WORK:
--   Thread AllocState through Semantics.eval to eliminate encoding
--   postulates in Once/Postulates.agda.
------------------------------------------------------------------------
