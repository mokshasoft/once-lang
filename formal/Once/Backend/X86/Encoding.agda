------------------------------------------------------------------------
-- Once.Backend.X86.Encoding
--
-- Derivation of encoding properties from 3 fundamental axioms.
--
-- The 3-Axiom Foundation:
--   1. mem-read-write : readMem (writeMem m addr v) addr ≡ just v
--   2. mem-read-other : addr₁ ≢ addr₂ → readMem (writeMem m addr₁ v) addr₂ ≡ readMem m addr₂
--   3. encode-injective : encode x ≡ encode y → x ≡ y
--
-- All other encoding properties are DERIVED from these 3 axioms.
------------------------------------------------------------------------

module Once.Backend.X86.Encoding where

open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _≡ᵇ_)
open import Data.Nat.Properties using (+-suc; +-comm)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong)
open import Relation.Nullary using (yes; no)

------------------------------------------------------------------------
-- Memory Model (same as Semantics.agda)
------------------------------------------------------------------------

Word : Set
Word = ℕ

Memory : Set
Memory = Word → Maybe Word

readMem : Memory → Word → Maybe Word
readMem m addr = m addr

writeMem : Memory → Word → Word → Memory
writeMem m addr val = λ a → if a ≡ᵇ addr then just val else m a

------------------------------------------------------------------------
-- Helper: n ≢ n + 8
------------------------------------------------------------------------

-- n + suc m ≡ suc (n + m), so n = n + suc m would require n = suc (n + m)
-- But n cannot equal suc of anything larger than n - 1
n≢n+suc-m : ∀ (n m : ℕ) → n ≢ n + suc m
n≢n+suc-m zero m ()      -- 0 ≢ suc m
n≢n+suc-m (suc n) m eq = n≢n+suc-m n m (suc-injective eq)
  where
    suc-injective : ∀ {a b : ℕ} → suc a ≡ suc b → a ≡ b
    suc-injective refl = refl

n≢n+8 : ∀ (n : ℕ) → n ≢ n + 8
n≢n+8 n = n≢n+suc-m n 7

------------------------------------------------------------------------
-- THE 3 FUNDAMENTAL AXIOMS
------------------------------------------------------------------------

postulate
  -- Axiom 1: Read after write (same address)
  mem-read-write : ∀ {m : Memory} {addr v : Word} →
    readMem (writeMem m addr v) addr ≡ just v

  -- Axiom 2: Frame rule (different address)
  mem-read-other : ∀ {m : Memory} {addr₁ addr₂ v : Word} →
    addr₁ ≢ addr₂ →
    readMem (writeMem m addr₁ v) addr₂ ≡ readMem m addr₂

  -- Axiom 3: Encoding is injective
  encode-injective : ∀ {A : Set} {x y : A} {encode : A → Word} →
    encode x ≡ encode y → x ≡ y

------------------------------------------------------------------------
-- Allocation Primitives
--
-- These are concrete definitions, not axioms.
-- They model how the x86 backend allocates memory.
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
-- Summary: The 3-Axiom Architecture
--
-- AXIOMS (trusted base):
--   1. mem-read-write
--   2. mem-read-other
--   3. encode-injective
--
-- DERIVED (theorems):
--   - alloc-pair-fst    : from mem-read-write + mem-read-other
--   - alloc-pair-snd    : from mem-read-write
--   - alloc-inl-tag     : from mem-read-write + mem-read-other
--   - alloc-inl-val     : from mem-read-write
--   - alloc-inr-tag     : from mem-read-write + mem-read-other
--   - alloc-inr-val     : from mem-read-write
--
-- The current encode-pair-fst, encode-inl-tag, etc. axioms in
-- Postulates.agda can be replaced by these derived theorems
-- once we track that memory was created by proper allocation.
------------------------------------------------------------------------
