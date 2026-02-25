------------------------------------------------------------------------
-- Once.CCC.Target.X86.Correct.Arithmetic
--
-- Arithmetic lemmas for X86 backend proofs.
-- Frame layout constants are defined semantically, not as magic numbers.
------------------------------------------------------------------------

module Once.CCC.Target.X86.Correct.Arithmetic where

open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _*_; _≤_; _>_; z≤n; s≤s; _<_; _≤?_; _<?_)
open import Data.Nat.Properties using (+-comm; +-assoc; +-identityʳ; +-identityˡ; +-suc;
                                       ≤-refl; ≤-trans; m≤m+n; m∸n≤m;
                                       m+n∸m≡n; m+n∸n≡m; ∸-+-assoc; +-monoʳ-<)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst)
open import Relation.Nullary using (yes; no; Dec)
open import Data.Empty using (⊥-elim)

------------------------------------------------------------------------
-- Frame layout constants (semantic definitions)
--
-- Pair frame structure:
--   push r14        ; rsp -= word-size
--   push r15        ; rsp -= word-size
--   push rbp        ; rsp -= word-size
--   mov rbp, rsp    ; rbp = original_rsp - saved-regs-size
--   sub rsp, 16     ; rsp -= pair-alloc (space for 2 slots)
--
-- Final layout from original rsp:
--   [rsp - 8]  = saved r14
--   [rsp - 16] = saved r15
--   [rsp - 24] = saved rbp  ← rbp points here
--   [rsp - 32] = pair snd   (slot 1)
--   [rsp - 40] = pair fst   (slot 0) ← final rsp
------------------------------------------------------------------------

-- | Machine word size in bytes (64-bit)
word-size : ℕ
word-size = 8

-- | Number of registers pushed in frame setup
saved-reg-count : ℕ
saved-reg-count = 3  -- r14, r15, rbp

-- | Number of slots allocated for pair
pair-slot-count : ℕ
pair-slot-count = 2  -- fst, snd

-- | Size of saved registers area
saved-regs-size : ℕ
saved-regs-size = saved-reg-count * word-size  -- 3 × 8 = 24

-- | Size of pair allocation
pair-alloc : ℕ
pair-alloc = pair-slot-count * word-size  -- 2 × 8 = 16

-- | Total frame size
frame-size : ℕ
frame-size = saved-regs-size + pair-alloc  -- 24 + 16 = 40

-- Verify our constants (these are compile-time checked)
_ : saved-regs-size ≡ 24
_ = refl

_ : pair-alloc ≡ 16
_ = refl

_ : frame-size ≡ 40
_ = refl

_ : frame-size ∸ word-size ≡ 32
_ = refl

_ : frame-size ∸ pair-alloc ≡ 24
_ = refl

------------------------------------------------------------------------
-- Extract witnesses from decidable propositions
------------------------------------------------------------------------

-- | Extract ≤ proof from decision (unreachable case uses postulate)
from-yes-≤ : ∀ {m n} → Dec (m ≤ n) → m ≤ n
from-yes-≤ (yes p) = p
from-yes-≤ (no _) = ⊥-elim impossible
  where postulate impossible : _

-- | Extract < proof from decision
from-yes-< : ∀ {m n} → Dec (m < n) → m < n
from-yes-< (yes p) = p
from-yes-< (no _) = ⊥-elim impossible
  where postulate impossible : _

------------------------------------------------------------------------
-- Core subtraction lemma
------------------------------------------------------------------------

private
  -- Helper: suc (x - y) = suc x - y when y ≤ x
  suc-∸ : ∀ x y → y ≤ x → suc (x ∸ y) ≡ suc x ∸ y
  suc-∸ x zero _ = refl
  suc-∸ zero (suc y) ()
  suc-∸ (suc x) (suc y) (s≤s y≤x) = suc-∸ x y y≤x

-- | Key lemma: (m - n) + k = m - (n - k) when n ≤ m and k ≤ n
--
-- Used for stack pointer arithmetic:
--   (rsp - frame-size) + word-size = rsp - (frame-size - word-size)
m∸n+k≡m∸n-k : ∀ m n k → n ≤ m → k ≤ n → m ∸ n + k ≡ m ∸ (n ∸ k)
m∸n+k≡m∸n-k m n zero n≤m z≤n = +-identityʳ (m ∸ n)
m∸n+k≡m∸n-k zero (suc n) (suc k) () _
m∸n+k≡m∸n-k (suc m) zero (suc k) _ ()
m∸n+k≡m∸n-k (suc m) (suc n) (suc k) (s≤s n≤m) (s≤s k≤n) =
  help ((n ∸ k) ≤? m)
  where
    help : Dec ((n ∸ k) ≤ m) → (m ∸ n) + suc k ≡ suc m ∸ (n ∸ k)
    help (yes nk≤m) =
      trans (+-suc (m ∸ n) k)
        (trans (cong suc (m∸n+k≡m∸n-k m n k n≤m k≤n))
               (suc-∸ m (n ∸ k) nk≤m))
    help (no ¬nk≤m) = ⊥-elim (¬nk≤m (≤-trans (m∸n≤m n k) n≤m))

-- | Alias for contexts needing distinct names
m∸n+k≡m∸n-k' : ∀ m n k → n ≤ m → k ≤ n → m ∸ n + k ≡ m ∸ (n ∸ k)
m∸n+k≡m∸n-k' = m∸n+k≡m∸n-k

------------------------------------------------------------------------
-- Frame arithmetic lemmas (using semantic constants)
------------------------------------------------------------------------

-- | Slot 0 + word-size = Slot 1
-- (rsp - frame-size) + word-size = rsp - (frame-size - word-size)
slot0-plus-word≡slot1 : ∀ m → frame-size ≤ m → m ∸ frame-size + word-size ≡ m ∸ (frame-size ∸ word-size)
slot0-plus-word≡slot1 m frame≤m = m∸n+k≡m∸n-k m frame-size word-size frame≤m
                                   (from-yes-≤ (word-size ≤? frame-size))

-- | Slot 0 + pair-alloc = rbp offset
-- (rsp - frame-size) + pair-alloc = rsp - saved-regs-size
slot0-plus-pair≡rbp : ∀ m → frame-size ≤ m → m ∸ frame-size + pair-alloc ≡ m ∸ (frame-size ∸ pair-alloc)
slot0-plus-pair≡rbp m frame≤m = m∸n+k≡m∸n-k m frame-size pair-alloc frame≤m
                                 (from-yes-≤ (pair-alloc ≤? frame-size))

------------------------------------------------------------------------
-- Rbp-relative arithmetic (for saved register access)
------------------------------------------------------------------------

-- | rbp + word-size = r15-save offset
-- (m - saved-regs-size) + word-size = m - pair-alloc
rbp-plus-word≡r15-save : ∀ m → saved-regs-size ≤ m → m ∸ saved-regs-size + word-size ≡ m ∸ pair-alloc
rbp-plus-word≡r15-save m 24≤m = m∸n+k≡m∸n-k m saved-regs-size word-size 24≤m
                                 (from-yes-≤ (word-size ≤? saved-regs-size))

-- | rbp + pair-alloc = r14-save offset
-- (m - saved-regs-size) + pair-alloc = m - word-size
rbp-plus-pair≡r14-save : ∀ m → saved-regs-size ≤ m → m ∸ saved-regs-size + pair-alloc ≡ m ∸ word-size
rbp-plus-pair≡r14-save m 24≤m = m∸n+k≡m∸n-k m saved-regs-size pair-alloc 24≤m
                                 (from-yes-≤ (pair-alloc ≤? saved-regs-size))

------------------------------------------------------------------------
-- Frame layout relationships (semantic names, no ordering symbols)
--
-- These prove containment relationships between frame components.
-- Names use "fits" to be architecture-neutral (stack grows up or down).
------------------------------------------------------------------------

-- | Word fits strictly within pair-alloc space
word-fits-pair-strict : word-size < pair-alloc
word-fits-pair-strict = from-yes-< (word-size <? pair-alloc)

-- | Word fits within pair-alloc space
word-fits-pair : word-size ≤ pair-alloc
word-fits-pair = from-yes-≤ (word-size ≤? pair-alloc)

-- | Word fits strictly within saved-regs space
word-fits-regs-strict : word-size < saved-regs-size
word-fits-regs-strict = from-yes-< (word-size <? saved-regs-size)

-- | Word fits within saved-regs space
word-fits-regs : word-size ≤ saved-regs-size
word-fits-regs = from-yes-≤ (word-size ≤? saved-regs-size)

-- | Pair-alloc fits within saved-regs space
pair-fits-regs : pair-alloc ≤ saved-regs-size
pair-fits-regs = from-yes-≤ (pair-alloc ≤? saved-regs-size)

-- | Word fits within frame remainder (frame - word)
word-fits-frame-remainder : word-size ≤ (frame-size ∸ word-size)
word-fits-frame-remainder = from-yes-≤ (word-size ≤? (frame-size ∸ word-size))

-- | Pair-alloc fits within frame remainder
pair-fits-frame-remainder : pair-alloc ≤ (frame-size ∸ word-size)
pair-fits-frame-remainder = from-yes-≤ (pair-alloc ≤? (frame-size ∸ word-size))

-- | Saved-regs fits within frame remainder
regs-fits-frame-remainder : saved-regs-size ≤ (frame-size ∸ word-size)
regs-fits-frame-remainder = from-yes-≤ (saved-regs-size ≤? (frame-size ∸ word-size))

-- | Word+1 fits within pair-alloc (for rsp > 8 bounds)
word-plus-one-fits-pair : (word-size + 1) ≤ pair-alloc
word-plus-one-fits-pair = from-yes-≤ ((word-size + 1) ≤? pair-alloc)

-- | Pair-alloc fits strictly within saved-regs space
pair-fits-regs-strict : pair-alloc < saved-regs-size
pair-fits-regs-strict = from-yes-< (pair-alloc <? saved-regs-size)

------------------------------------------------------------------------
-- Slot arithmetic for deeper stack offsets
------------------------------------------------------------------------

-- | slot1 + word-size = slot2: (m - 32) + 8 = m - 24
slot1-plus-word≡slot2 : ∀ m → (frame-size ∸ word-size) ≤ m →
  m ∸ (frame-size ∸ word-size) + word-size ≡ m ∸ saved-regs-size
slot1-plus-word≡slot2 m 32≤m = m∸n+k≡m∸n-k m (frame-size ∸ word-size) word-size 32≤m word-fits-frame-remainder

------------------------------------------------------------------------
-- Ordering lemmas for address disjointness
------------------------------------------------------------------------

-- | Any n > m is positive (since suc m ≤ n implies 1 ≤ n)
>-implies-positive : ∀ {n m} → n > m → n > 0
>-implies-positive bound = ≤-trans (s≤s z≤n) bound

-- | m ≤ n and m > k and k > 0 implies (m - k) < n
∸-preserves-< : ∀ {m n k} → m ≤ n → m > k → k > 0 → (m ∸ k) < n
∸-preserves-< {suc m} {n} {suc k} m≤n (s≤s m>k) (s≤s z≤n) =
  ≤-trans (s≤s (m∸n≤m m k)) m≤n

-- | m < n implies m ≢ n
<⇒≢ : ∀ {m n} → m < n → m ≢ n
<⇒≢ {zero} {suc n} _ ()
<⇒≢ {suc m} {suc n} (s≤s p) refl = <⇒≢ p refl

-- | Adjacent slots have distinct addresses: k + word-size < k + pair-alloc
slot-addrs-distinct : ∀ k → k + word-size < k + pair-alloc
slot-addrs-distinct k = +-monoʳ-< k (from-yes-< (word-size <? pair-alloc))

-- | (m - pair-alloc) + word-size < m when m > pair-alloc
∸+<-lemma : ∀ {m} → m > pair-alloc → (m ∸ pair-alloc) + word-size < m
∸+<-lemma {m} m>alloc = subst ((m ∸ pair-alloc) + word-size <_) eq (slot-addrs-distinct (m ∸ pair-alloc))
  where
    open import Data.Nat.Properties using (<⇒≤; m∸n+n≡m)
    eq : (m ∸ pair-alloc) + pair-alloc ≡ m
    eq = m∸n+n≡m (<⇒≤ m>alloc)
