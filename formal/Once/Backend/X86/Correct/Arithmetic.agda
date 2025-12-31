------------------------------------------------------------------------
-- Once.Backend.X86.Correct.Arithmetic
--
-- Arithmetic lemmas for X86 backend proofs.
-- Eliminates inline arithmetic postulates from proof files.
------------------------------------------------------------------------

module Once.Backend.X86.Correct.Arithmetic where

open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _≤_; z≤n; s≤s; _<_)
open import Data.Nat.Properties using (+-comm; +-assoc; +-identityʳ; +-identityˡ; +-suc;
                                       ≤-refl; ≤-trans; m≤m+n; m∸n≤m;
                                       m+n∸m≡n; m+n∸n≡m; ∸-+-assoc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)
open import Data.Empty using (⊥-elim)

------------------------------------------------------------------------
-- Natural number subtraction lemmas
------------------------------------------------------------------------

-- | Key lemma: (m - n) + k = m - (n - k) when n ≤ m and k ≤ n
--
-- This identity is used in pair proofs to relate stack pointer arithmetic:
--   (rsp - 40) + 8 = rsp - (40 - 8) = rsp - 32
--
-- Proof by induction on k (easiest variable to induct on)
m∸n+k≡m∸n-k : ∀ m n k → n ≤ m → k ≤ n → m ∸ n + k ≡ m ∸ (n ∸ k)
m∸n+k≡m∸n-k m n zero n≤m z≤n =
  -- Base case: k = 0
  -- LHS: (m - n) + 0 = m - n
  -- RHS: m - (n - 0) = m - n
  +-identityʳ (m ∸ n)

m∸n+k≡m∸n-k zero (suc n) (suc k) () _  -- impossible: suc n ≤ 0

m∸n+k≡m∸n-k (suc m) zero (suc k) _ ()  -- impossible: suc k ≤ 0

m∸n+k≡m∸n-k (suc m) (suc n) (suc k) (s≤s n≤m) (s≤s k≤n) =
  -- Inductive case: m = suc m', n = suc n', k = suc k'
  -- LHS: (suc m - suc n) + suc k = (m - n) + suc k
  -- RHS: suc m - (suc n - suc k) = suc m - (n - k)
  --
  -- We have IH: m - n + k ≡ m - (n - k)
  --
  -- Need to show: (m - n) + suc k ≡ suc m - (n - k)
  --
  -- Chain: (m - n) + suc k = suc ((m - n) + k)      [by +-suc]
  --                        = suc (m - (n - k))      [by IH]
  --                        = suc m - (n - k)        [by suc-∸]
  help ((n ∸ k) ≤? m)
  where
    open import Data.Nat using (_≤?_)
    open import Relation.Nullary using (yes; no; Dec)

    -- Helper: suc (m - r) ≡ suc m - r when r ≤ m
    suc-∸ : ∀ x y → y ≤ x → suc (x ∸ y) ≡ suc x ∸ y
    suc-∸ x zero y≤x = refl
    suc-∸ zero (suc y) ()
    suc-∸ (suc x) (suc y) (s≤s y≤x) = suc-∸ x y y≤x

    help : Dec ((n ∸ k) ≤ m) → (m ∸ n) + suc k ≡ suc m ∸ (n ∸ k)
    help (yes nk≤m) =
      trans (+-suc (m ∸ n) k)
        (trans (cong suc (m∸n+k≡m∸n-k m n k n≤m k≤n))
               (suc-∸ m (n ∸ k) nk≤m))
    help (no ¬nk≤m) = ⊥-elim (¬nk≤m (≤-trans (m∸n≤m n k) n≤m))

------------------------------------------------------------------------
-- Derived lemmas
------------------------------------------------------------------------

-- | Alias for use when names need to be distinct
-- (Some proofs use both in different contexts)
m∸n+k≡m∸n-k' : ∀ m n k → n ≤ m → k ≤ n → m ∸ n + k ≡ m ∸ (n ∸ k)
m∸n+k≡m∸n-k' = m∸n+k≡m∸n-k

-- | Common special case: m - 40 + 8 = m - 32
-- Used in pair proofs for stack pointer tracking
m∸40+8≡m∸32 : ∀ m → 40 ≤ m → m ∸ 40 + 8 ≡ m ∸ 32
m∸40+8≡m∸32 m 40≤m = m∸n+k≡m∸n-k m 40 8 40≤m 8≤40
  where
    8≤40 : 8 ≤ 40
    8≤40 = s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))))

-- | Common special case: m - 40 + 16 = m - 24
-- Used in pair proofs for frame pointer calculations
m∸40+16≡m∸24 : ∀ m → 40 ≤ m → m ∸ 40 + 16 ≡ m ∸ 24
m∸40+16≡m∸24 m 40≤m = m∸n+k≡m∸n-k m 40 16 40≤m 16≤40
  where
    16≤40 : 16 ≤ 40
    16≤40 = s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))))))))))))
