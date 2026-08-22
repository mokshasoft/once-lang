------------------------------------------------------------------------
-- OCP-0009 — gcd IN PURE AGDA, cost control.
--
-- Nothing to do with the kernel.  Self-contained: no imports, so the file
-- IS the cost.
--
-- ⚠⚠ AND THERE IS NO "FOR FREE" VERSION, WHICH IS THE FIRST FINDING.
--   `NbEPDirDBExamplesAckAgda1` is nine lines because Agda's termination
--   checker already does lexicographic descent on the argument tuple, and
--   Ackermann's recursive arguments are all SUBTERMS.  Subtractive gcd's
--   are not — `a ∸ b` is a subterm of nothing — so the checker cannot
--   help, and pure Agda needs the same explicit well-foundedness the
--   kernel does.  ⇒ gcd's three-way comparison is fair in a way
--   Ackermann's is not: no route gets it for free.
--
-- ★ WHAT AGDA GIVES AWAY THAT THE KERNEL CHARGES FOR, and it is most of
--   the gap:
--
--     `suc a ∸ suc b = a ∸ b`  is DEFINITIONAL here (one clause of `_∸_`).
--       Over the kernel `monusTm` is a `natrec` through `pred`, so the
--       same fact is its own induction — `NbEPDirDBLibArithMonus.⊢monusLt`.
--
--     `+` monotone in EITHER argument is a three-line induction here.
--       Over the kernel the base argument is three lines and the RECURSED
--       one is unreachable without commutativity — `Id`, `jsub`, and the
--       two standard lemmas (`NbEPDirDBLibArithComm`, ~130 lines).
--
--   Both differences have the same cause: Agda's `_∸_`/`_+_` are defined
--   by pattern matching and REDUCE on open terms, while the kernel's are
--   `natrec` terms that are stuck until the scrutinee is a numeral.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Comparison.GcdRoute1Agda where
data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

infix  4 _≡_
infix  4 _≤_
infix  4 _<_
infixl 6 _+_
infixl 6 _∸_

data _≤_ : ℕ → ℕ → Set where
  z≤n : ∀ {n}           → zero  ≤ n
  s≤s : ∀ {m n} → m ≤ n → suc m ≤ suc n

_<_ : ℕ → ℕ → Set
m < n = suc m ≤ n

data Acc {A : Set} (R : A → A → Set) (x : A) : Set where
  acc : (∀ y → R y x → Acc R y) → Acc R x

_+_ : ℕ → ℕ → ℕ
zero  + n = n
suc m + n = suc (m + n)

-- ★ THE CLAUSE THE KERNEL HAS TO PROVE
_∸_ : ℕ → ℕ → ℕ
m     ∸ zero  = m
zero  ∸ suc n = zero
suc m ∸ suc n = m ∸ n

------------------------------------------------------------------------
-- order basics
------------------------------------------------------------------------

≤-refl : ∀ n → n ≤ n
≤-refl zero    = z≤n
≤-refl (suc n) = s≤s (≤-refl n)

≤-trans : ∀ {a b c} → a ≤ b → b ≤ c → a ≤ c
≤-trans z≤n     _       = z≤n
≤-trans (s≤s p) (s≤s q) = s≤s (≤-trans p q)

n≤sn : ∀ n → n ≤ suc n
n≤sn zero    = z≤n
n≤sn (suc n) = s≤s (n≤sn n)

<-acc : ∀ n → ∀ m → m < n → Acc _<_ m
<-acc (suc n) m (s≤s m≤n) = acc (λ y y<m → <-acc n y (≤-trans y<m m≤n))

<-wf : ∀ n → Acc _<_ n
<-wf n = acc (<-acc n)

------------------------------------------------------------------------
-- the arithmetic gcd's descent needs.  ⚠ Compare the kernel's:
-- `NbEPDirDBLibArith` + `NbEPDirDBLibArithComm` + `NbEPDirDBLibArithMonus`.
------------------------------------------------------------------------

∸-≤ : ∀ m n → m ∸ n ≤ m
∸-≤ m       zero    = ≤-refl m
∸-≤ zero    (suc n) = z≤n
∸-≤ (suc m) (suc n) = ≤-trans (∸-≤ m n) (n≤sn m)

≤-plusˡ : ∀ n c → c ≤ n + c
≤-plusˡ zero    c = ≤-refl c
≤-plusˡ (suc n) c = ≤-trans (≤-plusˡ n c) (n≤sn (n + c))

-- monotone in the FIRST argument — the one the kernel needs comm for
+-monoˡ : ∀ {a b} → a ≤ b → ∀ c → a + c ≤ b + c
+-monoˡ (z≤n {n}) c = ≤-plusˡ n c
+-monoˡ (s≤s p)   c = s≤s (+-monoˡ p c)

-- monotone in the SECOND, in the strict form the descent wants
+-monoʳ-s : ∀ a {x y} → x ≤ y → suc (a + x) ≤ a + suc y
+-monoʳ-s zero    p = s≤s p
+-monoʳ-s (suc a) p = s≤s (+-monoʳ-s a p)

------------------------------------------------------------------------
-- the comparison.  ⚠ Agda has coproducts; the kernel does not, and there
-- the same job is a `natrec` on `a ∸ b` with a CONSTANT motive.
------------------------------------------------------------------------

data Cmp (a b : ℕ) : Set where
  le : a ≤ b → Cmp a b
  gt : b < a → Cmp a b

cmp : ∀ a b → Cmp a b
cmp zero    b       = le z≤n
cmp (suc a) zero    = gt (s≤s z≤n)
cmp (suc a) (suc b) with cmp a b
... | le p = le (s≤s p)
... | gt p = gt (s≤s p)

------------------------------------------------------------------------
-- ★★★ THE FUNCTION.  Same four equations, same measure `a + b`, same
--     three-way split as `NbEPDirDBExamplesGcdLib`.
------------------------------------------------------------------------

desc-left : ∀ a b → ((a ∸ b) + suc b) < (suc a + suc b)
desc-left a b = s≤s (+-monoˡ (∸-≤ a b) (suc b))

desc-right : ∀ a b → (suc a + (b ∸ a)) < (suc a + suc b)
desc-right a b = s≤s (+-monoʳ-s a (∸-≤ b a))

gcd-acc : ∀ a b → Acc _<_ (a + b) → ℕ
gcd-acc a       zero    _       = a
gcd-acc zero    (suc b) _       = suc b
gcd-acc (suc a) (suc b) (acc r) with cmp a b
... | le _ = gcd-acc (suc a) (b ∸ a) (r _ (desc-right a b))
... | gt _ = gcd-acc (a ∸ b) (suc b) (r _ (desc-left a b))

gcd : ℕ → ℕ → ℕ
gcd a b = gcd-acc a b (<-wf (a + b))

------------------------------------------------------------------------
-- ★★ AND IT COMPUTES — by `refl`.  ⚠ THIS is the sharpest single line of
--    the comparison: over the kernel the same four facts are explicit
--    reduction chains (`NbEPDirDBExamplesGcdLib`'s four `⟶*` proofs plus
--    `gcd-2-0`), because `⟶*` is a DATATYPE there, not Agda's conversion.
------------------------------------------------------------------------

n2 n3 n4 n6 : ℕ
n2 = suc (suc zero)
n3 = suc n2
n4 = suc n3
n6 = suc (suc n4)

gcd-2-0 : gcd n2 zero ≡ n2
gcd-2-0 = refl

gcd-0-2 : gcd zero n2 ≡ n2
gcd-0-2 = refl

gcd-3-1 : gcd n3 (suc zero) ≡ suc zero
gcd-3-1 = refl

-- ★ the one the kernel version cannot yet reach end to end
gcd-4-6 : gcd n4 n6 ≡ n2
gcd-4-6 = refl
