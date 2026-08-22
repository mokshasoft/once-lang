------------------------------------------------------------------------
-- OCP-0009 — ACKERMANN IN PURE AGDA, cost control #2: BY HAND.
--
-- Same function, but with the lexicographic well-foundedness PROVED
-- rather than assumed — an explicit `Acc` on ℕ × ℕ ordered
-- lexicographically, and `ack` by recursion on that `Acc`.  Agda's
-- termination checker does nothing here but accept the structural
-- recursion on the accessibility proof.
--
-- This is the honest meta-level analogue of what `⊢lexrec` does inside
-- the object language, so it is the control that separates "proving
-- lexicographic descent at all" from "the kernel's ENCODING of it".
--
-- Self-contained: no imports, no sized types, `--safe`.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.AckAgda2 where
data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

record _×_ (A B : Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B
open _×_

data _≤_ : ℕ → ℕ → Set where
  z≤n : ∀ {n}             → zero  ≤ n
  s≤s : ∀ {m n} → m ≤ n   → suc m ≤ suc n

_<_ : ℕ → ℕ → Set
m < n = suc m ≤ n

data Acc {A : Set} (R : A → A → Set) (x : A) : Set where
  acc : (∀ y → R y x → Acc R y) → Acc R x

≤-refl : ∀ n → n ≤ n
≤-refl zero    = z≤n
≤-refl (suc n) = s≤s (≤-refl n)

≤-trans : ∀ {a b c} → a ≤ b → b ≤ c → a ≤ c
≤-trans z≤n     _       = z≤n
≤-trans (s≤s p) (s≤s q) = s≤s (≤-trans p q)

n<sn : ∀ n → n < suc n
n<sn n = s≤s (≤-refl n)

------------------------------------------------------------------------
-- `<` is well-founded.
------------------------------------------------------------------------

<-acc : ∀ n → ∀ m → m < n → Acc _<_ m
<-acc (suc n) m (s≤s m≤n) = acc (λ y y<m → <-acc n y (≤-trans y<m m≤n))

<-wf : ∀ n → Acc _<_ n
<-wf n = acc (<-acc n)

------------------------------------------------------------------------
-- The LEXICOGRAPHIC order on ℕ × ℕ, and its well-foundedness.
------------------------------------------------------------------------

data Lex : ℕ × ℕ → ℕ × ℕ → Set where
  fst< : ∀ {a b c d} → a < c → Lex (a , b) (c , d)
  snd< : ∀ {a b d}   → b < d → Lex (a , b) (a , d)

-- ★ THE NESTING IS THE ORDER, exactly as in ⊢lexrec: the outer step
--   drops the first component and RESETS the second; the inner step holds
--   the first and drops the second.
-- ⚠ the two recursions must be NESTED, not written as one clause: the
--   outer descends on `Acc _<_ a`, the inner on `Acc _<_ b` at a FIXED
--   `a`.  Flattened into a single function Agda rejects it, because the
--   `fst<` call passes a freshly built `<-wf d` for the second component.
lex-wf : ∀ a → Acc _<_ a → ∀ b → Acc _<_ b → Acc Lex (a , b)
lex-wf a (acc ra) = go
  where
    go : ∀ b → Acc _<_ b → Acc Lex (a , b)
    go b (acc rb) = acc step
      where
        step : ∀ p → Lex p (a , b) → Acc Lex p
        step (c , d) (fst< c<a) = lex-wf c (ra c c<a) d (<-wf d)
        step (c , d) (snd< d<b) = go d (rb d d<b)

Lex-wf : ∀ p → Acc Lex p
Lex-wf (a , b) = lex-wf a (<-wf a) b (<-wf b)

------------------------------------------------------------------------
-- Ackermann by recursion on the accessibility proof.
------------------------------------------------------------------------

ackF : ∀ p → Acc Lex p → ℕ
ackF (zero  , n)     _         = suc n
ackF (suc m , zero)  (acc rec) =
  ackF (m , suc zero) (rec (m , suc zero) (fst< (n<sn m)))
ackF (suc m , suc n) (acc rec) =
  ackF (m , inner) (rec (m , inner) (fst< (n<sn m)))
  where
    inner : ℕ
    inner = ackF (suc m , n) (rec (suc m , n) (snd< (n<sn n)))

ack : ℕ → ℕ → ℕ
ack m n = ackF (m , n) (Lex-wf (m , n))
