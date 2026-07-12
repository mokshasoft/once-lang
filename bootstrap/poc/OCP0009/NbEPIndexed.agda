------------------------------------------------------------------------
-- OCP-0009 · Rung 4 — native INDEXED inductive families (indexed containers)
--
-- Once's runtime core is polynomial functors / containers (`μ F`). Rung 4
-- generalizes that to INDEXED containers (Altenkirch–Morris): the least fixed
-- point is now an indexed FAMILY `μix C : I → Set`, so you can define genuinely
-- indexed data (`Vec n`) and — the headline — RELATIONS AS DATATYPES (the
-- typing relation, the evaluation relation, order). This is the single biggest
-- jump toward the summit: once relations are datatypes, "the compiler is
-- correct" is itself a TYPE, provable by indexed induction (`elim`).
--
-- An indexed container over `I` gives, at each index, a set of operations
-- (constructors), each with a set of recursive positions, each demanding a
-- child at some index. Its extension is one node; `μix` ties the knot. Strictly
-- positive (the fixpoint occurs only in a function CODOMAIN), no pragma.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPIndexed where

open import normalizer.Syntax.Types using ( Σ; _,_; ⊤; tt; ⊥ )

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

------------------------------------------------------------------------
-- Indexed containers, their extension, and the indexed fixpoint.
------------------------------------------------------------------------

record IxCon (I : Set) : Set₁ where
  field
    Op : I → Set                          -- constructors available at index i
    Ar : ∀ {i} → Op i → Set               -- recursive positions of a constructor
    ix : ∀ {i} (c : Op i) → Ar c → I      -- index demanded at each position
open IxCon

⟦_⟧ix : ∀ {I} → IxCon I → (I → Set) → (I → Set)
⟦ C ⟧ix X i = Σ (Op C i) (λ c → (a : Ar C c) → X (ix C c a))

data μix {I} (C : IxCon I) : I → Set where
  sup : ∀ {i} → ⟦ C ⟧ix (μix C) i → μix C i

-- Generic INDEXED INDUCTION — the eliminator (= `Cata` over an indexed family).
elim : ∀ {I} (C : IxCon I) (P : ∀ {i} → μix C i → Set)
     → (∀ {i} (c : Op C i) (f : (a : Ar C c) → μix C (ix C c a))
          → ((a : Ar C c) → P (f a)) → P (sup (c , f)))
     → ∀ {i} (x : μix C i) → P x
elim C P step (sup (c , f)) = step c f (λ a → elim C P step (f a))

------------------------------------------------------------------------
-- `Vec` as a GENUINE indexed inductive family (contrast `NbEPEl`'s fold trick).
--   at index 0    : one constructor `nil`, no recursive position;
--   at index suc n: constructor carrying a head `A`, one position, at index n.
------------------------------------------------------------------------

VecC : Set → IxCon ℕ
VecC A = record
  { Op = λ { zero → ⊤ ; (suc _) → A }
  ; Ar = λ { {zero} _ → ⊥ ; {suc _} _ → ⊤ }
  ; ix = λ { {zero} _ () ; {suc n} _ _ → n }
  }

Vec : Set → ℕ → Set
Vec A = μix (VecC A)

nil : ∀ {A} → Vec A zero
nil = sup (tt , λ ())

cons : ∀ {A n} → A → Vec A n → Vec A (suc n)
cons x xs = sup (x , λ _ → xs)

-- A length-2 vector of `ℕ`, at the type `Vec ℕ 2` — the index is a genuine part
-- of the type, tracked by construction.
vec2 : Vec ℕ (suc (suc zero))
vec2 = cons zero (cons (suc zero) nil)      -- [0, 1]

------------------------------------------------------------------------
-- RELATIONS AS DATATYPES — the Rung-4 headline. The `≤` relation is an indexed
-- inductive family; a proof of `1 ≤ 3` is an INHABITANT (evidence). This is the
-- shape every correctness property takes: state it as a family, prove it by
-- providing/deriving evidence.
------------------------------------------------------------------------

data _≤_ : ℕ → ℕ → Set where
  z≤n : ∀ {n}            → zero ≤ n
  s≤s : ∀ {m n} → m ≤ n → suc m ≤ suc n

-- `1 ≤ 3`, inhabited by evidence.
1≤3 : suc zero ≤ suc (suc (suc zero))
1≤3 = s≤s z≤n

-- `≤` is reflexive and transitive — proved by ordinary induction on the family
-- (the same `elim` shape, here specialized).
≤-refl : ∀ n → n ≤ n
≤-refl zero    = z≤n
≤-refl (suc n) = s≤s (≤-refl n)

≤-trans : ∀ {l m n} → l ≤ m → m ≤ n → l ≤ n
≤-trans z≤n       _         = z≤n
≤-trans (s≤s p)   (s≤s q)   = s≤s (≤-trans p q)
