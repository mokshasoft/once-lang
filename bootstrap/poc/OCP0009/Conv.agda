------------------------------------------------------------------------
-- OCP-0009 · POC-0 — Decidable conversion by the evaluator (no confluence)
--
-- This is the load-bearing POC of OCP-0009 (§6, "The load-bearing POC"):
-- decide conversion of IR morphisms by *evaluating both sides to a
-- canonical value and comparing*, exactly
--
--        conv(a, b)  =  eq-val (eval a) (eval b)
--
-- which is OCP-0009's evaluator route (Motivation → "The property, stated
-- at the right altitude"): determinism of `eval` REPLACES confluence — a
-- function has one output, so the canonical value is unique for free. NO
-- rewriting, NO confluence, NO strong-normalization-of-a-rewrite-system is
-- used anywhere below. The classical `SN + confluence` chain (provably
-- unavailable for full βη CCC — `NonConfluenceWitness`) is bypassed.
--
-- It reuses the real compiler IR and its evaluator UNCHANGED:
--   · `Term A B`  — the reified BCCR IR      (normalizer.Syntax.CCC)
--   · `eval`      — the total big-step evaluator (normalizer.Testing.Evaluator)
-- and adds only two small pieces: a generic structural equality on
-- canonical values (`eq-val`/`eq-Fix`) and a `FirstOrder` guard marking the
-- codomains where a canonical value is finite data (so equality is
-- decidable without neutral reification — see SCOPE below).
--
-- This module is `--safe` and POSTULATE-FREE. The two adequacy obligations
-- (that `conv` decides the intended definitional equality) are stated as
-- the named holes in `poc.OCP0009.Transparency`.
--
-- SCOPE (honest).  `conv` is defined for closed morphisms `Term Unit C`
-- whose codomain `C` is FIRST-ORDER (Void/Unit/×/+/μ — no `⇒`). That is
-- precisely the type-level-conversion case Once's checker needs most
-- (indices like `Vec n` are first-order data). Comparing function-valued
-- morphisms (`C = A ⇒ B`) needs NbE reification against a neutral/generic
-- argument — deferred to POC-0b (see README, "Next"). This is the one place
-- the closed-term evaluator genuinely extends (OCP-0009 §5, "open terms /
-- neutrals").
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.Conv where

open import normalizer.Syntax.Types
open import normalizer.Syntax.CCC
-- Hide the Σ-projection re-exports so `fst`/`snd` below refer to the IR
-- Term constructors, not the record fields.
open import normalizer.Testing.Evaluator hiding (fst; snd)

------------------------------------------------------------------------
-- FIRST-ORDER codomains: where a canonical value is finite data.
--
-- `Func` is Ty-independent (only Id/One/Kc/⊕/⊗ — no `⇒`; see Types.agda),
-- so every `μ F` is unconditionally first-order.
------------------------------------------------------------------------

data FirstOrder : Ty → Set where
  fo-void : FirstOrder Void
  fo-unit : FirstOrder Unit
  fo-*    : ∀ {A B} → FirstOrder A → FirstOrder B → FirstOrder (A * B)
  fo-+    : ∀ {A B} → FirstOrder A → FirstOrder B → FirstOrder (A + B)
  fo-μ    : ∀ {F} → FirstOrder (μ F)

------------------------------------------------------------------------
-- Generic structural equality on canonical values.
--
-- `eq-Fix`/`eq-FS` are the functor-generic version of the (monomorphic)
-- `eq-Term` in Testing.Evaluator: structural, total, no pragma. This is
-- the `≟` of `⌜eval a⌝ ≟ ⌜eval b⌝`, specialised to the value domain the
-- evaluator produces.
------------------------------------------------------------------------

mutual
  eq-Fix : ∀ F → Fix F → Fix F → Bool
  eq-Fix F (fix x) (fix y) = eq-FS F F x y

  eq-FS : ∀ F G → ⟦ G ⟧FS (Fix F) → ⟦ G ⟧FS (Fix F) → Bool
  eq-FS F Id      x        y        = eq-Fix F x y
  eq-FS F One     _        _        = true
  eq-FS F (Kc H)  x        y        = eq-Fix H x y
  eq-FS F (G ⊕ H) (inj₁ x) (inj₁ y) = eq-FS F G x y
  eq-FS F (G ⊕ H) (inj₂ x) (inj₂ y) = eq-FS F H x y
  eq-FS F (G ⊕ H) _        _        = false
  eq-FS F (G ⊗ H) (x , u)  (y , v)  = eq-FS F G x y ∧ eq-FS F H u v

-- Structural equality on a first-order canonical value.
eq-val : ∀ C → FirstOrder C → ⟦ C ⟧T → ⟦ C ⟧T → Bool
eq-val Void    fo-void       x        _        = ⊥-elim x
eq-val Unit    fo-unit       _        _        = true
eq-val (A * B) (fo-* fa fb)  (a , b)  (c , d)  = eq-val A fa a c ∧ eq-val B fb b d
eq-val (A + B) (fo-+ fa fb)  (inj₁ a) (inj₁ c) = eq-val A fa a c
eq-val (A + B) (fo-+ fa fb)  (inj₂ b) (inj₂ d) = eq-val B fb b d
eq-val (A + B) (fo-+ fa fb)  _        _        = false
eq-val (μ F)   fo-μ          x        y        = eq-Fix F x y

------------------------------------------------------------------------
-- Conversion of closed IR morphisms, decided by the evaluator.
--
--   conv fo t u  =  true   iff   eval t  and  eval u  are the same value.
--
-- Uniqueness of that value is DETERMINISM of `eval` (an Agda function),
-- not confluence of a rewrite relation. That is the whole thesis.
------------------------------------------------------------------------

conv : ∀ {C} → FirstOrder C → (t u : Term Unit C) → Bool
conv {C} fo t u = eq-val C fo (eval t tt) (eval u tt)

------------------------------------------------------------------------
-- Worked examples (each `refl` FORCES Agda to run `conv` at type-check
-- time — so these are the POC actually executing, not just type-checking).
------------------------------------------------------------------------

NatF : Func
NatF = One ⊕ Id

Nat : Ty
Nat = μ NatF

fo-Nat : FirstOrder Nat
fo-Nat = fo-μ

zero : Term Unit Nat
zero = In ∘ inl              -- inl : Term Unit (Unit + Nat)

suc : Term Nat Nat
suc = In ∘ inr               -- inr : Term Nat (Unit + Nat)

one : Term Unit Nat
one = suc ∘ zero

two : Term Unit Nat
two = suc ∘ one

-- Reflexivity of conversion on equal values.
_ : conv fo-Nat zero zero ≡ true
_ = refl

-- Distinct canonical values are distinguished.
_ : conv fo-Nat zero one ≡ false
_ = refl

_ : conv fo-Nat one two ≡ false
_ = refl

-- β for products: `fst ∘ ⟨ t , u ⟩` converts to `t`. Decided purely by
-- evaluation — the redex is never *rewritten*, both sides are just run.
_ : conv fo-Nat (fst ∘ ⟨ zero , one ⟩) zero ≡ true
_ = refl

_ : conv fo-Nat (snd ∘ ⟨ zero , one ⟩) one ≡ true
_ = refl

-- A longer chain reducing to `one`: snd ∘ ⟨ zero , suc ∘ (fst ∘ ⟨ zero , one ⟩) ⟩.
-- (fst ∘ ⟨zero,one⟩ = zero ; suc zero = one ; snd ⟨zero,one'⟩ = one.)
_ : conv fo-Nat (snd ∘ ⟨ zero , suc ∘ (fst ∘ ⟨ zero , one ⟩) ⟩) one ≡ true
_ = refl

-- Identity and associativity of composition are invisible to `conv`
-- (they hold in the model), again without orienting any rewrite.
_ : conv fo-Nat (id ∘ one) ((id ∘ suc) ∘ zero) ≡ true
_ = refl
