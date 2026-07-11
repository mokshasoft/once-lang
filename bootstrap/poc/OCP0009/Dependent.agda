------------------------------------------------------------------------
-- OCP-0009 · POC-1 — dependent-index conversion via the same evaluator
--
-- A dependent type-checker's core new obligation is deciding equality of
-- types that mention TERMS: `Vec m A ≡ Vec n A` holds iff the index terms
-- `m` and `n` are convertible. OCP-0009's whole bet (Rung 2) is that this
-- reuses the *same* evaluator `conv` — dependency adds no new decision
-- engine, only the discipline of comparing indices.
--
-- This module cashes that on the motivating example `Vec (0+n) ≡ Vec n`,
-- with the index arithmetic `+` implemented as a REAL IR morphism (a `cata`
-- over `Nat`, point-free), and the type-equality decided by the POC's proven
-- `conv` on the index terms. No new machinery: `add` is an ordinary
-- `Term`, index conversion is `conv fo-Nat`.
--
-- Scope: CLOSED indices (`0+3 ≋ 3`, `3+0 ≋ 3`). The *general* law
-- `∀ n. Vec (0+n) ≡ Vec n` with `n` a free context variable is conversion
-- on an OPEN term of `Nat` domain — the `μ`-domain frontier that needs
-- neutrals / NbE (POC-0b(iii)). The mechanism, though, is identical: the
-- checker calls the same `conv` on the indices.
------------------------------------------------------------------------

module poc.OCP0009.Dependent where

open import normalizer.Syntax.Types
open import normalizer.Syntax.CCC
open import normalizer.Testing.Evaluator hiding (fst; snd)
open import poc.OCP0009.Conv   using (conv; FirstOrder; fo-μ)
open import poc.OCP0009.Sound  using (_≋_; conv-sound)

------------------------------------------------------------------------
-- Nat and its numerals (the index type), as IR morphisms.
------------------------------------------------------------------------

NatF : Func
NatF = One ⊕ Id

Nat : Ty
Nat = μ NatF

fo-Nat : FirstOrder Nat
fo-Nat = fo-μ

zero : Term Unit Nat
zero = In ∘ inl

suc : Term Nat Nat
suc = In ∘ inr

one two three : Term Unit Nat
one   = suc ∘ zero
two   = suc ∘ one
three = suc ∘ two

------------------------------------------------------------------------
-- Addition, point-free, as a `cata` over the first argument.
--
--   add 0     = λ n. n              = curry snd
--   add (k+1) = λ n. suc (add k n)  = λ f. suc ∘ f  = curry (suc ∘ apply)
--
--   add  : Nat → (Nat ⇒ Nat)   (curried)
--   plus : (Nat × Nat) → Nat
------------------------------------------------------------------------

addAlg : Term (⟦ NatF ⟧F (Nat ⇒ Nat)) (Nat ⇒ Nat)
addAlg = [ curry snd , curry (suc ∘ apply) ]

add : Term Nat (Nat ⇒ Nat)
add = cata NatF addAlg

plus : Term (Nat * Nat) Nat
plus = apply ∘ ⟨ add ∘ fst , snd ⟩

-- index term  m + n  (as a closed `Term Unit Nat` when m, n are closed)
_⊕N_ : Term Unit Nat → Term Unit Nat → Term Unit Nat
m ⊕N n = plus ∘ ⟨ m , n ⟩

------------------------------------------------------------------------
-- Type equality of `Vec _ A` is index-term conversion — decided by `conv`.
--
--   Vec m A ≡ Vec n A     ⇔     conv fo-Nat m n ≡ true
--
-- (`Vec` is not built in the simply-typed IR; POC-1 is about the CONVERSION
-- mechanism a dependent layer would call, which is exactly this.)
------------------------------------------------------------------------

VecConv : Term Unit Nat → Term Unit Nat → Bool
VecConv = conv fo-Nat

------------------------------------------------------------------------
-- The motivating equalities, as executing checks (Agda runs `add`/`plus`).
------------------------------------------------------------------------

-- Vec (0 + 3) ≡ Vec 3   (left unit — definitional: add 0 = id function)
_ : VecConv (zero ⊕N three) three ≡ true
_ = refl

-- Vec (3 + 0) ≡ Vec 3   (right unit — requires the `cata` to actually run)
_ : VecConv (three ⊕N zero) three ≡ true
_ = refl

-- Vec (1 + 2) ≡ Vec 3
_ : VecConv (one ⊕N two) three ≡ true
_ = refl

-- Vec (1 + 1) ≢ Vec 3   (conversion correctly REJECTS)
_ : VecConv (one ⊕N one) three ≡ false
_ = refl

------------------------------------------------------------------------
-- Not just a Bool: an actual conversion PROOF `_≋_`, the object a
-- dependent checker would transport along.
------------------------------------------------------------------------

Vec-0+3≡Vec-3 : (zero ⊕N three) ≋ three
Vec-0+3≡Vec-3 = conv-sound fo-Nat (zero ⊕N three) three refl

Vec-3+0≡Vec-3 : (three ⊕N zero) ≋ three
Vec-3+0≡Vec-3 = conv-sound fo-Nat (three ⊕N zero) three refl
