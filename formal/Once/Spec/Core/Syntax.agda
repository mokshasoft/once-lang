-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Spec.Core.Syntax — the CORE CALCULUS's raw terms (plan 0.102 A).
--
-- SPEC. The core is the language definition; the bidirectional judgment is a
-- surface that elaborates into it. Shaped as the non-dependent fragment of
-- OCP-0009's `Spec/Kernel` (`NbEPDirDBType`): well-scoped de Bruijn raw terms,
-- Curry-style binders (the typing judgment supplies the domain), and a
-- separate EXTRINSIC judgment (`Once.Spec.Core.Typing`). The dependent kernel
-- lands by adding formers here, never by introducing a second syntax.
--
-- What is NOT a former: the categorical combinators (`id`, `compose`, `fst`
-- as a morphism, `pair`/`case` of arrows, `curry`, `apply`, `terminal`,
-- `initial`, …). They are DEFINITIONS (`Once.Spec.Core.Derived`) — each is a
-- λ-term over the formers below. The compiler still emits `IR.fst` for `fst`;
-- its obligation is that the IR means what the definition means.
--
-- Formers, per type:
--   variables / arrows   var, lam, app, let′
--   Unit                 unit
--   products             pair, fst, snd
--   sums                 inl, inr, case
--   Void                 absurd
--   μ F                  roll (In), fold (the non-dependent eliminator)
--   ν F                  unfold (ana), out (Out)
--   subtyping            coerce (a term converted along `A <: B`, D226)
--   base types           lit, prim (the arithmetic SigOps, saturated)
--   FFI                  sigop (a declared constant with a contract, D061/D071)
------------------------------------------------------------------------

module Once.Spec.Core.Syntax where

open import Data.Nat using (ℕ; suc)
open import Data.Fin using (Fin; zero; suc)
open import Data.Integer using (ℤ)
open import Data.String using (String)
open import Once.Float.Decimal using (Decimal)
open import Once.CanonicalName using (CanonicalName)
open import Once.Type using (Type; Unit; Int; Float; _*_; _+_)

------------------------------------------------------------------------
-- Literals and primitive operations
------------------------------------------------------------------------

data Lit : Set where
  lit-int   : ℤ → Lit
  lit-float : Decimal → Lit          -- a negative literal is a negative decimal (F3)
  lit-str   : String → Lit

-- The arithmetic, as SATURATED primitive applications: each one is a Pure
-- SigOp (`Once.Arith.SigOp.Builders`), applied to one argument (a pair for the
-- binary ones). Saturated so that `a + b` uses exactly `Ψa +ᵘ Ψb`, as the
-- surface's `add` does, rather than an application's `q *ᵘ Ψ`.
data Prim : Set where
  p-add p-sub p-mul p-div p-mod p-neg : Prim
  p-lt p-le p-gt p-ge p-eq p-ne        : Prim
  p-fadd p-fsub p-fmul p-fdiv          : Prim
  p-i2f                                : Prim

primDom : Prim → Type
primDom p-add  = Int * Int
primDom p-sub  = Int * Int
primDom p-mul  = Int * Int
primDom p-div  = Int * Int
primDom p-mod  = Int * Int
primDom p-neg  = Int
primDom p-lt   = Int * Int
primDom p-le   = Int * Int
primDom p-gt   = Int * Int
primDom p-ge   = Int * Int
primDom p-eq   = Int * Int
primDom p-ne   = Int * Int
primDom p-fadd = Float * Float
primDom p-fsub = Float * Float
primDom p-fmul = Float * Float
primDom p-fdiv = Float * Float
primDom p-i2f  = Int

primCod : Prim → Type
primCod p-add  = Int
primCod p-sub  = Int
primCod p-mul  = Int
primCod p-div  = Int
primCod p-mod  = Int
primCod p-neg  = Int
primCod p-lt   = Unit + Unit
primCod p-le   = Unit + Unit
primCod p-gt   = Unit + Unit
primCod p-ge   = Unit + Unit
primCod p-eq   = Unit + Unit
primCod p-ne   = Unit + Unit
primCod p-fadd = Float
primCod p-fsub = Float
primCod p-fmul = Float
primCod p-fdiv = Float
primCod p-i2f  = Float

------------------------------------------------------------------------
-- Raw terms, well-scoped: `Tm n` has at most `n` free variables.
------------------------------------------------------------------------

data Tm (n : ℕ) : Set where
  var    : Fin n → Tm n
  lam    : Tm (suc n) → Tm n
  app    : Tm n → Tm n → Tm n
  let′   : Tm n → Tm (suc n) → Tm n
  unit   : Tm n
  pair   : Tm n → Tm n → Tm n
  fst    : Tm n → Tm n
  snd    : Tm n → Tm n
  inl    : Tm n → Tm n
  inr    : Tm n → Tm n
  case   : Tm n → Tm (suc n) → Tm (suc n) → Tm n
  absurd : Tm n → Tm n
  roll   : Tm n → Tm n
  fold   : Tm n → Tm n → Tm n            -- fold alg t
  unfold : Tm n → Tm n → Tm n            -- unfold coalg seed
  out    : Tm n → Tm n
  coerce : Type → Type → Tm n → Tm n     -- coerce A B t, along A <: B
  lit    : Lit → Tm n
  prim   : Prim → Tm n → Tm n
  sigop  : CanonicalName → Type → Tm n

------------------------------------------------------------------------
-- Renaming and substitution (strict, as in the POC's K0)
------------------------------------------------------------------------

Ren : ℕ → ℕ → Set
Ren n m = Fin n → Fin m

extR : ∀ {n m} → Ren n m → Ren (suc n) (suc m)
extR ρ zero    = zero
extR ρ (suc i) = suc (ρ i)

ren : ∀ {n m} → Ren n m → Tm n → Tm m
ren ρ (var i)        = var (ρ i)
ren ρ (lam t)        = lam (ren (extR ρ) t)
ren ρ (app t u)      = app (ren ρ t) (ren ρ u)
ren ρ (let′ t u)     = let′ (ren ρ t) (ren (extR ρ) u)
ren ρ unit           = unit
ren ρ (pair t u)     = pair (ren ρ t) (ren ρ u)
ren ρ (fst t)        = fst (ren ρ t)
ren ρ (snd t)        = snd (ren ρ t)
ren ρ (inl t)        = inl (ren ρ t)
ren ρ (inr t)        = inr (ren ρ t)
ren ρ (case s l r)   = case (ren ρ s) (ren (extR ρ) l) (ren (extR ρ) r)
ren ρ (absurd t)     = absurd (ren ρ t)
ren ρ (roll t)       = roll (ren ρ t)
ren ρ (fold a t)     = fold (ren ρ a) (ren ρ t)
ren ρ (unfold c t)   = unfold (ren ρ c) (ren ρ t)
ren ρ (out t)        = out (ren ρ t)
ren ρ (coerce A B t) = coerce A B (ren ρ t)
ren ρ (lit l)        = lit l
ren ρ (prim p t)     = prim p (ren ρ t)
ren ρ (sigop c A)    = sigop c A

wk : ∀ {n} → Tm n → Tm (suc n)
wk = ren suc

Sub : ℕ → ℕ → Set
Sub n m = Fin n → Tm m

extS : ∀ {n m} → Sub n m → Sub (suc n) (suc m)
extS σ zero    = var zero
extS σ (suc i) = wk (σ i)

sub : ∀ {n m} → Sub n m → Tm n → Tm m
sub σ (var i)        = σ i
sub σ (lam t)        = lam (sub (extS σ) t)
sub σ (app t u)      = app (sub σ t) (sub σ u)
sub σ (let′ t u)     = let′ (sub σ t) (sub (extS σ) u)
sub σ unit           = unit
sub σ (pair t u)     = pair (sub σ t) (sub σ u)
sub σ (fst t)        = fst (sub σ t)
sub σ (snd t)        = snd (sub σ t)
sub σ (inl t)        = inl (sub σ t)
sub σ (inr t)        = inr (sub σ t)
sub σ (case s l r)   = case (sub σ s) (sub (extS σ) l) (sub (extS σ) r)
sub σ (absurd t)     = absurd (sub σ t)
sub σ (roll t)       = roll (sub σ t)
sub σ (fold a t)     = fold (sub σ a) (sub σ t)
sub σ (unfold c t)   = unfold (sub σ c) (sub σ t)
sub σ (out t)        = out (sub σ t)
sub σ (coerce A B t) = coerce A B (sub σ t)
sub σ (lit l)        = lit l
sub σ (prim p t)     = prim p (sub σ t)
sub σ (sigop c A)    = sigop c A

-- What β plugs in.
single : ∀ {n} → Tm n → Sub (suc n) n
single u zero    = u
single u (suc i) = var i

_[_] : ∀ {n} → Tm (suc n) → Tm n → Tm n
t [ u ] = sub (single u) t

infix 8 _[_]

------------------------------------------------------------------------
-- Values (call-by-value): what a variable may be replaced by, and where
-- the β rows of the equality judgment apply.
------------------------------------------------------------------------

data Value {n} : Tm n → Set where
  v-var  : ∀ {i} → Value (var i)
  v-lam  : ∀ {t} → Value (lam t)
  v-unit : Value unit
  v-pair : ∀ {a b} → Value a → Value b → Value (pair a b)
  v-inl  : ∀ {a} → Value a → Value (inl a)
  v-inr  : ∀ {b} → Value b → Value (inr b)
  v-roll : ∀ {a} → Value a → Value (roll a)
