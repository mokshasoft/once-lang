-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Internal.Core.Syntax — the CORE CALCULUS's raw terms (plan 0.102 A).
--
-- The compiler's internal core (D333; the Spec's is `Once.Spec.Core`); the
-- bidirectional judgment is a surface that elaborates into it. Shaped as the non-dependent fragment of
-- OCP-0009's `Spec/Kernel` (`NbEPDirDBType`): well-scoped de Bruijn raw terms
-- and a separate EXTRINSIC judgment (`Once.Internal.Core.Typing`). The dependent
-- kernel lands by adding formers here, never by introducing a second syntax.
--
-- A TERM, IN ITS CONTEXT, DETERMINES ITS TYPE (D310): Church-style. `lam`
-- carries its arrow's domain, quantity and grade; `inl`/`inr` the other
-- summand; `absurd` its type; `roll`/`fold`/`unfold` their functor; `let′` and
-- `case` the quantities their binders are used at (a usage is not a type, but
-- it decides whether the bound value is evaluated). The rest (`app`, `pair`,
-- `fst`, `out`, …) are determined by their parts. The grade is determined up
-- to `⊢sub-eff`, which changes no type. The meaning is defined on derivations,
-- and this is what makes it a function of the judgment
-- (the Spec's `Coherence`, `Once.Metatheory.Coherence`): two derivations differ
-- only in where the structural rules sit.
--
-- What is NOT a former: the categorical combinators (`id`, `compose`, `fst`
-- as a morphism, `pair`/`case` of arrows, `curry`, `apply`, `terminal`,
-- `initial`, …). They are DEFINITIONS (`Once.Internal.Core.Derived`) — each is a
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
--   running forever      iter (the loop; its typing comes with plan 0.119 D5)
--   subtyping            coerce (a term converted along `A <: B`, D226)
--   base types           lit, prim (the arithmetic SigOps, saturated)
--   FFI                  sigop (a declared constant with a contract, D061/D071)
------------------------------------------------------------------------

open import Data.Nat using (ℕ)
open import Once.Internal.Core.PolyTy using (Sig; _!!_; GSub; module Schema)
open Schema using (arity)

-- Plan 0.103 phase 4: the core is relative to a DEFINITIONS SIGNATURE `S` —
-- the schemas of the telescope's earlier definitions.
open import Once.Internal.Contract using (ISig)
module Once.Internal.Core.Syntax {Fs : ISig} {s : ℕ} (S : Sig Fs s) where

open import Data.Nat using (ℕ; suc)
open import Data.Fin using (Fin; zero; suc)
open import Data.Integer using (ℤ)
open import Once.Spec.Float.Decimal using (Decimal)
open import Once.Spec.Name using (CanonicalName)
open import Once.Spec.Type using (Type; Unit; Int; Float; _*_; _+_)
open import Once.Internal.Type using (Functor)
open import Once.Spec.Grade using (Quantity; Purity)

------------------------------------------------------------------------
-- Literals and primitive operations
------------------------------------------------------------------------

data Lit : Set where
  lit-int   : ℤ → Lit
  lit-float : Decimal → Lit          -- a negative literal is a negative decimal (F3)

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
  lam    : Type → Quantity → Purity → Tm (suc n) → Tm n  -- lam A q π t : A ⇒[ q , π ] _
  app    : Tm n → Tm n → Tm n
  let′   : Quantity → Tm n → Tm (suc n) → Tm n       -- let′ q e b: the bound variable used q times
  unit   : Tm n
  pair   : Tm n → Tm n → Tm n
  fst    : Tm n → Tm n
  snd    : Tm n → Tm n
  inl    : Type → Tm n → Tm n                      -- inl B a : _ + B
  inr    : Type → Tm n → Tm n                      -- inr A b : A + _
  case   : Quantity → Quantity → Tm n → Tm (suc n) → Tm (suc n) → Tm n  -- the arms' binders' quantities
  absurd : Type → Tm n → Tm n                      -- absurd A e : A
  roll   : Functor → Tm n → Tm n                   -- roll F t : μ F
  fold   : Functor → Tm n → Tm n → Tm n            -- fold F alg t: t : μ F
  unfold : Functor → Tm n → Tm n → Tm n            -- unfold F coalg seed : ν F _
  iter   : Tm n → Tm n → Tm n                      -- iter step seed : B, for step : A ⇒ B + A
  out    : Tm n → Tm n
  coerce : Type → Type → Tm n → Tm n     -- coerce A B t, along A <: B
  lit    : Lit → Tm n
  prim   : Prim → Tm n → Tm n
  sigop  : CanonicalName → Type → Tm n
  -- Plan 0.103 phase 4: a DEFINITION at a ground instance of its schema.
  ref    : (d : Fin s) → GSub (arity (S !! d)) → Tm n

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
ren ρ (lam A q π t)  = lam A q π (ren (extR ρ) t)
ren ρ (app t u)      = app (ren ρ t) (ren ρ u)
ren ρ (let′ q t u)   = let′ q (ren ρ t) (ren (extR ρ) u)
ren ρ unit           = unit
ren ρ (pair t u)     = pair (ren ρ t) (ren ρ u)
ren ρ (fst t)        = fst (ren ρ t)
ren ρ (snd t)        = snd (ren ρ t)
ren ρ (inl B t)      = inl B (ren ρ t)
ren ρ (inr A t)      = inr A (ren ρ t)
ren ρ (case qℓ qr s l r) = case qℓ qr (ren ρ s) (ren (extR ρ) l) (ren (extR ρ) r)
ren ρ (absurd A t)   = absurd A (ren ρ t)
ren ρ (roll F t)     = roll F (ren ρ t)
ren ρ (fold F a t)   = fold F (ren ρ a) (ren ρ t)
ren ρ (unfold F c t) = unfold F (ren ρ c) (ren ρ t)
ren ρ (iter f t)     = iter (ren ρ f) (ren ρ t)
ren ρ (out t)        = out (ren ρ t)
ren ρ (coerce A B t) = coerce A B (ren ρ t)
ren ρ (lit l)        = lit l
ren ρ (prim p t)     = prim p (ren ρ t)
ren ρ (sigop c A)    = sigop c A
ren ρ (ref d τ)      = ref d τ

wk : ∀ {n} → Tm n → Tm (suc n)
wk = ren suc

Sub : ℕ → ℕ → Set
Sub n m = Fin n → Tm m

extS : ∀ {n m} → Sub n m → Sub (suc n) (suc m)
extS σ zero    = var zero
extS σ (suc i) = wk (σ i)

sub : ∀ {n m} → Sub n m → Tm n → Tm m
sub σ (var i)        = σ i
sub σ (lam A q π t)  = lam A q π (sub (extS σ) t)
sub σ (app t u)      = app (sub σ t) (sub σ u)
sub σ (let′ q t u)   = let′ q (sub σ t) (sub (extS σ) u)
sub σ unit           = unit
sub σ (pair t u)     = pair (sub σ t) (sub σ u)
sub σ (fst t)        = fst (sub σ t)
sub σ (snd t)        = snd (sub σ t)
sub σ (inl B t)      = inl B (sub σ t)
sub σ (inr A t)      = inr A (sub σ t)
sub σ (case qℓ qr s l r) = case qℓ qr (sub σ s) (sub (extS σ) l) (sub (extS σ) r)
sub σ (absurd A t)   = absurd A (sub σ t)
sub σ (roll F t)     = roll F (sub σ t)
sub σ (fold F a t)   = fold F (sub σ a) (sub σ t)
sub σ (unfold F c t) = unfold F (sub σ c) (sub σ t)
sub σ (iter f t)     = iter (sub σ f) (sub σ t)
sub σ (out t)        = out (sub σ t)
sub σ (coerce A B t) = coerce A B (sub σ t)
sub σ (lit l)        = lit l
sub σ (prim p t)     = prim p (sub σ t)
sub σ (sigop c A)    = sigop c A
sub σ (ref d τ)      = ref d τ

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
  v-lam  : ∀ {A q π t} → Value (lam A q π t)
  v-unit : Value unit
  v-pair : ∀ {a b} → Value a → Value b → Value (pair a b)
  v-inl  : ∀ {B a} → Value a → Value (inl B a)
  v-inr  : ∀ {A b} → Value b → Value (inr A b)
  v-roll : ∀ {F a} → Value a → Value (roll F a)
