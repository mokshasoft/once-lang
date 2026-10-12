-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Spec.Core.Syntax — the CORE CALCULUS's raw terms (plan 0.102 A).
--
-- SPEC. The core is the language definition; the bidirectional judgment is a
-- surface that elaborates into it. Shaped as the non-dependent fragment of
-- OCP-0009's `Spec/Kernel` (`NbEPDirDBType`): well-scoped de Bruijn raw terms
-- and a separate EXTRINSIC judgment (`Once.Spec.Core.Typing`). The dependent
-- kernel lands by adding formers here, never by introducing a second syntax.
--
-- A TERM RECORDS WHAT ITS DERIVATION WOULD OTHERWISE CHOOSE (D310): given the
-- term and its judgment's type, every premise's type and grade is determined.
-- So `app`, `let′` carry the argument's type and quantity, `fst`/`snd` the
-- other component, `case` the summands and the arms' quantities, `fold`/`out`
-- the functor, `unfold` the seed's type. A former whose premises the
-- conclusion's type already fixes (`lam`, `pair`, `inl`, `roll`, …) carries
-- nothing. The meaning is defined on derivations, and this is what makes it a
-- function of the judgment (`Once.Spec.Core.Coherence`): two derivations can
-- then differ only in where the structural rules sit.
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

open import Data.Nat using (ℕ)
open import Once.Spec.Core.PolyTy using (Sig; _!!_; GSub; module Schema)
open Schema using (arity)

-- Plan 0.103 phase 4: the core is relative to a DEFINITIONS SIGNATURE `S` —
-- the schemas of the telescope's earlier definitions.
open import Once.Spec.Contract using (ISig)
module Once.Spec.Core.Syntax {Fs : ISig} {s : ℕ} (S : Sig Fs s) where

open import Data.Nat using (ℕ; suc)
open import Data.Fin using (Fin; zero; suc)
open import Data.Integer using (ℤ)
open import Once.Float.Decimal using (Decimal)
open import Once.Spec.Name using (CanonicalName)
open import Once.Spec.Type using (Type; Unit; Int; Float; _*_; _+_; Functor)
open import Once.Spec.Type.Grade using (Quantity)

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
  lam    : Tm (suc n) → Tm n
  app    : Type → Quantity → Tm n → Tm n → Tm n      -- app A q f x: f at A ⇒[ q , _ ] _
  let′   : Type → Quantity → Tm n → Tm (suc n) → Tm n  -- let′ A q e b: x : A, used q times
  unit   : Tm n
  pair   : Tm n → Tm n → Tm n
  fst    : Type → Tm n → Tm n                      -- fst B p: p : _ * B
  snd    : Type → Tm n → Tm n                      -- snd A p: p : A * _
  inl    : Tm n → Tm n
  inr    : Tm n → Tm n
  case   : Type → Type → Quantity → Quantity       -- case A B qℓ qr s l r: s : A + B
         → Tm n → Tm (suc n) → Tm (suc n) → Tm n
  absurd : Tm n → Tm n
  roll   : Tm n → Tm n
  fold   : Functor → Tm n → Tm n → Tm n            -- fold F alg t: t : μ F
  unfold : Type → Tm n → Tm n → Tm n               -- unfold A coalg seed: seed : A
  out    : Functor → Tm n → Tm n                   -- out F t: t : ν F _
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
ren ρ (lam t)        = lam (ren (extR ρ) t)
ren ρ (app A q t u)  = app A q (ren ρ t) (ren ρ u)
ren ρ (let′ A q t u) = let′ A q (ren ρ t) (ren (extR ρ) u)
ren ρ unit           = unit
ren ρ (pair t u)     = pair (ren ρ t) (ren ρ u)
ren ρ (fst B t)      = fst B (ren ρ t)
ren ρ (snd A t)      = snd A (ren ρ t)
ren ρ (inl t)        = inl (ren ρ t)
ren ρ (inr t)        = inr (ren ρ t)
ren ρ (case A B qℓ qr s l r) = case A B qℓ qr (ren ρ s) (ren (extR ρ) l) (ren (extR ρ) r)
ren ρ (absurd t)     = absurd (ren ρ t)
ren ρ (roll t)       = roll (ren ρ t)
ren ρ (fold F a t)   = fold F (ren ρ a) (ren ρ t)
ren ρ (unfold A c t) = unfold A (ren ρ c) (ren ρ t)
ren ρ (out F t)      = out F (ren ρ t)
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
sub σ (lam t)        = lam (sub (extS σ) t)
sub σ (app A q t u)  = app A q (sub σ t) (sub σ u)
sub σ (let′ A q t u) = let′ A q (sub σ t) (sub (extS σ) u)
sub σ unit           = unit
sub σ (pair t u)     = pair (sub σ t) (sub σ u)
sub σ (fst B t)      = fst B (sub σ t)
sub σ (snd A t)      = snd A (sub σ t)
sub σ (inl t)        = inl (sub σ t)
sub σ (inr t)        = inr (sub σ t)
sub σ (case A B qℓ qr s l r) = case A B qℓ qr (sub σ s) (sub (extS σ) l) (sub (extS σ) r)
sub σ (absurd t)     = absurd (sub σ t)
sub σ (roll t)       = roll (sub σ t)
sub σ (fold F a t)   = fold F (sub σ a) (sub σ t)
sub σ (unfold A c t) = unfold A (sub σ c) (sub σ t)
sub σ (out F t)      = out F (sub σ t)
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
  v-lam  : ∀ {t} → Value (lam t)
  v-unit : Value unit
  v-pair : ∀ {a b} → Value a → Value b → Value (pair a b)
  v-inl  : ∀ {a} → Value a → Value (inl a)
  v-inr  : ∀ {b} → Value b → Value (inr b)
  v-roll : ∀ {a} → Value a → Value (roll a)
