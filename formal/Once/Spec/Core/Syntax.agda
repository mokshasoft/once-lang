{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Spec.Core.Syntax — the core calculus's terms.
--
-- Well-scoped de Bruijn terms `Tm S m n`: `m` type variables, `n` term
-- variables, over the definitions signature `S` (the schemas of the earlier
-- definitions of the module; a module is a telescope). A term in its context
-- determines its type (Church style): `lam` carries its domain and its
-- arrow's grades, `inl`/`inr` the other summand, `absurd` its type, the
-- recursion formers their functor, `let′`/`case` the usages of their binders.
--
-- The categorical combinators (`id`, `compose`, `curry`, `cata`, `ana`, …)
-- are not formers: they are λ-terms over these (`Spec.Core.Derived`).
--
--   variables, arrows   var, lam, app, let′
--   Unit, ×, +, Void    unit, pair, fst, snd, inl, inr, case, absurd
--   μ F                 roll, fold                (initial algebra, its fold)
--   ν F π               unfold, out               (final coalgebra, its unfold)
--   Eff                 iter                      (guarded iteration: a server)
--   subtyping           coerce
--   numbers             lit, prim
--   the signature Σ     sigop                     (a declared constant or operation)
--   definitions         ref                       (an earlier definition at an instance)
------------------------------------------------------------------------

module Once.Spec.Core.Syntax where

open import Data.Nat using (ℕ; suc)
open import Data.Fin using (Fin; zero; suc)
open import Data.Integer using (ℤ)
open import Once.Spec.Float.Decimal using (Decimal)
open import Once.Spec.Name using (CanonicalName)
open import Once.Spec.Grade using (Quantity; Purity)
open import Once.Spec.Signature using (DeclType)
open import Once.Spec.Type using (Ty; Fun; KCtx; TySub; Unit; Int; Float; _*_; _+_; _⟨_⟩; _⟨_⟩F)

------------------------------------------------------------------------
-- The definitions signature: `∀ Δ. A` for each earlier definition
------------------------------------------------------------------------

record Schema : Set where
  constructor schema
  field
    arity : ℕ
    kinds : KCtx arity
    type  : Ty arity
open Schema

data Defs : ℕ → Set where
  []  : Defs 0
  _▷_ : ∀ {s} → Defs s → Schema → Defs (suc s)

infixl 5 _▷_

_!!_ : ∀ {s} → Defs s → Fin s → Schema
(S ▷ sc) !! zero  = sc
(S ▷ sc) !! suc d = S !! d

------------------------------------------------------------------------
-- Literals and the primitive operations on numbers
------------------------------------------------------------------------

data Lit : Set where
  lit-int   : ℤ → Lit
  lit-float : Decimal → Lit

data Prim : Set where
  p-add p-sub p-mul p-div p-mod p-neg : Prim
  p-lt p-le p-gt p-ge p-eq p-ne       : Prim
  p-fadd p-fsub p-fmul p-fdiv         : Prim
  p-i2f                               : Prim

primDom : ∀ {m} → Prim → Ty m
primDom p-neg  = Int
primDom p-i2f  = Int
primDom p-fadd = Float * Float
primDom p-fsub = Float * Float
primDom p-fmul = Float * Float
primDom p-fdiv = Float * Float
primDom p-add  = Int * Int
primDom p-sub  = Int * Int
primDom p-mul  = Int * Int
primDom p-div  = Int * Int
primDom p-mod  = Int * Int
primDom p-lt   = Int * Int
primDom p-le   = Int * Int
primDom p-gt   = Int * Int
primDom p-ge   = Int * Int
primDom p-eq   = Int * Int
primDom p-ne   = Int * Int

-- A comparison answers a `Bool = Unit + Unit`.
primCod : ∀ {m} → Prim → Ty m
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
-- Terms
------------------------------------------------------------------------

data Tm {s} (S : Defs s) (m : ℕ) : ℕ → Set where
  var     : ∀ {n} → Fin n → Tm S m n
  lam     : ∀ {n} → Ty m → Quantity → Purity → Tm S m (suc n) → Tm S m n
  app     : ∀ {n} → Tm S m n → Tm S m n → Tm S m n
  let′    : ∀ {n} → Quantity → Tm S m n → Tm S m (suc n) → Tm S m n
  unit    : ∀ {n} → Tm S m n
  pair    : ∀ {n} → Tm S m n → Tm S m n → Tm S m n
  fst snd : ∀ {n} → Tm S m n → Tm S m n
  inl inr : ∀ {n} → Ty m → Tm S m n → Tm S m n          -- inl B a : _ + B, inr A b : A + _
  case    : ∀ {n} → Quantity → Quantity → Tm S m n → Tm S m (suc n) → Tm S m (suc n) → Tm S m n
  absurd  : ∀ {n} → Ty m → Tm S m n → Tm S m n
  roll    : ∀ {n} → Fun m → Tm S m n → Tm S m n
  fold    : ∀ {n} → Fun m → Tm S m n → Tm S m n → Tm S m n     -- fold F algebra target
  unfold  : ∀ {n} → Fun m → Tm S m n → Tm S m n → Tm S m n     -- unfold F coalgebra seed
  out     : ∀ {n} → Tm S m n → Tm S m n
  iter    : ∀ {n} → Tm S m n → Tm S m n → Tm S m n             -- iter step seed
  coerce  : ∀ {n} → Ty m → Ty m → Tm S m n → Tm S m n          -- coerce A B t, along A <: B
  lit     : ∀ {n} → Lit → Tm S m n
  prim    : ∀ {n} → Prim → Tm S m n → Tm S m n
  sigop   : ∀ {n} → CanonicalName → DeclType → Tm S m n
  ref     : ∀ {n} (d : Fin s) → TySub (arity (S !! d)) m → Tm S m n

------------------------------------------------------------------------
-- Renaming: what moving a term under a binder does to it
------------------------------------------------------------------------

module _ {s} {S : Defs s} {m : ℕ} where

  ext : ∀ {n n′} → (Fin n → Fin n′) → Fin (suc n) → Fin (suc n′)
  ext ρ zero    = zero
  ext ρ (suc i) = suc (ρ i)

  ren : ∀ {n n′} → (Fin n → Fin n′) → Tm S m n → Tm S m n′
  ren ρ (var i)             = var (ρ i)
  ren ρ (lam A q π t)       = lam A q π (ren (ext ρ) t)
  ren ρ (app f x)           = app (ren ρ f) (ren ρ x)
  ren ρ (let′ q e b)        = let′ q (ren ρ e) (ren (ext ρ) b)
  ren ρ unit                = unit
  ren ρ (pair a b)          = pair (ren ρ a) (ren ρ b)
  ren ρ (fst p)             = fst (ren ρ p)
  ren ρ (snd p)             = snd (ren ρ p)
  ren ρ (inl B a)           = inl B (ren ρ a)
  ren ρ (inr A b)           = inr A (ren ρ b)
  ren ρ (case qℓ qr e l r)  = case qℓ qr (ren ρ e) (ren (ext ρ) l) (ren (ext ρ) r)
  ren ρ (absurd A e)        = absurd A (ren ρ e)
  ren ρ (roll F t)          = roll F (ren ρ t)
  ren ρ (fold F alg t)      = fold F (ren ρ alg) (ren ρ t)
  ren ρ (unfold F c a)      = unfold F (ren ρ c) (ren ρ a)
  ren ρ (out t)             = out (ren ρ t)
  ren ρ (iter f a)          = iter (ren ρ f) (ren ρ a)
  ren ρ (coerce A B t)      = coerce A B (ren ρ t)
  ren ρ (lit l)             = lit l
  ren ρ (prim p t)          = prim p (ren ρ t)
  ren ρ (sigop c t)         = sigop c t
  ren ρ (ref d τ)           = ref d τ

  wk : ∀ {n} → Tm S m n → Tm S m (suc n)
  wk = ren suc

------------------------------------------------------------------------
-- Substitution: what the laws of `let` and of polymorphism are stated with
------------------------------------------------------------------------

module _ {s} {S : Defs s} {m : ℕ} where

  exts : ∀ {n n′} → (Fin n → Tm S m n′) → Fin (suc n) → Tm S m (suc n′)
  exts σ zero    = var zero
  exts σ (suc i) = wk (σ i)

  subₜ : ∀ {n n′} → (Fin n → Tm S m n′) → Tm S m n → Tm S m n′
  subₜ σ (var i)             = σ i
  subₜ σ (lam A q π t)       = lam A q π (subₜ (exts σ) t)
  subₜ σ (app f x)           = app (subₜ σ f) (subₜ σ x)
  subₜ σ (let′ q e b)        = let′ q (subₜ σ e) (subₜ (exts σ) b)
  subₜ σ unit                = unit
  subₜ σ (pair a b)          = pair (subₜ σ a) (subₜ σ b)
  subₜ σ (fst p)             = fst (subₜ σ p)
  subₜ σ (snd p)             = snd (subₜ σ p)
  subₜ σ (inl B a)           = inl B (subₜ σ a)
  subₜ σ (inr A b)           = inr A (subₜ σ b)
  subₜ σ (case qℓ qr e l r)  = case qℓ qr (subₜ σ e) (subₜ (exts σ) l) (subₜ (exts σ) r)
  subₜ σ (absurd A e)        = absurd A (subₜ σ e)
  subₜ σ (roll F t)          = roll F (subₜ σ t)
  subₜ σ (fold F alg t)      = fold F (subₜ σ alg) (subₜ σ t)
  subₜ σ (unfold F c a)      = unfold F (subₜ σ c) (subₜ σ a)
  subₜ σ (out t)             = out (subₜ σ t)
  subₜ σ (iter f a)          = iter (subₜ σ f) (subₜ σ a)
  subₜ σ (coerce A B t)      = coerce A B (subₜ σ t)
  subₜ σ (lit l)             = lit l
  subₜ σ (prim p t)          = prim p (subₜ σ t)
  subₜ σ (sigop c t)         = sigop c t
  subₜ σ (ref d τ)           = ref d τ

  -- `t [ u ]`: the first variable replaced by `u`.
  _[_] : ∀ {n} → Tm S m (suc n) → Tm S m n → Tm S m n
  t [ u ] = subₜ (λ { zero → u ; (suc i) → var i }) t

-- Substituting TYPES: a term over `m` type variables at an instance over `k`.
_⟪_⟫ₜ : ∀ {s} {S : Defs s} {m k n} → Tm S m n → TySub m k → Tm S k n
var i             ⟪ σ ⟫ₜ = var i
lam A q π t       ⟪ σ ⟫ₜ = lam (A ⟨ σ ⟩) q π (t ⟪ σ ⟫ₜ)
app f x           ⟪ σ ⟫ₜ = app (f ⟪ σ ⟫ₜ) (x ⟪ σ ⟫ₜ)
let′ q e b        ⟪ σ ⟫ₜ = let′ q (e ⟪ σ ⟫ₜ) (b ⟪ σ ⟫ₜ)
unit              ⟪ σ ⟫ₜ = unit
pair a b          ⟪ σ ⟫ₜ = pair (a ⟪ σ ⟫ₜ) (b ⟪ σ ⟫ₜ)
fst p             ⟪ σ ⟫ₜ = fst (p ⟪ σ ⟫ₜ)
snd p             ⟪ σ ⟫ₜ = snd (p ⟪ σ ⟫ₜ)
inl B a           ⟪ σ ⟫ₜ = inl (B ⟨ σ ⟩) (a ⟪ σ ⟫ₜ)
inr A b           ⟪ σ ⟫ₜ = inr (A ⟨ σ ⟩) (b ⟪ σ ⟫ₜ)
case qℓ qr e l r  ⟪ σ ⟫ₜ = case qℓ qr (e ⟪ σ ⟫ₜ) (l ⟪ σ ⟫ₜ) (r ⟪ σ ⟫ₜ)
absurd A e        ⟪ σ ⟫ₜ = absurd (A ⟨ σ ⟩) (e ⟪ σ ⟫ₜ)
roll F t          ⟪ σ ⟫ₜ = roll (F ⟨ σ ⟩F) (t ⟪ σ ⟫ₜ)
fold F alg t      ⟪ σ ⟫ₜ = fold (F ⟨ σ ⟩F) (alg ⟪ σ ⟫ₜ) (t ⟪ σ ⟫ₜ)
unfold F c a      ⟪ σ ⟫ₜ = unfold (F ⟨ σ ⟩F) (c ⟪ σ ⟫ₜ) (a ⟪ σ ⟫ₜ)
out t             ⟪ σ ⟫ₜ = out (t ⟪ σ ⟫ₜ)
iter f a          ⟪ σ ⟫ₜ = iter (f ⟪ σ ⟫ₜ) (a ⟪ σ ⟫ₜ)
coerce A B t      ⟪ σ ⟫ₜ = coerce (A ⟨ σ ⟩) (B ⟨ σ ⟩) (t ⟪ σ ⟫ₜ)
lit l             ⟪ σ ⟫ₜ = lit l
prim p t          ⟪ σ ⟫ₜ = prim p (t ⟪ σ ⟫ₜ)
sigop c t         ⟪ σ ⟫ₜ = sigop c t
ref d τ           ⟪ σ ⟫ₜ = ref d (λ i → τ i ⟨ σ ⟩)
