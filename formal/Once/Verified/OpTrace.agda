-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Verified.OpTrace — the OPERATIONAL trace semantics of the CCC IR
-- (solution 2: fire a SigOp event when it is EXECUTED).
--
-- WHY operational. The denotational `obs` (TraceDenote) denotes the
-- function type as a pure Agda function `⟦A ⇒ B⟧ = ⟦A⟧ → ⟦B⟧`, which has
-- no slot for a trace. So a `SigOp` inside an applied CLOSURE contributes
-- to the value (via `semM`) but its event is lost at `apply` — `obs` only
-- fires at `SigOp` nodes it structurally reaches through `∘`/`⟨,⟩`/`case`.
-- The MACHINE (`flat-events`) is operational and DOES fire inside closures
-- (a call jumps into the body and runs its `instr-sigop`s), so denotational
-- `obs` and the machine disagree for higher-order effects.
--
-- The fix: an operational interpreter over a value domain that
-- DEFUNCTIONALIZES arrows — a closure is `(IR body, captured env)` data
-- (like `SS.eval`'s `Vclos`), so `apply` can RUN the body and fire its
-- effects as they execute. Everything else is boxed as the denotational
-- `⟦_⟧` (no defunctionalization needed). This module defines the value
-- domain `OVal` and its forgetful coercion `ov→sem : OVal A → ⟦ A ⟧`; the
-- interpreter `otrace` follows.
--
-- This is the ground-truth observable the machine refines; the compositional
-- denotational layer (Plan 0.46) is proven ADEQUATE to it later.
------------------------------------------------------------------------

module Once.Verified.OpTrace where

open import Data.Unit using (⊤; tt)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Maybe using (Maybe; just; nothing; map)
open import Data.Empty using (⊥-elim)

open import Once.Type
  using (Type; Unit; Void; _*_; _+_; _⇒[_]_; μ-type; ν-type; Int; Float; Str; Buffer;
         mk-kind; Many; eff)
open import Once.CCC.IR
open import Once.CCC.Eval using (eval; ⟦_⟧)
open import Once.CCC.SigOp.Info using (SigOpInfo; mk-info; Emits)
open import Once.Verified.Trace using (SigOpEvent; mk-event)
open import Once.Verified.TraceDenote using (emit-eff)
open import Data.Product using (proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

------------------------------------------------------------------------
-- The operational value domain.
--
-- DEFUNCTIONALIZE the arrow (`ovClos` carries the closure's IR body + the
-- captured environment, with the capture context `Γ` existential), be
-- STRUCTURAL on product/sum (so nested arrows are still defunctionalized),
-- and BOX every first-order / base type as its denotational value `⟦_⟧`.
--
-- `Void` has no constructor — `OVal Void` is the empty type (no values),
-- which is exactly right. (Boxed `μ`/`ν` assume first-order functors — no
-- arrows inside the data; faithful for Layer-0. A higher-order functor
-- would need a structural `μ`/`ν` value; deferred.)
------------------------------------------------------------------------

data OVal : Type → Set where
  ovUnit : OVal Unit
  ovPair : ∀ {A B} → OVal A → OVal B → OVal (A * B)
  ovInl  : ∀ {A B} → OVal A → OVal (A + B)
  ovInr  : ∀ {A B} → OVal B → OVal (A + B)
  -- defunctionalized closure: body `IR (Γ * A) B` + captured env `OVal Γ`.
  ovClos : ∀ {Γ A B k} → IR (Γ * A) B → OVal Γ → OVal (A ⇒[ k ] B)
  -- boxed base / first-order values.
  ovInt  : ⟦ Int ⟧    → OVal Int
  ovFlt  : ⟦ Float ⟧  → OVal Float
  ovStr  : ⟦ Str ⟧    → OVal Str
  ovBuf  : ⟦ Buffer ⟧ → OVal Buffer
  ovMu   : ∀ {F} → ⟦ μ-type F ⟧ → OVal (μ-type F)
  ovNu   : ∀ {F} → ⟦ ν-type F ⟧ → OVal (ν-type F)

------------------------------------------------------------------------
-- Forgetful coercion to the denotational value. A closure forgets to the
-- Agda function that RUNS its body via `eval` (the denotational value side;
-- the trace it would emit is exactly what `otrace` keeps and `ov→sem`
-- discards). The boxed cases are the identity; the structural cases recurse.
------------------------------------------------------------------------

ov→sem : ∀ {A} → OVal A → ⟦ A ⟧
ov→sem ovUnit        = tt
ov→sem (ovPair a b)  = (ov→sem a , ov→sem b)
ov→sem (ovInl a)     = inj₁ (ov→sem a)
ov→sem (ovInr b)     = inj₂ (ov→sem b)
ov→sem (ovClos h γ)  = λ a → eval h (ov→sem γ , a)
ov→sem (ovInt v)     = v
ov→sem (ovFlt v)     = v
ov→sem (ovStr v)     = v
ov→sem (ovBuf v)     = v
ov→sem (ovMu v)      = v
ov→sem (ovNu v)      = v

------------------------------------------------------------------------
-- Reflect a denotational value back to `OVal` — PARTIAL: an arrow value is
-- an Agda function with no IR body to defunctionalize, so it has no `OVal`
-- (returns `nothing` = "outside the first-order model"). Total on the
-- first-order types, which is exactly where `SigOp`/`const` results live
-- (external primitives are first-order). Used to box those results.
------------------------------------------------------------------------

sem→ov? : ∀ {A} → ⟦ A ⟧ → Maybe (OVal A)
sem→ov? {Unit}        _        = just ovUnit
sem→ov? {Void}        ()
sem→ov? {A * B}       (a , b)  with sem→ov? a | sem→ov? b
... | just oa | just ob = just (ovPair oa ob)
... | _       | _       = nothing
sem→ov? {A + B}       (inj₁ a) = map ovInl (sem→ov? a)
sem→ov? {A + B}       (inj₂ b) = map ovInr (sem→ov? b)
sem→ov? {A ⇒[ k ] B}  _        = nothing
sem→ov? {Int}         v        = just (ovInt v)
sem→ov? {Float}       v        = just (ovFlt v)
sem→ov? {Str}         v        = just (ovStr v)
sem→ov? {Buffer}      v        = just (ovBuf v)
sem→ov? {μ-type F}    v        = just (ovMu v)
sem→ov? {ν-type F}    v        = just (ovNu v)

------------------------------------------------------------------------
-- The operational interpreter. Fuel-bounded (decrements on every recursive
-- call — `n = 0` is out-of-fuel `nothing`). Fires a SigOp event WHEN THE
-- SigOp EXECUTES, including inside an applied closure — the clause
--   otrace apply (ovPair (ovClos h γ) a) = otrace h (ovPair γ a)
-- RUNS the closure body, so its effects appear in order. (Pure-fn `obs`
-- could not do this; the machine, being operational, already does.)
--
-- WIP: the recursion-scheme constructors (In/Out/out-μ/in-ν/Ana/Cata/Para/
-- Hylo/Fuse) + `free-heap` are DEFERRED to the catch-all (`nothing`) — they
-- must fire their algebra/coalgebra effects operationally (the operational
-- cata fold is the next sub-step). This module is not yet imported anywhere,
-- so the placeholder is safe WIP.
------------------------------------------------------------------------

otrace : ∀ {A B} → ℕ → IR A B → OVal A → List SigOpEvent × Maybe (OVal B)
otrace zero    _              _                       = ([] , nothing)
otrace (suc n) id             x                       = ([] , just x)
otrace (suc n) (g ∘ f)        x with otrace n f x
... | (e₁ , nothing) = (e₁ , nothing)
... | (e₁ , just v)  with otrace n g v
...   | (e₂ , w) = (e₁ ++ e₂ , w)
otrace (suc n) fst            (ovPair a b)            = ([] , just a)
otrace (suc n) snd            (ovPair a b)            = ([] , just b)
otrace (suc n) (⟨ f , g ⟩ m)  x with otrace n f x
... | (e₁ , nothing) = (e₁ , nothing)
... | (e₁ , just a)  with otrace n g x
...   | (e₂ , nothing) = (e₁ ++ e₂ , nothing)
...   | (e₂ , just b)  = (e₁ ++ e₂ , just (ovPair a b))
otrace (suc n) (inl m)        x                       = ([] , just (ovInl x))
otrace (suc n) (inr m)        x                       = ([] , just (ovInr x))
otrace (suc n) (case f g)     (ovInl a)               = otrace n f a
otrace (suc n) (case f g)     (ovInr b)               = otrace n g b
otrace (suc n) terminal       x                       = ([] , just ovUnit)
otrace (suc n) (curry h m)    x                       = ([] , just (ovClos h x))
otrace (suc n) apply          (ovPair (ovClos h γ) a) = otrace n h (ovPair γ a)
otrace (suc n) arr            (ovClos h γ)            = ([] , just (ovClos h γ))
otrace (suc n) (SigOp si)     x                       =
  (emit-eff si (suc n) (ov→sem x) , sem→ov? (eval (SigOp si) (ov→sem x)))
otrace (suc n) (const f iv mv) x                      = ([] , sem→ov? mv)
otrace (suc n) ir             x                       = ([] , nothing)   -- recursion schemes / heap: deferred

------------------------------------------------------------------------
-- Non-vacuity / the POINT of solution 2: an effect INSIDE an applied
-- closure fires. `λ _ → tick ()` is `ovClos (SigOp tickInfo ∘ snd) ovUnit`;
-- applying it runs the body and emits the `io.tick` event. The denotational
-- `obs` returns `[]` here (its `apply`/`curry` clauses are value-pure) — this
-- is exactly the gap the operational semantics closes.
------------------------------------------------------------------------

tickInfo : SigOpInfo Unit Unit
tickInfo = mk-info "io.tick" (λ _ → tt) (λ _ → tt) (Emits refl)

op-apply-fires-closure-effect :
  proj₁ (otrace 5 (apply {k = mk-kind Many eff}) (ovPair (ovClos (SigOp tickInfo ∘ snd) ovUnit) ovUnit))
    ≡ mk-event "io.tick" nothing ∷ []
op-apply-fires-closure-effect = refl
