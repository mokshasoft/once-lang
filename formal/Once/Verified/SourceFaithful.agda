-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Verified.SourceFaithful — `faithful` (Plan 0.46 / OCP-0006, M3).
--
-- The elaborator is meaning-preserving: the denotation of the ELABORATED IR
-- agrees, pointwise in the observation depth, with THE source semantics `⟦_⟧ˢ`:
--
--     evalᴰ (elaborate Heap e) dγ k  ≡  ⟦ e ⟧ˢ dγ k
--
-- Both sides live in the SAME trace monad `T`, so this is a plain equality (no
-- `∃s`, no fuel, no `SS.eval`) — the OCP-0006 payoff. It is the elaborator-
-- load-bearing obligation under the apex (`SourceTrace.elaborate-faithful` is its
-- closed-`Unit` projection via `cong proj₁`).
--
-- TOP-DOWN: structural induction on `e`; each constructor is a hole the apex
-- demanded. Leaf cases (`unit`, the `semM`-routed arith/comparison, the
-- `evalᴰ`-routed `lift-morphism`) are near-definitional because `⟦_⟧ˢ` denotes
-- them through the SAME `semM`/`evalᴰ` the elaborated IR uses. Undischarged
-- constructors route to `faithful-todo` (an explicit obligation, NOT an island).
------------------------------------------------------------------------

module Once.Verified.SourceFaithful where

open import Data.Nat using (ℕ)
open import Data.List using (List; []; _++_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

open import Once.Type using (Type)
open import Once.Surface.Syntax using (Expr; Ctx; Usage)
open import Once.Surface.Elaborate using (elaborate; ⟦_⟧ᶜ)
open import Once.Verified.TraceMonad using (T)
open import Once.Verified.DenotTrace using (⟦_⟧ᴰ; evalᴰ)
import Once.Verified.SourceDenote as SD
import Once.Compile as C

open Once.Surface.Syntax.Expr

------------------------------------------------------------------------
-- The elaborator-faithfulness lemma (general — over any context/env, so the
-- induction can recurse into open subterms). Pointwise in the depth `k`.
------------------------------------------------------------------------

postulate
  -- TOP-DOWN HOLE (M3): the not-yet-discharged constructors. Each is an obligation
  -- the apex demands; discharge in place (leaf cases definitional via the shared
  -- semM/evalᴰ, composition cases via the IH + the monad-combinator reduction).
  faithful-todo :
    ∀ {n} {Γ : Ctx n} {Ψ : Usage n} {A} (e : Expr Γ Ψ A)
      (dγ : ⟦ ⟦ Γ ⟧ᶜ ⟧ᴰ) (k : ℕ)
    → evalᴰ (elaborate C.Heap e) dγ k ≡ SD.⟦ e ⟧ˢ dγ k

faithful :
  ∀ {n} {Γ : Ctx n} {Ψ : Usage n} {A} (e : Expr Γ Ψ A)
    (dγ : ⟦ ⟦ Γ ⟧ᶜ ⟧ᴰ) (k : ℕ)
  → evalᴰ (elaborate C.Heap e) dγ k ≡ SD.⟦ e ⟧ˢ dγ k
-- `unit` ↦ `terminal`; both sides reduce to `returnT tt` ⇒ refl.
faithful unit    dγ k = refl
faithful (int n) dγ k = refl   -- intLit's semM reduces to `absℤ n`, matching ⟦int n⟧ˢ
-- str: `str-lit-semM s tt` does NOT reduce to `s` definitionally → needs the
-- literal-semantics lemma (`str-lit-semM s tt ≡ s`); deferred to faithful-todo.
-- Single-subterm projections/injections: `elaborate (op e) = <prim> ∘ elaborate e`
-- and `⟦ op e ⟧ˢ = ⟦e⟧ˢ >>=T (λv → returnT (<prim> v))`; `_>>=T_` sees the same
-- depth on both sides, so the trace+value at `n` is a function of the SUBTERM's
-- (trace,value) at `n` — one `cong` over the IH (`faithful e`).
faithful (fst' e) dγ n = cong (λ r → (proj₁ r ++ [] , proj₁ (proj₂ r))) (faithful e dγ n)
faithful (snd' e) dγ n = cong (λ r → (proj₁ r ++ [] , proj₂ (proj₂ r))) (faithful e dγ n)
faithful (inl' e) dγ n = cong (λ r → (proj₁ r ++ [] , inj₁ (proj₂ r))) (faithful e dγ n)
faithful (inr' e) dγ n = cong (λ r → (proj₁ r ++ [] , inj₂ (proj₂ r))) (faithful e dγ n)
faithful e       dγ k = faithful-todo e dγ k
