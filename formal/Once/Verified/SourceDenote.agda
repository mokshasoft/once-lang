-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Verified.SourceDenote — `⟦_⟧ˢ`, THE source semantics (Plan 0.46 / OCP-0006).
--
-- The single anchor: a typed, FUEL-FREE, total+productive denotational trace
-- semantics directly over the intrinsically-typed surface `Expr` — independent of
-- `elaborate` (so the elaborator stays load-bearing: `⟦ elaborate e ⟧ᴰ ≡ ⟦ e ⟧ˢ`).
--
-- It is a structural fold of `Expr` into the SAME trace monad `T` that `⟦_⟧ᴰ`
-- (the IR view) targets — one meaning, two syntaxes. Totality is Agda's checker
-- (structural recursion on `Expr`); productivity is the `Ana` observation depth.
-- THERE IS NO FUEL: `T`'s `ℕ` is the event-observation depth (D058), consumed
-- only by `Ana`. A fuel parameter here would be a bug (it is how general recursion
-- leaked into the retired `SS.eval`).
--
-- TOP-DOWN (Plan 0.46): the effect/recursion constructors route, for now, to the
-- explicit `⟦⟧ˢ-todo` hole — each is an obligation the apex will demand, not an
-- island. Discharge them as the elaborate-correctness proof (M3) reaches them.
------------------------------------------------------------------------

module Once.Verified.SourceDenote where

open import Data.Fin using (Fin; zero; suc)
open import Data.Nat using (ℕ) renaming (_+_ to _+ℕ_; _∸_ to _∸ℕ_; _*_ to _*ℕ_)
open import Data.Integer using (ℤ) renaming (∣_∣ to absℤ)
open import Data.List using (List)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.String using (String)

open import Once.Type
  using (Type; Unit; Void; Int; Str; _*_; _+_; _⇒[_]_)
open import Once.Surface.Syntax using (Expr; Ctx; Usage; lookup; _,_^_; ∅)
open import Once.Surface.Elaborate using (⟦_⟧ᶜ)
open import Once.Verified.TraceMonad using (T; returnT; _>>=T_)
open import Once.Verified.DenotTrace using (⟦_⟧ᴰ)

open Once.Surface.Syntax.Expr

------------------------------------------------------------------------
-- Environment lookup: `⟦Γ⟧ᶜ` is the nested product (`∅ ↦ Unit`,
-- `Γ , A ↦ ⟦Γ⟧ᶜ * A`), so `⟦ ⟦Γ⟧ᶜ ⟧ᴰ` is `… × ⟦A⟧ᴰ`; de-Bruijn `zero`
-- is the most recent binding (`proj₂`), `suc i` recurses into `proj₁`.
------------------------------------------------------------------------

lookupᴰ : ∀ {n} (Γ : Ctx n) (i : Fin n) → ⟦ ⟦ Γ ⟧ᶜ ⟧ᴰ → ⟦ lookup Γ i ⟧ᴰ
lookupᴰ (Γ , A ^ q) zero    dγ = proj₂ dγ
lookupᴰ (Γ , A ^ q) (suc i) dγ = lookupᴰ Γ i (proj₁ dγ)

------------------------------------------------------------------------
-- THE SOURCE SEMANTICS. Structural on `Expr`; arrows are Kleisli arrows
-- into `T`; `apply`/`let`/`case` thread the trace via `_>>=T_`.
------------------------------------------------------------------------

postulate
  -- TOP-DOWN HOLE (Plan 0.46 M1): the effect (sigOp/closure/poly/effApp/lift-
  -- morphism/morph-app), comparison (lt..ne), div/mod, and recursion-scheme
  -- (cata/ana) constructors. Each is an explicit obligation the elaborate-
  -- correctness proof (M3) will demand; discharge in place, NOT as islands.
  ⟦⟧ˢ-todo : ∀ {n} {Γ : Ctx n} {Ψ : Usage n} {A} → Expr Γ Ψ A → ⟦ ⟦ Γ ⟧ᶜ ⟧ᴰ → T ⟦ A ⟧ᴰ

⟦_⟧ˢ : ∀ {n} {Γ : Ctx n} {Ψ : Usage n} {A}
     → Expr Γ Ψ A → ⟦ ⟦ Γ ⟧ᶜ ⟧ᴰ → T ⟦ A ⟧ᴰ
⟦ var {Γ = Γ} i ⟧ˢ dγ = returnT (lookupᴰ Γ i dγ)
⟦ lam q _ e ⟧ˢ    dγ = returnT (λ a → ⟦ e ⟧ˢ (dγ , a))
⟦ app f x ⟧ˢ      dγ = ⟦ f ⟧ˢ dγ >>=T λ vf → ⟦ x ⟧ˢ dγ >>=T λ vx → vf vx
⟦ pair a b ⟧ˢ     dγ = ⟦ a ⟧ˢ dγ >>=T λ va → ⟦ b ⟧ˢ dγ >>=T λ vb → returnT (va , vb)
⟦ fst' e ⟧ˢ       dγ = ⟦ e ⟧ˢ dγ >>=T λ v → returnT (proj₁ v)
⟦ snd' e ⟧ˢ       dγ = ⟦ e ⟧ˢ dγ >>=T λ v → returnT (proj₂ v)
⟦ inl' e ⟧ˢ       dγ = ⟦ e ⟧ˢ dγ >>=T λ v → returnT (inj₁ v)
⟦ inr' e ⟧ˢ       dγ = ⟦ e ⟧ˢ dγ >>=T λ v → returnT (inj₂ v)
⟦ case' s l r ⟧ˢ  dγ = ⟦ s ⟧ˢ dγ >>=T λ v →
                         [ (λ a → ⟦ l ⟧ˢ (dγ , a)) , (λ b → ⟦ r ⟧ˢ (dγ , b)) ]′ v
⟦ unit ⟧ˢ         dγ = returnT tt
⟦ absurd e ⟧ˢ     dγ = ⟦ e ⟧ˢ dγ >>=T λ v → ⊥-elim v
⟦ let' e1 e2 ⟧ˢ   dγ = ⟦ e1 ⟧ˢ dγ >>=T λ v1 → ⟦ e2 ⟧ˢ (dγ , v1)
⟦ int n ⟧ˢ        dγ = returnT (absℤ n)
⟦ str s ⟧ˢ        dγ = returnT s
⟦ add a b ⟧ˢ      dγ = ⟦ a ⟧ˢ dγ >>=T λ va → ⟦ b ⟧ˢ dγ >>=T λ vb → returnT (va +ℕ vb)
⟦ sub a b ⟧ˢ      dγ = ⟦ a ⟧ˢ dγ >>=T λ va → ⟦ b ⟧ˢ dγ >>=T λ vb → returnT (va ∸ℕ vb)
⟦ mul a b ⟧ˢ      dγ = ⟦ a ⟧ˢ dγ >>=T λ va → ⟦ b ⟧ˢ dγ >>=T λ vb → returnT (va *ℕ vb)
⟦ neg e ⟧ˢ        dγ = ⟦ e ⟧ˢ dγ >>=T λ v → returnT 0
⟦ arr' f ⟧ˢ       dγ = ⟦ f ⟧ˢ dγ
⟦ e ⟧ˢ            dγ = ⟦⟧ˢ-todo e dγ
