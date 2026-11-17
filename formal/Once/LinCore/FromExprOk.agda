-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.LinCore.FromExprOk — plan 0.146 B1.7 step 2c (D456): THE BRIDGE'S
-- MEANING, against `elaborate`'s.
--
-- On related contexts, the core's meaning of `Lq e` (`Sem.Lᶜ`) is bisimilar,
-- up to the IR's value relation (`Bridge.W`), to master's meaning of
-- `elaborate e` (`evalᴰ`). By induction on `e`, clause for clause.
--
-- The context's plumbing is PURE on both sides: the core's `weak`, `split`,
-- `bindL`, `var-at` and the IR's `restrictEnv`, `projUsed`, `bindEnv` each
-- return a value at once (`Pure`, `PureI`), and the two values are related
-- (`weak-W`, `split-W`, …). Where the IR copies a context into two
-- restrictions (`⟨ f ∘ envˡ , g ∘ envʳ ⟩`), the core's split gives the same two
-- restrictions, linearly.
------------------------------------------------------------------------

{-# OPTIONS --guardedness #-}

open import Once.Spec.Numerics using (TargetNum)
open import Once.IR.Semantics.Trace using (FFIAnswers)

module Once.LinCore.FromExprOk (fmt : TargetNum) (ans : FFIAnswers) where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (_,_; fst; snd)
open import Data.Product using (_×_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)

import Once.Spec.Grade as G
open import Once.Spec.Type using (Ty)
import Once.Spec.Context as SC
open import Once.Spec.Context using (Ctx; Usage; []; _∷_; _+ᵘ_; _⊑ᵘ_; _⊑∷_)
open import Once.Context using (⟦_⟧ᶜ; _↾_; ⊑ᵘ-+ˡ; ⊑ᵘ-+ʳ; z≤z; z≤o; z≤m; o≤o; o≤m; m≤m)
open import Once.IRTy using (⌊_⌋)
import Once.IR as M
open import Once.Surface.Elaborate using (restrictEnv)
open import Once.Denotation.DenotTrace using (evalᴰ; CallEnv)
open import Once.Denotation.ValueDomain using (⟦_⟧ᴰᴵ)

open import Once.LinCore.Core fmt
open import Once.LinCore.NbEPLinCore fmt ans
open import Once.LinCore.FromExpr fmt using (ty; Co; weak; split; carryL; mixL; apω)
open import Once.LinCore.FromIR fmt using (⟪_⟫; grade)
import Once.LinCore.PassTr
open import Once.IRTy using (IRTy; _⇛[_]_)
import Once.IRTy as I
open import Once.LinCore.Bridge fmt ans using (W)
open import Once.LinCore.Bisim fmt ans using (_≈_; block≈; Bl-refl; ≈-refl; ≈-trans; ≈-sym; >>=-cong; _≈[_]_; ret≈R; >>=-congR; ≈-≈R; ≈R-≈; pair-drop)

------------------------------------------------------------------------
-- 1. THE MONAD: a bind of a return is its continuation, by `block`'s
-- definition.
------------------------------------------------------------------------

ret-bind : ∀ {X Y} {x : X} {k : X → T∞ Y} → (return∞ x >>=∞ k) ≈ k x
block≈ (ret-bind {x = x} {k = k}) = Bl-refl (block (k x))

-- a computation that returns at once, bound
bind-pure : ∀ {X Y} {m : T∞ X} {x : X} {k : X → T∞ Y} → m ≈ return∞ x → (m >>=∞ k) ≈ k x
bind-pure p = ≈-trans (>>=-cong p (λ _ → ≈-refl)) ret-bind

------------------------------------------------------------------------
-- 2. PURE TERMS: a term whose meaning returns a value at once.
------------------------------------------------------------------------

module _ {L : Cx} (δ : Env L) where

  Pure : ∀ {E A B} → Tm L E A B → (⟦ A ⟧ → ⟦ B ⟧) → Set
  Pure t v = ∀ e x → Lᶜ δ t e x ≈ return∞ (v x)

  p-id : ∀ {E A} → Pure (lid {A = A} {E}) (λ x → x)
  p-id e x = ≈-refl

  p-∘ : ∀ {E A B C} {f : Tm L E B C} {g : Tm L E A B} {u v} → Pure f u → Pure g v → Pure (f ∘l g) (λ x → u (v x))
  p-∘ pf pg e x = ≈-trans (bind-pure (pg e x)) (pf e _)

  p-⊗ : ∀ {E A B C D} {f : Tm L E A B} {g : Tm L E C D} {u v} → Pure f u → Pure g v
      → Pure (f ⊗l g) (λ x → u (fst x) , v (snd x))
  p-⊗ pf pg e (a , b) = ≈-trans (bind-pure (pf e a)) (bind-pure (pg e b))

  p-ρ : ∀ {E A} → Pure (ρl {A = A} {E}) fst
  p-ρ e (a , tt) = ≈-refl

  p-ρ⁻ : ∀ {E A} → Pure (ρl⁻ {A = A} {E}) (λ a → a , tt)
  p-ρ⁻ e a = ≈-refl

  p-lul : ∀ {E A} → Pure (lul {A = A} {E}) snd
  p-lul e (tt , a) = ≈-refl

  p-assoc : ∀ {E A B C} → Pure (lassoc {A = A} {B} {C} {E}) (λ x → fst (fst x) , (snd (fst x) , snd x))
  p-assoc e ((a , b) , c) = ≈-refl

  p-assoc⁻ : ∀ {E A B C} → Pure (lassoc⁻ {A = A} {B} {C} {E}) (λ x → (fst x , fst (snd x)) , snd (snd x))
  p-assoc⁻ e (a , (b , c)) = ≈-refl

  p-swap : ∀ {E A B} → Pure (lswap {A = A} {B} {E}) (λ x → snd x , fst x)
  p-swap e (a , b) = ≈-refl

  p-dup : ∀ {E A} → Pure (dup {A = A} {E}) (λ a → a , a)
  p-dup e a = ≈-refl

  p-drop : ∀ {E A} → Pure (drop {A = A} {E}) (λ _ → tt)
  p-drop e a = ≈-refl

------------------------------------------------------------------------
-- 3. PURE IR: the same on master's side.
------------------------------------------------------------------------

module _ (ρ : CallEnv) where

  PureI : ∀ {A B} → M.IR A B → (⟦ A ⟧ᴰᴵ → ⟦ B ⟧ᴰᴵ) → Set
  PureI t v = ∀ x → evalᴰ fmt ρ t x ≈ return∞ (v x)

  q-id : ∀ {A} → PureI (M.id {A}) (λ x → x)
  q-id x = ≈-refl

  q-∘ : ∀ {A B C} {f : M.IR B C} {g : M.IR A B} {u v} → PureI f u → PureI g v → PureI (f M.∘ g) (λ x → u (v x))
  q-∘ pf pg x = ≈-trans (bind-pure (pg x)) (pf _)

  q-pair : ∀ {A B C} {f : M.IR A B} {g : M.IR A C} {u v} → PureI f u → PureI g v → PureI M.⟨ f , g ⟩ (λ x → u x , v x)
  q-pair pf pg x = ≈-trans (bind-pure (pf x)) (bind-pure (pg x))

  q-fst : ∀ {A B} → PureI (M.fst {A} {B}) proj₁
  q-fst x = ≈-refl

  q-snd : ∀ {A B} → PureI (M.snd {A} {B}) proj₂
  q-snd x = ≈-refl

------------------------------------------------------------------------
-- 4. RESTRICTION: the core's drops against the IR's projections.
------------------------------------------------------------------------

-- the restriction's value on each side
wv : ∀ {m n} {Γ : Ctx m n} {Ψ Ψ′ : Usage n} → Ψ ⊑ᵘ Ψ′ → ⟦ Co Γ Ψ′ ⟧ → ⟦ Co Γ Ψ ⟧
wv {Γ = SC.∅}       []         x       = x
wv {Γ = Γ SC.▸ A} (z≤z ⊑∷ p) x       = wv {Γ = Γ} p x
wv {Γ = Γ SC.▸ A} (z≤o ⊑∷ p) (x , a) = wv {Γ = Γ} p x
wv {Γ = Γ SC.▸ A} (z≤m ⊑∷ p) (x , a) = wv {Γ = Γ} p x
wv {Γ = Γ SC.▸ A} (o≤o ⊑∷ p) (x , a) = wv {Γ = Γ} p x , a
wv {Γ = Γ SC.▸ A} (o≤m ⊑∷ p) (x , a) = wv {Γ = Γ} p x , a
wv {Γ = Γ SC.▸ A} (m≤m ⊑∷ p) (x , a) = wv {Γ = Γ} p x , a

rv : ∀ {m n} {Γ : Ctx m n} {Ψ Ψ′ : Usage n} → Ψ ⊑ᵘ Ψ′ → ⟦ ⌊ ⟦ Γ ↾ Ψ′ ⟧ᶜ ⌋ ⟧ᴰᴵ → ⟦ ⌊ ⟦ Γ ↾ Ψ ⟧ᶜ ⌋ ⟧ᴰᴵ
rv {Γ = SC.∅}       []         x = x
rv {Γ = Γ SC.▸ A} (z≤z ⊑∷ p) x = rv {Γ = Γ} p x
rv {Γ = Γ SC.▸ A} (z≤o ⊑∷ p) x = rv {Γ = Γ} p (proj₁ x)
rv {Γ = Γ SC.▸ A} (z≤m ⊑∷ p) x = rv {Γ = Γ} p (proj₁ x)
rv {Γ = Γ SC.▸ A} (o≤o ⊑∷ p) x = rv {Γ = Γ} p (proj₁ x) , proj₂ x
rv {Γ = Γ SC.▸ A} (o≤m ⊑∷ p) x = rv {Γ = Γ} p (proj₁ x) , proj₂ x
rv {Γ = Γ SC.▸ A} (m≤m ⊑∷ p) x = rv {Γ = Γ} p (proj₁ x) , proj₂ x

module _ {L : Cx} (δ : Env L) where

  weak-pure : ∀ {E m n} {Γ : Ctx m n} {Ψ Ψ′ : Usage n} (p : Ψ ⊑ᵘ Ψ′) → Pure δ (weak {L} {E} {Γ = Γ} p) (wv {Γ = Γ} p)
  weak-pure {Γ = SC.∅}       []         e x       = ≈-refl
  weak-pure {Γ = Γ SC.▸ A} (z≤z ⊑∷ p) e x       = weak-pure {Γ = Γ} p e x
  weak-pure {Γ = Γ SC.▸ A} (z≤o ⊑∷ p) e (x , a) = bind-pure (≈-trans (bind-pure (weak-pure {Γ = Γ} p e x)) ret-bind)
  weak-pure {Γ = Γ SC.▸ A} (z≤m ⊑∷ p) e (x , a) = bind-pure (≈-trans (bind-pure (weak-pure {Γ = Γ} p e x)) ret-bind)
  weak-pure {Γ = Γ SC.▸ A} (o≤o ⊑∷ p) e (x , a) = ≈-trans (bind-pure (weak-pure {Γ = Γ} p e x)) ret-bind
  weak-pure {Γ = Γ SC.▸ A} (o≤m ⊑∷ p) e (x , a) = ≈-trans (bind-pure (weak-pure {Γ = Γ} p e x)) ret-bind
  weak-pure {Γ = Γ SC.▸ A} (m≤m ⊑∷ p) e (x , a) = ≈-trans (bind-pure (weak-pure {Γ = Γ} p e x)) ret-bind

module _ (ρ : CallEnv) (am : M.AllocMode) where

  restrict-pure : ∀ {m n} {Γ : Ctx m n} {Ψ Ψ′ : Usage n} (p : Ψ ⊑ᵘ Ψ′) → PureI ρ (restrictEnv {Γ = Γ} am p) (rv {Γ = Γ} p)
  restrict-pure {Γ = SC.∅}       []         x = ≈-refl
  restrict-pure {Γ = Γ SC.▸ A} (z≤z ⊑∷ p) x = restrict-pure {Γ = Γ} p x
  restrict-pure {Γ = Γ SC.▸ A} (z≤o ⊑∷ p) x = ≈-trans ret-bind (restrict-pure {Γ = Γ} p (proj₁ x))
  restrict-pure {Γ = Γ SC.▸ A} (z≤m ⊑∷ p) x = ≈-trans ret-bind (restrict-pure {Γ = Γ} p (proj₁ x))
  restrict-pure {Γ = Γ SC.▸ A} (o≤o ⊑∷ p) x = ≈-trans (bind-pure (≈-trans ret-bind (restrict-pure {Γ = Γ} p (proj₁ x)))) ret-bind
  restrict-pure {Γ = Γ SC.▸ A} (o≤m ⊑∷ p) x = ≈-trans (bind-pure (≈-trans ret-bind (restrict-pure {Γ = Γ} p (proj₁ x)))) ret-bind
  restrict-pure {Γ = Γ SC.▸ A} (m≤m ⊑∷ p) x = ≈-trans (bind-pure (≈-trans ret-bind (restrict-pure {Γ = Γ} p (proj₁ x)))) ret-bind

-- ★ the two restrictions' values are related
weak-W : ∀ {m n} {Γ : Ctx m n} {Ψ Ψ′ : Usage n} (p : Ψ ⊑ᵘ Ψ′) {x x′}
       → W ⌊ ⟦ Γ ↾ Ψ′ ⟧ᶜ ⌋ x x′ → W ⌊ ⟦ Γ ↾ Ψ ⟧ᶜ ⌋ (wv {Γ = Γ} p x) (rv {Γ = Γ} p x′)
weak-W {Γ = SC.∅}       []         w        = w
weak-W {Γ = Γ SC.▸ A} (z≤z ⊑∷ p) w        = weak-W {Γ = Γ} p w
weak-W {Γ = Γ SC.▸ A} (z≤o ⊑∷ p) (w , _)  = weak-W {Γ = Γ} p w
weak-W {Γ = Γ SC.▸ A} (z≤m ⊑∷ p) (w , _)  = weak-W {Γ = Γ} p w
weak-W {Γ = Γ SC.▸ A} (o≤o ⊑∷ p) (w , wa) = weak-W {Γ = Γ} p w , wa
weak-W {Γ = Γ SC.▸ A} (o≤m ⊑∷ p) (w , wa) = weak-W {Γ = Γ} p w , wa
weak-W {Γ = Γ SC.▸ A} (m≤m ⊑∷ p) (w , wa) = weak-W {Γ = Γ} p w , wa

------------------------------------------------------------------------
-- 5. ★ THE SPLIT: its two halves are the IR's two restrictions.
------------------------------------------------------------------------

-- the split's value: the two halves
sv : ∀ {m n} (Γ : Ctx m n) (Ψ₁ Ψ₂ : Usage n) → ⟦ Co Γ (Ψ₁ +ᵘ Ψ₂) ⟧ → ⟦ Co Γ Ψ₁ ⟧ × ⟦ Co Γ Ψ₂ ⟧
sv SC.∅          []          []          x       = x , tt
sv (Γ SC.▸ A) (G.Zero ∷ Ψ₁) (G.Zero ∷ Ψ₂) x       = sv Γ Ψ₁ Ψ₂ x
sv (Γ SC.▸ A) (G.Zero ∷ Ψ₁) (G.One  ∷ Ψ₂) (x , a) = fst (sv Γ Ψ₁ Ψ₂ x) , (snd (sv Γ Ψ₁ Ψ₂ x) , a)
sv (Γ SC.▸ A) (G.Zero ∷ Ψ₁) (G.Many ∷ Ψ₂) (x , a) = fst (sv Γ Ψ₁ Ψ₂ x) , (snd (sv Γ Ψ₁ Ψ₂ x) , a)
sv (Γ SC.▸ A) (G.One  ∷ Ψ₁) (G.Zero ∷ Ψ₂) (x , a) = (fst (sv Γ Ψ₁ Ψ₂ x) , a) , snd (sv Γ Ψ₁ Ψ₂ x)
sv (Γ SC.▸ A) (G.Many ∷ Ψ₁) (G.Zero ∷ Ψ₂) (x , a) = (fst (sv Γ Ψ₁ Ψ₂ x) , a) , snd (sv Γ Ψ₁ Ψ₂ x)
sv (Γ SC.▸ A) (G.One  ∷ Ψ₁) (G.One  ∷ Ψ₂) (x , a) = (fst (sv Γ Ψ₁ Ψ₂ x) , a) , (snd (sv Γ Ψ₁ Ψ₂ x) , a)
sv (Γ SC.▸ A) (G.One  ∷ Ψ₁) (G.Many ∷ Ψ₂) (x , a) = (fst (sv Γ Ψ₁ Ψ₂ x) , a) , (snd (sv Γ Ψ₁ Ψ₂ x) , a)
sv (Γ SC.▸ A) (G.Many ∷ Ψ₁) (G.One  ∷ Ψ₂) (x , a) = (fst (sv Γ Ψ₁ Ψ₂ x) , a) , (snd (sv Γ Ψ₁ Ψ₂ x) , a)
sv (Γ SC.▸ A) (G.Many ∷ Ψ₁) (G.Many ∷ Ψ₂) (x , a) = (fst (sv Γ Ψ₁ Ψ₂ x) , a) , (snd (sv Γ Ψ₁ Ψ₂ x) , a)

module _ {L : Cx} (δ : Env L) {E : LTy} where

  carry-pure : ∀ {X Y Z} (e : ⟦ E ⟧) (v : ⟦ (X ⊗t Y) ⊗t Z ⟧)
             → Lᶜ δ (carryL {L} {E} {X} {Y} {Z}) e v ≈ return∞ ((fst (fst v) , snd v) , snd (fst v))
  carry-pure e ((l , r) , a) = bind-pure (≈-trans ret-bind (≈-trans ret-bind ret-bind))

  mix-pure : ∀ {X Y Z U} (e : ⟦ E ⟧) (v : ⟦ (X ⊗t Y) ⊗t (Z ⊗t U) ⟧)
           → Lᶜ δ (mixL {L} {E} {X} {Y} {Z} {U}) e v ≈ return∞ ((fst (fst v) , fst (snd v)) , (snd (fst v) , snd (snd v)))
  mix-pure e ((x , y) , (z , w)) =
    bind-pure (≈-trans ret-bind (≈-trans ret-bind (bind-pure (bind-pure (≈-trans ret-bind (≈-trans ret-bind ret-bind))))))

  split-pure : ∀ {m n} (Γ : Ctx m n) (Ψ₁ Ψ₂ : Usage n) → Pure δ (split {L} {E} Γ Ψ₁ Ψ₂) (sv Γ Ψ₁ Ψ₂)
  split-pure SC.∅          []          []          e x       = ≈-refl
  split-pure (Γ SC.▸ A) (G.Zero ∷ Ψ₁) (G.Zero ∷ Ψ₂) e x       = split-pure Γ Ψ₁ Ψ₂ e x
  split-pure (Γ SC.▸ A) (G.Zero ∷ Ψ₁) (G.One  ∷ Ψ₂) e (x , a) = bind-pure (≈-trans (bind-pure (split-pure Γ Ψ₁ Ψ₂ e x)) ret-bind)
  split-pure (Γ SC.▸ A) (G.Zero ∷ Ψ₁) (G.Many ∷ Ψ₂) e (x , a) = bind-pure (≈-trans (bind-pure (split-pure Γ Ψ₁ Ψ₂ e x)) ret-bind)
  split-pure (Γ SC.▸ A) (G.One  ∷ Ψ₁) (G.Zero ∷ Ψ₂) e (x , a) =
    ≈-trans (bind-pure (≈-trans (bind-pure (split-pure Γ Ψ₁ Ψ₂ e x)) ret-bind)) (carry-pure {X = Co Γ Ψ₁} {Y = Co Γ Ψ₂} {Z = ty A} e _)
  split-pure (Γ SC.▸ A) (G.Many ∷ Ψ₁) (G.Zero ∷ Ψ₂) e (x , a) =
    ≈-trans (bind-pure (≈-trans (bind-pure (split-pure Γ Ψ₁ Ψ₂ e x)) ret-bind)) (carry-pure {X = Co Γ Ψ₁} {Y = Co Γ Ψ₂} {Z = ty A} e _)
  split-pure (Γ SC.▸ A) (G.One  ∷ Ψ₁) (G.One  ∷ Ψ₂) e (x , a) =
    ≈-trans (bind-pure (≈-trans (bind-pure (split-pure Γ Ψ₁ Ψ₂ e x)) ret-bind)) (mix-pure {X = Co Γ Ψ₁} {Y = Co Γ Ψ₂} {Z = ty A} {U = ty A} e _)
  split-pure (Γ SC.▸ A) (G.One  ∷ Ψ₁) (G.Many ∷ Ψ₂) e (x , a) =
    ≈-trans (bind-pure (≈-trans (bind-pure (split-pure Γ Ψ₁ Ψ₂ e x)) ret-bind)) (mix-pure {X = Co Γ Ψ₁} {Y = Co Γ Ψ₂} {Z = ty A} {U = ty A} e _)
  split-pure (Γ SC.▸ A) (G.Many ∷ Ψ₁) (G.One  ∷ Ψ₂) e (x , a) =
    ≈-trans (bind-pure (≈-trans (bind-pure (split-pure Γ Ψ₁ Ψ₂ e x)) ret-bind)) (mix-pure {X = Co Γ Ψ₁} {Y = Co Γ Ψ₂} {Z = ty A} {U = ty A} e _)
  split-pure (Γ SC.▸ A) (G.Many ∷ Ψ₁) (G.Many ∷ Ψ₂) e (x , a) =
    ≈-trans (bind-pure (≈-trans (bind-pure (split-pure Γ Ψ₁ Ψ₂ e x)) ret-bind)) (mix-pure {X = Co Γ Ψ₁} {Y = Co Γ Ψ₂} {Z = ty A} {U = ty A} e _)

-- ★ each half is the IR's restriction to its side (`elaborate`'s `envˡ`, `envʳ`)
split-W : ∀ {m n} (Γ : Ctx m n) (Ψ₁ Ψ₂ : Usage n) {x x′} → W ⌊ ⟦ Γ ↾ (Ψ₁ +ᵘ Ψ₂) ⟧ᶜ ⌋ x x′
        → W ⌊ ⟦ Γ ↾ Ψ₁ ⟧ᶜ ⌋ (fst (sv Γ Ψ₁ Ψ₂ x)) (rv {Γ = Γ} (⊑ᵘ-+ˡ Ψ₁ Ψ₂) x′)
        × W ⌊ ⟦ Γ ↾ Ψ₂ ⟧ᶜ ⌋ (snd (sv Γ Ψ₁ Ψ₂ x)) (rv {Γ = Γ} (⊑ᵘ-+ʳ Ψ₁ Ψ₂) x′)
split-W SC.∅          []          []          w        = tt , tt
split-W (Γ SC.▸ A) (G.Zero ∷ Ψ₁) (G.Zero ∷ Ψ₂) w        = split-W Γ Ψ₁ Ψ₂ w
split-W (Γ SC.▸ A) (G.Zero ∷ Ψ₁) (G.One  ∷ Ψ₂) (w , wa) = proj₁ (split-W Γ Ψ₁ Ψ₂ w) , (proj₂ (split-W Γ Ψ₁ Ψ₂ w) , wa)
split-W (Γ SC.▸ A) (G.Zero ∷ Ψ₁) (G.Many ∷ Ψ₂) (w , wa) = proj₁ (split-W Γ Ψ₁ Ψ₂ w) , (proj₂ (split-W Γ Ψ₁ Ψ₂ w) , wa)
split-W (Γ SC.▸ A) (G.One  ∷ Ψ₁) (G.Zero ∷ Ψ₂) (w , wa) = (proj₁ (split-W Γ Ψ₁ Ψ₂ w) , wa) , proj₂ (split-W Γ Ψ₁ Ψ₂ w)
split-W (Γ SC.▸ A) (G.Many ∷ Ψ₁) (G.Zero ∷ Ψ₂) (w , wa) = (proj₁ (split-W Γ Ψ₁ Ψ₂ w) , wa) , proj₂ (split-W Γ Ψ₁ Ψ₂ w)
split-W (Γ SC.▸ A) (G.One  ∷ Ψ₁) (G.One  ∷ Ψ₂) (w , wa) = (proj₁ (split-W Γ Ψ₁ Ψ₂ w) , wa) , (proj₂ (split-W Γ Ψ₁ Ψ₂ w) , wa)
split-W (Γ SC.▸ A) (G.One  ∷ Ψ₁) (G.Many ∷ Ψ₂) (w , wa) = (proj₁ (split-W Γ Ψ₁ Ψ₂ w) , wa) , (proj₂ (split-W Γ Ψ₁ Ψ₂ w) , wa)
split-W (Γ SC.▸ A) (G.Many ∷ Ψ₁) (G.One  ∷ Ψ₂) (w , wa) = (proj₁ (split-W Γ Ψ₁ Ψ₂ w) , wa) , (proj₂ (split-W Γ Ψ₁ Ψ₂ w) , wa)
split-W (Γ SC.▸ A) (G.Many ∷ Ψ₁) (G.Many ∷ Ψ₂) (w , wa) = (proj₁ (split-W Γ Ψ₁ Ψ₂ w) , wa) , (proj₂ (split-W Γ Ψ₁ Ψ₂ w) , wa)

------------------------------------------------------------------------
-- 6. ★ RELATED TERMS: a core term and an IR term mean related
-- computations on related inputs.
------------------------------------------------------------------------

module Rel {L : Cx} (δ : Env L) (ρ : CallEnv) where

  Rel : ∀ {A B : IRTy} → LTm L ⟪ A ⟫ ⟪ B ⟫ → M.IR A B → Set
  Rel {A} {B} t t′ = ∀ {x x′} → W A x x′ → Lᶜ δ t tt x ≈[ W B ] evalᴰ fmt ρ t′ x′

  rel-∘ : ∀ {A B C} {f : LTm L ⟪ B ⟫ ⟪ C ⟫} {f′ : M.IR B C} {g : LTm L ⟪ A ⟫ ⟪ B ⟫} {g′ : M.IR A B}
        → Rel f f′ → Rel g g′ → Rel (f ∘l g) (f′ M.∘ g′)
  rel-∘ rf rg w = >>=-congR (rg w) rf

  -- pure on both sides, with related values
  rel-pure : ∀ {A B} {t : LTm L ⟪ A ⟫ ⟪ B ⟫} {t′ : M.IR A B} {v v′}
           → Pure δ t v → PureI ρ t′ v′ → (∀ {x x′} → W A x x′ → W B (v x) (v′ x′)) → Rel t t′
  rel-pure p q r {x} {x′} w = ≈-≈R (p tt x) (≈R-≈ (ret≈R (r w)) (≈-sym (q x′)))

  rel-weak : ∀ (am : M.AllocMode) {m n} {Γ : Ctx m n} {Ψ Ψ′ : Usage n} (p : Ψ ⊑ᵘ Ψ′)
           → Rel (weak {Γ = Γ} p) (restrictEnv {Γ = Γ} am p)
  rel-weak am {Γ = Γ} p = rel-pure {t = weak {Γ = Γ} p} {t′ = restrictEnv {Γ = Γ} am p} (weak-pure δ {E = One} {Γ = Γ} p) (restrict-pure ρ am {Γ = Γ} p) (weak-W {Γ = Γ} p)

  -- ★ the application: a closure applied owned, against `apply`
  rel-apω : ∀ {π A B} → Rel (apω {g = grade π} {⟪ A ⟫} {⟪ B ⟫}) (M.apply {A} {B} {π})
  rel-apω {π} {A} {B} {x = f , a} {x′ = f′ , a′} (wf , wa) =
    ≈-≈R (pair-drop (f ,_) (Lᶜ δ (Once.LinCore.PassTr.dropl fmt {Γ = L} {E = One} {A = Fn many (grade π) ⟪ A ⟫ ⟪ B ⟫} {B = ⟪ B ⟫}) tt) (λ _ → refl)) (wf wa)

  -- ★ THE SPLIT against the IR's copy into two restrictions
  rel-pair : ∀ (am : M.AllocMode) {m n} (Γ : Ctx m n) (Ψ₁ Ψ₂ : Usage n) {A B : IRTy}
             {a : LTm L (Co Γ Ψ₁) ⟪ A ⟫} {a′ : M.IR ⌊ ⟦ Γ ↾ Ψ₁ ⟧ᶜ ⌋ A}
             {b : LTm L (Co Γ Ψ₂) ⟪ B ⟫} {b′ : M.IR ⌊ ⟦ Γ ↾ Ψ₂ ⟧ᶜ ⌋ B}
           → Rel a a′ → Rel b b′
           → Rel ((a ⊗l b) ∘l split Γ Ψ₁ Ψ₂)
                 M.⟨ a′ M.∘ restrictEnv {Γ = Γ} am (⊑ᵘ-+ˡ Ψ₁ Ψ₂) , b′ M.∘ restrictEnv {Γ = Γ} am (⊑ᵘ-+ʳ Ψ₁ Ψ₂) ⟩
  rel-pair am Γ Ψ₁ Ψ₂ ra rb {x} {x′} w =
    ≈-≈R (bind-pure (split-pure δ Γ Ψ₁ Ψ₂ tt x))
      (≈R-≈ (>>=-congR (ra (proj₁ sw)) (λ r → >>=-congR (rb (proj₂ sw)) (λ r′ → ret≈R (r , r′))))
            (≈-sym (>>=-cong (bind-pure (restrict-pure ρ am {Γ = Γ} (⊑ᵘ-+ˡ Ψ₁ Ψ₂) x′))
                             (λ _ → >>=-cong (bind-pure (restrict-pure ρ am {Γ = Γ} (⊑ᵘ-+ʳ Ψ₁ Ψ₂) x′)) (λ _ → ≈-refl)))))
    where sw = split-W Γ Ψ₁ Ψ₂ w
