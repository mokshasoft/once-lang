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
open import Relation.Binary.PropositionalEquality using (cong; subst; sym)
open import Agda.Builtin.Sigma using (Σ; _,_; fst; snd)
open import Data.Product using (_×_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
import Data.Sum.Relation.Binary.Pointwise

import Once.Spec.Grade as G
open import Once.Spec.Type using (Ty; Type; _⇒[_]_; _+_; μ; ν; WFFun; KCtx; Fun)
import Once.Spec.Type as ST
import Once.Spec.Context as SC
open import Once.Spec.Context using (Ctx; Usage; []; _∷_; _+ᵘ_; _*ᵘ_; _⊑ᵘ_; _⊑∷_; singleUse)
open import Once.Context using (⟦_⟧ᶜ; _↾_; ⊑ᵘ-+ˡ; ⊑ᵘ-+ʳ; ⊑ᵘ-trans; ⊑ᵘ-*One; ⊑ᵘ-*Many; z≤z; z≤o; z≤m; o≤o; o≤m; m≤m)
open import Once.IRTy using (⌊_⌋)
import Once.IR as M
open import Once.Surface.Elaborate using (restrictEnv; projUsed; bindEnv; elaborate; numIR; sigOpIR; distribute; distribIR)
open import Once.Arith.SigOp.Builders using (numInfo; value-info; arrow-info)
open import Once.SigOp.Info using (SigOpInfo; module SigOpInfo)
import Once.Spec.Theory as Th
open import Once.IRTy using (⌊wk₀⌋)
open import Once.Type.Concrete using (con-base; con-fun)
open import Once.Surface.Syntax
open import Once.Surface.Map using (Map)
open import Once.Spec.Sub using (_<:_; sub-void; sub-var; sub-unit; sub-int; sub-float; sub-arr; sub-*; sub-+; sub-μ; sub-ν)
open import Once.Surface.CoerceIR using (coeIR; runCoe-dec; voidFree?; erase-eq; VoidFree)
open import Relation.Nullary using (Dec; yes; no)
open import Once.Spec.Theory using (Has; Sym; symDom)
open import Once.Type.Concrete using (IsConcrete)
open import Once.Spec.Name using (CanonicalName)
open import Data.String using (String)
import Data.Fin
open import Once.Denotation.DenotTrace using (evalᴰ; CallEnv; callEnv)
open import Once.Denotation.ValueDomain using (⟦_⟧ᴰᴵ)

open import Once.LinCore.Core fmt
open import Once.LinCore.NbEPLinCore fmt ans
open import Once.LinCore.FromExpr fmt using (ty; Co; weak; split; carryL; mixL; apω; var-at; bindL; Rs; Lq; castΦ; opL; numL; sigL; cast; clo; callM; refL; mapT; layerEq; dist; coeL; coeR)
open import Once.Context using (_⊔ᵘ_; ⊑ᵘ-⊔ˡ; ⊑ᵘ-⊔ʳ)
open import Once.Surface.Map using (mp-id; mp-fst; mp-snd; mp-terminal; mp-inl; mp-inr; mp-initial; mp-apply; mp-In; mp-Out; mp-toFloat)
open import Once.TypeCheck.Table using (mapIR)
open import Once.IRTy using (⌊⟧T-commute; WellFormedFI; ⟦_⟧TI; μ-type; ν-type)
open import Once.IRTy.WF using (wf-⌊⌋)
open import Once.LinCore.FromIR fmt using (lf; ⟪⟫-TI)
open import Once.Arith.SigOp.Builders using (i2f-info)
open import Once.IR.Semantics.Trace using (unlinkedT)
open import Once.IR.Semantics.Iterative using (embed)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Once.IR.Ref using (refIR)
open import Once.Spec.Name using (bare)
open import Once.LinCore.FromIR fmt using (⟪⌊⌋⟫-flat)
open import Once.LinCore.Pass fmt ans using (ev)
open import Once.LinCore.Casts fmt ans using (casts)
import Once.LinCore.BridgeProof
open import Relation.Binary.PropositionalEquality using (subst₂; trans)
open import Once.Surface.Properties using (erase-arg-usage)
open import Once.LinCore.FromIR fmt using (⟪_⟫; grade)
import Once.LinCore.PassTr
open import Once.LinCore.PassTr fmt using (copyIn)
open import Once.LinCore.Grade fmt ans using (blk-coh)
open import Once.IRTy using (IRTy; _⇛[_]_)
import Once.IRTy as I
open import Once.LinCore.Bridge fmt ans using (W)
open import Once.LinCore.Bisim fmt ans using (_≈_; block≈; Bl; Bl-refl; ≈step; ≈call; ≈halt; ≈-refl; ≈-trans; ≈-sym; >>=-cong; _≈[_]_; ret≈R; >>=-congR; ≈-≈R; ≈R-≈; pair-drop; blockR; ≈haltR; iter-congR)
open import Data.Sum using (_⊎_; inj₁; inj₂)

------------------------------------------------------------------------
-- 1. THE MONAD: a bind of a return is its continuation, by `block`'s
-- definition.
------------------------------------------------------------------------

ret-bind : ∀ {X Y} {x : X} {k : X → T∞ Y} → (return∞ x >>=∞ k) ≈ k x
block≈ (ret-bind {x = x} {k = k}) = Bl-refl (block (k x))

-- the monad's associativity, block by block
mutual
  bind-assoc : ∀ {X Y Z} (m : T∞ X) (k : X → T∞ Y) (h : Y → T∞ Z) → ((m >>=∞ k) >>=∞ h) ≈ (m >>=∞ λ x → k x >>=∞ h)
  block≈ (bind-assoc m k h) = assocB (block m) k h

  assocB : ∀ {X Y Z} (b : T (X ⊎ T∞ X)) (k : X → T∞ Y) (h : Y → T∞ Z)
         → Bl (bindBlock (bindBlock b k) h) (bindBlock b (λ x → k x >>=∞ h))
  assocB (ret (inj₁ x)) k h = Bl-refl (bindBlock (block (k x)) h)
  assocB (ret (inj₂ m)) k h = ≈step (bind-assoc m k h)
  assocB (call s a c)   k h = ≈call (λ y → assocB (c y) k h)
  assocB (halt s a)     k h = ≈halt

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

  -- (a record, so that the two terms stay visible to unification)
  record Rel {A B : IRTy} (t : LTm L ⟪ A ⟫ ⟪ B ⟫) (t′ : M.IR A B) : Set where
    constructor mkRel
    field rel : ∀ {x x′} → W A x x′ → Lᶜ δ t tt x ≈[ W B ] evalᴰ fmt ρ t′ x′
  open Rel public

  rel-∘ : ∀ {A B C} {f : LTm L ⟪ B ⟫ ⟪ C ⟫} {f′ : M.IR B C} {g : LTm L ⟪ A ⟫ ⟪ B ⟫} {g′ : M.IR A B}
        → Rel f f′ → Rel g g′ → Rel (f ∘l g) (f′ M.∘ g′)
  rel-∘ rf rg = mkRel λ w → >>=-congR (rel rg w) (rel rf)

  -- pure on both sides, with related values
  rel-pure : ∀ {A B} {t : LTm L ⟪ A ⟫ ⟪ B ⟫} {t′ : M.IR A B} {v v′}
           → Pure δ t v → PureI ρ t′ v′ → (∀ {x x′} → W A x x′ → W B (v x) (v′ x′)) → Rel t t′
  rel-pure p q r = mkRel λ {x} {x′} w → ≈-≈R (p tt x) (≈R-≈ (ret≈R (r w)) (≈-sym (q x′)))

  rel-weak : ∀ (am : M.AllocMode) {m n} {Γ : Ctx m n} {Ψ Ψ′ : Usage n} (p : Ψ ⊑ᵘ Ψ′)
           → Rel (weak {Γ = Γ} p) (restrictEnv {Γ = Γ} am p)
  rel-weak am {Γ = Γ} p = rel-pure {t = weak {Γ = Γ} p} {t′ = restrictEnv {Γ = Γ} am p} (weak-pure δ {E = One} {Γ = Γ} p) (restrict-pure ρ am {Γ = Γ} p) (weak-W {Γ = Γ} p)

  -- ★ the application: a closure applied owned, against `apply`
  rel-apω : ∀ {π A B} → Rel (apω {g = grade π} {⟪ A ⟫} {⟪ B ⟫}) (M.apply {A} {B} {π})
  rel-apω {π} {A} {B} = mkRel λ { {f , a} {f′ , a′} (wf , wa) →
    ≈-≈R (pair-drop (f ,_) (Lᶜ δ (Once.LinCore.PassTr.dropl fmt {Γ = L} {E = One} {A = Fn many (grade π) ⟪ A ⟫ ⟪ B ⟫} {B = ⟪ B ⟫}) tt) (λ _ → refl)) (wf wa) }

  -- ★ THE SPLIT against the IR's copy into two restrictions
  rel-pair : ∀ (am : M.AllocMode) {m n} (Γ : Ctx m n) (Ψ₁ Ψ₂ : Usage n) {A B : IRTy}
             {a : LTm L (Co Γ Ψ₁) ⟪ A ⟫} {a′ : M.IR ⌊ ⟦ Γ ↾ Ψ₁ ⟧ᶜ ⌋ A}
             {b : LTm L (Co Γ Ψ₂) ⟪ B ⟫} {b′ : M.IR ⌊ ⟦ Γ ↾ Ψ₂ ⟧ᶜ ⌋ B}
           → Rel a a′ → Rel b b′
           → Rel ((a ⊗l b) ∘l split Γ Ψ₁ Ψ₂)
                 M.⟨ a′ M.∘ restrictEnv {Γ = Γ} am (⊑ᵘ-+ˡ Ψ₁ Ψ₂) , b′ M.∘ restrictEnv {Γ = Γ} am (⊑ᵘ-+ʳ Ψ₁ Ψ₂) ⟩
  rel-pair am Γ Ψ₁ Ψ₂ ra rb = mkRel λ {x} {x′} w → let sw = split-W Γ Ψ₁ Ψ₂ w in
    ≈-≈R (bind-pure (split-pure δ Γ Ψ₁ Ψ₂ tt x))
      (≈R-≈ (>>=-congR (rel ra (proj₁ sw)) (λ r → >>=-congR (rel rb (proj₂ sw)) (λ r′ → ret≈R (r , r′))))
            (≈-sym (>>=-cong (bind-pure (restrict-pure ρ am {Γ = Γ} (⊑ᵘ-+ˡ Ψ₁ Ψ₂) x′))
                             (λ _ → >>=-cong (bind-pure (restrict-pure ρ am {Γ = Γ} (⊑ᵘ-+ʳ Ψ₁ Ψ₂) x′)) (λ _ → ≈-refl)))))

------------------------------------------------------------------------
-- 7. A RESTRICTION THROUGH ANOTHER, and the application.
------------------------------------------------------------------------

rv-trans : ∀ {m n} {Γ : Ctx m n} {Ψ₁ Ψ₂ Ψ₃ : Usage n} (p : Ψ₁ ⊑ᵘ Ψ₂) (q : Ψ₂ ⊑ᵘ Ψ₃) (x : ⟦ ⌊ ⟦ Γ ↾ Ψ₃ ⟧ᶜ ⌋ ⟧ᴰᴵ)
         → rv {Γ = Γ} (⊑ᵘ-trans p q) x ≡ rv {Γ = Γ} p (rv {Γ = Γ} q x)
rv-trans {Γ = SC.∅}       []         []         x = refl
rv-trans {Γ = Γ SC.▸ A} (z≤z ⊑∷ p) (z≤z ⊑∷ q) x = rv-trans {Γ = Γ} p q x
rv-trans {Γ = Γ SC.▸ A} (z≤z ⊑∷ p) (z≤o ⊑∷ q) x = rv-trans {Γ = Γ} p q (proj₁ x)
rv-trans {Γ = Γ SC.▸ A} (z≤z ⊑∷ p) (z≤m ⊑∷ q) x = rv-trans {Γ = Γ} p q (proj₁ x)
rv-trans {Γ = Γ SC.▸ A} (z≤o ⊑∷ p) (o≤o ⊑∷ q) x = rv-trans {Γ = Γ} p q (proj₁ x)
rv-trans {Γ = Γ SC.▸ A} (z≤o ⊑∷ p) (o≤m ⊑∷ q) x = rv-trans {Γ = Γ} p q (proj₁ x)
rv-trans {Γ = Γ SC.▸ A} (z≤m ⊑∷ p) (m≤m ⊑∷ q) x = rv-trans {Γ = Γ} p q (proj₁ x)
rv-trans {Γ = Γ SC.▸ A} (o≤o ⊑∷ p) (o≤o ⊑∷ q) x = cong (_, proj₂ x) (rv-trans {Γ = Γ} p q (proj₁ x))
rv-trans {Γ = Γ SC.▸ A} (o≤o ⊑∷ p) (o≤m ⊑∷ q) x = cong (_, proj₂ x) (rv-trans {Γ = Γ} p q (proj₁ x))
rv-trans {Γ = Γ SC.▸ A} (o≤m ⊑∷ p) (m≤m ⊑∷ q) x = cong (_, proj₂ x) (rv-trans {Γ = Γ} p q (proj₁ x))
rv-trans {Γ = Γ SC.▸ A} (m≤m ⊑∷ p) (m≤m ⊑∷ q) x = cong (_, proj₂ x) (rv-trans {Γ = Γ} p q (proj₁ x))

module _ (ρ : CallEnv) (am : M.AllocMode) where

  -- the IR restricted through a composite, as through its two parts
  restrict-trans : ∀ {m n} {Γ : Ctx m n} {Ψ₁ Ψ₂ Ψ₃ : Usage n} (p : Ψ₁ ⊑ᵘ Ψ₂) (q : Ψ₂ ⊑ᵘ Ψ₃) x
                 → evalᴰ fmt ρ (restrictEnv {Γ = Γ} am (⊑ᵘ-trans p q)) x ≈ evalᴰ fmt ρ (restrictEnv {Γ = Γ} am p M.∘ restrictEnv {Γ = Γ} am q) x
  restrict-trans {Γ = Γ} p q x =
    ≈-trans (restrict-pure ρ am {Γ = Γ} (⊑ᵘ-trans p q) x)
      (≈-trans (subst (λ v → return∞ (rv {Γ = Γ} (⊑ᵘ-trans p q) x) ≈ return∞ v) (rv-trans {Γ = Γ} p q x) ≈-refl)
        (≈-sym (≈-trans (bind-pure (restrict-pure ρ am {Γ = Γ} q x)) (restrict-pure ρ am {Γ = Γ} p (rv {Γ = Γ} q x)))))

  -- a term after two restrictions, as after their composite
  restrict-assoc : ∀ {m n} {Γ : Ctx m n} {Ψ₁ Ψ₂ Ψ₃ : Usage n} {B} (t : M.IR ⌊ ⟦ Γ ↾ Ψ₁ ⟧ᶜ ⌋ B) (p : Ψ₁ ⊑ᵘ Ψ₂) (q : Ψ₂ ⊑ᵘ Ψ₃) x
                 → evalᴰ fmt ρ ((t M.∘ restrictEnv {Γ = Γ} am p) M.∘ restrictEnv {Γ = Γ} am q) x
                   ≈ evalᴰ fmt ρ (t M.∘ restrictEnv {Γ = Γ} am (⊑ᵘ-trans p q)) x
  restrict-assoc {Γ = Γ} t p q x =
    ≈-trans (bind-pure (restrict-pure ρ am {Γ = Γ} q x))
      (≈-trans (bind-pure (restrict-pure ρ am {Γ = Γ} p (rv {Γ = Γ} q x)))
        (≈-sym (≈-trans (bind-pure (restrict-pure ρ am {Γ = Γ} (⊑ᵘ-trans p q) x))
                        (subst (λ v → evalᴰ fmt ρ t v ≈ evalᴰ fmt ρ t (rv {Γ = Γ} p (rv {Γ = Γ} q x))) (Relation.Binary.PropositionalEquality.sym (rv-trans {Γ = Γ} p q x)) ≈-refl))))

module RelApp {L : Cx} (δ : Env L) (ρ : CallEnv) (am : M.AllocMode) where
  open Rel δ ρ

  -- a rewrite on the IR's side
  rel-≈ʳ : ∀ {A B} {t : LTm L ⟪ A ⟫ ⟪ B ⟫} {t′ t″ : M.IR A B} → Rel t t′ → (∀ x′ → evalᴰ fmt ρ t′ x′ ≈ evalᴰ fmt ρ t″ x′) → Rel t t″
  rel-≈ʳ r e = mkRel λ {x} {x′} w → ≈R-≈ (rel r w) (e x′)

  -- the pairing an application and a combinator share: the context split, the
  -- right share relabelled
  rel-pairW : ∀ {m n} (Γ : Ctx m n) (Ψ₁ Ψ₂ Φ : Usage n) (p : Ψ₂ ⊑ᵘ Φ) {A B : IRTy}
                {f : LTm L (Co Γ Ψ₁) ⟪ B ⟫} {f′ : M.IR ⌊ ⟦ Γ ↾ Ψ₁ ⟧ᶜ ⌋ B}
                {x : LTm L (Co Γ Ψ₂) ⟪ A ⟫} {x′ : M.IR ⌊ ⟦ Γ ↾ Ψ₂ ⟧ᶜ ⌋ A}
            → Rel f f′ → Rel x x′
            → Rel ((f ⊗l (x ∘l weak {Γ = Γ} p)) ∘l split Γ Ψ₁ Φ)
                  M.⟨ f′ M.∘ restrictEnv {Γ = Γ} am (⊑ᵘ-+ˡ Ψ₁ Φ) , x′ M.∘ restrictEnv {Γ = Γ} am (⊑ᵘ-trans p (⊑ᵘ-+ʳ Ψ₁ Φ)) ⟩
  rel-pairW Γ Ψ₁ Ψ₂ Φ p {A} {x′ = x′} rf rx =
    rel-≈ʳ (rel-pair am Γ Ψ₁ Φ rf (rel-∘ rx (rel-weak am {Γ = Γ} p)))
           (λ v → >>=-cong ≈-refl (λ _ → >>=-cong (restrict-assoc ρ am {Γ = Γ} {B = A} x′ p (⊑ᵘ-+ʳ Ψ₁ Φ) v) (λ _ → ≈-refl)))

  -- ★ AN APPLICATION: the context split between the function and the argument,
  -- the argument's share relabelled (`q *ᵘ Ψ₂` to `Ψ₂`), against `elaborate`'s
  -- `apply ∘ ⟨ f ∘ restrict , x ∘ restrict ⟩`
  rel-app : ∀ {m n} (Γ : Ctx m n) (Ψ₁ Ψ₂ Φ : Usage n) (p : Ψ₂ ⊑ᵘ Φ) {π} {A B : IRTy}
              {f : LTm L (Co Γ Ψ₁) ⟪ A ⇛[ π ] B ⟫} {f′ : M.IR ⌊ ⟦ Γ ↾ Ψ₁ ⟧ᶜ ⌋ (A ⇛[ π ] B)}
              {x : LTm L (Co Γ Ψ₂) ⟪ A ⟫} {x′ : M.IR ⌊ ⟦ Γ ↾ Ψ₂ ⟧ᶜ ⌋ A}
          → Rel f f′ → Rel x x′
          → Rel (apω ∘l (f ⊗l (x ∘l weak {Γ = Γ} p)) ∘l split Γ Ψ₁ Φ)
                (M.apply M.∘ M.⟨ f′ M.∘ restrictEnv {Γ = Γ} am (⊑ᵘ-+ˡ Ψ₁ Φ) , x′ M.∘ restrictEnv {Γ = Γ} am (⊑ᵘ-trans p (⊑ᵘ-+ʳ Ψ₁ Φ)) ⟩)
  rel-app Γ Ψ₁ Ψ₂ Φ p {π} {A} {B} {x′ = x′} rf rx =
    rel-∘ (rel-apω {π = π})
      (rel-≈ʳ (rel-pair am Γ Ψ₁ Φ rf (rel-∘ rx (rel-weak am {Γ = Γ} p)))
              (λ v → >>=-cong ≈-refl (λ _ → >>=-cong (restrict-assoc ρ am {Γ = Γ} {B = A} x′ p (⊑ᵘ-+ʳ Ψ₁ Φ) v) (λ _ → ≈-refl))))

------------------------------------------------------------------------
-- 8. THE SMALL GENERATORS, the variables, the binders.
------------------------------------------------------------------------

module RelGen {L : Cx} (δ : Env L) (ρ : CallEnv) (am : M.AllocMode) where
  open Rel δ ρ

  private
    fst-pure : ∀ {E X Y} → Pure δ (ρl ∘l (lid {A = X} {E} ⊗l drop {A = Y})) fst
    fst-pure e (x , a) = bind-pure (≈-trans ret-bind ret-bind)

    snd-pure : ∀ {E X Y} → Pure δ (Once.LinCore.PassTr.dropl fmt {L} {E} {X} {Y}) snd
    snd-pure e (x , a) = bind-pure (≈-trans ret-bind ret-bind)

  rel-fst : ∀ {A B} → Rel (ρl ∘l (lid ⊗l drop)) (M.fst {A} {B})
  rel-fst {A} {B} = rel-pure (fst-pure {E = One} {X = ⟪ A ⟫} {Y = ⟪ B ⟫}) (q-fst ρ {A} {B}) proj₁

  rel-snd : ∀ {A B} → Rel (Once.LinCore.PassTr.dropl fmt) (M.snd {A} {B})
  rel-snd {A} {B} = rel-pure (snd-pure {E = One} {X = ⟪ A ⟫} {Y = ⟪ B ⟫}) (q-snd ρ {A} {B}) proj₂

  rel-inl : ∀ {A B} → Rel (linl {B = ⟪ B ⟫}) (M.inl {A} {B})
  rel-inl = mkRel λ w → ret≈R (Data.Sum.Relation.Binary.Pointwise.inj₁ w)

  rel-inr : ∀ {A B} → Rel (linr {A = ⟪ A ⟫}) (M.inr {A} {B})
  rel-inr = mkRel λ w → ret≈R (Data.Sum.Relation.Binary.Pointwise.inj₂ w)

  rel-zero : ∀ {B} → Rel (lzero {A = ⟪ B ⟫}) (M.initial {B})
  rel-zero = mkRel λ { {()} }

  rel-drop : ∀ {A} → Rel (drop {A = ⟪ A ⟫}) (M.terminal {A})
  rel-drop = mkRel λ w → ret≈R tt

  rel-id : ∀ {A} → Rel (lid {A = ⟪ A ⟫}) (M.id {A})
  rel-id = mkRel ret≈R

  -- a variable: its slot, against `projUsed`
  rel-var : ∀ {m n} {Γ : Ctx m n} (i : Data.Fin.Fin n) → Rel (var-at {Γ = Γ} i) (projUsed {Γ = Γ} i)
  rel-var {Γ = Γ SC.▸ A} Data.Fin.zero    = rel-snd
  rel-var {Γ = Γ SC.▸ A} (Data.Fin.suc i) = rel-var {Γ = Γ} i

  -- a binder, against `bindEnv`
  rel-bind : ∀ {m n} {Γ : Ctx m n} {Ψ : Usage n} {A : Ty m} (q : G.Quantity)
           → Rel (bindL {Γ = Γ} {Ψ} {A} q) (bindEnv {Γ = Γ} {Ψ} {A} am q)
  rel-bind G.Zero = rel-fst
  rel-bind G.One  = rel-id
  rel-bind G.Many = rel-id

------------------------------------------------------------------------
-- 9. ★ CLOSURES: a many-use closure over a body, against `curry`.
------------------------------------------------------------------------

module RelClo {L : Cx} (δ : Env L) (ρ : CallEnv) where
  open Rel δ ρ

  -- the body, on a copy of the environment it reads lent
  copyIn-≈ : ∀ {X A B} (b : LTm L (X ⊗t A) B) e a → Lᶜ δ (copyIn b) e a ≈ Lᶜ δ b tt (e , a)
  copyIn-≈ b e a = bind-pure (≈-trans ret-bind (≈-trans ret-bind ret-bind))

  -- ★ at either grade: a block's meaning is its computation's (`Grade.blk-coh`)
  rel-cloG : ∀ (π : G.Purity) {X A B : IRTy} {b : LTm L (⟪ X ⟫ ⊗t ⟪ A ⟫) ⟪ B ⟫} {b′ : M.IR (X I.* A) B}
               (γ : Gd (grade π) (copyIn b))
           → Rel b b′ → Rel (llamω (copyIn b) γ) (M.curry {π = π} b′)
  rel-cloG (G.fin φ) {b = b} γ rb = mkRel λ {x} {x′} w →
    ret≈R (λ {a} {a′} wa → ≈-≈R (≈-trans (≈-sym (blk-coh δ γ x a)) (copyIn-≈ b x a)) (rel rb (w , wa)))
  rel-cloG G.eff {b = b} γ rb = mkRel λ {x} {x′} w →
    ret≈R (λ {a} {a′} wa → ≈-≈R (copyIn-≈ b x a) (rel rb (w , wa)))

------------------------------------------------------------------------
-- 10. ★★ THE BRIDGE'S MEANING, by induction on the expression. The clauses
-- not yet proved are named premises (`Owed`), discharged one by one.
------------------------------------------------------------------------

module Main {L : Cx} (rs : Rs L) (δ : Env L) (cs : CanonicalName → (A B : IRTy) → ⟦ A ⟧ᴰᴵ → T∞ ⟦ B ⟧ᴰᴵ) (am : M.AllocMode) where
  ρ : CallEnv
  ρ = callEnv cs ans

  open Rel δ ρ
  open RelApp δ ρ am
  open RelGen δ ρ am
  open RelClo δ ρ

  -- the theorem's statement at one expression
  Goal : ∀ {m n} {Γ : Ctx m n} {Ψ : Usage n} {A : Ty m} → Expr Γ Ψ A → Set
  Goal e = Rel (Lq rs e) (elaborate am e)

  -- a binding: the body's share kept, the bound term's relabelled
  rel-let : ∀ {m n} (Γ : Ctx m n) (Ψ₂ Ψ₁ Φ : Usage n) (p : Ψ₁ ⊑ᵘ Φ) {A : IRTy}
              {x : LTm L (Co Γ Ψ₁) ⟪ A ⟫} {x′ : M.IR ⌊ ⟦ Γ ↾ Ψ₁ ⟧ᶜ ⌋ A}
          → Rel x x′
          → Rel ((lid ⊗l (x ∘l weak {Γ = Γ} p)) ∘l split Γ Ψ₂ Φ)
                M.⟨ restrictEnv {Γ = Γ} am (⊑ᵘ-+ˡ Ψ₂ Φ) , x′ M.∘ restrictEnv {Γ = Γ} am (⊑ᵘ-trans p (⊑ᵘ-+ʳ Ψ₂ Φ)) ⟩
  rel-let Γ Ψ₂ Ψ₁ Φ p {A} {x′ = x′} rx =
    rel-≈ʳ (rel-pair am Γ Ψ₂ Φ rel-id (rel-∘ rx (rel-weak am {Γ = Γ} p)))
      (λ v → >>=-cong (≈-trans (bind-pure (restrict-pure ρ am {Γ = Γ} (⊑ᵘ-+ˡ Ψ₂ Φ) v)) (≈-sym (restrict-pure ρ am {Γ = Γ} (⊑ᵘ-+ˡ Ψ₂ Φ) v)))
                      (λ _ → >>=-cong (restrict-assoc ρ am {Γ = Γ} {B = A} x′ p (⊑ᵘ-+ʳ Ψ₂ Φ) v) (λ _ → ≈-refl)))

  -- a usage relabelled by the same equation on both sides
  rel-castΦ : ∀ {m n} {Γ : Ctx m n} {Φ Φ′ : Usage n} {B : Ty m} (e : Φ ≡ Φ′)
                {t : LTm L (Co Γ Φ) (ty B)} {t′ : M.IR ⌊ ⟦ Γ ↾ Φ ⟧ᶜ ⌋ ⌊ B ⌋}
            → Rel t t′ → Rel (castΦ rs {Γ = Γ} e t) (subst (λ Ψ → M.IR ⌊ ⟦ Γ ↾ Ψ ⟧ᶜ ⌋ ⌊ B ⌋) e t′)
  rel-castΦ refl r = r

  -- ★ an erased binding: the body alone
  ok-let0 : ∀ {m n} {Γ : Ctx m n} {Ψ₁ Ψ₂ : Usage n} {A B : Ty m}
              (e1 : Expr Γ Ψ₁ A) (e2 : Expr (Γ SC.▸ A) (G.Zero ∷ Ψ₂) B) → Goal e2 → Goal (let' e1 e2)
  ok-let0 {Γ = Γ} {Ψ₁} {Ψ₂} {A} {B} e1 e2 g = rel-castΦ {Γ = Γ} {B = B} (sym (erase-arg-usage Ψ₂ Ψ₁)) g

  -- the function on `tt`, at any grade
  rel-app0 : ∀ {π} {X B : IRTy} {f : LTm L ⟪ X ⟫ ⟪ I.Unit ⇛[ π ] B ⟫} {f′ : M.IR X (I.Unit ⇛[ π ] B)}
           → Rel f f′ → Rel (apω {g = grade π} ∘l (f ⊗l lid) ∘l ρl⁻) (M.apply {I.Unit} {B} {π} M.∘ M.⟨ f′ , M.terminal ⟩)
  rel-app0 {π} g =
    rel-∘ (rel-apω {π = π})
      (mkRel λ w → ≈-≈R ret-bind (>>=-congR (rel g w) (λ r → ≈-≈R ret-bind (≈R-≈ (ret≈R (r , tt)) (≈-sym ret-bind)))))

  -- dropping the unit argument
  rel-ρ : ∀ {X : IRTy} → Rel (ρl {A = ⟪ X ⟫}) (M.fst {X} {I.Unit})
  rel-ρ = mkRel λ { {x , tt} (w , _) → ret≈R w }

  -- ★ an erased argument: the function on `tt`
  ok-app0 : ∀ {m n} {Γ : Ctx m n} {Ψ₁ Ψ₂ : Usage n} {A B : Ty m}
              (f : Expr Γ Ψ₁ (A ⇒[ G.mk-kind G.Zero G.pure ] B)) (x : Expr Γ Ψ₂ A) → Goal f → Goal (app f x)
  ok-app0 {Γ = Γ} {Ψ₁} {Ψ₂} {A} {B} f x g =
    rel-castΦ {Γ = Γ} {B = B} (sym (erase-arg-usage Ψ₁ Ψ₂)) (rel-app0 g)

  -- applying owned is applying
  apω-≈ : ∀ {g A B} (f : ⟦ Fn many g A B ⟧) (a : ⟦ A ⟧) → Lᶜ δ (apω {L} {One} {g = g} {A} {B}) tt (f , a) ≈ up g (f a)
  apω-≈ {g} {A} {B} f a = pair-drop (f ,_) (Lᶜ δ (Once.LinCore.PassTr.dropl fmt {Γ = L} {E = One} {A = Fn many g A B} {B = B}) tt) (λ _ → refl)

  -- ★ the composite's body: `g` then `f`, linearly, against `compIR`'s
  compB : ∀ {π} {A B C : IRTy}
        → Rel (apω {g = grade π} {⟪ B ⟫} {⟪ C ⟫} ∘l (lid ⊗l apω {g = grade π} {⟪ A ⟫} {⟪ B ⟫}) ∘l lassoc)
              (M.apply {B} {C} {π} M.∘ M.⟨ M.fst M.∘ M.fst , M.apply {A} {B} {π} M.∘ M.⟨ M.snd M.∘ M.fst , M.snd ⟩ ⟩)
  compB {π} {A} {B} {C} = mkRel λ { {(f , g) , a} {(f′ , g′) , a′} ((wf , wg) , wa) →
    ≈-≈R (≈-trans (>>=-cong (≈-trans ret-bind ret-bind) (λ _ → ≈-refl))
                  (≈-trans (bind-assoc _ _ _) (>>=-cong (apω-≈ {grade π} {⟪ A ⟫} {⟪ B ⟫} g a) (λ y → ≈-trans ret-bind (apω-≈ {grade π} {⟪ B ⟫} {⟪ C ⟫} f y)))))
      (≈R-≈ (>>=-congR (wg wa) (λ wb → wf wb))
            (≈-sym (≈-trans (>>=-cong (≈-trans (bind-pure ret-bind) (>>=-cong (bind-pure (≈-trans (bind-pure ret-bind) ret-bind)) (λ _ → ≈-refl))) (λ _ → ≈-refl))
                            (≈-trans (bind-assoc _ _ _) (>>=-cong ≈-refl (λ _ → ret-bind)))))) }

  ok-comp : ∀ {m n} {Γ : Ctx m n} {Ψ₁ Ψ₂ : Usage n} {A B C : Ty m} {π}
              (f : Expr Γ Ψ₁ (B ⇒[ G.mk-kind G.Many π ] C)) (g : Expr Γ Ψ₂ (A ⇒[ G.mk-kind G.Many π ] B))
            → Goal f → Goal g → Goal (comp' f g)
  ok-comp {Γ = Γ} {Ψ₁} {Ψ₂} {π = π} f g rf rg =
    rel-∘ (rel-cloG π _ compB) (rel-pairW Γ Ψ₁ Ψ₂ (G.Many *ᵘ Ψ₂) (⊑ᵘ-*Many Ψ₂) rf rg)

  -- ★ the fork's body: the argument copied, each closure applied to one copy
  forkB : ∀ {π} {A B C : IRTy}
        → Rel ((apω {g = grade π} {⟪ A ⟫} {⟪ B ⟫} ⊗l apω {g = grade π} {⟪ A ⟫} {⟪ C ⟫}) ∘l mixL ∘l (lid ⊗l dup))
              M.⟨ M.apply {A} {B} {π} M.∘ M.⟨ M.fst M.∘ M.fst , M.snd ⟩ , M.apply {A} {C} {π} M.∘ M.⟨ M.snd M.∘ M.fst , M.snd ⟩ ⟩
  forkB {π} {A} {B} {C} = mkRel λ { {(f , g) , a} {(f′ , g′) , a′} ((wf , wg) , wa) →
    ≈-≈R (≈-trans (bind-pure (≈-trans (bind-pure (≈-trans ret-bind ret-bind))
                                      (mix-pure δ {E = One} {X = Fn many (grade π) ⟪ A ⟫ ⟪ B ⟫} {Y = Fn many (grade π) ⟪ A ⟫ ⟪ C ⟫} {Z = ⟪ A ⟫} {U = ⟪ A ⟫} tt _)))
                  (>>=-cong (apω-≈ {grade π} {⟪ A ⟫} {⟪ B ⟫} f a) (λ b → >>=-cong (apω-≈ {grade π} {⟪ A ⟫} {⟪ C ⟫} g a) (λ _ → ≈-refl))))
      (≈R-≈ (>>=-congR (wf wa) (λ r → >>=-congR (wg wa) (λ r′ → ret≈R (r , r′))))
            (≈-sym (>>=-cong (bind-pure (≈-trans (bind-pure ret-bind) ret-bind))
                             (λ _ → >>=-cong (bind-pure (≈-trans (bind-pure ret-bind) ret-bind)) (λ _ → ≈-refl))))) }

  ok-fork : ∀ {m n} {Γ : Ctx m n} {Ψ₁ Ψ₂ : Usage n} {A B C : Ty m} {π}
              (f : Expr Γ Ψ₁ (A ⇒[ G.mk-kind G.Many π ] B)) (g : Expr Γ Ψ₂ (A ⇒[ G.mk-kind G.Many π ] C))
            → Goal f → Goal g → Goal (fork' f g)
  ok-fork {Γ = Γ} {Ψ₁} {Ψ₂} {π = π} f g rf rg = rel-∘ (rel-cloG π _ forkB) (rel-pair am Γ Ψ₁ Ψ₂ rf rg)

  -- ★ the curried: a closure that builds a closure, whose body applies the
  -- first to the pair
  curryB : ∀ {π} {A B C : IRTy}
         → Rel (apω {g = grade π} {⟪ A ⟫ ⊗t ⟪ B ⟫} {⟪ C ⟫} ∘l lassoc)
               (M.apply {A I.* B} {C} {π} M.∘ M.⟨ M.fst M.∘ M.fst , M.⟨ M.snd M.∘ M.fst , M.snd ⟩ ⟩)
  curryB {π} {A} {B} {C} = mkRel λ { {(f , a) , b} {(f′ , a′) , b′} ((wf , wa) , wb) →
    ≈-≈R (≈-trans ret-bind (apω-≈ {grade π} {⟪ A ⟫ ⊗t ⟪ B ⟫} {⟪ C ⟫} f (a , b)))
      (≈R-≈ (wf (wa , wb))
            (≈-sym (bind-pure (≈-trans (bind-pure ret-bind) (bind-pure (≈-trans (bind-pure ret-bind) ret-bind)))))) }

  ok-curry : ∀ {m n} {Γ : Ctx m n} {Ψ : Usage n} {A B C : Ty m} {π₀ π}
               (f : Expr Γ Ψ ((A Once.Spec.Type.* B) ⇒[ G.mk-kind G.Many π ] C)) → Goal f → Goal (curry' {π₀ = π₀} f)
  ok-curry {π₀ = π₀} {π} f rf = rel-∘ (rel-cloG π₀ _ (rel-cloG π _ curryB)) rf

  -- ★ an effectful application, suspended: a closure on `tt` whose body applies
  ok-effApp : ∀ {m n} {Γ : Ctx m n} {Ψ₁ Ψ₂ : Usage n} {A B : Ty m} {q π g}
                (f : Expr Γ Ψ₁ (A ⇒[ G.mk-kind q π ] B)) (x : Expr Γ Ψ₂ A) → Goal f → Goal x → Goal (effApp {g = g} f x)
  ok-effApp {Γ = Γ} {Ψ₁} {Ψ₂} {A} {B} {q = G.Zero} {π} f x rf rx =
    rel-castΦ {Γ = Γ} {B = Once.Spec.Type.Unit Once.Spec.Type.⇒[ G.mk-kind G.Many π ] B} (sym (erase-arg-usage Ψ₁ Ψ₂))
      (rel-cloG π _ (rel-∘ (rel-app0 rf) rel-ρ))
  ok-effApp {Γ = Γ} {Ψ₁} {Ψ₂} {q = G.One} {π} f x rf rx =
    rel-cloG π _ (rel-∘ (rel-app Γ Ψ₁ Ψ₂ (G.One *ᵘ Ψ₂) (⊑ᵘ-*One Ψ₂) rf rx) rel-ρ)
  ok-effApp {Γ = Γ} {Ψ₁} {Ψ₂} {q = G.Many} {π} f x rf rx =
    rel-cloG π _ (rel-∘ (rel-app Γ Ψ₁ Ψ₂ (G.Many *ᵘ Ψ₂) (⊑ᵘ-*Many Ψ₂) rf rx) rel-ρ)

  module P = Once.LinCore.PassTr fmt
  module BP = Once.LinCore.BridgeProof fmt ans

  -- the core's term and the pass's, moved along the same equal types
  subst₂-ev : ∀ {X X′ Y Y′} (p : X ≡ X′) (q : Y ≡ Y′) {t : LTm L X Y} {c : P.IR L X Y}
            → (∀ y → Lᶜ δ t tt y ≡ ev δ c y) → ∀ x → Lᶜ δ (subst₂ (Tm L One) p q t) tt x ≡ ev δ (subst₂ (P.IR L) p q c) x
  subst₂-ev refl refl h x = h x

  -- ★ A SIGOP: the pass's cast (`Casts.op≈`), the core's op being the pass's op
  rel-op : ∀ {A B} (si : SigOpInfo A B) → Rel (opL si) (M.SigOp si)
  rel-op {A} {B} si = mkRel λ {x} w →
    subst (λ m → m ≈[ W ⌊ B ⌋ ] _)
          (sym (subst₂-ev (sym (⟪⌊⌋⟫-flat (SigOpInfo.baseA si))) (sym (⟪⌊⌋⟫-flat (SigOpInfo.conB si))) (λ y → refl) x))
          (BP.Casts.op≈ (casts δ cs) si w)

  -- a numeric operation, case for case `numIR`
  rel-num : ∀ {m A U k} (h : Has A U) (o : Sym U k) → Rel (numL {L} {One} {m} h o) (numIR {m} h o)
  rel-num {A = Th.int}   {k = Th.unary}   h o = rel-op (numInfo h o)
  rel-num {A = Th.int}   {k = Th.binary}  h o = rel-op (numInfo h o)
  rel-num {A = Th.int}   {k = Th.compare} h o = rel-op (numInfo h o)
  rel-num {A = Th.float} {k = Th.unary}   h o = rel-op (numInfo h o)
  rel-num {A = Th.float} {k = Th.binary}  h o = rel-op (numInfo h o)
  rel-num {A = Th.float} {k = Th.compare} h o = rel-op (numInfo h o)

  ok-num : ∀ {m n} {Γ : Ctx m n} {Ψ : Usage n} {A U k} (h : Has A U) (o : Sym U k) (e : Expr Γ Ψ (symDom {m} A k))
         → Goal e → Goal (num h o e)
  ok-num h o e re = rel-∘ (rel-num h o) re

  -- a result moved along equal types, on both sides
  rel-cod : ∀ {X B B′ : IRTy} (e : B ≡ B′) {t : LTm L ⟪ X ⟫ ⟪ B ⟫} {t′ : M.IR X B}
          → Rel t t′ → Rel (cast refl (cong ⟪_⟫ e) t) (subst (M.IR X) e t′)
  rel-cod refl r = r

  -- ★ a closure built after dropping the environment, against one that
  -- ignores it (`elaborate`'s `curry (… ∘ snd)`)
  rel-cloD : ∀ (π : G.Purity) {X A B : IRTy} {bc : LTm L ⟪ A ⟫ ⟪ B ⟫} {b″ : M.IR A B}
               (γ : Gd (grade π) (copyIn (bc ∘l Once.LinCore.PassTr.dropl fmt {E = One} {A = One})))
           → Rel bc b″ → Rel (llamω (copyIn (bc ∘l Once.LinCore.PassTr.dropl fmt)) γ ∘l drop {A = ⟪ X ⟫}) (M.curry {X} {A} {B} {π} (b″ M.∘ M.snd))
  rel-cloD (G.fin φ) {bc = bc} γ rb = mkRel λ {x} {x′} w → ≈-≈R ret-bind (ret≈R (λ {a} {a′} wa →
    ≈-≈R (≈-trans (≈-sym (blk-coh δ γ tt a)) (≈-trans (copyIn-≈ (bc ∘l Once.LinCore.PassTr.dropl fmt {E = One} {A = One}) tt a) (bind-pure (bind-pure (≈-trans ret-bind ret-bind)))))
         (≈R-≈ (rel rb wa) (≈-sym ret-bind))))
  rel-cloD G.eff {bc = bc} γ rb = mkRel λ {x} {x′} w → ≈-≈R ret-bind (ret≈R (λ {a} {a′} wa →
    ≈-≈R (≈-trans (copyIn-≈ (bc ∘l Once.LinCore.PassTr.dropl fmt {E = One} {A = One}) tt a) (bind-pure (bind-pure (≈-trans ret-bind ret-bind))))
         (≈R-≈ (rel rb wa) (≈-sym ret-bind))))

  -- ★ a SigOp named in the source, against `sigOpIR`, case for case
  rel-sig : ∀ {X : IRTy} (A : Type) (name : CanonicalName) (c : IsConcrete A)
          → Rel (sigL A name c ∘l drop {A = ⟪ X ⟫}) (sigOpIR {X} A name c)
  rel-sig (Dom ⇒[ G.mk-kind G.Zero (G.fin G.pureᶠ) ] Cod) name (con-fun bDom cCod) = rel-cloD G.pure _ (rel-op _)
  rel-sig (Dom ⇒[ G.mk-kind G.Zero G.eff ] Cod) name (con-fun bDom cCod) = rel-cloD G.eff _ (rel-op _)
  rel-sig (Dom ⇒[ G.mk-kind G.Zero (G.fin G.actᶠ) ] Cod) name (con-fun bDom cCod) = rel-cloD G.act _ (rel-op _)
  rel-sig (Dom ⇒[ G.mk-kind G.One π ] Cod) name (con-fun bDom cCod) = rel-cloD π _ (rel-op _)
  rel-sig (Dom ⇒[ G.mk-kind G.Many π ] Cod) name (con-fun bDom cCod) = rel-cloD π _ (rel-op _)
  rel-sig _ name (con-base (ST.b-var {i = ()} _))
  rel-sig _ name (con-base ib@ST.b-Unit)    = rel-≈ʳ (rel-∘ (rel-∘ (rel-op (value-info name ST.b-Unit ib)) rel-drop) rel-drop) (λ _ → ret-bind)
  rel-sig _ name (con-base ib@ST.b-Void)    = rel-≈ʳ (rel-∘ (rel-∘ (rel-op (value-info name ST.b-Unit ib)) rel-drop) rel-drop) (λ _ → ret-bind)
  rel-sig _ name (con-base ib@ST.b-Int)     = rel-≈ʳ (rel-∘ (rel-∘ (rel-op (value-info name ST.b-Unit ib)) rel-drop) rel-drop) (λ _ → ret-bind)
  rel-sig _ name (con-base ib@ST.b-Float)   = rel-≈ʳ (rel-∘ (rel-∘ (rel-op (value-info name ST.b-Unit ib)) rel-drop) rel-drop) (λ _ → ret-bind)
  rel-sig _ name (con-base ib@(ST.b-* a b)) = rel-≈ʳ (rel-∘ (rel-∘ (rel-op (value-info name ST.b-Unit ib)) rel-drop) rel-drop) (λ _ → ret-bind)
  rel-sig _ name (con-base ib@(ST.b-+ a b)) = rel-≈ʳ (rel-∘ (rel-∘ (rel-op (value-info name ST.b-Unit ib)) rel-drop) rel-drop) (λ _ → ret-bind)

  ok-sigOp : ∀ {m n} {Γ : Ctx m n} {A : Type} (name : CanonicalName) (c : IsConcrete A) → Goal (sigOp {Γ = Γ} name c)
  ok-sigOp {A = A} name c = rel-cod (sym (⌊wk₀⌋ A)) (rel-sig A name c)

  -- ★ THE TABLE'S TWO MEANINGS, related (a hypothesis on the program's table,
  -- discharged by its construction, as `BridgeProof.EnvOK`): a resolved call
  -- against the table's, an unlinked one master's `unlinkedT`
  record CallsOK : Set where
    field
      hit≈  : ∀ {f A B g l} {p : L ∋[ l ] sg once g One ⟪ A ⟫ ⟪ B ⟫} → rs f A B g ≡ just (l , p)
            → ∀ {a a′} → W A a a′ → up g (lookup δ p tt a) ≈[ W B ] cs f A B a′
      miss≡ : ∀ {f A B g} → rs f A B g ≡ nothing → ∀ a′ → cs f A B a′ ≡ embed unlinkedT

  module Calls (ck : CallsOK) where
    open CallsOK ck

    -- the unlinked op halts as master's `unlinkedT`
    unlinked≈ : ∀ {g} {A B : IRTy} {a} → Lᶜ δ (callM {L} {g} {⟪ A ⟫} {⟪ B ⟫} nothing) tt a ≈[ W B ] embed unlinkedT
    blockR unlinked≈ = ≈haltR

    callM-rel : ∀ {f A B g} (r : Maybe (Σ ℕ λ l → L ∋[ l ] sg once g One ⟪ A ⟫ ⟪ B ⟫)) → rs f A B g ≡ r
              → Rel (callM r) (M.Call {A} {B} f)
    callM-rel (just (l , p)) e = mkRel λ w → ≈-≈R (bind-pure (≈-trans ret-bind (≈-trans ret-bind ret-bind))) (hit≈ e w)
    callM-rel {f} {A} {B} {g} nothing e = mkRel λ {a} {a′} w →
      subst (λ m → Lᶜ δ (callM {L} {g} {⟪ A ⟫} {⟪ B ⟫} nothing) tt a ≈[ W B ] m) (sym (miss≡ {f} {A} {B} {g} e a′)) (unlinked≈ {g} {A} {B} {a})

    -- ★ a call of a definition
    rel-call : ∀ f (A B : IRTy) g → Rel (callM (rs f A B g)) (M.Call {A} {B} f)
    rel-call f A B g = callM-rel (rs f A B g) refl

    -- ★ a reference to a definition, case for case `refIR`
    rel-ref : ∀ {m} (T : Ty m) (f : CanonicalName) → Rel (refL rs T f) (refIR T f)
    rel-ref (A ⇒[ G.mk-kind G.Zero π ] B) f = rel-cloG π _ (rel-∘ (rel-call f I.Unit ⌊ B ⌋ (grade π)) rel-snd)
    rel-ref (A ⇒[ G.mk-kind G.One π ] B) f  = rel-cloG π _ (rel-∘ (rel-call f ⌊ A ⌋ ⌊ B ⌋ (grade π)) rel-snd)
    rel-ref (A ⇒[ G.mk-kind G.Many π ] B) f = rel-cloG π _ (rel-∘ (rel-call f ⌊ A ⌋ ⌊ B ⌋ (grade π)) rel-snd)
    rel-ref T@ST.Unit      f = rel-∘ (rel-call f I.Unit ⌊ T ⌋ act) rel-drop
    rel-ref T@ST.Void      f = rel-∘ (rel-call f I.Unit ⌊ T ⌋ act) rel-drop
    rel-ref T@(_ ST.* _)   f = rel-∘ (rel-call f I.Unit ⌊ T ⌋ act) rel-drop
    rel-ref T@(_ ST.+ _)   f = rel-∘ (rel-call f I.Unit ⌊ T ⌋ act) rel-drop
    rel-ref T@(ST.μ _)     f = rel-∘ (rel-call f I.Unit ⌊ T ⌋ act) rel-drop
    rel-ref T@(ST.ν _ _)   f = rel-∘ (rel-call f I.Unit ⌊ T ⌋ act) rel-drop
    rel-ref T@ST.Int       f = rel-∘ (rel-call f I.Unit ⌊ T ⌋ act) rel-drop
    rel-ref T@ST.Float     f = rel-∘ (rel-call f I.Unit ⌊ T ⌋ act) rel-drop
    rel-ref T@(ST.var _)   f = rel-∘ (rel-call f I.Unit ⌊ T ⌋ act) rel-drop

    ok-closure : ∀ {m n} {Γ : Ctx m n} {A : Ty m} (name : String) → Goal (closure {Γ = Γ} {A = A} name)
    ok-closure {A = A} name = rel-∘ (rel-ref A (bare name)) rel-drop

    ok-poly : ∀ {m n} {Γ : Ctx m n} (name : String) (T : Ty m) → Goal (poly {Γ = Γ} name T)
    ok-poly name T = rel-∘ (rel-ref T (bare name)) rel-drop

  -- (K: two proofs of one equation are one)
  uip : ∀ {X : Set} {x y : X} (p q : x ≡ y) → p ≡ q
  uip refl refl = refl

  -- two casts of the input, as one
  cast-fuse : ∀ {X Y Z B} (p : X ≡ Y) (q : Y ≡ Z) (t : LTm L X B) → cast q refl (cast p refl t) ≡ cast (trans p q) refl t
  cast-fuse refl refl t = refl

  cast-fuseᶜ : ∀ {A X Y Z} (p : X ≡ Y) (q : Y ≡ Z) (t : LTm L A X) → cast refl q (cast refl p t) ≡ cast refl (trans p q) t
  cast-fuseᶜ refl refl t = refl

  -- a relation moved along a term's equality
  rel-≡ : ∀ {A B} {t u : LTm L ⟪ A ⟫ ⟪ B ⟫} {t′ : M.IR A B} → t ≡ u → Rel t t′ → Rel u t′
  rel-≡ refl r = r

  -- an input moved along equal types, on both sides
  rel-dom : ∀ {X Y B : IRTy} (e : X ≡ Y) {t : LTm L ⟪ Y ⟫ ⟪ B ⟫} {t′ : M.IR Y B}
          → Rel t t′ → Rel (cast (cong ⟪_⟫ (sym e)) refl t) (subst (λ o → M.IR o B) (sym e) t′)
  rel-dom refl r = r

  -- the core's term and the pass's, moved along the same input or result
  subst-ev₁ : ∀ {X X′ Y} (p : X ≡ X′) {t : LTm L X Y} {c : P.IR L X Y}
            → (∀ y → Lᶜ δ t tt y ≡ ev δ c y) → ∀ x → Lᶜ δ (cast p refl t) tt x ≡ ev δ (subst (λ Z → P.IR L Z Y) p c) x
  subst-ev₁ refl h x = h x

  subst-ev₂ : ∀ {X Y Y′} (q : Y ≡ Y′) {t : LTm L X Y} {c : P.IR L X Y}
            → (∀ y → Lᶜ δ t tt y ≡ ev δ c y) → ∀ x → Lᶜ δ (cast refl q t) tt x ≡ ev δ (subst (λ Z → P.IR L X Z) q c) x
  subst-ev₂ refl h x = h x

  -- ★ the initial algebra's constructor and the ν's observation, from the pass's casts
  rel-In₀ : ∀ {F} (wf : WellFormedFI F) → Rel (cast (sym (⟪⟫-TI wf (μ-type F))) refl (lIn {F = lf F})) (M.In wf)
  rel-In₀ {F} wf = mkRel λ {x} w →
    subst (λ m → m ≈[ W (μ-type F) ] _) (sym (subst-ev₁ (sym (⟪⟫-TI wf (μ-type F))) (λ y → refl) x)) (BP.Casts.In≈ (casts δ cs) wf w)

  rel-Out₀ : ∀ {F} (wf : WellFormedFI F) → Rel (cast refl (sym (⟪⟫-TI wf (ν-type F))) (lout {F = lf F})) (M.Out wf)
  rel-Out₀ {F} wf = mkRel λ {x} w →
    subst (λ m → m ≈[ W (⟦ F ⟧TI (ν-type F)) ] _) (sym (subst-ev₂ (sym (⟪⟫-TI wf (ν-type F))) (λ y → refl) x)) (BP.Casts.Out≈ (casts δ cs) wf w)

  -- the Spec's functor's layer, the IR's, the core's code: one cast
  rel-In : ∀ {m} {Δ : KCtx m} (F : Fun m) (w : WFFun Δ F) → Rel (mapT {L} (mp-In F w)) (mapIR (mp-In F w))
  rel-In F w =
    rel-≡ (trans (cast-fuse (sym (⟪⟫-TI (wf-⌊⌋ w) (μ-type (I.eraseF F)))) (cong ⟪_⟫ (sym (⌊⟧T-commute F (μ F)))) lIn)
                 (cong (λ e → cast e refl lIn) (uip _ _)))
          (rel-dom (⌊⟧T-commute F (μ F)) (rel-In₀ (wf-⌊⌋ w)))

  rel-Out : ∀ {m} {Δ : KCtx m} (F : Fun m) (f : G.Finite) (w : WFFun Δ F)
          → Rel (cast refl (sym (layerEq F w (ν F f))) (lout {L} {lf (I.eraseF F)})) (Once.TypeCheck.Table.outIR F f w)
  rel-Out F f w =
    rel-≡ (trans (cast-fuseᶜ (sym (⟪⟫-TI (wf-⌊⌋ w) (ν-type (I.eraseF F)))) (cong ⟪_⟫ (sym (⌊⟧T-commute F (ν F f)))) lout)
                 (cong (λ e → cast refl e lout) (uip _ _)))
          (rel-cod (sym (⌊⟧T-commute F (ν F f))) (rel-Out₀ (wf-⌊⌋ w)))

  -- ★ a structure map, entry for entry
  rel-map : ∀ {m} {A B : Ty m} (mp : Map A B) → Rel (mapT {L} mp) (mapIR mp)
  rel-map mp-id                         = rel-id
  rel-map mp-fst                        = rel-fst
  rel-map mp-snd                        = rel-snd
  rel-map mp-terminal                   = rel-drop
  rel-map mp-inl                        = rel-inl
  rel-map mp-inr                        = rel-inr
  rel-map mp-initial                    = rel-zero
  rel-map (mp-apply A B (G.fin G.pureᶠ)) = rel-apω {π = G.pure}
  rel-map (mp-apply A B (G.fin G.actᶠ))  = rel-cloG G.act _ (rel-∘ (rel-apω {π = G.act}) rel-ρ)
  rel-map (mp-apply A B G.eff)          = rel-cloG G.eff _ (rel-∘ (rel-apω {π = G.eff}) rel-ρ)
  rel-map (mp-In F w)                   = rel-In F w
  rel-map (mp-Out F G.pureᶠ w)          = rel-Out F G.pureᶠ w
  rel-map (mp-Out F G.actᶠ w)           = rel-cloG G.act _ (rel-∘ (rel-Out F G.actᶠ w) rel-ρ)
  rel-map mp-toFloat                    = rel-op i2f-info

  ok-lift : ∀ {m n} {Γ : Ctx m n} {A B : Ty m} {π} (mp : Map A B) → Goal (lift-morphism {Γ = Γ} {π = π} mp)
  ok-lift {π = π} mp = rel-cloG π _ (rel-∘ (rel-map mp) rel-snd)

  ok-mapp : ∀ {m n} {Γ : Ctx m n} {Ψ : Usage n} {A B : Ty m} (mp : Map A B) (x : Expr Γ Ψ A) → Goal x → Goal (morph-app mp x)
  ok-mapp {Γ = Γ} {Ψ} mp x rx = rel-∘ (rel-map mp) (rel-∘ rx (rel-weak am {Γ = Γ} (⊑ᵘ-trans (⊑ᵘ-*Many Ψ) (⊑ᵘ-+ʳ SC.zeroUsage (G.Many *ᵘ Ψ)))))

  -- ★ DISTRIBUTIVITY: the core's one-shot closures against master's curried injections
  dv : ∀ {X A B : IRTy} → ⟦ ⟪ X ⟫ ⊗t (⟪ A ⟫ ⊕t ⟪ B ⟫) ⟧ → ⟦ (⟪ X ⟫ ⊗t ⟪ A ⟫) ⊕t (⟪ X ⟫ ⊗t ⟪ B ⟫) ⟧
  dv (x , inj₁ a) = inj₁ (x , a)
  dv (x , inj₂ b) = inj₂ (x , b)

  dv′ : ∀ {X A B : IRTy} → ⟦ X I.* (A I.+ B) ⟧ᴰᴵ → ⟦ (X I.* A) I.+ (X I.* B) ⟧ᴰᴵ
  dv′ (x , inj₁ a) = inj₁ (x , a)
  dv′ (x , inj₂ b) = inj₂ (x , b)

  dist-pure : ∀ {X A B : IRTy} → Pure δ (dist {L} {One} {⟪ X ⟫} {⟪ A ⟫} {⟪ B ⟫}) (dv {X} {A} {B})
  dist-pure {X} {A} {B} e (x , inj₁ a) =
    ≈-trans (bind-pure (≈-trans ret-bind (≈-trans ret-bind ret-bind)))
            (≈-trans (≈-sym (blk-coh δ (k-∘ (k-inl {A = ⟪ X ⟫ ⊗t ⟪ A ⟫} {B = ⟪ X ⟫ ⊗t ⟪ B ⟫} {E = One}) (k-swap {A = ⟪ A ⟫} {B = ⟪ X ⟫} {E = One})) tt (a , x))) ret-bind)
  dist-pure {X} {A} {B} e (x , inj₂ b) =
    ≈-trans (bind-pure (≈-trans ret-bind (≈-trans ret-bind ret-bind)))
            (≈-trans (≈-sym (blk-coh δ (k-∘ (k-inr {A = ⟪ X ⟫ ⊗t ⟪ A ⟫} {B = ⟪ X ⟫ ⊗t ⟪ B ⟫} {E = One}) (k-swap {A = ⟪ B ⟫} {B = ⟪ X ⟫} {E = One})) tt (b , x))) ret-bind)

  distribute-pure : ∀ {X A B : IRTy} → PureI ρ (distribute {X} {A} {B} am) (dv′ {X} {A} {B})
  distribute-pure (x , inj₁ a) =
    ≈-trans (bind-pure (≈-trans ret-bind ret-bind))
      (≈-trans (bind-pure (≈-trans (bind-pure ret-bind) ret-bind)) (bind-pure (≈-trans ret-bind ret-bind)))
  distribute-pure (x , inj₂ b) =
    ≈-trans (bind-pure (≈-trans ret-bind ret-bind))
      (≈-trans (bind-pure (≈-trans (bind-pure ret-bind) ret-bind)) (bind-pure (≈-trans ret-bind ret-bind)))

  rel-dist : ∀ {X A B : IRTy} → Rel (dist {L} {One} {⟪ X ⟫} {⟪ A ⟫} {⟪ B ⟫}) (distribute {X} {A} {B} am)
  rel-dist {X} {A} {B} = rel-pure (dist-pure {X} {A} {B}) (distribute-pure {X} {A} {B}) dW
    where
      dW : ∀ {x x′} → W (X I.* (A I.+ B)) x x′ → W ((X I.* A) I.+ (X I.* B)) (dv {X} {A} {B} x) (dv′ {X} {A} {B} x′)
      dW {_ , inj₁ _} {_ , inj₁ _} (wx , Data.Sum.Relation.Binary.Pointwise.inj₁ wa) = Data.Sum.Relation.Binary.Pointwise.inj₁ (wx , wa)
      dW {_ , inj₂ _} {_ , inj₂ _} (wx , Data.Sum.Relation.Binary.Pointwise.inj₂ wb) = Data.Sum.Relation.Binary.Pointwise.inj₂ (wx , wb)

  -- a case against `case`
  rel-lcase : ∀ {A B C : IRTy} {f : LTm L ⟪ A ⟫ ⟪ C ⟫} {f′ : M.IR A C} {g : LTm L ⟪ B ⟫ ⟪ C ⟫} {g′ : M.IR B C}
            → Rel f f′ → Rel g g′ → Rel (lcase f g) (M.case f′ g′)
  rel-lcase rf rg = mkRel λ { (Data.Sum.Relation.Binary.Pointwise.inj₁ w) → rel rf w ; (Data.Sum.Relation.Binary.Pointwise.inj₂ w) → rel rg w }

  -- the scrutinee's share split off, the arms' share beside its value
  rel-swapPair : ∀ {m n} (Γ : Ctx m n) (Ψs Φ : Usage n) {S : IRTy} {s : LTm L (Co Γ Ψs) ⟪ S ⟫} {s′ : M.IR ⌊ ⟦ Γ ↾ Ψs ⟧ᶜ ⌋ S}
               → Rel s s′
               → Rel ((lid ⊗l s) ∘l lswap ∘l split Γ Ψs Φ)
                     M.⟨ restrictEnv {Γ = Γ} am (⊑ᵘ-+ʳ Ψs Φ) , s′ M.∘ restrictEnv {Γ = Γ} am (⊑ᵘ-+ˡ Ψs Φ) ⟩
  rel-swapPair Γ Ψs Φ rs′ = mkRel λ {x} {x′} w → let sw = split-W Γ Ψs Φ w in
    ≈-≈R (≈-trans (bind-pure (bind-pure (split-pure δ Γ Ψs Φ tt x))) ret-bind)
      (≈R-≈ (>>=-congR (rel rs′ (proj₁ sw)) (λ r → ret≈R (proj₂ sw , r)))
            (≈-sym (≈-trans (bind-pure (restrict-pure ρ am {Γ = Γ} (⊑ᵘ-+ʳ Ψs Φ) x′))
                            (>>=-cong (bind-pure (restrict-pure ρ am {Γ = Γ} (⊑ᵘ-+ˡ Ψs Φ) x′)) (λ _ → ≈-refl)))))

  -- an arm's share, beside the bound value
  rel-arm : ∀ {m n} {Γ : Ctx m n} {Ψ Ψ′ : Usage n} {A : IRTy} (p : Ψ ⊑ᵘ Ψ′)
          → Rel (weak {Γ = Γ} p ⊗l lid {A = ⟪ A ⟫}) M.⟨ restrictEnv {Γ = Γ} am p M.∘ M.fst , M.snd ⟩
  rel-arm {Γ = Γ} p = mkRel λ { {x , a} {x′ , a′} (w , wa) →
    ≈-≈R (≈-trans (bind-pure (weak-pure δ {E = One} {Γ = Γ} p tt x)) ret-bind)
      (≈R-≈ (ret≈R (weak-W {Γ = Γ} p w , wa))
            (≈-sym (≈-trans (bind-pure (≈-trans ret-bind (restrict-pure ρ am {Γ = Γ} p x′))) ret-bind))) }

  -- ★ A CASE: the scrutinee's share split off, the arms' share distributed,
  -- each arm on its share and the bound value
  ok-case : ∀ {m n} {Γ : Ctx m n} {Ψs Ψₗ Ψᵣ : Usage n} {qℓ qr : G.Quantity} {A B C : Ty m}
              (s : Expr Γ Ψs (A + B)) (l : Expr (Γ SC.▸ A) (qℓ ∷ Ψₗ) C) (r : Expr (Γ SC.▸ B) (qr ∷ Ψᵣ) C)
            → Goal s → Goal l → Goal r → Goal (case' s l r)
  ok-case {Γ = Γ} {Ψs} {Ψₗ} {Ψᵣ} {qℓ} {qr} {A} {B} s l r rs′ rl rr =
    rel-∘ (rel-lcase (rel-∘ rl (rel-∘ (rel-bind {Γ = Γ} {A = A} qℓ) (rel-arm {Γ = Γ} (⊑ᵘ-⊔ˡ Ψₗ Ψᵣ))))
                     (rel-∘ rr (rel-∘ (rel-bind {Γ = Γ} {A = B} qr) (rel-arm {Γ = Γ} (⊑ᵘ-⊔ʳ Ψₗ Ψᵣ)))))
          (rel-∘ rel-dist (rel-swapPair Γ Ψs (Ψₗ ⊔ᵘ Ψᵣ) rs′))

  -- the combinators' distribution (`distribIR`), the same values
  distribIR-pure : ∀ {X A B : IRTy} → PureI ρ (distribIR {X} {A} {B} am) (dv′ {X} {A} {B})
  distribIR-pure (x , inj₁ a) =
    ≈-trans (bind-pure (≈-trans (bind-pure ret-bind) ret-bind)) (bind-pure (≈-trans ret-bind ret-bind))
  distribIR-pure (x , inj₂ b) =
    ≈-trans (bind-pure (≈-trans (bind-pure ret-bind) ret-bind)) (bind-pure (≈-trans ret-bind ret-bind))

  rel-distIR : ∀ {X A B : IRTy} → Rel (dist {L} {One} {⟪ X ⟫} {⟪ A ⟫} {⟪ B ⟫}) (distribIR {X} {A} {B} am)
  rel-distIR {X} {A} {B} = rel-pure (dist-pure {X} {A} {B}) (distribIR-pure {X} {A} {B}) dW
    where
      dW : ∀ {x x′} → W (X I.* (A I.+ B)) x x′ → W ((X I.* A) I.+ (X I.* B)) (dv {X} {A} {B} x) (dv′ {X} {A} {B} x′)
      dW {_ , inj₁ _} {_ , inj₁ _} (wx , Data.Sum.Relation.Binary.Pointwise.inj₁ wa) = Data.Sum.Relation.Binary.Pointwise.inj₁ (wx , wa)
      dW {_ , inj₂ _} {_ , inj₂ _} (wx , Data.Sum.Relation.Binary.Pointwise.inj₂ wb) = Data.Sum.Relation.Binary.Pointwise.inj₂ (wx , wb)

  -- ★ the copairing's body: distributed, each arm one closure, the other dropped
  copairB : ∀ {π} {A B C : IRTy}
          → Rel (lcase (apω {g = grade π} {⟪ A ⟫} {⟪ C ⟫} ∘l ((ρl ∘l (lid ⊗l drop)) ⊗l lid))
                       (apω {g = grade π} {⟪ B ⟫} {⟪ C ⟫} ∘l (Once.LinCore.PassTr.dropl fmt ⊗l lid)) ∘l dist)
                (M.case (M.apply {A} {C} {π} M.∘ M.⟨ M.fst M.∘ M.fst , M.snd ⟩) (M.apply {B} {C} {π} M.∘ M.⟨ M.snd M.∘ M.fst , M.snd ⟩)
                 M.∘ distribIR am)
  copairB {π} {A} {B} {C} =
    rel-∘ (rel-lcase (rel-∘ (rel-apω {π = π})
                       (mkRel λ { {(f , g) , a} {(f′ , g′) , a′} ((wf , wg) , wa) →
                         ≈-≈R (≈-trans (bind-pure (bind-pure (≈-trans ret-bind ret-bind))) ret-bind)
                              (≈R-≈ (ret≈R (wf , wa)) (≈-sym (≈-trans (bind-pure ret-bind) ret-bind))) }))
                     (rel-∘ (rel-apω {π = π})
                       (mkRel λ { {(f , g) , b} {(f′ , g′) , b′} ((wf , wg) , wb) →
                         ≈-≈R (≈-trans (bind-pure (bind-pure (≈-trans ret-bind ret-bind))) ret-bind)
                              (≈R-≈ (ret≈R (wg , wb)) (≈-sym (≈-trans (bind-pure ret-bind) ret-bind))) })))
          rel-distIR

  ok-copair : ∀ {m n} {Γ : Ctx m n} {Ψ₁ Ψ₂ : Usage n} {A B C : Ty m} {π}
                (f : Expr Γ Ψ₁ (A ⇒[ G.mk-kind G.Many π ] C)) (g : Expr Γ Ψ₂ (B ⇒[ G.mk-kind G.Many π ] C))
              → Goal f → Goal g → Goal (copair' f g)
  ok-copair {Γ = Γ} {Ψ₁} {Ψ₂} {π = π} f g rf rg = rel-∘ (rel-cloG π _ copairB) (rel-pair am Γ Ψ₁ Ψ₂ rf rg)

  -- ★ THE LOOP: the round lent to every round, against master's `Iter` of `apply`
  loopB : ∀ {A B : IRTy}
        → Rel (Once.LinCore.PassTr.dropl fmt ∘l lend (liter (bsnd (bev {g = act} {⟪ A ⟫} {⟪ B ⟫ ⊕t ⟪ A ⟫})) (k-snd k-bev)))
              (M.Iter (M.apply {A} {B I.+ A} {G.act} M.∘ M.⟨ M.fst , M.snd ⟩))
  loopB {A} {B} = mkRel λ { {F , a} {F′ , a′} (wF , wa) →
    ≈-≈R (pair-drop (F ,_) (Lᶜ δ (Once.LinCore.PassTr.dropl fmt {Γ = L} {E = One} {A = Fn many act ⟪ A ⟫ (⟪ B ⟫ ⊕t ⟪ A ⟫)} {B = ⟪ B ⟫}) tt) (λ _ → refl))
         (iter-congR (λ r → ≈R-≈ (wF r) (≈-sym (bind-pure (≈-trans ret-bind ret-bind))))
                     (≈R-≈ (wF wa) (≈-sym (bind-pure (≈-trans ret-bind ret-bind))))) }

  ok-loop : ∀ {m n} {Γ : Ctx m n} {Ψ : Usage n} {A B : Ty m}
              (r : Expr Γ Ψ (A ⇒[ G.mk-kind G.Many G.act ] (B + A))) → Goal r → Goal (loop r)
  ok-loop {Γ = Γ} {Ψ} r rr = rel-∘ (rel-cloG G.eff tt loopB) (rel-∘ rr (rel-weak am {Γ = Γ} (⊑ᵘ-*Many Ψ)))

  -- ★ A CONVERSION, along the subtyping derivation (`coeIR`)
  -- (the argument converted, the closure beside it)
  rel-arg : ∀ {F X X′ : IRTy} {f : LTm L ⟪ X′ ⟫ ⟪ X ⟫} {f′ : M.IR X′ X}
          → Rel f f′ → Rel (lid {A = ⟪ F ⟫} ⊗l f) M.⟨ M.fst {F} {X′} , f′ M.∘ M.snd ⟩
  rel-arg rf = mkRel λ { {Fv , x} {Fv′ , x′} (wF , wx) →
    ≈-≈R ret-bind (≈R-≈ (>>=-congR (rel rf wx) (λ r → ret≈R (wF , r)))
                        (≈-sym (≈-trans ret-bind (>>=-cong ret-bind (λ _ → ≈-refl))))) }

  rel-coeL : ∀ {m} {A B : Ty m} (p : A <: B) → Rel (coeL {L} p) (coeIR p)
  rel-coeL sub-void   = rel-zero
  rel-coeL sub-unit   = rel-id
  rel-coeL sub-int    = rel-id
  rel-coeL sub-float  = rel-id
  rel-coeL (sub-arr {q = G.Zero} {π = π} {π′ = π′} a b r) = rel-cloG π′ _ (rel-∘ (rel-coeL b) (rel-apω {π = π}))
  rel-coeL (sub-arr {q = G.One}  {π = π} {π′ = π′} a b r) = rel-cloG π′ _ (rel-∘ (rel-coeL b) (rel-∘ (rel-apω {π = π}) (rel-arg (rel-coeL a))))
  rel-coeL (sub-arr {q = G.Many} {π = π} {π′ = π′} a b r) = rel-cloG π′ _ (rel-∘ (rel-coeL b) (rel-∘ (rel-apω {π = π}) (rel-arg (rel-coeL a))))
  rel-coeL (sub-* a b) = mkRel λ { {x , y} {x′ , y′} (wx , wy) →
    ≈R-≈ (>>=-congR (rel (rel-coeL a) wx) (λ r → >>=-congR (rel (rel-coeL b) wy) (λ r′ → ret≈R (r , r′))))
         (≈-sym (>>=-cong ret-bind (λ _ → >>=-cong ret-bind (λ _ → ≈-refl)))) }
  rel-coeL (sub-+ a b) = rel-lcase (rel-∘ rel-inl (rel-coeL a)) (rel-∘ rel-inr (rel-coeL b))
  rel-coeL sub-μ      = rel-id
  rel-coeL (sub-ν _)  = rel-id
  rel-coeL sub-var    = rel-id

  rel-coeR : ∀ {m} {Z : IRTy} {A B : Ty m} (p : A <: B) (d : Dec (VoidFree p)) {t : LTm L ⟪ Z ⟫ (ty A)} {t′ : M.IR Z ⌊ A ⌋}
           → Rel t t′ → Rel (coeR p d t) (runCoe-dec p d t′)
  rel-coeR p (yes vf) r = rel-cod (erase-eq p vf) r
  rel-coeR p (no _)   r = rel-∘ (rel-coeL p) r

  ok-coerce : ∀ {m n} {Γ : Ctx m n} {Ψ : Usage n} {A B : Ty m} (p : A <: B) (f : Expr Γ Ψ A) → Goal f → Goal (coerce p f)
  ok-coerce p f rf = rel-coeR p (voidFree? p) rf

  record Owed : Set where
    field
      o-cata    : ∀ {m n} {Γ : Ctx m n} {Ψ : Usage n} {F : Fun m} {Δₖ : KCtx m} {A : Ty m} {π}
                    (wf : WFFun Δₖ F) (alg : Expr Γ Ψ (ST.⟦ F ⟧F A ⇒[ G.mk-kind G.Many π ] A)) → Goal alg → Goal (cata wf alg)
      o-ana     : ∀ {m n} {Γ : Ctx m n} {Ψ : Usage n} {F : Fun m} {Δₖ : KCtx m} {A : Ty m} {π₀} {φ : G.Finite}
                    (wf : WFFun Δₖ F) (c : Expr Γ Ψ (A ⇒[ G.mk-kind G.Many (G.fin φ) ] ST.⟦ F ⟧F A))
                  → Goal c → Goal (ana {π₀ = π₀} wf c)

  module _ (ck : CallsOK) (ow : Owed) where
    open Owed ow
    open Calls ck

    Lq-ok : ∀ {m n} {Γ : Ctx m n} {Ψ : Usage n} {A : Ty m} (e : Expr Γ Ψ A) → Goal e
    Lq-ok {Γ = Γ} (var i) = rel-var {Γ = Γ} i
    Lq-ok (lam {q' = G.Zero} {π = π} G.Zero _ e) = rel-cloG π _ (rel-∘ (Lq-ok e) rel-fst)
    Lq-ok (lam {q' = G.Zero} {π = π} G.One  _ e) = rel-cloG π _ (rel-∘ (Lq-ok e) rel-fst)
    Lq-ok (lam {q' = G.Zero} {π = π} G.Many _ e) = rel-cloG π _ (rel-∘ (Lq-ok e) rel-fst)
    Lq-ok (lam {q' = G.One}  {π = π} G.One  _ e) = rel-cloG π _ (Lq-ok e)
    Lq-ok (lam {q' = G.One}  {π = π} G.Many _ e) = rel-cloG π _ (Lq-ok e)
    Lq-ok (lam {q' = G.Many} {π = π} G.Many _ e) = rel-cloG π _ (Lq-ok e)
    Lq-ok (app {q = G.Zero} f x) = ok-app0 f x (Lq-ok f)
    Lq-ok {Γ = Γ} (app {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {q = G.One} f x) =
      rel-app Γ Ψ₁ Ψ₂ (G.One *ᵘ Ψ₂) (⊑ᵘ-*One Ψ₂) (Lq-ok f) (Lq-ok x)
    Lq-ok {Γ = Γ} (app {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {q = G.Many} f x) =
      rel-app Γ Ψ₁ Ψ₂ (G.Many *ᵘ Ψ₂) (⊑ᵘ-*Many Ψ₂) (Lq-ok f) (Lq-ok x)
    Lq-ok (effApp f x) = ok-effApp f x (Lq-ok f) (Lq-ok x)
    Lq-ok {Γ = Γ} (pair {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} a b) = rel-pair am Γ Ψ₁ Ψ₂ (Lq-ok a) (Lq-ok b)
    Lq-ok (fst' p) = rel-∘ rel-fst (Lq-ok p)
    Lq-ok (snd' p) = rel-∘ rel-snd (Lq-ok p)
    Lq-ok (inl' a) = rel-∘ rel-inl (Lq-ok a)
    Lq-ok (inr' b) = rel-∘ rel-inr (Lq-ok b)
    Lq-ok (case' s l r) = ok-case s l r (Lq-ok s) (Lq-ok l) (Lq-ok r)
    Lq-ok unit = rel-drop
    Lq-ok (absurd v) = rel-∘ rel-zero (Lq-ok v)
    Lq-ok (let' {q = G.Zero} e1 e2) = ok-let0 e1 e2 (Lq-ok e2)
    Lq-ok {Γ = Γ} (let' {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {q = G.One} {A = A} e1 e2) =
      rel-∘ (Lq-ok e2) (rel-∘ (rel-bind {Γ = Γ} {A = A} G.One) (rel-let Γ Ψ₂ Ψ₁ (G.One *ᵘ Ψ₁) (⊑ᵘ-*One Ψ₁) (Lq-ok e1)))
    Lq-ok {Γ = Γ} (let' {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {q = G.Many} {A = A} e1 e2) =
      rel-∘ (Lq-ok e2) (rel-∘ (rel-bind {Γ = Γ} {A = A} G.Many) (rel-let Γ Ψ₂ Ψ₁ (G.Many *ᵘ Ψ₁) (⊑ᵘ-*Many Ψ₁) (Lq-ok e1)))
    Lq-ok (int n) = rel-∘ (mkRel λ _ → ret≈R refl) rel-drop
    Lq-ok (float d) = rel-∘ (mkRel λ _ → ret≈R refl) rel-drop
    Lq-ok (num h o e) = ok-num h o e (Lq-ok e)
    Lq-ok (coerce p f) = ok-coerce p f (Lq-ok f)
    Lq-ok {Γ = Γ} (sigOp name c) = ok-sigOp {Γ = Γ} name c
    Lq-ok {Γ = Γ} (closure name) = ok-closure {Γ = Γ} name
    Lq-ok {Γ = Γ} (poly name T) = ok-poly {Γ = Γ} name T
    Lq-ok (closed e) = rel-∘ (Lq-ok e) rel-drop
    Lq-ok {Γ = Γ} (lift-morphism mp) = ok-lift {Γ = Γ} mp
    Lq-ok (morph-app mp x) = ok-mapp mp x (Lq-ok x)
    Lq-ok (comp' f g) = ok-comp f g (Lq-ok f) (Lq-ok g)
    Lq-ok (copair' f g) = ok-copair f g (Lq-ok f) (Lq-ok g)
    Lq-ok (fork' f g) = ok-fork f g (Lq-ok f) (Lq-ok g)
    Lq-ok (curry' f) = ok-curry f (Lq-ok f)
    Lq-ok (cata wf alg) = o-cata wf alg (Lq-ok alg)
    Lq-ok (ana wf c) = o-ana wf c (Lq-ok c)
    Lq-ok (loop r) = ok-loop r (Lq-ok r)
