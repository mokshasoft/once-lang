-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.LinCore.FromExprOk — plan 0.146 B1.7 step 2c (D461): THE BRIDGE'S
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
import Relation.Binary.PropositionalEquality
open import Agda.Builtin.Sigma using (Σ; _,_; fst; snd)
open import Data.Product using (_×_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
import Data.Sum.Relation.Binary.Pointwise
import Data.Empty

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
open import Once.Arith.SigOp.AsBlock using (as-block)
open import Once.Arith.SigOp.AsBlockSound using (as-block-ev)
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
open import Once.LinCore.Flat using (⟦_⟧F; int; float)
open import Once.IR.Semantics.Trace using (T; ret; call; halt)
open import Once.IR.Semantics.Iterative using (T∞; return∞; _>>=∞_; bindBlock)
open import Once.LinCore.NbEPLinCore fmt ans
open Sem using (Lᶜ; cataC; travC)
open import Once.LinCore.FromExpr fmt using (ty; Co; weak; split; carryL; mixL; apω; var-at; bindL; Rs; Lq; castΦ; opL; numL; sigL; cast; clo; callM; refL; mapT; layerEq; dist; coeL; coeR)
open import Once.LinCore.FromExpr fmt using (Pth; p-var; p-fst; p-snd; p-mfst; p-msnd; mq; Rd; rd-path; rd-int; rd-float; rd-num; rd-pair; rd-coe; rd-app; coeRd; rd?; rdw?; rdx?; pth?; lv; Rp; Rt; lentS; scrutL; pairL)
open import Once.LinCore.FromExpr fmt using (Im; im-var; im-lam; im-closed; im-coe; im-app1; im-appω; ImF; imf-lam; imf-closed; CP; cp; cp?; appL; appR; appS; scrutA; lamOr; rdl?)
open import Once.LinCore.FromExpr fmt using (IsPj; pj-id; pj-fst; pj-snd; PjL; pjl; Arm; arm-map; arm-comp; arm?; pjT; rdFst; rdSnd; splitP; ArmD; armOf; forkB; forkL)
open import Once.Surface.Elaborate using (copairIR)
open import Once.Context using (_⊔ᵘ_; ⊑ᵘ-⊔ˡ; ⊑ᵘ-⊔ʳ; ⊑ᵘ-refl)
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
open import Once.Denotation.SurfaceRefs using (Refs)
open import Once.LinCore.FromIR fmt using (⟪⌊⌋⟫-flat)
open import Once.LinCore.Pass fmt ans using (ev; evB)
import Once.LinCore.Casts
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
open import Once.LinCore.Bisim fmt ans using (_≈_; Bl; Bl-refl; ≈-blk; ret-bind; bind-return; bind-assoc; assocB; ≈step; ≈call; ≈halt; ≈-refl; ≈-trans; ≈-sym; >>=-cong; _≈[_]_; ret≈R; >>=-congR; ≈-≈R; ≈R-≈; pair-drop; ≈haltR; iter-congR; module _≈_; module _≈[_]_)
open _≈[_]_ using (blockR)
open _≈_ using (block≈)
open import Data.Sum using (_⊎_; inj₁; inj₂)

------------------------------------------------------------------------
-- 1. THE MONAD: a bind of a return is its continuation, by `block`'s
-- definition.
------------------------------------------------------------------------

-- a computation that returns at once, bound
bind-pure : ∀ {X Y} {m : T∞ X} {x : X} {k : X → T∞ Y} → m ≈ return∞ x → (m >>=∞ k) ≈ k x
bind-pure p = ≈-trans (>>=-cong p (λ _ → ≈-refl)) ret-bind

------------------------------------------------------------------------
-- 2. PURE TERMS: a term whose meaning returns a value at once.
------------------------------------------------------------------------

-- ★ D494: a projection's value
pjv : ∀ {m} {A B : Ty m} {mp : Map A B} → IsPj mp → ⟦ ty A ⟧ → ⟦ ty B ⟧
pjv pj-id  x = x
pjv pj-fst x = fst x
pjv pj-snd x = snd x

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

  -- ★ D494: a projection, a half read beside the whole, and the fork's routing
  p-pjT : ∀ {m E} {A B : Ty m} {mp : Map A B} (p : IsPj mp) → Pure (pjT {L} {E = E} p) (pjv p)
  p-pjT pj-id  e x = ≈-refl
  p-pjT pj-fst e x = bind-pure (≈-trans ret-bind ret-bind)
  p-pjT pj-snd e x = bind-pure (≈-trans ret-bind ret-bind)

  -- (each case proved on its own term: a composite's value functions are not
  -- solved by unification once `Lᶜ` has run the term)
  p-splitP : ∀ {m E} {A Af Ag : Ty m} {pf : Map A Af} {pg : Map A Ag} (p : IsPj pf) (q : IsPj pg)
           → Pure (splitP {L} {E = E} p q) (λ x → pjv p x , pjv q x)
  p-splitP pj-id  pj-id  e x = ≈-refl
  p-splitP pj-id  pj-fst e x = ≈-trans (bind-pure ≈-refl) ret-bind
  p-splitP pj-id  pj-snd e x = ≈-trans (bind-pure ≈-refl) ret-bind
  p-splitP pj-fst pj-id  e x = bind-pure (≈-trans (bind-pure ≈-refl) ret-bind)
  p-splitP pj-fst pj-fst e x = bind-pure (bind-pure (≈-trans ret-bind ret-bind))
  p-splitP pj-fst pj-snd e x = ≈-refl
  p-splitP pj-snd pj-id  e x = bind-pure (≈-trans (bind-pure ≈-refl) ret-bind)
  p-splitP pj-snd pj-fst e x = ≈-refl
  p-splitP pj-snd pj-snd e x = bind-pure (bind-pure (≈-trans ret-bind ret-bind))

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

-- (D499: restriction to the whole usage is the context itself)
wv-refl : ∀ {m n} {Γ : Ctx m n} (Ψ : Usage n) (x : ⟦ Co Γ Ψ ⟧) → wv {Γ = Γ} (⊑ᵘ-refl Ψ) x ≡ x
wv-refl {Γ = SC.∅}       []           x       = refl
wv-refl {Γ = Γ SC.▸ A} (G.Zero ∷ Ψ) x       = wv-refl {Γ = Γ} Ψ x
wv-refl {Γ = Γ SC.▸ A} (G.One  ∷ Ψ) (x , a) = cong (_, a) (wv-refl {Γ = Γ} Ψ x)
wv-refl {Γ = Γ SC.▸ A} (G.Many ∷ Ψ) (x , a) = cong (_, a) (wv-refl {Γ = Γ} Ψ x)

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

-- ★ D477: restrictions compose (a restriction's value is fixed by the usages)
wv-comp : ∀ {m n} {Γ : Ctx m n} {Ψ Ψ′ Φ : Usage n} (p : Ψ ⊑ᵘ Ψ′) (q : Ψ′ ⊑ᵘ Φ) (r : Ψ ⊑ᵘ Φ) (e : ⟦ Co Γ Φ ⟧)
        → wv {Γ = Γ} p (wv {Γ = Γ} q e) ≡ wv {Γ = Γ} r e
wv-comp {Γ = SC.∅}       []         []         []         e       = refl
wv-comp {Γ = Γ SC.▸ A} (z≤z ⊑∷ p) (z≤z ⊑∷ q) (z≤z ⊑∷ r) e       = wv-comp {Γ = Γ} p q r e
wv-comp {Γ = Γ SC.▸ A} (z≤z ⊑∷ p) (z≤o ⊑∷ q) (z≤o ⊑∷ r) (e , a) = wv-comp {Γ = Γ} p q r e
wv-comp {Γ = Γ SC.▸ A} (z≤z ⊑∷ p) (z≤m ⊑∷ q) (z≤m ⊑∷ r) (e , a) = wv-comp {Γ = Γ} p q r e
wv-comp {Γ = Γ SC.▸ A} (z≤o ⊑∷ p) (o≤o ⊑∷ q) (z≤o ⊑∷ r) (e , a) = wv-comp {Γ = Γ} p q r e
wv-comp {Γ = Γ SC.▸ A} (z≤o ⊑∷ p) (o≤m ⊑∷ q) (z≤m ⊑∷ r) (e , a) = wv-comp {Γ = Γ} p q r e
wv-comp {Γ = Γ SC.▸ A} (z≤m ⊑∷ p) (m≤m ⊑∷ q) (z≤m ⊑∷ r) (e , a) = wv-comp {Γ = Γ} p q r e
wv-comp {Γ = Γ SC.▸ A} (o≤o ⊑∷ p) (o≤o ⊑∷ q) (o≤o ⊑∷ r) (e , a) = cong (_, a) (wv-comp {Γ = Γ} p q r e)
wv-comp {Γ = Γ SC.▸ A} (o≤o ⊑∷ p) (o≤m ⊑∷ q) (o≤m ⊑∷ r) (e , a) = cong (_, a) (wv-comp {Γ = Γ} p q r e)
wv-comp {Γ = Γ SC.▸ A} (o≤m ⊑∷ p) (m≤m ⊑∷ q) (o≤m ⊑∷ r) (e , a) = cong (_, a) (wv-comp {Γ = Γ} p q r e)
wv-comp {Γ = Γ SC.▸ A} (m≤m ⊑∷ p) (m≤m ⊑∷ q) (m≤m ⊑∷ r) (e , a) = cong (_, a) (wv-comp {Γ = Γ} p q r e)

-- the split's halves are the two restrictions
sv-l : ∀ {m n} (Γ : Ctx m n) (Ψ₁ Ψ₂ : Usage n) (x : ⟦ Co Γ (Ψ₁ +ᵘ Ψ₂) ⟧) → fst (sv Γ Ψ₁ Ψ₂ x) ≡ wv {Γ = Γ} (⊑ᵘ-+ˡ Ψ₁ Ψ₂) x
sv-l SC.∅          []          []          x       = refl
sv-l (Γ SC.▸ A) (G.Zero ∷ Ψ₁) (G.Zero ∷ Ψ₂) x       = sv-l Γ Ψ₁ Ψ₂ x
sv-l (Γ SC.▸ A) (G.Zero ∷ Ψ₁) (G.One  ∷ Ψ₂) (x , a) = sv-l Γ Ψ₁ Ψ₂ x
sv-l (Γ SC.▸ A) (G.Zero ∷ Ψ₁) (G.Many ∷ Ψ₂) (x , a) = sv-l Γ Ψ₁ Ψ₂ x
sv-l (Γ SC.▸ A) (G.One  ∷ Ψ₁) (G.Zero ∷ Ψ₂) (x , a) = cong (_, a) (sv-l Γ Ψ₁ Ψ₂ x)
sv-l (Γ SC.▸ A) (G.Many ∷ Ψ₁) (G.Zero ∷ Ψ₂) (x , a) = cong (_, a) (sv-l Γ Ψ₁ Ψ₂ x)
sv-l (Γ SC.▸ A) (G.One  ∷ Ψ₁) (G.One  ∷ Ψ₂) (x , a) = cong (_, a) (sv-l Γ Ψ₁ Ψ₂ x)
sv-l (Γ SC.▸ A) (G.One  ∷ Ψ₁) (G.Many ∷ Ψ₂) (x , a) = cong (_, a) (sv-l Γ Ψ₁ Ψ₂ x)
sv-l (Γ SC.▸ A) (G.Many ∷ Ψ₁) (G.One  ∷ Ψ₂) (x , a) = cong (_, a) (sv-l Γ Ψ₁ Ψ₂ x)
sv-l (Γ SC.▸ A) (G.Many ∷ Ψ₁) (G.Many ∷ Ψ₂) (x , a) = cong (_, a) (sv-l Γ Ψ₁ Ψ₂ x)

sv-r : ∀ {m n} (Γ : Ctx m n) (Ψ₁ Ψ₂ : Usage n) (x : ⟦ Co Γ (Ψ₁ +ᵘ Ψ₂) ⟧) → snd (sv Γ Ψ₁ Ψ₂ x) ≡ wv {Γ = Γ} (⊑ᵘ-+ʳ Ψ₁ Ψ₂) x
sv-r SC.∅          []          []          x       = refl
sv-r (Γ SC.▸ A) (G.Zero ∷ Ψ₁) (G.Zero ∷ Ψ₂) x       = sv-r Γ Ψ₁ Ψ₂ x
sv-r (Γ SC.▸ A) (G.Zero ∷ Ψ₁) (G.One  ∷ Ψ₂) (x , a) = cong (_, a) (sv-r Γ Ψ₁ Ψ₂ x)
sv-r (Γ SC.▸ A) (G.Zero ∷ Ψ₁) (G.Many ∷ Ψ₂) (x , a) = cong (_, a) (sv-r Γ Ψ₁ Ψ₂ x)
sv-r (Γ SC.▸ A) (G.One  ∷ Ψ₁) (G.Zero ∷ Ψ₂) (x , a) = sv-r Γ Ψ₁ Ψ₂ x
sv-r (Γ SC.▸ A) (G.Many ∷ Ψ₁) (G.Zero ∷ Ψ₂) (x , a) = sv-r Γ Ψ₁ Ψ₂ x
sv-r (Γ SC.▸ A) (G.One  ∷ Ψ₁) (G.One  ∷ Ψ₂) (x , a) = cong (_, a) (sv-r Γ Ψ₁ Ψ₂ x)
sv-r (Γ SC.▸ A) (G.One  ∷ Ψ₁) (G.Many ∷ Ψ₂) (x , a) = cong (_, a) (sv-r Γ Ψ₁ Ψ₂ x)
sv-r (Γ SC.▸ A) (G.Many ∷ Ψ₁) (G.One  ∷ Ψ₂) (x , a) = cong (_, a) (sv-r Γ Ψ₁ Ψ₂ x)
sv-r (Γ SC.▸ A) (G.Many ∷ Ψ₁) (G.Many ∷ Ψ₂) (x , a) = cong (_, a) (sv-r Γ Ψ₁ Ψ₂ x)

-- ★ D477: a read's derivation is unique (it follows the expression)
pth-irr : ∀ {m n} {Γ : Ctx m n} {Ψ : Usage n} {A : Ty m} {e : Expr Γ Ψ A} (d d′ : Pth e) → d ≡ d′
pth-irr (p-var i)  (p-var .i)  = refl
pth-irr (p-fst d)  (p-fst d′)  = cong p-fst (pth-irr d d′)
pth-irr (p-snd d)  (p-snd d′)  = cong p-snd (pth-irr d d′)
pth-irr (p-mfst d) (p-mfst d′) = cong p-mfst (pth-irr d d′)
pth-irr (p-msnd d) (p-msnd d′) = cong p-msnd (pth-irr d d′)

rd-irr : ∀ {m n} {Γ : Ctx m n} {Ψ : Usage n} {A : Ty m} {e : Expr Γ Ψ A} (d d′ : Rd e) → d ≡ d′
rd-irr (rd-path d)     (rd-path d′)      = cong rd-path (pth-irr d d′)
rd-irr (rd-path ())    (rd-int z)
rd-irr (rd-path ())    (rd-float x)
rd-irr (rd-path ())    (rd-num h o d′)
rd-irr (rd-path ())    (rd-pair a′ b′)
rd-irr (rd-int z)      (rd-path ())
rd-irr (rd-int z)      (rd-int .z)       = refl
rd-irr (rd-float x)    (rd-path ())
rd-irr (rd-float x)    (rd-float .x)     = refl
rd-irr (rd-num h o d)  (rd-path ())
rd-irr (rd-num h o d)  (rd-num .h .o d′) = cong (rd-num h o) (rd-irr d d′)
rd-irr (rd-pair a b)   (rd-path ())
rd-irr (rd-path ())    (rd-coe c d′)
rd-irr (rd-coe c d)    (rd-path ())
rd-irr (rd-coe c d)    (rd-coe .c d′)    = cong (rd-coe c) (rd-irr d d′)
rd-irr (rd-pair a b)   (rd-pair a′ b′)   = Relation.Binary.PropositionalEquality.cong₂ rd-pair (rd-irr a a′) (rd-irr b b′)
rd-irr (rd-path ())    (rd-app p′ d′)
rd-irr (rd-app p d)    (rd-path ())
rd-irr (rd-app p d)    (rd-app p′ d′)    = Relation.Binary.PropositionalEquality.cong₂ rd-app (pth-irr p p′) (rd-irr d d′)

-- (D495: a path is no case combinator)
cp-pth : ∀ {m n} {Γ : Ctx m n} {Ψ : Usage n} {T : Ty m} {f : Expr Γ Ψ T} → CP f → Pth f → Data.Empty.⊥
cp-pth (cp _ _) ()

-- a variable's value in its own context
vval : ∀ {m n} {Γ : Ctx m n} (i : Data.Fin.Fin n) → ⟦ Co Γ (singleUse i G.One) ⟧ → ⟦ ty (SC.lookup Γ i) ⟧
vval {Γ = Γ SC.▸ A} Data.Fin.zero    (y , a) = a
vval {Γ = Γ SC.▸ A} (Data.Fin.suc i) y       = vval {Γ = Γ} i y

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

module RelM {L : Cx} (δ : Env L) (ρ : CallEnv) where

  -- (a record, so that the two terms stay visible to unification)
  record Rel {A B : IRTy} (t : LTm L ⟪ A ⟫ ⟪ B ⟫) (t′ : M.IR A B) : Set where
    constructor mkRel
    field rel : ∀ {x x′} → W A x x′ → Lᶜ δ t tt x ≈[ W B ] evalᴰ fmt ρ t′ x′
  open Rel using (rel)

  -- the relation's content, as a plain function (for importers: no re-export)
  relOf : ∀ {A B : IRTy} {t : LTm L ⟪ A ⟫ ⟪ B ⟫} {t′ : M.IR A B} → Rel t t′ → ∀ {x x′} → W A x x′ → Lᶜ δ t tt x ≈[ W B ] evalᴰ fmt ρ t′ x′
  relOf r = rel r

  rel-∘ : ∀ {A B C} {f : LTm L ⟪ B ⟫ ⟪ C ⟫} {f′ : M.IR B C} {g : LTm L ⟪ A ⟫ ⟪ B ⟫} {g′ : M.IR A B}
        → Rel f f′ → Rel g g′ → Rel (f ∘l g) (f′ M.∘ g′)
  rel-∘ rf rg = mkRel λ w → >>=-congR (relOf rg w) (relOf rf)

  -- pure on both sides, with related values
  rel-pure : ∀ {A B} {t : LTm L ⟪ A ⟫ ⟪ B ⟫} {t′ : M.IR A B} {v v′}
           → Pure δ t v → PureI ρ t′ v′ → (∀ {x x′} → W A x x′ → W B (v x) (v′ x′)) → Rel t t′
  rel-pure p q r = mkRel λ {x} {x′} w → ≈-≈R (p tt x) (≈R-≈ (ret≈R (r w)) (≈-sym (q x′)))

  rel-weak : ∀ (am : M.AllocMode) {m n} {Γ : Ctx m n} {Ψ Ψ′ : Usage n} (p : Ψ ⊑ᵘ Ψ′)
           → Rel (weak {Γ = Γ} p) (restrictEnv {Γ = Γ} am p)
  rel-weak am {Γ = Γ} p = rel-pure {t = weak {Γ = Γ} p} {t′ = restrictEnv {Γ = Γ} am p} (weak-pure δ {E = One} {Γ = Γ} p) (restrict-pure ρ am {Γ = Γ} p) (weak-W {Γ = Γ} p)

  -- ★ the application: a closure applied owned, against `apply`
  rel-apω : ∀ {π A B} → Rel (apω {g = grade π} {⟪ A ⟫} {⟪ B ⟫}) (M.apply {A} {B} {π})
  rel-apω {π} {A} {B} = mkRel λ { {f , a} {f′ , a′} (wf , wa) → wf wa }

  -- ★ THE SPLIT against the IR's copy into two restrictions
  rel-pair : ∀ (am : M.AllocMode) {m n} (Γ : Ctx m n) (Ψ₁ Ψ₂ : Usage n) {A B : IRTy}
             {a : LTm L (Co Γ Ψ₁) ⟪ A ⟫} {a′ : M.IR ⌊ ⟦ Γ ↾ Ψ₁ ⟧ᶜ ⌋ A}
             {b : LTm L (Co Γ Ψ₂) ⟪ B ⟫} {b′ : M.IR ⌊ ⟦ Γ ↾ Ψ₂ ⟧ᶜ ⌋ B}
           → Rel a a′ → Rel b b′
           → Rel ((a ⊗l b) ∘l split Γ Ψ₁ Ψ₂)
                 M.⟨ a′ M.∘ restrictEnv {Γ = Γ} am (⊑ᵘ-+ˡ Ψ₁ Ψ₂) , b′ M.∘ restrictEnv {Γ = Γ} am (⊑ᵘ-+ʳ Ψ₁ Ψ₂) ⟩
  rel-pair am Γ Ψ₁ Ψ₂ ra rb = mkRel λ {x} {x′} w → let sw = split-W Γ Ψ₁ Ψ₂ w in
    ≈-≈R (bind-pure (split-pure δ Γ Ψ₁ Ψ₂ tt x))
      (≈R-≈ (>>=-congR (relOf ra (proj₁ sw)) (λ r → >>=-congR (relOf rb (proj₂ sw)) (λ r′ → ret≈R (r , r′))))
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
  open RelM δ ρ

  -- a rewrite on the IR's side
  rel-≈ʳ : ∀ {A B} {t : LTm L ⟪ A ⟫ ⟪ B ⟫} {t′ t″ : M.IR A B} → Rel t t′ → (∀ x′ → evalᴰ fmt ρ t′ x′ ≈ evalᴰ fmt ρ t″ x′) → Rel t t″
  rel-≈ʳ r e = mkRel λ {x} {x′} w → ≈R-≈ (relOf r w) (e x′)

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
  open RelM δ ρ

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
  open RelM δ ρ

  -- the body, on a copy of the environment it reads lent
  copyIn-≈ : ∀ {X A B} (b : LTm L (X ⊗t A) B) e a → Lᶜ δ (copyIn b) e a ≈ Lᶜ δ b tt (e , a)
  copyIn-≈ b e a = bind-pure (≈-trans ret-bind (≈-trans ret-bind ret-bind))

  -- ★ at either grade: a block's meaning is its computation's (`Grade.blk-coh`)
  rel-cloG : ∀ (π : G.Purity) {X A B : IRTy} {b : LTm L (⟪ X ⟫ ⊗t ⟪ A ⟫) ⟪ B ⟫} {b′ : M.IR (X I.* A) B}
               (γ : Gd (grade π) b)
           → Rel b b′ → Rel (llamωᶜ b γ) (M.curry {π = π} b′)
  rel-cloG (G.fin φ) {b = b} γ rb = mkRel λ {x} {x′} w →
    ret≈R (λ {a} {a′} wa → ≈-≈R (≈-sym (blk-coh δ γ tt (x , a))) (relOf rb (w , wa)))
  rel-cloG G.eff {b = b} γ rb = mkRel λ {x} {x′} w →
    ret≈R (λ {a} {a′} wa → relOf rb (w , wa))

  -- ★ plan 0.157 S2: a closure whose body READS its environment (`llamω`):
  -- related through its body's run on the lent environment
  rel-cloL : ∀ (π : G.Purity) {X A B : IRTy} {b : Tm L ⟪ X ⟫ ⟪ A ⟫ ⟪ B ⟫} {b′ : M.IR (X I.* A) B}
               (γ : Gd (grade π) b)
           → (∀ {x x′} → W X x x′ → ∀ {a a′} → W A a a′ → Lᶜ δ b x a ≈[ W B ] evalᴰ fmt ρ b′ (x′ , a′))
           → Rel (llamω b γ) (M.curry {π = π} b′)
  rel-cloL (G.fin φ) γ rb = mkRel λ {x} {x′} w →
    ret≈R (λ {a} {a′} wa → ≈-≈R (≈-sym (blk-coh δ γ x a)) (rb w wa))
  rel-cloL G.eff γ rb = mkRel λ {x} {x′} w →
    ret≈R (λ {a} {a′} wa → rb w wa)

------------------------------------------------------------------------
-- 10. ★★ THE BRIDGE'S MEANING, by induction on the expression, every clause
-- proved; its premise is the expression's references, related (`RefOK`, by
-- `SurfaceRefs.Refs`): a reference at another grade than its definition's could
-- not be a block, so the program's linking, grades included, is its obligation
-- (`Calls.rel-ref` gives it from a table where it holds, `CallsOK`).
------------------------------------------------------------------------

module Main {L : Cx} (rs : Rs L) (δ : Env L) (cs : CanonicalName → (A B : IRTy) → ⟦ A ⟧ᴰᴵ → T∞ ⟦ B ⟧ᴰᴵ) (am : M.AllocMode) where
  ρ : CallEnv
  ρ = callEnv cs ans

  open RelM δ ρ
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
      (mkRel λ w → ≈-≈R ret-bind (>>=-congR (relOf g w) (λ r → ≈-≈R ret-bind (≈R-≈ (ret≈R (r , tt)) (≈-sym ret-bind)))))

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
  apω-≈ {g} {A} {B} f a = ≈-refl

  ok-comp : ∀ {m n} {Γ : Ctx m n} {Ψ₁ Ψ₂ : Usage n} {A B C : Ty m} {π}
              (f : Expr Γ Ψ₁ (B ⇒[ G.mk-kind G.Many π ] C)) (g : Expr Γ Ψ₂ (A ⇒[ G.mk-kind G.Many π ] B))
            → Goal f → Goal g → Goal (comp' f g)
  ok-comp {Γ = Γ} {Ψ₁} {Ψ₂} {π = π} f g rf rg =
    rel-∘ (rel-cloL π _ compL) (rel-pairW Γ Ψ₁ Ψ₂ (G.Many *ᵘ Ψ₂) (⊑ᵘ-*Many Ψ₂) rf rg)
    where
      -- the lent body: `g` applied lent, then `f`
      compL : ∀ {A B C : IRTy} {x x′} → W ((B I.⇛[ π ] C) I.* (A I.⇛[ π ] B)) x x′ → ∀ {a a′} → W A a a′
            → Lᶜ δ (bfst (bev {g = grade π} {⟪ B ⟫} {⟪ C ⟫}) ∘l bsnd (bev {g = grade π} {⟪ A ⟫} {⟪ B ⟫})) x a
              ≈[ W C ] evalᴰ fmt ρ (M.apply {B} {C} {π} M.∘ M.⟨ M.fst M.∘ M.fst , M.apply {A} {B} {π} M.∘ M.⟨ M.snd M.∘ M.fst , M.snd ⟩ ⟩) (x′ , a′)
      compL {x = f₀ , g₀} {f′ , g′} (wf , wg) {a} {a′} wa =
        ≈R-≈ (>>=-congR (wg wa) (λ wb → wf wb))
             (≈-sym (≈-trans (>>=-cong (≈-trans (bind-pure ret-bind) (>>=-cong (bind-pure (≈-trans (bind-pure ret-bind) ret-bind)) (λ _ → ≈-refl))) (λ _ → ≈-refl))
                             (≈-trans (bind-assoc _ _ _) (>>=-cong ≈-refl (λ _ → ret-bind)))))

  ------------------------------------------------------------------------
  -- ★ D494: THE FORK, BY ITS ARMS. What the fork keeps for an arm, run on
  -- the arm's part of an argument, is the IR's closure of the arm applied to
  -- the whole argument (`ArmR`); each kind of arm keeps such a thing
  -- (`ArmOK`); the routing returns the parts at once (`p-splitP`).
  ------------------------------------------------------------------------

  ArmR : ∀ {m n} {Γ : Ctx m n} {Ψ : Usage n} {A B : Ty m} {π} (a : ArmD rs Γ Ψ A B π)
       → ⟦ ArmD.Ek a ⟧ → ⟦ ⌊ A ⌋ I.⇛[ π ] ⌊ B ⌋ ⟧ᴰᴵ → Set
  ArmR {A = A} {B} a e fv = ∀ {x x′} → W ⌊ A ⌋ x x′ → Lᶜ δ (ArmD.ap a) e (pjv (ArmD.pj a) x) ≈[ W ⌊ B ⌋ ] fv x′

  ArmOK : ∀ {m n} {Γ : Ctx m n} {Ψ : Usage n} {A B : Ty m} {π} (f : Expr Γ Ψ (A ⇒[ G.mk-kind G.Many π ] B)) → Maybe (Arm f) → Set
  ArmOK {Γ = Γ} {Ψ} f d = ∀ {γ γ′} → W ⌊ ⟦ Γ ↾ Ψ ⟧ᶜ ⌋ γ γ′
                         → Lᶜ δ (ArmD.env (armOf rs f d)) tt γ ≈[ ArmR (armOf rs f d) ] evalᴰ fmt ρ (elaborate am f) γ′

  -- a projection's map returns its part at once
  mapT-pj : ∀ {m} {A B : Ty m} {mp : Map A B} (p : IsPj mp) → Pure δ (mapT {L} mp) (pjv p)
  mapT-pj pj-id  e x = ≈-refl
  mapT-pj pj-fst e x = bind-pure (≈-trans ret-bind ret-bind)
  mapT-pj pj-snd e x = bind-pure (≈-trans ret-bind ret-bind)

  -- the fork's body on what it keeps, against `forkIR`'s: each arm on its part, in order
  forkB-≈ : ∀ {m n} {Γ : Ctx m n} {Ψ₁ Ψ₂ : Usage n} {A B C : Ty m} {π} (af : ArmD rs Γ Ψ₁ A B π) (ag : ArmD rs Γ Ψ₂ A C π)
              {ef eg fv gv} → ArmR af ef fv → ArmR ag eg gv
          → ∀ {x x′} → W ⌊ A ⌋ x x′
          → Lᶜ δ (forkB rs af ag) (ef , eg) x
            ≈[ W (⌊ B ⌋ I.* ⌊ C ⌋) ] evalᴰ fmt ρ (M.⟨ M.apply {⌊ A ⌋} {⌊ B ⌋} {π} M.∘ M.⟨ M.fst M.∘ M.fst , M.snd ⟩
                                                 , M.apply {⌊ A ⌋} {⌊ C ⌋} {π} M.∘ M.⟨ M.snd M.∘ M.fst , M.snd ⟩ ⟩) ((fv , gv) , x′)
  forkB-≈ af ag {ef} {eg} rf rg {x} wx =
    ≈-≈R (bind-pure (p-splitP δ (ArmD.pj af) (ArmD.pj ag) (ef , eg) x))
      (≈R-≈ (>>=-congR (rf wx) (λ r → >>=-congR (rg wx) (λ r′ → ret≈R (r , r′))))
            (≈-sym (>>=-cong (bind-pure (≈-trans (bind-pure ret-bind) ret-bind))
                             (λ _ → >>=-cong (bind-pure (≈-trans (bind-pure ret-bind) ret-bind)) (λ _ → ≈-refl)))))

  -- a closure whose body reads what it keeps, related through any relation on what it keeps
  cloLR : ∀ (π : G.Purity) {Xc : LTy} {X A B : IRTy} {b : Tm L Xc ⟪ A ⟫ ⟪ B ⟫} {b′ : M.IR (X I.* A) B}
            (γ : Gd (grade π) b) (R : ⟦ Xc ⟧ → ⟦ X ⟧ᴰᴵ → Set)
        → (∀ {x x′} → R x x′ → ∀ {a a′} → W A a a′ → Lᶜ δ b x a ≈[ W B ] evalᴰ fmt ρ b′ (x′ , a′))
        → ∀ {x x′} → R x x′ → Lᶜ δ (llamω {E = One} b γ) tt x ≈[ W (A I.⇛[ π ] B) ] evalᴰ fmt ρ (M.curry {π = π} b′) x′
  cloLR (G.fin φ) γ R rb {x} r = ret≈R (λ {a} {a′} wa → ≈-≈R (≈-sym (blk-coh δ γ x a)) (rb r wa))
  cloLR G.eff     γ R rb r = ret≈R (λ wa → rb r wa)

  ok-fork : ∀ {m n} {Γ : Ctx m n} {Ψ₁ Ψ₂ : Usage n} {A B C : Ty m} {π}
              (f : Expr Γ Ψ₁ (A ⇒[ G.mk-kind G.Many π ] B)) (g : Expr Γ Ψ₂ (A ⇒[ G.mk-kind G.Many π ] C))
            → ArmOK f (arm? f) → ArmOK g (arm? g) → Goal (fork' f g)
  ok-fork {Γ = Γ} {Ψ₁} {Ψ₂} {A} {B} {C} {π} f g af ag = mkRel λ {x} {x′} w → let sw = split-W Γ Ψ₁ Ψ₂ w in
    ≈-≈R (bind-pure (split-pure δ Γ Ψ₁ Ψ₂ tt x))
      (>>=-congR
        (≈R-≈ (>>=-congR {R = ArmR AF} (af (proj₁ sw))
                         (λ r → >>=-congR {R = ArmR AG} (ag (proj₂ sw))
                                  (λ r′ → ret≈R {R = λ e e′ → ArmR AF (proj₁ e) (proj₁ e′) × ArmR AG (proj₂ e) (proj₂ e′)}
                                                ((λ {_} {_} → r) , (λ {_} {_} → r′)))))
              (≈-sym (>>=-cong (bind-pure (restrict-pure ρ am {Γ = Γ} (⊑ᵘ-+ˡ Ψ₁ Ψ₂) x′))
                               (λ _ → >>=-cong (bind-pure (restrict-pure ρ am {Γ = Γ} (⊑ᵘ-+ʳ Ψ₁ Ψ₂) x′)) (λ _ → ≈-refl)))))
        (cloLR π {X = (⌊ A ⌋ I.⇛[ π ] ⌊ B ⌋) I.* (⌊ A ⌋ I.⇛[ π ] ⌊ C ⌋)} {A = ⌊ A ⌋} {B = ⌊ B ⌋ I.* ⌊ C ⌋}
               {b′ = M.⟨ M.apply {⌊ A ⌋} {⌊ B ⌋} {π} M.∘ M.⟨ M.fst M.∘ M.fst , M.snd ⟩
                       , M.apply {⌊ A ⌋} {⌊ C ⌋} {π} M.∘ M.⟨ M.snd M.∘ M.fst , M.snd ⟩ ⟩}
               _ (λ e e′ → ArmR AF (proj₁ e) (proj₁ e′) × ArmR AG (proj₂ e) (proj₂ e′))
               (λ r wa → forkB-≈ AF AG (proj₁ r) (proj₂ r) wa)))
    where
      AF = armOf rs f (arm? f)
      AG = armOf rs g (arm? g)

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
  -- (the core runs the op as its block, D464: master's op means the same, `as-block-ev`)
  rel-op {A} {B} si = mkRel λ {x} {x′} w →
    subst (λ m → Lᶜ δ (opL {L} {One} si) tt x ≈[ W ⌊ B ⌋ ] m) (as-block-ev fmt ρ si x′)
      (subst (λ m → m ≈[ W ⌊ B ⌋ ] _)
             (sym (subst₂-ev (sym (⟪⌊⌋⟫-flat (SigOpInfo.baseA si))) (sym (⟪⌊⌋⟫-flat (SigOpInfo.conB si))) (λ y → refl) x))
             (BP.Casts.op≈ (casts δ cs) (as-block si) w))

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
               (γ : Gd (grade π) (bc ∘l Once.LinCore.PassTr.dropl fmt {E = One} {A = One}))
           → Rel bc b″ → Rel (llamωᶜ (bc ∘l Once.LinCore.PassTr.dropl fmt) γ ∘l drop {A = ⟪ X ⟫}) (M.curry {X} {A} {B} {π} (b″ M.∘ M.snd))
  rel-cloD (G.fin φ) {bc = bc} γ rb = mkRel λ {x} {x′} w → ≈-≈R ret-bind (ret≈R (λ {a} {a′} wa →
    ≈-≈R (≈-trans (≈-sym (blk-coh δ γ tt (tt , a))) (bind-pure (bind-pure (≈-trans ret-bind ret-bind))))
         (≈R-≈ (relOf rb wa) (≈-sym ret-bind))))
  rel-cloD G.eff {bc = bc} γ rb = mkRel λ {x} {x′} w → ≈-≈R ret-bind (ret≈R (λ {a} {a′} wa →
    ≈-≈R (bind-pure (bind-pure (≈-trans ret-bind ret-bind)))
         (≈R-≈ (relOf rb wa) (≈-sym ret-bind))))

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

  -- the projection, against the IR's map, on related arguments
  pj-W : ∀ {m} {A B : Ty m} {mp : Map A B} (p : IsPj mp) {x x′} → W ⌊ A ⌋ x x′
       → return∞ (pjv p x) ≈[ W ⌊ B ⌋ ] evalᴰ fmt ρ (mapIR mp) x′
  pj-W {mp = mp} p {x} wx = ≈-≈R (≈-sym (mapT-pj p tt x)) (relOf (rel-map mp) wx)

  -- the whole closure, on the whole argument: its relation is the arm's
  armOk-all : ∀ {m n} {Γ : Ctx m n} {Ψ : Usage n} {A B : Ty m} {π} (f : Expr Γ Ψ (A ⇒[ G.mk-kind G.Many π ] B))
            → Goal f → ArmOK f nothing
  armOk-all f rf w = relOf rf w

  -- a projection: nothing kept, the part itself
  armOk-map : ∀ {m n} {Γ : Ctx m n} {A B : Ty m} {π} {mp : Map A B} (p : IsPj mp)
            → ArmOK (lift-morphism {Γ = Γ} {π = π} mp) (just (arm-map (pjl p)))
  armOk-map {mp = mp} p w = ret≈R (λ {x} {x′} wx → ≈R-≈ (pj-W p wx) (≈-sym ret-bind))

  -- the IR's composite applied: the inner closure, then the outer
  comp-ev : ∀ {π} {A B C : IRTy} (hv : ⟦ B I.⇛[ π ] C ⟧ᴰᴵ) (mv : ⟦ A I.⇛[ π ] B ⟧ᴰᴵ) (a′ : ⟦ A ⟧ᴰᴵ)
          → evalᴰ fmt ρ (M.apply {B} {C} {π} M.∘ M.⟨ M.fst M.∘ M.fst , M.apply {A} {B} {π} M.∘ M.⟨ M.snd M.∘ M.fst , M.snd ⟩ ⟩) ((hv , mv) , a′)
            ≈ (mv a′ >>=∞ hv)
  comp-ev hv mv a′ =
    ≈-trans (>>=-cong (≈-trans (bind-pure ret-bind) (>>=-cong (bind-pure (≈-trans (bind-pure ret-bind) ret-bind)) (λ _ → ≈-refl))) (λ _ → ≈-refl))
            (≈-trans (bind-assoc _ _ _) (>>=-cong ≈-refl (λ _ → ret-bind)))

  -- a closure after a projection: the closure kept, run on the part
  armOk-comp : ∀ {m n} {Γ : Ctx m n} {Ψ : Usage n} {A A′ B : Ty m} {π} (h : Expr Γ Ψ (A′ ⇒[ G.mk-kind G.Many π ] B))
               {mp : Map A A′} (p : IsPj mp) → Goal h
             → ArmOK (comp' h (lift-morphism {Γ = Γ} {π = π} mp)) (just (arm-comp h (pjl p)))
  armOk-comp {Γ = Γ} {Ψ} {A} {A′} {B} {π} h {mp} p rh {γ} {γ′} w =
    ≈-≈R (≈-trans (bind-pure (weak-pure δ {E = One} {Γ = Γ} q tt γ)) (≈-sym bind-return))
      (≈R-≈ (>>=-congR (relOf rh (weak-W {Γ = Γ} q w))
                       (λ {e} {hv} wh → ret≈R (λ {x} {x′} wx →
                          ≈-≈R (≈-sym ret-bind)
                            (≈R-≈ (>>=-congR (pj-W p wx) (λ wy → wh wy))
                                  (≈-sym (≈-trans (comp-ev {π} {⌊ A ⌋} {⌊ A′ ⌋} {⌊ B ⌋} hv _ x′) (>>=-cong ret-bind (λ _ → ≈-refl))))))))
            (≈-sym (≈-trans (>>=-cong (>>=-cong (bind-pure (restrict-pure ρ am {Γ = Γ} q γ′))
                                                (λ _ → bind-pure (≈-trans (bind-pure (restrict-pure ρ am {Γ = Γ} q′ γ′)) ≈-refl)))
                                      (λ _ → ≈-refl))
                            (≈-trans (bind-assoc _ _ _) (>>=-cong ≈-refl (λ _ → ret-bind))))))
    where
      q  = ⊑ᵘ-+ˡ Ψ (G.Many *ᵘ SC.zeroUsage)
      q′ = ⊑ᵘ-trans (⊑ᵘ-*Many SC.zeroUsage) (⊑ᵘ-+ʳ Ψ (G.Many *ᵘ SC.zeroUsage))

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
  dist-pure {X} {A} {B} e (x , inj₁ a) = ≈-refl
  dist-pure {X} {A} {B} e (x , inj₂ b) = ≈-refl

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
  rel-lcase rf rg = mkRel λ { (Data.Sum.Relation.Binary.Pointwise.inj₁ w) → relOf rf w ; (Data.Sum.Relation.Binary.Pointwise.inj₂ w) → relOf rg w }

  -- the scrutinee's share split off, the arms' share beside its value
  rel-swapPair : ∀ {m n} (Γ : Ctx m n) (Ψs Φ : Usage n) {S : IRTy} {s : LTm L (Co Γ Ψs) ⟪ S ⟫} {s′ : M.IR ⌊ ⟦ Γ ↾ Ψs ⟧ᶜ ⌋ S}
               → Rel s s′
               → Rel ((lid ⊗l s) ∘l lswap ∘l split Γ Ψs Φ)
                     M.⟨ restrictEnv {Γ = Γ} am (⊑ᵘ-+ʳ Ψs Φ) , s′ M.∘ restrictEnv {Γ = Γ} am (⊑ᵘ-+ˡ Ψs Φ) ⟩
  rel-swapPair Γ Ψs Φ rs′ = mkRel λ {x} {x′} w → let sw = split-W Γ Ψs Φ w in
    ≈-≈R (≈-trans (bind-pure (bind-pure (split-pure δ Γ Ψs Φ tt x))) ret-bind)
      (≈R-≈ (>>=-congR (relOf rs′ (proj₁ sw)) (λ r → ret≈R (proj₂ sw , r)))
            (≈-sym (≈-trans (bind-pure (restrict-pure ρ am {Γ = Γ} (⊑ᵘ-+ʳ Ψs Φ) x′))
                            (>>=-cong (bind-pure (restrict-pure ρ am {Γ = Γ} (⊑ᵘ-+ˡ Ψs Φ) x′)) (λ _ → ≈-refl)))))

  -- an arm's share, beside the bound value
  rel-arm : ∀ {m n} {Γ : Ctx m n} {Ψ Ψ′ : Usage n} {A : IRTy} (p : Ψ ⊑ᵘ Ψ′)
          → Rel (weak {Γ = Γ} p ⊗l lid {A = ⟪ A ⟫}) M.⟨ restrictEnv {Γ = Γ} am p M.∘ M.fst , M.snd ⟩
  rel-arm {Γ = Γ} p = mkRel λ { {x , a} {x′ , a′} (w , wa) →
    ≈-≈R (≈-trans (bind-pure (weak-pure δ {E = One} {Γ = Γ} p tt x)) ret-bind)
      (≈R-≈ (ret≈R (weak-W {Γ = Γ} p w , wa))
            (≈-sym (≈-trans (bind-pure (≈-trans ret-bind (restrict-pure ρ am {Γ = Γ} p x′))) ret-bind))) }

  -- ★ D477: A SCRUTINEE READ IN PLACE means what the split one means: the lent
  -- read is the consuming translation on the restricted context
  private
    -- a conversion's cast keeps a run's meaning
    cast-≈ : ∀ {E₁ E₂ A₁ A₂ B B′} (e : B ≡ B′) (t₁ : Tm L E₁ A₁ B) (t₂ : Tm L E₂ A₂ B) {e₁ a₁ e₂ a₂}
           → Lᶜ δ t₁ e₁ a₁ ≈ Lᶜ δ t₂ e₂ a₂ → Lᶜ δ (cast {E = E₁} refl e t₁) e₁ a₁ ≈ Lᶜ δ (cast {E = E₂} refl e t₂) e₂ a₂
    cast-≈ refl t₁ t₂ h = h

    lv-eq : ∀ {m n} {Γ : Ctx m n} {Φ : Usage n} {X C : LTy} (i : Data.Fin.Fin n) (q : singleUse i G.One ⊑ᵘ Φ)
            (t : Tm L (ty (SC.lookup Γ i)) X C) (e : ⟦ Co Γ Φ ⟧) (a : ⟦ X ⟧)
          → Lᶜ δ (lv {Γ = Γ} i q t) e a ≡ Lᶜ δ t (vval {Γ = Γ} i (wv {Γ = Γ} q e)) a
    lv-eq {Γ = Γ SC.▸ A} Data.Fin.zero    (o≤o ⊑∷ q) t (e , x) a = refl
    lv-eq {Γ = Γ SC.▸ A} Data.Fin.zero    (o≤m ⊑∷ q) t (e , x) a = refl
    lv-eq {Γ = Γ SC.▸ A} (Data.Fin.suc i) (z≤z ⊑∷ q) t e       a = lv-eq {Γ = Γ} i q t e a
    lv-eq {Γ = Γ SC.▸ A} (Data.Fin.suc i) (z≤o ⊑∷ q) t (e , x) a = lv-eq {Γ = Γ} i q t e a
    lv-eq {Γ = Γ SC.▸ A} (Data.Fin.suc i) (z≤m ⊑∷ q) t (e , x) a = lv-eq {Γ = Γ} i q t e a

    var-pure : ∀ {m n} {Γ : Ctx m n} (i : Data.Fin.Fin n) → Pure δ (var-at {L} {One} {Γ = Γ} i) (vval {Γ = Γ} i)
    var-pure {Γ = Γ SC.▸ A} Data.Fin.zero    e x = bind-pure (≈-trans ret-bind ret-bind)
    var-pure {Γ = Γ SC.▸ A} (Data.Fin.suc i) = var-pure {Γ = Γ} i

    pv : ∀ {m n} {Γ : Ctx m n} {Ψ : Usage n} {A : Ty m} {e : Expr Γ Ψ A} → Pth e → ⟦ Co Γ Ψ ⟧ → ⟦ ty A ⟧
    pv {Γ = Γ} (p-var i) y = vval {Γ = Γ} i y
    pv (p-fst d) y = fst (pv d y)
    pv (p-snd d) y = snd (pv d y)
    pv {Γ = Γ} (p-mfst {Ψ = Ψ} d) y = fst (pv d (wv {Γ = Γ} (mq Ψ) y))
    pv {Γ = Γ} (p-msnd {Ψ = Ψ} d) y = snd (pv d (wv {Γ = Γ} (mq Ψ) y))

    path-pure : ∀ {m n} {Γ : Ctx m n} {Ψ : Usage n} {A : Ty m} {e : Expr Γ Ψ A} (d : Pth e) → Pure δ (Lq rs e) (pv d)
    path-pure {Γ = Γ} (p-var i) = var-pure {Γ = Γ} i
    path-pure (p-fst d) e x = ≈-trans (bind-pure (path-pure d e x)) (bind-pure (≈-trans ret-bind ret-bind))
    path-pure (p-snd d) e x = ≈-trans (bind-pure (path-pure d e x)) (bind-pure (≈-trans ret-bind ret-bind))
    path-pure {Γ = Γ} (p-mfst {Ψ = Ψ} d) e x =
      ≈-trans (bind-pure (≈-trans (bind-pure (weak-pure δ {E = One} {Γ = Γ} (mq Ψ) e x)) (path-pure d e (wv {Γ = Γ} (mq Ψ) x))))
              (bind-pure (≈-trans ret-bind ret-bind))
    path-pure {Γ = Γ} (p-msnd {Ψ = Ψ} d) e x =
      ≈-trans (bind-pure (≈-trans (bind-pure (weak-pure δ {E = One} {Γ = Γ} (mq Ψ) e x)) (path-pure d e (wv {Γ = Γ} (mq Ψ) x))))
              (bind-pure (≈-trans ret-bind ret-bind))

    Rp-eq : ∀ {m n} {Γ : Ctx m n} {Ψ Φ : Usage n} {A : Ty m} {X C : LTy} {e : Expr Γ Ψ A} (d : Pth e) (q : Ψ ⊑ᵘ Φ)
            (t : Tm L (ty A) X C) (x : ⟦ Co Γ Φ ⟧) (a : ⟦ X ⟧) → Lᶜ δ (Rp d q t) x a ≡ Lᶜ δ t (pv d (wv {Γ = Γ} q x)) a
    Rp-eq {Γ = Γ} (p-var i) q t x a = lv-eq {Γ = Γ} i q t x a
    Rp-eq (p-fst d) q t x a = Rp-eq d q (bfst t) x a
    Rp-eq (p-snd d) q t x a = Rp-eq d q (bsnd t) x a
    Rp-eq {Γ = Γ} (p-mfst {Ψ = Ψ} d) q t x a =
      trans (Rp-eq d (⊑ᵘ-trans (mq Ψ) q) (bfst t) x a)
            (cong (λ z → Lᶜ δ t (fst (pv d z)) a) (sym (wv-comp {Γ = Γ} (mq Ψ) q (⊑ᵘ-trans (mq Ψ) q) x)))
    Rp-eq {Γ = Γ} (p-msnd {Ψ = Ψ} d) q t x a =
      trans (Rp-eq d (⊑ᵘ-trans (mq Ψ) q) (bsnd t) x a)
            (cong (λ z → Lᶜ δ t (snd (pv d z)) a) (sym (wv-comp {Γ = Γ} (mq Ψ) q (⊑ᵘ-trans (mq Ψ) q) x)))

    -- the lent read's run: the read, the kept share beside it
    lentS-≈ : ∀ {m n} {Γ : Ctx m n} {Ψs Φ : Usage n} {S : Ty m} {s : Expr Γ Ψs S} (d : Rd s) (x : ⟦ Co Γ (Ψs +ᵘ Φ) ⟧)
            → Lᶜ δ (lentS {Γ = Γ} {Ψs} {Φ} d) tt x ≈ (Lᶜ δ (Rt d (⊑ᵘ-+ˡ Ψs Φ)) x tt >>=∞ λ v → return∞ (wv {Γ = Γ} (⊑ᵘ-+ʳ Ψs Φ) x , v))
    lentS-≈ {Γ = Γ} {Ψs} {Φ} d x =
      ≈-trans (>>=-cong ret-bind (λ _ → ≈-refl))
        (≈-trans (bind-assoc (Lᶜ δ (Rt d (⊑ᵘ-+ˡ Ψs Φ)) x tt) _ _)
          (>>=-cong ≈-refl (λ v → ≈-trans ret-bind (≈-trans (bind-pure (weak-pure δ {E = One} {Γ = Γ} (⊑ᵘ-+ʳ Ψs Φ) tt x)) ret-bind))))

    -- an argument read in place: the read, the function's share beside it
    scrutA-≈ : ∀ {m n} {Γ : Ctx m n} {Φ Ψs : Usage n} {S : Ty m} (s : Expr Γ Ψs S) (d : Rd s) (x : ⟦ Co Γ (Φ +ᵘ (G.Many *ᵘ Ψs)) ⟧)
             → Lᶜ δ (scrutA rs {Γ = Γ} {Φ = Φ} s (just d)) tt x
               ≈ (Lᶜ δ (Rt d (⊑ᵘ-trans (⊑ᵘ-*Many Ψs) (⊑ᵘ-+ʳ Φ (G.Many *ᵘ Ψs)))) x tt >>=∞ λ v → return∞ (wv {Γ = Γ} (⊑ᵘ-+ˡ Φ (G.Many *ᵘ Ψs)) x , v))
    scrutA-≈ {Γ = Γ} {Φ} {Ψs} s d x =
      ≈-trans (>>=-cong ret-bind (λ _ → ≈-refl))
        (≈-trans (bind-assoc (Lᶜ δ (Rt d (⊑ᵘ-trans (⊑ᵘ-*Many Ψs) (⊑ᵘ-+ʳ Φ (G.Many *ᵘ Ψs)))) x tt) _ _)
          (>>=-cong ≈-refl (λ v → ≈-trans ret-bind (≈-trans (bind-pure (weak-pure δ {E = One} {Γ = Γ} (⊑ᵘ-+ˡ Φ (G.Many *ᵘ Ψs)) tt x)) ret-bind))))


    pairL-≈ : ∀ {m n} {Γ : Ctx m n} {Ψ₁ Ψ₂ : Usage n} {A B : Ty m} (a : Expr Γ Ψ₁ A) (b : Expr Γ Ψ₂ B) (d : Rd a)
              (y : ⟦ Co Γ (Ψ₁ +ᵘ Ψ₂) ⟧)
            → Lᶜ δ (pairL rs {Γ = Γ} a b (just d)) tt y
              ≈ (Lᶜ δ (Rt d (⊑ᵘ-+ˡ Ψ₁ Ψ₂)) y tt >>=∞ λ v → Lᶜ δ (Lq rs b) tt (wv {Γ = Γ} (⊑ᵘ-+ʳ Ψ₁ Ψ₂) y) >>=∞ λ u → return∞ (v , u))
    pairL-≈ {Γ = Γ} {Ψ₁} {Ψ₂} a b d y =
      ≈-trans (>>=-cong (>>=-cong (lentS-≈ {Γ = Γ} {Ψ₁} {Ψ₂} d y) (λ _ → ≈-refl)) (λ _ → ≈-refl))
        (≈-trans (bind-assoc _ _ _)
          (≈-trans (bind-assoc (Lᶜ δ (Rt d (⊑ᵘ-+ˡ Ψ₁ Ψ₂)) y tt) _ _)
            (>>=-cong ≈-refl (λ v → ≈-trans ret-bind (≈-trans ret-bind ret-bind)))))

    rt-eq : ∀ {m n} {Γ : Ctx m n} {Ψ Φ : Usage n} {A : Ty m} {e : Expr Γ Ψ A} (d : Rd e) (q : Ψ ⊑ᵘ Φ) (x : ⟦ Co Γ Φ ⟧)
          → Lᶜ δ (Rt {Γ = Γ} d q) x tt ≈ Lᶜ δ (Lq rs e) tt (wv {Γ = Γ} q x)
    rt-eq {Γ = Γ} {e = e} (rd-path d) q x =
      subst (λ z → z ≈ Lᶜ δ (Lq rs e) tt (wv {Γ = Γ} q x)) (sym (Rp-eq d q bcopy x tt)) (≈-sym (path-pure d tt (wv {Γ = Γ} q x)))
    rt-eq (rd-int z) q x = ≈-sym ret-bind
    rt-eq (rd-float d) q x = ≈-sym ret-bind
    rt-eq (rd-num h o d) q x = >>=-cong (rt-eq d q x) (λ _ → ≈-refl)
    rt-eq {Γ = Γ} {e = coerce c f} (rd-coe c d) q x = by (voidFree? c)
      where
        by : ∀ dc → Lᶜ δ (coeRd c dc (Rt d q)) x tt ≈ Lᶜ δ (coeR c dc (Lq rs f)) tt (wv {Γ = Γ} q x)
        by (yes vf) = cast-≈ (cong ⟪_⟫ (erase-eq c vf)) (Rt d q) (Lq rs f) (rt-eq d q x)
        by (no _)   = >>=-cong (rt-eq d q x) (λ _ → ≈-refl)
    rt-eq {Γ = Γ} (rd-pair {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {a = a} {b = b} da db) q x = by (rdw? a)
      where
        qa = ⊑ᵘ-trans (⊑ᵘ-+ˡ Ψ₁ Ψ₂) q
        qb = ⊑ᵘ-trans (⊑ᵘ-+ʳ Ψ₁ Ψ₂) q
        y = wv {Γ = Γ} q x
        ea : wv {Γ = Γ} qa x ≡ fst (sv Γ Ψ₁ Ψ₂ y)
        ea = sym (trans (sv-l Γ Ψ₁ Ψ₂ y) (wv-comp {Γ = Γ} (⊑ᵘ-+ˡ Ψ₁ Ψ₂) q qa x))
        eb : wv {Γ = Γ} qb x ≡ snd (sv Γ Ψ₁ Ψ₂ y)
        eb = sym (trans (sv-r Γ Ψ₁ Ψ₂ y) (wv-comp {Γ = Γ} (⊑ᵘ-+ʳ Ψ₁ Ψ₂) q qb x))
        ea′ : wv {Γ = Γ} qa x ≡ wv {Γ = Γ} (⊑ᵘ-+ˡ Ψ₁ Ψ₂) y
        ea′ = sym (wv-comp {Γ = Γ} (⊑ᵘ-+ˡ Ψ₁ Ψ₂) q qa x)
        eb′ : wv {Γ = Γ} qb x ≡ wv {Γ = Γ} (⊑ᵘ-+ʳ Ψ₁ Ψ₂) y
        eb′ = sym (wv-comp {Γ = Γ} (⊑ᵘ-+ʳ Ψ₁ Ψ₂) q qb x)
        -- the right read, at the right share of the restricted context
        rb≈ : ∀ z → wv {Γ = Γ} qb x ≡ z → Lᶜ δ (Rt db qb) x tt ≈ Lᶜ δ (Lq rs b) tt z
        rb≈ z e = subst (λ w′ → Lᶜ δ (Rt db qb) x tt ≈ Lᶜ δ (Lq rs b) tt w′) e (rt-eq db qb x)
        by : ∀ md → Lᶜ δ (Rt (rd-pair da db) q) x tt ≈ Lᶜ δ (pairL rs {Γ = Γ} a b md) tt y
        by nothing =
          ≈-trans ret-bind
            (≈-trans (>>=-cong (subst (λ w′ → Lᶜ δ (Rt da qa) x tt ≈ Lᶜ δ (Lq rs a) tt w′) ea (rt-eq da qa x))
                               (λ u → >>=-cong (rb≈ _ eb) (λ _ → ≈-refl)))
                     (≈-sym (bind-pure (split-pure δ Γ Ψ₁ Ψ₂ tt y))))
        by (just d′) = subst (λ d″ → Lᶜ δ (Rt (rd-pair da db) q) x tt ≈ Lᶜ δ (pairL rs {Γ = Γ} a b (just d″)) tt y) (rd-irr da d′)
          (≈-trans ret-bind
            (≈-trans (>>=-cong (≈-trans (rt-eq da qa x)
                                  (subst (λ w′ → Lᶜ δ (Lq rs a) tt w′ ≈ Lᶜ δ (Rt da (⊑ᵘ-+ˡ Ψ₁ Ψ₂)) y tt) (sym ea′)
                                         (≈-sym (rt-eq da (⊑ᵘ-+ˡ Ψ₁ Ψ₂) y))))
                               (λ u → >>=-cong (rb≈ _ eb′) (λ _ → ≈-refl)))
                     (≈-sym (pairL-≈ {Γ = Γ} a b da y))))
    -- ★ D495: a lent call means the application, whichever way `appR` builds it
    -- (the function's path returns at once, so reading the argument first is the same)
    rt-eq {Γ = Γ} (rd-app {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {A = Aa} {B = Bb} {f = f} {x = x′} p d) q x = byC (cp? f)
      where
        Φ₂ = G.Many *ᵘ Ψ₂
        q₁ = ⊑ᵘ-trans (⊑ᵘ-+ˡ Ψ₁ Φ₂) q
        q₂ = ⊑ᵘ-trans (⊑ᵘ-*Many Ψ₂) (⊑ᵘ-trans (⊑ᵘ-+ʳ Ψ₁ Φ₂) q)
        r₂ = ⊑ᵘ-trans (⊑ᵘ-*Many Ψ₂) (⊑ᵘ-+ʳ Ψ₁ Φ₂)
        y = wv {Γ = Γ} q x
        z₁ = wv {Γ = Γ} (⊑ᵘ-+ˡ Ψ₁ Φ₂) y
        z₂ = wv {Γ = Γ} r₂ y
        e₁ : wv {Γ = Γ} q₁ x ≡ z₁
        e₁ = sym (wv-comp {Γ = Γ} (⊑ᵘ-+ˡ Ψ₁ Φ₂) q q₁ x)
        e₂ : wv {Γ = Γ} q₂ x ≡ z₂
        e₂ = sym (wv-comp {Γ = Γ} r₂ q q₂ x)
        -- the application's meaning, the function's value first
        bv : Tm L (ty (Aa ⇒[ G.mk-kind G.Many G.pure ] Bb)) (ty Aa) (ty Bb)
        bv = bev {g = grade G.pure}
        Nf : ⟦ Co Γ Ψ₁ ⟧ → ⟦ Co Γ Ψ₂ ⟧ → T∞ ⟦ ty Bb ⟧
        Nf w₁ w₂ = Lᶜ δ (Lq rs x′) tt w₂ >>=∞ λ a → Lᶜ δ bv (pv p w₁) a
        lhs : Lᶜ δ (Rt (rd-app p d) q) x tt ≈ Nf z₁ z₂
        lhs = >>=-cong (subst (λ w → Lᶜ δ (Rt d q₂) x tt ≈ Lᶜ δ (Lq rs x′) tt w) e₂ (rt-eq d q₂ x))
                       (λ a → subst (λ w → Lᶜ δ (Rp p q₁ bv) x a ≈ Lᶜ δ bv (pv p w) a) e₁
                                    (subst (λ m → m ≈ Lᶜ δ bv (pv p (wv {Γ = Γ} q₁ x)) a) (sym (Rp-eq p q₁ bv x a)) ≈-refl))
        sv₁ = fst (sv Γ Ψ₁ Φ₂ y)
        sv₂ = snd (sv Γ Ψ₁ Φ₂ y)
        split-route : Lᶜ δ (appS rs {Γ = Γ} f x′) tt y ≈ Nf z₁ z₂
        split-route =
          ≈-trans (>>=-cong (bind-pure (split-pure δ Γ Ψ₁ Φ₂ tt y)) (λ _ → ≈-refl))
            (≈-trans (>>=-cong (bind-pure (path-pure p tt sv₁)) (λ _ → ≈-refl))
              (≈-trans (bind-assoc _ _ _)
                (≈-trans (>>=-cong (bind-pure (weak-pure δ {E = One} {Γ = Γ} (⊑ᵘ-*Many Ψ₂) tt sv₂)) (λ a → ret-bind))
                  (subst₂ (λ w₁ w₂ → Nf sv₁ (wv {Γ = Γ} (⊑ᵘ-*Many Ψ₂) sv₂) ≈ Nf w₁ w₂)
                          (sv-l Γ Ψ₁ Φ₂ y)
                          (trans (cong (wv {Γ = Γ} (⊑ᵘ-*Many Ψ₂)) (sv-r Γ Ψ₁ Φ₂ y)) (wv-comp {Γ = Γ} (⊑ᵘ-*Many Ψ₂) (⊑ᵘ-+ʳ Ψ₁ Φ₂) r₂ y))
                          ≈-refl))))
        read-route : Lᶜ δ (appR rs {Γ = Γ} f x′ (just p) (just d)) tt y ≈ Nf z₁ z₂
        read-route =
          ≈-trans (>>=-cong (>>=-cong (scrutA-≈ {Γ = Γ} {Φ = Ψ₁} x′ d y) (λ _ → ≈-refl)) (λ _ → ≈-refl))
            (≈-trans (>>=-cong (bind-assoc (Lᶜ δ (Rt d r₂) y tt) _ _) (λ _ → ≈-refl))
              (≈-trans (bind-assoc (Lᶜ δ (Rt d r₂) y tt) _ _)
                (>>=-cong (rt-eq d r₂ y)
                  (λ v → ≈-trans (>>=-cong ret-bind (λ _ → ≈-refl))
                           (≈-trans (>>=-cong (bind-pure (path-pure p tt z₁)) (λ _ → ≈-refl))
                             (≈-trans (>>=-cong ret-bind (λ _ → ≈-refl)) ret-bind))))))
        byR : ∀ mp md → Lᶜ δ (Rt (rd-app p d) q) x tt ≈ Lᶜ δ (appR rs {Γ = Γ} f x′ mp md) tt y
        byR (just p′) (just d′) =
          subst₂ (λ p″ d″ → Lᶜ δ (Rt (rd-app p d) q) x tt ≈ Lᶜ δ (appR rs {Γ = Γ} f x′ (just p″) (just d″)) tt y)
                 (pth-irr p p′) (rd-irr d d′) (≈-trans lhs (≈-sym read-route))
        byR (just p′) nothing = ≈-trans lhs (≈-sym split-route)
        byR nothing md        = ≈-trans lhs (≈-sym split-route)
        byC : ∀ mc → Lᶜ δ (Rt (rd-app p d) q) x tt ≈ Lᶜ δ (appL rs {Γ = Γ} f x′ mc) tt y
        byC nothing  = byR (pth? f) (rdx? Ψ₁ Ψ₂ x′)
        byC (just c) = Data.Empty.⊥-elim (cp-pth c p)

  -- ★ a pair whose first component reads in place, against the IR's pairing
  rel-pairL : ∀ {m n} {Γ : Ctx m n} {Ψ₁ Ψ₂ : Usage n} {A B : Ty m} (a : Expr Γ Ψ₁ A) (b : Expr Γ Ψ₂ B) (md : Maybe (Rd a))
            → Goal a → Goal b
            → Rel (pairL rs {Γ = Γ} a b md)
                  M.⟨ elaborate am a M.∘ restrictEnv {Γ = Γ} am (⊑ᵘ-+ˡ Ψ₁ Ψ₂) , elaborate am b M.∘ restrictEnv {Γ = Γ} am (⊑ᵘ-+ʳ Ψ₁ Ψ₂) ⟩
  rel-pairL {Γ = Γ} {Ψ₁} {Ψ₂} a b nothing  ra rb = rel-pair am Γ Ψ₁ Ψ₂ ra rb
  rel-pairL {Γ = Γ} {Ψ₁} {Ψ₂} a b (just d) ra rb = mkRel λ {x} {x′} w →
    ≈-≈R (pairL-≈ {Γ = Γ} a b d x)
      (≈R-≈ (>>=-congR (≈-≈R (rt-eq d q₁ x) (relOf ra (weak-W {Γ = Γ} q₁ w)))
                       (λ r → >>=-congR (relOf rb (weak-W {Γ = Γ} q₂ w)) (λ r′ → ret≈R (r , r′))))
            (≈-sym (>>=-cong (bind-pure (restrict-pure ρ am {Γ = Γ} q₁ x′))
                             (λ _ → >>=-cong (bind-pure (restrict-pure ρ am {Γ = Γ} q₂ x′)) (λ _ → ≈-refl)))))
    where
      q₁ = ⊑ᵘ-+ˡ Ψ₁ Ψ₂
      q₂ = ⊑ᵘ-+ʳ Ψ₁ Ψ₂

  -- the scrutinee and the arms' share, read in place or split off: the same values
  rel-scrut : ∀ {m n} {Γ : Ctx m n} {Ψs Φ : Usage n} {S : Ty m} (s : Expr Γ Ψs S) (md : Maybe (Rd s)) → Goal s
            → Rel (scrutL rs {Γ = Γ} {Φ = Φ} s md)
                  M.⟨ restrictEnv {Γ = Γ} am (⊑ᵘ-+ʳ Ψs Φ) , elaborate am s M.∘ restrictEnv {Γ = Γ} am (⊑ᵘ-+ˡ Ψs Φ) ⟩
  rel-scrut {Γ = Γ} {Ψs} {Φ} s nothing  rs′ = rel-swapPair Γ Ψs Φ rs′
  rel-scrut {Γ = Γ} {Ψs} {Φ} s (just d) rs′ = mkRel λ {x} {x′} w →
    ≈-≈R (≈-trans (>>=-cong ret-bind (λ _ → ≈-refl))
           (≈-trans (bind-assoc (Lᶜ δ (Rt d q₁) x tt) _ _)
             (>>=-cong ≈-refl (λ v → ≈-trans ret-bind (≈-trans (bind-pure (weak-pure δ {E = One} {Γ = Γ} q₂ tt x)) ret-bind)))))
      (≈R-≈ (>>=-congR (≈-≈R (rt-eq d q₁ x) (relOf rs′ (weak-W {Γ = Γ} q₁ w))) (λ r → ret≈R (weak-W {Γ = Γ} q₂ w , r)))
            (≈-sym (≈-trans (bind-pure (restrict-pure ρ am {Γ = Γ} q₂ x′))
                            (>>=-cong (bind-pure (restrict-pure ρ am {Γ = Γ} q₁ x′)) (λ _ → ≈-refl)))))
    where
      q₁ = ⊑ᵘ-+ˡ Ψs Φ
      q₂ = ⊑ᵘ-+ʳ Ψs Φ

  -- the combinators' distribution (`distribIR`), the same values
  distribIR-pure : ∀ {X A B : IRTy} → PureI ρ (distribIR {X} {A} {B} am) (dv′ {X} {A} {B})
  distribIR-pure (x , inj₁ a) =
    ≈-trans (bind-pure (≈-trans (bind-pure ret-bind) ret-bind)) (bind-pure (≈-trans ret-bind ret-bind))
  distribIR-pure (x , inj₂ b) =
    ≈-trans (bind-pure (≈-trans (bind-pure ret-bind) ret-bind)) (bind-pure (≈-trans ret-bind ret-bind))

  ------------------------------------------------------------------------
  -- ★ D481 (B1): WHAT EVALUATES AT ONCE does so in the IR — a value, no
  -- event — so a case combinator's arms may be built in the branch.
  ------------------------------------------------------------------------

  -- a pure IR morphism, its value named (a record: the morphism stays visible)
  record PI {A B : IRTy} (t : M.IR A B) : Set where
    constructor pi
    field
      ival : ⟦ A ⟧ᴰᴵ → ⟦ B ⟧ᴰᴵ
      iprf : PureI ρ t ival
  open PI using (ival; iprf)

  -- a function value whose every application returns at once
  AppNow : ∀ (C : IRTy) → ⟦ C ⟧ᴰᴵ → Set
  AppNow (X I.⇛[ π ] Y) v = ∀ b → Σ ⟦ Y ⟧ᴰᴵ (λ c → v b ≈ return∞ c)
  {-# CATCHALL #-}
  AppNow _ _ = ⊤

  record PF {A C : IRTy} (t : M.IR A C) : Set where
    constructor pf
    field
      fv : ⟦ A ⟧ᴰᴵ → ⟦ C ⟧ᴰᴵ
      fp : PureI ρ t fv
      fn : ∀ a → AppNow C (fv a)
  open PF using (fv; fp; fn)

  pi-id : ∀ {A} → PI (M.id {A})
  pi-id = pi (λ x → x) (λ x → ≈-refl)

  pi-∘ : ∀ {A B C} {f : M.IR B C} {g : M.IR A B} → PI f → PI g → PI (f M.∘ g)
  pi-∘ {f = f} {g = g} (pi u pu) (pi v pg) = pi (λ x → u (v x)) (q-∘ ρ {f = f} {g = g} pu pg)

  pi-pair : ∀ {A B C} {f : M.IR A B} {g : M.IR A C} → PI f → PI g → PI M.⟨ f , g ⟩
  pi-pair {f = f} {g = g} (pi u pu) (pi v pg) = pi (λ x → u x , v x) (q-pair ρ {f = f} {g = g} pu pg)

  pi-fst : ∀ {A B} → PI (M.fst {A} {B})
  pi-fst = pi proj₁ (λ x → ≈-refl)

  pi-snd : ∀ {A B} → PI (M.snd {A} {B})
  pi-snd = pi proj₂ (λ x → ≈-refl)

  pi-term : ∀ {A} → PI (M.terminal {A})
  pi-term = pi (λ _ → tt) (λ x → ≈-refl)

  pi-curry : ∀ {A X Y π} (t : M.IR (A I.* X) Y) → PI (M.curry {π = π} t)
  pi-curry t = pi (λ a b → evalᴰ fmt ρ t (a , b)) (λ x → ≈-refl)

  pi-inl : ∀ {A B} → PI (M.inl {A} {B})
  pi-inl = pi inj₁ (λ x → ≈-refl)

  pi-inr : ∀ {A B} → PI (M.inr {A} {B})
  pi-inr = pi inj₂ (λ x → ≈-refl)

  pi-case : ∀ {A B C} {f : M.IR A C} {g : M.IR B C} → PI f → PI g → PI (M.case f g)
  pi-case (pi u pu) (pi v pg) = pi (λ { (inj₁ a) → u a ; (inj₂ b) → v b }) (λ { (inj₁ a) → pu a ; (inj₂ b) → pg b })

  pi-restrict : ∀ {m n} {Γ : Ctx m n} {Ψ Ψ′ : Usage n} (p : Ψ ⊑ᵘ Ψ′) → PI (restrictEnv {Γ = Γ} am p)
  pi-restrict {Γ = Γ} p = pi (rv {Γ = Γ} p) (restrict-pure ρ am {Γ = Γ} p)

  pi-subst : ∀ {Z X Y : IRTy} (e : X ≡ Y) {t : M.IR Z X} → PI t → PI (subst (M.IR Z) e t)
  pi-subst refl p = p

  -- every conversion is pure
  coe-pure : ∀ {m} {A B : Ty m} (c : A <: B) → PI (coeIR c)
  coe-pure sub-void = pi (λ ()) (λ ())
  coe-pure sub-unit = pi-id
  coe-pure sub-int = pi-id
  coe-pure sub-float = pi-id
  coe-pure (sub-arr {q = G.Zero} a b _) = pi-curry _
  coe-pure (sub-arr {q = G.One} a b _)  = pi-curry _
  coe-pure (sub-arr {q = G.Many} a b _) = pi-curry _
  coe-pure (sub-* a b) = pi-pair (pi-∘ (coe-pure a) pi-fst) (pi-∘ (coe-pure b) pi-snd)
  coe-pure (sub-+ a b) = pi-case (pi-∘ pi-inl (coe-pure a)) (pi-∘ pi-inr (coe-pure b))
  coe-pure sub-μ = pi-id
  coe-pure (sub-ν _) = pi-id
  coe-pure sub-var = pi-id

  coe-I : ∀ {m} {A B : Ty m} {Z : IRTy} (c : A <: B) (d : Dec (VoidFree c)) {t : M.IR Z ⌊ A ⌋} → PI t → PI (runCoe-dec c d t)
  coe-I c (yes vf) p = pi-subst (erase-eq c vf) p
  coe-I c (no _)   p = pi-∘ (coe-pure c) p

  proj-pure : ∀ {m n} {Γ : Ctx m n} (i : Data.Fin.Fin n) → PI (projUsed {Γ = Γ} i)
  proj-pure {Γ = Γ SC.▸ A} Data.Fin.zero    = pi-snd
  proj-pure {Γ = Γ SC.▸ A} (Data.Fin.suc i) = proj-pure {Γ = Γ} i

  -- a function that returns at once, after what returns at once
  pf-∘ : ∀ {A B C} {f : M.IR B C} {g : M.IR A B} → PF f → PI g → PF (f M.∘ g)
  pf-∘ {f = f} {g = g} (pf u pu nu) (pi v pg) = pf (λ x → u (v x)) (q-∘ ρ {f = f} {g = g} pu pg) (λ x → nu (v x))

  pf-closed : ∀ {A C} {f : M.IR I.Unit C} → PF f → PF (f M.∘ M.terminal {A})
  pf-closed {A} {f = f} (pf u pu nu) = pf (λ _ → u tt) (q-∘ ρ {f = f} {g = M.terminal {A}} pu (λ _ → ≈-refl)) (λ _ → nu tt)

  -- ... applied to what returns at once
  app-I : ∀ {A B C : IRTy} {π} {F : M.IR A (B I.⇛[ π ] C)} {X : M.IR A B} → PF F → PI X → PI (M.apply M.∘ M.⟨ F , X ⟩)
  app-I {F = F} {X = X} (pf vF pF nF) (pi vX pX) =
    pi (λ y → proj₁ (nF y (vX y))) (λ y → ≈-trans (bind-pure (q-pair ρ {f = F} {g = X} pF pX y)) (proj₂ (nF y (vX y))))

  -- a closure whose body returns at once
  pf-curry : ∀ {A X Y π} {t : M.IR (A I.* X) Y} → PI t → PF (M.curry {π = π} t)
  pf-curry {t = t} (pi u pu) = pf (λ a b → evalᴰ fmt ρ t (a , b)) (λ x → ≈-refl) (λ a b → u (a , b) , pu (a , b))

  im-I : ∀ {m n} {Γ : Ctx m n} {Ψ : Usage n} {A : Ty m} {e : Expr Γ Ψ A} → Im e → PI (elaborate am e)
  imf-I : ∀ {m n} {Γ : Ctx m n} {Ψ : Usage n} {T : Ty m} {e : Expr Γ Ψ T} → ImF e → PF (elaborate am e)
  im-I {Γ = Γ} (im-var i) = proj-pure {Γ = Γ} i
  im-I (im-lam {q′ = G.Zero} {q = G.Zero}) = pi-curry _
  im-I (im-lam {q′ = G.Zero} {q = G.One})  = pi-curry _
  im-I (im-lam {q′ = G.Zero} {q = G.Many}) = pi-curry _
  im-I (im-lam {q′ = G.One}  {q = G.One})  = pi-curry _
  im-I (im-lam {q′ = G.One}  {q = G.Many}) = pi-curry _
  im-I (im-lam {q′ = G.Many} {q = G.Many}) = pi-curry _
  im-I (im-lam {q′ = G.One}  {q = G.Zero} {p = ()})
  im-I (im-lam {q′ = G.Many} {q = G.Zero} {p = ()})
  im-I (im-lam {q′ = G.Many} {q = G.One}  {p = ()})
  im-I (im-closed p) = pi-∘ (im-I p) pi-term
  im-I (im-coe c p) = coe-I c (voidFree? c) (im-I p)
  im-I {Γ = Γ} (im-app1 {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} f x) =
    app-I (pf-∘ (imf-I f) (pi-restrict {Γ = Γ} (⊑ᵘ-+ˡ Ψ₁ (G.One *ᵘ Ψ₂))))
          (pi-∘ (im-I x) (pi-restrict {Γ = Γ} (⊑ᵘ-trans (⊑ᵘ-*One Ψ₂) (⊑ᵘ-+ʳ Ψ₁ (G.One *ᵘ Ψ₂)))))
  im-I {Γ = Γ} (im-appω {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} f x) =
    app-I (pf-∘ (imf-I f) (pi-restrict {Γ = Γ} (⊑ᵘ-+ˡ Ψ₁ (G.Many *ᵘ Ψ₂))))
          (pi-∘ (im-I x) (pi-restrict {Γ = Γ} (⊑ᵘ-trans (⊑ᵘ-*Many Ψ₂) (⊑ᵘ-+ʳ Ψ₁ (G.Many *ᵘ Ψ₂)))))
  imf-I (imf-lam {q′ = G.Zero} {q = G.Zero} p) = pf-curry (pi-∘ (im-I p) pi-fst)
  imf-I (imf-lam {q′ = G.Zero} {q = G.One} p)  = pf-curry (pi-∘ (im-I p) pi-fst)
  imf-I (imf-lam {q′ = G.Zero} {q = G.Many} p) = pf-curry (pi-∘ (im-I p) pi-fst)
  imf-I (imf-lam {q′ = G.One}  {q = G.One} p)  = pf-curry (im-I p)
  imf-I (imf-lam {q′ = G.One}  {q = G.Many} p) = pf-curry (im-I p)
  imf-I (imf-lam {q′ = G.Many} {q = G.Many} p) = pf-curry (im-I p)
  imf-I (imf-lam {q′ = G.One}  {q = G.Zero} {p = ()} _)
  imf-I (imf-lam {q′ = G.Many} {q = G.Zero} {p = ()} _)
  imf-I (imf-lam {q′ = G.Many} {q = G.One}  {p = ()} _)
  imf-I (imf-closed p) = pf-closed (imf-I p)

  -- ★ D495: a path's elaboration returns at once
  pth-I : ∀ {m n} {Γ : Ctx m n} {Ψ : Usage n} {A : Ty m} {e : Expr Γ Ψ A} → Pth e → PI (elaborate am e)
  pth-I {Γ = Γ} (p-var i) = proj-pure {Γ = Γ} i
  pth-I (p-fst d) = pi-∘ pi-fst (pth-I d)
  pth-I (p-snd d) = pi-∘ pi-snd (pth-I d)
  pth-I {Γ = Γ} (p-mfst {Ψ = Ψ} d) = pi-∘ pi-fst (pi-∘ (pth-I d) (pi-restrict {Γ = Γ} (mq Ψ)))
  pth-I {Γ = Γ} (p-msnd {Ψ = Ψ} d) = pi-∘ pi-snd (pi-∘ (pth-I d) (pi-restrict {Γ = Γ} (mq Ψ)))

  -- a term beside a value it passes on
  rel-side : ∀ {X Y A : IRTy} {t : LTm L ⟪ X ⟫ ⟪ Y ⟫} {t′ : M.IR X Y}
           → Rel t t′ → Rel (t ⊗l lid {A = ⟪ A ⟫}) M.⟨ t′ M.∘ M.fst , M.snd ⟩
  rel-side r = mkRel λ { {x , a} {x′ , a′} (w , wa) →
    ≈-≈R (>>=-cong ≈-refl (λ _ → ret-bind))
      (≈R-≈ (>>=-congR (relOf r w) (λ r′ → ret≈R (r′ , wa))) (≈-sym (>>=-cong ret-bind (λ _ → ret-bind)))) }

  -- an argument as a scrutinee, the function's share beside it: read in place or split off
  rel-scrutA : ∀ {m n} {Γ : Ctx m n} {Φ Ψs : Usage n} {S : Ty m} (s : Expr Γ Ψs S) (md : Maybe (Rd s)) → Goal s
             → Rel (scrutA rs {Γ = Γ} {Φ = Φ} s md)
                   M.⟨ M.id M.∘ restrictEnv {Γ = Γ} am (⊑ᵘ-+ˡ Φ (G.Many *ᵘ Ψs))
                     , elaborate am s M.∘ restrictEnv {Γ = Γ} am (⊑ᵘ-trans (⊑ᵘ-*Many Ψs) (⊑ᵘ-+ʳ Φ (G.Many *ᵘ Ψs))) ⟩
  rel-scrutA {Γ = Γ} {Φ} {Ψs} s nothing  rs′ = rel-pairW Γ Φ Ψs (G.Many *ᵘ Ψs) (⊑ᵘ-*Many Ψs) rel-id rs′
  rel-scrutA {Γ = Γ} {Φ} {Ψs} s (just d) rs′ = mkRel λ {x} {x′} w →
    ≈-≈R (≈-trans (>>=-cong ret-bind (λ _ → ≈-refl))
           (≈-trans (bind-assoc (Lᶜ δ (Rt d q₁) x tt) _ _)
             (>>=-cong ≈-refl (λ v → ≈-trans ret-bind (≈-trans (bind-pure (weak-pure δ {E = One} {Γ = Γ} q₂ tt x)) ret-bind)))))
      (≈R-≈ (>>=-congR (≈-≈R (rt-eq d q₁ x) (relOf rs′ (weak-W {Γ = Γ} q₁ w))) (λ r → ret≈R (weak-W {Γ = Γ} q₂ w , r)))
            (≈-sym (≈-trans (bind-pure (bind-pure (restrict-pure ρ am {Γ = Γ} q₂ x′)))
                            (>>=-cong (bind-pure (restrict-pure ρ am {Γ = Γ} q₁ x′)) (λ _ → ≈-refl)))))
    where
      q₁ = ⊑ᵘ-trans (⊑ᵘ-*Many Ψs) (⊑ᵘ-+ʳ Φ (G.Many *ᵘ Ψs))
      q₂ = ⊑ᵘ-+ˡ Φ (G.Many *ᵘ Ψs)

  -- ★ the branch against the IR's eager copairing: the arms return at once,
  -- so building both first and choosing after is choosing first and building one
  rel-appB : ∀ {m n} {Γ : Ctx m n} {Ψf Ψg Ψx : Usage n} {A B C : Ty m}
               (f : Expr Γ Ψf (A ⇒[ G.mk-kind G.Many G.pure ] C)) (g : Expr Γ Ψg (B ⇒[ G.mk-kind G.Many G.pure ] C))
               (x : Expr Γ Ψx (A + B)) (i : Im f) (j : Im g)
           → Goal f → Goal g → Goal x
           → Rel (appL rs {Γ = Γ} (copair' f g) x (just (cp i j))) (elaborate am (app (copair' f g) x))
  rel-appB {Γ = Γ} {Ψf} {Ψg} {Ψx} {A} {B} {C} f g x i j rf rg rx =
    rel-≈ʳ (rel-∘ (rel-lcase (rel-∘ (rel-apω {π = G.pure}) (rel-side (rel-∘ rf (rel-weak am {Γ = Γ} pl))))
                             (rel-∘ (rel-apω {π = G.pure}) (rel-side (rel-∘ rg (rel-weak am {Γ = Γ} pr)))))
                  (rel-∘ rel-dist (rel-scrutA {Γ = Γ} {Φ = Ψf +ᵘ Ψg} x (rdw? x) rx)))
           eq
    where
      pl = ⊑ᵘ-+ˡ Ψf Ψg
      pr = ⊑ᵘ-+ʳ Ψf Ψg
      q₁ = ⊑ᵘ-+ˡ (Ψf +ᵘ Ψg) (G.Many *ᵘ Ψx)
      q₂ = ⊑ᵘ-trans (⊑ᵘ-*Many Ψx) (⊑ᵘ-+ʳ (Ψf +ᵘ Ψg) (G.Many *ᵘ Ψx))
      Fe = elaborate am f
      Ge = elaborate am g
      Xe = elaborate am x
      PFl = pi-∘ (im-I i) (pi-restrict {Γ = Γ} pl)
      PGr = pi-∘ (im-I j) (pi-restrict {Γ = Γ} pr)
      A1 = M.apply M.∘ M.⟨ (Fe M.∘ restrictEnv {Γ = Γ} am pl) M.∘ M.fst , M.snd ⟩
      A2 = M.apply M.∘ M.⟨ (Ge M.∘ restrictEnv {Γ = Γ} am pr) M.∘ M.fst , M.snd ⟩
      B1 : M.IR (((⌊ A ⌋ I.⇛[ G.pure ] ⌊ C ⌋) I.* (⌊ B ⌋ I.⇛[ G.pure ] ⌊ C ⌋)) I.* ⌊ A ⌋) ⌊ C ⌋
      B1 = M.apply M.∘ M.⟨ M.fst M.∘ M.fst , M.snd ⟩
      B2 : M.IR (((⌊ A ⌋ I.⇛[ G.pure ] ⌊ C ⌋) I.* (⌊ B ⌋ I.⇛[ G.pure ] ⌊ C ⌋)) I.* ⌊ B ⌋) ⌊ C ⌋
      B2 = M.apply M.∘ M.⟨ M.snd M.∘ M.fst , M.snd ⟩
      FnA = ⌊ A ⌋ I.⇛[ G.pure ] ⌊ C ⌋
      FnB = ⌊ B ⌋ I.⇛[ G.pure ] ⌊ C ⌋
      Cx₀ = ⌊ ⟦ Γ ↾ (Ψf +ᵘ Ψg) ⟧ᶜ ⌋
      PA1 : PI {Cx₀ I.* ⌊ A ⌋} {FnA I.* ⌊ A ⌋} M.⟨ (Fe M.∘ restrictEnv {Γ = Γ} am pl) M.∘ M.fst , M.snd ⟩
      PA1 = pi-pair (pi-∘ PFl pi-fst) pi-snd
      PA2 : PI {Cx₀ I.* ⌊ B ⌋} {FnB I.* ⌊ B ⌋} M.⟨ (Ge M.∘ restrictEnv {Γ = Γ} am pr) M.∘ M.fst , M.snd ⟩
      PA2 = pi-pair (pi-∘ PGr pi-fst) pi-snd
      PB1 : PI {(FnA I.* FnB) I.* ⌊ A ⌋} {FnA I.* ⌊ A ⌋} M.⟨ M.fst M.∘ M.fst , M.snd ⟩
      PB1 = pi-pair (pi-∘ pi-fst pi-fst) pi-snd
      PB2 : PI {(FnA I.* FnB) I.* ⌊ B ⌋} {FnB I.* ⌊ B ⌋} M.⟨ M.snd M.∘ M.fst , M.snd ⟩
      PB2 = pi-pair (pi-∘ pi-snd pi-fst) pi-snd

      -- one branch's two runs: the arm built after the choice, or chosen among two built
      arm : ∀ (r : ⟦ ⌊ ⟦ Γ ↾ (Ψf +ᵘ Ψg) ⟧ᶜ ⌋ ⟧ᴰᴵ) (c : ⟦ ⌊ A ⌋ I.+ ⌊ B ⌋ ⟧ᴰᴵ)
          → (evalᴰ fmt ρ (distribute am) (r , c) >>=∞ evalᴰ fmt ρ (M.case A1 A2))
            ≈ (evalᴰ fmt ρ (distribIR am) ((ival PFl r , ival PGr r) , c) >>=∞ evalᴰ fmt ρ (M.case B1 B2))
      arm r (inj₁ a) =
        ≈-trans (bind-pure (distribute-pure (r , inj₁ a)))
          (≈-trans (bind-pure {k = λ p → proj₁ p (proj₂ p)} (iprf PA1 (r , a)))
            (≈-sym (≈-trans (bind-pure (distribIR-pure ((ival PFl r , ival PGr r) , inj₁ a)))
                            (bind-pure {k = λ p → proj₁ p (proj₂ p)} (iprf PB1 ((ival PFl r , ival PGr r) , a))))))
      arm r (inj₂ b) =
        ≈-trans (bind-pure (distribute-pure (r , inj₂ b)))
          (≈-trans (bind-pure {k = λ p → proj₁ p (proj₂ p)} (iprf PA2 (r , b)))
            (≈-sym (≈-trans (bind-pure (distribIR-pure ((ival PFl r , ival PGr r) , inj₂ b)))
                            (bind-pure {k = λ p → proj₁ p (proj₂ p)} (iprf PB2 ((ival PFl r , ival PGr r) , b))))))

      eq : ∀ y → evalᴰ fmt ρ (M.case A1 A2 M.∘ (distribute am M.∘ M.⟨ M.id M.∘ restrictEnv {Γ = Γ} am q₁ , Xe M.∘ restrictEnv {Γ = Γ} am q₂ ⟩)) y
                 ≈ evalᴰ fmt ρ (elaborate am (app {q = G.Many} (copair' f g) x)) y
      eq y =
        ≈-trans (>>=-cong (>>=-cong (bind-pure (iprf (pi-∘ pi-id (pi-restrict {Γ = Γ} q₁)) y)) (λ _ → ≈-refl)) (λ _ → ≈-refl))
          (≈-trans (bind-assoc _ _ _) (≈-trans (bind-assoc (evalᴰ fmt ρ (Xe M.∘ restrictEnv {Γ = Γ} am q₂) y) _ _)
            (≈-trans (>>=-cong ≈-refl (λ c → ≈-trans ret-bind (arm (rv {Γ = Γ} q₁ y) c)))
              (≈-sym (≈-trans (>>=-cong (bind-pure (iprf (pi-∘ (pi-∘ (pi-curry {π = G.pure} (M.case B1 B2 M.∘ distribIR am)) (pi-pair PFl PGr)) (pi-restrict {Γ = Γ} q₁)) y))
                                        (λ _ → ≈-refl))
                        (≈-trans (bind-assoc _ _ _) (>>=-cong ≈-refl (λ _ → ret-bind))))))))

  -- ★ D495: a function off a path, its argument read in place first, against the
  -- IR's function-then-argument: the function's elaboration returns at once
  rel-appR : ∀ {m n} {Γ : Ctx m n} {Ψ₁ Ψ₂ : Usage n} {A B : Ty m}
               (f : Expr Γ Ψ₁ (A ⇒[ G.mk-kind G.Many G.pure ] B)) (x : Expr Γ Ψ₂ A) (mp : Maybe (Pth f)) (md : Maybe (Rd x))
           → Goal f → Goal x → Rel (appR rs {Γ = Γ} f x mp md) (elaborate am (app {q = G.Many} f x))
  rel-appR {Γ = Γ} {Ψ₁} {Ψ₂} {A} {B} f x (just p) (just d) rf rx =
    rel-≈ʳ (rel-∘ (rel-apω {π = G.pure} {⌊ A ⌋} {⌊ B ⌋}) (rel-∘ (rel-side rf) (rel-scrutA {Γ = Γ} {Φ = Ψ₁} x (just d) rx))) eq
    where
      q₁ = ⊑ᵘ-+ˡ Ψ₁ (G.Many *ᵘ Ψ₂)
      q₂ = ⊑ᵘ-trans (⊑ᵘ-*Many Ψ₂) (⊑ᵘ-+ʳ Ψ₁ (G.Many *ᵘ Ψ₂))
      Fe = elaborate am f
      Xe = elaborate am x
      PFp = pth-I p
      N = λ y → evalᴰ fmt ρ (Xe M.∘ restrictEnv {Γ = Γ} am q₂) y >>=∞ λ w → evalᴰ fmt ρ (M.apply {⌊ A ⌋} {⌊ B ⌋} {G.pure}) (ival PFp (rv {Γ = Γ} q₁ y) , w)
      lhs : ∀ y → evalᴰ fmt ρ (M.apply {⌊ A ⌋} {⌊ B ⌋} {G.pure} M.∘ (M.⟨ Fe M.∘ M.fst {⌊ ⟦ Γ ↾ Ψ₁ ⟧ᶜ ⌋} {⌊ A ⌋} , M.snd ⟩ M.∘ M.⟨ M.id M.∘ restrictEnv {Γ = Γ} am q₁ , Xe M.∘ restrictEnv {Γ = Γ} am q₂ ⟩)) y ≈ N y
      lhs y =
        ≈-trans (>>=-cong (>>=-cong (bind-pure (iprf (pi-∘ pi-id (pi-restrict {Γ = Γ} q₁)) y)) (λ _ → ≈-refl)) (λ _ → ≈-refl))
          (≈-trans (bind-assoc _ _ _) (≈-trans (bind-assoc (evalᴰ fmt ρ (Xe M.∘ restrictEnv {Γ = Γ} am q₂) y) _ _)
            (>>=-cong ≈-refl (λ w → ≈-trans ret-bind
               (≈-trans (>>=-cong (bind-pure (iprf (pi-∘ PFp (pi-fst {⌊ ⟦ Γ ↾ Ψ₁ ⟧ᶜ ⌋} {⌊ A ⌋})) (rv {Γ = Γ} q₁ y , w))) (λ _ → ≈-refl))
                 (≈-trans (>>=-cong ret-bind (λ _ → ≈-refl)) ret-bind))))))
      rhs : ∀ y → evalᴰ fmt ρ (elaborate am (app {q = G.Many} f x)) y ≈ N y
      rhs y =
        ≈-trans (>>=-cong (bind-pure (iprf (pi-∘ PFp (pi-restrict {Γ = Γ} q₁)) y)) (λ _ → ≈-refl))
          (≈-trans (bind-assoc _ _ _) (>>=-cong ≈-refl (λ _ → ret-bind)))
      eq : ∀ y → _ ≈ _
      eq y = ≈-trans (lhs y) (≈-sym (rhs y))
  rel-appR {Γ = Γ} {Ψ₁} {Ψ₂} f x (just p) nothing rf rx = rel-app Γ Ψ₁ Ψ₂ (G.Many *ᵘ Ψ₂) (⊑ᵘ-*Many Ψ₂) rf rx
  rel-appR {Γ = Γ} {Ψ₁} {Ψ₂} f x nothing md rf rx      = rel-app Γ Ψ₁ Ψ₂ (G.Many *ᵘ Ψ₂) (⊑ᵘ-*Many Ψ₂) rf rx

  -- ★ A CASE: the scrutinee's share split off, the arms' share distributed,
  -- each arm on its share and the bound value
  ok-case : ∀ {m n} {Γ : Ctx m n} {Ψs Ψₗ Ψᵣ : Usage n} {qℓ qr : G.Quantity} {A B C : Ty m}
              (s : Expr Γ Ψs (A + B)) (l : Expr (Γ SC.▸ A) (qℓ ∷ Ψₗ) C) (r : Expr (Γ SC.▸ B) (qr ∷ Ψᵣ) C)
            → Goal s → Goal l → Goal r → Goal (case' s l r)
  ok-case {Γ = Γ} {Ψs} {Ψₗ} {Ψᵣ} {qℓ} {qr} {A} {B} s l r rs′ rl rr =
    rel-∘ (rel-lcase (rel-∘ rl (rel-∘ (rel-bind {Γ = Γ} {A = A} qℓ) (rel-arm {Γ = Γ} (⊑ᵘ-⊔ˡ Ψₗ Ψᵣ))))
                     (rel-∘ rr (rel-∘ (rel-bind {Γ = Γ} {A = B} qr) (rel-arm {Γ = Γ} (⊑ᵘ-⊔ʳ Ψₗ Ψᵣ)))))
          (rel-∘ rel-dist (rel-scrut {Γ = Γ} {Φ = Ψₗ ⊔ᵘ Ψᵣ} s (rdw? s) rs′))

  ok-copair : ∀ {m n} {Γ : Ctx m n} {Ψ₁ Ψ₂ : Usage n} {A B C : Ty m} {π}
                (f : Expr Γ Ψ₁ (A ⇒[ G.mk-kind G.Many π ] C)) (g : Expr Γ Ψ₂ (B ⇒[ G.mk-kind G.Many π ] C))
              → Goal f → Goal g → Goal (copair' f g)
  ok-copair {Γ = Γ} {Ψ₁} {Ψ₂} {A} {B} {C} {π = π} f g rf rg = rel-∘ (rel-cloL π _ copairL) (rel-pair am Γ Ψ₁ Ψ₂ rf rg)
    where
      -- the lent body: the chosen arm applied lent
      copairL : ∀ {x x′} → W ((⌊ A ⌋ I.⇛[ π ] ⌊ C ⌋) I.* (⌊ B ⌋ I.⇛[ π ] ⌊ C ⌋)) x x′ → ∀ {s s′} → W (⌊ A ⌋ I.+ ⌊ B ⌋) s s′
              → Lᶜ δ (lcase (bfst (bev {g = grade π} {ty A} {ty C})) (bsnd (bev {g = grade π} {ty B} {ty C}))) x s
                ≈[ W ⌊ C ⌋ ] evalᴰ fmt ρ (M.case (M.apply {⌊ A ⌋} {⌊ C ⌋} {π} M.∘ M.⟨ M.fst M.∘ M.fst , M.snd ⟩)
                                                 (M.apply {⌊ B ⌋} {⌊ C ⌋} {π} M.∘ M.⟨ M.snd M.∘ M.fst , M.snd ⟩) M.∘ distribIR am) (x′ , s′)
      copairL {x = f₀ , g₀} {f′ , g′} (wf , wg) {inj₁ a} {inj₁ a′} (Data.Sum.Relation.Binary.Pointwise.inj₁ wa) =
        ≈R-≈ (wf wa) (≈-sym (≈-trans (bind-pure (distribIR-pure ((f′ , g′) , inj₁ a′))) (bind-pure (≈-trans (bind-pure ret-bind) ret-bind))))
      copairL {x = f₀ , g₀} {f′ , g′} (wf , wg) {inj₂ b} {inj₂ b′} (Data.Sum.Relation.Binary.Pointwise.inj₂ wb) =
        ≈R-≈ (wg wb) (≈-sym (≈-trans (bind-pure (distribIR-pure ((f′ , g′) , inj₂ b′))) (bind-pure (≈-trans (bind-pure ret-bind) ret-bind))))

  -- ★ THE LOOP: the round lent to every round, against master's `Iter` of `apply`
  -- (the closure reads the round: `llamω`, plan 0.157 S2)
  loopL : ∀ {A B : IRTy} {F F′} → W (A I.⇛[ G.act ] (B I.+ A)) F F′ → ∀ {a a′} → W A a a′
        → Lᶜ δ (liter (bev {g = act} {⟪ A ⟫} {⟪ B ⟫ ⊕t ⟪ A ⟫}) k-bev) F a
          ≈[ W B ] evalᴰ fmt ρ (M.Iter (M.apply {A} {B I.+ A} {G.act} M.∘ M.⟨ M.fst , M.snd ⟩)) (F′ , a′)
  loopL wF wa =
    iter-congR (λ r → ≈R-≈ (wF r) (≈-sym (bind-pure (≈-trans ret-bind ret-bind))))
               (≈R-≈ (wF wa) (≈-sym (bind-pure (≈-trans ret-bind ret-bind))))

  ok-loop : ∀ {m n} {Γ : Ctx m n} {Ψ : Usage n} {A B : Ty m}
              (r : Expr Γ Ψ (A ⇒[ G.mk-kind G.Many G.act ] (B + A))) → Goal r → Goal (loop r)
  ok-loop {Γ = Γ} {Ψ} r rr = rel-∘ (rel-cloL G.eff tt loopL) (rel-∘ rr (rel-weak am {Γ = Γ} (⊑ᵘ-*Many Ψ)))

  -- ★ A CONVERSION, along the subtyping derivation (`coeIR`)
  -- (the argument converted, the closure beside it)
  rel-arg : ∀ {F X X′ : IRTy} {f : LTm L ⟪ X′ ⟫ ⟪ X ⟫} {f′ : M.IR X′ X}
          → Rel f f′ → Rel (lid {A = ⟪ F ⟫} ⊗l f) M.⟨ M.fst {F} {X′} , f′ M.∘ M.snd ⟩
  rel-arg rf = mkRel λ { {Fv , x} {Fv′ , x′} (wF , wx) →
    ≈-≈R ret-bind (≈R-≈ (>>=-congR (relOf rf wx) (λ r → ret≈R (wF , r)))
                        (≈-sym (≈-trans ret-bind (>>=-cong ret-bind (λ _ → ≈-refl))))) }

  -- ★ D497: a coerced arrow's lent body (the closure read) means its owned body (the closure moved in)
  lent≈ : ∀ {g X X′ Y Y′} (f : LTm L X′ X) (h : LTm L Y Y′) (c : ⟦ Fn many g X Y ⟧) (a : ⟦ X′ ⟧)
        → Lᶜ δ (blift h ∘l bev {g = g} ∘l blift f) c a ≈ Lᶜ δ (h ∘l apω {g = g} ∘l (lid ⊗l f)) tt (c , a)
  lent≈ f h c a =
    ≈-sym (≈-blk refl (>>=-cong (≈-trans (bind-assoc (Lᶜ δ f tt a) _ _) (>>=-cong ≈-refl (λ b → ret-bind))) (λ _ → ≈-refl)))

  rel-coeL : ∀ {m} {A B : Ty m} (p : A <: B) → Rel (coeL {L} p) (coeIR p)
  rel-coeL sub-void   = rel-zero
  rel-coeL sub-unit   = rel-id
  rel-coeL sub-int    = rel-id
  rel-coeL sub-float  = rel-id
  -- (D497: the coerced arrow reads the closure it holds; its lent body means the owned one)
  rel-coeL (sub-arr {q = G.Zero} {π = π} {π′ = π′} a b r) =
    rel-cloL π′ _ (λ w wa → relOf (rel-∘ (rel-coeL b) (rel-apω {π = π})) (w , wa))
  rel-coeL (sub-arr {q = G.One}  {π = π} {π′ = π′} a b r) =
    rel-cloL π′ _ (λ {x} w {a₀} wa → ≈-≈R (lent≈ (coeL a) (coeL b) x a₀)
                                      (relOf (rel-∘ (rel-coeL b) (rel-∘ (rel-apω {π = π}) (rel-arg (rel-coeL a)))) (w , wa)))
  rel-coeL (sub-arr {q = G.Many} {π = π} {π′ = π′} a b r) =
    rel-cloL π′ _ (λ {x} w {a₀} wa → ≈-≈R (lent≈ (coeL a) (coeL b) x a₀)
                                      (relOf (rel-∘ (rel-coeL b) (rel-∘ (rel-apω {π = π}) (rel-arg (rel-coeL a)))) (w , wa)))
  rel-coeL (sub-* a b) = mkRel λ { {x , y} {x′ , y′} (wx , wy) →
    ≈R-≈ (>>=-congR (relOf (rel-coeL a) wx) (λ r → >>=-congR (relOf (rel-coeL b) wy) (λ r′ → ret≈R (r , r′))))
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

  -- ★ THE FOLD. A fold's congruence, for pointwise-equal algebras
  mutual
    cataC-≡ : ∀ F {X : Set} {a₁ a₂ : FS F X → T∞ X} → (∀ y → a₁ y ≡ a₂ y) → ∀ x → cataC δ F a₁ x ≈ cataC δ F a₂ x
    cataC-≡ F {a₁ = a₁} h (inμ w) = >>=-cong (travC-≡ F F h w) (λ y → subst (λ m → a₁ y ≈ m) (h y) ≈-refl)

    travC-≡ : ∀ F G {X : Set} {a₁ a₂ : FS F X → T∞ X} → (∀ y → a₁ y ≡ a₂ y) → ∀ w → travC δ F G a₁ w ≈ travC δ F G a₂ w
    travC-≡ F Idf      h y        = cataC-≡ F h y
    travC-≡ F Kone     h y        = ≈-refl
    travC-≡ F Kzero    h ()
    travC-≡ F (Kb _)   h y        = ≈-refl
    travC-≡ F (Kμ _)   h y        = ≈-refl
    travC-≡ F (G ⊕f H) h (inj₁ y) = >>=-cong (travC-≡ F G h y) (λ _ → ≈-refl)
    travC-≡ F (G ⊕f H) h (inj₂ z) = >>=-cong (travC-≡ F H h z) (λ _ → ≈-refl)
    travC-≡ F (G ⊗f H) h (y , z)  = >>=-cong (travC-≡ F G h y) (λ _ → >>=-cong (travC-≡ F H h z) (λ _ → ≈-refl))

  -- the core's lent algebra is the pass's `apply`, moved along the same type equation
  alg-eq : ∀ {g} {X₀ Z B : LTy} (p : X₀ ≡ Z) (f : ⟦ Fn many g X₀ B ⟧) (z : ⟦ Z ⟧)
         → Lᶜ δ (cast {L} {Fn many g X₀ B} p refl (bev {g = g} {X₀} {B})) f z
           ≡ ev δ (subst (λ X → P.IR L (Fn many g X₀ B ⊗t X) B) p (P.apply {g = g})) (f , z)
  alg-eq refl f z = refl

  subst-trans′ : ∀ {E B X Y Z : LTy} (p : X ≡ Y) (q : Y ≡ Z) (c : P.IR L (E ⊗t X) B)
               → subst (λ W′ → P.IR L (E ⊗t W′) B) q (subst (λ W′ → P.IR L (E ⊗t W′) B) p c)
                 ≡ subst (λ W′ → P.IR L (E ⊗t W′) B) (trans p q) c
  subst-trans′ refl refl c = refl

  -- the pass's algebra against master's, moved along the Spec's layer
  fold-ih : ∀ {X Y B : IRTy} {π} (c : X ≡ Y) {x x′} → W ((X I.⇛[ π ] B) I.* Y) x x′
          → ev δ (subst (λ Z → P.IR L (Fn many (grade π) ⟪ X ⟫ ⟪ B ⟫ ⊗t Z) ⟪ B ⟫) (cong ⟪_⟫ c) (P.apply {g = grade π})) x
            ≈[ W B ] evalᴰ fmt ρ (subst (λ o → M.IR ((X I.⇛[ π ] B) I.* o) B) c (M.apply M.∘ M.⟨ M.fst , M.snd ⟩)) x′
  fold-ih refl {f , y} {f′ , y′} (wf , wy) = ≈R-≈ (wf wy) (≈-sym (bind-pure (≈-trans ret-bind ret-bind)))

  rel-foldL : ∀ {m} {Δ : KCtx m} (F : Fun m) (wf : WFFun Δ F) (A : Ty m) {π} {e e′}
            → W (⌊ ST.⟦ F ⟧F A ⌋ I.⇛[ π ] ⌊ A ⌋) e e′ → ∀ {x x′} → W ⌊ ST.μ F ⌋ x x′
            → Lᶜ δ (lcata (lf (I.eraseF F)) (cast (layerEq F wf A) refl (bev {g = grade π} {ty (ST.⟦ F ⟧F A)} {ty A}))) e x
              ≈[ W ⌊ A ⌋ ] evalᴰ fmt ρ (M.Cata (wf-⌊⌋ wf) (subst (λ o → M.IR ((⌊ ST.⟦ F ⟧F A ⌋ I.⇛[ π ] ⌊ A ⌋) I.* o) ⌊ A ⌋) (⌊⟧T-commute F A) (M.apply M.∘ M.⟨ M.fst , M.snd ⟩))) (e′ , x′)
  rel-foldL F wf A {π} {e} {e′} we {x} {x′} wx =
    ≈-≈R (cataC-≡ (lf (I.eraseF F))
            (λ y → trans (alg-eq (layerEq F wf A) e (coh⁻¹ (lf (I.eraseF F)) _ y))
                         (cong (λ c → ev δ c (e , coh⁻¹ (lf (I.eraseF F)) _ y))
                               (sym (subst-trans′ (cong ⟪_⟫ (⌊⟧T-commute F A)) (⟪⟫-TI (wf-⌊⌋ wf) ⌊ A ⌋) P.apply))))
            x)
         (BP.Casts.cata≈ (casts δ cs) (wf-⌊⌋ wf)
            (subst (λ o → M.IR ((⌊ ST.⟦ F ⟧F A ⌋ I.⇛[ π ] ⌊ A ⌋) I.* o) ⌊ A ⌋) (⌊⟧T-commute F A) (M.apply M.∘ M.⟨ M.fst , M.snd ⟩))
            (subst (λ Z → P.IR L (Fn many (grade π) (ty (ST.⟦ F ⟧F A)) (ty A) ⊗t Z) (ty A)) (cong ⟪_⟫ (⌊⟧T-commute F A)) (P.apply {g = grade π}))
            (fold-ih (⌊⟧T-commute F A)) (we , wx))

  ok-cata : ∀ {m n} {Γ : Ctx m n} {Ψ : Usage n} {F : Fun m} {Δₖ : KCtx m} {A : Ty m} {π}
              (wf : WFFun Δₖ F) (alg : Expr Γ Ψ (ST.⟦ F ⟧F A ⇒[ G.mk-kind G.Many π ] A)) → Goal alg → Goal (cata wf alg)
  ok-cata {Γ = Γ} {Ψ} {F} {A = A} {π} wf alg ra = rel-∘ (rel-cloL π _ (rel-foldL F wf A {π})) (rel-∘ ra (rel-weak am {Γ = Γ} (⊑ᵘ-*Many Ψ)))

  -- ★ THE UNFOLD. A cast of the identity returns its input, moved
  cast-id : ∀ {X Y : LTy} (q : X ≡ Y) (v : ⟦ X ⟧) → Lᶜ δ (cast {L} {One} refl q (lid {A = X})) tt v ≡ return∞ (subst ⟦_⟧ q v)
  cast-id refl v = refl

  -- a block moved along its result's type, and its meaning
  blk-sub : ∀ {X Y Y′} (q : Y ≡ Y′) {t : P.IR L X Y} → P.BlkIR L t → P.BlkIR L (subst (λ Z → P.IR L X Z) q t)
  blk-sub refl φ = φ

  evB-sub : ∀ {X Y Y′} (q : Y ≡ Y′) {t : P.IR L X Y} (φ : P.BlkIR L t) x
          → evB δ (blk-sub q φ) x ≡ subst (λ Z → T ⟦ Z ⟧) q (evB δ φ x)
  evB-sub refl φ x = refl

  -- a closure moved along its result's type, applied
  app-sub : ∀ {S Y Y′ : LTy} (q : Y ≡ Y′) (f : ⟦ Fn many act S Y ⟧) a
          → subst ⟦_⟧ (cong (Fn many act S) q) f a ≡ subst (λ Z → T ⟦ Z ⟧) q (f a)
  app-sub refl f a = refl

  T-trans : ∀ {X Y Z : LTy} (p : X ≡ Y) (q : Y ≡ Z) (v : T ⟦ X ⟧)
          → subst (λ W′ → T ⟦ W′ ⟧) (trans p q) v ≡ subst (λ W′ → T ⟦ W′ ⟧) q (subst (λ W′ → T ⟦ W′ ⟧) p v)
  T-trans refl refl v = refl

  -- the pass's coalgebra against master's, moved along the Spec's layer
  unfold-ih : ∀ {X Y : IRTy} {A : IRTy} {φ : G.Finite} (c : X ≡ Y) {x x′} → W ((A I.⇛[ G.fin φ ] X) I.* A) x x′
            → ev δ (subst (λ Z → P.IR L (Fn many act ⟪ A ⟫ ⟪ X ⟫ ⊗t ⟪ A ⟫) Z) (cong ⟪_⟫ c) (P.apply {g = act})) x
              ≈[ W Y ] evalᴰ fmt ρ (subst (λ o → M.IR ((A I.⇛[ G.fin φ ] X) I.* A) o) c (M.apply M.∘ M.⟨ M.fst , M.snd ⟩)) x′
  unfold-ih refl {f , a} {f′ , a′} (wf , wa) = ≈R-≈ (wf wa) (≈-sym (bind-pure (≈-trans ret-bind ret-bind)))

  module UF {m} {Δ : KCtx m} (F : Fun m) (wf : WFFun Δ F) (A : Ty m) (φf : G.Finite) where
    F′ = I.eraseF F
    wfI = wf-⌊⌋ wf
    c₀q = ⌊⟧T-commute F A
    dq = ⟪⟫-TI wfI ⌊ A ⌋
    Eᵢ = ⌊ A ⌋ I.⇛[ G.fin φf ] ⌊ ST.⟦ F ⟧F A ⌋

    cIR : M.IR (Eᵢ I.* ⌊ A ⌋) (⟦ F′ ⟧TI ⌊ A ⌋)
    cIR = subst (λ o → M.IR (Eᵢ I.* ⌊ A ⌋) o) c₀q (M.apply M.∘ M.⟨ M.fst , M.snd ⟩)

    c′ : P.IR L (⟪ Eᵢ ⟫ ⊗t ⟪ ⌊ A ⌋ ⟫) ⟪ ⟦ F′ ⟧TI ⌊ A ⌋ ⟫
    c′ = subst (λ Z → P.IR L (⟪ Eᵢ ⟫ ⊗t ⟪ ⌊ A ⌋ ⟫) Z) (cong ⟪_⟫ c₀q) (P.apply {g = act})

    φ : P.BlkIR L (subst (λ Z → P.IR L (⟪ Eᵢ ⟫ ⊗t ⟪ ⌊ A ⌋ ⟫) Z) dq c′)
    φ = blk-sub dq (blk-sub (cong ⟪_⟫ c₀q) P.i-apply)

    -- the core's coalgebra: the closure's function, moved
    k : ⟦ ⟪ Eᵢ ⟫ ⟧ → ⟦ ty A ⟧ → T (FS (lf F′) ⟦ ty A ⟧)
    k e = cohc (lf F′) (ty A) (subst ⟦_⟧ (cong (Fn many act (ty A)) (layerEq F wf A)) e)

    k≡ : ∀ e a → k e a ≡ fmapT (coh (lf F′) (ty A)) (evB δ φ (e , a))
    k≡ e a = cong (fmapT (coh (lf F′) (ty A)))
      (trans (app-sub (layerEq F wf A) e a)
        (trans (T-trans (cong ⟪_⟫ c₀q) dq (e a))
               (sym (trans (evB-sub dq (blk-sub (cong ⟪_⟫ c₀q) P.i-apply) (e , a))
                           (cong (subst (λ Z → T ⟦ Z ⟧) dq) (evB-sub (cong ⟪_⟫ c₀q) P.i-apply (e , a)))))))

    -- ★ the unfold: the coalgebra and the seed, a ν, against master's `Ana`
    rel-unfold : Rel (lunf ∘l (cast {L} {One} refl (cong (Fn many act (ty A)) (layerEq F wf A)) lid ⊗l lid)) (M.Ana wfI cIR)
    rel-unfold = mkRel λ { {e , a} {e′ , a′} (we , wa) →
      ≈-≈R (bind-pure (≈-trans (bind-pure (subst (λ m′ → m′ ≈ return∞ (subst ⟦_⟧ (cong (Fn many act (ty A)) (layerEq F wf A)) e)) (sym (cast-id (cong (Fn many act (ty A)) (layerEq F wf A)) e)) ≈-refl)) ret-bind))
           (ret≈R (Once.LinCore.Casts.Unfold.ana-W fmt ans δ cs wfI cIR c′ φ (unfold-ih {φ = φf} c₀q) e e′ we (k e) (k≡ e) wa)) }

  ok-ana : ∀ {m n} {Γ : Ctx m n} {Ψ : Usage n} {F : Fun m} {Δₖ : KCtx m} {A : Ty m} {π₀} {φ : G.Finite}
             (wf : WFFun Δₖ F) (c : Expr Γ Ψ (A ⇒[ G.mk-kind G.Many (G.fin φ) ] ST.⟦ F ⟧F A))
           → Goal c → Goal (ana {π₀ = π₀} wf c)
  ok-ana {Γ = Γ} {Ψ} {F} {A = A} {π₀} {φ} wf c rc =
    rel-∘ (rel-cloG π₀ _ (UF.rel-unfold F wf A φ)) (rel-∘ rc (rel-weak am {Γ = Γ} (⊑ᵘ-*Many Ψ)))

  -- ★ a reference, related: the program's obligation (a reference names its
  -- definition at its declared type, grade and all; `Calls.rel-ref` derives it
  -- from the table where it holds)
  RefOK : ∀ {m} → String → Ty m → Set
  RefOK x A = Rel (refL rs A (bare x)) (refIR A (bare x))

  -- ★★ THE BRIDGE'S MEANING: for every expression whose references are related
  -- ★ D499: a lambda whose body is a read: the read, run lent beside the argument, means the body
  lentRead : ∀ {m n} {Γ : Ctx m n} {Ψ : Usage n} {A B : Ty m} {q′} (e : Expr (Γ SC.▸ A) (q′ ∷ Ψ) B) (d : Rd e)
             (x : ⟦ Co (Γ SC.▸ A) (q′ ∷ Ψ) ⟧)
           → Lᶜ δ (Rt {L} {Γ = Γ SC.▸ A} d (⊑ᵘ-refl (q′ ∷ Ψ))) x tt ≈ Lᶜ δ (Lq rs e) tt x
  lentRead {Γ = Γ} {Ψ} {q′ = q′} e d x =
    subst (λ z → Lᶜ δ (Rt {L} {Γ = Γ SC.▸ _} d (⊑ᵘ-refl (q′ ∷ Ψ))) x tt ≈ Lᶜ δ (Lq rs e) tt z)
          (wv-refl {Γ = Γ SC.▸ _} (q′ ∷ Ψ) x) (rt-eq d (⊑ᵘ-refl (q′ ∷ Ψ)) x)

  rel-lamOr : ∀ {R : Set} {X A B : IRTy} (π : G.Purity) {b : LTm L (⟪ X ⟫ ⊗t ⟪ A ⟫) ⟪ B ⟫} {β : Blk b} (md : Maybe R)
                {rt : R → Tm L (⟪ X ⟫ ⊗t ⟪ A ⟫) One ⟪ B ⟫} {kt : ∀ d → Blk (rt d)} {b′ : M.IR (X I.* A) B}
            → Rel b b′ → (∀ d x a → Lᶜ δ (rt d) (x , a) tt ≈ Lᶜ δ b tt (x , a))
            → Rel (lamOr rs π b β md rt kt) (M.curry {π = π} b′)
  rel-lamOr π nothing  rb h = rel-cloG π _ rb
  rel-lamOr π (just d) {rt = rt} rb h = rel-cloL π _ (λ {x} w {a} wa →
    ≈-≈R (≈-blk refl (≈-trans (bind-assoc (Lᶜ δ (rt d) (x , a) tt) _ _)
                       (≈-trans (>>=-cong ≈-refl (λ v → ≈-blk refl ≈-refl)) (≈-trans bind-return (h d x a)))))
         (relOf rb (w , wa)))

  Lq-ok : ∀ {m n} {Γ : Ctx m n} {Ψ : Usage n} {A : Ty m} (e : Expr Γ Ψ A)
        → Refs (λ _ _ → ⊤) RefOK RefOK e → Goal e
  -- ★ D494: a fork's arm, by what it takes
  armOk : ∀ {m n} {Γ : Ctx m n} {Ψ : Usage n} {A B : Ty m} {π} (f : Expr Γ Ψ (A ⇒[ G.mk-kind G.Many π ] B))
          (d : Maybe (Arm f)) → Refs (λ _ _ → ⊤) RefOK RefOK f → ArmOK f d
  armOk f nothing r = armOk-all f (Lq-ok f r)
  armOk {Γ = Γ} {π = π} _ (just (arm-map (pjl p))) r = armOk-map {Γ = Γ} {π = π} p
  armOk _ (just (arm-comp h (pjl p))) (rh , _) = armOk-comp h p (Lq-ok h rh)
  -- an application at `Many`, a branch where `appL` makes one (D481 B1)
  ok-appL : ∀ {m n} {Γ : Ctx m n} {Ψ₁ Ψ₂ : Usage n} {A B : Ty m}
              (f : Expr Γ Ψ₁ (A ⇒[ G.mk-kind G.Many G.pure ] B)) (x : Expr Γ Ψ₂ A) (md : Maybe (CP f))
          → Refs (λ _ _ → ⊤) RefOK RefOK f → Refs (λ _ _ → ⊤) RefOK RefOK x
          → Rel (appL rs {Γ = Γ} f x md) (elaborate am (app f x))
  Lq-ok {Γ = Γ} (var i) r = rel-var {Γ = Γ} i
  Lq-ok (lam {q' = G.Zero} {π = π} G.Zero _ e) r = rel-cloG π _ (rel-∘ (Lq-ok e r) rel-fst)
  Lq-ok (lam {q' = G.Zero} {π = π} G.One  _ e) r = rel-cloG π _ (rel-∘ (Lq-ok e r) rel-fst)
  Lq-ok (lam {q' = G.Zero} {π = π} G.Many _ e) r = rel-cloG π _ (rel-∘ (Lq-ok e r) rel-fst)
  Lq-ok (lam {q' = G.One}  {π = π} G.One  _ e) r = rel-lamOr π (rdl? e) (Lq-ok e r) (λ d x a → lentRead e d (x , a))
  Lq-ok (lam {q' = G.One}  {π = π} G.Many _ e) r = rel-lamOr π (rdl? e) (Lq-ok e r) (λ d x a → lentRead e d (x , a))
  Lq-ok (lam {q' = G.Many} {π = π} G.Many _ e) r = rel-lamOr π (rdl? e) (Lq-ok e r) (λ d x a → lentRead e d (x , a))
  Lq-ok (app {q = G.Zero} f x) (rf , rx) = ok-app0 f x (Lq-ok f rf)
  Lq-ok {Γ = Γ} (app {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {q = G.One} f x) (rf , rx) =
    rel-app Γ Ψ₁ Ψ₂ (G.One *ᵘ Ψ₂) (⊑ᵘ-*One Ψ₂) (Lq-ok f rf) (Lq-ok x rx)
  Lq-ok {Γ = Γ} (app {q = G.Many} f x) (rf , rx) = ok-appL {Γ = Γ} f x (cp? f) rf rx
  Lq-ok (effApp f x) (rf , rx) = ok-effApp f x (Lq-ok f rf) (Lq-ok x rx)
  Lq-ok {Γ = Γ} (pair a b) (ra , rb) = rel-pairL {Γ = Γ} a b (rdw? a) (Lq-ok a ra) (Lq-ok b rb)
  Lq-ok (fst' p) r = rel-∘ rel-fst (Lq-ok p r)
  Lq-ok (snd' p) r = rel-∘ rel-snd (Lq-ok p r)
  Lq-ok (inl' a) r = rel-∘ rel-inl (Lq-ok a r)
  Lq-ok (inr' b) r = rel-∘ rel-inr (Lq-ok b r)
  Lq-ok (case' s l r) (rs′ , rl , rr) = ok-case s l r (Lq-ok s rs′) (Lq-ok l rl) (Lq-ok r rr)
  Lq-ok unit r = rel-drop
  Lq-ok (absurd v) r = rel-∘ rel-zero (Lq-ok v r)
  Lq-ok (let' {q = G.Zero} e1 e2) (r1 , r2) = ok-let0 e1 e2 (Lq-ok e2 r2)
  Lq-ok {Γ = Γ} (let' {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {q = G.One} {A = A} e1 e2) (r1 , r2) =
    rel-∘ (Lq-ok e2 r2) (rel-∘ (rel-bind {Γ = Γ} {A = A} G.One) (rel-let Γ Ψ₂ Ψ₁ (G.One *ᵘ Ψ₁) (⊑ᵘ-*One Ψ₁) (Lq-ok e1 r1)))
  Lq-ok {Γ = Γ} (let' {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {q = G.Many} {A = A} e1 e2) (r1 , r2) =
    rel-∘ (Lq-ok e2 r2) (rel-∘ (rel-bind {Γ = Γ} {A = A} G.Many) (rel-let Γ Ψ₂ Ψ₁ (G.Many *ᵘ Ψ₁) (⊑ᵘ-*Many Ψ₁) (Lq-ok e1 r1)))
  Lq-ok (int n) r = rel-∘ (mkRel λ _ → ret≈R refl) rel-drop
  Lq-ok (float d) r = rel-∘ (mkRel λ _ → ret≈R refl) rel-drop
  Lq-ok (num h o e) r = ok-num h o e (Lq-ok e r)
  Lq-ok (coerce p f) r = ok-coerce p f (Lq-ok f r)
  Lq-ok {Γ = Γ} (sigOp name c) r = ok-sigOp {Γ = Γ} name c
  Lq-ok (closure name) r = rel-∘ r rel-drop
  Lq-ok (poly name T) r = rel-∘ r rel-drop
  Lq-ok (closed e) r = rel-∘ (Lq-ok e r) rel-drop
  Lq-ok {Γ = Γ} (lift-morphism mp) r = ok-lift {Γ = Γ} mp
  Lq-ok (morph-app mp x) (_ , r) = ok-mapp mp x (Lq-ok x r)
  Lq-ok (comp' f g) (rf , rg) = ok-comp f g (Lq-ok f rf) (Lq-ok g rg)
  Lq-ok (copair' f g) (rf , rg) = ok-copair f g (Lq-ok f rf) (Lq-ok g rg)
  Lq-ok (fork' f g) (rf , rg) = ok-fork f g (armOk f (arm? f) rf) (armOk g (arm? g) rg)
  Lq-ok (curry' f) r = ok-curry f (Lq-ok f r)
  Lq-ok (cata wf alg) r = ok-cata wf alg (Lq-ok alg r)
  Lq-ok (ana wf c) r = ok-ana wf c (Lq-ok c r)
  Lq-ok (loop round) r = ok-loop round (Lq-ok round r)

  ok-appL {Γ = Γ} {Ψ₁} {Ψ₂} f x nothing rf rx =
    rel-appR {Γ = Γ} f x (pth? f) (rdx? Ψ₁ Ψ₂ x) (Lq-ok f rf) (Lq-ok x rx)
  ok-appL {Γ = Γ} (copair' f g) x (just (cp i j)) (rf , rg) rx =
    rel-appB {Γ = Γ} f g x i j (Lq-ok f rf) (Lq-ok g rg) (Lq-ok x rx)
