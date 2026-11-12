-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.LinCore.Casts — plan 0.146 B1.3: the obligations `BridgeProof.Casts`,
-- each a lemma about one generator whose translation crosses a cast of
-- types.
--
--   * §1, general: a term transported along equal types means its meaning
--     transported (`ev-subst₂`), and a relation survives a transport
--     (`≈-subst`); a pair's and a sum's transport is its parts'.
--   * §2, SigOps: an op's base argument is its flat one (`arg≡`), its answer
--     related to the flat answer (`res-W`), both by the base evidence; the two
--     sides run the same contract block (`sigOpT`).
------------------------------------------------------------------------

{-# OPTIONS --guardedness #-}

open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (subst; subst₂; sym; cong₂)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Sum.Relation.Binary.Pointwise using () renaming (inj₁ to ⊎₁; inj₂ to ⊎₂)
open import Once.Spec.Numerics using (TargetNum)
open import Once.IR.Semantics.Trace using (FFIAnswers)
import Once.IR.Semantics.Trace as Tr
open import Once.IR.Semantics.Iterative using (embed)
import Once.IR.Semantics.Iterative
open import Once.IR.Semantics.StreamInf using (in-νᴵ; anaFᴵ)
import Once.IR.Semantics.StreamInf as SI
open import Once.Spec.Type using (Type; ∅ₖ; b-var; b-Unit; b-Void; b-Int; b-Float; b-*; b-+)
open import Once.IRTy using (IRTy; ⌊_⌋; _*_; _+_)
open import Once.Denotation.ValueDomain using (⟦_⟧ᴰᴵ; ⟦_⟧ᴰ; cohᴰ; forgetᵇ; injectᵇ)
open import Once.Spec.Word using (Carrier)
open import Once.Spec.Type using () renaming (Base to SBase)
import Once.IR.Semantics.Value Carrier Carrier as Val
import Relation.Binary.PropositionalEquality
open import Once.Spec.Name using (CanonicalName)
open import Once.SigOp.Info using (SigOpInfo; module SigOpInfo)
open import Once.Denotation.DenotTrace using (evalᴰ; sigOpT; callEnv)
import Once.IR as M
import Once.Spec.Type as ST
open import Once.IRTy using (K; IsBaseTypeI; base-Unit; base-Void; base-Int; base-Float; base-Prod; base-Sum; WellFormedFI; wf-K; wf-Id; wf-Sum; wf-Prod; ⟦_⟧TI; μ-type; ν-type; ⌈_⌉; ⌈_⌉F; ⌈⟧TI-commute) renaming (_⊕_ to _⊕ᴵ_; _⊗_ to _⊗ᴵ_)
open import Once.IRTy.WF using (base-⌈⌉; wf-⌈⌉)
open import Once.Denotation.ValueDomain using (coerce-functor-D; coerce-functor⁻¹-D)
open import Once.Denotation.DenotTrace using (cata-ev-algᴰ)
open import Once.IR.Semantics.Iterative using (seqF∞)
import Once.IR.Semantics.Polynomial as Pol
open import Data.Empty using (⊥)
open import Data.Sum.Relation.Binary.Pointwise using (Pointwise)
open import Once.IRTy using (IRFunctor; Id; Unit; Void; Int; Float; _⇛[_]_)
open import Once.Spec.Polynomial using (⟦_⟧SF)
import Once.LinCore.FromIR
import Once.LinCore.Bridge
import Once.LinCore.Bisim
import Once.LinCore.BridgeProof

module Once.LinCore.Casts (fmt : TargetNum) (ans : FFIAnswers) where

open import Once.LinCore.NbEPLinCore fmt ans
open Once.LinCore.FromIR fmt ans
open Once.LinCore.Bridge fmt ans
module BP = Once.LinCore.BridgeProof fmt ans
open Once.LinCore.Bisim fmt ans using (_≈[_]_; module _≈[_]_; BlR; ≈retR; ≈stepR; ≈callR; ≈haltR; ret≈R; >>=-congR; fmap-congR; ≈-≈R; ≈-sym)

------------------------------------------------------------------------
-- 1. TRANSPORTS.
------------------------------------------------------------------------

-- a term moved along equal types means its meaning, moved
ev-subst₂ : ∀ {Γ} (δ : Env Γ) {X X′ Y Y′} (e₁ : X′ ≡ X) (e₂ : Y′ ≡ Y) (c : P.IR Γ X Y) (a : ⟦ X′ ⟧)
          → P.ev δ (subst₂ (P.IR Γ) (sym e₁) (sym e₂) c) a ≡ subst (λ Z → T∞ ⟦ Z ⟧) (sym e₂) (P.ev δ c (subst ⟦_⟧ e₁ a))
ev-subst₂ δ refl refl c a = refl

-- a relation on a transported computation is one on the computation
≈-subst : ∀ {Y Y′ Z} {R : ⟦ Y′ ⟧ → Z → Set} (e : Y ≡ Y′) {m : T∞ ⟦ Y ⟧} {m′ : T∞ Z}
        → m ≈[ (λ y z → R (subst ⟦_⟧ e y) z) ] m′ → subst (λ V → T∞ ⟦ V ⟧) e m ≈[ R ] m′
≈-subst refl p = p

-- a pair's and a sum's transport are their parts'
subst-⊗ : ∀ {X X′ Y Y′} (e : X ≡ X′) (e′ : Y ≡ Y′) (x : ⟦ X ⟧) (y : ⟦ Y ⟧)
        → subst ⟦_⟧ (cong₂ _⊗t_ e e′) (x , y) ≡ (subst ⟦_⟧ e x , subst ⟦_⟧ e′ y)
subst-⊗ refl refl x y = refl

subst-⊕₁ : ∀ {X X′ Y Y′} (e : X ≡ X′) (e′ : Y ≡ Y′) (x : ⟦ X ⟧)
         → subst ⟦_⟧ (cong₂ _⊕t_ e e′) (inj₁ x) ≡ inj₁ (subst ⟦_⟧ e x)
subst-⊕₁ refl refl x = refl

subst-⊕₂ : ∀ {X X′ Y Y′} (e : X ≡ X′) (e′ : Y ≡ Y′) (y : ⟦ Y ⟧)
         → subst ⟦_⟧ (cong₂ _⊕t_ e e′) (inj₂ y) ≡ inj₂ (subst ⟦_⟧ e′ y)
subst-⊕₂ refl refl y = refl

subst-× : ∀ {X X′ Y Y′ : Set} (e : X ≡ X′) (e′ : Y ≡ Y′) (x : X) (y : Y)
        → subst (λ S → S) (cong₂ _×_ e e′) (x , y) ≡ (subst (λ S → S) e x , subst (λ S → S) e′ y)
subst-× refl refl x y = refl

subst-⊎₁ : ∀ {X X′ Y Y′ : Set} (e : X ≡ X′) (e′ : Y ≡ Y′) (x : X)
         → subst (λ S → S) (cong₂ _⊎_ e e′) (inj₁ {B = Y} x) ≡ inj₁ (subst (λ S → S) e x)
subst-⊎₁ refl refl x = refl

subst-⊎₂ : ∀ {X X′ Y Y′ : Set} (e : X ≡ X′) (e′ : Y ≡ Y′) (y : Y)
         → subst (λ S → S) (cong₂ _⊎_ e e′) (inj₂ {A = X} y) ≡ inj₂ (subst (λ S → S) e′ y)
subst-⊎₂ refl refl y = refl

-- the same, transported back
subst-⊗⁻ : ∀ {X X′ Y Y′} (e : X ≡ X′) (e′ : Y ≡ Y′) (x : ⟦ X′ ⟧) (y : ⟦ Y′ ⟧)
         → subst ⟦_⟧ (sym (cong₂ _⊗t_ e e′)) (x , y) ≡ (subst ⟦_⟧ (sym e) x , subst ⟦_⟧ (sym e′) y)
subst-⊗⁻ refl refl x y = refl

subst-⊕₁⁻ : ∀ {X X′ Y Y′} (e : X ≡ X′) (e′ : Y ≡ Y′) (x : ⟦ X′ ⟧)
          → subst ⟦_⟧ (sym (cong₂ _⊕t_ e e′)) (inj₁ x) ≡ inj₁ (subst ⟦_⟧ (sym e) x)
subst-⊕₁⁻ refl refl x = refl

subst-⊕₂⁻ : ∀ {X X′ Y Y′} (e : X ≡ X′) (e′ : Y ≡ Y′) (y : ⟦ Y′ ⟧)
          → subst ⟦_⟧ (sym (cong₂ _⊕t_ e e′)) (inj₂ y) ≡ inj₂ (subst ⟦_⟧ (sym e′) y)
subst-⊕₂⁻ refl refl y = refl

subst-×⁻ : ∀ {X X′ Y Y′ : Set} (e : X ≡ X′) (e′ : Y ≡ Y′) (x : X′) (y : Y′)
         → subst (λ S → S) (sym (cong₂ _×_ e e′)) (x , y) ≡ (subst (λ S → S) (sym e) x , subst (λ S → S) (sym e′) y)
subst-×⁻ refl refl x y = refl

subst-⊎₁⁻ : ∀ {X X′ Y Y′ : Set} (e : X ≡ X′) (e′ : Y ≡ Y′) (x : X′)
          → subst (λ S → S) (sym (cong₂ _⊎_ e e′)) (inj₁ {B = Y′} x) ≡ inj₁ (subst (λ S → S) (sym e) x)
subst-⊎₁⁻ refl refl x = refl

subst-⊎₂⁻ : ∀ {X X′ Y Y′ : Set} (e : X ≡ X′) (e′ : Y ≡ Y′) (y : Y′)
          → subst (λ S → S) (sym (cong₂ _⊎_ e e′)) (inj₂ {A = X′} y) ≡ inj₂ (subst (λ S → S) (sym e′) y)
subst-⊎₂⁻ refl refl y = refl

------------------------------------------------------------------------
-- 2. ★ SIGOPS: the two sides run the same contract block.
------------------------------------------------------------------------

-- an op's argument: the core's flat value is master's base value
arg≡ : ∀ {A : Type} (b : SBase ∅ₖ A) {x : ⟦ ⟪ ⌊ A ⌋ ⟫ ⟧} {a′ : ⟦ ⌊ A ⌋ ⟧ᴰᴵ} → W ⌊ A ⌋ x a′
     → toV b (toF (flat b) (subst ⟦_⟧ (⟪⌊⌋⟫-flat b) x)) ≡ forgetᵇ b (subst (λ S → S) (cohᴰ A) a′)
arg≡ (b-var {i = ()} _)
arg≡ b-Unit  w = refl
arg≡ b-Void  {x = ()}
arg≡ b-Int   w = w
arg≡ b-Float w = w
arg≡ (b-* {A = A} {B = B} a b) {x = x₁ , x₂} {a′ = a₁ , a₂} (w₁ , w₂)
  rewrite subst-⊗ (⟪⌊⌋⟫-flat a) (⟪⌊⌋⟫-flat b) x₁ x₂ | subst-× (cohᴰ A) (cohᴰ B) a₁ a₂ =
  cong₂ _,_ (arg≡ a w₁) (arg≡ b w₂)
arg≡ (b-+ {A = A} {B = B} a b) {x = inj₁ x} {a′ = inj₁ y} (⊎₁ w)
  rewrite subst-⊕₁ (⟪⌊⌋⟫-flat a) (⟪⌊⌋⟫-flat b) x | subst-⊎₁ (cohᴰ A) (cohᴰ B) y =
  Relation.Binary.PropositionalEquality.cong inj₁ (arg≡ a w)
arg≡ (b-+ {A = A} {B = B} a b) {x = inj₂ x} {a′ = inj₂ y} (⊎₂ w)
  rewrite subst-⊕₂ (⟪⌊⌋⟫-flat a) (⟪⌊⌋⟫-flat b) x | subst-⊎₂ (cohᴰ A) (cohᴰ B) y =
  Relation.Binary.PropositionalEquality.cong inj₂ (arg≡ b w)

-- an op's answer: the core's flat value against master's injected one
res-W : ∀ {B : Type} (b : SBase ∅ₖ B) (v : Val.⟦ B ⟧)
      → W ⌊ B ⌋ (subst ⟦_⟧ (sym (⟪⌊⌋⟫-flat b)) (fromF (flat b) (fromV b v))) (subst (λ S → S) (sym (cohᴰ B)) (injectᵇ b v))
res-W (b-var {i = ()} _)
res-W b-Unit  v = tt
res-W b-Void  ()
res-W b-Int   v = refl
res-W b-Float v = refl
res-W (b-* {A = A} {B = B} a b) (v₁ , v₂)
  rewrite subst-⊗⁻ (⟪⌊⌋⟫-flat a) (⟪⌊⌋⟫-flat b) (fromF (flat a) (fromV a v₁)) (fromF (flat b) (fromV b v₂))
        | subst-×⁻ (cohᴰ A) (cohᴰ B) (injectᵇ a v₁) (injectᵇ b v₂) =
  res-W a v₁ , res-W b v₂
res-W (b-+ {A = A} {B = B} a b) (inj₁ v)
  rewrite subst-⊕₁⁻ (⟪⌊⌋⟫-flat a) (⟪⌊⌋⟫-flat b) (fromF (flat a) (fromV a v))
        | subst-⊎₁⁻ (cohᴰ A) (cohᴰ B) (injectᵇ a v) =
  ⊎₁ (res-W a v)
res-W (b-+ {A = A} {B = B} a b) (inj₂ v)
  rewrite subst-⊕₂⁻ (⟪⌊⌋⟫-flat a) (⟪⌊⌋⟫-flat b) (fromF (flat b) (fromV b v))
        | subst-⊎₂⁻ (cohᴰ A) (cohᴰ B) (injectᵇ b v) =
  ⊎₂ (res-W b v)

-- one block, its values mapped on each side, embedded on each side
emb-embed : ∀ {X Y Y′ Z : Set} {R : Y → Z → Set} (g : Y′ → Y) (f : X → Y′) (h : X → Z) (m : T X)
          → (∀ x → R (g (f x)) (h x)) → emb (fmapT g (fmapT f m)) ≈[ R ] embed (Tr.fmapT h m)
_≈[_]_.blockR (emb-embed {R = R} g f h m r) = go m
  where
  go : ∀ m → BlR R (embB (fmapT g (fmapT f m))) (block (embed (Tr.fmapT h m)))
  go (ret x)      = ≈retR (r x)
  go (call o a k) = ≈callR (λ y → go (k y))
  go (halt o a)   = ≈haltR

module _ {Γ : Cx} (δ : Env Γ) (cs : CanonicalName → (A B : IRTy) → ⟦ A ⟧ᴰᴵ → T∞ ⟦ B ⟧ᴰᴵ) where

  -- the core's op, from master's argument
  op-core : ∀ {A B} (si : SigOpInfo A B) (z : Val.⟦ A ⟧) → T∞ ⟦ ⌜ flat (SigOpInfo.conB si) ⌝ ⟧
  op-core si z = emb (fmapT (fromF (flat (SigOpInfo.conB si))) (fmapT (fromV (SigOpInfo.conB si)) (sigOpT fmt ans si z)))

  -- ★ a SigOp against master's: the same contract block, on the same argument
  op≈ : ∀ {A B} (si : SigOpInfo A B) {a a′} → W ⌊ A ⌋ a a′ →
        P.ev δ (subst₂ (P.IR Γ) (sym (⟪⌊⌋⟫-flat (SigOpInfo.baseA si))) (sym (⟪⌊⌋⟫-flat (SigOpInfo.conB si)))
                                (P.SigOp (sig si))) a
          ≈[ W ⌊ B ⌋ ] evalᴰ fmt (callEnv cs ans) (M.SigOp si) a′
  op≈ {A} {B} si {a} {a′} w
    rewrite ev-subst₂ δ (⟪⌊⌋⟫-flat (SigOpInfo.baseA si)) (⟪⌊⌋⟫-flat (SigOpInfo.conB si)) (P.SigOp (sig si)) a =
    ≈-subst (sym (⟪⌊⌋⟫-flat (SigOpInfo.conB si)))
      (subst (λ z → op-core si z ≈[ _ ] evalᴰ fmt (callEnv cs ans) (M.SigOp si) a′)
             (sym (arg≡ (SigOpInfo.baseA si) w))
             (emb-embed (fromF (flat (SigOpInfo.conB si))) (fromV (SigOpInfo.conB si))
                        (λ v → subst (λ S → S) (sym (cohᴰ B)) (injectᵇ (SigOpInfo.conB si) v))
                        (sigOpT fmt ans si (forgetᵇ (SigOpInfo.baseA si) (subst (λ S → S) (cohᴰ A) a′)))
                        (res-W (SigOpInfo.conB si))))

------------------------------------------------------------------------
-- 3. ★ μ: a layer built by `In` (the core's `coh` on its code against
-- master's `coerce-functor-D` then `coerce-μ-in`), by the functor's
-- well-formedness.
------------------------------------------------------------------------

-- master's types, transported: a sum's and a pair's are their parts'
substᴰ-+₁ : ∀ {A A′ B B′ : ST.Type} (p : A ≡ A′) (q : B ≡ B′) (x : ⟦ A ⟧ᴰ)
          → subst (λ Ty → ⟦ Ty ⟧ᴰ) (cong₂ ST._+_ p q) (inj₁ x) ≡ inj₁ (subst (λ Ty → ⟦ Ty ⟧ᴰ) p x)
substᴰ-+₁ refl refl x = refl

substᴰ-+₂ : ∀ {A A′ B B′ : ST.Type} (p : A ≡ A′) (q : B ≡ B′) (y : ⟦ B ⟧ᴰ)
          → subst (λ Ty → ⟦ Ty ⟧ᴰ) (cong₂ ST._+_ p q) (inj₂ y) ≡ inj₂ (subst (λ Ty → ⟦ Ty ⟧ᴰ) q y)
substᴰ-+₂ refl refl y = refl

substᴰ-* : ∀ {A A′ B B′ : ST.Type} (p : A ≡ A′) (q : B ≡ B′) (x : ⟦ A ⟧ᴰ) (y : ⟦ B ⟧ᴰ)
         → subst (λ Ty → ⟦ Ty ⟧ᴰ) (cong₂ ST._*_ p q) (x , y) ≡ (subst (λ Ty → ⟦ Ty ⟧ᴰ) p x , subst (λ Ty → ⟦ Ty ⟧ᴰ) q y)
substᴰ-* refl refl x y = refl

-- a base constant: the core's code against master's base value
K-lay : ∀ {A} (b : IsBaseTypeI A) (X : LTy) {a a′} → W A a a′
      → WK A {⟦ X ⟧} (coh (lfK A) X (subst ⟦_⟧ (sym (⟪⟫-K b X)) a))
                     (Val.coerce-full-to-base ⌈ A ⌉ (forgetᵇ (base-⌈⌉ b) a′))
K-lay base-Unit  X w = tt
K-lay base-Void  X {a = ()}
K-lay base-Int   X w = w
K-lay base-Float X w = w
K-lay (base-Prod a b) X {a = x , y} {a′ = x′ , y′} (w₁ , w₂)
  rewrite subst-⊗⁻ (⟪⟫-K a X) (⟪⟫-K b X) x y = K-lay a X w₁ , K-lay b X w₂
K-lay (base-Sum a b) X {a = inj₁ x} {a′ = inj₁ x′} (⊎₁ w)
  rewrite subst-⊕₁⁻ (⟪⟫-K a X) (⟪⟫-K b X) x = ⊎₁ (K-lay a X w)
K-lay (base-Sum a b) X {a = inj₂ y} {a′ = inj₂ y′} (⊎₂ w)
  rewrite subst-⊕₂⁻ (⟪⟫-K a X) (⟪⟫-K b X) y = ⊎₂ (K-lay b X w)

-- a layer `In` builds, at the position's functor `G`
In-layer : ∀ {F G} (wg : WellFormedFI G) {a a′} → W (⟦ G ⟧TI (μ-type F)) a a′
         → WLμ F G (coh (lf G) (μt (lf F)) (subst ⟦_⟧ (⟪⟫-TI wg (μ-type F)) a))
                   (Val.coerce-μ-in ⌈ G ⌉F (Val.⟦μ⟧ ⌈ F ⌉F)
                      (coerce-functor-D (wf-⌈⌉ wg) ⌈ μ-type F ⌉ (subst (λ Ty → ⟦ Ty ⟧ᴰ) (⌈⟧TI-commute G (μ-type F)) a′)))
In-layer {F} (wf-K b) w = K-lay b (μt (lf F)) w
In-layer wf-Id w = w
In-layer {F} {G ⊕ᴵ H} (wf-Sum f g) {a = inj₁ x} {a′ = inj₁ x′} (⊎₁ w)
  rewrite subst-⊕₁ (⟪⟫-TI f (μ-type F)) (⟪⟫-TI g (μ-type F)) x
        | substᴰ-+₁ (⌈⟧TI-commute G (μ-type F)) (⌈⟧TI-commute H (μ-type F)) x′ = ⊎₁ (In-layer f w)
In-layer {F} {G ⊕ᴵ H} (wf-Sum f g) {a = inj₂ y} {a′ = inj₂ y′} (⊎₂ w)
  rewrite subst-⊕₂ (⟪⟫-TI f (μ-type F)) (⟪⟫-TI g (μ-type F)) y
        | substᴰ-+₂ (⌈⟧TI-commute G (μ-type F)) (⌈⟧TI-commute H (μ-type F)) y′ = ⊎₂ (In-layer g w)
In-layer {F} {G ⊗ᴵ H} (wf-Prod f g) {a = x , y} {a′ = x′ , y′} (w₁ , w₂)
  rewrite subst-⊗ (⟪⟫-TI f (μ-type F)) (⟪⟫-TI g (μ-type F)) x y
        | substᴰ-* (⌈⟧TI-commute G (μ-type F)) (⌈⟧TI-commute H (μ-type F)) x′ y′ = In-layer f w₁ , In-layer g w₂

-- a term moved along equal domains
ev-subst-dom : ∀ {Γ} (δ : Env Γ) {X X′ Y} (e : X′ ≡ X) (c : P.IR Γ X Y) (a : ⟦ X′ ⟧)
             → P.ev δ (subst (λ Z → P.IR Γ Z Y) (sym e) c) a ≡ P.ev δ c (subst ⟦_⟧ e a)
ev-subst-dom δ refl c a = refl

module _ {Γ : Cx} (δ : Env Γ) (cs : CanonicalName → (A B : IRTy) → ⟦ A ⟧ᴰᴵ → T∞ ⟦ B ⟧ᴰᴵ) where

  -- ★ `In` against master's
  In≈ : ∀ {F} (wf : WellFormedFI F) {a a′} → W (⟦ F ⟧TI (μ-type F)) a a′ →
        P.ev δ (subst (λ X → P.IR Γ X ⟪ μ-type F ⟫) (sym (⟪⟫-TI wf (μ-type F))) (P.In (lf F))) a
          ≈[ W (μ-type F) ] evalᴰ fmt (callEnv cs ans) (M.In wf) a′
  In≈ {F} wf {a} w rewrite ev-subst-dom δ (⟪⟫-TI wf (μ-type F)) (P.In (lf F)) a = ret≈R (wmu (In-layer wf w))

------------------------------------------------------------------------
-- 4. ★ μ, the other way: a layer `out-μ` exposes (the core's `coh⁻¹`
-- against master's `coerce-μ-out` then `coerce-functor⁻¹-D`).
------------------------------------------------------------------------

substᴰ-+₁⁻ : ∀ {A A′ B B′ : ST.Type} (p : A ≡ A′) (q : B ≡ B′) (x : ⟦ A′ ⟧ᴰ)
           → subst (λ Ty → ⟦ Ty ⟧ᴰ) (sym (cong₂ ST._+_ p q)) (inj₁ x) ≡ inj₁ (subst (λ Ty → ⟦ Ty ⟧ᴰ) (sym p) x)
substᴰ-+₁⁻ refl refl x = refl

substᴰ-+₂⁻ : ∀ {A A′ B B′ : ST.Type} (p : A ≡ A′) (q : B ≡ B′) (y : ⟦ B′ ⟧ᴰ)
           → subst (λ Ty → ⟦ Ty ⟧ᴰ) (sym (cong₂ ST._+_ p q)) (inj₂ y) ≡ inj₂ (subst (λ Ty → ⟦ Ty ⟧ᴰ) (sym q) y)
substᴰ-+₂⁻ refl refl y = refl

substᴰ-*⁻ : ∀ {A A′ B B′ : ST.Type} (p : A ≡ A′) (q : B ≡ B′) (x : ⟦ A′ ⟧ᴰ) (y : ⟦ B′ ⟧ᴰ)
          → subst (λ Ty → ⟦ Ty ⟧ᴰ) (sym (cong₂ ST._*_ p q)) (x , y)
            ≡ (subst (λ Ty → ⟦ Ty ⟧ᴰ) (sym p) x , subst (λ Ty → ⟦ Ty ⟧ᴰ) (sym q) y)
substᴰ-*⁻ refl refl x y = refl

subst-sym² : ∀ {X X′ : LTy} (e : X ≡ X′) (x : ⟦ X ⟧) → subst ⟦_⟧ (sym (sym e)) x ≡ subst ⟦_⟧ e x
subst-sym² refl x = refl

-- a base constant, back: master's base value against the core's code
K-lay⁻ : ∀ {A} (b : IsBaseTypeI A) (X : LTy) {w w′} → WK A {⟦ X ⟧} w w′
       → W A (subst ⟦_⟧ (⟪⟫-K b X) (coh⁻¹ (lfK A) X w))
             (injectᵇ (base-⌈⌉ b) (Val.coerce-base-to-full (base-⌈⌉ b) w′))
K-lay⁻ base-Unit  X w = tt
K-lay⁻ base-Void  X {w = ()}
K-lay⁻ base-Int   X w = w
K-lay⁻ base-Float X w = w
K-lay⁻ (base-Prod {A₁} {A₂} a b) X {w = x , y} {w′ = x′ , y′} (w₁ , w₂) =
  subst (λ z → W (A₁ * A₂) z (injectᵇ (base-⌈⌉ a) (Val.coerce-base-to-full (base-⌈⌉ a) x′)
                              , injectᵇ (base-⌈⌉ b) (Val.coerce-base-to-full (base-⌈⌉ b) y′)))
        (sym (subst-⊗ (⟪⟫-K a X) (⟪⟫-K b X) (coh⁻¹ (lfK A₁) X x) (coh⁻¹ (lfK A₂) X y)))
        (K-lay⁻ a X w₁ , K-lay⁻ b X w₂)
K-lay⁻ (base-Sum {A₁} {A₂} a b) X {w = inj₁ x} {w′ = inj₁ x′} (⊎₁ w) =
  subst (λ z → W (A₁ + A₂) z (inj₁ (injectᵇ (base-⌈⌉ a) (Val.coerce-base-to-full (base-⌈⌉ a) x′))))
        (sym (subst-⊕₁ (⟪⟫-K a X) (⟪⟫-K b X) (coh⁻¹ (lfK A₁) X x)))
        (⊎₁ (K-lay⁻ a X w))
K-lay⁻ (base-Sum {A₁} {A₂} a b) X {w = inj₂ y} {w′ = inj₂ y′} (⊎₂ w) =
  subst (λ z → W (A₁ + A₂) z (inj₂ (injectᵇ (base-⌈⌉ b) (Val.coerce-base-to-full (base-⌈⌉ b) y′))))
        (sym (subst-⊕₂ (⟪⟫-K a X) (⟪⟫-K b X) (coh⁻¹ (lfK A₂) X y)))
        (⊎₂ (K-lay⁻ b X w))

-- a layer `out-μ` exposes, at the position's functor `G`
Out-layer : ∀ {F G} (wg : WellFormedFI G) {w w′} → WLμ F G w w′
          → W (⟦ G ⟧TI (μ-type F))
              (subst ⟦_⟧ (sym (⟪⟫-TI wg (μ-type F))) (coh⁻¹ (lf G) (μt (lf F)) w))
              (subst (λ Ty → ⟦ Ty ⟧ᴰ) (sym (⌈⟧TI-commute G (μ-type F)))
                 (coerce-functor⁻¹-D (wf-⌈⌉ wg) ⌈ μ-type F ⌉ (Val.coerce-μ-out (wf-⌈⌉ wg) (Val.⟦μ⟧ ⌈ F ⌉F) w′)))
Out-layer {F} {K A} (wf-K b) {w} {w′} r =
  subst (λ z → W A z (injectᵇ (base-⌈⌉ b) (Val.coerce-base-to-full (base-⌈⌉ b) w′)))
        (sym (subst-sym² (⟪⟫-K b (μt (lf F))) (coh⁻¹ (lfK A) (μt (lf F)) w)))
        (K-lay⁻ b (μt (lf F)) r)
Out-layer wf-Id r = r
Out-layer {F} {G ⊕ᴵ H} (wf-Sum f g) {w = inj₁ x} {w′ = inj₁ x′} (⊎₁ r)
  rewrite subst-⊕₁⁻ (⟪⟫-TI f (μ-type F)) (⟪⟫-TI g (μ-type F)) (coh⁻¹ (lf G) (μt (lf F)) x)
        | substᴰ-+₁⁻ (⌈⟧TI-commute G (μ-type F)) (⌈⟧TI-commute H (μ-type F))
                     (coerce-functor⁻¹-D (wf-⌈⌉ f) ⌈ μ-type F ⌉ (Val.coerce-μ-out (wf-⌈⌉ f) (Val.⟦μ⟧ ⌈ F ⌉F) x′)) =
  ⊎₁ (Out-layer f r)
Out-layer {F} {G ⊕ᴵ H} (wf-Sum f g) {w = inj₂ y} {w′ = inj₂ y′} (⊎₂ r)
  rewrite subst-⊕₂⁻ (⟪⟫-TI f (μ-type F)) (⟪⟫-TI g (μ-type F)) (coh⁻¹ (lf H) (μt (lf F)) y)
        | substᴰ-+₂⁻ (⌈⟧TI-commute G (μ-type F)) (⌈⟧TI-commute H (μ-type F))
                     (coerce-functor⁻¹-D (wf-⌈⌉ g) ⌈ μ-type F ⌉ (Val.coerce-μ-out (wf-⌈⌉ g) (Val.⟦μ⟧ ⌈ F ⌉F) y′)) =
  ⊎₂ (Out-layer g r)
Out-layer {F} {G ⊗ᴵ H} (wf-Prod f g) {w = x , y} {w′ = x′ , y′} (r₁ , r₂)
  rewrite subst-⊗⁻ (⟪⟫-TI f (μ-type F)) (⟪⟫-TI g (μ-type F)) (coh⁻¹ (lf G) (μt (lf F)) x) (coh⁻¹ (lf H) (μt (lf F)) y)
        | substᴰ-*⁻ (⌈⟧TI-commute G (μ-type F)) (⌈⟧TI-commute H (μ-type F))
                    (coerce-functor⁻¹-D (wf-⌈⌉ f) ⌈ μ-type F ⌉ (Val.coerce-μ-out (wf-⌈⌉ f) (Val.⟦μ⟧ ⌈ F ⌉F) x′))
                    (coerce-functor⁻¹-D (wf-⌈⌉ g) ⌈ μ-type F ⌉ (Val.coerce-μ-out (wf-⌈⌉ g) (Val.⟦μ⟧ ⌈ F ⌉F) y′)) =
  Out-layer f r₁ , Out-layer g r₂

-- a term moved along equal codomains
ev-subst-cod : ∀ {Γ} (δ : Env Γ) {X Y Y′} (e : Y′ ≡ Y) (c : P.IR Γ X Y) (a : ⟦ X ⟧)
             → P.ev δ (subst (λ Z → P.IR Γ X Z) (sym e) c) a ≡ subst (λ Z → T∞ ⟦ Z ⟧) (sym e) (P.ev δ c a)
ev-subst-cod δ refl c a = refl

module _ {Γ : Cx} (δ : Env Γ) (cs : CanonicalName → (A B : IRTy) → ⟦ A ⟧ᴰᴵ → T∞ ⟦ B ⟧ᴰᴵ) where

  -- ★ `out-μ` against master's
  out≈ : ∀ {F} (wf : WellFormedFI F) {a a′} → W (μ-type F) a a′ →
         P.ev δ (subst (λ X → P.IR Γ ⟪ μ-type F ⟫ X) (sym (⟪⟫-TI wf (μ-type F))) (P.out-μ (lf F))) a
           ≈[ W (⟦ F ⟧TI (μ-type F)) ] evalᴰ fmt (callEnv cs ans) (M.out-μ wf) a′
  out≈ {F} wf {inμ w} (wmu r) rewrite ev-subst-cod δ (⟪⟫-TI wf (μ-type F)) (P.out-μ (lf F)) (inμ w) =
    ≈-subst (sym (⟪⟫-TI wf (μ-type F))) (ret≈R (Out-layer wf r))

------------------------------------------------------------------------
-- 5. ★ ν: a layer `in-ν` takes and `Out` gives (master's ν coercions are its
-- μ ones), and an observation mapped on each side.
------------------------------------------------------------------------

Inν-layer : ∀ {F G} (wg : WellFormedFI G) {a a′} → W (⟦ G ⟧TI (ν-type F)) a a′
          → WLν F G (coh (lf G) (Nu (lf F)) (subst ⟦_⟧ (⟪⟫-TI wg (ν-type F)) a))
                    (Val.coerce-μ-in ⌈ G ⌉F ⟦ ⌈ ν-type F ⌉ ⟧ᴰ
                       (coerce-functor-D (wf-⌈⌉ wg) ⌈ ν-type F ⌉ (subst (λ Ty → ⟦ Ty ⟧ᴰ) (⌈⟧TI-commute G (ν-type F)) a′)))
Inν-layer {F} (wf-K b) w = K-lay b (Nu (lf F)) w
Inν-layer wf-Id w = w
Inν-layer {F} {G ⊕ᴵ H} (wf-Sum f g) {a = inj₁ x} {a′ = inj₁ x′} (⊎₁ w)
  rewrite subst-⊕₁ (⟪⟫-TI f (ν-type F)) (⟪⟫-TI g (ν-type F)) x
        | substᴰ-+₁ (⌈⟧TI-commute G (ν-type F)) (⌈⟧TI-commute H (ν-type F)) x′ = ⊎₁ (Inν-layer f w)
Inν-layer {F} {G ⊕ᴵ H} (wf-Sum f g) {a = inj₂ y} {a′ = inj₂ y′} (⊎₂ w)
  rewrite subst-⊕₂ (⟪⟫-TI f (ν-type F)) (⟪⟫-TI g (ν-type F)) y
        | substᴰ-+₂ (⌈⟧TI-commute G (ν-type F)) (⌈⟧TI-commute H (ν-type F)) y′ = ⊎₂ (Inν-layer g w)
Inν-layer {F} {G ⊗ᴵ H} (wf-Prod f g) {a = x , y} {a′ = x′ , y′} (w₁ , w₂)
  rewrite subst-⊗ (⟪⟫-TI f (ν-type F)) (⟪⟫-TI g (ν-type F)) x y
        | substᴰ-* (⌈⟧TI-commute G (ν-type F)) (⌈⟧TI-commute H (ν-type F)) x′ y′ = Inν-layer f w₁ , Inν-layer g w₂

Outν-layer : ∀ {F G} (wg : WellFormedFI G) {w w′} → WLν F G w w′
           → W (⟦ G ⟧TI (ν-type F))
               (subst ⟦_⟧ (sym (⟪⟫-TI wg (ν-type F))) (coh⁻¹ (lf G) (Nu (lf F)) w))
               (subst (λ Ty → ⟦ Ty ⟧ᴰ) (sym (⌈⟧TI-commute G (ν-type F)))
                  (coerce-functor⁻¹-D (wf-⌈⌉ wg) ⌈ ν-type F ⌉ (Val.coerce-μ-out (wf-⌈⌉ wg) ⟦ ⌈ ν-type F ⌉ ⟧ᴰ w′)))
Outν-layer {F} {K A} (wf-K b) {w} {w′} r =
  subst (λ z → W A z (injectᵇ (base-⌈⌉ b) (Val.coerce-base-to-full (base-⌈⌉ b) w′)))
        (sym (subst-sym² (⟪⟫-K b (Nu (lf F))) (coh⁻¹ (lfK A) (Nu (lf F)) w)))
        (K-lay⁻ b (Nu (lf F)) r)
Outν-layer wf-Id r = r
Outν-layer {F} {G ⊕ᴵ H} (wf-Sum f g) {w = inj₁ x} {w′ = inj₁ x′} (⊎₁ r)
  rewrite subst-⊕₁⁻ (⟪⟫-TI f (ν-type F)) (⟪⟫-TI g (ν-type F)) (coh⁻¹ (lf G) (Nu (lf F)) x)
        | substᴰ-+₁⁻ (⌈⟧TI-commute G (ν-type F)) (⌈⟧TI-commute H (ν-type F))
                     (coerce-functor⁻¹-D (wf-⌈⌉ f) ⌈ ν-type F ⌉ (Val.coerce-μ-out (wf-⌈⌉ f) ⟦ ⌈ ν-type F ⌉ ⟧ᴰ x′)) =
  ⊎₁ (Outν-layer f r)
Outν-layer {F} {G ⊕ᴵ H} (wf-Sum f g) {w = inj₂ y} {w′ = inj₂ y′} (⊎₂ r)
  rewrite subst-⊕₂⁻ (⟪⟫-TI f (ν-type F)) (⟪⟫-TI g (ν-type F)) (coh⁻¹ (lf H) (Nu (lf F)) y)
        | substᴰ-+₂⁻ (⌈⟧TI-commute G (ν-type F)) (⌈⟧TI-commute H (ν-type F))
                     (coerce-functor⁻¹-D (wf-⌈⌉ g) ⌈ ν-type F ⌉ (Val.coerce-μ-out (wf-⌈⌉ g) ⟦ ⌈ ν-type F ⌉ ⟧ᴰ y′)) =
  ⊎₂ (Outν-layer g r)
Outν-layer {F} {G ⊗ᴵ H} (wf-Prod f g) {w = x , y} {w′ = x′ , y′} (r₁ , r₂)
  rewrite subst-⊗⁻ (⟪⟫-TI f (ν-type F)) (⟪⟫-TI g (ν-type F)) (coh⁻¹ (lf G) (Nu (lf F)) x) (coh⁻¹ (lf H) (Nu (lf F)) y)
        | substᴰ-*⁻ (⌈⟧TI-commute G (ν-type F)) (⌈⟧TI-commute H (ν-type F))
                    (coerce-functor⁻¹-D (wf-⌈⌉ f) ⌈ ν-type F ⌉ (Val.coerce-μ-out (wf-⌈⌉ f) ⟦ ⌈ ν-type F ⌉ ⟧ᴰ x′))
                    (coerce-functor⁻¹-D (wf-⌈⌉ g) ⌈ ν-type F ⌉ (Val.coerce-μ-out (wf-⌈⌉ g) ⟦ ⌈ ν-type F ⌉ ⟧ᴰ y′)) =
  Outν-layer f r₁ , Outν-layer g r₂

-- a block related to a computation, each mapped
embfmap≈ : ∀ {X X′ Y Y′ : Set} {S : X → X′ → Set} {R : Y → Y′ → Set} {f : X → Y} {g : X′ → Y′}
           (m : T X) {m′ : T∞ X′} → emb m ≈[ S ] m′ → (∀ {x y} → S x y → R (f x) (g y))
         → emb (fmapT f m) ≈[ R ] fmap∞ g m′
_≈[_]_.blockR (embfmap≈ {S = S} {R} {f} {g} m {m′} p r) = go m (_≈[_]_.blockR p)
  where
  go : ∀ (m : T _) {b′} → BlR S (embB m) b′ → BlR R (embB (fmapT f m)) (Once.IR.Semantics.Iterative.bindBlock b′ (λ y → Once.IR.Semantics.Iterative.return∞ (g y)))
  go (ret x)      (≈retR s)  = ≈retR (r s)
  go (call o a k) (≈callR h) = ≈callR (λ z → go (k z) (h z))
  go (halt o a)   ≈haltR     = ≈haltR

-- a ν built from a layer: its one observation is the layer
inν-W : ∀ {F l l′} → WLν F F l l′ → WNu F (P.inν l) (in-νᴵ l′)
_≈[_]_.blockR (wout (inν-W r)) = ≈retR r

module _ {Γ : Cx} (δ : Env Γ) (cs : CanonicalName → (A B : IRTy) → ⟦ A ⟧ᴰᴵ → T∞ ⟦ B ⟧ᴰᴵ) where

  -- ★ `Out` against master's
  Out≈ : ∀ {F} (wf : WellFormedFI F) {a a′} → W (ν-type F) a a′ →
         P.ev δ (subst (λ X → P.IR Γ ⟪ ν-type F ⟫ X) (sym (⟪⟫-TI wf (ν-type F))) (P.Out (lf F))) a
           ≈[ W (⟦ F ⟧TI (ν-type F)) ] evalᴰ fmt (callEnv cs ans) (M.Out wf) a′
  Out≈ {F} wf {v} w rewrite ev-subst-cod δ (⟪⟫-TI wf (ν-type F)) (P.Out (lf F)) v =
    ≈-subst (sym (⟪⟫-TI wf (ν-type F))) (embfmap≈ (outν v) (wout w) (Outν-layer wf))

  -- ★ `in-ν` against master's
  inν≈ : ∀ {F} (wf : WellFormedFI F) {a a′} → W (⟦ F ⟧TI (ν-type F)) a a′ →
         P.ev δ (subst (λ X → P.IR Γ X ⟪ ν-type F ⟫) (sym (⟪⟫-TI wf (ν-type F))) (P.in-ν (lf F))) a
           ≈[ W (ν-type F) ] evalᴰ fmt (callEnv cs ans) (M.in-ν wf) a′
  inν≈ {F} wf {a} w rewrite ev-subst-dom δ (⟪⟫-TI wf (ν-type F)) (P.in-ν (lf F)) a = ret≈R (inν-W (Inν-layer wf w))

------------------------------------------------------------------------
-- 6. ★ THE FOLD: the core's `cataC`/`travC` against master's `sem-cata`
-- with `seqF∞` (children left to right, then the algebra), by induction on
-- the μ value.
------------------------------------------------------------------------

-- a base constant's code against master's FULL value (a fold's layer)
WKf : ∀ (B : IRTy) {X} → FS (lfK B) X → Val.⟦ ⌈ B ⌉ ⟧ → Set
WKf Unit         _ _               = ⊤
WKf Void         () _
WKf Int          x x′              = x ≡ x′
WKf Float        x x′              = x ≡ x′
WKf (A * B)      (x , y) (x′ , y′) = WKf A x x′ × WKf B y y′
WKf (A + B)      x x′              = Pointwise (WKf A) (WKf B) x x′
WKf (μ-type G)   _ _               = ⊥
WKf (_ ⇛[ _ ] _) () _
WKf (ν-type _)   () _

-- a layer of results: the core's against master's
WLA : ∀ (A : IRTy) (G : IRFunctor) → FS (lf G) ⟦ ⟪ A ⟫ ⟧ → Val.⟦ ⌈ G ⌉F ⟧F ⟦ ⌈ A ⌉ ⟧ᴰ → Set
WLA A (K B)     x x′ = WKf B x x′
WLA A Id        x x′ = W A x x′
WLA A (G ⊕ᴵ H)  x x′ = Pointwise (WLA A G) (WLA A H) x x′
WLA A (G ⊗ᴵ H)  (x , y) (x′ , y′) = WLA A G x x′ × WLA A H y y′

-- a computation given by a block equal to its own
≈R-blkʳ : ∀ {X Y} {R : X → Y → Set} {m : T∞ X} {m₁ m₂ : T∞ Y} → block m₂ ≡ block m₁ → m ≈[ R ] m₁ → m ≈[ R ] m₂
_≈[_]_.blockR (≈R-blkʳ {R = R} {m} e p) = subst (BlR R (block m)) (sym e) (_≈[_]_.blockR p)

-- a base constant, base to full
K-full : ∀ {B} (b : IsBaseTypeI B) {X} {y y′} → WK B {X} y y′ → WKf B y (Val.coerce-base-to-full (base-⌈⌉ b) y′)
K-full base-Unit  w = tt
K-full base-Void  {y = ()}
K-full base-Int   w = w
K-full base-Float w = w
K-full (base-Prod a b) {y = _ , _} {y′ = _ , _} (w₁ , w₂) = K-full a w₁ , K-full b w₂
K-full (base-Sum a b) {y = inj₁ _} {y′ = inj₁ _} (⊎₁ w) = ⊎₁ (K-full a w)
K-full (base-Sum a b) {y = inj₂ _} {y′ = inj₂ _} (⊎₂ w) = ⊎₂ (K-full b w)

-- a base constant of a fold's layer, back into the relation by type
K-back : ∀ {B} (b : IsBaseTypeI B) (X : LTy) {w w′} → WKf B {⟦ X ⟧} w w′
       → W B (subst ⟦_⟧ (⟪⟫-K b X) (coh⁻¹ (lfK B) X w)) (injectᵇ (base-⌈⌉ b) w′)
K-back base-Unit  X w = tt
K-back base-Void  X {w = ()}
K-back base-Int   X w = w
K-back base-Float X w = w
K-back (base-Prod {A₁} {A₂} a b) X {w = x , y} {w′ = x′ , y′} (w₁ , w₂) =
  subst (λ z → W (A₁ * A₂) z (injectᵇ (base-⌈⌉ a) x′ , injectᵇ (base-⌈⌉ b) y′))
        (sym (subst-⊗ (⟪⟫-K a X) (⟪⟫-K b X) (coh⁻¹ (lfK A₁) X x) (coh⁻¹ (lfK A₂) X y)))
        (K-back a X w₁ , K-back b X w₂)
K-back (base-Sum {A₁} {A₂} a b) X {w = inj₁ x} {w′ = inj₁ x′} (⊎₁ w) =
  subst (λ z → W (A₁ + A₂) z (inj₁ (injectᵇ (base-⌈⌉ a) x′)))
        (sym (subst-⊕₁ (⟪⟫-K a X) (⟪⟫-K b X) (coh⁻¹ (lfK A₁) X x)))
        (⊎₁ (K-back a X w))
K-back (base-Sum {A₁} {A₂} a b) X {w = inj₂ y} {w′ = inj₂ y′} (⊎₂ w) =
  subst (λ z → W (A₁ + A₂) z (inj₂ (injectᵇ (base-⌈⌉ b) y′)))
        (sym (subst-⊕₂ (⟪⟫-K a X) (⟪⟫-K b X) (coh⁻¹ (lfK A₂) X y)))
        (⊎₂ (K-back b X w))

-- a layer of results, back into the relation by type (the algebra's input)
A-back : ∀ {A G} (wg : WellFormedFI G) {u u′} → WLA A G u u′
       → W (⟦ G ⟧TI A) (subst ⟦_⟧ (sym (⟪⟫-TI wg A)) (coh⁻¹ (lf G) ⟪ A ⟫ u))
                       (subst (λ Ty → ⟦ Ty ⟧ᴰ) (sym (⌈⟧TI-commute G A)) (coerce-functor⁻¹-D (wf-⌈⌉ wg) ⌈ A ⌉ u′))
A-back {A} {K B} (wf-K b) {u} {u′} r =
  subst (λ z → W B z (injectᵇ (base-⌈⌉ b) u′))
        (sym (subst-sym² (⟪⟫-K b ⟪ A ⟫) (coh⁻¹ (lfK B) ⟪ A ⟫ u)))
        (K-back b ⟪ A ⟫ r)
A-back wf-Id r = r
A-back {A} {G ⊕ᴵ H} (wf-Sum f g) {u = inj₁ x} {u′ = inj₁ x′} (⊎₁ r)
  rewrite subst-⊕₁⁻ (⟪⟫-TI f A) (⟪⟫-TI g A) (coh⁻¹ (lf G) ⟪ A ⟫ x)
        | substᴰ-+₁⁻ (⌈⟧TI-commute G A) (⌈⟧TI-commute H A) (coerce-functor⁻¹-D (wf-⌈⌉ f) ⌈ A ⌉ x′) =
  ⊎₁ (A-back f r)
A-back {A} {G ⊕ᴵ H} (wf-Sum f g) {u = inj₂ y} {u′ = inj₂ y′} (⊎₂ r)
  rewrite subst-⊕₂⁻ (⟪⟫-TI f A) (⟪⟫-TI g A) (coh⁻¹ (lf H) ⟪ A ⟫ y)
        | substᴰ-+₂⁻ (⌈⟧TI-commute G A) (⌈⟧TI-commute H A) (coerce-functor⁻¹-D (wf-⌈⌉ g) ⌈ A ⌉ y′) =
  ⊎₂ (A-back g r)
A-back {A} {G ⊗ᴵ H} (wf-Prod f g) {u = x , y} {u′ = x′ , y′} (r₁ , r₂)
  rewrite subst-⊗⁻ (⟪⟫-TI f A) (⟪⟫-TI g A) (coh⁻¹ (lf G) ⟪ A ⟫ x) (coh⁻¹ (lf H) ⟪ A ⟫ y)
        | substᴰ-*⁻ (⌈⟧TI-commute G A) (⌈⟧TI-commute H A)
                    (coerce-functor⁻¹-D (wf-⌈⌉ f) ⌈ A ⌉ x′) (coerce-functor⁻¹-D (wf-⌈⌉ g) ⌈ A ⌉ y′) =
  A-back f r₁ , A-back g r₂

-- the algebra's term moved along its layer's types
ev-subst-alg : ∀ {Γ} (δ : Env Γ) {E X X′ A} (e : X ≡ X′) (c : P.IR Γ (E ⊗t X) A) (x : ⟦ E ⟧) (y : ⟦ X′ ⟧)
             → P.ev δ (subst (λ Z → P.IR Γ (E ⊗t Z) A) e c) (x , y) ≡ P.ev δ c (x , subst ⟦_⟧ (sym e) y)
ev-subst-alg δ refl c x y = refl

module _ {Γ : Cx} (δ : Env Γ) (cs : CanonicalName → (A B : IRTy) → ⟦ A ⟧ᴰᴵ → T∞ ⟦ B ⟧ᴰᴵ) where

  module Fold {F} (wf : WellFormedFI F) {E A} (alg : M.IR (E * ⟦ F ⟧TI A) A) (a′ : P.IR Γ (⟪ E ⟫ ⊗t ⟪ ⟦ F ⟧TI A ⟫) ⟪ A ⟫)
              (ih : ∀ {x x′} → W (E * ⟦ F ⟧TI A) x x′ → P.ev δ a′ x ≈[ W A ] evalᴰ fmt (callEnv cs ans) alg x′)
              (e : ⟦ ⟪ E ⟫ ⟧) (e′ : ⟦ E ⟧ᴰᴵ) (we : W E e e′) where

    a″ : P.IR Γ (⟪ E ⟫ ⊗t LF∙ (lf F) ⟪ A ⟫) ⟪ A ⟫
    a″ = subst (λ X → P.IR Γ (⟪ E ⟫ ⊗t X) ⟪ A ⟫) (⟪⟫-TI wf A) a′

    algC : FS (lf F) ⟦ ⟪ A ⟫ ⟧ → T∞ ⟦ ⟪ A ⟫ ⟧
    algC y = P.ev δ a″ (e , coh⁻¹ (lf F) _ y)

    algM : Val.⟦ ⌈ F ⌉F ⟧F (T∞ ⟦ ⌈ A ⌉ ⟧ᴰ) → T∞ ⟦ ⌈ A ⌉ ⟧ᴰ
    algM = cata-ev-algᴰ fmt (callEnv cs ans) wf alg e′

    alg″ : ⟦ SF F ⟧SF (T∞ ⟦ ⌈ A ⌉ ⟧ᴰ) → T∞ ⟦ ⌈ A ⌉ ⟧ᴰ
    alg″ x = algM (Val.coerce-μ-out (wf-⌈⌉ wf) _ x)

    -- the algebra, on related layers
    alg≈ : ∀ {u u′} → WLA A F u u′ → algC u ≈[ W A ]
             evalᴰ fmt (callEnv cs ans) alg (e′ , subst (λ Ty → ⟦ Ty ⟧ᴰ) (sym (⌈⟧TI-commute F A))
                                                     (coerce-functor⁻¹-D (wf-⌈⌉ wf) ⌈ A ⌉ u′))
    alg≈ {u} r rewrite ev-subst-alg δ (⟪⟫-TI wf A) a′ e (coh⁻¹ (lf F) ⟪ A ⟫ u) = ih (we , A-back wf r)


    -- a base constant's traversal: its value
    travK : ∀ {B} (b : IsBaseTypeI B) {y y′} → WK B y y′
          → travC δ (lf F) (lfK B) algC y ≈[ WKf B ] return∞ (Val.coerce-base-to-full (base-⌈⌉ b) y′)
    travK base-Unit  w = ret≈R tt
    travK base-Void  {y = ()}
    travK base-Int   w = ret≈R w
    travK base-Float w = ret≈R w
    travK (base-Prod a b) {y = _ , _} {y′ = _ , _} (w₁ , w₂) =
      ≈R-blkʳ refl (>>=-congR (travK a w₁) (λ r → fmap-congR (travK b w₂) (λ r′ → r , r′)))
    travK (base-Sum a b) {y = inj₁ _} {y′ = inj₁ _} (⊎₁ w) = ≈R-blkʳ refl (fmap-congR (travK a w) ⊎₁)
    travK (base-Sum a b) {y = inj₂ _} {y′ = inj₂ _} (⊎₂ w) = ≈R-blkʳ refl (fmap-congR (travK b w) ⊎₂)

    mutual
      -- ★ the fold, by induction on the μ value
      cata-rel : ∀ {x x′} → WMu F x x′ → cataC δ (lf F) algC x ≈[ W A ] Pol.cataS alg″ x′
      cata-rel (wmu r) = >>=-congR (trav-rel wf r) alg≈

      -- a layer's children, left to right
      trav-rel : ∀ {G} (wg : WellFormedFI G) {w w′} → WLμ F G w w′
               → travC δ (lf F) (lf G) algC w
                   ≈[ WLA A G ] seqF∞ ⌈ G ⌉F (Val.coerce-μ-out (wf-⌈⌉ wg) _ (Pol.sfmapCata (SF G) alg″ w′))
      trav-rel (wf-K b) r = travK b r
      trav-rel wf-Id r = cata-rel r
      trav-rel (wf-Sum f g) {w = inj₁ _} {w′ = inj₁ _} (⊎₁ r) = fmap-congR (trav-rel f r) ⊎₁
      trav-rel (wf-Sum f g) {w = inj₂ _} {w′ = inj₂ _} (⊎₂ r) = fmap-congR (trav-rel g r) ⊎₂
      trav-rel (wf-Prod f g) {w = _ , _} {w′ = _ , _} (r₁ , r₂) =
        >>=-congR (trav-rel f r₁) (λ r → >>=-congR (trav-rel g r₂) (λ r′ → ret≈R (r , r′)))

  -- ★ `Cata` against master's
  cata≈ : ∀ {F} (wf : WellFormedFI F) {E A} (alg : M.IR (E * ⟦ F ⟧TI A) A) a′ →
          (∀ {x x′} → W (E * ⟦ F ⟧TI A) x x′ → P.ev δ a′ x ≈[ W A ] evalᴰ fmt (callEnv cs ans) alg x′) →
          ∀ {a b} → W (E * μ-type F) a b →
          P.ev δ (P.Cata (lf F) (subst (λ X → P.IR Γ (⟪ E ⟫ ⊗t X) ⟪ A ⟫) (⟪⟫-TI wf A) a′)) a
            ≈[ W A ] evalᴰ fmt (callEnv cs ans) (M.Cata wf alg) b
  cata≈ wf alg a′ ih {e , x} {e′ , x′} (we , wx) = Fold.cata-rel wf alg a′ ih e e′ we wx

------------------------------------------------------------------------
-- 7. ★ THE UNFOLD: the core's `anaN` against master's `anaFᴵ`, by guarded
-- corecursion (each observation: the coalgebra's block against master's
-- run, its seeds unfolded again).
------------------------------------------------------------------------

-- a layer of seeds: the core's against master's
WLS : ∀ (A : IRTy) (G : IRFunctor) → FS (lf G) ⟦ ⟪ A ⟫ ⟧ → ⟦ SF G ⟧SF ⟦ ⌈ A ⌉ ⟧ᴰ → Set
WLS A (K B)     x x′ = WK B x x′
WLS A Id        x x′ = W A x x′
WLS A (G ⊕ᴵ H)  x x′ = Pointwise (WLS A G) (WLS A H) x x′
WLS A (G ⊗ᴵ H)  (x , y) (x′ , y′) = WLS A G x x′ × WLS A H y y′

-- a layer of seeds a coalgebra gives, at the position's functor `G`
Seed-layer : ∀ {A G} (wg : WellFormedFI G) {a a′} → W (⟦ G ⟧TI A) a a′
           → WLS A G (coh (lf G) ⟪ A ⟫ (subst ⟦_⟧ (⟪⟫-TI wg A) a))
                     (Val.coerce-μ-in ⌈ G ⌉F ⟦ ⌈ A ⌉ ⟧ᴰ
                        (coerce-functor-D (wf-⌈⌉ wg) ⌈ A ⌉ (subst (λ Ty → ⟦ Ty ⟧ᴰ) (⌈⟧TI-commute G A) a′)))
Seed-layer {A} (wf-K b) w = K-lay b ⟪ A ⟫ w
Seed-layer wf-Id w = w
Seed-layer {A} {G ⊕ᴵ H} (wf-Sum f g) {a = inj₁ x} {a′ = inj₁ x′} (⊎₁ w)
  rewrite subst-⊕₁ (⟪⟫-TI f A) (⟪⟫-TI g A) x
        | substᴰ-+₁ (⌈⟧TI-commute G A) (⌈⟧TI-commute H A) x′ = ⊎₁ (Seed-layer f w)
Seed-layer {A} {G ⊕ᴵ H} (wf-Sum f g) {a = inj₂ y} {a′ = inj₂ y′} (⊎₂ w)
  rewrite subst-⊕₂ (⟪⟫-TI f A) (⟪⟫-TI g A) y
        | substᴰ-+₂ (⌈⟧TI-commute G A) (⌈⟧TI-commute H A) y′ = ⊎₂ (Seed-layer g w)
Seed-layer {A} {G ⊗ᴵ H} (wf-Prod f g) {a = x , y} {a′ = x′ , y′} (w₁ , w₂)
  rewrite subst-⊗ (⟪⟫-TI f A) (⟪⟫-TI g A) x y
        | substᴰ-* (⌈⟧TI-commute G A) (⌈⟧TI-commute H A) x′ y′ = Seed-layer f w₁ , Seed-layer g w₂

-- a base constant's map over the ν: its value
K-map : ∀ {F B} (b : IsBaseTypeI B) {X} {c : X → T (FS (lf F) X)} {x x′} → WK B x x′
      → WK B {Nuᵐ (lf F)} (mapN (lf F) (lfK B) c x) x′
K-map base-Unit  w = tt
K-map base-Void  {x = ()}
K-map base-Int   w = w
K-map base-Float w = w
K-map {F} (base-Prod a b) {x = _ , _} {x′ = _ , _} (w₁ , w₂) = K-map {F} a w₁ , K-map {F} b w₂
K-map {F} (base-Sum a b) {x = inj₁ _} {x′ = inj₁ _} (⊎₁ w) = ⊎₁ (K-map {F} a w)
K-map {F} (base-Sum a b) {x = inj₂ _} {x′ = inj₂ _} (⊎₂ w) = ⊎₂ (K-map {F} b w)

-- a relation with a map on the right side only
mutual
  fmapʳ : ∀ {X Y Z} {R : X → Z → Set} {f : Y → Z} {m : T∞ X} {m′ : T∞ Y}
        → m ≈[ (λ x y → R x (f y)) ] m′ → m ≈[ R ] fmap∞ f m′
  _≈[_]_.blockR (fmapʳ p) = fmapʳ-B (_≈[_]_.blockR p)

  fmapʳ-B : ∀ {X Y Z} {R : X → Z → Set} {f : Y → Z} {b : T (X ⊎ T∞ X)} {b′ : T (Y ⊎ T∞ Y)}
          → BlR (λ x y → R x (f y)) b b′ → BlR R b (Once.IR.Semantics.Iterative.bindBlock b′ (λ y → Once.IR.Semantics.Iterative.return∞ (f y)))
  fmapʳ-B (≈retR r)  = ≈retR r
  fmapʳ-B (≈stepR p) = ≈stepR (fmapʳ p)
  fmapʳ-B (≈callR h) = ≈callR (λ y → fmapʳ-B (h y))
  fmapʳ-B ≈haltR     = ≈haltR

-- a computation transported along its codomain, related with its result moved back
≈-transport : ∀ {Y Y′ Z} {R : ⟦ Y ⟧ → Z → Set} (e : Y ≡ Y′) {m : T∞ ⟦ Y ⟧} {m′ : T∞ Z}
            → m ≈[ R ] m′ → subst (λ V → T∞ ⟦ V ⟧) e m ≈[ (λ y z → R (subst ⟦_⟧ (sym e) y) z) ] m′
≈-transport refl p = p

subst-sym-subst : ∀ {X X′ : LTy} (e : X ≡ X′) (x : ⟦ X′ ⟧) → subst ⟦_⟧ e (subst ⟦_⟧ (sym e) x) ≡ x
subst-sym-subst refl x = refl

-- a term moved forward along equal codomains
ev-subst-cod⁺ : ∀ {Γ} (δ : Env Γ) {X Y Y′} (e : Y ≡ Y′) (c : P.IR Γ X Y) (a : ⟦ X ⟧)
              → P.ev δ (subst (λ Z → P.IR Γ X Z) e c) a ≡ subst (λ Z → T∞ ⟦ Z ⟧) e (P.ev δ c a)
ev-subst-cod⁺ δ refl c a = refl

module _ {Γ : Cx} (δ : Env Γ) (cs : CanonicalName → (A B : IRTy) → ⟦ A ⟧ᴰᴵ → T∞ ⟦ B ⟧ᴰᴵ) where

  module Unfold {F} (wf : WellFormedFI F) {E A} (c : M.IR (E * A) (⟦ F ⟧TI A)) (c′ : P.IR Γ (⟪ E ⟫ ⊗t ⟪ A ⟫) ⟪ ⟦ F ⟧TI A ⟫)
                (φ : P.BlkIR Γ (subst (λ X → P.IR Γ (⟪ E ⟫ ⊗t ⟪ A ⟫) X) (⟪⟫-TI wf A) c′))
                (ih : ∀ {x x′} → W (E * A) x x′ → P.ev δ c′ x ≈[ W (⟦ F ⟧TI A) ] evalᴰ fmt (callEnv cs ans) c x′)
                (e : ⟦ ⟪ E ⟫ ⟧) (e′ : ⟦ E ⟧ᴰᴵ) (we : W E e e′) where

    c″ : P.IR Γ (⟪ E ⟫ ⊗t ⟪ A ⟫) (LF∙ (lf F) ⟪ A ⟫)
    c″ = subst (λ X → P.IR Γ (⟪ E ⟫ ⊗t ⟪ A ⟫) X) (⟪⟫-TI wf A) c′

    -- the two coalgebras, per seed
    cC : ⟦ ⟪ A ⟫ ⟧ → T (FS (lf F) ⟦ ⟪ A ⟫ ⟧)
    cC a = fmapT (coh (lf F) ⟪ A ⟫) (P.evB δ φ (e , a))

    cM : ⟦ ⌈ A ⌉ ⟧ᴰ → T∞ (⟦ SF F ⟧SF ⟦ ⌈ A ⌉ ⟧ᴰ)
    cM a′ = fmap∞ (Val.coerce-μ-in ⌈ F ⌉F ⟦ ⌈ A ⌉ ⟧ᴰ)
              (fmap∞ (λ x → coerce-functor-D (wf-⌈⌉ wf) ⌈ A ⌉ (subst (λ Ty → ⟦ Ty ⟧ᴰ) (⌈⟧TI-commute F A) x))
                     (evalᴰ fmt (callEnv cs ans) c (e′ , a′)))

    -- a seed's coalgebra, against master's
    seed≈ : ∀ {a a′} → W A a a′ → emb (cC a) ≈[ WLS A F ] cM a′
    seed≈ {a} {a′} w =
      fmapʳ (embfmap≈ (P.evB δ φ (e , a))
               (≈-≈R (≈-sym (P.ev-coh δ φ (e , a)))
                     (subst (λ m → m ≈[ _ ] evalᴰ fmt (callEnv cs ans) c (e′ , a′))
                            (sym (ev-subst-cod⁺ δ (⟪⟫-TI wf A) c′ (e , a)))
                            (≈-transport (⟪⟫-TI wf A) (ih (we , w)))))
               (λ {x} {x′} s → subst (λ z → WLS A F (coh (lf F) ⟪ A ⟫ z) _) (subst-sym-subst (⟪⟫-TI wf A) x)
                                      (Seed-layer wf s)))

    mutual
      -- ★ the unfold, coinductively
      ana-W : ∀ {a a′} → W A a a′ → WNu F (anaN (lf F) cC a) (anaFᴵ ⌈ F ⌉F _ a′)
      _≈[_]_.blockR (wout (ana-W {a} w)) = tree (cC a) (_≈[_]_.blockR (seed≈ w))

      tree : ∀ (b : T (FS (lf F) ⟦ ⟪ A ⟫ ⟧)) {m′} → BlR (WLS A F) (embB b) m′
           → BlR (WLν F F) (embB (treeN (lf F) cC b)) (SI.anaBlock (SF F) cM m′)
      tree (ret l)      (≈retR s)  = ≈retR (mapR wf s)
      tree (call o a k) (≈callR h) = ≈callR (λ y → tree (k y) (h y))
      tree (halt o a)   ≈haltR     = ≈haltR

      mapR : ∀ {G} (wg : WellFormedFI G) {l l′} → WLS A G l l′
           → WLν F G (mapN (lf F) (lf G) cC l) (SI.mapAnaᴵ (SF F) (SF G) cM l′)
      mapR (wf-K b) s = K-map {F} b s
      mapR wf-Id s = ana-W s
      mapR (wf-Sum f g) {l = inj₁ _} {l′ = inj₁ _} (⊎₁ s) = ⊎₁ (mapR f s)
      mapR (wf-Sum f g) {l = inj₂ _} {l′ = inj₂ _} (⊎₂ s) = ⊎₂ (mapR g s)
      mapR (wf-Prod f g) {l = _ , _} {l′ = _ , _} (s₁ , s₂) = mapR f s₁ , mapR g s₂

  -- ★ `Ana` against master's
  ana≈ : ∀ {F} (wf : WellFormedFI F) {E A} (c : M.IR (E * A) (⟦ F ⟧TI A)) c′ φ →
         (∀ {x x′} → W (E * A) x x′ → P.ev δ c′ x ≈[ W (⟦ F ⟧TI A) ] evalᴰ fmt (callEnv cs ans) c x′) →
         ∀ {a b} → W (E * A) a b →
         P.ev δ (P.Ana (lf F) (subst (λ X → P.IR Γ (⟪ E ⟫ ⊗t ⟪ A ⟫) X) (⟪⟫-TI wf A) c′) φ) a
           ≈[ W (ν-type F) ] evalᴰ fmt (callEnv cs ans) (M.Ana wf c) b
  ana≈ wf c c′ φ ih {e , a} {e′ , a′} (we , wa) = ret≈R (Unfold.ana-W wf c c′ φ ih e e′ we wa)

------------------------------------------------------------------------
-- 8. ★ THE OBLIGATIONS, discharged.
------------------------------------------------------------------------

module _ {Γ : Cx} (δ : Env Γ) (cs : CanonicalName → (A B : IRTy) → ⟦ A ⟧ᴰᴵ → T∞ ⟦ B ⟧ᴰᴵ) where

  casts : BP.Casts δ cs
  casts = record
    { In≈   = In≈ δ cs
    ; out≈  = out≈ δ cs
    ; Out≈  = Out≈ δ cs
    ; inν≈  = inν≈ δ cs
    ; op≈   = op≈ δ cs
    ; cata≈ = cata≈ δ cs
    ; ana≈  = ana≈ δ cs
    }
