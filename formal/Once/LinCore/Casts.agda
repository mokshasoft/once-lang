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
open import Once.Spec.Type using (Type; ∅ₖ; b-var; b-Unit; b-Void; b-Int; b-Float; b-*; b-+)
open import Once.IRTy using (IRTy; ⌊_⌋)
open import Once.Denotation.ValueDomain using (⟦_⟧ᴰᴵ; ⟦_⟧ᴰ; cohᴰ; forgetᵇ; injectᵇ)
open import Once.Spec.Word using (Carrier)
open import Once.Spec.Type using () renaming (Base to SBase)
import Once.IR.Semantics.Value Carrier Carrier as Val
import Relation.Binary.PropositionalEquality
open import Once.Spec.Name using (CanonicalName)
open import Once.SigOp.Info using (SigOpInfo; module SigOpInfo)
open import Once.Denotation.DenotTrace using (evalᴰ; sigOpT; callEnv)
import Once.IR as M
import Once.LinCore.FromIR
import Once.LinCore.Bridge
import Once.LinCore.Bisim

module Once.LinCore.Casts (fmt : TargetNum) (ans : FFIAnswers) where

open import Once.LinCore.NbEPLinCore fmt ans
open Once.LinCore.FromIR fmt ans
open Once.LinCore.Bridge fmt ans
open Once.LinCore.Bisim fmt ans using (_≈[_]_; module _≈[_]_; BlR; ≈retR; ≈callR; ≈haltR)

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
