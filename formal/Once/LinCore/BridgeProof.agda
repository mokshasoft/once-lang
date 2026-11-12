-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.LinCore.BridgeProof — plan 0.146 B1.3: the pass's meaning against
-- master's `evalᴰ`.
--
-- ★ `bridge`: if `c` translates `ir` (`FromIR.Tr`), then on related
-- arguments the resolved IR's meaning (`Pass.ev`, over the core's values) is
-- bisimilar to master's `evalᴰ`, up to the relation `Bridge.W`. With
-- `Pass.pass-ok` (the core's term against `ev`), the core's compiled program
-- is related to master's meaning.
--
-- By induction on `Tr`. The calls need the table's two meanings related
-- (`EnvOK`). The CASTS — the IR's functor layers against the core's codes (μ,
-- ν), and an op's base values against its flat ones — are the record `Casts`,
-- each a lemma about one generator, proved in `Once.LinCore.Casts`.
------------------------------------------------------------------------

{-# OPTIONS --guardedness #-}

open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (subst; subst₂; sym)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Sum.Relation.Binary.Pointwise using () renaming (inj₁ to ⊎₁; inj₂ to ⊎₂)
open import Data.Maybe using (just; nothing)
open import Once.Spec.Numerics using (TargetNum)
open import Once.IR.Semantics.Trace using (FFIAnswers; unlinkedT)
open import Once.IR.Semantics.Iterative using (embed)
open import Once.Spec.Grade using (fin; eff)
open import Once.IRTy using (IRTy; ⌊_⌋; WellFormedFI; ⟦_⟧TI; μ-type; ν-type; _*_; _+_; _⇛[_]_)
open import Once.Spec.Name using (CanonicalName)
open import Once.SigOp.Info using (SigOpInfo; module SigOpInfo)
open import Once.Denotation.DenotTrace using (evalᴰ; CallEnv; callEnv)
open import Once.Denotation.ValueDomain using (⟦_⟧ᴰᴵ)
import Once.IR as M
import Once.LinCore.FromIR
import Once.LinCore.Bridge
import Once.LinCore.Bisim
import Once.LinCore.Pass

module Once.LinCore.BridgeProof (fmt : TargetNum) (ans : FFIAnswers) where

open import Once.LinCore.NbEPLinCore fmt ans
open Once.LinCore.FromIR fmt ans
open Once.LinCore.Bridge fmt ans
open Once.LinCore.Bisim fmt ans using (_≈[_]_; ret≈R; >>=-congR; iter-congR; ≈-≈R; ≈-sym; module _≈[_]_; ≈haltR)

------------------------------------------------------------------------
-- 1. THE OBLIGATIONS: each cast, one generator at a time.
------------------------------------------------------------------------

module _ {Γ : Cx} (δ : Env Γ) (cs : CanonicalName → (A B : IRTy) → ⟦ A ⟧ᴰᴵ → T∞ ⟦ B ⟧ᴰᴵ) where

  ρ : CallEnv
  ρ = callEnv cs ans

  -- the IR's generators at a cast, each against master's
  record Casts : Set where
    field
      In≈    : ∀ {F} (wf : WellFormedFI F) {a a′} → W (⟦ F ⟧TI (μ-type F)) a a′ →
               P.ev δ (subst (λ X → P.IR Γ X ⟪ μ-type F ⟫) (sym (⟪⟫-TI wf (μ-type F))) (P.In (lf F))) a
                 ≈[ W (μ-type F) ] evalᴰ fmt ρ (M.In wf) a′
      out≈   : ∀ {F} (wf : WellFormedFI F) {a a′} → W (μ-type F) a a′ →
               P.ev δ (subst (λ X → P.IR Γ ⟪ μ-type F ⟫ X) (sym (⟪⟫-TI wf (μ-type F))) (P.out-μ (lf F))) a
                 ≈[ W (⟦ F ⟧TI (μ-type F)) ] evalᴰ fmt ρ (M.out-μ wf) a′
      Out≈   : ∀ {F} (wf : WellFormedFI F) {a a′} → W (ν-type F) a a′ →
               P.ev δ (subst (λ X → P.IR Γ ⟪ ν-type F ⟫ X) (sym (⟪⟫-TI wf (ν-type F))) (P.Out (lf F))) a
                 ≈[ W (⟦ F ⟧TI (ν-type F)) ] evalᴰ fmt ρ (M.Out wf) a′
      inν≈   : ∀ {F} (wf : WellFormedFI F) {a a′} → W (⟦ F ⟧TI (ν-type F)) a a′ →
               P.ev δ (subst (λ X → P.IR Γ X ⟪ ν-type F ⟫) (sym (⟪⟫-TI wf (ν-type F))) (P.in-ν (lf F))) a
                 ≈[ W (ν-type F) ] evalᴰ fmt ρ (M.in-ν wf) a′
      op≈    : ∀ {A B} (si : SigOpInfo A B) {a a′} → W ⌊ A ⌋ a a′ →
               P.ev δ (subst₂ (P.IR Γ) (sym (⟪⌊⌋⟫-flat (SigOpInfo.baseA si))) (sym (⟪⌊⌋⟫-flat (SigOpInfo.conB si)))
                                       (P.SigOp (sig si))) a
                 ≈[ W ⌊ B ⌋ ] evalᴰ fmt ρ (M.SigOp si) a′
      -- the fold and the unfold: their algebra and coalgebra related as the
      -- induction gives them
      cata≈  : ∀ {F} (wf : WellFormedFI F) {E A} (alg : M.IR (E * ⟦ F ⟧TI A) A) a′ →
               (∀ {x x′} → W (E * ⟦ F ⟧TI A) x x′ → P.ev δ a′ x ≈[ W A ] evalᴰ fmt ρ alg x′) →
               ∀ {a b} → W (E * μ-type F) a b →
               P.ev δ (P.Cata (lf F) (subst (λ X → P.IR Γ (⟪ E ⟫ ⊗t X) ⟪ A ⟫) (⟪⟫-TI wf A) a′)) a
                 ≈[ W A ] evalᴰ fmt ρ (M.Cata wf alg) b
      ana≈   : ∀ {F} (wf : WellFormedFI F) {E A} (c : M.IR (E * A) (⟦ F ⟧TI A)) c′ φ →
               (∀ {x x′} → W (E * A) x x′ → P.ev δ c′ x ≈[ W (⟦ F ⟧TI A) ] evalᴰ fmt ρ c x′) →
               ∀ {a b} → W (E * A) a b →
               P.ev δ (P.Ana (lf F) (subst (λ X → P.IR Γ (⟪ E ⟫ ⊗t ⟪ A ⟫) X) (⟪⟫-TI wf A) c′) φ) a
                 ≈[ W (ν-type F) ] evalᴰ fmt ρ (M.Ana wf c) b

  -- ★ the table's two meanings, related: a resolved call against master's
  -- `callsE`, and an unlinked one is master's `unlinkedT`
  record EnvOK (rs : Resolver Γ) : Set where
    field
      hit≈  : ∀ {f A B g l} {p : Γ ∋[ l ] sg once g One ⟪ A ⟫ ⟪ B ⟫} → rs f A B ≡ just (hit g p) →
              ∀ {a a′} → W A a a′ → up g (lookup δ p tt a) ≈[ W B ] cs f A B a′
      miss≡ : ∀ {f A B} → rs f A B ≡ nothing → ∀ a′ → cs f A B a′ ≡ embed unlinkedT

------------------------------------------------------------------------
-- 2. ★ THE BRIDGE, by induction on the translation.
------------------------------------------------------------------------

  module _ (κ : Casts) {rs : Resolver Γ} (ok : EnvOK rs) where
    open Casts κ
    open EnvOK ok

    -- the unlinked call: the core's op halts as master's `unlinkedT`
    miss≈ : ∀ {A B f} → rs f A B ≡ nothing → ∀ {a a′} →
            P.ev δ (unlinked {Γ} {A} {B}) a ≈[ W B ] evalᴰ fmt ρ (M.Call {A} {B} f) a′
    _≈[_]_.blockR (miss≈ {A} {B} {f} e {a′ = a′}) rewrite miss≡ e a′ = ≈haltR

    bridge : ∀ {A B} {ir : M.IR A B} {c} → Tr rs ir c → ∀ {a a′} → W A a a′ → P.ev δ c a ≈[ W B ] evalᴰ fmt ρ ir a′
    bridge t-id         w = ret≈R w
    bridge (t-∘ tg tf)  w = >>=-congR (bridge tf w) (λ r → bridge tg r)
    bridge (t-pair tf tg) w = >>=-congR (bridge tf w) (λ r → >>=-congR (bridge tg w) (λ r′ → ret≈R (r , r′)))
    bridge t-fst {a = _ , _} {a′ = _ , _} (w , _) = ret≈R w
    bridge t-snd {a = _ , _} {a′ = _ , _} (_ , w) = ret≈R w
    bridge t-inl        w = ret≈R (⊎₁ w)
    bridge t-inr        w = ret≈R (⊎₂ w)
    bridge (t-case tf tg) (⊎₁ w) = bridge tf w
    bridge (t-case tf tg) (⊎₂ w) = bridge tg w
    bridge t-term       w = ret≈R tt
    bridge t-init {a = ()}
    bridge (t-curry {π = fin _} {γ = γ} tf) w =
      ret≈R (λ r → ≈-≈R (≈-sym (P.ev-coh δ γ _)) (bridge tf (w , r)))
    bridge (t-curry {π = eff} tf) w = ret≈R (λ r → bridge tf (w , r))
    bridge t-apply {a = _ , _} {a′ = _ , _} (wf , wa) = wf wa
    bridge (t-In wf)    w = In≈ wf w
    bridge (t-out wf)   w = out≈ wf w
    bridge (t-cata wf {alg = alg} {a′ = a′} ta) w = cata≈ wf alg a′ (bridge ta) w
    bridge (t-Out wf)   w = Out≈ wf w
    bridge (t-inν wf)   w = inν≈ wf w
    bridge (t-ana wf {c = c} {c′ = c′} tc φ) w = ana≈ wf c c′ φ (bridge tc) w
    bridge (t-iter tb φ) {a = _ , _} {a′ = _ , _} (we , wa) =
      iter-congR (λ r → bridge tb (we , r)) (bridge tb (we , wa))
    bridge t-int        w = ret≈R refl
    bridge t-float      w = ret≈R refl
    bridge (t-op si)    w = op≈ si w
    bridge (t-hit e)    w = hit≈ e w
    bridge (t-miss {A} {B} {f} e) {a} {a′} w = miss≈ {A} {B} {f} e {a} {a′}
