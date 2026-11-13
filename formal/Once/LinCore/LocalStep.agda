-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.LinCore.LocalStep — plan 0.146 B1.4b (D417, step 3): ★ THE LOCAL
-- STEP THEOREM.
--
-- Every image step that stays in its root's code (`Local`: not a call, a
-- return, a loop's turn, a dispatch through a cell, a trampoline's cell
-- part, nor a SigOp — `lop`'s lemma is still owed) takes the flat machine,
-- `Here` at its path, to `Here` at the next path (`succ`), in the steps its
-- lowering takes, keeping what `Keep` says, with the flat heap counter the
-- image's.
------------------------------------------------------------------------

{-# OPTIONS --guardedness #-}

open import Data.Nat using (ℕ; suc; _≤_)
open import Data.List using ([]; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong)
open import Once.Spec.Numerics using (TargetNum)
open import Once.IR.Semantics.Trace using (FFIAnswers)
open import Once.LinCore.Flat using (Base)
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.SMCore
open import Once.CCC.Machine.Flat using (module FlatMachine)
open import Once.CCC.Codegen.FlatStepLemmas using (module FlatStepsAPI)

module Once.LinCore.LocalStep
  (fmt : TargetNum) (ans : FFIAnswers)
  (bw : Base → ℕ)
  where

open import Once.LinCore.NbEPLinCore fmt ans
open import Once.LinCore.Events fmt ans bw
open import Once.LinCore.Machine fmt ans bw using (Sh; _∣_; Stk; _∷ˢ_; Slots; Cfg; _∥_)
open import Once.LinCore.Image fmt ans bw
open import Once.LinCore.ImageRun fmt ans bw
open import Once.LinCore.Keys fmt ans bw
open import Once.LinCore.Layout fmt ans bw using (Frame; frameOf; budget)
open import Once.LinCore.ImagePt fmt ans bw using (Sub; next; left; right; eleft; eright)
open import Once.LinCore.LowAt fmt ans bw using (Inside; module At)
open import Once.LinCore.StepLocal fmt ans bw using (module Loc)
open import Once.LinCore.StepPrim fmt ans bw using (module Prims)

------------------------------------------------------------------------
-- 1. WHICH STEPS ARE LOCAL.
------------------------------------------------------------------------

-- a primitive other than a SigOp (whose lemma is owed)
NotOp : ∀ {Γ A B} → LTm Γ A B → Set
NotOp (lop s) = ⊥
{-# CATCHALL #-}
NotOp _       = ⊤

Local : ∀ {T sh U sh′ U′} {c : Codeᴵ sh U} {r : Ret U T} {m n t} {c′ : Codeᴵ sh′ U′} {r′ : Ret U′ T} {m′ n′}
      → StepI c r m n t c′ r′ m′ n′ → Set
Local i-unpair       = ⊤
Local i-pair         = ⊤
Local i-swap         = ⊤
Local i-unit         = ⊤
Local (i-prim {g = g} _) = NotOp g
Local i-untag        = ⊤
Local i-untag₁       = ⊤
Local i-tag₁         = ⊤
Local i-case₁        = ⊤
Local i-case₂        = ⊤
Local i-elend        = ⊤
Local i-eunlend      = ⊤
Local i-elift        = ⊤
Local (i-efst _)     = ⊤
Local (i-esnd _)     = ⊤
Local (i-eout _)     = ⊤
Local (i-eoutq _)    = ⊤
Local (i-ecase₁ _)   = ⊤
Local (i-ecase₂ _)   = ⊤
Local (i-eapp _)     = ⊤
Local i-epop         = ⊤
Local (i-eword _)    = ⊤
{-# CATCHALL #-}
Local _              = ⊥

------------------------------------------------------------------------
-- 2. ★ THE THEOREM, at a root.
------------------------------------------------------------------------

module Steps {FS : FrameSemantics} (U : Univ)
             (ncty : ∀ {F S} → (F , S) ∈ nus U → cty (F , S) ∈ tys U)
             (ldConst : ∀ {b} → ⟦ b ⟧b → AbstractInstr)
             (wordOf : ∀ {b} → ⟦ b ⟧b → StoredValue FS)
             (prog : AbstractTrace)
             {sh₀ U₀} (root : Codeᴵ sh₀ U₀) (j : ℕ)
             (L₀ : At.Low U ncty ldConst (frameOf root) j root)
             (R : Inside prog (At.code U ncty ldConst (frameOf root) j L₀)) where

  open Loc {FS} U ncty ldConst wordOf prog root j L₀ R
  open Prims {FS} U ncty ldConst wordOf prog root j L₀ R
  open At U ncty ldConst φ j using (lcin)
  open FlatMachine {FS} using (FlatState; floc; falloc; fpc)
  open FlatStepsAPI {FS} using (FlatSteps)
  open import Once.LinCore.Moves {FS} using (Keep; Old; slot)

  -- a constant's loader puts its word in `Output` (the image's `ldConst`'s contract)
  LdOk : Set
  LdOk = ∀ {b} (v : ⟦ b ⟧b) (fs : FlatState)
       → FlatMachine.flat-exec-instr {FS} (ldConst v) prog fs
         ≡ record fs { floc = record (floc fs) { regs = writeReg (LocState.regs (floc fs)) Output (wordOf v) } ; fpc = suc (fpc fs) }

  -- what a local step gives: the flat steps, `Here` at the next path, the
  -- frames kept, the heap counter the image's
  Out : ∀ {sh U′} {c : Codeᴵ sh U′} → Sub root c → FlatState → ℕ → Cfg sh → Set
  Out s′ fs n′ m′ = Σ ℕ λ N → Σ FlatState λ fs′ → FlatSteps prog N fs fs′ × Here s′ m′ fs′ × Keep fs fs′
                    × AllocState.next-heap-ref (falloc fs′) ≡ n′ × Old (AllocState.next-heap-ref (falloc fs)) fs fs′
                    × (∀ x → budget φ ≤ x → slot fs′ x ≡ slot fs x)

  private
    out0 : ∀ {sh U′} {c : Codeᴵ sh U′} {s′ : Sub root c} {fs n m′} → Moved s′ fs 0 m′
         → AllocState.next-heap-ref (falloc fs) ≡ n → Out s′ fs n m′
    out0 (N , fs′ , st , H′ , K , nx′ , o , tp) nx = N , fs′ , st , H′ , K , trans nx′ nx , o , tp

    out1 : ∀ {sh U′} {c : Codeᴵ sh U′} {s′ : Sub root c} {fs n m′} → Moved s′ fs 1 m′
         → AllocState.next-heap-ref (falloc fs) ≡ n → Out s′ fs (suc n) m′
    out1 (N , fs′ , st , H′ , K , nx′ , o , tp) nx = N , fs′ , st , H′ , K , trans nx′ (cong suc nx) , o , tp

  -- ★ a primitive, by its run
  prim-step : ∀ {Γ} {ds : Defs Γ} {Es A B S V} {g : LTm Γ A B} {k : Codeᴵ (Es ∣ B ∷ S) V} (s : Sub root (prim ds g ⨾ k))
                {es : Slots Es} {os : Stk S} {v : MV A} {w : MV B} {n n′ t fs}
            → LdOk → Run ds g mone v n (gives w n′) t → NotOp g
            → Here s (es ∥ v ∷ˢ os) fs → AllocState.next-heap-ref (falloc fs) ≡ n → Fresh (es ∥ v ∷ˢ os) fs
            → Out (next s) fs n′ (es ∥ w ∷ˢ os)
  prim-step s ld r-ρ      _ H nx fr = out0 (st-ρ s H) nx
  prim-step s ld r-ρ⁻     _ H nx fr = out0 (st-ρ⁻ s H) nx
  prim-step s ld r-λ      _ H nx fr = out0 (st-λ s H) nx
  prim-step s ld r-λ⁻     _ H nx fr = out0 (st-λ⁻ s H) nx
  prim-step s ld r-α      _ H nx fr = out0 (st-α s H) nx
  prim-step s ld r-α⁻     _ H nx fr = out0 (st-α⁻ s H) nx
  prim-step s ld r-swap   _ H nx fr = out0 (st-lswap s H) nx
  prim-step s ld r-drop   _ H nx fr = out0 (st-drop s H) nx
  prim-step s ld r-inl    _ H nx fr = out0 (st-inl s H) nx
  prim-step s ld r-inr    _ H nx fr = out0 (st-inr s H) nx
  prim-step s ld r-In     _ H refl fr = out1 (st-in s H fr) refl
  prim-step s ld r-Outμ   _ H nx fr = out0 (st-out s H) nx
  prim-step s ld r-clo    _ H nx fr = out0 (st-clo s H) nx
  prim-step s ld r-lam    _ H refl fr = out1 (st-lam s H fr) refl
  prim-step s ld r-lamω   _ H refl fr = out1 (st-lamω s H fr) refl
  prim-step s ld r-unf    _ H refl fr = out1 (st-unf s H fr) refl
  prim-step s {fs = fs} ld (r-const {v = v}) _ H nx fr = out0 (st-const s (ld v fs) H) nx
  prim-step s ld (r-op _) () H nx fr
  prim-step s ld (r-tmp r _ _) no H nx fr = prim-step s ld r no H nx fr
  -- not primitives: no lowering evidence
  prim-step s ld r-id               _ H nx fr = ⊥-elim (proj₁ (lcin (lowAt s)))
  prim-step s ld (r-∘ _ _)          _ H nx fr = ⊥-elim (proj₁ (lcin (lowAt s)))
  prim-step s ld (r-⊗ _ _)          _ H nx fr = ⊥-elim (proj₁ (lcin (lowAt s)))
  prim-step s ld r-dup              _ H nx fr = ⊥-elim (proj₁ (lcin (lowAt s)))
  prim-step s ld (r-case₁ _)        _ H nx fr = ⊥-elim (proj₁ (lcin (lowAt s)))
  prim-step s ld (r-case₂ _)        _ H nx fr = ⊥-elim (proj₁ (lcin (lowAt s)))
  prim-step s ld (r-app _ _)        _ H nx fr = ⊥-elim (proj₁ (lcin (lowAt s)))
  prim-step s ld (r-cata _ _)       _ H nx fr = ⊥-elim (proj₁ (lcin (lowAt s)))
  prim-step s ld (r-cata-reuse _ _) _ H nx fr = ⊥-elim (proj₁ (lcin (lowAt s)))
  prim-step s ld (r-lend _)         _ H nx fr = ⊥-elim (proj₁ (lcin (lowAt s)))
  prim-step s ld (r-lift _)         _ H nx fr = ⊥-elim (proj₁ (lcin (lowAt s)))
  prim-step s ld r-copy             _ H nx fr = ⊥-elim (proj₁ (lcin (lowAt s)))
  prim-step s ld (r-ev _)           _ H nx fr = ⊥-elim (proj₁ (lcin (lowAt s)))
  prim-step s ld (r-nout _)         _ H nx fr = ⊥-elim (proj₁ (lcin (lowAt s)))
  prim-step s ld (r-iter _ _)       _ H nx fr = ⊥-elim (proj₁ (lcin (lowAt s)))

  -- the next path of a local step
  succ : ∀ {T sh U sh′ U′} {c : Codeᴵ sh U} {r : Ret U T} {m n t} {c′ : Codeᴵ sh′ U′} {r′ : Ret U′ T} {m′ n′}
       → (st : StepI c r m n t c′ r′ m′ n′) → Local st → Sub root c → Sub root c′
  succ i-unpair     _ s = next s
  succ i-pair       _ s = next s
  succ i-swap       _ s = next s
  succ i-unit       _ s = next s
  succ (i-prim _)   _ s = next s
  succ i-untag      _ s = next s
  succ i-untag₁     _ s = next s
  succ i-tag₁       _ s = next s
  succ i-case₁      _ s = left s
  succ i-case₂      _ s = right s
  succ i-elend      _ s = next s
  succ i-eunlend    _ s = next s
  succ i-elift      _ s = next s
  succ (i-efst _)   _ s = next s
  succ (i-esnd _)   _ s = next s
  succ (i-eout _)   _ s = next s
  succ (i-eoutq _)  _ s = next s
  succ (i-ecase₁ _) _ s = eleft s
  succ (i-ecase₂ _) _ s = eright s
  succ (i-eapp _)   _ s = next s
  succ i-epop       _ s = next s
  succ (i-eword _)  _ s = next s

  -- ★ THE LOCAL STEP THEOREM
  local-step : ∀ {T sh U sh′ U′} {c : Codeᴵ sh U} {r : Ret U T} {m n t} {c′ : Codeᴵ sh′ U′} {r′ : Ret U′ T} {m′ n′} {fs}
             → LdOk → Labelled
             → (st : StepI c r m n t c′ r′ m′ n′) (l : Local st) (s : Sub root c)
             → Here s m fs → AllocState.next-heap-ref (falloc fs) ≡ n → Fresh m fs
             → Out (succ st l s) fs n′ m′
  local-step ld lab i-unpair       _ s H nx fr = out0 (st-unpair s H) nx
  local-step ld lab i-pair         _ s H nx fr = out0 (st-pair s H) nx
  local-step ld lab i-swap         _ s H nx fr = out0 (st-swap s H) nx
  local-step ld lab i-unit         _ s H nx fr = out0 (st-unit s H) nx
  local-step ld lab (i-prim r)     l s H nx fr = prim-step s ld r l H nx fr
  local-step ld lab i-untag        _ s H nx fr = out0 (st-untag s H) nx
  local-step ld lab i-untag₁       _ s H nx fr = out0 (st-untag₁ s H) nx
  local-step ld lab i-tag₁         _ s H nx fr = out0 (st-tag₁ s H) nx
  local-step ld lab i-case₁        _ s H nx fr = out0 (st-case₁ lab s H) nx
  local-step ld lab i-case₂        _ s H nx fr = out0 (st-case₂ s H) nx
  local-step ld lab i-elend        _ s H nx fr = out0 (st-elend s H) nx
  local-step ld lab i-eunlend      _ s H nx fr = out0 (st-eunlend s H) nx
  local-step ld lab i-elift        _ s H nx fr = out0 (st-elift s H) nx
  local-step ld lab (i-efst eq)    _ s H nx fr = out0 (st-efst s eq H) nx
  local-step ld lab (i-esnd eq)    _ s H nx fr = out0 (st-esnd s eq H) nx
  local-step ld lab (i-eout eq)    _ s H nx fr = out0 (st-eout s eq H) nx
  local-step ld lab (i-eoutq eq)   _ s H nx fr = out0 (st-eoutq s eq H) nx
  local-step ld lab (i-ecase₁ eq)  _ s H nx fr = out0 (st-ecase₁ lab s eq H) nx
  local-step ld lab (i-ecase₂ eq)  _ s H nx fr = out0 (st-ecase₂ s eq H) nx
  local-step ld lab (i-eapp eq)    _ s H nx fr = out0 (st-eapp s eq H) nx
  local-step ld lab i-epop         _ s H nx fr = out0 (st-epop s H) nx
  local-step ld lab (i-eword eq)   _ s H nx fr = out0 (st-eword s eq H) nx
