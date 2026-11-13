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
-- which steps are local: by the code's head
open import Once.LinCore.StepKinds fmt ans bw using (NotOp; Local; LocalC; Motive; LocalCases; local-elim)
import Level

------------------------------------------------------------------------
-- ★ THE THEOREM, at a root.
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
  open At U ncty ldConst φ j using (lcin; lfin)
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
  -- the next path of a local step, and what stays: the return stack, the way out
  record Succ {T sh U sh′ U′} {c : Codeᴵ sh U} {c′ : Codeᴵ sh′ U′} (r : Ret U T) (r′ : Ret U′ T) (s : Sub root c) : Set₁ where
    field
      sub   : Sub root c′
      carry : ∀ (P : ∀ {V} → AbstractTrace → Ret V T → Set) → P (lfin (lowAt s)) r → P (lfin (lowAt sub)) r′

  -- by the step's constructor (the split is StepKinds')
  SuccM : ∀ {T} → Motive {Level.suc Level.zero} {T}
  SuccM {c = c} {r = r} {c′ = c′} {r′ = r′} _ = (s : Sub root c) → Succ {c′ = c′} r r′ s

  succ-cases : ∀ {T} → LocalCases {Level.suc Level.zero} {T}
  succ-cases = record
    { P        = SuccM
    ; unpair′  = λ s → record { sub = next s ; carry = λ P x → x }
    ; pair′    = λ s → record { sub = next s ; carry = λ P x → x }
    ; swap′    = λ s → record { sub = next s ; carry = λ P x → x }
    ; unit′    = λ s → record { sub = next s ; carry = λ P x → x }
    ; prim′    = λ _ _ s → record { sub = next s ; carry = λ P x → x }
    ; untag′   = λ s → record { sub = next s ; carry = λ P x → x }
    ; untag₁′  = λ s → record { sub = next s ; carry = λ P x → x }
    ; tag₁′    = λ s → record { sub = next s ; carry = λ P x → x }
    ; case₁′   = λ s → record { sub = left s ; carry = λ P x → x }
    ; case₂′   = λ s → record { sub = right s ; carry = λ P x → x }
    ; elend′   = λ s → record { sub = next s ; carry = λ P x → x }
    ; eunlend′ = λ s → record { sub = next s ; carry = λ P x → x }
    ; elift′   = λ s → record { sub = next s ; carry = λ P x → x }
    ; efst′    = λ _ s → record { sub = next s ; carry = λ P x → x }
    ; esnd′    = λ _ s → record { sub = next s ; carry = λ P x → x }
    ; eout′    = λ _ s → record { sub = next s ; carry = λ P x → x }
    ; eoutq′   = λ _ s → record { sub = next s ; carry = λ P x → x }
    ; ecase₁′  = λ _ s → record { sub = eleft s ; carry = λ P x → x }
    ; ecase₂′  = λ _ s → record { sub = eright s ; carry = λ P x → x }
    ; eapp′    = λ _ s → record { sub = next s ; carry = λ P x → x }
    ; epop′    = λ s → record { sub = next s ; carry = λ P x → x }
    ; eword′   = λ _ s → record { sub = next s ; carry = λ P x → x }
    }

  succ′ : ∀ {T sh U sh′ U′} {c : Codeᴵ sh U} {r : Ret U T} {m n t} {c′ : Codeᴵ sh′ U′} {r′ : Ret U′ T} {m′ n′}
        → (st : StepI c r m n t c′ r′ m′ n′) → Local st → (s : Sub root c) → Succ {c′ = c′} r r′ s
  succ′ st l = local-elim succ-cases st l

  succ : ∀ {T sh U sh′ U′} {c : Codeᴵ sh U} {r : Ret U T} {m n t} {c′ : Codeᴵ sh′ U′} {r′ : Ret U′ T} {m′ n′}
       → (st : StepI c r m n t c′ r′ m′ n′) → Local st → Sub root c → Sub root c′
  succ st l s = Succ.sub (succ′ st l s)

  -- what a local step owes: from `Here` at its path, `Here` at the next
  StepM : ∀ {T} → Motive {Level.zero} {T}
  StepM {c = c} {m = m} {n = n} {m′ = m′} {n′ = n′} st =
    (l : LocalC c) (s : Sub root c) {fs : FlatState} → Here s m fs → AllocState.next-heap-ref (falloc fs) ≡ n → Fresh m fs
    → Out (succ st l s) fs n′ m′

  step-cases : ∀ {T} → LdOk → Labelled → LocalCases {Level.zero} {T}
  step-cases ld lab = record
    { P        = StepM
    ; unpair′  = λ _ s H nx fr → out0 (st-unpair s H) nx
    ; pair′    = λ _ s H nx fr → out0 (st-pair s H) nx
    ; swap′    = λ _ s H nx fr → out0 (st-swap s H) nx
    ; unit′    = λ _ s H nx fr → out0 (st-unit s H) nx
    ; prim′    = λ run no _ s H nx fr → prim-step s ld run no H nx fr
    ; untag′   = λ _ s H nx fr → out0 (st-untag s H) nx
    ; untag₁′  = λ _ s H nx fr → out0 (st-untag₁ s H) nx
    ; tag₁′    = λ _ s H nx fr → out0 (st-tag₁ s H) nx
    ; case₁′   = λ _ s H nx fr → out0 (st-case₁ lab s H) nx
    ; case₂′   = λ _ s H nx fr → out0 (st-case₂ s H) nx
    ; elend′   = λ _ s H nx fr → out0 (st-elend s H) nx
    ; eunlend′ = λ _ s H nx fr → out0 (st-eunlend s H) nx
    ; elift′   = λ _ s H nx fr → out0 (st-elift s H) nx
    ; efst′    = λ eq _ s H nx fr → out0 (st-efst s eq H) nx
    ; esnd′    = λ eq _ s H nx fr → out0 (st-esnd s eq H) nx
    ; eout′    = λ eq _ s H nx fr → out0 (st-eout s eq H) nx
    ; eoutq′   = λ eq _ s H nx fr → out0 (st-eoutq s eq H) nx
    ; ecase₁′  = λ eq _ s H nx fr → out0 (st-ecase₁ lab s eq H) nx
    ; ecase₂′  = λ eq _ s H nx fr → out0 (st-ecase₂ s eq H) nx
    ; eapp′    = λ eq _ s H nx fr → out0 (st-eapp s eq H) nx
    ; epop′    = λ _ s H nx fr → out0 (st-epop s H) nx
    ; eword′   = λ eq _ s H nx fr → out0 (st-eword s eq H) nx
    }

  -- ★ THE LOCAL STEP THEOREM
  local-step : ∀ {T sh U sh′ U′} {c : Codeᴵ sh U} {r : Ret U T} {m n t} {c′ : Codeᴵ sh′ U′} {r′ : Ret U′ T} {m′ n′} {fs}
             → LdOk → Labelled
             → (st : StepI c r m n t c′ r′ m′ n′) (l : Local st) (s : Sub root c)
             → Here s m fs → AllocState.next-heap-ref (falloc fs) ≡ n → Fresh m fs
             → Out (succ st l s) fs n′ m′
  local-step ld lab st l s H nx fr = local-elim (step-cases ld lab) st l l s H nx fr
