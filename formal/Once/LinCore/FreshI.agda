-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.LinCore.FreshI — plan 0.146 B1.4b (D417, step 3): NO CELL PAST THE
-- COUNTER, from the image's invariant.
--
-- `HeldI.InvI`: the live cells are exactly those the frames hold, and no
-- cell at or past the counter `n` is live; a view sees only cells owned
-- below it. So no slot, view or operand of the current frame or of a saved
-- one mentions a cell at or past `n` — the freshness an allocation's lemma
-- asks (`StepPrim.Fresh`) and what keeps a saved frame's words standing
-- while the heap grows (D419).
------------------------------------------------------------------------

{-# OPTIONS --guardedness #-}

open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (m+n≡0⇒m≡0; m+n≡0⇒n≡0; ≤-trans; ≤-reflexive)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Once.Spec.Numerics using (TargetNum)
open import Once.IR.Semantics.Trace using (FFIAnswers)
open import Once.LinCore.Flat using (Base)
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.SMCore using (StoredValue)

module Once.LinCore.FreshI
  (fmt : TargetNum) (ans : FFIAnswers)
  (bw : Base → ℕ)
  where

open import Once.LinCore.NbEPLinCore fmt ans
open import Once.LinCore.Events fmt ans bw
open import Once.LinCore.Machine fmt ans bw using (Sh; Stk; []ˢ; _∷ˢ_; Slots; []ᵉ; vw; ln; Cfg; _∥_)
open import Once.LinCore.Keys fmt ans bw using (Univ)
open import Once.LinCore.Held fmt ans bw using (own; held; Owned; Within)
open import Once.LinCore.ImageRun fmt ans bw using (Ret; []ʳ; frm; _∷ⁱ_)
open import Once.LinCore.HeldI fmt ans bw using (InvI; OwnR; EnvR; Sees′; SeesR; envR≤)
open import Once.LinCore.LowerSim fmt ans bw using (module Sim)

module Cells {FS : FrameSemantics} (U : Univ) (wordOf : ∀ {b} → ⟦ b ⟧b → StoredValue FS) where
  open Sim {FS} U wordOf using (cntE; cntS)

  private
    zero-of : ∀ {a} → (1 ≤ a → 1 ≤ 0) → a ≡ 0
    zero-of {zero}  f = refl
    zero-of {suc a} f with f (s≤s z≤n)
    ... | ()

  -- an operand stack's cells are the cells it holds
  cntS-held : ∀ {S} (os : Stk S) i → cntS os i ≡ held os i
  cntS-held []ˢ       i = refl
  cntS-held (v ∷ˢ os) i = cong (cnt v i +_) (cntS-held os i)

  -- ★ slots that own nothing at `i`, and see only cells owned below them,
  -- mention nothing at `i`
  cntE-zero : ∀ {Es O} (es : Slots Es) i → Sees′ O es → own es i ≡ 0 → O i ≡ 0 → cntE es i ≡ 0
  cntE-zero []ᵉ         i _        _  _  = refl
  cntE-zero {O = O} (vw e es) i (w , s) ow oz =
    trans (cong (_+ cntE es i) (zero-of (λ l → subst (1 ≤_) (trans (cong (_+ O i) ow) oz) (w i l))))
          (cntE-zero es i s ow oz)
  cntE-zero {O = O} (ln e x es) i (w , s) ow oz =
    trans (cong₃ (zero-of (λ l → subst (1 ≤_) (trans (cong (_+ O i) (m+n≡0⇒n≡0 (cnt x i) ow)) oz) (w i l)))
                 (m+n≡0⇒m≡0 (cnt x i) ow))
          (cntE-zero es i s (m+n≡0⇒n≡0 (cnt x i) ow) oz)
    where
      cong₃ : ∀ {a b} → a ≡ 0 → b ≡ 0 → (a + b) + cntE es i ≡ cntE es i
      cong₃ refl refl = refl

  -- ★ THE CURRENT CONFIGURATION: nothing at or past the counter
  fresh-cfg : ∀ {sh U′ T} {m : Cfg sh} {r : Ret U′ T} {n h} → InvI m r n h
            → ∀ i → n ≤ serial i → cntE (Cfg.envs m) i ≡ 0 × cntS (Cfg.opds m) i ≡ 0
  fresh-cfg {m = es ∥ os} {r} inv i le =
    cntE-zero es i (InvI.i-sees inv) (m+n≡0⇒m≡0 (own es i) owned) envR0 ,
    trans (cntS-held os i) (m+n≡0⇒n≡0 (own es i) owned)
    where
      total : Owned (es ∥ os) i + OwnR r i ≡ 0
      total = trans (sym (InvI.i-exact inv i)) (InvI.i-above inv i le)
      owned : own es i + held os i ≡ 0
      owned = m+n≡0⇒m≡0 (own es i + held os i) total
      envR0 : EnvR r i ≡ 0
      envR0 = zero-of (λ l → ≤-trans l (≤-trans (envR≤ r i) (≤-reflexive (m+n≡0⇒n≡0 (own es i + held os i) total))))

  -- ★ THE SAVED FRAMES: nothing at or past the counter either
  FreshR : ∀ {U′ T} → Ret U′ T → ℕ → Set
  FreshR []ʳ             n = Data.Unit.⊤
    where import Data.Unit
  FreshR (frm k es os r) n = (∀ i → n ≤ serial i → cntE es i ≡ 0 × cntS os i ≡ 0) × FreshR r n
  FreshR (k ∷ⁱ r)        n = FreshR r n

  private
    freshR-go : ∀ {U′ T} (r : Ret U′ T) {n} → SeesR r → (∀ i → n ≤ serial i → OwnR r i ≡ 0) → FreshR r n
    freshR-go []ʳ             _          _ = Data.Unit.tt
      where import Data.Unit
    freshR-go (frm k es os r) (s , sr) z =
      (λ i le → let zi = z i le ; o0 = m+n≡0⇒m≡0 (own es i + held os i) zi in
                cntE-zero es i s (m+n≡0⇒m≡0 (own es i) o0)
                  (zero-of (λ l → ≤-trans l (≤-trans (envR≤ r i) (≤-reflexive (m+n≡0⇒n≡0 (own es i + held os i) zi))))) ,
                trans (cntS-held os i) (m+n≡0⇒n≡0 (own es i) o0)) ,
      freshR-go r sr (λ i le → m+n≡0⇒n≡0 (own es i + held os i) (z i le))
    freshR-go (k ∷ⁱ r)        sr         z = freshR-go r sr z

  fresh-ret : ∀ {sh U′ T} {m : Cfg sh} {r : Ret U′ T} {n h} → InvI m r n h → FreshR r n
  fresh-ret {m = m} {r} inv =
    freshR-go r (InvI.i-seesR inv) (λ i le → m+n≡0⇒n≡0 (Owned m i) (trans (sym (InvI.i-exact inv i)) (InvI.i-above inv i le)))
