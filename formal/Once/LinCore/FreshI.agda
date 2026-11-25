-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.LinCore.FreshI — plan 0.146 B1.4b (D436, step 3): NO CELL PAST THE
-- COUNTER, from the image's invariant.
--
-- `HeldI.InvI`: the live cells are exactly those the frames hold, and no
-- cell at or past the counter `n` is live; a view sees only cells owned
-- below it. So no slot, view or operand of the current frame or of a saved
-- one mentions a cell at or past `n` — the freshness an allocation's lemma
-- asks (`StepPrim.Fresh`) and what keeps a saved frame's words standing
-- while the heap grows (D438).
------------------------------------------------------------------------

{-# OPTIONS --guardedness #-}

open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (m+n≡0⇒m≡0; m+n≡0⇒n≡0; ≤-trans; ≤-reflexive; n≤0⇒n≡0; m≤n+m; m≤m+n)
open import Data.List using (List; [])
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Nat.Tactic.RingSolver using (solve-∀)
open import Relation.Nullary using (¬_)
import Data.Empty
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)
open import Once.Spec.Numerics using (TargetNum)
open import Once.IR.Semantics.Trace using (FFIAnswers)
open import Once.LinCore.Flat using (Base)
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.SMCore using (StoredValue)

module Once.LinCore.FreshI
  (fmt : TargetNum) (ans : FFIAnswers)
  (bw : Base → ℕ)
  where

open import Once.LinCore.Core fmt
open import Once.LinCore.Flat using (Base; ⟦_⟧b)
open import Once.IR.Semantics.Trace using (T)
open import Once.LinCore.NbEPLinCore fmt ans
open import Once.LinCore.Events fmt ans bw
open import Once.LinCore.Values fmt bw
open import Once.LinCore.Code fmt bw using (Sh; Stk; []ˢ; _∷ˢ_; Slots; []ᵉ; vw; ln; Cfg; _∥_)
open import Once.LinCore.Keys fmt bw using (Univ)
open import Once.LinCore.Held fmt ans bw using (own; held; Owned; Within)
open import Once.LinCore.ImageRun fmt ans bw using (Ret; []ʳ; frm; _∷ⁱ_)
open import Once.LinCore.HeldI fmt ans bw using (InvI; InvH; module InvH; OwnR; EnvR; Sees′; SeesR; envR≤)
open import Once.LinCore.LowerSim fmt ans bw using (module Sim)

module Cells {FS : FrameSemantics} (U : Univ) (wordOf : ∀ {b} → ⟦ b ⟧b → StoredValue FS) where
  open Sim {FS} U wordOf using (cntE; cntS)

  private
    zero-of : ∀ {a} → (1 ≤ a → 1 ≤ 0) → a ≡ 0
    zero-of {zero}  f = refl
    zero-of {suc a} f = no (f (s≤s z≤n))
      where no : 1 ≤ 0 → suc a ≡ 0
            no ()

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
    cntE-zero es i (InvH.i-sees (InvI.i-h inv)) (m+n≡0⇒m≡0 (own es i) owned) envR0 ,
    trans (cntS-held os i) (m+n≡0⇒n≡0 (own es i) owned)
    where
      total : Owned (es ∥ os) i + OwnR r i ≡ 0
      total = trans (sym (InvH.i-exact (InvI.i-h inv) i)) (InvH.i-above (InvI.i-h inv) i le)
      owned : own es i + held os i ≡ 0
      owned = m+n≡0⇒m≡0 (own es i + held os i) total
      envR0 : EnvR r i ≡ 0
      envR0 = zero-of (λ l → ≤-trans l (≤-trans (envR≤ r i) (≤-reflexive (m+n≡0⇒n≡0 (own es i + held os i) total))))

  -- a cell the slots or the operands mention is held: owned in the frame
  -- or by the frames below
  seen-owned : ∀ {Es S U′ T} (es : Slots Es) (os : Stk S) (r : Ret U′ T) → Sees′ (EnvR r) es
             → ∀ j → 1 ≤ cntE es j + cntS os j → 1 ≤ (own es j + held os j) + OwnR r j
  seen-owned es os r s j p = pos (λ z → no0 (subst (1 ≤_) (both z) p))
    where
      no0 : 1 ≤ 0 → Data.Empty.⊥
      no0 ()
      pos : ∀ {a} → (a ≡ 0 → Data.Empty.⊥) → 1 ≤ a
      pos {zero}  f = ⊥-elim (f refl)
      pos {suc a} f = s≤s z≤n
      both : (own es j + held os j) + OwnR r j ≡ 0 → cntE es j + cntS os j ≡ 0
      both z = cong₂ _+_
        (cntE-zero es j s (m+n≡0⇒m≡0 (own es j) (m+n≡0⇒m≡0 (own es j + held os j) z))
                          (n≤0⇒n≡0 (≤-trans (envR≤ r j) (≤-reflexive (m+n≡0⇒n≡0 (own es j + held os j) z)))))
        (trans (cntS-held os j) (m+n≡0⇒n≡0 (own es j) (m+n≡0⇒m≡0 (own es j + held os j) z)))

  -- ★ D470: a μ cell on top shares its serial (its block) with no other
  -- cell the configuration mentions — what freeing it needs (`lOutμ-sim`'s `nd`)
  apart-top : ∀ {Es F S U′ T} {es : Slots Es} {i} {v : MV (LF∙ F (μt F))} {os : Stk S} {r : Ret U′ T} {n h}
            → InvI (es ∥ mmu i v ∷ˢ os) r n h
            → ∀ j → 1 ≤ cntE es j + (cnt v j + cntS os j) → ¬ serial j ≡ serial i
  apart-top {es = es} {i} {v} {os} {r} {h = h} inv j p e = two≰1 (≤-trans (s≤s oi) le)
    where
      O : Id → ℕ
      O x = (own es x + (cnt v x + held os x)) + OwnR r x
      rr : ∀ a d c b q → (a + ((d + c) + b)) + q ≡ d + ((a + (c + b)) + q)
      rr = solve-∀
      ex : ∀ x → h x ≡ δ i x + O x
      ex x = trans (InvH.i-exact (InvI.i-h inv) x) (rr (own es x) (δ i x) (cnt v x) (held os x) (OwnR r x))
      sv : 1 ≤ O j
      sv = seen-owned es (v ∷ˢ os) r (InvH.i-sees (InvI.i-h inv)) j p
      exi : h i ≡ suc (O i)
      exi = trans (ex i) (cong (_+ O i) (δ-same i))
      hj : 1 ≤ h j
      hj = subst (1 ≤_) (sym (ex j)) (≤-trans sv (m≤n+m (O j) (δ i j)))
      hi : 1 ≤ h i
      hi = subst (1 ≤_) (sym exi) (s≤s z≤n)
      oi : 1 ≤ O i
      oi = subst (λ x → 1 ≤ O x) (InvH.i-ser (InvI.i-h inv) j i hj hi e) sv
      le : suc (O i) ≤ 1
      le = subst (_≤ 1) exi (InvH.i-le1 (InvI.i-h inv) i)
      two≰1 : 2 ≤ 1 → Data.Empty.⊥
      two≰1 (s≤s ())

  -- ★ D470 (the core of `apart-top`): a cell `i` held once beside the rest `O`
  -- shares its serial with no cell of the rest
  apart-core : ∀ {sh U′ T} {m : Cfg sh} {r : Ret U′ T} {n h} → InvI m r n h
             → ∀ i (O : Id → ℕ) → (∀ x → h x ≡ δ i x + O x) → ∀ j → 1 ≤ O j → ¬ serial j ≡ serial i
  apart-core {h = h} inv i O ex j sv e = two≰1 (≤-trans (s≤s oi) le)
    where
      exi : h i ≡ suc (O i)
      exi = trans (ex i) (cong (_+ O i) (δ-same i))
      hj : 1 ≤ h j
      hj = subst (1 ≤_) (sym (ex j)) (≤-trans sv (m≤n+m (O j) (δ i j)))
      hi : 1 ≤ h i
      hi = subst (1 ≤_) (sym exi) (s≤s z≤n)
      oi : 1 ≤ O i
      oi = subst (λ x → 1 ≤ O x) (InvH.i-ser (InvI.i-h inv) j i hj hi e) sv
      le : suc (O i) ≤ 1
      le = subst (_≤ 1) exi (InvH.i-le1 (InvI.i-h inv) i)
      two≰1 : 2 ≤ 1 → Data.Empty.⊥
      two≰1 (s≤s ())

  -- ★ THE SAVED FRAMES: nothing at or past the counter either
  FreshR : ∀ {U′ T} → Ret U′ T → ℕ → Set
  FreshR []ʳ             n = Data.Unit.⊤
    where import Data.Unit
  FreshR (frm k es os r) n = (∀ i → n ≤ serial i → cntE es i ≡ 0 × cntS os i ≡ 0) × FreshR r n
  FreshR (k ∷ⁱ r)        n = FreshR r n

  -- ★ D471: the saved frames hold no cell whose block is in `fl` (a run's frees)
  AwayR : ∀ {U′ T} → Ret U′ T → List ℕ → Set
  AwayR []ʳ             fl = Data.Unit.⊤
    where import Data.Unit
  AwayR (frm k es os r) fl = (∀ i → serial i ∈ fl → cntE es i ≡ 0 × cntS os i ≡ 0) × AwayR r fl
  AwayR (k ∷ⁱ r)        fl = AwayR r fl

  away-[] : ∀ {U′ T} (r : Ret U′ T) → AwayR r []
  away-[] []ʳ             = Data.Unit.tt
    where import Data.Unit
  away-[] (frm k es os r) = (λ i ()) , away-[] r
  away-[] (k ∷ⁱ r)        = away-[] r

  -- from the frames' owned cells: a cell a slot or a stack value mentions is owned in the frames
  away-of : ∀ {U′ T} (r : Ret U′ T) {fl} → SeesR r → (∀ i → 1 ≤ OwnR r i → ¬ serial i ∈ fl) → AwayR r fl
  away-of []ʳ             _        _  = Data.Unit.tt
    where import Data.Unit
  away-of (frm k es os r) (s , sr) nf =
    (λ i m → zero-of (λ l → ⊥-elim (nf i (seen-owned es os r s i (lft l)) m)) ,
             zero-of (λ l → ⊥-elim (nf i (seen-owned es os r s i (rgt l)) m))) ,
    away-of r sr (λ i l → nf i (≤-trans l (m≤n+m (OwnR r i) (own es i + held os i))))
    where
      lft : ∀ {a b} → 1 ≤ a → 1 ≤ a + b
      lft {a} {b} l = ≤-trans l (m≤m+n a b)
      rgt : ∀ {a b} → 1 ≤ b → 1 ≤ a + b
      rgt {a} {b} l = ≤-trans l (m≤n+m b a)
  away-of (k ∷ⁱ r)        sr       nf = away-of r sr nf

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
    freshR-go r (InvH.i-seesR (InvI.i-h inv)) (λ i le → m+n≡0⇒n≡0 (Owned m i) (trans (sym (InvH.i-exact (InvI.i-h inv) i)) (InvH.i-above (InvI.i-h inv) i le)))
