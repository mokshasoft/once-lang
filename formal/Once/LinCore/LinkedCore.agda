-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.LinCore.LinkedCore — plan 0.146 B1.5 (D431): MASTER'S LINKEDNESS AT
-- THE CORE. A linked IR program (`Denotation.Program.LinkedProgram`: every
-- SigOp leaf `Declared` by the interpretation) translates (`FromIR`, then
-- `Pass.tr`) to a core program whose universe's ops (`Keys.ops`) are all
-- declared: the translations are structural, and each keeps an IR's ops
-- among the ops it had (FromIR adds only the halting `unlinked` op, which
-- owes nothing).
------------------------------------------------------------------------

{-# OPTIONS --guardedness #-}

open import Data.Nat using (ℕ)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁻)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; subst₂)
open import Once.Spec.Numerics using (TargetNum)
open import Once.IR.Semantics.Trace using (FFIAnswers)
open import Once.LinCore.Flat using (Base)
import Once.LinCore.Pass

module Once.LinCore.LinkedCore (fmt : TargetNum) (ans : FFIAnswers) (bw : Base → ℕ) where

open import Once.LinCore.NbEPLinCore fmt ans
module P = Once.LinCore.Pass fmt ans
open import Once.LinCore.Keys fmt ans bw using (Got; ps; tmGot; defsGot; ops; univ)

------------------------------------------------------------------------
-- 1. THE PASS IR'S OPS, and the core's are among them
------------------------------------------------------------------------

module _ (D : Sig → Set) where
  OpsOK : ∀ {Γ A B} → P.IR Γ A B → Set
  OpsOK (g P.∘ f)        = OpsOK g × OpsOK f
  OpsOK P.⟨ f , g ⟩      = OpsOK f × OpsOK g
  OpsOK (P.case f g)     = OpsOK f × OpsOK g
  OpsOK (P.curry g f γ)  = OpsOK f
  OpsOK (P.Cata F alg)   = OpsOK alg
  OpsOK (P.Ana F c φ)    = OpsOK c
  OpsOK (P.Iter body φ)  = OpsOK body
  OpsOK (P.SigOp s)      = D s
  {-# CATCHALL #-}
  OpsOK _                = ⊤

  data ProgOK : ∀ {Γ} → P.Prog Γ → Set where
    ε   : ProgOK P.ε
    _▹_ : ∀ {Γ g A B} {Q : P.Prog Γ} {f : P.IR Γ A B} {γ : P.GdIR Γ g f} → ProgOK Q → OpsOK f → ProgOK (Q P.▹ f ∣ γ)

  private
    either : ∀ {s : Sig} xs {ys} → s ∈ xs ++ ys → (s ∈ xs → D s) → (s ∈ ys → D s) → D s
    either xs m l r = case′ (∈-++⁻ xs m)
      where
        case′ : _ → _
        case′ (inj₁ a) = l a
        case′ (inj₂ b) = r b

  -- a layer's map names the ops its function does
  mapL-ps : ∀ {Γ} (ds : Defs Γ) G {E A B} (f : Tm Γ E A B) → (∀ {s} → s ∈ ps (tmGot ds f) → D s)
          → ∀ {s} → s ∈ ps (tmGot ds (P.mapL G f)) → D s
  mapL-ps ds Idf      f k m = k m
  mapL-ps ds Kone     f k ()
  mapL-ps ds Kzero    f k ()
  mapL-ps ds (Kb b)   f k ()
  mapL-ps ds (Kμ G)   f k ()
  mapL-ps ds (G ⊕f H) f k m = either (ps (tmGot ds (P.mapL G f))) m (mapL-ps ds G f k) (mapL-ps ds H f k)
  mapL-ps ds (G ⊗f H) f k m = either (ps (tmGot ds (P.mapL G f))) m (mapL-ps ds G f k) (mapL-ps ds H f k)

  -- Lambek's inverse names none
  inco-ps : ∀ {Γ} (ds : Defs Γ) F → ∀ {s} → s ∈ ps (tmGot ds (P.inco {Γ} F)) → D s
  inco-ps ds F m =
    either (ps (tmGot ds (P.mapL F linr))) m (mapL-ps ds F linr (λ ()))
      (λ m₁ → either (ps (tmGot ds (P.mapL F linr))) m₁ (mapL-ps ds F linr (λ ())) (λ ()))

  -- ★ the core term's ops are its IR's
  tr-ps : ∀ {Γ} (ds : Defs Γ) {A B} (g : P.IR Γ A B) → OpsOK g → ∀ {s} → s ∈ ps (tmGot ds (P.tr g)) → D s
  tr-ps ds P.id o ()
  tr-ps ds (g P.∘ f) (og , of) m = either (ps (tmGot ds (P.tr g))) m (tr-ps ds g og) (tr-ps ds f of)
  tr-ps ds P.⟨ f , g ⟩ (of , og) m =
    either (ps (tmGot ds (P.tr f)) ++ ps (tmGot ds (P.tr g))) m
      (λ m′ → either (ps (tmGot ds (P.tr f))) m′ (tr-ps ds f of) (tr-ps ds g og)) (λ ())
  tr-ps ds P.fst o ()
  tr-ps ds P.snd o ()
  tr-ps ds P.inl o ()
  tr-ps ds P.inr o ()
  tr-ps ds (P.case f g) (of , og) m = either (ps (tmGot ds (P.tr f))) m (tr-ps ds f of) (tr-ps ds g og)
  tr-ps ds P.terminal o ()
  tr-ps ds P.initial o ()
  tr-ps ds (P.curry g f γ) o m = either (ps (tmGot ds (P.tr f))) m (tr-ps ds f o) (λ ())
  tr-ps ds P.apply o ()
  tr-ps ds (P.In F) o ()
  tr-ps ds (P.out-μ F) o ()
  tr-ps ds (P.Cata F alg) o m = either (ps (tmGot ds (P.tr alg))) m (tr-ps ds alg o) (λ ())
  tr-ps ds (P.Ana F c φ) o m = either (ps (tmGot ds (P.tr c)) ++ []) m (λ m′ → either (ps (tmGot ds (P.tr c))) m′ (tr-ps ds c o) (λ ())) (λ ())
  tr-ps ds (P.Out F) o ()
  tr-ps ds (P.in-ν F) o m =
    either (ps (tmGot ds (P.inco F)) ++ []) m (λ m₁ → either (ps (tmGot ds (P.inco F))) m₁ (inco-ps ds F) (λ ())) (λ ())
  tr-ps ds (P.Iter body φ) o m = either (ps (tmGot ds (P.tr body))) m (tr-ps ds body o) (λ ())
  tr-ps ds (P.const v) o ()
  tr-ps ds (P.SigOp s) o (here refl) = o
  tr-ps ds (P.Call p) o ()

  -- the table's
  defs-ps : ∀ {Γ} (Q : P.Prog Γ) → ProgOK Q → ∀ {s} → s ∈ ps (defsGot (P.trP Q)) → D s
  defs-ps P.ε ε ()
  defs-ps (Q P.▹ f ∣ γ) (oq ▹ of) m =
    either (ps (defsGot (P.trP Q))) m (defs-ps Q oq)
      (λ m′ → either (ps (tmGot (P.trP Q) (P.tr f))) m′ (tr-ps (P.trP Q) f of) (λ ()))

  -- ★ a program's universe's ops
  univ-ps : ∀ {Γ} (Q : P.Prog Γ) (f : P.IR Γ One One) → ProgOK Q → OpsOK f
          → ∀ {s} → s ∈ ops (univ (P.trP Q) (P.tr f)) → D s
  univ-ps Q f oq of m = either (ps (defsGot (P.trP Q))) m (defs-ps Q oq) (tr-ps (P.trP Q) f of)
