-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.LinCore.NoHalt — plan 0.146 B1.5 (D443, D446): a run that gives a
-- value holds no halt (its trace's i/o is calls only). Split from
-- `AgreeRun` for its build time (each module under 60 s alone).
------------------------------------------------------------------------

{-# OPTIONS --guardedness #-}

open import Data.Nat using (ℕ)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.All.Properties using (++⁺)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import Once.Spec.Numerics using (TargetNum)
open import Once.IR.Semantics.Trace using (FFIAnswers)
open import Once.LinCore.Flat using (Base)

module Once.LinCore.NoHalt
  (fmt : TargetNum) (ans : FFIAnswers)
  (bw : Base → ℕ)
  where

open import Once.LinCore.Core fmt
open import Once.IR.Semantics.Trace using (T)
open import Once.LinCore.NbEPLinCore fmt ans
open import Once.LinCore.Events fmt ans bw
open import Once.LinCore.Values fmt bw
open import Once.LinCore.Free using (Weave)

------------------------------------------------------------------------
-- 1. A run that gives a value holds no halt
------------------------------------------------------------------------

IsCall : Io → Set
IsCall (io-call _ _ _) = ⊤
IsCall (io-halt _ _)   = ⊥

NoHalt : Trace → Set
NoHalt t = All IsCall (ios t)

private
  nh-++ : ∀ t₁ t₂ → NoHalt t₁ → NoHalt t₂ → NoHalt (t₁ ++ t₂)
  nh-++ t₁ t₂ a b = subst (All IsCall) (sym (ios-++ t₁ t₂)) (++⁺ a b)

  nh-[] : ∀ t → ios t ≡ [] → NoHalt t
  nh-[] t q = subst (All IsCall) (sym q) []

  path-nh : ∀ {X : Set} {b : T X} {t x} → OpPath b t (inj₁ x) → NoHalt t
  path-nh p-ret      = []
  path-nh (p-call p) = tt ∷ path-nh p

mutual
  gives-nh : ∀ {Γ} {ds : Defs Γ} {E A B} {f : Tm Γ E A B} {e v n w n′ t} → Run ds f e v n (gives w n′) t → NoHalt t
  gives-nh r-id = []
  gives-nh (r-∘ {t₁ = t₁} {t₂} rg (go-on rf)) = nh-++ t₁ t₂ (gives-nh′ rg) (gives-nh rf)
  gives-nh (r-⊗ {t₁ = t₁} {t₂} rf (go-on (fm-gives rg))) = nh-++ t₁ t₂ (gives-nh′ rf) (gives-nh rg)
  gives-nh r-ρ = []
  gives-nh r-ρ⁻ = []
  gives-nh r-λ = []
  gives-nh r-λ⁻ = []
  gives-nh r-α = []
  gives-nh r-α⁻ = []
  gives-nh r-swap = []
  gives-nh (r-dup {v = v} {n}) = nh-[] (proj₂ (proj₂ (copy v n))) (ios-copy v n)
  gives-nh (r-drop {v = v}) = nh-[] (freeAll v) (ios-freeAll v)
  gives-nh r-inl = []
  gives-nh r-inr = []
  gives-nh (r-case₁ r) = gives-nh r
  gives-nh (r-case₂ r) = gives-nh r
  gives-nh r-In = []
  gives-nh r-Outμ = []
  gives-nh r-clo = []
  gives-nh (r-app q r) = gives-nh r
  gives-nh (r-cata {t₁ = t₁} {t₂} rm (go-on ra)) = nh-++ t₁ t₂ (gives-nhM′ rm) (gives-nh ra)
  gives-nh (r-cata-reuse {t₁ = t₁} {t₂} rm (go-on (fm-gives rg))) = nh-++ t₁ t₂ (gives-nhM′ rm) (gives-nh rg)
  gives-nh (r-lend (fm-gives r)) = gives-nh r
  gives-nh (r-lift r) = gives-nh r
  gives-nh (r-fst r) = gives-nh r
  gives-nh (r-snd r) = gives-nh r
  gives-nh (r-caseE₁ r) = gives-nh r
  gives-nh (r-caseE₂ r) = gives-nh r
  gives-nh (r-out r) = gives-nh r
  gives-nh (r-copy {e = e} {n}) = nh-[] (proj₂ (proj₂ (copy e n))) (ios-copy e n)
  gives-nh (r-bapp q r) = gives-nh r
  gives-nh r-lam = []
  gives-nh r-lamω = []
  gives-nh (r-ev r) = gives-nh r
  gives-nh (r-bev r) = gives-nh r
  gives-nh (r-evω r) = gives-nh r
  gives-nh r-lamωᶜ = []
  gives-nh (r-evωᶜ r) = gives-nh r
  gives-nh (r-bevᶜ r) = gives-nh r
  gives-nh r-unf = []
  gives-nh (r-nout r) = gives-nh r
  gives-nh r-const = []
  gives-nh (r-op p) = path-nh p
  gives-nh (r-iter {t₁ = t₁} r (go-on done)) = nh-++ t₁ [] (gives-nh r) []
  gives-nh (r-iter {t₁ = t₁} {t₂} r (go-on (again rn))) = nh-++ t₁ t₂ (gives-nh r) (gives-nh rn)
  gives-nh (r-tmp r wv p) = subst (All IsCall) (sym (ios-weave wv)) (gives-nh r)

  -- a sub-run that gave (any outcome type)
  gives-nh′ : ∀ {Γ} {ds : Defs Γ} {E A B} {f : Tm Γ E A B} {e v n w n′ t} → Run ds f e v n (gives w n′) t → NoHalt t
  gives-nh′ = gives-nh

  gives-nhM′ : ∀ {Γ} {ds : Defs Γ} {E A F} {alg : Tm Γ E (LF∙ F A) A} {e : MV E} {G x n w n′ t}
             → RunMap ds F alg e G x n (gives w n′) t → NoHalt t
  gives-nhM′ (m-id r) = gives-nh r
  gives-nhM′ m-one = []
  gives-nhM′ m-b = []
  gives-nhM′ m-μ = []
  gives-nhM′ (m-inl (fm-gives r)) = gives-nhM′ r
  gives-nhM′ (m-inr (fm-gives r)) = gives-nhM′ r
  gives-nhM′ (m-pair {t₁ = t₁} {t₂} r (go-on (fm-gives r′))) = nh-++ t₁ t₂ (gives-nhM′ r) (gives-nhM′ r′)

------------------------------------------------------------------------
-- 2. An op's giving run: its contract path, under temporaries woven in.
-- Split once here (a small module), not at each use: matching a run at
-- `lop s` rules out every other constructor by index unification.
------------------------------------------------------------------------

op-elim : ∀ {Γ} {ds : Defs Γ} {E} {s : Sig} {e : MV E} {x : MV ⌜ sdom s ⌝}
          (P : MV ⌜ scod s ⌝ → ℕ → ℕ → Trace → Set)
        → (∀ {y₀ n t} → OpPath (opF s (toF (sdom s) (er x))) t (inj₁ y₀) → P (mvF (scod s) y₀) n n t)
        → (∀ {y n n′ t ts t′} → Run ds (lop s) e x n (gives y n′) t → P y n n′ t
             → Weave tmp t ts t′ → TPost (gives y n′) (tmps ts) → P y n n′ t′)
        → ∀ {y n n′ t} → Run ds (lop s) e x n (gives y n′) t → P y n n′ t
op-elim P po pt (r-op p)        = po p
op-elim P po pt (r-tmp r wv tp) = pt r (op-elim P po pt r) wv tp
