-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- OCP-0009 · EXAMPLES — ★ THE AGREEMENT ORACLE (PLAN-EVAL E1): the
-- environment evaluator (`Algorithm/NbE`, untrusted) gives the SAME normal
-- form as the certified one (`Algorithm/Eval`: every step a `_⟶_`
-- constructor, the result `Nf`).
--
-- The corpus has one row (at least) per computation rule — both sides of
-- every guard (`pw?`, `stkA?`, `stkC?`, the `var vz` motives), stuck
-- eliminators, congruences under binders, open terms (three free
-- variables) — plus programs: System T Ackermann (nested `natrec`, higher
-- order), a recursive datatype eliminated through `ielim`/`dih`, and lazy δ.
--
-- Two checks per corpus, each a list of the FAILING row indices:
--   · `bad`   — rows where the two evaluators disagree;
--   · `inert` — rows that are already normal (a row that does not compute
--               tests nothing: the non-triviality control).
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.NbEAgree where
open import normalizer.Syntax.Types using ( _≡_; refl )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import Agda.Builtin.Bool using ( Bool; true; false )
open import Agda.Builtin.List using ( List; []; _∷_ )
open import DirectedHoTT.Spec.Syntax
open import DirectedHoTT.Lib.NatNum using ( num )
open import DirectedHoTT.Algorithm.DecEq using ( _≟Tm_; _≟Ty_; yes; no )
open import DirectedHoTT.Algorithm.Eval using ( eval; evalᵀ; nfd; out; nfdᵀ; outᵀ )
open import DirectedHoTT.Algorithm.NbE using ( nbe; nbeᵀ )

private
  Γ₃ : Cx
  Γ₃ = ((ε ∙) ∙) ∙

  fuel : ℕ
  fuel = 100000

  -- the certified evaluator's normal form
  nfE : {Γ : Cx} → RTm Γ → RTm Γ
  nfE t with eval fuel t
  ... | nfd u _ _ = u
  ... | out u _   = u

  nfEᵀ : {Γ : Cx} → RTy Γ → RTy Γ
  nfEᵀ A with evalᵀ fuel A
  ... | nfdᵀ B _ _ = B
  ... | outᵀ B _   = B

  same : {Γ : Cx} → RTm Γ → RTm Γ → Bool
  same t u with t ≟Tm u
  ... | yes _ = true
  ... | no  _ = false

  sameᵀ : {Γ : Cx} → RTy Γ → RTy Γ → Bool
  sameᵀ A B with A ≟Ty B
  ... | yes _ = true
  ... | no  _ = false

  not : Bool → Bool
  not true  = false
  not false = true

  -- the indices (from i) of the rows failing a test
  fails : {X : Set} → (X → Bool) → ℕ → List X → List ℕ
  fails p i []       = []
  fails p i (x ∷ xs) with p x
  ... | true  = fails p (suc i) xs
  ... | false = i ∷ fails p (suc i) xs

  -- free variables of Γ₃, and a redex around a stuck term
  x₀ x₁ x₂ : {Γ : Cx} → RTm (((Γ ∙) ∙) ∙)
  x₀ = var vz
  x₁ = var (vs vz)
  x₂ = var (vs (vs vz))

  I : {Γ : Cx} → RTm Γ → RTm Γ
  I t = app (lam (var vz)) t

  v0 : {Γ : Cx} → RTm (Γ ∙)
  v0 = var vz
  v1 : {Γ : Cx} → RTm ((Γ ∙) ∙)
  v1 = var (vs vz)
  v2 : {Γ : Cx} → RTm (((Γ ∙) ∙) ∙)
  v2 = var (vs (vs vz))
  v3 : {Γ : Cx} → RTm ((((Γ ∙) ∙) ∙) ∙)
  v3 = var (vs (vs (vs vz)))

  ΠNN : {Γ : Cx} → RTm Γ
  ΠNN = ⌜Π⌝ ⌜Nat⌝ ⌜Nat⌝

  -- a motive `⌜Hom⌝ c a m` with an arbitrary endpoint m (tr-J-*)
  homM : {Γ : Cx} → RTm (Γ ∙)
  homM = ⌜Hom⌝ ⌜Nat⌝ v0 v0

  -- System T Ackermann: ack m = natrec succ (λ pred rec. λ n. natrec (rec 1) (λ _ r. rec r) n) m
  ack : {Γ : Cx} → RTm Γ
  ack = lam (natrec (lam (nsuc v0))
                    (lam (natrec (app v1 (num 1)) (app v3 v0) v0))
                    v0)

  -- a Nat-like datatype: tag 0 = zero (no fields), tag 1 = suc (one
  -- recursive field at the same index); `count` folds it back to Nat
  NatD : {Γ : Cx} → RTm Γ
  NatD = lam (dσ (⌜Fin⌝ (num 2)) (lam (fcase v0 dι (dρ v2 dι))))
  zeroN : {Γ : Cx} → RTm Γ
  zeroN = con (pair fzero unit)
  sucN : {Γ : Cx} → RTm Γ → RTm Γ
  sucN t = con (pair (fsuc fzero) (pair t unit))
  -- method: λ i p h. case (fst p) of 0 ↦ 0 ; 1 ↦ suc (fst h)
  count : {Γ : Cx} → RTm Γ
  count = lam (lam (lam (fcase (fst v1) nzero (nsuc (fst v1)))))

------------------------------------------------------------------------
-- ★ TERMS
------------------------------------------------------------------------

rows : List (RTm Γ₃)
rows =
  -- β, projections, split
    app (lam (nsuc v0)) x₀
  ∷ fst (pair x₀ x₁) ∷ snd (pair x₀ x₁)
  ∷ psplit (pair v0 v1) (pair x₀ x₁)
  ∷ lam (app (lam v0) v0)                                         -- under a binder
  ∷ ⌜Π⌝ (I ⌜Nat⌝) (I v0)
  -- ordtr: every rule, and stuck
  ∷ ordtr nzero x₀ x₁ x₂ x₂
  ∷ ordtr (num 1) nzero nzero x₀ x₁
  ∷ ordtr (num 1) (num 1) nzero x₀ x₁
  ∷ ordtr (num 1) nzero (num 1) x₀ x₁
  ∷ ordtr (num 2) (num 1) (num 1) x₀ x₁
  ∷ I (ordtr x₀ x₁ x₂ x₀ x₁)
  -- tr-J at every J-able code, tr-J-Hom (stkA?, incl. ⌜Nat⌝), stuck
  ∷ tr homM (hrefl ⌜base⌝ x₀) x₂
  ∷ tr homM (hrefl (⌜Σ⌝ ⌜Nat⌝ ⌜Nat⌝) x₀) x₂
  ∷ tr homM (hrefl ⌜Unit⌝ x₀) x₂
  ∷ tr homM (hrefl (⌜Id⌝ ⌜Nat⌝ x₀ x₁) x₀) x₂
  ∷ tr homM (hrefl (⌜IMu⌝ x₀ x₁ x₂) x₀) x₂
  ∷ tr homM (hrefl (⌜Fin⌝ x₀) x₀) x₂
  ∷ tr homM (hrefl (⌜Hom⌝ ⌜base⌝ x₀ x₁) x₂) x₂
  ∷ tr homM (hrefl (⌜Hom⌝ ⌜Nat⌝ x₀ x₁) x₂) x₂
  ∷ I (tr homM (hrefl (⌜Hom⌝ x₀ x₁ x₂) x₀) x₂)
  -- tr-pw (at ⌜Π⌝, and through ⌜Hom⌝), tr-taut, stuck
  ∷ tr (⌜Hom⌝ ΠNN v1 v0) (lam (nsuc v0)) x₁
  ∷ tr (⌜Hom⌝ (⌜Hom⌝ ΠNN v1 v1) v1 v0) (lam v0) x₁
  ∷ tr v0 (lam (nsuc v0)) x₀
  ∷ I (tr v0 x₀ x₁)
  ∷ I (tr (⌜Hom⌝ ⌜Nat⌝ v1 v0) (lam v0) x₁)                       -- not pw: stuck
  -- hrefl: pw (⌜Π⌝, nested ⌜Π⌝, through ⌜Hom⌝), the order's, stuck
  ∷ hrefl ΠNN x₀
  ∷ hrefl (⌜Π⌝ ⌜Nat⌝ ΠNN) (lam (lam v0))
  ∷ hrefl (⌜Hom⌝ ΠNN x₀ x₁) x₂
  ∷ hrefl ⌜Nat⌝ (num 2)
  ∷ I (hrefl ⌜Nat⌝ x₀)
  -- ap: J-able (stkC?), through ⌜Hom⌝ ⌜Nat⌝ (stkA? ⌜Nat⌝), stuck at ⌜Nat⌝
  ∷ ap ⌜Nat⌝ (nsuc v0) (hrefl ⌜base⌝ x₀)
  ∷ ap ⌜base⌝ v0 (hrefl (⌜Hom⌝ ⌜Nat⌝ x₀ x₁) x₂)
  ∷ I (ap ⌜Nat⌝ v0 (hrefl ⌜Nat⌝ (nsuc x₀)))
  ∷ jsub v0 (idrefl ⌜Nat⌝ x₀) x₁
  -- natrec, and System T Ackermann (higher order, nested natrec)
  ∷ natrec x₀ (nsuc v0) (num 3)
  ∷ I (natrec x₀ (nsuc v0) x₁)
  ∷ app (app ack (num 2)) (num 2)
  ∷ app (app ack (num 1)) x₀                                      -- open: stuck inside
  -- datatypes: ielim through dih (σ, ρ, ι), the payload
  ∷ ielim NatD x₀ count zeroN
  ∷ ielim NatD x₀ count (sucN (sucN zeroN))
  ∷ ielim NatD x₀ (lam (lam (lam v0))) (sucN zeroN)             -- the IH itself
  ∷ I (ielim NatD x₀ count x₁)
  ∷ dpay x₀ x₁ dι
  ∷ dpay x₀ x₁ (dσ ⌜Nat⌝ (lam dι))
  ∷ dpay x₀ x₁ (dρ x₂ dι)
  ∷ app NatD nzero
  ∷ I (dih x₀ x₁ x₂ x₀)
  -- Fin
  ∷ fcase (fsuc fzero) x₀ (nsuc v0)
  ∷ fcase fzero x₀ x₁
  ∷ I (fcase0 x₀)
  -- lazy δ
  ∷ app (ref 7 (lam (nsuc v0))) (num 1)
  ∷ ref 3 nzero
  ∷ app (ref 4 ack) (num 1)
  ∷ []

terms-agree : fails (λ t → same (nbe fuel t) (nfE t)) 0 rows ≡ []
terms-agree = refl

terms-compute : fails (λ t → not (same t (nbe fuel t))) 0 rows ≡ []
terms-compute = refl

------------------------------------------------------------------------
-- ★ TYPES
------------------------------------------------------------------------

rowsᵀ : List (RTy Γ₃)
rowsᵀ =
    El ⌜base⌝
  ∷ El (⌜Π⌝ ⌜Nat⌝ (⌜Fin⌝ v0))
  ∷ El (⌜Σ⌝ ⌜Nat⌝ ⌜Unit⌝)
  ∷ El (⌜Hom⌝ ⌜Nat⌝ nzero x₀)                                     -- then Hom-Nat-z
  ∷ El (⌜Hom⌝ ⌜Nat⌝ (num 2) (num 1))                              -- Hom-Nat-ss, -sz
  ∷ El (⌜Id⌝ ⌜Nat⌝ x₀ x₁)
  ∷ El (⌜IMu⌝ x₀ x₁ x₂)
  ∷ El (⌜Fin⌝ x₀)
  ∷ El ⌜Unit⌝
  ∷ El (I x₀)
  ∷ Hom U ⌜Nat⌝ ⌜Unit⌝
  ∷ Hom (Π Nat Nat) x₀ x₁
  ∷ Hom (El ΠNN) x₀ x₁
  ∷ Hom Nat (I x₀) x₁
  ∷ DIh x₀ (Id Nat v1 v0) dι x₂
  ∷ DIh x₀ (Id Nat v1 v0) (dσ ⌜Nat⌝ (lam dι)) x₂
  ∷ DIh x₀ (Id Nat v1 v0) (dρ x₁ dι) x₂
  ∷ DIh x₀ (Id Nat v1 v0) (app NatD x₁) (pair (fsuc fzero) x₂)
  ∷ Π (El (I ⌜Nat⌝)) (El (I v0))
  ∷ []

types-agree : fails (λ A → sameᵀ (nbeᵀ fuel A) (nfEᵀ A)) 0 rowsᵀ ≡ []
types-agree = refl

types-compute : fails (λ A → not (sameᵀ A (nbeᵀ fuel A))) 0 rowsᵀ ≡ []
types-compute = refl

-- ★ a value, not only an agreement: Ackermann(2, 2) = 7
ack-2-2 : nbe {Γ₃} fuel (app (app ack (num 2)) (num 2)) ≡ num 7
ack-2-2 = refl
