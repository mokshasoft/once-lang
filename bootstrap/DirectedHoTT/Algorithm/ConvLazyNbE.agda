-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- OCP-0009 · dHoTT — ★ LAZY CONVERSION BY THE ENVIRONMENT EVALUATOR,
-- certified (PLAN-EVAL E3, the checker's side).
--
-- `Algorithm/ConvLazy`'s strategy — syntactic equality first; else both
-- sides weak-head and compared; else, at the same head, the fields —
-- with its weak-head engine replaced: a term's weak-head form is the
-- READING of its value (`⌊ force (eval t) ⌋`), a type's the reading of
-- its type value, convertible with the input by `S-eval`/`T-eval`.  So an
-- equal subterm (the quoted signature's decoder, say) is never unfolded,
-- and an unequal one is unfolded by environments, not substitution
-- chains.  `just` a proof or `nothing`; the deciding procedures follow.
--
-- `--safe`, ZERO postulates.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
open import DirectedHoTT.Spec.Syntax using ( KSig; _<ˢ_; _<ˢ?_ )
open import DirectedHoTT.Algorithm.NbE.Value using ( Tbl )
import DirectedHoTT.Algorithm.NbE.TblOK as TO
module DirectedHoTT.Algorithm.ConvLazyNbE (𝒮 : KSig) (tbl : Tbl) (tok : TO.TblOK 𝒮 tbl) where
open import normalizer.Syntax.Types using ( _≡_; refl; sym; trans; Σ; _,_ )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import Agda.Builtin.Maybe using ( Maybe; just; nothing )
open import DirectedHoTT.Spec.Syntax
open import DirectedHoTT.Spec.Reduction 𝒮 hiding ( _×_; _,,_; ⌊_⌋ )
open import DirectedHoTT.Algorithm.ConvLazy 𝒮 using ( cong≅; cong≅ᵗ; cong≅ᵀ )
open import DirectedHoTT.Algorithm.DecEq using ( Dec; yes; no; _≟Tm_; _≟Ty_ )
open import DirectedHoTT.Algorithm.NbE tbl using ( eval; evalᵀ; force; ⌊_⌋; ⌊_⌋ᵀ; ⌊_⌋ᵉ; idEnv; len; lvl )
open import DirectedHoTT.Algorithm.NbESound 𝒮 tbl tok using ( S-eval; S-force; idEnv-read; sc-idEnv )
open import DirectedHoTT.Algorithm.NbESoundTy 𝒮 tbl tok using ( T-eval )

private
  variable
    Γ Δ : Cx

------------------------------------------------------------------------
-- 1. ★ Weak-head by evaluation: the reading of the value.
------------------------------------------------------------------------

private
  id-sub : (t : RTm Γ) → t ≡ subTm (⌊ idEnv Γ ⌋ᵉ (lvl Γ)) t
  id-sub {Γ} t = trans (sym (subTm-id t)) (subTm-cong (λ x → sym (idEnv-read Γ x)) t)

  id-subᵀ : (A : RTy Γ) → A ≡ subTy (⌊ idEnv Γ ⌋ᵉ (lvl Γ)) A
  id-subᵀ {Γ} A = trans (sym (subTy-id A)) (subTy-cong (λ x → sym (idEnv-read Γ x)) A)

  ≡→≅ : {t u : RTm Γ} → t ≡ u → t ≅ u
  ≡→≅ refl = crfl

  ≡→≅ᵀ : {A B : RTy Γ} → A ≡ B → A ≅ᵀ B
  ≡→≅ᵀ refl = crflᵀ

whnfN : ℕ → (t : RTm Γ) → Σ (RTm Γ) (t ≅_)
whnfN {Γ} k t =
  ⌊ force k (eval k (len Γ) (idEnv Γ) t) ⌋ (lvl Γ) ,
  ctrn (≡→≅ (id-sub t))
       (ctrn (S-eval k (len Γ) (idEnv Γ) t (lvl Γ) (sc-idEnv Γ)) (S-force k (eval k (len Γ) (idEnv Γ) t) (lvl Γ)))

whnfNᵀ : ℕ → (A : RTy Γ) → Σ (RTy Γ) (A ≅ᵀ_)
whnfNᵀ {Γ} k A =
  ⌊ evalᵀ k (len Γ) (idEnv Γ) A ⌋ᵀ (lvl Γ) ,
  ctrnᵀ (≡→≅ᵀ (id-subᵀ A)) (T-eval k (len Γ) (idEnv Γ) A (lvl Γ) (sc-idEnv Γ))

------------------------------------------------------------------------
-- 2. ★ LAZY CONVERSION — `just` a proof, or `nothing`.
------------------------------------------------------------------------

private
  both : {A B C : Set} → Maybe A → Maybe B → (A → B → C) → Maybe C
  both (just a) (just b) k = just (k a b)
  both _        _        k = nothing

  back : {t t' u u' : RTm Γ} → t ≅ t' → u ≅ u' → t' ≅ u' → t ≅ u
  back ct cu c = ctrn ct (ctrn c (csym cu))

  backᵀ : {A A' B B' : RTy Γ} → A ≅ᵀ A' → B ≅ᵀ B' → A' ≅ᵀ B' → A ≅ᵀ B
  backᵀ ca cb c = ctrnᵀ ca (ctrnᵀ c (csymᵀ cb))

  mapM : {A B : Set} → (A → B) → Maybe A → Maybe B
  mapM f (just a) = just (f a)
  mapM f nothing  = nothing

convTmN : ℕ → (t u : RTm Γ) → Maybe (t ≅ u)
convTyN : ℕ → (A B : RTy Γ) → Maybe (A ≅ᵀ B)
structTmN : ℕ → (t u : RTm Γ) → Maybe (t ≅ u)
structTyN : ℕ → (A B : RTy Γ) → Maybe (A ≅ᵀ B)

convTmN zero t u with t ≟Tm u
... | yes refl = just crfl
... | no _     = nothing
convTmN (suc k) t u with t ≟Tm u
... | yes refl = just crfl
... | no _ with whnfN k t | whnfN k u
...   | t' , ct | u' , cu with t' ≟Tm u'
...     | yes refl = just (back ct cu crfl)
...     | no _     = mapM (back ct cu) (structTmN k t' u')

convTyN zero A B with A ≟Ty B
... | yes refl = just crflᵀ
... | no _     = nothing
convTyN (suc k) A B with A ≟Ty B
... | yes refl = just crflᵀ
... | no _ with whnfNᵀ k A | whnfNᵀ k B
...   | A' , ca | B' , cb with A' ≟Ty B'
...     | yes refl = just (backᵀ ca cb crflᵀ)
...     | no _     = mapM (backᵀ ca cb) (structTyN k A' B')

-- the same head: the fields
structTmN k (lam b) (lam b') = mapM (cong≅ lam ξ-lam) (convTmN k b b')
structTmN k (app f a) (app f' a') =
  both (convTmN k f f') (convTmN k a a') λ c₁ c₂ → ctrn (cong≅ (λ x → app x a) ξ-appˡ c₁) (cong≅ (app f') ξ-appʳ c₂)
structTmN k (pair a b) (pair a' b') =
  both (convTmN k a a') (convTmN k b b') λ c₁ c₂ → ctrn (cong≅ (λ x → pair x b) ξ-pairˡ c₁) (cong≅ (pair a') ξ-pairʳ c₂)
structTmN k (fst p) (fst p') = mapM (cong≅ fst ξ-fst) (convTmN k p p')
structTmN k (snd p) (snd p') = mapM (cong≅ snd ξ-snd) (convTmN k p p')
structTmN k (nsuc n) (nsuc n') = mapM (cong≅ nsuc ξ-nsuc) (convTmN k n n')
structTmN k (fsuc n) (fsuc n') = mapM (cong≅ fsuc ξ-fsuc) (convTmN k n n')
structTmN k (con p) (con p') = mapM (cong≅ con ξ-con) (convTmN k p p')
structTmN k (⌜Fin⌝ n) (⌜Fin⌝ n') = mapM (cong≅ ⌜Fin⌝ ξ-⌜Fin⌝) (convTmN k n n')
structTmN k (⌜Σ⌝ c d) (⌜Σ⌝ c' d') =
  both (convTmN k c c') (convTmN k d d') λ c₁ c₂ → ctrn (cong≅ (λ x → ⌜Σ⌝ x d) ξ-⌜Σ⌝ˡ c₁) (cong≅ (⌜Σ⌝ c') ξ-⌜Σ⌝ʳ c₂)
structTmN k (⌜Π⌝ c d) (⌜Π⌝ c' d') =
  both (convTmN k c c') (convTmN k d d') λ c₁ c₂ → ctrn (cong≅ (λ x → ⌜Π⌝ x d) ξ-⌜Π⌝ˡ c₁) (cong≅ (⌜Π⌝ c') ξ-⌜Π⌝ʳ c₂)
structTmN k (⌜IMu⌝ I D i) (⌜IMu⌝ I' D' i') =
  both (convTmN k I I') (both (convTmN k D D') (convTmN k i i') (λ a b → a , b)) λ { c₁ (c₂ , c₃) →
    ctrn (cong≅ (λ x → ⌜IMu⌝ x D i) ξ-⌜IMu⌝ᴵ c₁)
         (ctrn (cong≅ (λ x → ⌜IMu⌝ I' x i) ξ-⌜IMu⌝ᴰ c₂) (cong≅ (⌜IMu⌝ I' D') ξ-⌜IMu⌝ⁱ c₃)) }
structTmN k (dσ S f) (dσ S' f') =
  both (convTmN k S S') (convTmN k f f') λ c₁ c₂ → ctrn (cong≅ (λ x → dσ x f) ξ-dσˢ c₁) (cong≅ (dσ S') ξ-dσᶠ c₂)
structTmN k (dρ j C) (dρ j' C') =
  both (convTmN k j j') (convTmN k C C') λ c₁ c₂ → ctrn (cong≅ (λ x → dρ x C) ξ-dρʲ c₁) (cong≅ (dρ j') ξ-dρᶜ c₂)
structTmN k (dpay I D C) (dpay I' D' C') =
  both (convTmN k I I') (both (convTmN k D D') (convTmN k C C') (λ a b → a , b)) λ { c₁ (c₂ , c₃) →
    ctrn (cong≅ (λ x → dpay x D C) ξ-dpayᴵ c₁)
         (ctrn (cong≅ (λ x → dpay I' x C) ξ-dpayᴰ c₂) (cong≅ (dpay I' D') ξ-dpayᶜ c₃)) }
structTmN k (fcase t a b) (fcase t' a' b') =
  both (convTmN k t t') (both (convTmN k a a') (convTmN k b b') (λ x y → x , y)) λ { c₁ (c₂ , c₃) →
    ctrn (cong≅ (λ x → fcase x a b) ξ-fcaseᵗ c₁)
         (ctrn (cong≅ (λ x → fcase t' x b) ξ-fcaseᵃ c₂) (cong≅ (fcase t' a') ξ-fcaseᵇ c₃)) }
structTmN k (natrec z s n) (natrec z' s' n') =
  both (convTmN k z z') (both (convTmN k s s') (convTmN k n n') (λ x y → x , y)) λ { c₁ (c₂ , c₃) →
    ctrn (cong≅ (λ x → natrec x s n) ξ-natrecᶻ c₁)
         (ctrn (cong≅ (λ x → natrec z' x n) ξ-natrecˢ c₂) (cong≅ (natrec z' s') ξ-natrecⁿ c₃)) }
structTmN k _ _ = nothing

structTyN k (Π A B) (Π A' B') =
  both (convTyN k A A') (convTyN k B B') λ c₁ c₂ → ctrnᵀ (cong≅ᵀ (λ X → Π X B) ξ-Πˡ c₁) (cong≅ᵀ (Π A') ξ-Πʳ c₂)
structTyN k (Σ' A B) (Σ' A' B') =
  both (convTyN k A A') (convTyN k B B') λ c₁ c₂ → ctrnᵀ (cong≅ᵀ (λ X → Σ' X B) ξ-Σˡ c₁) (cong≅ᵀ (Σ' A') ξ-Σʳ c₂)
structTyN k (El c) (El c') = mapM (cong≅ᵗ El ξ-El) (convTmN k c c')
structTyN k (Fin n) (Fin n') = mapM (cong≅ᵗ Fin ξ-Fin) (convTmN k n n')
structTyN k (Desc I) (Desc I') = mapM (cong≅ᵗ Desc ξ-Desc) (convTmN k I I')
structTyN k (IMu I D i) (IMu I' D' i') =
  both (convTmN k I I') (both (convTmN k D D') (convTmN k i i') (λ a b → a , b)) λ { c₁ (c₂ , c₃) →
    ctrnᵀ (cong≅ᵗ (λ x → IMu x D i) ξ-IMuᴵ c₁)
          (ctrnᵀ (cong≅ᵗ (λ x → IMu I' x i) ξ-IMuᴰ c₂) (cong≅ᵗ (IMu I' D') ξ-IMuⁱ c₃)) }
structTyN k (DIh D M C p) (DIh D' M' C' p') =
  both (convTmN k D D') (both (convTyN k M M') (both (convTmN k C C') (convTmN k p p') (λ a b → a , b)) (λ a b → a , b))
    λ { c₁ (c₂ , (c₃ , c₄)) →
      ctrnᵀ (cong≅ᵗ (λ x → DIh x M C p) ξ-DIhᴰ c₁)
            (ctrnᵀ (cong≅ᵀ (λ X → DIh D' X C p) ξ-DIhᴹ c₂)
                   (ctrnᵀ (cong≅ᵗ (λ x → DIh D' M' x p) ξ-DIhᶜ c₃) (cong≅ᵗ (DIh D' M' C') ξ-DIhᵖ c₄))) }
structTyN k _ _ = nothing

