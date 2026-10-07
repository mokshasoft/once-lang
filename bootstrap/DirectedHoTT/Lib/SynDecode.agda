-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- OCP-0009 · Lib — ★ DECODING A SYNTAX (PLAN-FAITHFUL F6.1), generic in
-- the signature.
--
-- The converse of `⊢conSyn`/`⊢payArgsF`: a CLOSED NORMAL term of sort `s`
-- at depth `d` is a constructor `conₗ k p` of that sort, and its payload's
-- fields are closed normal terms at the field kinds' own types (`DArgs`,
-- the closed-normal twin of `Args`).
--
--     syn-dec : NthG sg s shs → ◇ ⊢ t ∷ SK sg s d → IsNormal t →
--               t ≡ conₗ k p,  NthSh shs k sh,  DArgs d sh p
--
-- Built from `Lib/Decode`: the family peels to a tag and the selected
-- telescope (`fibₛ-β`, `selF-β`), and the telescope peels field by field.
--
-- `--safe`, ZERO axioms.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
open import DirectedHoTT.Spec.Syntax using ( KSig; _<ˢ_; _<ˢ?_ )
open import DirectedHoTT.Spec.SigWf using ( WfK )
import DirectedHoTT.Metatheory.Entries as Entries
module DirectedHoTT.Lib.SynDecode (𝒮 : KSig) (wf : WfK 𝒮) where

-- ★ PLAN-REF: at a well-formed signature, all its names
private
  𝓃 = KSig.size 𝒮
  ok = Entries.sigOK 𝒮 𝓃 wf
  refs = Entries.refsOK 𝒮 𝓃 (λ p → p) wf


open import normalizer.Syntax.Types using ( _≡_; refl; sym; trans; cong; subst; Σ; _,_; _×_ )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax
open import DirectedHoTT.Spec.Typing 𝒮 𝓃 hiding ( _×_; _,,_ )
open import DirectedHoTT.Metatheory.RedCong 𝒮 using ( _⟶ᵀ*_; doneᵀ; stepᵀ; ⟶ᵀ*-El; ⟶ᵀ*-IMu; ⟶ᵀ*-Fin; red→≅ᵀ; ⟶*-dpayᶜ; ⟶*-pairʳ )
open import DirectedHoTT.Metatheory.TySub 𝒮 𝓃 using ( wk-cancel-tm; ⊢-cast )
open import DirectedHoTT.Metatheory.LogicalRelation 𝒮 using ( IsNormal )
open import DirectedHoTT.Lib.Sugar 𝒮 𝓃 ok using ( tag; conₗ; Lt; lt-z; lt-s; selF-β; nth-sub )
open import DirectedHoTT.Lib.Tel 𝒮 𝓃 ok using ( ⌜_⌝ᵗ; nth-⌜⌝ )
open import DirectedHoTT.Lib.TelAt 𝒮 𝓃 ok using ( nth-⌜⌝ₛₛ )
open import DirectedHoTT.Lib.Sorted 𝒮 𝓃 ok using ( fibₛ-β )
open import DirectedHoTT.Lib.Syn 𝒮 𝓃 ok
open import DirectedHoTT.Lib.Decode 𝒮 wf

private
  variable
    n c k s : ℕ

------------------------------------------------------------------------
-- 1. The fields, closed and normal.
------------------------------------------------------------------------

data DArgs (sg : Sig n) (d : RTm ε) : Shape → RTm ε → Set where
  d[]   : DArgs sg d []ʰ unit
  d-rec : {a p : RTm ε} {sh : Shape} →
          ◇ ⊢ a ∷ SK sg s (nsucs k d) → IsNormal a → DArgs sg d sh p →
          DArgs sg d (rec s k ∷ʰ sh) (pair a p)
  d-nat : {a p : RTm ε} {sh : Shape} →
          ◇ ⊢ a ∷ El ⌜Nat⌝ → IsNormal a → DArgs sg d sh p → DArgs sg d (nat ∷ʰ sh) (pair a p)
  d-cls : {a p : RTm ε} {sh : Shape} →
          ◇ ⊢ a ∷ SK sg s nzero → IsNormal a → DArgs sg d sh p →
          DArgs sg d (cls s ∷ʰ sh) (pair a p)
  d-v   : {a : RTm ε} → ◇ ⊢ a ∷ Fin d → IsNormal a → DArgs sg d vʰ (pair a unit)

------------------------------------------------------------------------
-- 2. A payload, peeled along its shape.
------------------------------------------------------------------------

private
  -- a β into the rest of the telescope, at the instantiated index
  βrest : {I D a : RTm ε} {p : RTm ε} (sh : Shape) (i : RTm ε) →
          ◇ ⊢ p ∷ El (dpay I D (app (lam ⌜ tel sh (renTm vs i) ⌝ᵗ) a)) →
          ◇ ⊢ p ∷ El (dpay I D ⌜ tel sh i ⌝ᵗ)
  βrest {a = a} sh i dp =
    ⊢-cast (cong (λ X → El (dpay _ _ X)) (trans (sub-tel (single a) sh (renTm vs i)) (cong (λ z → ⌜ tel sh z ⌝ᵗ) (wk-cancel-tm a i))))
           (⊢conv dp (red→≅ᵀ (⟶ᵀ*-El (⟶*-dpayᶜ (step (β _ a) done)))))

  βι : {I D a : RTm ε} {p : RTm ε} → ◇ ⊢ p ∷ El (dpay I D (app (lam dι) a)) → ◇ ⊢ p ∷ El (dpay I D dι)
  βι {a = a} dp = ⊢conv dp (red→≅ᵀ (⟶ᵀ*-El (⟶*-dpayᶜ (step (β dι a) done))))

args-dec : {sg : Sig n} {i d p : RTm ε} (sh : Shape) → snd i ⟶* d →
           ◇ ⊢ p ∷ El (dpay (SI n) (SD sg) ⌜ tel sh i ⌝ᵗ) → IsNormal p → DArgs sg d sh p
args-dec []ʰ r dp nrm with pay-ι dp done nrm
... | refl = d[]
args-dec {sg = sg} (rec s k ∷ʰ sh) r dp nrm with pay-ρ dp done nrm
... | a , (b , (refl , ((da , db) , (na , nb)))) =
      d-rec (⊢IMu→SK {sg = sg} {s = s} (⊢conv da (red→≅ᵀ (⟶ᵀ*-IMu (⟶*-pairʳ (⟶*-nsucs k r)))))) na
            (args-dec sh r db nb)
args-dec {i = i} (nat ∷ʰ sh) r dp nrm with pay-σ dp done nrm
... | a , (b , (refl , ((da , db) , (na , nb)))) = d-nat da na (args-dec sh r (βrest sh i db) nb)
args-dec {sg = sg} (cls s ∷ʰ sh) r dp nrm with pay-ρ dp done nrm
... | a , (b , (refl , ((da , db) , (na , nb)))) =
      d-cls (⊢IMu→SK {sg = sg} {s = s} da) na (args-dec sh r db nb)
args-dec vʰ r dp nrm with pay-σ dp done nrm
... | a , (b , (refl , ((da , db) , (na , nb)))) with pay-ι (βι db) done nb
...   | refl = d-v (⊢conv (⊢conv da (credᵀ El-⌜Fin⌝)) (red→≅ᵀ (⟶ᵀ*-Fin r))) na

------------------------------------------------------------------------
-- 3. ★ A closed normal term of a syntax is a constructor.
------------------------------------------------------------------------

-- the shape at a tag in range
nthSh-lt : (shs : Shapes c) → Lt k c → Σ Shape (λ sh → NthSh shs k sh)
nthSh-lt (sh ∷ˢʰ shs) lt-z     = sh , nthʰ-z
nthSh-lt (_ ∷ˢʰ shs)  (lt-s l) with nthSh-lt shs l
... | sh , nt = sh , nthʰ-s nt

syn-dec : {sg : Sig n} {shs : Shapes c} {t d : RTm ε} → NthG sg s shs →
          ◇ ⊢ t ∷ SK sg s d → IsNormal t →
          Σ ℕ (λ k → Σ Shape (λ sh → Σ (RTm ε) (λ p →
            NthSh shs k sh × ((t ≡ conₗ k p) × DArgs sg d sh p))))
syn-dec {n = n} {s = s} {sg = sg} {shs = shs} {d = d} ng dt nrm
  with con-dec (⊢SK→IMu {sg = sg} {s = s} dt) nrm
... | q , (refl , (dq , nq))
  with pay-σ dq (fibₛ-β d (nth-⌜⌝ₛₛ (nth-stels ng))) nq
...   | a , (b , (refl , ((da , db) , (na , nb))))
  with tag-decᶜ da na
...     | k , (lt , refl) with nthSh-lt shs lt
...       | sh , nh =
            k , (sh , (b , (nh , (refl ,
              args-dec sh (step (βsnd (tag s) d) done)
                (⊢-cast (cong (λ X → El (dpay (SI n) (SD sg) X)) (sub-tel (single ix) sh (var vz)))
                  (⊢conv db (red→≅ᵀ (⟶ᵀ*-El (⟶*-dpayᶜ (selF-β (nth-sub (single ix) (nth-⌜⌝ (nth-tels nh)))))))))
                nb))))
  where ix = pair (tag s) d
