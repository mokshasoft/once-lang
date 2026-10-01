-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- OCP-0009 · KNOT — the REDUCTION judgements `t ⟶ u` and `A ⟶ᵀ B` as
-- families fibred by their SUBJECT (the source; D077), the target in the
-- convoy: `Lib/SynFam` at the Knot, convoy = a Knot term at the subject's
-- own index.  Two families (D077's strata: `⟶ᵀ` cites `⟶`), one index.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Knot.RedIx where

open import normalizer.Syntax.Types using ( _≡_; refl; sym; trans; cong; cong₂; subst )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax hiding ( Fin )
open import DirectedHoTT.Spec.Typing hiding ( _×_; _,,_ )
open import DirectedHoTT.Metatheory.TySub using ( ⊢-cast )
open import DirectedHoTT.Metatheory.RedCong using ( red→≅ᵀ; _⟶ᵀ*_; stepᵀ; ⟶ᵀ*-IMu; ⟶*-pairʳ; ⟶*-nsuc )
open import DirectedHoTT.Lib.FinFam using ( ⊢isuc )
open import DirectedHoTT.Lib.Sugar using ( tag; Lt; lt-z; lt-s )
open import DirectedHoTT.Lib.Syn
open import DirectedHoTT.Lib.SynFam using ( module SynFam )
open import DirectedHoTT.Examples.Knot.Sig

private
  variable
    Δ Θ : Cx

-- the target: a Knot term at the subject's index
CR : RTm (Δ ∙)
CR = ⌜IMu⌝ (SI 2) KD (var vz)

CR-sub : (σ : Sub Δ Θ) → subTm (extS σ) (CR {Δ}) ≡ CR
CR-sub {Δ} σ = cong (λ D → ⌜IMu⌝ (SI 2) D (var vz)) (SD-sub (extS σ) KSig)

⊢CR : {Γ : Ctx} → (Γ ▹ El (SI 2)) ⊢ CR ∷ U
⊢CR = ⊢⌜IMu⌝ ⊢SI ⊢KD (⊢var here)

module Redₘ = SynFam KOK CR CR-sub ⊢CR     -- t ⟶ u
module RedTₘ = SynFam KOK CR CR-sub ⊢CR    -- A ⟶ᵀ B

-- the convoy at an index IS a Knot term there
eCR : (i : RTm Δ) → subTm (single i) (CR {Δ}) ≡ ⌜IMu⌝ (SI 2) KD i
eCR {Δ} i = cong (λ D → ⌜IMu⌝ (SI 2) D i) (SD-sub (single i) KSig)

module _ {Ξ : Ctx} {s : ℕ} {j c : RTm ⌊ Ξ ⌋} where
  -- the target, read off the convoy
  ⊢tgt : Ξ ⊢ c ∷ El (subTm (single (pair (tag s) j)) CR) → Ξ ⊢ c ∷ K s j
  ⊢tgt dc = ⊢conv (⊢-cast {Ξ} {c} {El (subTm (single (pair (tag s) j)) CR)} {El (⌜IMu⌝ (SI 2) KD (pair (tag s) j))}
                          (cong El (eCR (pair (tag s) j))) dc)
                  (credᵀ El-⌜SK⌝)

  -- …and put into one
  ⊢toCR : Ξ ⊢ c ∷ K s j → Ξ ⊢ c ∷ El (subTm (single (pair (tag s) j)) CR)
  ⊢toCR dc = ⊢-cast {Ξ} {c} {El (⌜IMu⌝ (SI 2) KD (pair (tag s) j))} {El (subTm (single (pair (tag s) j)) CR)}
                    (cong El (sym (eCR (pair (tag s) j)))) (⊢conv dc (csymᵀ (credᵀ El-⌜SK⌝)))

-- the two judgements' indices
ix⟶ ix⟶ᵀ : RTm Δ → RTm Δ → RTm Δ → RTm Δ
ix⟶ d t u = Redₘ.ixJ (pair (tag 1) d) t u
ix⟶ᵀ d A B = RedTₘ.ixJ (pair (tag 0) d) A B

⊢ix⟶ : {Ξ : Ctx} {d t u : RTm ⌊ Ξ ⌋} → Ξ ⊢ d ∷ El ⌜Nat⌝ → Ξ ⊢ t ∷ K 1 d → Ξ ⊢ u ∷ K 1 d → Ξ ⊢ ix⟶ d t u ∷ El Redₘ.J
⊢ix⟶ dd dt du = Redₘ.⊢ixJ (⊢ix (lt-s lt-z) dd) (⊢SK→IMu {sg = KSig} dt) (⊢toCR du)

⊢ix⟶ᵀ : {Ξ : Ctx} {d A B : RTm ⌊ Ξ ⌋} → Ξ ⊢ d ∷ El ⌜Nat⌝ → Ξ ⊢ A ∷ K 0 d → Ξ ⊢ B ∷ K 0 d → Ξ ⊢ ix⟶ᵀ d A B ∷ El RedTₘ.J
⊢ix⟶ᵀ dd dA dB = RedTₘ.⊢ixJ (⊢ix lt-z dd) (⊢SK→IMu {sg = KSig} dA) (⊢toCR dB)

-- ★ the CONVERSIONS `t ≅ u` / `A ≅ᵀ B`: the same index; their rules
--   (red, refl, sym, trans) have a bare-variable subject, so they sit in
--   every fibre (D077)
module Convₘ = SynFam KOK CR CR-sub ⊢CR     -- t ≅ u
module ConvTₘ = SynFam KOK CR CR-sub ⊢CR    -- A ≅ᵀ B

ix≅ ix≅ᵀ : RTm Δ → RTm Δ → RTm Δ → RTm Δ
ix≅ d t u = Convₘ.ixJ (pair (tag 1) d) t u
ix≅ᵀ d A B = ConvTₘ.ixJ (pair (tag 0) d) A B

⊢ix≅ : {Ξ : Ctx} {d t u : RTm ⌊ Ξ ⌋} → Ξ ⊢ d ∷ El ⌜Nat⌝ → Ξ ⊢ t ∷ K 1 d → Ξ ⊢ u ∷ K 1 d → Ξ ⊢ ix≅ d t u ∷ El Convₘ.J
⊢ix≅ dd dt du = Convₘ.⊢ixJ (⊢ix (lt-s lt-z) dd) (⊢SK→IMu {sg = KSig} dt) (⊢toCR du)

⊢ix≅ᵀ : {Ξ : Ctx} {d A B : RTm ⌊ Ξ ⌋} → Ξ ⊢ d ∷ El ⌜Nat⌝ → Ξ ⊢ A ∷ K 0 d → Ξ ⊢ B ∷ K 0 d → Ξ ⊢ ix≅ᵀ d A B ∷ El ConvTₘ.J
⊢ix≅ᵀ dd dA dB = ConvTₘ.⊢ixJ (⊢ix lt-z dd) (⊢SK→IMu {sg = KSig} dA) (⊢toCR dB)

-- ★ `pwBody`'s GRAPH on the codes `pw?` accepts (`Spec/Variance`): fibred
--   by the code, the convoy is the BODY — a Knot term ONE BINDER deeper
module _ where
  CP : RTm (Δ ∙)
  CP = ⌜IMu⌝ (SI 2) KD (pair (tag 1) (nsuc (snd (var vz))))

  CP-sub : (σ : Sub Δ Θ) → subTm (extS σ) (CP {Δ}) ≡ CP
  CP-sub {Δ} σ = cong₂ (λ D t → ⌜IMu⌝ (SI 2) D (pair t (nsuc (snd (var vz))))) (SD-sub (extS σ) KSig) (tag-sub (extS σ) 1)

  ⊢CP : {Γ : Ctx} → (Γ ▹ El (SI 2)) ⊢ CP ∷ U
  ⊢CP = ⊢⌜IMu⌝ ⊢SI ⊢KD (⊢ix (lt-s lt-z) (⊢isuc (⊢depth (⊢var here))))

module Pwₘ = SynFam KOK CP CP-sub ⊢CP

eCP : (j : RTm Δ) → subTm (single (pair (tag 1) j)) (CP {Δ}) ≡ ⌜IMu⌝ (SI 2) KD (pair (tag 1) (nsuc (snd (pair (tag 1) j))))
eCP {Δ} j = cong₂ (λ D t → ⌜IMu⌝ (SI 2) D (pair t (nsuc (snd (pair (tag 1) j))))) (SD-sub (single (pair (tag 1) j)) KSig) (tag-sub (single (pair (tag 1) j)) 1)

module _ {Ξ : Ctx} {j c : RTm ⌊ Ξ ⌋} where
  private
    bR : El (⌜IMu⌝ (SI 2) KD (pair (tag 1) (nsuc (snd (pair (tag 1) j))))) ⟶ᵀ* K 1 (nsuc j)
    bR = stepᵀ El-⌜SK⌝ (⟶ᵀ*-SK (⟶*-nsuc (step (βsnd (tag 1) j) done)))

  -- the body, read off the convoy
  ⊢pwTgt : Ξ ⊢ c ∷ El (subTm (single (pair (tag 1) j)) CP) → Ξ ⊢ c ∷ K 1 (nsuc j)
  ⊢pwTgt dc = ⊢conv (⊢-cast {Ξ} {c} {El (subTm (single (pair (tag 1) j)) CP)} {El (⌜IMu⌝ (SI 2) KD (pair (tag 1) (nsuc (snd (pair (tag 1) j)))))}
                            (cong El (eCP j)) dc)
                    (red→≅ᵀ bR)

  -- …and put into one
  ⊢toCP : Ξ ⊢ c ∷ K 1 (nsuc j) → Ξ ⊢ c ∷ El (subTm (single (pair (tag 1) j)) CP)
  ⊢toCP dc = ⊢-cast {Ξ} {c} {El (⌜IMu⌝ (SI 2) KD (pair (tag 1) (nsuc (snd (pair (tag 1) j)))))} {El (subTm (single (pair (tag 1) j)) CP)}
                    (cong El (sym (eCP j))) (⊢conv dc (csymᵀ (red→≅ᵀ bR)))

ixPw : RTm Δ → RTm Δ → RTm Δ → RTm Δ
ixPw d c b = Pwₘ.ixJ (pair (tag 1) d) c b

⊢ixPw : {Ξ : Ctx} {d c b : RTm ⌊ Ξ ⌋} → Ξ ⊢ d ∷ El ⌜Nat⌝ → Ξ ⊢ c ∷ K 1 d → Ξ ⊢ b ∷ K 1 (nsuc d) → Ξ ⊢ ixPw d c b ∷ El Pwₘ.J
⊢ixPw dd dc db = Pwₘ.⊢ixJ (⊢ix (lt-s lt-z) dd) (⊢SK→IMu {sg = KSig} dc) (⊢toCP db)
