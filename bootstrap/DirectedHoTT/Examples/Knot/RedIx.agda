-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- OCP-0009 · KNOT — the REDUCTION judgements `t ⟶ u` and `A ⟶ᵀ B` as
-- families fibred by their SUBJECT (the source; D077), the target in the
-- convoy: `Lib/SynFam` at the Knot, convoy = a Knot term at the subject's
-- own index.  ★ PLAN-REF: over the quoted signature (`Knot/QSig`) — the
-- parameter δ reads; `Pw` is over nothing.  Two families (D077's strata: `⟶ᵀ` cites `⟶`), one index.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
open import DirectedHoTT.Spec.Syntax using ( Defs )
open import DirectedHoTT.Spec.SigWf using ( WfK )
import DirectedHoTT.Metatheory.Entries as Entries
module DirectedHoTT.Examples.Knot.RedIx (𝒮 : Defs) (wf : WfK 𝒮) where

-- ★ PLAN-REF: over a well-formed signature, at all its names
private
  𝓃 = Defs.size 𝒮
  ok = Entries.sigOK 𝒮 𝓃 wf
  refs = Entries.refsOK 𝒮 𝓃 (λ p → p) wf


open import normalizer.Syntax.Types using ( _≡_; refl; sym; trans; cong; cong₂; subst )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax hiding ( Fin )
open import DirectedHoTT.Spec.Typing 𝒮 𝓃 hiding ( _×_; _,,_ )
open import DirectedHoTT.Metatheory.TySub 𝒮 𝓃 using ( ⊢-cast )
open import DirectedHoTT.Metatheory.RedCong 𝒮 using ( red→≅ᵀ; _⟶ᵀ*_; stepᵀ; ⟶ᵀ*-IMu; ⟶*-pairʳ; ⟶*-nsuc )
open import DirectedHoTT.Lib.NatCode 𝒮 𝓃 using ( ⊢isuc )
open import DirectedHoTT.Lib.Sugar 𝒮 𝓃 ok using ( tag; Lt; lt-z; lt-s; v₀; _,ₚ_ )
open import DirectedHoTT.Lib.Syn 𝒮 𝓃 ok
open import DirectedHoTT.Lib.SynFam 𝒮 𝓃 ok using ( module SynFam )
open import DirectedHoTT.Examples.Knot.Sig 𝒮 wf
open import DirectedHoTT.Examples.Knot.QSig 𝒮 wf using ( ⌜QSig⌝; ⌜QSig⌝-sub; ⊢⌜QSig⌝ )

private
  variable
    Δ Θ : Cx

-- the target: a Knot term at the subject's index — OPAQUE: it carries the
--   description, and a row's `Cat (pair (tag s) j)` reached through the
--   dispatch (`s` as `suc zero`) against an `ok…` lemma's (`s` as `1`)
--   failed the syntactic check and pushed `subTm` through all of KD
--   (`rowOK⟶` 24 s; `context-form-mismatch-opaque`).  Interface: CR-sub,
--   ⊢CR, eCR.
opaque
  CR : RTm (Δ ∙)
  CR = ⌜IMu⌝ (SI 2) KD v₀

  CR-sub : (σ : Sub Δ Θ) → subTm (extS σ) (CR {Δ}) ≡ CR
  CR-sub {Δ} σ = cong (λ D → ⌜IMu⌝ (SI 2) D v₀) (SD-sub (extS σ) KSig)

  ⊢CR : {Γ : Ctx} → (Γ ▹ El (SI 2)) ⊢ CR ∷ U
  ⊢CR = ⊢⌜IMu⌝ ⊢SI ⊢KD (⊢var here)

  -- the convoy at an index IS a Knot term there
  eCR : (i : RTm Δ) → subTm (single i) (CR {Δ}) ≡ ⌜IMu⌝ (SI 2) KD i
  eCR {Δ} i = cong (λ D → ⌜IMu⌝ (SI 2) D i) (SD-sub (single i) KSig)

module Redₘ = SynFam KOK ⌜QSig⌝ ⌜QSig⌝-sub ⊢⌜QSig⌝ CR CR-sub ⊢CR     -- t ⟶ u
module RedTₘ = SynFam KOK ⌜QSig⌝ ⌜QSig⌝-sub ⊢⌜QSig⌝ CR CR-sub ⊢CR    -- A ⟶ᵀ B


module _ {Ξ : Ctx} {s : ℕ} {j c : RTm ⌊ Ξ ⌋} where
  -- the target, read off the convoy
  ⊢tgt : Ξ ⊢ c ∷ El (subTm (single ((tag s) ,ₚ j)) CR) → Ξ ⊢ c ∷ K s j
  ⊢tgt dc = ⊢conv (⊢-cast {Ξ} {c} {El (subTm (single ((tag s) ,ₚ j)) CR)} {El (⌜IMu⌝ (SI 2) KD ((tag s) ,ₚ j))}
                          (cong El (eCR ((tag s) ,ₚ j))) dc)
                  (credᵀ El-⌜SK⌝)

  -- …and put into one
  ⊢toCR : Ξ ⊢ c ∷ K s j → Ξ ⊢ c ∷ El (subTm (single ((tag s) ,ₚ j)) CR)
  ⊢toCR dc = ⊢-cast {Ξ} {c} {El (⌜IMu⌝ (SI 2) KD ((tag s) ,ₚ j))} {El (subTm (single ((tag s) ,ₚ j)) CR)}
                    (cong El (sym (eCR ((tag s) ,ₚ j)))) (⊢conv dc (csymᵀ (credᵀ El-⌜SK⌝)))

-- the two judgements' indices
ix⟶ ix⟶ᵀ : RTm Δ → RTm Δ → RTm Δ → RTm Δ
ix⟶ d t u = Redₘ.ixJ ((tag 1) ,ₚ d) t u
ix⟶ᵀ d A B = RedTₘ.ixJ ((tag 0) ,ₚ d) A B

⊢ix⟶ : {Ξ : Ctx} {d t u : RTm ⌊ Ξ ⌋} → Ξ ⊢ d ∷ El ⌜Nat⌝ → Ξ ⊢ t ∷ K 1 d → Ξ ⊢ u ∷ K 1 d → Ξ ⊢ ix⟶ d t u ∷ El Redₘ.J
⊢ix⟶ dd dt du = Redₘ.⊢ixJ (⊢ix (lt-s lt-z) dd) (⊢SK→IMu {sg = KSig} dt) (⊢toCR du)

⊢ix⟶ᵀ : {Ξ : Ctx} {d A B : RTm ⌊ Ξ ⌋} → Ξ ⊢ d ∷ El ⌜Nat⌝ → Ξ ⊢ A ∷ K 0 d → Ξ ⊢ B ∷ K 0 d → Ξ ⊢ ix⟶ᵀ d A B ∷ El RedTₘ.J
⊢ix⟶ᵀ dd dA dB = RedTₘ.⊢ixJ (⊢ix lt-z dd) (⊢SK→IMu {sg = KSig} dA) (⊢toCR dB)

-- ★ the CONVERSIONS `t ≅ u` / `A ≅ᵀ B`: the same index; their rules
--   (red, refl, sym, trans) have a bare-variable subject, so they sit in
--   every fibre (D077)
module Convₘ = SynFam KOK ⌜QSig⌝ ⌜QSig⌝-sub ⊢⌜QSig⌝ CR CR-sub ⊢CR     -- t ≅ u
module ConvTₘ = SynFam KOK ⌜QSig⌝ ⌜QSig⌝-sub ⊢⌜QSig⌝ CR CR-sub ⊢CR    -- A ≅ᵀ B

ix≅ ix≅ᵀ : RTm Δ → RTm Δ → RTm Δ → RTm Δ
ix≅ d t u = Convₘ.ixJ ((tag 1) ,ₚ d) t u
ix≅ᵀ d A B = ConvTₘ.ixJ ((tag 0) ,ₚ d) A B

⊢ix≅ : {Ξ : Ctx} {d t u : RTm ⌊ Ξ ⌋} → Ξ ⊢ d ∷ El ⌜Nat⌝ → Ξ ⊢ t ∷ K 1 d → Ξ ⊢ u ∷ K 1 d → Ξ ⊢ ix≅ d t u ∷ El Convₘ.J
⊢ix≅ dd dt du = Convₘ.⊢ixJ (⊢ix (lt-s lt-z) dd) (⊢SK→IMu {sg = KSig} dt) (⊢toCR du)

⊢ix≅ᵀ : {Ξ : Ctx} {d A B : RTm ⌊ Ξ ⌋} → Ξ ⊢ d ∷ El ⌜Nat⌝ → Ξ ⊢ A ∷ K 0 d → Ξ ⊢ B ∷ K 0 d → Ξ ⊢ ix≅ᵀ d A B ∷ El ConvTₘ.J
⊢ix≅ᵀ dd dA dB = ConvTₘ.⊢ixJ (⊢ix lt-z dd) (⊢SK→IMu {sg = KSig} dA) (⊢toCR dB)

-- ★ `pwBody`'s GRAPH on the codes `pw?` accepts (`Spec/Variance`): fibred
--   by the code, the convoy is the BODY — a Knot term ONE BINDER deeper
opaque
  CP : RTm (Δ ∙)
  CP = ⌜IMu⌝ (SI 2) KD ((tag 1) ,ₚ (nsuc (snd v₀)))

  CP-sub : (σ : Sub Δ Θ) → subTm (extS σ) (CP {Δ}) ≡ CP
  CP-sub {Δ} σ = cong₂ (λ D t → ⌜IMu⌝ (SI 2) D (t ,ₚ (nsuc (snd v₀)))) (SD-sub (extS σ) KSig) (tag-sub (extS σ) 1)

  ⊢CP : {Γ : Ctx} → (Γ ▹ El (SI 2)) ⊢ CP ∷ U
  ⊢CP = ⊢⌜IMu⌝ ⊢SI ⊢KD (⊢ix (lt-s lt-z) (⊢isuc (⊢depth (⊢var here))))

  eCP : (j : RTm Δ) → subTm (single ((tag 1) ,ₚ j)) (CP {Δ}) ≡ ⌜IMu⌝ (SI 2) KD ((tag 1) ,ₚ (nsuc (snd ((tag 1) ,ₚ j))))
  eCP {Δ} j = cong₂ (λ D t → ⌜IMu⌝ (SI 2) D (t ,ₚ (nsuc (snd ((tag 1) ,ₚ j))))) (SD-sub (single ((tag 1) ,ₚ j)) KSig) (tag-sub (single ((tag 1) ,ₚ j)) 1)

module Pwₘ = SynFam KOK ⌜Unit⌝ (λ σ → refl) ⊢⌜Unit⌝ CP CP-sub ⊢CP


module _ {Ξ : Ctx} {j c : RTm ⌊ Ξ ⌋} where
  private
    bR : El (⌜IMu⌝ (SI 2) KD ((tag 1) ,ₚ (nsuc (snd ((tag 1) ,ₚ j))))) ⟶ᵀ* K 1 (nsuc j)
    bR = stepᵀ El-⌜SK⌝ (⟶ᵀ*-SK (⟶*-nsuc (step (βsnd (tag 1) j) done)))

  -- the body, read off the convoy
  ⊢pwTgt : Ξ ⊢ c ∷ El (subTm (single ((tag 1) ,ₚ j)) CP) → Ξ ⊢ c ∷ K 1 (nsuc j)
  ⊢pwTgt dc = ⊢conv (⊢-cast {Ξ} {c} {El (subTm (single ((tag 1) ,ₚ j)) CP)} {El (⌜IMu⌝ (SI 2) KD ((tag 1) ,ₚ (nsuc (snd ((tag 1) ,ₚ j)))))}
                            (cong El (eCP j)) dc)
                    (red→≅ᵀ bR)

  -- …and put into one
  ⊢toCP : Ξ ⊢ c ∷ K 1 (nsuc j) → Ξ ⊢ c ∷ El (subTm (single ((tag 1) ,ₚ j)) CP)
  ⊢toCP dc = ⊢-cast {Ξ} {c} {El (⌜IMu⌝ (SI 2) KD ((tag 1) ,ₚ (nsuc (snd ((tag 1) ,ₚ j)))))} {El (subTm (single ((tag 1) ,ₚ j)) CP)}
                    (cong El (sym (eCP j))) (⊢conv dc (csymᵀ (red→≅ᵀ bR)))

ixPw : RTm Δ → RTm Δ → RTm Δ → RTm Δ
ixPw d c b = Pwₘ.ixJ ((tag 1) ,ₚ d) c b

⊢ixPw : {Ξ : Ctx} {d c b : RTm ⌊ Ξ ⌋} → Ξ ⊢ d ∷ El ⌜Nat⌝ → Ξ ⊢ c ∷ K 1 d → Ξ ⊢ b ∷ K 1 (nsuc d) → Ξ ⊢ ixPw d c b ∷ El Pwₘ.J
⊢ixPw dd dc db = Pwₘ.⊢ixJ (⊢ix (lt-s lt-z) dd) (⊢SK→IMu {sg = KSig} dc) (⊢toCP db)
