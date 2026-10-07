-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- OCP-0009 · KNOT — the `⊢` rows' NESTED CASE on the conclusion type
-- (D077, `Lib/SynPat`): its convoy.
--
-- A term rule whose conclusion type is a constructor pattern (`⊢lam`'s
-- `Π A B`) cases on the type; the case's rows need the context and the
-- TERM's payload, so the case's convoy over the type's index `(0 , j)`
-- is `(Γ , p)` with `p` a payload of the term's shape at `(1 , j)`:
--
--     CI sh  =  ⌜Σ⌝ (⌜Ctx⌝ j) (dpay (SI 2) KD ⌜ tel sh (1 , j) ⌝ᵗ)
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
open import DirectedHoTT.Spec.Syntax using ( Defs )
open import DirectedHoTT.Spec.SigWf using ( WfK )
import DirectedHoTT.Metatheory.Entries as Entries
module DirectedHoTT.Examples.Knot.JudgeTmIx (𝒮 : Defs) (wf : WfK 𝒮) where



open import normalizer.Syntax.Types using ( _≡_; refl; sym; trans; cong; cong₂; subst )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax hiding ( Fin )
open import DirectedHoTT.Spec.Typing 𝒮 (Defs.size 𝒮) hiding ( _×_; _,,_ )
open import DirectedHoTT.Metatheory.TySub 𝒮 (Defs.size 𝒮) using ( ⊢wk; ⊢-cast; wk-cancel-tm )
open import DirectedHoTT.Metatheory.RedCong 𝒮 using ( red→≅ᵀ; ⟶ᵀ*-trans )
open import DirectedHoTT.Lib.Sugar 𝒮 (Defs.size 𝒮) (Entries.okᵂ 𝒮 wf) using ( tag; lt-z; lt-s; v₀; v₁; _,ₚ_ )
open import DirectedHoTT.Lib.SynView 𝒮 (Defs.size 𝒮) (Entries.okᵂ 𝒮 wf) using ( PayV; payV-red; payV-ix )
open import DirectedHoTT.Lib.Tel 𝒮 (Defs.size 𝒮) (Entries.okᵂ 𝒮 wf)
open import DirectedHoTT.Lib.Syn 𝒮 (Defs.size 𝒮) (Entries.okᵂ 𝒮 wf)
open import DirectedHoTT.Examples.Knot.Sig 𝒮 wf
open import DirectedHoTT.Examples.Knot.Ctx 𝒮 wf
open import DirectedHoTT.Examples.Knot.Lookup 𝒮 wf using ( ⌜Ctx⌝ )
open import DirectedHoTT.Examples.Knot.JudgeIx 𝒮 wf using ( ctxK≅ )

private
  variable
    Δ Θ : Cx

-- the payload's telescope at the term index over the type index `var vz`
PT : Shape → RTm ((Δ ∙) ∙)
PT sh = ⌜ tel sh ((tag 1) ,ₚ (snd v₁)) ⌝ᵗ

CI : Shape → RTm (Δ ∙)
CI sh = ⌜Σ⌝ (⌜Ctx⌝ (snd v₀)) (dpay (SI 2) KD (PT sh))

CI-sub : (sh : Shape) (σ : Sub Δ Θ) → subTm (extS σ) (CI {Δ} sh) ≡ CI sh
CI-sub {Δ} {Θ} sh σ = c3 (CtxD-sub (extS σ)) (SD-sub (extS (extS σ)) KSig) (sub-tel (extS (extS σ)) sh ((tag 1) ,ₚ (snd v₁)))
  where
    c3 : {D D' : RTm (Θ ∙)} {K K' X X' : RTm ((Θ ∙) ∙)} → D ≡ D' → K ≡ K' → X ≡ X' →
         ⌜Σ⌝ (⌜IMu⌝ ⌜Nat⌝ D (snd v₀)) (dpay (SI 2) K X) ≡ ⌜Σ⌝ (⌜IMu⌝ ⌜Nat⌝ D' (snd v₀)) (dpay (SI 2) K' X')
    c3 refl refl refl = refl

⊢CI : {sh : Shape} → ShOK 2 sh → {Γ : Ctx} → (Γ ▹ El (SI 2)) ⊢ CI sh ∷ U
⊢CI shok = ⊢⌜Σ⌝ (⊢⌜IMu⌝ ⊢⌜Nat⌝ ⊢CtxD (⊢depth (⊢var here)))
                (⊢dpay ⊢SI ⊢KD (⊢tel ⊢SI (telOK shok (⊢ix (lt-s lt-z) (⊢depth (⊢var (there here)))))))

------------------------------------------------------------------------
-- The convoy at a type index `(0 , j)`: its two halves.
------------------------------------------------------------------------

CIat : Shape → RTm Δ → RTm Δ
CIat sh i = subTm (single i) (CI sh)

module _ {Ξ : Ctx} {j : RTm ⌊ Ξ ⌋} (sh : Shape) where
  private
    ix : RTm ⌊ Ξ ⌋
    ix = pair (tag 0) j
    B : RTm (⌊ Ξ ⌋ ∙)
    B = dpay (SI 2) KD ⌜ tel sh ((tag 1) ,ₚ (snd (renTm vs ix))) ⌝ᵗ
    eCI : CIat sh ix ≡ ⌜Σ⌝ (⌜Ctx⌝ (snd ix)) B
    eCI = c3 (CtxD-sub (single ix)) (SD-sub (extS (single ix)) KSig)
             (sub-tel (extS (single ix)) sh ((tag 1) ,ₚ (snd v₁)))
      where
        c3 : {D D' : RTm ⌊ Ξ ⌋} {K K' X X' : RTm (⌊ Ξ ⌋ ∙)} → D ≡ D' → K ≡ K' → X ≡ X' →
             ⌜Σ⌝ (⌜IMu⌝ ⌜Nat⌝ D (snd ix)) (dpay (SI 2) K X) ≡ ⌜Σ⌝ (⌜IMu⌝ ⌜Nat⌝ D' (snd ix)) (dpay (SI 2) K' X')
        c3 refl refl refl = refl
    -- the payload half instantiated at the context
    eB : (g : RTm ⌊ Ξ ⌋) → subTy (single g) (El B) ≡ El (dpay (SI 2) KD ⌜ tel sh ((tag 1) ,ₚ (snd ix)) ⌝ᵗ)
    eB g = c2 (SD-sub (single g) KSig)
              (trans (sub-tel (single g) sh ((tag 1) ,ₚ (snd (renTm vs ix))))
                     (cong (λ z → ⌜ tel sh ((tag 1) ,ₚ (snd z)) ⌝ᵗ) {x = subTm (single g) (renTm vs ix)} {y = ix}
                           (wk-cancel-tm g ix)))
      where
        c2 : {K K' X X' : RTm ⌊ Ξ ⌋} → K ≡ K' → X ≡ X' → El (dpay (SI 2) K X) ≡ El (dpay (SI 2) K' X')
        c2 refl refl = refl
    -- …and read as the payload's normal form at the term index
    payR : El (dpay (SI 2) KD ⌜ tel sh ((tag 1) ,ₚ (snd ix)) ⌝ᵗ) ≅ᵀ PayV sh ((tag 1) ,ₚ j) (SI 2) (SD KSig)
    payR = red→≅ᵀ (⟶ᵀ*-trans (payV-red sh ((tag 1) ,ₚ (snd ix)) (SI 2) (SD KSig))
                             (payV-ix sh (tag 1) (tag 0) j (SI 2) (SD KSig)))
    dΣ : {c : RTm ⌊ Ξ ⌋} → Ξ ⊢ c ∷ El (CIat sh ix) → Ξ ⊢ c ∷ Σ' (El (⌜Ctx⌝ (snd ix))) (El B)
    dΣ {c} dc = ⊢conv (⊢-cast {Ξ} {c} {El (CIat sh ix)} {El (⌜Σ⌝ (⌜Ctx⌝ (snd ix)) B)} (cong El eCI) dc)
                      (credᵀ (El-⌜Σ⌝ (⌜Ctx⌝ (snd ix)) B))

  -- the context
  ⊢gI : {c : RTm ⌊ Ξ ⌋} → Ξ ⊢ c ∷ El (CIat sh ((tag 0) ,ₚ j)) → Ξ ⊢ fst c ∷ KCtx j
  ⊢gI dc = ⊢conv (⊢fst (dΣ dc)) (ctxK≅ {s = 0} j)

  -- the term's payload
  ⊢pI : {c : RTm ⌊ Ξ ⌋} → Ξ ⊢ c ∷ El (CIat sh ((tag 0) ,ₚ j)) → Ξ ⊢ snd c ∷ PayV sh ((tag 1) ,ₚ j) (SI 2) (SD KSig)
  ⊢pI {c} dc = ⊢conv (⊢-cast {Ξ} {snd c} {subTy (single (fst c)) (El B)} (eB (fst c)) (⊢snd (dΣ dc))) payR

  -- the convoy from its halves
  ⊢cI : {g p : RTm ⌊ Ξ ⌋} → ShOK 2 sh → Ξ ⊢ j ∷ El ⌜Nat⌝ → Ξ ⊢ g ∷ KCtx j →
        Ξ ⊢ p ∷ PayV sh ((tag 1) ,ₚ j) (SI 2) (SD KSig) → Ξ ⊢ pair g p ∷ El (CIat sh ix)
  ⊢cI {g} {p} shok dj dg dp =
    ⊢-cast {Ξ} {pair g p} {El (⌜Σ⌝ (⌜Ctx⌝ (snd ix)) B)} {El (CIat sh ix)} (cong El (sym eCI))
      (⊢conv (⊢pair tyB (⊢conv dg (csymᵀ (ctxK≅ {s = 0} j)))
                        (⊢-cast {Ξ} {p} {El (dpay (SI 2) KD ⌜ tel sh ((tag 1) ,ₚ (snd ix)) ⌝ᵗ)} {subTy (single g) (El B)}
                                (sym (eB g)) (⊢conv dp (csymᵀ payR))))
             (csymᵀ (credᵀ (El-⌜Σ⌝ (⌜Ctx⌝ (snd ix)) B))))
    where
      dix : Ξ ⊢ ix ∷ El (SI 2)
      dix = ⊢ix lt-z dj
      tyB : (Ξ ▹ El (⌜Ctx⌝ (snd ix))) ⊢ty El B
      tyB = ty-El (⊢dpay ⊢SI ⊢KD (⊢tel ⊢SI (telOK shok (⊢ix (lt-s lt-z) (⊢depth (⊢wk dix))))))
