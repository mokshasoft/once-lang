-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- OCP-0009 · KNOT — the typing judgement's INDEX: the Knot index, the subject, the sort-dependent convoy; building and projecting indices; the generic row machinery (`defRow`, `TelLaw`) and the object-level pieces rows share (`DF`, `⌜Tm⌝`, `mc`).
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
open import DirectedHoTT.Spec.Syntax using ( Defs )
open import DirectedHoTT.Spec.SigWf using ( WfK )
import DirectedHoTT.Metatheory.Entries as Entries
module DirectedHoTT.Examples.Knot.JudgeIx (𝒮 : Defs) (wf : WfK 𝒮) where

-- ★ PLAN-REF: over a well-formed signature, at all its names
private
  𝓃 = Defs.size 𝒮
  ok = Entries.sigOK 𝒮 𝓃 wf
  refs = Entries.refsOK 𝒮 𝓃 (λ p → p) wf



open import normalizer.Syntax.Types using ( _≡_; refl; sym; trans; cong; cong₂; subst; _,_ )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax
import DirectedHoTT.Lib.NatCode 𝒮 𝓃 as ᴵNatCode
open ᴵNatCode using ( fromI )
open import DirectedHoTT.Spec.Typing 𝒮 𝓃 hiding ( _×_; _,,_ )
import DirectedHoTT.Metatheory.TySub 𝒮 𝓃 as ᴵTySub
open ᴵTySub using ( ⊢wk; ⊢-cast; wk-cancel-tm )
open import DirectedHoTT.Metatheory.SubjectReductionBase 𝒮 using () renaming ( wk-sub to wkS )
open import DirectedHoTT.Metatheory.Fundamental.Syntactic 𝒮 using ( ⟨_⟩ᵣ; subTm-var )
open import DirectedHoTT.Metatheory.RedCong 𝒮 using ( red→≅ᵀ; _⟶ᵀ*_; stepᵀ; doneᵀ; ⟶*-trans; ⟶*-appˡ; ⟶*-appʳ; ⟶*-ielimⁱ; ⟶*-ielimᵗ; ⟶*-fst; ⟶*-snd; ⟶*-pairˡ; ⟶*-pairʳ; ⟶*-con; ⟶ᵀ*-IMu )
open import DirectedHoTT.Lib.Sugar 𝒮 𝓃 ok using ( Cons; []; _∷_; conₗ; tag; Lt; lt-z; lt-s; subC; selF-sub; Dσ-sub; []ᵈ; _∷ᵈ_; v₀; v₁; v₂; _,ₚ_ )
open import DirectedHoTT.Lib.SynView 𝒮 𝓃 ok using ( PayV; payV-red; ⊢recFst; ⊢recSnd; ⊢atDepthSK )
open ᴵNatCode using ( ⊢isuc )
open import DirectedHoTT.Examples.Knot.Ctors 𝒮 wf
open import DirectedHoTT.Examples.Knot.Ren 𝒮 wf using ( wk; wk-sub; ⊢wkS )
open import DirectedHoTT.Lib.Tel 𝒮 𝓃 ok
open import DirectedHoTT.Lib.Sorted 𝒮 𝓃 ok using ( ⊢sortOf )
open import DirectedHoTT.Lib.Syn 𝒮 𝓃 ok
open import DirectedHoTT.Lib.SynFib 𝒮 𝓃 ok using ( Row; module Fib; ⊢conRow )
open import DirectedHoTT.Examples.Knot.Sig 𝒮 wf
open import DirectedHoTT.Examples.Knot.Ctx 𝒮 wf
open import DirectedHoTT.Examples.Knot.Lookup 𝒮 wf using ( ⌜Ctx⌝; rows; ⊢rows )


private
  variable
    Δ Θ : Cx

------------------------------------------------------------------------
-- 1. THE CONVOY AND THE INDEX.
------------------------------------------------------------------------

-- over a Knot index `i`: a context at its depth, and — for a term — a type
CT : RTm (Δ ∙)
CT = ⌜Σ⌝ (⌜Ctx⌝ (snd v₀)) (fcase (fst v₁) ⌜Unit⌝ (⌜Ty⌝ (snd v₂)))

CT-sub : (σ : Sub Δ Θ) → subTm (extS σ) (CT {Δ}) ≡ CT
CT-sub {Δ} σ =
  cong₂ (λ D X → ⌜Σ⌝ (⌜IMu⌝ ⌜Nat⌝ D (snd v₀)) (fcase (fst v₁) ⌜Unit⌝ X))
        {x = subTm (extS σ) (CtxD {Δ ∙})} {x' = CtxD}
        {y = subTm (extS (extS (extS σ))) (⌜Ty⌝ (snd v₂))} {y' = ⌜Ty⌝ (snd v₂)}
        (CtxD-sub (extS σ)) (⌜Ty⌝-sub (extS (extS (extS σ))) (snd v₂))

⊢CT : {Γ : Ctx} → (Γ ▹ El (SI 2)) ⊢ CT ∷ U
⊢CT = ⊢⌜Σ⌝ (⊢⌜IMu⌝ ⊢⌜Nat⌝ ⊢CtxD (⊢depth (⊢var here)))
           (⊢fcase ty-U (⊢sortOf (⊢var (there here))) ⊢⌜Unit⌝ (⊢⌜Ty⌝ (⊢depth (⊢var (there (there here))))))

-- (i , t , c)
JT : RTm Δ
JT = ⌜Σ⌝ (SI 2) (⌜Σ⌝ (⌜IMu⌝ (SI 2) KD v₀) (renTm vs CT))

JT-sub : (σ : Sub Δ Θ) → subTm σ (JT {Δ}) ≡ JT
JT-sub {Δ} σ =
  cong₂ (λ D X → ⌜Σ⌝ (SI 2) (⌜Σ⌝ (⌜IMu⌝ (SI 2) D v₀) X))
        {x = subTm (extS σ) (KD {Δ ∙})} {x' = KD}
        {y = subTm (extS (extS σ)) (renTm vs (CT {Δ}))} {y' = renTm vs CT}
        (SD-sub (extS σ) KSig)
        (trans (wkS (extS σ) CT) (cong (renTm vs) {x = subTm (extS σ) CT} {y = CT} (CT-sub σ)))

JT-ren : (ρ : Ren Δ Θ) → renTm ρ (JT {Δ}) ≡ JT
JT-ren ρ = trans (sym (subTm-var ρ JT)) (JT-sub ⟨ ρ ⟩ᵣ)

-- ⚠ `⊢wk ⊢CT` PINNED: an unsolved `renTm vs ?t` against `renTm vs CT`
--   normalises the whole description (`knot-description-normalisation-trap`)
⊢wkCT : {Γ : Ctx} → ((Γ ▹ El (SI 2)) ▹ El (⌜IMu⌝ (SI 2) KD v₀)) ⊢ renTm vs CT ∷ U
⊢wkCT {Γ} = ⊢wk {Γ ▹ El (SI 2)} {El (⌜IMu⌝ (SI 2) KD v₀)} {CT} {U} ⊢CT

⊢JT : {Γ : Ctx} → Γ ⊢ JT ∷ U
⊢JT = ⊢⌜Σ⌝ ⊢SI (⊢⌜Σ⌝ (⊢⌜IMu⌝ ⊢SI ⊢KD (⊢var here)) ⊢wkCT)

-- the convoy's code at an index
CTat : RTm Δ → RTm Δ
CTat i = subTm (single i) CT

ixJ : RTm Δ → RTm Δ → RTm Δ → RTm Δ
ixJ i t c = pair i (t ,ₚ c)

⊢ixJ : {Ξ : Ctx} {i t c : RTm ⌊ Ξ ⌋} → Ξ ⊢ i ∷ El (SI 2) → Ξ ⊢ t ∷ IMu (SI 2) KD i → Ξ ⊢ c ∷ El (CTat i) →
       Ξ ⊢ ixJ i t c ∷ El JT
⊢ixJ {Ξ} {i} {t} {c} di dt dc = ⊢conv p1 (csymᵀ (credᵀ (El-⌜Σ⌝ (SI 2) B1)))
  where
    B1 : RTm (⌊ Ξ ⌋ ∙)
    B1 = ⌜Σ⌝ (⌜IMu⌝ (SI 2) KD v₀) (renTm vs CT)
    B2 : RTm (⌊ Ξ ⌋ ∙)
    B2 = renTm vs (CTat i)
    e1 : subTy (single i) (El B1) ≡ El (⌜Σ⌝ (⌜IMu⌝ (SI 2) KD i) B2)
    e1 = cong El (cong₂ ⌜Σ⌝ {x = subTm (single i) (⌜IMu⌝ (SI 2) KD v₀)} {x' = ⌜IMu⌝ (SI 2) KD i}
                            {y = subTm (extS (single i)) (renTm vs CT)} {y' = B2}
                    (cong (λ D → ⌜IMu⌝ (SI 2) D i) (SD-sub (single i) KSig))
                    (wkS (single i) CT))
    e2 : subTy (single t) (El B2) ≡ El (CTat i)
    e2 = cong El (wk-cancel-tm t (CTat i))
    tyB1 : (Ξ ▹ El (SI 2)) ⊢ty El B1
    tyB1 = ty-El (⊢⌜Σ⌝ (⊢⌜IMu⌝ ⊢SI ⊢KD (⊢var here)) ⊢wkCT)
    tyB2 : (Ξ ▹ El (⌜IMu⌝ (SI 2) KD i)) ⊢ty El B2
    tyB2 = ty-El (⊢wk {Ξ} {El (⌜IMu⌝ (SI 2) KD i)} {CTat i} {U} (sub-lemma' ⊢CT di))
      where
        open ᴵTySub using ( sub-lemma; ⊢single )
        sub-lemma' : {Ξ' : Ctx} {j : RTm ⌊ Ξ' ⌋} → (Ξ' ▹ El (SI 2)) ⊢ CT ∷ U → Ξ' ⊢ j ∷ El (SI 2) → Ξ' ⊢ CTat j ∷ U
        sub-lemma' dC dj = sub-lemma dC (⊢single dj)
    p2 : Ξ ⊢ pair t c ∷ Σ' (El (⌜IMu⌝ (SI 2) KD i)) (El B2)
    p2 = ⊢pair tyB2 (⊢conv dt (csymᵀ (credᵀ El-⌜IMu⌝)))
               (⊢-cast {Ξ} {c} {El (CTat i)} {subTy (single t) (El B2)} (sym e2) dc)
    p1 : Ξ ⊢ ixJ i t c ∷ Σ' (El (SI 2)) (El B1)
    p1 = ⊢pair tyB1 di
               (⊢-cast {Ξ} {pair t c} {El (⌜Σ⌝ (⌜IMu⌝ (SI 2) KD i) B2)} {subTy (single i) (El B1)} (sym e1)
                       (⊢conv p2 (csymᵀ (credᵀ (El-⌜Σ⌝ (⌜IMu⌝ (SI 2) KD i) B2)))))

------------------------------------------------------------------------
-- 2. THE CONVOY AT A SORT, and the two index builders.
------------------------------------------------------------------------

private
  k1 : (u t : RTm Δ) → subTm (extS (single u)) (renTm vs (renTm vs t)) ≡ renTm vs t
  k1 u t = trans (wkS (single u) (renTm vs t)) (cong (renTm vs) (wk-cancel-tm u t))

-- the convoy's code at an index, its two substitutions cast
eCT : (ix : RTm Δ) → CTat ix ≡ ⌜Σ⌝ (⌜Ctx⌝ (snd ix)) (fcase (fst (renTm vs ix)) ⌜Unit⌝ (⌜Ty⌝ (snd (renTm vs (renTm vs ix)))))
eCT {Δ} ix =
  cong₂ (λ D X → ⌜Σ⌝ (⌜IMu⌝ ⌜Nat⌝ D (snd ix)) (fcase (fst (renTm vs ix)) ⌜Unit⌝ X))
        {x = subTm (single ix) (CtxD {Δ ∙})} {x' = CtxD}
        {y = subTm (extS (extS (single ix))) (⌜Ty⌝ (snd v₂))} {y' = ⌜Ty⌝ (snd (renTm vs (renTm vs ix)))}
        (CtxD-sub (single ix)) (⌜Ty⌝-sub (extS (extS (single ix))) (snd v₂))

-- the sort-dependent half, at its two sorts
FT : RTm Δ → RTm (Δ ∙)
FT ix = fcase (fst (renTm vs ix)) ⌜Unit⌝ (⌜Ty⌝ (snd (renTm vs (renTm vs ix))))

-- …instantiated (the pair's second component's type)
eFTat : (ix u : RTm Δ) → subTy (single u) (El (FT ix)) ≡ El (fcase (fst ix) ⌜Unit⌝ (⌜Ty⌝ (snd (renTm vs ix))))
eFTat ix u = cong₂ (λ a X → El (fcase (fst a) ⌜Unit⌝ X))
                   {x = subTm (single u) (renTm vs ix)} {x' = ix}
                   {y = subTm (extS (single u)) (⌜Ty⌝ (snd (renTm vs (renTm vs ix))))} {y' = ⌜Ty⌝ (snd (renTm vs ix))}
                   (wk-cancel-tm u ix)
                   (trans (⌜Ty⌝-sub (extS (single u)) (snd (renTm vs (renTm vs ix))))
                          (cong (λ z → ⌜Ty⌝ (snd z)) {x = subTm (extS (single u)) (renTm vs (renTm vs ix))} {y = renTm vs ix}
                                (k1 u ix)))

-- the type half at sort 1 converts to the Knot's types
eTy1 : (j : RTm Δ) → El (subTm (single fzero) (⌜Ty⌝ (snd (renTm vs ((tag 1) ,ₚ j))))) ≡ El (⌜Ty⌝ (snd ((tag 1) ,ₚ j)))
eTy1 j = cong El (trans (⌜Ty⌝-sub (single fzero) (snd (renTm vs ((tag 1) ,ₚ j))))
                        (cong (λ z → ⌜Ty⌝ (snd z)) {x = subTm (single fzero) (renTm vs ((tag 1) ,ₚ j))} {y = pair (tag 1) j}
                              (wk-cancel-tm fzero ((tag 1) ,ₚ j))))

red1 : (j : RTm Δ) → El (fcase (fst ((tag 1) ,ₚ j)) ⌜Unit⌝ (⌜Ty⌝ (snd (renTm vs ((tag 1) ,ₚ j)))))
                     ≅ᵀ El (subTm (single fzero) (⌜Ty⌝ (snd (renTm vs ((tag 1) ,ₚ j)))))
red1 j = red→≅ᵀ (stepᵀ (ξ-El (ξ-fcaseᵗ (βfst (tag 1) j)))
                 (stepᵀ (ξ-El (fcase-s fzero ⌜Unit⌝ (⌜Ty⌝ (snd (renTm vs ((tag 1) ,ₚ j)))))) doneᵀ))

tyK≅ : (j : RTm Δ) → El (⌜Ty⌝ (snd ((tag 1) ,ₚ j))) ≅ᵀ K 0 j
tyK≅ j = ctrnᵀ (credᵀ El-⌜Ty⌝) (credᵀ (ξ-SK (βsnd (tag 1) j)))

red0 : (j : RTm Δ) → El (fcase (fst ((tag 0) ,ₚ j)) ⌜Unit⌝ (⌜Ty⌝ (snd (renTm vs ((tag 0) ,ₚ j))))) ≅ᵀ Unit
red0 j = red→≅ᵀ (stepᵀ (ξ-El (ξ-fcaseᵗ (βfst (tag 0) j)))
                 (stepᵀ (ξ-El (fcase-z ⌜Unit⌝ (⌜Ty⌝ (snd (renTm vs ((tag 0) ,ₚ j)))))) (stepᵀ El-⌜Unit⌝ doneᵀ)))

ctxK≅ : {s : ℕ} (j : RTm Δ) → El (⌜Ctx⌝ (snd ((tag s) ,ₚ j))) ≅ᵀ KCtx j
ctxK≅ {s = s} j = ctrnᵀ (credᵀ El-⌜IMu⌝) (credᵀ (ξ-IMuⁱ (βsnd (tag s) j)))

module _ {Ξ : Ctx} {s : ℕ} {j c : RTm ⌊ Ξ ⌋} where
  private
    ix : RTm ⌊ Ξ ⌋
    ix = pair (tag s) j
    dΣ : Ξ ⊢ c ∷ El (CTat ix) → Ξ ⊢ c ∷ Σ' (El (⌜Ctx⌝ (snd ix))) (El (FT ix))
    dΣ dc = ⊢conv (⊢-cast {Ξ} {c} {El (CTat ix)} {El (⌜Σ⌝ (⌜Ctx⌝ (snd ix)) (FT ix))} (cong El (eCT ix)) dc)
                  (credᵀ (El-⌜Σ⌝ (⌜Ctx⌝ (snd ix)) (FT ix)))

  -- the context, at any sort
  ⊢ctxOf : Ξ ⊢ c ∷ El (CTat ((tag s) ,ₚ j)) → Ξ ⊢ fst c ∷ KCtx j
  ⊢ctxOf dc = ⊢conv (⊢fst (dΣ dc)) (ctrnᵀ (credᵀ El-⌜IMu⌝) (credᵀ (ξ-IMuⁱ (βsnd (tag s) j))))

  -- the type half, read at the instance of its sort
  eFT : subTy (single (fst c)) (El (FT ((tag s) ,ₚ j))) ≡ El (fcase (fst ((tag s) ,ₚ j)) ⌜Unit⌝ (⌜Ty⌝ (snd (renTm vs ((tag s) ,ₚ j)))))
  eFT = cong₂ (λ a X → El (fcase (fst a) ⌜Unit⌝ X))
              {x = subTm (single (fst c)) (renTm vs ix)} {x' = ix}
              {y = subTm (extS (single (fst c))) (⌜Ty⌝ (snd (renTm vs (renTm vs ix))))} {y' = ⌜Ty⌝ (snd (renTm vs ix))}
              (wk-cancel-tm (fst c) ix)
              (trans (⌜Ty⌝-sub (extS (single (fst c))) (snd (renTm vs (renTm vs ix))))
                     (cong (λ z → ⌜Ty⌝ (snd z)) {x = subTm (extS (single (fst c))) (renTm vs (renTm vs ix))} {y = renTm vs ix}
                           (k1 (fst c) ix)))

  ⊢sndFT : Ξ ⊢ c ∷ El (CTat ((tag s) ,ₚ j)) → Ξ ⊢ snd c ∷ El (fcase (fst ((tag s) ,ₚ j)) ⌜Unit⌝ (⌜Ty⌝ (snd (renTm vs ((tag s) ,ₚ j)))))
  ⊢sndFT dc = ⊢-cast {Ξ} {snd c} {subTy (single (fst c)) (El (FT ix))} eFT (⊢snd (dΣ dc))

-- a term's type (sort 1)
⊢tyOf : {Ξ : Ctx} {j c : RTm ⌊ Ξ ⌋} → Ξ ⊢ c ∷ El (CTat ((tag 1) ,ₚ j)) → Ξ ⊢ snd c ∷ K 0 j
⊢tyOf {Ξ} {j} {c} dc =
  ⊢conv (⊢-cast {Ξ} {snd c} {El (subTm (single fzero) (⌜Ty⌝ (snd (renTm vs ((tag 1) ,ₚ j)))))}
                {El (⌜Ty⌝ (snd ((tag 1) ,ₚ j)))} (eTy1 j)
                (⊢conv (⊢sndFT {s = 1} dc) (red1 j)))
        (tyK≅ j)

------------------------------------------------------------------------
-- 3. BUILDING AN INDEX: the convoy at each sort, and `Γ ⊢ty A` / `Γ ⊢ t ∷ A`.
------------------------------------------------------------------------

module _ {Ξ : Ctx} {s : ℕ} {j g u : RTm ⌊ Ξ ⌋} (lt : Lt s 2) (dj : Ξ ⊢ j ∷ El ⌜Nat⌝) where
  private
    ix : RTm ⌊ Ξ ⌋
    ix = pair (tag s) j
    dix : Ξ ⊢ ix ∷ El (SI 2)
    dix = ⊢ix lt dj
    tyF : (Ξ ▹ El (⌜Ctx⌝ (snd ix))) ⊢ty El (FT ix)
    tyF = ty-El (⊢fcase ty-U (⊢sortOf (⊢wk dix)) ⊢⌜Unit⌝ (⊢⌜Ty⌝ (⊢depth (⊢wk (⊢wk dix)))))
  -- a convoy from its two halves
  ⊢conv₂ : Ξ ⊢ g ∷ KCtx j → Ξ ⊢ u ∷ El (fcase (fst ((tag s) ,ₚ j)) ⌜Unit⌝ (⌜Ty⌝ (snd (renTm vs ((tag s) ,ₚ j))))) →
           Ξ ⊢ pair g u ∷ El (CTat ((tag s) ,ₚ j))
  ⊢conv₂ dg du =
    ⊢-cast {Ξ} {pair g u} {El (⌜Σ⌝ (⌜Ctx⌝ (snd ix)) (FT ix))} {El (CTat ix)} (cong El (sym (eCT ix)))
      (⊢conv (⊢pair tyF (⊢conv dg (csymᵀ (ctxK≅ j)))
                        (⊢-cast {Ξ} {u} {El (fcase (fst ix) ⌜Unit⌝ (⌜Ty⌝ (snd (renTm vs ix))))} {subTy (single g) (El (FT ix))}
                                (sym (eFTat ix g)) du))
             (csymᵀ (credᵀ (El-⌜Σ⌝ (⌜Ctx⌝ (snd ix)) (FT ix)))))

⊢cTy : {Ξ : Ctx} {j g : RTm ⌊ Ξ ⌋} → Ξ ⊢ j ∷ El ⌜Nat⌝ → Ξ ⊢ g ∷ KCtx j → Ξ ⊢ pair g unit ∷ El (CTat ((tag 0) ,ₚ j))
⊢cTy {j = j} dj dg = ⊢conv₂ lt-z dj dg (⊢conv ⊢unit (csymᵀ (red0 j)))

⊢cTm : {Ξ : Ctx} {j g a : RTm ⌊ Ξ ⌋} → Ξ ⊢ j ∷ El ⌜Nat⌝ → Ξ ⊢ g ∷ KCtx j → Ξ ⊢ a ∷ K 0 j →
       Ξ ⊢ pair g a ∷ El (CTat ((tag 1) ,ₚ j))
⊢cTm {Ξ} {j} {g} {a} dj dg da =
  ⊢conv₂ (lt-s lt-z) dj dg
    (⊢conv (⊢-cast {Ξ} {a} {El (⌜Ty⌝ (snd ((tag 1) ,ₚ j)))} {El (subTm (single fzero) (⌜Ty⌝ (snd (renTm vs ((tag 1) ,ₚ j)))))}
                   (sym (eTy1 j)) (⊢conv da (csymᵀ (tyK≅ j))))
           (csymᵀ (red1 j)))

-- ★ the two judgement forms' indices
tyIx : RTm Δ → RTm Δ → RTm Δ → RTm Δ
tyIx j g A = ixJ ((tag 0) ,ₚ j) A (g ,ₚ unit)

tmIx : RTm Δ → RTm Δ → RTm Δ → RTm Δ → RTm Δ
tmIx j g t A = ixJ ((tag 1) ,ₚ j) t (g ,ₚ A)

⊢tyIx : {Ξ : Ctx} {j g A : RTm ⌊ Ξ ⌋} → Ξ ⊢ j ∷ El ⌜Nat⌝ → Ξ ⊢ g ∷ KCtx j → Ξ ⊢ A ∷ K 0 j → Ξ ⊢ tyIx j g A ∷ El JT
⊢tyIx dj dg dA = ⊢ixJ (⊢ix lt-z dj) (⊢SK→IMu {sg = KSig} dA) (⊢cTy dj dg)

⊢tmIx : {Ξ : Ctx} {j g t A : RTm ⌊ Ξ ⌋} → Ξ ⊢ j ∷ El ⌜Nat⌝ → Ξ ⊢ g ∷ KCtx j → Ξ ⊢ t ∷ K 1 j → Ξ ⊢ A ∷ K 0 j →
        Ξ ⊢ tmIx j g t A ∷ El JT
⊢tmIx dj dg dt dA = ⊢ixJ (⊢ix (lt-s lt-z) dj) (⊢SK→IMu {sg = KSig} dt) (⊢cTm dj dg dA)


------------------------------------------------------------------------
-- 4. ★ THE `⊢ty` ROWS: one per type former, its premises at computed
--   indices.  A row with no code and no closed function inside commutes
--   with substitution DEFINITIONALLY; its law is `rows-sub'`.
------------------------------------------------------------------------

rows-sub' : {c : ℕ} (τ : Sub Δ Θ) (Cs : Cons Δ c) → subTm τ (rows Cs) ≡ rows (subC τ Cs)
rows-sub' τ Cs = Dσ-sub τ Cs

row1 : Tel Δ → RTm Δ
row1 T = rows (⌜ T ⌝ᵗ ∷ [])

-- DescF I, object-level:  Π (El I) (Desc (wk I))
DF : RTm Δ → RTm Δ → RTm Δ
DF j I = kPi (kEl I) (kDesc (wk 1 j I))

DF-sub : (σ : Sub Δ Θ) (j I : RTm Δ) → subTm σ (DF j I) ≡ DF (subTm σ j) (subTm σ I)
DF-sub σ j I = cong (λ z → kPi (kEl (subTm σ I)) (kDesc z)) {x = subTm σ (wk 1 j I)} {y = wk 1 (subTm σ j) (subTm σ I)}
                    (wk-sub σ 1 j I)

⊢DF : {Ξ : Ctx} {j I : RTm ⌊ Ξ ⌋} → Ξ ⊢ j ∷ El ⌜Nat⌝ → Ξ ⊢ I ∷ K 1 j → Ξ ⊢ DF j I ∷ K 0 j
⊢DF dj dI = ⊢kPi dj (⊢kEl dj dI) (⊢kDesc (⊢isuc dj) (⊢wkS (lt-s lt-z) dj dI))


-- a row from its telescope and the telescope's law (`refl` when definitional);
--   the telescope is over the family's PARAMETER `q` too (PLAN-REF: the
--   quoted signature), which a row that does not cite it ignores
TelLaw : ({Δ : Cx} → RTm Δ → RTm Δ → RTm Δ → RTm Δ → Tel Δ) → Set
TelLaw T = {Δ Θ : Cx} (σ : Sub Δ Θ) (q j p c : RTm Δ) →
           subTm σ ⌜ T q j p c ⌝ᵗ ≡ ⌜ T (subTm σ q) (subTm σ j) (subTm σ p) (subTm σ c) ⌝ᵗ

defRow : (T : {Δ : Cx} → RTm Δ → RTm Δ → RTm Δ → RTm Δ → Tel Δ) → TelLaw T → Row
defRow T law = record
  { R = λ q j p c → row1 (T q j p c)
  ; R-sub = λ σ q j p c →
      trans (rows-sub' σ (⌜ T q j p c ⌝ᵗ ∷ []))
            (cong (λ C → rows (C ∷ [])) {x = subTm σ ⌜ T q j p c ⌝ᵗ} {y = ⌜ T (subTm σ q) (subTm σ j) (subTm σ p) (subTm σ c) ⌝ᵗ}
                  (law σ q j p c)) }


-- ★ DIh: its index code `I` is not a subterm, so it is a σ-field; the
--   motive context `(Γ ▹ El I) ▹ IMu (wk I) (wk D) (var 0)` is built
--   object-level (`mc`)
opaque
  ⌜Tm⌝ : RTm Δ → RTm Δ
  ⌜Tm⌝ d = ⌜IMu⌝ (SI 2) KD ((tag 1) ,ₚ d)

  ⌜Tm⌝-sub : (σ : Sub Δ Θ) (d : RTm Δ) → subTm σ (⌜Tm⌝ d) ≡ ⌜Tm⌝ (subTm σ d)
  ⌜Tm⌝-sub σ d = cong (λ D → ⌜IMu⌝ (SI 2) D ((tag 1) ,ₚ (subTm σ d))) (SD-sub σ KSig)

  El-⌜Tm⌝ : {d : RTm Δ} → El (⌜Tm⌝ d) ⟶ᵀ K 1 d
  El-⌜Tm⌝ = El-⌜SK⌝

  ⊢⌜Tm⌝ : {Ξ : Ctx} {d : RTm ⌊ Ξ ⌋} → Ξ ⊢ d ∷ El ⌜Nat⌝ → Ξ ⊢ ⌜Tm⌝ d ∷ U
  ⊢⌜Tm⌝ dd = ⊢⌜IMu⌝ ⊢SI ⊢KD (⊢ix (lt-s lt-z) dd)

⌜Tm⌝-ren : (ρ : Ren Δ Θ) (d : RTm Δ) → renTm ρ (⌜Tm⌝ d) ≡ ⌜Tm⌝ (renTm ρ d)
⌜Tm⌝-ren ρ d = trans (sym (subTm-var ρ (⌜Tm⌝ d))) (trans (⌜Tm⌝-sub ⟨ ρ ⟩ᵣ d)
                 (cong ⌜Tm⌝ {x = subTm ⟨ ρ ⟩ᵣ d} {y = renTm ρ d} (subTm-var ρ d)))


mc : RTm Δ → RTm Δ → RTm Δ → RTm Δ → RTm Δ
mc j g I D = cext (cext g (kEl I)) (kIMu (wk 1 j I) (wk 1 j D) (kvar fzero))

mc-sub : (σ : Sub Δ Θ) (j g I D : RTm Δ) → subTm σ (mc j g I D) ≡ mc (subTm σ j) (subTm σ g) (subTm σ I) (subTm σ D)
mc-sub σ j g I D =
  cong₂ (λ a b → cext (cext (subTm σ g) (kEl (subTm σ I))) (kIMu a b (kvar fzero)))
        {x = subTm σ (wk 1 j I)} {x' = wk 1 (subTm σ j) (subTm σ I)} {y = subTm σ (wk 1 j D)} {y' = wk 1 (subTm σ j) (subTm σ D)}
        (wk-sub σ 1 j I) (wk-sub σ 1 j D)


-- empty fibre (a head no rule concludes with)
rNone : Row
rNone = record { R = λ q j p c → rows [] ; R-sub = λ σ q j p c → refl }

-- a payload of the Knot, at its normal form
⊢payK : {Ξ : Ctx} {s : ℕ} {j p : RTm ⌊ Ξ ⌋} {sh : Shape} → Lt s 2 → ShOK 2 sh → Ξ ⊢ j ∷ El ⌜Nat⌝ →
        Args Ξ 2 KSig j sh p → Ξ ⊢ p ∷ PayV sh ((tag s) ,ₚ j) (SI 2) (SD KSig)
⊢payK {s = s} {j = j} {sh = sh} lt ok dj as =
  ⊢conv (⊢payArgs ⊢KD ok (⊢ix lt dj) (step (βsnd (tag s) j) done) as) (red→≅ᵀ (payV-red sh ((tag s) ,ₚ j) (SI 2) (SD KSig)))
