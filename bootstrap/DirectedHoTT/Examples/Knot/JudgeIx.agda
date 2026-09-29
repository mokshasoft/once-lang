-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- OCP-0009 · KNOT — the typing judgement's INDEX: the Knot index, the subject, the sort-dependent convoy; building and projecting indices; the generic row machinery (`defRow`, `TelLaw`) and the object-level pieces rows share (`DF`, `⌜Tm⌝`, `mc`).
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Knot.JudgeIx where


open import normalizer.Syntax.Types using ( _≡_; refl; sym; trans; cong; cong₂; subst; _,_ )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax hiding ( Fin )
open import DirectedHoTT.Spec.Typing hiding ( _×_; _,,_ )
open import DirectedHoTT.Metatheory.TySub using ( ⊢wk; ⊢-cast; wk-cancel-tm )
open import DirectedHoTT.Metatheory.SubjectReductionBase using () renaming ( wk-sub to wkS )
open import DirectedHoTT.Metatheory.Fundamental.Syntactic using ( ⟨_⟩ᵣ; subTm-var )
open import DirectedHoTT.Metatheory.RedCong using ( red→≅ᵀ; _⟶ᵀ*_; stepᵀ; doneᵀ; ⟶*-trans; ⟶*-appˡ; ⟶*-appʳ; ⟶*-ielimⁱ; ⟶*-ielimᵗ; ⟶*-fst; ⟶*-snd; ⟶*-pairˡ; ⟶*-pairʳ; ⟶*-con; ⟶ᵀ*-IMu )
open import DirectedHoTT.Lib.Sugar using ( Cons; []; _∷_; conₗ; tag; Lt; lt-z; lt-s; subC; selF-sub; []ᵈ; _∷ᵈ_ )
open import DirectedHoTT.Lib.SynView using ( PayV; payV-red; ⊢recFst; ⊢recSnd; ⊢atDepth )
open import DirectedHoTT.Lib.FinFam using ( FinI; ffz; ⊢ffz; ⊢isuc )
open import DirectedHoTT.Examples.Knot.Ctors
open import DirectedHoTT.Examples.Knot.Ren using ( wk; wk-sub; ⊢wkS )
open import DirectedHoTT.Lib.Tel
open import DirectedHoTT.Lib.Sorted using ( ⊢sortOf )
open import DirectedHoTT.Lib.Syn
open import DirectedHoTT.Lib.SynFib using ( Row; module Fib; ⊢conRow )
open import DirectedHoTT.Examples.Knot.Sig
open import DirectedHoTT.Examples.Knot.Ctx
open import DirectedHoTT.Examples.Knot.Lookup using ( ⌜Ctx⌝; rows; ⊢rows )


private
  variable
    Δ Θ : Cx

------------------------------------------------------------------------
-- 1. THE CONVOY AND THE INDEX.
------------------------------------------------------------------------

-- over a Knot index `i`: a context at its depth, and — for a term — a type
CT : RTm (Δ ∙)
CT = ⌜Σ⌝ (⌜Ctx⌝ (snd (var vz))) (fcase (fst (var (vs vz))) ⌜Unit⌝ (⌜Ty⌝ (snd (var (vs (vs vz))))))

CT-sub : (σ : Sub Δ Θ) → subTm (extS σ) (CT {Δ}) ≡ CT
CT-sub {Δ} σ =
  cong₂ (λ D X → ⌜Σ⌝ (⌜IMu⌝ ⌜Nat⌝ D (snd (var vz))) (fcase (fst (var (vs vz))) ⌜Unit⌝ X))
        {x = subTm (extS σ) (CtxD {Δ ∙})} {x' = CtxD}
        {y = subTm (extS (extS (extS σ))) (⌜Ty⌝ (snd (var (vs (vs vz)))))} {y' = ⌜Ty⌝ (snd (var (vs (vs vz))))}
        (CtxD-sub (extS σ)) (⌜Ty⌝-sub (extS (extS (extS σ))) (snd (var (vs (vs vz)))))

⊢CT : {Γ : Ctx} → (Γ ▹ El (SI 2)) ⊢ CT ∷ U
⊢CT = ⊢⌜Σ⌝ (⊢⌜IMu⌝ ⊢⌜Nat⌝ ⊢CtxD (⊢depth (⊢var here)))
           (⊢fcase ty-U (⊢sortOf (⊢var (there here))) ⊢⌜Unit⌝ (⊢⌜Ty⌝ (⊢depth (⊢var (there (there here))))))

-- (i , t , c)
JT : RTm Δ
JT = ⌜Σ⌝ (SI 2) (⌜Σ⌝ (⌜IMu⌝ (SI 2) KD (var vz)) (renTm vs CT))

JT-sub : (σ : Sub Δ Θ) → subTm σ (JT {Δ}) ≡ JT
JT-sub {Δ} σ =
  cong₂ (λ D X → ⌜Σ⌝ (SI 2) (⌜Σ⌝ (⌜IMu⌝ (SI 2) D (var vz)) X))
        {x = subTm (extS σ) (KD {Δ ∙})} {x' = KD}
        {y = subTm (extS (extS σ)) (renTm vs (CT {Δ}))} {y' = renTm vs CT}
        (SD-sub (extS σ) KSig)
        (trans (wkS (extS σ) CT) (cong (renTm vs) {x = subTm (extS σ) CT} {y = CT} (CT-sub σ)))

JT-ren : (ρ : Ren Δ Θ) → renTm ρ (JT {Δ}) ≡ JT
JT-ren ρ = trans (sym (subTm-var ρ JT)) (JT-sub ⟨ ρ ⟩ᵣ)

-- ⚠ `⊢wk ⊢CT` PINNED: an unsolved `renTm vs ?t` against `renTm vs CT`
--   normalises the whole description (`knot-description-normalisation-trap`)
⊢wkCT : {Γ : Ctx} → ((Γ ▹ El (SI 2)) ▹ El (⌜IMu⌝ (SI 2) KD (var vz))) ⊢ renTm vs CT ∷ U
⊢wkCT {Γ} = ⊢wk {Γ ▹ El (SI 2)} {El (⌜IMu⌝ (SI 2) KD (var vz))} {CT} {U} ⊢CT

⊢JT : {Γ : Ctx} → Γ ⊢ JT ∷ U
⊢JT = ⊢⌜Σ⌝ ⊢SI (⊢⌜Σ⌝ (⊢⌜IMu⌝ ⊢SI ⊢KD (⊢var here)) ⊢wkCT)

-- the convoy's code at an index
CTat : RTm Δ → RTm Δ
CTat i = subTm (single i) CT

ixJ : RTm Δ → RTm Δ → RTm Δ → RTm Δ
ixJ i t c = pair i (pair t c)

⊢ixJ : {Ξ : Ctx} {i t c : RTm ⌊ Ξ ⌋} → Ξ ⊢ i ∷ El (SI 2) → Ξ ⊢ t ∷ IMu (SI 2) KD i → Ξ ⊢ c ∷ El (CTat i) →
       Ξ ⊢ ixJ i t c ∷ El JT
⊢ixJ {Ξ} {i} {t} {c} di dt dc = ⊢conv p1 (csymᵀ (credᵀ (El-⌜Σ⌝ (SI 2) B1)))
  where
    B1 : RTm (⌊ Ξ ⌋ ∙)
    B1 = ⌜Σ⌝ (⌜IMu⌝ (SI 2) KD (var vz)) (renTm vs CT)
    B2 : RTm (⌊ Ξ ⌋ ∙)
    B2 = renTm vs (CTat i)
    e1 : subTy (single i) (El B1) ≡ El (⌜Σ⌝ (⌜IMu⌝ (SI 2) KD i) B2)
    e1 = cong El (cong₂ ⌜Σ⌝ {x = subTm (single i) (⌜IMu⌝ (SI 2) KD (var vz))} {x' = ⌜IMu⌝ (SI 2) KD i}
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
        open import DirectedHoTT.Metatheory.TySub using ( sub-lemma; ⊢single )
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
        {y = subTm (extS (extS (single ix))) (⌜Ty⌝ (snd (var (vs (vs vz)))))} {y' = ⌜Ty⌝ (snd (renTm vs (renTm vs ix)))}
        (CtxD-sub (single ix)) (⌜Ty⌝-sub (extS (extS (single ix))) (snd (var (vs (vs vz)))))

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
eTy1 : (j : RTm Δ) → El (subTm (single fzero) (⌜Ty⌝ (snd (renTm vs (pair (tag 1) j))))) ≡ El (⌜Ty⌝ (snd (pair (tag 1) j)))
eTy1 j = cong El (trans (⌜Ty⌝-sub (single fzero) (snd (renTm vs (pair (tag 1) j))))
                        (cong (λ z → ⌜Ty⌝ (snd z)) {x = subTm (single fzero) (renTm vs (pair (tag 1) j))} {y = pair (tag 1) j}
                              (wk-cancel-tm fzero (pair (tag 1) j))))

red1 : (j : RTm Δ) → El (fcase (fst (pair (tag 1) j)) ⌜Unit⌝ (⌜Ty⌝ (snd (renTm vs (pair (tag 1) j)))))
                     ≅ᵀ El (subTm (single fzero) (⌜Ty⌝ (snd (renTm vs (pair (tag 1) j)))))
red1 j = red→≅ᵀ (stepᵀ (ξ-El (ξ-fcaseᵗ (βfst (tag 1) j)))
                 (stepᵀ (ξ-El (fcase-s fzero ⌜Unit⌝ (⌜Ty⌝ (snd (renTm vs (pair (tag 1) j)))))) doneᵀ))

tyK≅ : (j : RTm Δ) → El (⌜Ty⌝ (snd (pair (tag 1) j))) ≅ᵀ K 0 j
tyK≅ j = ctrnᵀ (credᵀ El-⌜Ty⌝) (credᵀ (ξ-IMuⁱ (ξ-pairʳ (βsnd (tag 1) j))))

red0 : (j : RTm Δ) → El (fcase (fst (pair (tag 0) j)) ⌜Unit⌝ (⌜Ty⌝ (snd (renTm vs (pair (tag 0) j))))) ≅ᵀ Unit
red0 j = red→≅ᵀ (stepᵀ (ξ-El (ξ-fcaseᵗ (βfst (tag 0) j)))
                 (stepᵀ (ξ-El (fcase-z ⌜Unit⌝ (⌜Ty⌝ (snd (renTm vs (pair (tag 0) j)))))) (stepᵀ El-⌜Unit⌝ doneᵀ)))

ctxK≅ : {s : ℕ} (j : RTm Δ) → El (⌜Ctx⌝ (snd (pair (tag s) j))) ≅ᵀ KCtx j
ctxK≅ {s = s} j = ctrnᵀ (credᵀ El-⌜IMu⌝) (credᵀ (ξ-IMuⁱ (βsnd (tag s) j)))

module _ {Ξ : Ctx} {s : ℕ} {j c : RTm ⌊ Ξ ⌋} where
  private
    ix : RTm ⌊ Ξ ⌋
    ix = pair (tag s) j
    dΣ : Ξ ⊢ c ∷ El (CTat ix) → Ξ ⊢ c ∷ Σ' (El (⌜Ctx⌝ (snd ix))) (El (FT ix))
    dΣ dc = ⊢conv (⊢-cast {Ξ} {c} {El (CTat ix)} {El (⌜Σ⌝ (⌜Ctx⌝ (snd ix)) (FT ix))} (cong El (eCT ix)) dc)
                  (credᵀ (El-⌜Σ⌝ (⌜Ctx⌝ (snd ix)) (FT ix)))

  -- the context, at any sort
  ⊢ctxOf : Ξ ⊢ c ∷ El (CTat ix) → Ξ ⊢ fst c ∷ KCtx j
  ⊢ctxOf dc = ⊢conv (⊢fst (dΣ dc)) (ctrnᵀ (credᵀ El-⌜IMu⌝) (credᵀ (ξ-IMuⁱ (βsnd (tag s) j))))

  -- the type half, read at the instance of its sort
  eFT : subTy (single (fst c)) (El (FT ix)) ≡ El (fcase (fst ix) ⌜Unit⌝ (⌜Ty⌝ (snd (renTm vs ix))))
  eFT = cong₂ (λ a X → El (fcase (fst a) ⌜Unit⌝ X))
              {x = subTm (single (fst c)) (renTm vs ix)} {x' = ix}
              {y = subTm (extS (single (fst c))) (⌜Ty⌝ (snd (renTm vs (renTm vs ix))))} {y' = ⌜Ty⌝ (snd (renTm vs ix))}
              (wk-cancel-tm (fst c) ix)
              (trans (⌜Ty⌝-sub (extS (single (fst c))) (snd (renTm vs (renTm vs ix))))
                     (cong (λ z → ⌜Ty⌝ (snd z)) {x = subTm (extS (single (fst c))) (renTm vs (renTm vs ix))} {y = renTm vs ix}
                           (k1 (fst c) ix)))

  ⊢sndFT : Ξ ⊢ c ∷ El (CTat ix) → Ξ ⊢ snd c ∷ El (fcase (fst ix) ⌜Unit⌝ (⌜Ty⌝ (snd (renTm vs ix))))
  ⊢sndFT dc = ⊢-cast {Ξ} {snd c} {subTy (single (fst c)) (El (FT ix))} eFT (⊢snd (dΣ dc))

-- a term's type (sort 1)
⊢tyOf : {Ξ : Ctx} {j c : RTm ⌊ Ξ ⌋} → Ξ ⊢ c ∷ El (CTat (pair (tag 1) j)) → Ξ ⊢ snd c ∷ K 0 j
⊢tyOf {Ξ} {j} {c} dc =
  ⊢conv (⊢-cast {Ξ} {snd c} {El (subTm (single fzero) (⌜Ty⌝ (snd (renTm vs (pair (tag 1) j)))))}
                {El (⌜Ty⌝ (snd (pair (tag 1) j)))} (eTy1 j)
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
  ⊢conv₂ : Ξ ⊢ g ∷ KCtx j → Ξ ⊢ u ∷ El (fcase (fst ix) ⌜Unit⌝ (⌜Ty⌝ (snd (renTm vs ix)))) →
           Ξ ⊢ pair g u ∷ El (CTat ix)
  ⊢conv₂ dg du =
    ⊢-cast {Ξ} {pair g u} {El (⌜Σ⌝ (⌜Ctx⌝ (snd ix)) (FT ix))} {El (CTat ix)} (cong El (sym (eCT ix)))
      (⊢conv (⊢pair tyF (⊢conv dg (csymᵀ (ctxK≅ j)))
                        (⊢-cast {Ξ} {u} {El (fcase (fst ix) ⌜Unit⌝ (⌜Ty⌝ (snd (renTm vs ix))))} {subTy (single g) (El (FT ix))}
                                (sym (eFTat ix g)) du))
             (csymᵀ (credᵀ (El-⌜Σ⌝ (⌜Ctx⌝ (snd ix)) (FT ix)))))

⊢cTy : {Ξ : Ctx} {j g : RTm ⌊ Ξ ⌋} → Ξ ⊢ j ∷ El ⌜Nat⌝ → Ξ ⊢ g ∷ KCtx j → Ξ ⊢ pair g unit ∷ El (CTat (pair (tag 0) j))
⊢cTy {j = j} dj dg = ⊢conv₂ lt-z dj dg (⊢conv ⊢unit (csymᵀ (red0 j)))

⊢cTm : {Ξ : Ctx} {j g a : RTm ⌊ Ξ ⌋} → Ξ ⊢ j ∷ El ⌜Nat⌝ → Ξ ⊢ g ∷ KCtx j → Ξ ⊢ a ∷ K 0 j →
       Ξ ⊢ pair g a ∷ El (CTat (pair (tag 1) j))
⊢cTm {Ξ} {j} {g} {a} dj dg da =
  ⊢conv₂ (lt-s lt-z) dj dg
    (⊢conv (⊢-cast {Ξ} {a} {El (⌜Ty⌝ (snd (pair (tag 1) j)))} {El (subTm (single fzero) (⌜Ty⌝ (snd (renTm vs (pair (tag 1) j)))))}
                   (sym (eTy1 j)) (⊢conv da (csymᵀ (tyK≅ j))))
           (csymᵀ (red1 j)))

-- ★ the two judgement forms' indices
tyIx : RTm Δ → RTm Δ → RTm Δ → RTm Δ
tyIx j g A = ixJ (pair (tag 0) j) A (pair g unit)

tmIx : RTm Δ → RTm Δ → RTm Δ → RTm Δ → RTm Δ
tmIx j g t A = ixJ (pair (tag 1) j) t (pair g A)

⊢tyIx : {Ξ : Ctx} {j g A : RTm ⌊ Ξ ⌋} → Ξ ⊢ j ∷ El ⌜Nat⌝ → Ξ ⊢ g ∷ KCtx j → Ξ ⊢ A ∷ K 0 j → Ξ ⊢ tyIx j g A ∷ El JT
⊢tyIx dj dg dA = ⊢ixJ (⊢ix lt-z dj) dA (⊢cTy dj dg)

⊢tmIx : {Ξ : Ctx} {j g t A : RTm ⌊ Ξ ⌋} → Ξ ⊢ j ∷ El ⌜Nat⌝ → Ξ ⊢ g ∷ KCtx j → Ξ ⊢ t ∷ K 1 j → Ξ ⊢ A ∷ K 0 j →
        Ξ ⊢ tmIx j g t A ∷ El JT
⊢tmIx dj dg dt dA = ⊢ixJ (⊢ix (lt-s lt-z) dj) dt (⊢cTm dj dg dA)


------------------------------------------------------------------------
-- 4. ★ THE `⊢ty` ROWS: one per type former, its premises at computed
--   indices.  A row with no code and no closed function inside commutes
--   with substitution DEFINITIONALLY; its law is `rows-sub'`.
------------------------------------------------------------------------

rows-sub' : {c : ℕ} (τ : Sub Δ Θ) (Cs : Cons Δ c) → subTm τ (rows Cs) ≡ rows (subC τ Cs)
rows-sub' {c = c} τ Cs = cong (dσ (⌜Fin⌝ c)) (selF-sub τ Cs)

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


-- a row from its telescope and the telescope's law (`refl` when definitional)
TelLaw : ({Δ : Cx} → RTm Δ → RTm Δ → RTm Δ → Tel Δ) → Set
TelLaw T = {Δ Θ : Cx} (σ : Sub Δ Θ) (j p c : RTm Δ) →
           subTm σ ⌜ T j p c ⌝ᵗ ≡ ⌜ T (subTm σ j) (subTm σ p) (subTm σ c) ⌝ᵗ

defRow : (T : {Δ : Cx} → RTm Δ → RTm Δ → RTm Δ → Tel Δ) → TelLaw T → Row
defRow T law = record
  { R = λ j p c → row1 (T j p c)
  ; R-sub = λ σ j p c →
      trans (rows-sub' σ (⌜ T j p c ⌝ᵗ ∷ []))
            (cong (λ C → rows (C ∷ [])) {x = subTm σ ⌜ T j p c ⌝ᵗ} {y = ⌜ T (subTm σ j) (subTm σ p) (subTm σ c) ⌝ᵗ}
                  (law σ j p c)) }


-- ★ DIh: its index code `I` is not a subterm, so it is a σ-field; the
--   motive context `(Γ ▹ El I) ▹ IMu (wk I) (wk D) (var 0)` is built
--   object-level (`mc`)
opaque
  ⌜Tm⌝ : RTm Δ → RTm Δ
  ⌜Tm⌝ d = ⌜IMu⌝ (SI 2) KD (pair (tag 1) d)

  ⌜Tm⌝-sub : (σ : Sub Δ Θ) (d : RTm Δ) → subTm σ (⌜Tm⌝ d) ≡ ⌜Tm⌝ (subTm σ d)
  ⌜Tm⌝-sub σ d = cong (λ D → ⌜IMu⌝ (SI 2) D (pair (tag 1) (subTm σ d))) (SD-sub σ KSig)

  El-⌜Tm⌝ : {d : RTm Δ} → El (⌜Tm⌝ d) ⟶ᵀ K 1 d
  El-⌜Tm⌝ = El-⌜IMu⌝

  ⊢⌜Tm⌝ : {Ξ : Ctx} {d : RTm ⌊ Ξ ⌋} → Ξ ⊢ d ∷ El ⌜Nat⌝ → Ξ ⊢ ⌜Tm⌝ d ∷ U
  ⊢⌜Tm⌝ dd = ⊢⌜IMu⌝ ⊢SI ⊢KD (⊢ix (lt-s lt-z) dd)

⌜Tm⌝-ren : (ρ : Ren Δ Θ) (d : RTm Δ) → renTm ρ (⌜Tm⌝ d) ≡ ⌜Tm⌝ (renTm ρ d)
⌜Tm⌝-ren ρ d = trans (sym (subTm-var ρ (⌜Tm⌝ d))) (trans (⌜Tm⌝-sub ⟨ ρ ⟩ᵣ d)
                 (cong ⌜Tm⌝ {x = subTm ⟨ ρ ⟩ᵣ d} {y = renTm ρ d} (subTm-var ρ d)))


mc : RTm Δ → RTm Δ → RTm Δ → RTm Δ → RTm Δ
mc j g I D = cext (cext g (kEl I)) (kIMu (wk 1 j I) (wk 1 j D) (kvar ffz))

mc-sub : (σ : Sub Δ Θ) (j g I D : RTm Δ) → subTm σ (mc j g I D) ≡ mc (subTm σ j) (subTm σ g) (subTm σ I) (subTm σ D)
mc-sub σ j g I D =
  cong₂ (λ a b → cext (cext (subTm σ g) (kEl (subTm σ I))) (kIMu a b (kvar ffz)))
        {x = subTm σ (wk 1 j I)} {x' = wk 1 (subTm σ j) (subTm σ I)} {y = subTm σ (wk 1 j D)} {y' = wk 1 (subTm σ j) (subTm σ D)}
        (wk-sub σ 1 j I) (wk-sub σ 1 j D)


-- empty fibre (a head no rule concludes with)
rNone : Row
rNone = record { R = λ j p c → rows [] ; R-sub = λ σ j p c → refl }

-- a payload of the Knot, at its normal form
⊢payK : {Ξ : Ctx} {s : ℕ} {j p : RTm ⌊ Ξ ⌋} {sh : Shape} → Lt s 2 → ShOK 2 sh → Ξ ⊢ j ∷ El ⌜Nat⌝ →
        Args Ξ 2 KD j sh p → Ξ ⊢ p ∷ PayV sh (pair (tag s) j) (SI 2) (SD KSig)
⊢payK {s = s} {j = j} {sh = sh} lt ok dj as =
  ⊢conv (⊢payArgs ⊢KD ok (⊢ix lt dj) (step (βsnd (tag s) j) done) as) (red→≅ᵀ (payV-red sh (pair (tag s) j) (SI 2) (SD KSig)))
