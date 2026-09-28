------------------------------------------------------------------------
-- OCP-0009 · KNOT — ★★ `Γ ⊢ty A` / `Γ ⊢ t ∷ A`: THE TYPING JUDGEMENT,
-- ONE FAMILY OVER BOTH SORTS, FIBRED BY ITS SUBJECT (D077, `Lib/SynFib`).
--
-- The index is `(i , t , c)`: a Knot index `i = (sort , depth)`, the
-- subject `t : K sort depth`, and the CONVOY `c`:
--
--     sort Ty:   c = (Γ , tt)       Γ ⊢ty t
--     sort Tm:   c = (Γ , A)        Γ ⊢ t ∷ A
--
-- The fibre over `(i , t , c)` is a case on `t`'s head: exactly the rules
-- whose conclusion has that head.  Nothing about the subject Fords; a
-- computed OUTPUT (a conclusion type such as `B[u]`) Fords explicitly.
--
-- ⬜ This module is built in stages: the `⊢ty` rows first.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Knot.Judge where

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
tyK≅ j = ctrnᵀ (credᵀ El-⌜IMu⌝) (credᵀ (ξ-IMuⁱ (ξ-pairʳ (βsnd (tag 1) j))))

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

-- the telescopes (index `j`, payload `p`, convoy `c`; the context is `fst c`)
T0 TPi TEl THom TIMu TDesc : RTm Δ → RTm Δ → RTm Δ → Tel Δ
T0 j p c = tι
TPi j p c = tρ (tyIx j (fst c) (fst p)) (tρ (tyIx (nsuc j) (cext (fst c) (fst p)) (fst (snd p))) tι)
TEl j p c = tρ (tmIx j (fst c) (fst p) kU) tι
THom j p c = tρ (tyIx j (fst c) (fst p))
               (tρ (tmIx j (fst c) (fst (snd p)) (fst p)) (tρ (tmIx j (fst c) (fst (snd (snd p))) (fst p)) tι))
TIMu j p c = tρ (tmIx j (fst c) (fst p) kU)
               (tρ (tmIx j (fst c) (fst (snd p)) (DF j (fst p))) (tρ (tmIx j (fst c) (fst (snd (snd p))) (kEl (fst p))) tι))
TDesc j p c = tρ (tmIx j (fst c) (fst p) kU) tι

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

rIMu : Row
rIMu = record
  { R = λ j p c → row1 (TIMu j p c)
  ; R-sub = λ σ j p c →
      trans (rows-sub' σ (⌜ TIMu j p c ⌝ᵗ ∷ []))
            (cong (λ X → rows (dρ (tmIx (subTm σ j) (fst (subTm σ c)) (fst (subTm σ p)) kU)
                                  (dρ (tmIx (subTm σ j) (fst (subTm σ c)) (fst (snd (subTm σ p))) X)
                                      (dρ (tmIx (subTm σ j) (fst (subTm σ c)) (fst (snd (snd (subTm σ p)))) (kEl (fst (subTm σ p)))) dι))
                               ∷ []))
                  {x = subTm σ (DF j (fst p))} {y = DF (subTm σ j) (fst (subTm σ p))}
                  (DF-sub σ j (fst p)))
  }

-- empty fibre (a head no rule concludes with)
rNone : Row
rNone = record { R = λ j p c → rows [] ; R-sub = λ σ j p c → refl }

-- ★ the rows, by (sort, constructor); the `⊢` rows are the next stage
rowT : ℕ → ℕ → Row
rowT 0 0  = defRow T0 (λ σ j p c → refl)      -- base
rowT 0 1  = defRow T0 (λ σ j p c → refl)      -- U
rowT 0 2  = defRow TPi (λ σ j p c → refl)     -- Π
rowT 0 3  = defRow TPi (λ σ j p c → refl)     -- Σ
rowT 0 4  = defRow TEl (λ σ j p c → refl)     -- El
rowT 0 5  = defRow THom (λ σ j p c → refl)    -- Hom
rowT 0 6  = defRow T0 (λ σ j p c → refl)      -- Unit
rowT 0 7  = defRow T0 (λ σ j p c → refl)      -- Nat
rowT 0 8  = defRow THom (λ σ j p c → refl)    -- Id
rowT 0 9  = rIMu           -- IMu
rowT 0 10 = defRow TDesc (λ σ j p c → refl)   -- Desc
rowT 0 11 = rNone          -- DIh  ⬜ (its index code is a σ-field; next)
rowT 0 12 = defRow T0 (λ σ j p c → refl)      -- Fin
rowT _ _  = rNone

------------------------------------------------------------------------
-- 5. ★ THE FAMILY: the fibre method at the Knot's signature, typed from
--   every row's typing.
------------------------------------------------------------------------

open Fib KOK JT JT-sub ⊢JT CT CT-sub ⊢CT rowT public

private
  module RowTyping {Ξ : Ctx} {j c : RTm ⌊ Ξ ⌋} (dj : Ξ ⊢ j ∷ El ⌜Nat⌝) (dc : Ξ ⊢ c ∷ El (CTat (pair (tag 0) j))) where
    dg : Ξ ⊢ fst c ∷ KCtx j
    dg = ⊢ctxOf dc
    done1 : (T : Tel ⌊ Ξ ⌋) → TelOK Ξ JT T → Ξ ⊢ rows (⌜ T ⌝ᵗ ∷ []) ∷ Desc JT
    done1 T ok = ⊢rows ⊢JT (⊢tel {Ξ} {JT} {T} ⊢JT ok ∷ᵈ []ᵈ)

  -- a payload's fields at sort 0, the shape EXPLICIT (`PayV` computes on it)
  f0 : {Ξ : Ctx} {j p : RTm ⌊ Ξ ⌋} (s k : ℕ) (sh : Shape) →
       Ξ ⊢ p ∷ PayV (rec s k ∷ʰ sh) (pair (tag 0) j) (SI 2) (SD KSig) → Ξ ⊢ fst p ∷ K s (nsucs k j)
  f0 {j = j} s k sh dp = ⊢atDepth {a = tag 0} {j = j} {s = s} {k = k} (⊢recFst {s = s} {k = k} {sh = sh} dp)

  r1 : {Ξ : Ctx} {j p : RTm ⌊ Ξ ⌋} (s k : ℕ) (sh : Shape) →
       Ξ ⊢ p ∷ PayV (rec s k ∷ʰ sh) (pair (tag 0) j) (SI 2) (SD KSig) → Ξ ⊢ snd p ∷ PayV sh (pair (tag 0) j) (SI 2) (SD KSig)
  r1 s k sh dp = ⊢recSnd {s = s} {k = k} {sh = sh} dp

  ok0 : {sh : Shape} → RowOK 0 sh (defRow T0 (λ σ j p c → refl))
  ok0 {j = j} {p} {c} dj dp dc = RowTyping.done1 dj dc (T0 j p c) ok-ι

  okPi : RowOK 0 sh-kPi (defRow TPi (λ σ j p c → refl))
  okPi {j = j} {p} {c} dj dp dc =
    done1 (TPi j p c) (ok-ρ (⊢tyIx dj dg dA) (ok-ρ (⊢tyIx (⊢isuc dj) (⊢cext dj dg dA) dB) ok-ι))
    where open RowTyping dj dc
          dA = f0 0 0 (rec 0 1 ∷ʰ []ʰ) dp
          dB = f0 0 1 []ʰ (r1 0 0 (rec 0 1 ∷ʰ []ʰ) dp)

  okEl : RowOK 0 sh-kEl (defRow TEl (λ σ j p c → refl))
  okEl {j = j} {p} {c} dj dp dc = done1 (TEl j p c) (ok-ρ (⊢tmIx dj dg (f0 1 0 []ʰ dp) (⊢kU dj)) ok-ι)
    where open RowTyping dj dc

  okHom : RowOK 0 sh-kHom (defRow THom (λ σ j p c → refl))
  okHom {j = j} {p} {c} dj dp dc =
    done1 (THom j p c) (ok-ρ (⊢tyIx dj dg dA) (ok-ρ (⊢tmIx dj dg dt dA) (ok-ρ (⊢tmIx dj dg du dA) ok-ι)))
    where open RowTyping dj dc
          p1 = r1 0 0 (rec 1 0 ∷ʰ rec 1 0 ∷ʰ []ʰ) dp
          dA = f0 0 0 (rec 1 0 ∷ʰ rec 1 0 ∷ʰ []ʰ) dp
          dt = f0 1 0 (rec 1 0 ∷ʰ []ʰ) p1
          du = f0 1 0 []ʰ (r1 1 0 (rec 1 0 ∷ʰ []ʰ) p1)

  okIMu : RowOK 0 sh-kIMu rIMu
  okIMu {j = j} {p} {c} dj dp dc =
    done1 (TIMu j p c) (ok-ρ (⊢tmIx dj dg dI (⊢kU dj)) (ok-ρ (⊢tmIx dj dg dD (⊢DF dj dI)) (ok-ρ (⊢tmIx dj dg di (⊢kEl dj dI)) ok-ι)))
    where open RowTyping dj dc
          p1 = r1 1 0 (rec 1 0 ∷ʰ rec 1 0 ∷ʰ []ʰ) dp
          dI = f0 1 0 (rec 1 0 ∷ʰ rec 1 0 ∷ʰ []ʰ) dp
          dD = f0 1 0 (rec 1 0 ∷ʰ []ʰ) p1
          di = f0 1 0 []ʰ (r1 1 0 (rec 1 0 ∷ʰ []ʰ) p1)

  okDesc : RowOK 0 sh-kDesc (defRow TDesc (λ σ j p c → refl))
  okDesc {j = j} {p} {c} dj dp dc = done1 (TDesc j p c) (ok-ρ (⊢tmIx dj dg (f0 1 0 []ʰ dp) (⊢kU dj)) ok-ι)
    where open RowTyping dj dc

  okNone : {s : ℕ} {sh : Shape} → RowOK s sh rNone
  okNone dj dp dc = ⊢rows {I = JT} {Cs = []} ⊢JT []ᵈ

-- the Π/Σ row's telescope, typed (what a constructor needs)
okPiT : {Ξ : Ctx} {j p c : RTm ⌊ Ξ ⌋} → Ξ ⊢ j ∷ El ⌜Nat⌝ →
        Ξ ⊢ p ∷ PayV sh-kPi (pair (tag 0) j) (SI 2) (SD KSig) → Ξ ⊢ c ∷ El (CTat (pair (tag 0) j)) → TelOK Ξ JT (TPi j p c)
okPiT dj dp dc = ok-ρ (⊢tyIx dj dg dA) (ok-ρ (⊢tyIx (⊢isuc dj) (⊢cext dj dg dA) dB) ok-ι)
  where dg = ⊢ctxOf dc
        dA = f0 0 0 (rec 0 1 ∷ʰ []ʰ) dp
        dB = f0 0 1 []ʰ (r1 0 0 (rec 0 1 ∷ʰ []ʰ) dp)

-- ★ every row typed, by its position in the signature
rowOK : {s c k : ℕ} {shs : Shapes c} {sh : Shape} → NthG KSig s shs → NthSh shs k sh → RowOK s sh (rowT s k)
rowOK nthᵍ-z nthʰ-z = ok0 {sh-kbase}
rowOK nthᵍ-z (nthʰ-s nthʰ-z) = ok0 {sh-kU}
rowOK nthᵍ-z (nthʰ-s (nthʰ-s nthʰ-z)) = okPi
rowOK nthᵍ-z (nthʰ-s (nthʰ-s (nthʰ-s nthʰ-z))) = okPi
rowOK nthᵍ-z (nthʰ-s (nthʰ-s (nthʰ-s (nthʰ-s nthʰ-z)))) = okEl
rowOK nthᵍ-z (nthʰ-s (nthʰ-s (nthʰ-s (nthʰ-s (nthʰ-s nthʰ-z))))) = okHom
rowOK nthᵍ-z (nthʰ-s (nthʰ-s (nthʰ-s (nthʰ-s (nthʰ-s (nthʰ-s nthʰ-z)))))) = ok0 {sh-kUnit}
rowOK nthᵍ-z (nthʰ-s (nthʰ-s (nthʰ-s (nthʰ-s (nthʰ-s (nthʰ-s (nthʰ-s nthʰ-z))))))) = ok0 {sh-kNat}
rowOK nthᵍ-z (nthʰ-s (nthʰ-s (nthʰ-s (nthʰ-s (nthʰ-s (nthʰ-s (nthʰ-s (nthʰ-s nthʰ-z)))))))) = okHom
rowOK nthᵍ-z (nthʰ-s (nthʰ-s (nthʰ-s (nthʰ-s (nthʰ-s (nthʰ-s (nthʰ-s (nthʰ-s (nthʰ-s nthʰ-z))))))))) = okIMu
rowOK nthᵍ-z (nthʰ-s (nthʰ-s (nthʰ-s (nthʰ-s (nthʰ-s (nthʰ-s (nthʰ-s (nthʰ-s (nthʰ-s (nthʰ-s nthʰ-z)))))))))) = okDesc
rowOK nthᵍ-z (nthʰ-s (nthʰ-s (nthʰ-s (nthʰ-s (nthʰ-s (nthʰ-s (nthʰ-s (nthʰ-s (nthʰ-s (nthʰ-s (nthʰ-s nthʰ-z))))))))))) = okNone {0} {sh-kDIh}
rowOK nthᵍ-z (nthʰ-s (nthʰ-s (nthʰ-s (nthʰ-s (nthʰ-s (nthʰ-s (nthʰ-s (nthʰ-s (nthʰ-s (nthʰ-s (nthʰ-s (nthʰ-s nthʰ-z)))))))))))) = ok0 {sh-kFin}
rowOK {sh = sh} (nthᵍ-s nthᵍ-z) nh = okNone {1} {sh}

⊢FIBMT : {Γ : Ctx} → Γ ⊢ FIBM ∷ MethTy (SI 2) (SD KSig) FM
⊢FIBMT = ⊢FIBM rowOK

------------------------------------------------------------------------
-- 6. ★ THE FIBRE FUNCTION and the family.
------------------------------------------------------------------------

D⊢ : RTm Δ
D⊢ = lam (app (ielim KD (fst (var vz)) FIBM (fst (snd (var vz)))) (snd (snd (var vz))))

K⊢ : RTm Δ → RTy Δ
K⊢ x = IMu JT D⊢ x

JT-ren : (ρ : Ren Δ Θ) → renTm ρ (JT {Δ}) ≡ JT
JT-ren ρ = trans (sym (subTm-var ρ JT)) (JT-sub ⟨ ρ ⟩ᵣ)

-- an index's three components (the inverse of `⊢ixJ`)
module UnJ {Ξ : Ctx} {x : RTm ⌊ Ξ ⌋} (dx : Ξ ⊢ x ∷ El JT) where
  i0 t0 c0 : RTm ⌊ Ξ ⌋
  i0 = fst x
  t0 = fst (snd x)
  c0 = snd (snd x)
  private
    B1 : RTm (⌊ Ξ ⌋ ∙)
    B1 = ⌜Σ⌝ (⌜IMu⌝ (SI 2) KD (var vz)) (renTm vs CT)
    B2 : RTm (⌊ Ξ ⌋ ∙)
    B2 = renTm vs (CTat i0)
    e1 : subTy (single i0) (El B1) ≡ El (⌜Σ⌝ (⌜IMu⌝ (SI 2) KD i0) B2)
    e1 = cong El (cong₂ ⌜Σ⌝ {x = subTm (single i0) (⌜IMu⌝ (SI 2) KD (var vz))} {x' = ⌜IMu⌝ (SI 2) KD i0}
                            {y = subTm (extS (single i0)) (renTm vs CT)} {y' = B2}
                    (cong (λ D → ⌜IMu⌝ (SI 2) D i0) (SD-sub (single i0) KSig))
                    (wkS (single i0) CT))
    dx' : Ξ ⊢ x ∷ Σ' (El (SI 2)) (El B1)
    dx' = ⊢conv dx (credᵀ (El-⌜Σ⌝ (SI 2) B1))
    d2 : Ξ ⊢ snd x ∷ Σ' (El (⌜IMu⌝ (SI 2) KD i0)) (El B2)
    d2 = ⊢conv (⊢-cast {Ξ} {snd x} {subTy (single i0) (El B1)} {El (⌜Σ⌝ (⌜IMu⌝ (SI 2) KD i0) B2)} e1 (⊢snd dx'))
               (credᵀ (El-⌜Σ⌝ (⌜IMu⌝ (SI 2) KD i0) B2))
  di0 : Ξ ⊢ i0 ∷ El (SI 2)
  di0 = ⊢fst dx'
  dt0 : Ξ ⊢ t0 ∷ IMu (SI 2) KD i0
  dt0 = ⊢conv (⊢fst d2) (credᵀ El-⌜IMu⌝)
  dc0 : Ξ ⊢ c0 ∷ El (CTat i0)
  dc0 = ⊢-cast {Ξ} {c0} {subTy (single t0) (El B2)} {El (CTat i0)} (cong El (wk-cancel-tm t0 (CTat i0))) (⊢snd d2)

module _ {Γ : Ctx} where
  private
    Ξ : Ctx
    Ξ = Γ ▹ El JT
    dv : Ξ ⊢ var vz ∷ El JT
    dv = ⊢-cast {Ξ} {var vz} {renTy vs (El JT)} {El JT} (cong El (JT-ren vs)) (⊢var here)
    open UnJ dv
    dI : Ξ ⊢ ielim KD i0 FIBM t0 ∷ iinst i0 t0 FM
    dI = ⊢ielim {Ξ} {SI 2} {KD} {FM} {FIBM} {i0} {t0} ⊢SI ⊢KD ⊢FM ⊢FIBMT di0 dt0
    eI : iinst i0 t0 FM ≡ Π (El (CTat i0)) (Desc JT)
    eI = trans {x = iinst i0 t0 FM} {y = subTy (single t0 ∘ₛ extS (single i0)) FM} {z = Π (El (CTat i0)) (Desc JT)}
               (subTy-subTy {τ = single t0} {σ = extS (single i0)} FM)
               (trans (FM-sub (single t0 ∘ₛ extS (single i0)))
                      (cong (λ z → Π (El (CTat z)) (Desc JT)) {x = subTm (single t0) (renTm vs i0)} {y = i0}
                            (wk-cancel-tm t0 i0)))
    bodyD : Ξ ⊢ app (ielim KD i0 FIBM t0) c0 ∷ Desc (renTm vs JT)
    bodyD = ⊢-cast {Ξ} {app (ielim KD i0 FIBM t0) c0} {subTy (single c0) (Desc JT)} {Desc (renTm vs JT)}
                   (trans (cong Desc (JT-sub (single c0))) (cong Desc (sym (JT-ren vs))))
                   (⊢app {Ξ} {El (CTat i0)} {Desc JT} {ielim KD i0 FIBM t0} {c0}
                         (⊢-cast {Ξ} {ielim KD i0 FIBM t0} {iinst i0 t0 FM} {Π (El (CTat i0)) (Desc JT)} eI dI) dc0)

  -- ★ THE TYPING JUDGEMENT IS A WELL-FORMED FAMILY
  ⊢D⊢ : Γ ⊢ D⊢ ∷ DescF JT
  ⊢D⊢ = ⊢lam (ty-El ⊢JT) bodyD

  ty-K⊢ : {x : RTm ⌊ Γ ⌋} → Γ ⊢ x ∷ El JT → Γ ⊢ty K⊢ x
  ty-K⊢ dx = ty-IMu ⊢JT ⊢D⊢ dx

------------------------------------------------------------------------
-- 7. ★ THE FIBRE COMPUTES, and the constructors.
------------------------------------------------------------------------

-- the fibre function at an index is the case on its subject
D⊢-β : (i t c : RTm Δ) → app D⊢ (ixJ i t c) ⟶* app (ielim KD i FIBM t) c
D⊢-β {Δ} i t c =
  step (β B x)
    (subst (λ z → z ⟶* app (ielim KD i FIBM t) c) (sym e)
      (⟶*-trans {t = app (ielim KD (fst x) FIBM (fst (snd x))) (snd (snd x))}
                {u = app (ielim KD i FIBM t) (snd (snd x))} {v = app (ielim KD i FIBM t) c}
        (⟶*-appˡ (⟶*-trans {t = ielim KD (fst x) FIBM (fst (snd x))} {u = ielim KD i FIBM (fst (snd x))}
                            {v = ielim KD i FIBM t}
                    (⟶*-ielimⁱ (step (βfst i (pair t c)) done))
                    (⟶*-ielimᵗ (⟶*-trans {t = fst (snd x)} {u = fst (pair t c)} {v = t}
                                  (⟶*-fst (step (βsnd i (pair t c)) done)) (step (βfst t c) done)))))
        (⟶*-appʳ (⟶*-trans {t = snd (snd x)} {u = snd (pair t c)} {v = c}
                   (⟶*-snd (step (βsnd i (pair t c)) done)) (step (βsnd t c) done)))))
  where
    x = ixJ i t c
    B : RTm (Δ ∙)
    B = app (ielim KD (fst (var vz)) FIBM (fst (snd (var vz)))) (snd (snd (var vz)))
    e : subTm (single x) B ≡ app (ielim KD (fst x) FIBM (fst (snd x))) (snd (snd x))
    e = cong₂ (λ D M → app (ielim D (fst x) M (fst (snd x))) (snd (snd x)))
              {x = subTm (single x) (KD {Δ ∙})} {x' = KD} {y = subTm (single x) (FIBM {Δ ∙})} {y' = FIBM}
              (SD-sub (single x) KSig) (FIBM-sub (single x))

-- ★ at a canonical subject, the fibre IS the row
fibK : {s c₀ k : ℕ} {shs : Shapes c₀} {sh : Shape} {j p c : RTm Δ} → NthG KSig s shs → NthSh shs k sh →
       app D⊢ (ixJ (pair (tag s) j) (conₗ k p) c) ⟶* Row.R (rowT s k) j p c
fibK {s = s} {k = k} {j = j} {p} {c} ng nh =
  ⟶*-trans (D⊢-β (pair (tag s) j) (conₗ k p) c) (fib-β {D = KD} {j = j} {p = p} {c₀ = c} ng nh)

-- a payload of the Knot, at its normal form
⊢payK : {Ξ : Ctx} {s : ℕ} {j p : RTm ⌊ Ξ ⌋} {sh : Shape} → Lt s 2 → ShOK 2 sh → Ξ ⊢ j ∷ El ⌜Nat⌝ →
        Args Ξ 2 KD j sh p → Ξ ⊢ p ∷ PayV sh (pair (tag s) j) (SI 2) (SD KSig)
⊢payK {s = s} {j = j} {sh = sh} lt ok dj as =
  ⊢conv (⊢payArgs ⊢KD ok (⊢ix lt dj) (step (βsnd (tag s) j) done) as) (red→≅ᵀ (payV-red sh (pair (tag s) j) (SI 2) (SD KSig)))

-- ★ `ty-base : Γ ⊢ty base`
⊢ty-base : {Ξ : Ctx} {j g : RTm ⌊ Ξ ⌋} → Ξ ⊢ j ∷ El ⌜Nat⌝ → Ξ ⊢ g ∷ KCtx j →
           Ξ ⊢ conₗ 0 unit ∷ K⊢ (tyIx j g kbase)
⊢ty-base {Ξ} {j} {g} dj dg =
  ⊢conRow {Ξ} {JT} {D⊢} {tyIx j g kbase} {dι} {unit} ⊢JT ⊢D⊢ (⊢tyIx dj dg (⊢kbase dj))
          (fibK {s = 0} {k = 0} {j = j} {p = unit} {c = pair g unit} nthᵍ-z nthʰ-z)
          (⊢dι ⊢JT) (⊢payι {Ξ} {JT} {D⊢} ⊢JT ⊢D⊢ {unit} ⊢unit)

-- ★ `ty-Π : Γ ⊢ty A → (Γ ▹ A) ⊢ty B → Γ ⊢ty Π A B`
⊢ty-Π : {Ξ : Ctx} {j g A B r₁ r₂ : RTm ⌊ Ξ ⌋} → Ξ ⊢ j ∷ El ⌜Nat⌝ → Ξ ⊢ g ∷ KCtx j →
        Ξ ⊢ A ∷ K 0 j → Ξ ⊢ B ∷ K 0 (nsuc j) →
        Ξ ⊢ r₁ ∷ K⊢ (tyIx j g A) → Ξ ⊢ r₂ ∷ K⊢ (tyIx (nsuc j) (cext g A) B) →
        Ξ ⊢ conₗ 0 (pair r₁ (pair r₂ unit)) ∷ K⊢ (tyIx j g (kPi A B))
⊢ty-Π {Ξ} {j} {g} {A} {B} {r₁} {r₂} dj dg dA dB dr₁ dr₂ =
  ⊢conRow {Ξ} {JT} {D⊢} {tyIx j g (kPi A B)} {⌜ TPi j p c ⌝ᵗ} {pair r₁ (pair r₂ unit)} ⊢JT ⊢D⊢
          (⊢tyIx dj dg (⊢kPi dj dA dB))
          (fibK {s = 0} {k = 2} {j = j} {p = p} {c = c} nthᵍ-z (nthʰ-s (nthʰ-s nthʰ-z)))
          (⊢tel {Ξ} {JT} {TPi j p c} ⊢JT ok)
          (⊢payρ {Ξ} {JT} {D⊢} ⊢JT ⊢D⊢ {J1} {r₁} {pair r₂ unit} {tρ J2 tι} ok
                 (⊢conv dr₁ (csymᵀ (red→≅ᵀ (⟶ᵀ*-IMu rix1))))
                 (⊢payρ {Ξ} {JT} {D⊢} ⊢JT ⊢D⊢ {J2} {r₂} {unit} {tι} (okRest ok)
                        (⊢conv dr₂ (csymᵀ (red→≅ᵀ (⟶ᵀ*-IMu rix2))))
                        (⊢payι {Ξ} {JT} {D⊢} ⊢JT ⊢D⊢ {unit} ⊢unit)))
  where
    p c : RTm ⌊ Ξ ⌋
    p = pair A (pair B unit)
    c = pair g unit
    J1 J2 : RTm ⌊ Ξ ⌋
    J1 = tyIx j (fst c) (fst p)
    J2 = tyIx (nsuc j) (cext (fst c) (fst p)) (fst (snd p))
    ok : TelOK Ξ JT (TPi j p c)
    ok = okPiT dj (⊢payK lt-z ok-kPi dj (a-rec dA (a-rec dB a[]))) (⊢cTy dj dg)
    okRest : {J : RTm ⌊ Ξ ⌋} {T : Tel ⌊ Ξ ⌋} → TelOK Ξ JT (tρ J T) → TelOK Ξ JT T
    okRest (ok-ρ _ o) = o
    -- the row's indices, their projections reduced
    rix1 : J1 ⟶* tyIx j g A
    rix1 = ⟶*-pairʳ (⟶*-trans {t = pair (fst p) (pair (fst c) unit)} {u = pair A (pair (fst c) unit)} {v = pair A (pair g unit)}
                     (⟶*-pairˡ (step (βfst A (pair B unit)) done)) (⟶*-pairʳ (⟶*-pairˡ (step (βfst g unit) done))))
    rix2 : J2 ⟶* tyIx (nsuc j) (cext g A) B
    rix2 = ⟶*-pairʳ (⟶*-trans {t = pair (fst (snd p)) (pair (cext (fst c) (fst p)) unit)}
                              {u = pair B (pair (cext (fst c) (fst p)) unit)} {v = pair B (pair (cext g A) unit)}
                     (⟶*-pairˡ (⟶*-trans {t = fst (snd p)} {u = fst (pair B unit)} {v = B}
                                  (⟶*-fst (step (βsnd A (pair B unit)) done)) (step (βfst B unit) done)))
                     (⟶*-pairʳ (⟶*-pairˡ (⟶*-con (⟶*-pairʳ (⟶*-trans {t = pair (fst c) (pair (fst p) unit)}
                                  {u = pair g (pair (fst p) unit)} {v = pair g (pair A unit)}
                                  (⟶*-pairˡ (step (βfst g unit) done))
                                  (⟶*-pairʳ (⟶*-pairˡ (step (βfst A (pair B unit)) done)))))))))
