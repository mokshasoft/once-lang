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
open import DirectedHoTT.Lib.Sugar using ( Cons; []; _∷_; conₗ; tag; lt-z; lt-s )
open import DirectedHoTT.Lib.Tel
open import DirectedHoTT.Lib.Sorted using ( ⊢sortOf )
open import DirectedHoTT.Lib.Syn
open import DirectedHoTT.Lib.SynFib using ( Row )
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
