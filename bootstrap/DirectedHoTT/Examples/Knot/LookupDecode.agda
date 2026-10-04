-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- OCP-0009 · KNOT — ★ CONTEXT LOOKUP IS EXACT (PLAN-FAITHFUL F6, `∋`):
-- the converse of `LookupAgree.enLk`.
--
--     decLk : ◇ ⊢ k ∷ K∋ (ix∋ (dep ⌊ Γ ⌋) ⌜ Γ ⌝ ⌜ x ⌝ ⌜ A ⌝) → IsNormal k → Γ ∋ x ∷ A
--
-- By recursion on the variable.  `here`: the identity proof gives
-- ⌜A⌝ ≅ wk ⌜A'⌝, which IS ⌜renTy vs A'⌝ (F3 `wk-agree-ty`), and quotes are
-- normal and injective.  `there`: the type field unquotes, the premise
-- decodes by recursion, the identity proof as for `here`.  Read along
-- `LookupCon.⊢here∋`/`⊢there∋`; no `with` (with-over-knot-contexts-ooms).
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Knot.LookupDecode where

open import normalizer.Syntax.Types using ( _≡_; refl; sym; trans; cong; cong₂; subst; Σ; _,_ )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax hiding ( Fin )
open import DirectedHoTT.Spec.Typing hiding ( _×_; _,,_ )
open import DirectedHoTT.Metatheory.RedCong using ( red→≅ᵀ; ⟶ᵀ*-El; ⟶*-dpayᶜ )
open import DirectedHoTT.Metatheory.TySub using ( ⊢-cast; wk-cancel-tm )
open import DirectedHoTT.Metatheory.LogicalRelation using ( IsNormal )
open import DirectedHoTT.Lib.Sugar using ( Cons; []; _∷_; nth-z; v₀; _,ₚ_ )
open import DirectedHoTT.Lib.Tel
open import DirectedHoTT.Lib.FinFam using ( ffz; ffs )
open import DirectedHoTT.Lib.Decode
open import DirectedHoTT.Examples.Knot.Sig
open import DirectedHoTT.Examples.Knot.Terms
open import DirectedHoTT.Examples.Knot.Ctx
open import DirectedHoTT.Examples.Knot.Ren using ( wk; wk-sub )
open import DirectedHoTT.Examples.Knot.Lookup
open import DirectedHoTT.Examples.Knot.LookupCon using ( fib-here; fib-there )
open import DirectedHoTT.Examples.Knot.OpAgree using ( wk-agree-ty )
open import DirectedHoTT.Examples.Knot.Unquote using ( unqTy; quoteTy-inj; quoteTy-normal )

private
  -- ⌜A⌝ ≅ wk ⌜B⌝ makes `A` the Spec weakening of `B`
  wkEq : {Γ : Cx} (A : RTy (Γ ∙)) (B : RTy Γ) → quoteTy A ≅ wk 0 (dep Γ) (quoteTy B) → A ≡ renTy vs B
  wkEq A B c = quoteTy-inj A (renTy vs B) (nf-≅ (quoteTy-normal A) (quoteTy-normal (renTy vs B)) (ctrn c (⟶*→≅ (wk-agree-ty B))))

  -- the `there` row's telescope after its type field, instantiated (`⊢there∋`'s instT)
  Tρ : RTm ε → RTm ε → RTm ε → RTm ε → Tel (ε ∙)
  Tρ m g y a = tρ (ix∋ (renTm vs m) (renTm vs g) (renTm vs y) v₀)
                  (tσ (⌜Id⌝ (⌜Ty⌝ (nsuc (renTm vs m))) (renTm vs a) (wk 0 (renTm vs m) v₀)) tι)
  Tρ' : RTm ε → RTm ε → RTm ε → RTm ε → RTm ε → Tel ε
  Tρ' m g y a b = tρ (ix∋ m g y b) (tσ (⌜Id⌝ (⌜Ty⌝ (nsuc m)) a (wk 0 m b)) tι)

  instT : (m g y a b : RTm ε) → subTm (single b) ⌜ Tρ m g y a ⌝ᵗ ≡ ⌜ Tρ' m g y a b ⌝ᵗ
  instT m g y a b =
    cong₂ (λ J X → dρ J (dσ X (lam dι)))
      (cong₃ (λ u w z → ix∋ u w z b) (wkc m) (wkc g) (wkc y))
      (cong₃ ⌜Id⌝ (trans (⌜Ty⌝-sub (single b) (nsuc (renTm vs m)))
                         (cong (λ z → ⌜Ty⌝ (nsuc z)) {x = subTm (single b) (renTm vs m)} {y = m} (wkc m)))
                  (wkc a)
                  (trans (wk-sub (single b) 0 (renTm vs m) v₀)
                         (cong (λ z → wk 0 z b) {x = subTm (single b) (renTm vs m)} {y = m} (wkc m))))
    where wkc : (t : RTm ε) → subTm (single b) (renTm vs t) ≡ t
          wkc t = wk-cancel-tm b t

decLk : {Γ : Ctx} (x : Var ⌊ Γ ⌋) {A : RTy ⌊ Γ ⌋} {k : RTm ε} →
        ◇ ⊢ k ∷ K∋ (ix∋ (dep ⌊ Γ ⌋) (quoteCtx Γ) (quoteVar x) (quoteTy A)) → IsNormal k → Γ ∋ x ∷ A

private
  -- here
  dHere₁ : {Γ : Ctx} (A' : RTy ⌊ Γ ⌋) (A : RTy (⌊ Γ ⌋ ∙)) {k : RTm ε} →
           RowsDec I∋ D∋ (⌜ hereT (dep ⌊ Γ ⌋) (quoteTy A') (quoteTy A) ⌝ᵗ ∷ []) k → (Γ ▹ A') ∋ vz ∷ A
  dHere₂ : {Γ : Ctx} (A' : RTy ⌊ Γ ⌋) (A : RTy (⌊ Γ ⌋ ∙)) {q : RTm ε} →
           PayΣ I∋ D∋ (⌜Id⌝ (⌜Ty⌝ (nsuc (dep ⌊ Γ ⌋))) (quoteTy A) (wk 0 (dep ⌊ Γ ⌋) (quoteTy A'))) (lam dι) q →
           (Γ ▹ A') ∋ vz ∷ A
  dHere₁ {Γ} A' A (_ , (_ , (q , (nth-z , (_ , (dq , nq)))))) =
    dHere₂ {Γ} A' A (pay-σ {I = I∋} {D = D∋} {C = ⌜ hereT (dep ⌊ Γ ⌋) (quoteTy A') (quoteTy A) ⌝ᵗ}
                           {S = ⌜Id⌝ (⌜Ty⌝ (nsuc (dep ⌊ Γ ⌋))) (quoteTy A) (wk 0 (dep ⌊ Γ ⌋) (quoteTy A'))} {f = lam dι} dq done nq)
  dHere₂ {Γ} A' A (e , (_ , (_ , ((de , _) , (ne , _))))) =
    subst (λ T → (Γ ▹ A') ∋ vz ∷ T) (sym (wkEq A A' (idrefl-decᶜ de ne))) here

  -- there
  dThere₁ : {Γ : Ctx} (A' : RTy ⌊ Γ ⌋) (y : Var ⌊ Γ ⌋) (A : RTy (⌊ Γ ⌋ ∙)) {k : RTm ε} →
            RowsDec I∋ D∋ (⌜ thereT (dep ⌊ Γ ⌋) (quoteCtx Γ) (fst (quoteVar y ,ₚ unit)) (quoteTy A) ⌝ᵗ ∷ []) k →
            (Γ ▹ A') ∋ vs y ∷ A
  dThere₁ᵇ : {Γ : Ctx} (A' : RTy ⌊ Γ ⌋) (y : Var ⌊ Γ ⌋) (A : RTy (⌊ Γ ⌋ ∙)) {q : RTm ε} →
             PayΣ I∋ D∋ (⌜Ty⌝ (dep ⌊ Γ ⌋)) (lam ⌜ Tρ (dep ⌊ Γ ⌋) (quoteCtx Γ) (fst (quoteVar y ,ₚ unit)) (quoteTy A) ⌝ᵗ) q →
             (Γ ▹ A') ∋ vs y ∷ A
  dThere₂ : {Γ : Ctx} (A' : RTy ⌊ Γ ⌋) (y : Var ⌊ Γ ⌋) (A : RTy (⌊ Γ ⌋ ∙)) (b rest : RTm ε) →
            Σ (RTy ⌊ Γ ⌋) (λ B → b ≡ quoteTy B) →
            ◇ ⊢ rest ∷ El (dpay I∋ D∋ (app (lam ⌜ Tρ (dep ⌊ Γ ⌋) (quoteCtx Γ) (fst (quoteVar y ,ₚ unit)) (quoteTy A) ⌝ᵗ) b)) →
            IsNormal rest → (Γ ▹ A') ∋ vs y ∷ A
  dThere₃ : {Γ : Ctx} (A' : RTy ⌊ Γ ⌋) (y : Var ⌊ Γ ⌋) (A : RTy (⌊ Γ ⌋ ∙)) (B : RTy ⌊ Γ ⌋) {rest : RTm ε} →
            PayΡ I∋ D∋ (ix∋ (dep ⌊ Γ ⌋) (quoteCtx Γ) (fst (quoteVar y ,ₚ unit)) (quoteTy B))
                 ⌜ tσ (⌜Id⌝ (⌜Ty⌝ (nsuc (dep ⌊ Γ ⌋))) (quoteTy A) (wk 0 (dep ⌊ Γ ⌋) (quoteTy B))) tι ⌝ᵗ rest →
            (Γ ▹ A') ∋ vs y ∷ A
  dThere₄ : {Γ : Ctx} (A' : RTy ⌊ Γ ⌋) (y : Var ⌊ Γ ⌋) (A : RTy (⌊ Γ ⌋ ∙)) (B : RTy ⌊ Γ ⌋) {rest : RTm ε} → Γ ∋ y ∷ B →
            PayΣ I∋ D∋ (⌜Id⌝ (⌜Ty⌝ (nsuc (dep ⌊ Γ ⌋))) (quoteTy A) (wk 0 (dep ⌊ Γ ⌋) (quoteTy B))) (lam dι) rest →
            (Γ ▹ A') ∋ vs y ∷ A

  dThere₁ {Γ} A' y A (_ , (_ , (q , (nth-z , (_ , (dq , nq)))))) =
    dThere₁ᵇ {Γ} A' y A
      (pay-σ {I = I∋} {D = D∋} {C = ⌜ thereT (dep ⌊ Γ ⌋) (quoteCtx Γ) (fst (quoteVar y ,ₚ unit)) (quoteTy A) ⌝ᵗ}
             {S = ⌜Ty⌝ (dep ⌊ Γ ⌋)} {f = lam ⌜ Tρ (dep ⌊ Γ ⌋) (quoteCtx Γ) (fst (quoteVar y ,ₚ unit)) (quoteTy A) ⌝ᵗ} dq done nq)
  dThere₁ᵇ {Γ} A' y A (b , (rest , (_ , ((db , drest) , (nb , nrest))))) =
    dThere₂ {Γ} A' y A b rest (unqTy {Γ = ⌊ Γ ⌋} (⊢conv db (credᵀ El-⌜Ty⌝)) nb) drest nrest
  dThere₂ {Γ} A' y A _ rest (B , refl) drest nrest =
    dThere₃ {Γ} A' y A B
      (pay-ρ {I = I∋} {D = D∋} {C = ⌜ Tρ' m g y' (quoteTy A) (quoteTy B) ⌝ᵗ} {j = ix∋ m g y' (quoteTy B)}
             {C' = ⌜ tσ (⌜Id⌝ (⌜Ty⌝ (nsuc m)) (quoteTy A) (wk 0 m (quoteTy B))) tι ⌝ᵗ}
             (⊢-cast (cong (λ C → El (dpay I∋ D∋ C)) (instT m g y' (quoteTy A) (quoteTy B)))
                     (⊢conv drest (red→≅ᵀ (⟶ᵀ*-El (⟶*-dpayᶜ (step (β _ (quoteTy B)) done))))))
             done nrest)
    where m = dep ⌊ Γ ⌋
          g = quoteCtx Γ
          y' = fst (quoteVar y ,ₚ unit)
  dThere₃ {Γ} A' y A B (r , (rest₂ , (_ , ((dr , drest₂) , (nr , nrest₂))))) =
    dThere₄ {Γ} A' y A B
      (decLk {Γ} y {B} (⊢conv dr (credᵀ (ξ-IMuⁱ (ξ-pairʳ (ξ-pairʳ (ξ-pairˡ (βfst (quoteVar y) unit))))))) nr)
      (pay-σ {I = I∋} {D = D∋} {C = ⌜ tσ (⌜Id⌝ (⌜Ty⌝ (nsuc (dep ⌊ Γ ⌋))) (quoteTy A) (wk 0 (dep ⌊ Γ ⌋) (quoteTy B))) tι ⌝ᵗ}
             {S = ⌜Id⌝ (⌜Ty⌝ (nsuc (dep ⌊ Γ ⌋))) (quoteTy A) (wk 0 (dep ⌊ Γ ⌋) (quoteTy B))} {f = lam dι} drest₂ done nrest₂)
  dThere₄ {Γ} A' y A B d (e , (_ , (_ , ((de , _) , (ne , _))))) =
    subst (λ T → (Γ ▹ A') ∋ vs y ∷ T) (sym (wkEq A B (idrefl-decᶜ de ne))) (there d)

decLk {Γ ▹ A'} vz {A} dk nrm =
  dHere₁ {Γ} A' A
    (rows-dec {I = I∋} {D = D∋} {i = ix∋ (nsuc (dep ⌊ Γ ⌋)) (cext (quoteCtx Γ) (quoteTy A')) ffz (quoteTy A)} {m = 1}
              {Cs = ⌜ hereT (dep ⌊ Γ ⌋) (quoteTy A') (quoteTy A) ⌝ᵗ ∷ []}
              (fib-here (dep ⌊ Γ ⌋) (quoteCtx Γ) (quoteTy A') (quoteTy A)) dk nrm)
decLk {Γ ▹ A'} (vs y) {A} dk nrm =
  dThere₁ {Γ} A' y A
    (rows-dec {I = I∋} {D = D∋} {i = ix∋ (nsuc (dep ⌊ Γ ⌋)) (cext (quoteCtx Γ) (quoteTy A')) (ffs (quoteVar y)) (quoteTy A)} {m = 1}
              {Cs = ⌜ thereT (dep ⌊ Γ ⌋) (quoteCtx Γ) (fst (quoteVar y ,ₚ unit)) (quoteTy A) ⌝ᵗ ∷ []}
              (fib-there (dep ⌊ Γ ⌋) (quoteCtx Γ) (quoteTy A') (quoteVar y) (quoteTy A)) dk nrm)
