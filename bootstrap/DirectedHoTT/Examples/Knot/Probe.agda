-- SUBSET PROBE for the smart-constructor emitter (6 representative rows)
{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Knot.Probe where
open import normalizer.Syntax.Types using ( _≡_; refl; sym; trans; cong; subst )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax
  using ( Cx; ε; _∙; vz; vs
        ; RTy; RTm; El; Unit; Nat; Σ'; IMu
        ; var; pair; fst; snd; unit; nzero; nsuc; ⌜Nat⌝; ⌜Id⌝; idrefl; icon
        ; Ren; Sub; renTm; subTm; extS )
open import DirectedHoTT.Spec.Typing
  using ( Ctx; ◇; _▹_; ⌊_⌋; single
        ; _⊢_∷_; _⊢ty_; ⊢var; here; there; ⊢conv
        ; ⊢pair; ⊢fst; ⊢snd; ⊢unit; ⊢nzero; ⊢nsuc; ⊢⌜Nat⌝; ⊢⌜Id⌝; ⊢idrefl; ⊢icon
        ; ty-El; ty-Unit; ty-Nat; ty-Σ; ty-IMu
        ; _⟶_; βfst; βsnd; ξ-pairʳ; ξ-nsuc
        ; _≅ᵀ_; csymᵀ; ctrnᵀ; credᵀ; El-⌜Id⌝; ξ-El; ξ-IMu; ξ-⌜Id⌝ˡ )
open import DirectedHoTT.Examples.Knot.Sorts
  using ( IPair; sTy; sTm; sDesc; sDCon; sIDesc; sICon; sVar
        ; ⊢sTy; ⊢sTm; ⊢sDesc; ⊢sDCon; ⊢sIDesc; ⊢sICon; ⊢sVar
        ; toI; fromI; ⊢ixP; num; ⊢num; num-ren; num-sub )
open import DirectedHoTT.Examples.Knot.Desc using ( KnotD; K )
open import DirectedHoTT.Examples.Knot.Wf using ( KnotWf )
open import DirectedHoTT.Examples.Knot.Tags
open import DirectedHoTT.Examples.Knot.Terms using ( ixConv; fordFst; tyFordFst )
open import DirectedHoTT.Examples.Knot.Build using ( tyCast; ⊢numAt; kCast )






-- Nat : RTy Γ
Ty-NatK : {Γ : Cx} → RTm Γ
Ty-NatK  = icon tagTy-Nat (pair (idrefl ⌜Nat⌝ sTy) unit)

⊢Ty-NatK : {Δ : Ctx} (n : ℕ) →
        Δ ⊢ Ty-NatK  ∷ K (pair sTy (num n))
⊢Ty-NatK n  =
  ⊢icon KnotWf memTy-Nat (⊢ixP ⊢sTy (⊢num n))
    (⊢pair (ty-Unit)
           (fordFst ⊢sTy)
     ⊢unit)

-- IMu : IDesc → RTy ε → RTm Γ → RTy Γ
Ty-IMuK : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ → RTm Γ
Ty-IMuK a0 a1 a2 = icon tagTy-IMu (pair a0 (pair a1 (pair a2 (pair (idrefl ⌜Nat⌝ sTy) unit))))

⊢Ty-IMuK : {Δ : Ctx} (n : ℕ) {a0 a1 a2 : RTm ⌊ Δ ⌋} →
        Δ ⊢ a0 ∷ K (pair sIDesc (num n)) →
        Δ ⊢ a1 ∷ K (pair sTy (num 0)) →
        Δ ⊢ a2 ∷ K (pair sTm (num n)) →
        Δ ⊢ Ty-IMuK a0 a1 a2 ∷ K (pair sTy (num n))
⊢Ty-IMuK n {a0 = a0} {a1 = a1} {a2 = a2} d0 d1 d2 =
  ⊢icon KnotWf memTy-IMu (⊢ixP ⊢sTy (⊢num n))
    (⊢pair (ty-Σ (ty-IMu KnotWf (⊢ixP ⊢sTy (⊢num 0))) (ty-Σ (ty-IMu KnotWf (⊢ixP ⊢sTm (⊢snd (⊢ixP ⊢sTy (⊢numAt n e1))))) (ty-Σ (ty-El (⊢⌜Id⌝ ⊢⌜Nat⌝ (toI (⊢fst (⊢ixP ⊢sTy (⊢numAt n e0)))) (toI ⊢sTy))) (ty-Unit))))
           (ixConv (ξ-pairʳ (βsnd sTy (num n))) (d0))
     (⊢pair (ty-Σ (ty-IMu KnotWf (⊢ixP ⊢sTm (⊢snd (⊢ixP ⊢sTy (⊢numAt n e3))))) (ty-Σ (ty-El (⊢⌜Id⌝ ⊢⌜Nat⌝ (toI (⊢fst (⊢ixP ⊢sTy (⊢numAt n e2)))) (toI ⊢sTy))) (ty-Unit)))
            (d1)
      (⊢pair (ty-Σ (ty-El (⊢⌜Id⌝ ⊢⌜Nat⌝ (toI (⊢fst (⊢ixP ⊢sTy (⊢numAt n e4)))) (toI ⊢sTy))) (ty-Unit))
             (ixConv (ξ-pairʳ (βsnd sTy (subTm (single a1) (subTm (extS (single a0)) (renTm vs (renTm vs (num n))))))) (kCast (sym e5) d2))
       (⊢pair (ty-Unit)
              (fordFst ⊢sTy)
        ⊢unit))))
  where
    e0 : renTm vs (renTm vs (renTm vs (num n))) ≡ num n
    e0 = trans (cong (renTm vs) (trans (cong (renTm vs) (trans (cong (renTm vs) (refl)) (num-ren vs n))) (num-ren vs n))) (num-ren vs n)
    e1 : renTm vs (renTm vs (num n)) ≡ num n
    e1 = trans (cong (renTm vs) (trans (cong (renTm vs) (refl)) (num-ren vs n))) (num-ren vs n)
    e2 : subTm (extS (extS (single a0))) (renTm vs (renTm vs (renTm vs (num n)))) ≡ num n
    e2 = trans (cong (subTm (extS (extS (single a0)))) (trans (cong (renTm vs) (trans (cong (renTm vs) (trans (cong (renTm vs) (refl)) (num-ren vs n))) (num-ren vs n))) (num-ren vs n))) (num-sub (extS (extS (single a0))) n)
    e3 : subTm (extS (single a0)) (renTm vs (renTm vs (num n))) ≡ num n
    e3 = trans (cong (subTm (extS (single a0))) (trans (cong (renTm vs) (trans (cong (renTm vs) (refl)) (num-ren vs n))) (num-ren vs n))) (num-sub (extS (single a0)) n)
    e4 : subTm (extS (single a1)) (subTm (extS (extS (single a0))) (renTm vs (renTm vs (renTm vs (num n))))) ≡ num n
    e4 = trans (cong (subTm (extS (single a1))) (trans (cong (subTm (extS (extS (single a0)))) (trans (cong (renTm vs) (trans (cong (renTm vs) (trans (cong (renTm vs) (refl)) (num-ren vs n))) (num-ren vs n))) (num-ren vs n))) (num-sub (extS (extS (single a0))) n))) (num-sub (extS (single a1)) n)
    e5 : subTm (single a1) (subTm (extS (single a0)) (renTm vs (renTm vs (num n)))) ≡ num n
    e5 = trans (cong (subTm (single a1)) (trans (cong (subTm (extS (single a0))) (trans (cong (renTm vs) (trans (cong (renTm vs) (refl)) (num-ren vs n))) (num-ren vs n))) (num-sub (extS (single a0)) n))) (num-sub (single a1) n)

-- lam : RTm (Γ ∙) → RTm Γ
Tm-lamK : {Γ : Cx} → RTm Γ → RTm Γ
Tm-lamK a0 = icon tagTm-lam (pair a0 (pair (idrefl ⌜Nat⌝ sTm) unit))

⊢Tm-lamK : {Δ : Ctx} (n : ℕ) {a0 : RTm ⌊ Δ ⌋} →
        Δ ⊢ a0 ∷ K (pair sTm (num (suc (n)))) →
        Δ ⊢ Tm-lamK a0 ∷ K (pair sTm (num n))
⊢Tm-lamK n {a0 = a0} d0 =
  ⊢icon KnotWf memTm-lam (⊢ixP ⊢sTm (⊢num n))
    (⊢pair (ty-Σ (ty-El (⊢⌜Id⌝ ⊢⌜Nat⌝ (toI (⊢fst (⊢ixP ⊢sTm (⊢numAt n e0)))) (toI ⊢sTm))) (ty-Unit))
           (ixConv (ξ-pairʳ (ξ-nsuc (βsnd sTm (num n)))) (d0))
     (⊢pair (ty-Unit)
            (fordFst ⊢sTm)
      ⊢unit))
  where
    e0 : renTm vs (num n) ≡ num n
    e0 = trans (cong (renTm vs) (refl)) (num-ren vs n)

-- app : RTm Γ → RTm Γ → RTm Γ
Tm-appK : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ
Tm-appK a0 a1 = icon tagTm-app (pair a0 (pair a1 (pair (idrefl ⌜Nat⌝ sTm) unit)))

⊢Tm-appK : {Δ : Ctx} (n : ℕ) {a0 a1 : RTm ⌊ Δ ⌋} →
        Δ ⊢ a0 ∷ K (pair sTm (num n)) →
        Δ ⊢ a1 ∷ K (pair sTm (num n)) →
        Δ ⊢ Tm-appK a0 a1 ∷ K (pair sTm (num n))
⊢Tm-appK n {a0 = a0} {a1 = a1} d0 d1 =
  ⊢icon KnotWf memTm-app (⊢ixP ⊢sTm (⊢num n))
    (⊢pair (ty-Σ (ty-IMu KnotWf (⊢ixP ⊢sTm (⊢snd (⊢ixP ⊢sTm (⊢numAt n e1))))) (ty-Σ (ty-El (⊢⌜Id⌝ ⊢⌜Nat⌝ (toI (⊢fst (⊢ixP ⊢sTm (⊢numAt n e0)))) (toI ⊢sTm))) (ty-Unit)))
           (ixConv (ξ-pairʳ (βsnd sTm (num n))) (d0))
     (⊢pair (ty-Σ (ty-El (⊢⌜Id⌝ ⊢⌜Nat⌝ (toI (⊢fst (⊢ixP ⊢sTm (⊢numAt n e2)))) (toI ⊢sTm))) (ty-Unit))
            (ixConv (ξ-pairʳ (βsnd sTm (subTm (single a0) (renTm vs (num n))))) (kCast (sym e3) d1))
      (⊢pair (ty-Unit)
             (fordFst ⊢sTm)
       ⊢unit)))
  where
    e0 : renTm vs (renTm vs (num n)) ≡ num n
    e0 = trans (cong (renTm vs) (trans (cong (renTm vs) (refl)) (num-ren vs n))) (num-ren vs n)
    e1 : renTm vs (num n) ≡ num n
    e1 = trans (cong (renTm vs) (refl)) (num-ren vs n)
    e2 : subTm (extS (single a0)) (renTm vs (renTm vs (num n))) ≡ num n
    e2 = trans (cong (subTm (extS (single a0))) (trans (cong (renTm vs) (trans (cong (renTm vs) (refl)) (num-ren vs n))) (num-ren vs n))) (num-sub (extS (single a0)) n)
    e3 : subTm (single a0) (renTm vs (num n)) ≡ num n
    e3 = trans (cong (subTm (single a0)) (trans (cong (renTm vs) (refl)) (num-ren vs n))) (num-sub (single a0) n)

-- natrec : RTm Γ → RTm ((Γ ∙) ∙) → RTm Γ → RTm Γ
Tm-natrecK : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ → RTm Γ
Tm-natrecK a0 a1 a2 = icon tagTm-natrec (pair a0 (pair a1 (pair a2 (pair (idrefl ⌜Nat⌝ sTm) unit))))

⊢Tm-natrecK : {Δ : Ctx} (n : ℕ) {a0 a1 a2 : RTm ⌊ Δ ⌋} →
        Δ ⊢ a0 ∷ K (pair sTm (num n)) →
        Δ ⊢ a1 ∷ K (pair sTm (num (suc (suc (n))))) →
        Δ ⊢ a2 ∷ K (pair sTm (num n)) →
        Δ ⊢ Tm-natrecK a0 a1 a2 ∷ K (pair sTm (num n))
⊢Tm-natrecK n {a0 = a0} {a1 = a1} {a2 = a2} d0 d1 d2 =
  ⊢icon KnotWf memTm-natrec (⊢ixP ⊢sTm (⊢num n))
    (⊢pair (ty-Σ (ty-IMu KnotWf (⊢ixP ⊢sTm (⊢nsuc (⊢nsuc (⊢snd (⊢ixP ⊢sTm (⊢numAt n e2))))))) (ty-Σ (ty-IMu KnotWf (⊢ixP ⊢sTm (⊢snd (⊢ixP ⊢sTm (⊢numAt n e1))))) (ty-Σ (ty-El (⊢⌜Id⌝ ⊢⌜Nat⌝ (toI (⊢fst (⊢ixP ⊢sTm (⊢numAt n e0)))) (toI ⊢sTm))) (ty-Unit))))
           (ixConv (ξ-pairʳ (βsnd sTm (num n))) (d0))
     (⊢pair (ty-Σ (ty-IMu KnotWf (⊢ixP ⊢sTm (⊢snd (⊢ixP ⊢sTm (⊢numAt n e4))))) (ty-Σ (ty-El (⊢⌜Id⌝ ⊢⌜Nat⌝ (toI (⊢fst (⊢ixP ⊢sTm (⊢numAt n e3)))) (toI ⊢sTm))) (ty-Unit)))
            (ixConv (ξ-pairʳ (ξ-nsuc (ξ-nsuc (βsnd sTm (subTm (single a0) (renTm vs (num n))))))) (kCast (sym (cong nsuc (cong nsuc (e5)))) d1))
      (⊢pair (ty-Σ (ty-El (⊢⌜Id⌝ ⊢⌜Nat⌝ (toI (⊢fst (⊢ixP ⊢sTm (⊢numAt n e6)))) (toI ⊢sTm))) (ty-Unit))
             (ixConv (ξ-pairʳ (βsnd sTm (subTm (single a1) (subTm (extS (single a0)) (renTm vs (renTm vs (num n))))))) (kCast (sym e7) d2))
       (⊢pair (ty-Unit)
              (fordFst ⊢sTm)
        ⊢unit))))
  where
    e0 : renTm vs (renTm vs (renTm vs (num n))) ≡ num n
    e0 = trans (cong (renTm vs) (trans (cong (renTm vs) (trans (cong (renTm vs) (refl)) (num-ren vs n))) (num-ren vs n))) (num-ren vs n)
    e1 : renTm vs (renTm vs (num n)) ≡ num n
    e1 = trans (cong (renTm vs) (trans (cong (renTm vs) (refl)) (num-ren vs n))) (num-ren vs n)
    e2 : renTm vs (num n) ≡ num n
    e2 = trans (cong (renTm vs) (refl)) (num-ren vs n)
    e3 : subTm (extS (extS (single a0))) (renTm vs (renTm vs (renTm vs (num n)))) ≡ num n
    e3 = trans (cong (subTm (extS (extS (single a0)))) (trans (cong (renTm vs) (trans (cong (renTm vs) (trans (cong (renTm vs) (refl)) (num-ren vs n))) (num-ren vs n))) (num-ren vs n))) (num-sub (extS (extS (single a0))) n)
    e4 : subTm (extS (single a0)) (renTm vs (renTm vs (num n))) ≡ num n
    e4 = trans (cong (subTm (extS (single a0))) (trans (cong (renTm vs) (trans (cong (renTm vs) (refl)) (num-ren vs n))) (num-ren vs n))) (num-sub (extS (single a0)) n)
    e5 : subTm (single a0) (renTm vs (num n)) ≡ num n
    e5 = trans (cong (subTm (single a0)) (trans (cong (renTm vs) (refl)) (num-ren vs n))) (num-sub (single a0) n)
    e6 : subTm (extS (single a1)) (subTm (extS (extS (single a0))) (renTm vs (renTm vs (renTm vs (num n))))) ≡ num n
    e6 = trans (cong (subTm (extS (single a1))) (trans (cong (subTm (extS (extS (single a0)))) (trans (cong (renTm vs) (trans (cong (renTm vs) (trans (cong (renTm vs) (refl)) (num-ren vs n))) (num-ren vs n))) (num-ren vs n))) (num-sub (extS (extS (single a0))) n))) (num-sub (extS (single a1)) n)
    e7 : subTm (single a1) (subTm (extS (single a0)) (renTm vs (renTm vs (num n)))) ≡ num n
    e7 = trans (cong (subTm (single a1)) (trans (cong (subTm (extS (single a0))) (trans (cong (renTm vs) (trans (cong (renTm vs) (refl)) (num-ren vs n))) (num-ren vs n))) (num-sub (extS (single a0)) n))) (num-sub (single a1) n)

-- dκ : RTy ε → DCon → DCon
DCon-kapK : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ
DCon-kapK a0 a1 = icon tagDCon-kap (pair a0 (pair a1 (pair (idrefl ⌜Nat⌝ sDCon) unit)))

⊢DCon-kapK : {Δ : Ctx} (n : ℕ) {a0 a1 : RTm ⌊ Δ ⌋} →
        Δ ⊢ a0 ∷ K (pair sTy (num 0)) →
        Δ ⊢ a1 ∷ K (pair sDCon (num n)) →
        Δ ⊢ DCon-kapK a0 a1 ∷ K (pair sDCon (num n))
⊢DCon-kapK n {a0 = a0} {a1 = a1} d0 d1 =
  ⊢icon KnotWf memDCon-kap (⊢ixP ⊢sDCon (⊢num n))
    (⊢pair (ty-Σ (ty-IMu KnotWf (⊢ixP ⊢sDCon (⊢snd (⊢ixP ⊢sDCon (⊢numAt n e1))))) (ty-Σ (ty-El (⊢⌜Id⌝ ⊢⌜Nat⌝ (toI (⊢fst (⊢ixP ⊢sDCon (⊢numAt n e0)))) (toI ⊢sDCon))) (ty-Unit)))
           (d0)
     (⊢pair (ty-Σ (ty-El (⊢⌜Id⌝ ⊢⌜Nat⌝ (toI (⊢fst (⊢ixP ⊢sDCon (⊢numAt n e2)))) (toI ⊢sDCon))) (ty-Unit))
            (ixConv (ξ-pairʳ (βsnd sDCon (subTm (single a0) (renTm vs (num n))))) (kCast (sym e3) d1))
      (⊢pair (ty-Unit)
             (fordFst ⊢sDCon)
       ⊢unit)))
  where
    e0 : renTm vs (renTm vs (num n)) ≡ num n
    e0 = trans (cong (renTm vs) (trans (cong (renTm vs) (refl)) (num-ren vs n))) (num-ren vs n)
    e1 : renTm vs (num n) ≡ num n
    e1 = trans (cong (renTm vs) (refl)) (num-ren vs n)
    e2 : subTm (extS (single a0)) (renTm vs (renTm vs (num n))) ≡ num n
    e2 = trans (cong (subTm (extS (single a0))) (trans (cong (renTm vs) (trans (cong (renTm vs) (refl)) (num-ren vs n))) (num-ren vs n))) (num-sub (extS (single a0)) n)
    e3 : subTm (single a0) (renTm vs (num n)) ≡ num n
    e3 = trans (cong (subTm (single a0)) (trans (cong (renTm vs) (refl)) (num-ren vs n))) (num-sub (single a0) n)

