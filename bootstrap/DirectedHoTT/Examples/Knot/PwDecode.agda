-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- OCP-0009 · KNOT — ★ `Pw` IS EXACTLY `pw?`/`pwBody` (PLAN-FAITHFUL F6,
-- the pilot): the converse of `PwAgree.⊢pwC`.
--
--     decPw : ◇ ⊢ x ∷ KPw (dep Γ) ⌜ c ⌝ ⌜ b ⌝ → IsNormal x →
--             pw? c ≡ true × b ≡ pwBody c
--
-- A closed normal inhabitant is one of the fibre's rules (`rows-dec`):
-- at `⌜Π⌝` the identity proof pins the body (quotes are normal and
-- injective, `Knot/Unquote`); at `⌜Hom⌝` the body field unquotes, the
-- premise decodes by recursion on `c`, and the identity proof meets the
-- Spec's body through `Xh-agree`.  Every other head's fibre is EMPTY
-- (`rows-none`).  Read along the constructor scheme of `PwConGen`.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Knot.PwDecode where

open import normalizer.Syntax.Types using ( _≡_; refl; sym; trans; cong; Σ; _,_; _×_; ⊥; ⊥-elim )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax
open import DirectedHoTT.Spec.Typing hiding ( _×_; _,,_ )
open import DirectedHoTT.Spec.Variance using ( 𝔹; true; false; pw?; pwBody )
open import DirectedHoTT.Metatheory.RedCong using ( red→≅ᵀ; ⟶ᵀ*-El; ⟶*-dpayᶜ )
open import DirectedHoTT.Metatheory.TySub using ( ⊢-cast; wk-cancel-tm )
open import DirectedHoTT.Metatheory.LogicalRelation using ( IsNormal )
open import DirectedHoTT.Lib.Sugar using ( Cons; []; _∷_; conₗ; atᶜ; v₀; v₁; v₂; v₃; v₄; _,ₚ_; nth-z )
open import DirectedHoTT.Examples.Knot.Ren using ( wk )
open import DirectedHoTT.Lib.SynRed
open import DirectedHoTT.Lib.Tel
open import DirectedHoTT.Lib.Syn
open import DirectedHoTT.Lib.Decode
open import DirectedHoTT.Examples.Knot.Sig
open import DirectedHoTT.Examples.Knot.Terms
open import DirectedHoTT.Examples.Knot.Unquote using ( unqTm; quoteTm-inj; quoteTm-normal )
open import DirectedHoTT.Examples.Knot.JudgeIx using ( ⌜Tm⌝; El-⌜Tm⌝ )
open import DirectedHoTT.Examples.Knot.JudgeCase using ( w1 )
open import DirectedHoTT.Examples.Knot.RedIx
open import DirectedHoTT.Examples.Knot.Pw
open import DirectedHoTT.Examples.Knot.PwAgree using ( Xh; Xh-agree )

private
  -- the `⌜Hom⌝` row's telescope, read at the payload's values (`PwConGen`'s R₀)
  R₀Hom : (Γ : Cx) (a0 a1 a2 : RTm Γ) (c : RTm ε) →
          ⌜ TPwcHom (dep Γ) (quoteTm a0 ,ₚ quoteTm a1 ,ₚ quoteTm a2 ,ₚ unit) c ⌝ᵗ
            ⟶* ⌜ TPwcHom⁽0⁾ (dep Γ) c (quoteTm a0) (quoteTm a1) (quoteTm a2) ⌝ᵗ
  R₀Hom Γ a0 a1 a2 c =
    mono-by {Δ = ε} {n = 5} {as = (j ∷ c ∷ (fst p) ∷ (fst (snd p)) ∷ (fst (snd (snd p))) ∷ [])} {as' = (j ∷ c ∷ f0 ∷ f1 ∷ f2 ∷ [])}
      ⌜ TPwcHom⁽0⁾ v₀ v₁ v₂ v₃ v₄ ⌝ᵗ
      (TPwcHom⁽0⁾-sub (σₗ (j ∷ c ∷ (fst p) ∷ (fst (snd p)) ∷ (fst (snd (snd p))) ∷ [])) v₀ v₁ v₂ v₃ v₄)
      (TPwcHom⁽0⁾-sub (σₗ (j ∷ c ∷ f0 ∷ f1 ∷ f2 ∷ [])) v₀ v₁ v₂ v₃ v₄)
      (done ∷ʳ done ∷ʳ (prj-tup {ws = f0 ∷ f1 ∷ f2 ∷ []} unit (atᶜ 0)) ∷ʳ (prj-tup {ws = f0 ∷ f1 ∷ f2 ∷ []} unit (atᶜ 1))
            ∷ʳ (prj-tup {ws = f0 ∷ f1 ∷ f2 ∷ []} unit (atᶜ 2)) ∷ʳ []ʳ)
    where
      j f0 f1 f2 p : RTm ε
      j = dep Γ
      f0 = quoteTm a0
      f1 = quoteTm a1
      f2 = quoteTm a2
      p = (f0 ,ₚ f1 ,ₚ f2 ,ₚ unit)

  -- the β past the body field, cast to the row's next telescope (`PwConGen`'s dPv)
  restHom : {j c f0 f1 f2 e q : RTm ε} →
            ◇ ⊢ q ∷ El (dpay Pwₘ.J PwF.DF (app (lam ⌜ TPwcHom⁽1⁾ (w1 j) (w1 c) (w1 f0) (w1 f1) (w1 f2) v₀ ⌝ᵗ) e)) →
            ◇ ⊢ q ∷ El (dpay Pwₘ.J PwF.DF ⌜ TPwcHom⁽1⁾ j c f0 f1 f2 e ⌝ᵗ)
  restHom {j} {c} {f0} {f1} {f2} {e} dq =
    ⊢-cast (cong (λ Z → El (dpay Pwₘ.J PwF.DF Z))
                 (trans (TPwcHom⁽1⁾-sub (single e) (w1 j) (w1 c) (w1 f0) (w1 f1) (w1 f2) v₀)
                        (TPwcHom⁽1⁾-cong (subTm (single e) (w1 j)) j (subTm (single e) (w1 c)) c
                                         (subTm (single e) (w1 f0)) f0 (subTm (single e) (w1 f1)) f1
                                         (subTm (single e) (w1 f2)) f2 (subTm (single e) v₀) e
                                         (wk-cancel-tm e j) (wk-cancel-tm e c) (wk-cancel-tm e f0)
                                         (wk-cancel-tm e f1) (wk-cancel-tm e f2) refl)))
           (⊢conv dq (red→≅ᵀ (⟶ᵀ*-El (⟶*-dpayᶜ (step (β _ e) done)))))

-- the pieces of the two rows, at quoted arguments
module _ {Γ : Cx} where
  PΠ : RTm Γ → RTm (Γ ∙) → RTm ε
  PΠ a0 a1 = quoteTm a0 ,ₚ quoteTm a1 ,ₚ unit
  CΠ : RTm Γ → RTm (Γ ∙) → RTm (Γ ∙) → RTm ε
  CΠ a0 a1 b = ⌜ TPwcPi (dep Γ) (PΠ a0 a1) (quoteTm b) ⌝ᵗ
  PH : (a0 a1 a2 : RTm Γ) → RTm ε
  PH a0 a1 a2 = quoteTm a0 ,ₚ quoteTm a1 ,ₚ quoteTm a2 ,ₚ unit
  CH : (a0 a1 a2 : RTm Γ) → RTm (Γ ∙) → RTm ε
  CH a0 a1 a2 b = ⌜ TPwcHom (dep Γ) (PH a0 a1 a2) (quoteTm b) ⌝ᵗ
  CH₀ : (a0 a1 a2 : RTm Γ) → RTm (Γ ∙) → RTm ε
  CH₀ a0 a1 a2 b = ⌜ TPwcHom⁽0⁾ (dep Γ) (quoteTm b) (quoteTm a0) (quoteTm a1) (quoteTm a2) ⌝ᵗ
  TH₁w : (a0 a1 a2 : RTm Γ) → RTm (Γ ∙) → RTm (ε ∙)
  TH₁w a0 a1 a2 b = ⌜ TPwcHom⁽1⁾ (w1 (dep Γ)) (w1 (quoteTm b)) (w1 (quoteTm a0)) (w1 (quoteTm a1)) (w1 (quoteTm a2)) v₀ ⌝ᵗ
  CH₁ : (a0 a1 a2 : RTm Γ) → RTm (Γ ∙) → RTm ε → RTm ε
  CH₁ a0 a1 a2 b e = ⌜ TPwcHom⁽1⁾ (dep Γ) (quoteTm b) (quoteTm a0) (quoteTm a1) (quoteTm a2) e ⌝ᵗ
  IdH : (a1 a2 : RTm Γ) → RTm (Γ ∙) → RTm ε → RTm ε
  IdH a1 a2 b e = ⌜Id⌝ (⌜Tm⌝ (nsuc (dep Γ))) (quoteTm b)
                       (kcHom e (kapp (wk 1 (dep Γ) (quoteTm a1)) (kvar fzero)) (kapp (wk 1 (dep Γ) (quoteTm a2)) (kvar fzero)))

-- ★ THE DECODER — written WITHOUT `with`: a with-abstraction over these
--   contexts runs out of memory (measured: > 5 GB, the same call 8 s as an
--   argument).  Each decoding step is a helper with its type stated.
decPw : {Γ : Cx} (c : RTm Γ) {b : RTm (Γ ∙)} {x : RTm ε} →
        ◇ ⊢ x ∷ KPw (dep Γ) (quoteTm c) (quoteTm b) → IsNormal x →
        (pw? c ≡ true) × (b ≡ pwBody c)

private
  decΠ : {Γ : Cx} (a0 : RTm Γ) (a1 : RTm (Γ ∙)) {b : RTm (Γ ∙)} {x : RTm ε} →
         RowsDec Pwₘ.J PwF.DF (CΠ a0 a1 b ∷ []) x → b ≡ a1
  decΠ₁ : {Γ : Cx} (a0 : RTm Γ) (a1 : RTm (Γ ∙)) {b : RTm (Γ ∙)} {q : RTm ε} →
          PayΣ Pwₘ.J PwF.DF (⌜Id⌝ (⌜Tm⌝ (nsuc (dep Γ))) (quoteTm b) (fst (snd (PΠ a0 a1)))) (lam dι) q → b ≡ a1

  decH : {Γ : Cx} (a0 a1 a2 : RTm Γ) {b : RTm (Γ ∙)} {x : RTm ε} →
         RowsDec Pwₘ.J PwF.DF (CH a0 a1 a2 b ∷ []) x → (pw? a0 ≡ true) × (b ≡ pwBody (⌜Hom⌝ a0 a1 a2))
  decH₁ : {Γ : Cx} (a0 a1 a2 : RTm Γ) {b : RTm (Γ ∙)} {q : RTm ε} →
          PayΣ Pwₘ.J PwF.DF (⌜Tm⌝ (nsuc (dep Γ))) (lam (TH₁w a0 a1 a2 b)) q →
          (pw? a0 ≡ true) × (b ≡ pwBody (⌜Hom⌝ a0 a1 a2))
  decH₂ : {Γ : Cx} (a0 a1 a2 : RTm Γ) {b : RTm (Γ ∙)} (e rest : RTm ε) → Σ (RTm (Γ ∙)) (λ E → e ≡ quoteTm E) →
          ◇ ⊢ rest ∷ El (dpay Pwₘ.J PwF.DF (app (lam (TH₁w a0 a1 a2 b)) e)) → IsNormal rest →
          (pw? a0 ≡ true) × (b ≡ pwBody (⌜Hom⌝ a0 a1 a2))
  decH₃ : {Γ : Cx} (a0 a1 a2 : RTm Γ) {b : RTm (Γ ∙)} (E : RTm (Γ ∙)) {rest : RTm ε} →
          PayΡ Pwₘ.J PwF.DF (ixPw (dep Γ) (quoteTm a0) (quoteTm E)) ⌜ tσ (IdH a1 a2 b (quoteTm E)) tι ⌝ᵗ rest →
          (pw? a0 ≡ true) × (b ≡ pwBody (⌜Hom⌝ a0 a1 a2))
  decH₄ : {Γ : Cx} (a0 a1 a2 : RTm Γ) {b : RTm (Γ ∙)} (E : RTm (Γ ∙)) {rest : RTm ε} →
          (pw? a0 ≡ true) × (E ≡ pwBody a0) →
          PayΣ Pwₘ.J PwF.DF (IdH a1 a2 b (quoteTm E)) (lam dι) rest →
          (pw? a0 ≡ true) × (b ≡ pwBody (⌜Hom⌝ a0 a1 a2))

  decΠ {Γ} a0 a1 {b} (_ , (_ , (q , (nth-z , (_ , (dq , nq)))))) =
    decΠ₁ a0 a1 {b} (pay-σ {I = Pwₘ.J} {D = PwF.DF} {C = CΠ a0 a1 b}
                           {S = ⌜Id⌝ (⌜Tm⌝ (nsuc (dep Γ))) (quoteTm b) (fst (snd (PΠ a0 a1)))} {f = lam dι} dq done nq)
  decΠ₁ a0 a1 {b} (a , (_ , (_ , ((da , _) , (na , _))))) =
    quoteTm-inj b a1 (nf-≅ (quoteTm-normal b) (quoteTm-normal a1)
      (ctrn (idrefl-decᶜ da na) (ctrn (cred (ξ-fst (βsnd _ _))) (cred (βfst _ _)))))

  decH {Γ} a0 a1 a2 {b} (_ , (_ , (q , (nth-z , (_ , (dq , nq)))))) =
    decH₁ a0 a1 a2 {b}
      (pay-σ {I = Pwₘ.J} {D = PwF.DF} {C = CH₀ a0 a1 a2 b} {S = ⌜Tm⌝ (nsuc (dep Γ))} {f = lam (TH₁w a0 a1 a2 b)}
             (⊢conv dq (red→≅ᵀ (⟶ᵀ*-El (⟶*-dpayᶜ (R₀Hom Γ a0 a1 a2 (quoteTm b)))))) done nq)
  decH₁ {Γ} a0 a1 a2 {b} (e , (rest , (_ , ((de , drest) , (ne , nrest))))) =
    decH₂ a0 a1 a2 {b} e rest (unqTm {Γ = Γ ∙} (⊢conv de (credᵀ El-⌜Tm⌝)) ne) drest nrest
  decH₂ {Γ} a0 a1 a2 {b} _ rest (E , refl) drest nrest =
    decH₃ a0 a1 a2 {b} E
      (pay-ρ {I = Pwₘ.J} {D = PwF.DF} {C = CH₁ a0 a1 a2 b (quoteTm E)} {j = ixPw (dep Γ) (quoteTm a0) (quoteTm E)}
             {C' = ⌜ tσ (IdH a1 a2 b (quoteTm E)) tι ⌝ᵗ} (restHom drest) done nrest)
  decH₃ {Γ} a0 a1 a2 {b} E (r , (rest₂ , (_ , ((dr , drest₂) , (nr , nrest₂))))) =
    decH₄ a0 a1 a2 {b} E (decPw a0 {E} dr nr)
      (pay-σ {I = Pwₘ.J} {D = PwF.DF} {C = ⌜ tσ (IdH a1 a2 b (quoteTm E)) tι ⌝ᵗ} {S = IdH a1 a2 b (quoteTm E)} {f = lam dι}
             drest₂ done nrest₂)
  decH₄ a0 a1 a2 {b} _ (k0 , refl) (idp , (_ , (_ , ((didp , _) , (nidp , _))))) =
    k0 , quoteTm-inj b (pwBody (⌜Hom⌝ a0 a1 a2))
           (nf-≅ (quoteTm-normal b) (quoteTm-normal (pwBody (⌜Hom⌝ a0 a1 a2)))
                 (ctrn (idrefl-decᶜ didp nidp) (⟶*→≅ (Xh-agree a0 a1 a2))))

decPw {Γ} (⌜Π⌝ a0 a1) {b} dx nrm =
  refl , decΠ a0 a1 {b}
    (rows-dec {I = Pwₘ.J} {D = PwF.DF} {i = ixPw (dep Γ) (quoteTm (⌜Π⌝ a0 a1)) (quoteTm b)} {m = 1} {Cs = CΠ a0 a1 b ∷ []}
              (PwF.fibF {s = 1} {k = 9} {j = dep Γ} {p = PΠ a0 a1} {c = quoteTm b} (atᵍ 1) (atʰ 9)) dx nrm)
decPw {Γ} (⌜Hom⌝ a0 a1 a2) {b} dx nrm =
  decH a0 a1 a2 {b}
    (rows-dec {I = Pwₘ.J} {D = PwF.DF} {i = ixPw (dep Γ) (quoteTm (⌜Hom⌝ a0 a1 a2)) (quoteTm b)} {m = 1} {Cs = CH a0 a1 a2 b ∷ []}
              (PwF.fibF {s = 1} {k = 11} {j = dep Γ} {p = PH a0 a1 a2} {c = quoteTm b} (atᵍ 1) (atʰ 11)) dx nrm)
-- every other head: the fibre has no rule
decPw {Γ} (var a0) {b} dx nrm = ⊥-elim (rows-none (PwF.fibF {s = 1} {k = 0} {j = dep Γ} {c = quoteTm b} (atᵍ 1) (atʰ 0)) dx nrm)
decPw {Γ} (lam a0) {b} dx nrm = ⊥-elim (rows-none (PwF.fibF {s = 1} {k = 1} {j = dep Γ} {c = quoteTm b} (atᵍ 1) (atʰ 1)) dx nrm)
decPw {Γ} (app a0 a1) {b} dx nrm = ⊥-elim (rows-none (PwF.fibF {s = 1} {k = 2} {j = dep Γ} {c = quoteTm b} (atᵍ 1) (atʰ 2)) dx nrm)
decPw {Γ} (pair a0 a1) {b} dx nrm = ⊥-elim (rows-none (PwF.fibF {s = 1} {k = 3} {j = dep Γ} {c = quoteTm b} (atᵍ 1) (atʰ 3)) dx nrm)
decPw {Γ} (absurd a0 a1) {b} dx nrm = ⊥-elim (rows-none (PwF.fibF {s = 1} {k = 4} {j = dep Γ} {c = quoteTm b} (atᵍ 1) (atʰ 4)) dx nrm)
decPw {Γ} (ordtr a0 a1 a2 a3 a4) {b} dx nrm = ⊥-elim (rows-none (PwF.fibF {s = 1} {k = 5} {j = dep Γ} {c = quoteTm b} (atᵍ 1) (atʰ 5)) dx nrm)
decPw {Γ} (fst a0) {b} dx nrm = ⊥-elim (rows-none (PwF.fibF {s = 1} {k = 6} {j = dep Γ} {c = quoteTm b} (atᵍ 1) (atʰ 6)) dx nrm)
decPw {Γ} (snd a0) {b} dx nrm = ⊥-elim (rows-none (PwF.fibF {s = 1} {k = 7} {j = dep Γ} {c = quoteTm b} (atᵍ 1) (atʰ 7)) dx nrm)
decPw {Γ} ⌜base⌝ {b} dx nrm = ⊥-elim (rows-none (PwF.fibF {s = 1} {k = 8} {j = dep Γ} {c = quoteTm b} (atᵍ 1) (atʰ 8)) dx nrm)
decPw {Γ} (⌜Σ⌝ a0 a1) {b} dx nrm = ⊥-elim (rows-none (PwF.fibF {s = 1} {k = 10} {j = dep Γ} {c = quoteTm b} (atᵍ 1) (atʰ 10)) dx nrm)
decPw {Γ} (hrefl a0 a1) {b} dx nrm = ⊥-elim (rows-none (PwF.fibF {s = 1} {k = 12} {j = dep Γ} {c = quoteTm b} (atᵍ 1) (atʰ 12)) dx nrm)
decPw {Γ} (tr a0 a1 a2) {b} dx nrm = ⊥-elim (rows-none (PwF.fibF {s = 1} {k = 13} {j = dep Γ} {c = quoteTm b} (atᵍ 1) (atʰ 13)) dx nrm)
decPw {Γ} (ap a0 a1 a2) {b} dx nrm = ⊥-elim (rows-none (PwF.fibF {s = 1} {k = 14} {j = dep Γ} {c = quoteTm b} (atᵍ 1) (atʰ 14)) dx nrm)
decPw {Γ} (⌜Id⌝ a0 a1 a2) {b} dx nrm = ⊥-elim (rows-none (PwF.fibF {s = 1} {k = 15} {j = dep Γ} {c = quoteTm b} (atᵍ 1) (atʰ 15)) dx nrm)
decPw {Γ} (idrefl a0 a1) {b} dx nrm = ⊥-elim (rows-none (PwF.fibF {s = 1} {k = 16} {j = dep Γ} {c = quoteTm b} (atᵍ 1) (atʰ 16)) dx nrm)
decPw {Γ} (jsub a0 a1 a2) {b} dx nrm = ⊥-elim (rows-none (PwF.fibF {s = 1} {k = 17} {j = dep Γ} {c = quoteTm b} (atᵍ 1) (atʰ 17)) dx nrm)
decPw {Γ} unit {b} dx nrm = ⊥-elim (rows-none (PwF.fibF {s = 1} {k = 18} {j = dep Γ} {c = quoteTm b} (atᵍ 1) (atʰ 18)) dx nrm)
decPw {Γ} nzero {b} dx nrm = ⊥-elim (rows-none (PwF.fibF {s = 1} {k = 19} {j = dep Γ} {c = quoteTm b} (atᵍ 1) (atʰ 19)) dx nrm)
decPw {Γ} (nsuc a0) {b} dx nrm = ⊥-elim (rows-none (PwF.fibF {s = 1} {k = 20} {j = dep Γ} {c = quoteTm b} (atᵍ 1) (atʰ 20)) dx nrm)
decPw {Γ} (natrec a0 a1 a2) {b} dx nrm = ⊥-elim (rows-none (PwF.fibF {s = 1} {k = 21} {j = dep Γ} {c = quoteTm b} (atᵍ 1) (atʰ 21)) dx nrm)
decPw {Γ} (con a0) {b} dx nrm = ⊥-elim (rows-none (PwF.fibF {s = 1} {k = 22} {j = dep Γ} {c = quoteTm b} (atᵍ 1) (atʰ 22)) dx nrm)
decPw {Γ} (ielim a0 a1 a2 a3) {b} dx nrm = ⊥-elim (rows-none (PwF.fibF {s = 1} {k = 23} {j = dep Γ} {c = quoteTm b} (atᵍ 1) (atʰ 23)) dx nrm)
decPw {Γ} dι {b} dx nrm = ⊥-elim (rows-none (PwF.fibF {s = 1} {k = 24} {j = dep Γ} {c = quoteTm b} (atᵍ 1) (atʰ 24)) dx nrm)
decPw {Γ} (dσ a0 a1) {b} dx nrm = ⊥-elim (rows-none (PwF.fibF {s = 1} {k = 25} {j = dep Γ} {c = quoteTm b} (atᵍ 1) (atʰ 25)) dx nrm)
decPw {Γ} (dρ a0 a1) {b} dx nrm = ⊥-elim (rows-none (PwF.fibF {s = 1} {k = 26} {j = dep Γ} {c = quoteTm b} (atᵍ 1) (atʰ 26)) dx nrm)
decPw {Γ} (dpay a0 a1 a2) {b} dx nrm = ⊥-elim (rows-none (PwF.fibF {s = 1} {k = 27} {j = dep Γ} {c = quoteTm b} (atᵍ 1) (atʰ 27)) dx nrm)
decPw {Γ} (dih a0 a1 a2 a3) {b} dx nrm = ⊥-elim (rows-none (PwF.fibF {s = 1} {k = 28} {j = dep Γ} {c = quoteTm b} (atᵍ 1) (atʰ 28)) dx nrm)
decPw {Γ} fzero {b} dx nrm = ⊥-elim (rows-none (PwF.fibF {s = 1} {k = 29} {j = dep Γ} {c = quoteTm b} (atᵍ 1) (atʰ 29)) dx nrm)
decPw {Γ} (fsuc a0) {b} dx nrm = ⊥-elim (rows-none (PwF.fibF {s = 1} {k = 30} {j = dep Γ} {c = quoteTm b} (atᵍ 1) (atʰ 30)) dx nrm)
decPw {Γ} (fcase a0 a1 a2) {b} dx nrm = ⊥-elim (rows-none (PwF.fibF {s = 1} {k = 31} {j = dep Γ} {c = quoteTm b} (atᵍ 1) (atʰ 31)) dx nrm)
decPw {Γ} (fcase0 a0) {b} dx nrm = ⊥-elim (rows-none (PwF.fibF {s = 1} {k = 32} {j = dep Γ} {c = quoteTm b} (atᵍ 1) (atʰ 32)) dx nrm)
decPw {Γ} (psplit a0 a1) {b} dx nrm = ⊥-elim (rows-none (PwF.fibF {s = 1} {k = 33} {j = dep Γ} {c = quoteTm b} (atᵍ 1) (atʰ 33)) dx nrm)
decPw {Γ} ⌜Nat⌝ {b} dx nrm = ⊥-elim (rows-none (PwF.fibF {s = 1} {k = 34} {j = dep Γ} {c = quoteTm b} (atᵍ 1) (atʰ 34)) dx nrm)
decPw {Γ} (⌜IMu⌝ a0 a1 a2) {b} dx nrm = ⊥-elim (rows-none (PwF.fibF {s = 1} {k = 35} {j = dep Γ} {c = quoteTm b} (atᵍ 1) (atʰ 35)) dx nrm)
decPw {Γ} (⌜Fin⌝ a0) {b} dx nrm = ⊥-elim (rows-none (PwF.fibF {s = 1} {k = 36} {j = dep Γ} {c = quoteTm b} (atᵍ 1) (atʰ 36)) dx nrm)
decPw {Γ} ⌜Unit⌝ {b} dx nrm = ⊥-elim (rows-none (PwF.fibF {s = 1} {k = 37} {j = dep Γ} {c = quoteTm b} (atᵍ 1) (atʰ 37)) dx nrm)
decPw {Γ} (ref a0 a1) {b} dx nrm = ⊥-elim (rows-none (PwF.fibF {s = 1} {k = 38} {j = dep Γ} {c = quoteTm b} (atᵍ 1) (atʰ 38)) dx nrm)
