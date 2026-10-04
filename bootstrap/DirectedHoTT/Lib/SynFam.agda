-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- OCP-0009 · Lib — ★★ A FAMILY OVER A SYNTAX, FIBRED BY ITS SUBJECT
-- (D077), generic in the signature and the CONVOY.
--
-- The index is `(i , t , c)`: a syntax index `i`, the SUBJECT `t : SK i`,
-- and a convoy `c : El (C i)`.  The fibre over it is `Lib/SynFib`'s case
-- on `t` — the rows of `t`'s head:
--
--     J  = Σ (SI n) (λ i. Σ (SK i) (λ _. El (C i)))
--     D  = λ x. FIBM (fst x) (fst (snd x)) (snd (snd x))
--
-- Instances: the Knot's judgements (`⊢` with the convoy `(Γ , A)`; the
-- side conditions `NoNatC`/`stkA?` with a trivial convoy; `⟶` with the
-- target).  ★ The fibre method is OPAQUE (`context-form-mismatch-opaque`):
-- it carries every row, and a transparent one is compared by
-- normalisation wherever two syntactic forms of one context meet.
--
-- `--safe`, ZERO axioms.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Lib.SynFam where

open import normalizer.Syntax.Types using ( _≡_; refl; sym; trans; cong; cong₂; subst )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax hiding ( Fin )
open import DirectedHoTT.Spec.Typing hiding ( _×_; _,,_ )
open import DirectedHoTT.Metatheory.TySub using ( ⊢wk; ⊢-cast; wk-cancel-tm; sub-lemma; ⊢single )
open import DirectedHoTT.Metatheory.SubjectReductionBase using () renaming ( wk-sub to wkS )
open import DirectedHoTT.Metatheory.Fundamental.Syntactic using ( ⟨_⟩ᵣ; subTm-var )
open import DirectedHoTT.Metatheory.RedCong using ( ⟶*-trans; ⟶*-appˡ; ⟶*-appʳ; ⟶*-ielimⁱ; ⟶*-ielimᵗ; ⟶*-fst; ⟶*-snd )
open import DirectedHoTT.Lib.Sugar using ( tag; conₗ )
open import DirectedHoTT.Lib.Syn
open import DirectedHoTT.Lib.Tel
open import DirectedHoTT.Lib.SynFib
open import DirectedHoTT.Lib.SynTravM using ( +'-zero )

private
  variable
    Δ Θ : Cx
    n : ℕ

module SynFam {sg : Sig n} (ok : SigOK n sg)
              (C : {Δ : Cx} → RTm (Δ ∙)) (C-sub : {Δ Θ : Cx} (σ : Sub Δ Θ) → subTm (extS σ) (C {Δ}) ≡ C)
              (⊢C : {Γ : Ctx} → (Γ ▹ El (SI n)) ⊢ C ∷ U) where

  ----------------------------------------------------------------------
  -- 1. THE INDEX.
  ----------------------------------------------------------------------

  J : RTm Δ
  J = ⌜Σ⌝ (SI n) (⌜Σ⌝ (⌜IMu⌝ (SI n) (SD sg) (var vz)) (renTm vs C))

  J-sub : (σ : Sub Δ Θ) → subTm σ (J {Δ}) ≡ J
  J-sub {Δ} σ =
    cong₄ (λ I I' D X → ⌜Σ⌝ I (⌜Σ⌝ (⌜IMu⌝ I' D (var vz)) X))
          (SI-sub σ n) (SI-sub (extS σ) n)
          (SD-sub (extS σ) sg)
          (trans (wkS (extS σ) C) (cong (renTm vs) {x = subTm (extS σ) C} {y = C} (C-sub σ)))

  J-ren : (ρ : Ren Δ Θ) → renTm ρ (J {Δ}) ≡ J
  J-ren ρ = trans (sym (subTm-var ρ J)) (J-sub ⟨ ρ ⟩ᵣ)

  ⊢wkC : {Γ : Ctx} → ((Γ ▹ El (SI n)) ▹ El (⌜IMu⌝ (SI n) (SD sg) (var vz))) ⊢ renTm vs C ∷ U
  ⊢wkC {Γ} = ⊢wk {Γ ▹ El (SI n)} {El (⌜IMu⌝ (SI n) (SD sg) (var vz))} {C} {U} ⊢C

  ⊢J : {Γ : Ctx} → Γ ⊢ J ∷ U
  ⊢J = ⊢⌜Σ⌝ ⊢SI (⊢⌜Σ⌝ (⊢⌜IMu⌝ ⊢SI (⊢SD ok) (⊢varSI here (SI-wks 1))) ⊢wkC)

  open Fib₀ ok J J-sub ⊢J C C-sub ⊢C public

  -- a σ-field in a row of this family (the index weakens past it)
  okσ : {Γ : Ctx} {S : RTm ⌊ Γ ⌋} {T : Tel (⌊ Γ ⌋ ∙)} → Γ ⊢ S ∷ U → TelOK (Γ ▹ El S) J T → TelOK Γ J (tσ S T)
  okσ {Γ} {S} {T} dS okT = ok-σ dS (subst (λ X → TelOK (Γ ▹ El S) X T) (sym (J-ren vs)) okT)

  ixJ : RTm Δ → RTm Δ → RTm Δ → RTm Δ
  ixJ i t c = pair i (pair t c)

  private
    B1 : RTm (Δ ∙)
    B1 = ⌜Σ⌝ (⌜IMu⌝ (SI n) (SD sg) (var vz)) (renTm vs C)

    e1 : (i : RTm Δ) → subTy (single i) (El B1) ≡ El (⌜Σ⌝ (⌜IMu⌝ (SI n) (SD sg) i) (renTm vs (Cat i)))
    e1 {Δ} i = cong El (cong₂ ⌜Σ⌝ {x = subTm (single i) (⌜IMu⌝ (SI n) (SD {Δ = Δ ∙} sg) (var vz))} {x' = ⌜IMu⌝ (SI n) (SD sg) i}
                                 {y = subTm (extS (single i)) (renTm vs C)} {y' = renTm vs (Cat i)}
                         (cong₂ (λ I D → ⌜IMu⌝ I D i) (SI-sub (single i) n) (SD-sub (single i) sg))
                         (wkS (single i) C))

  ⊢ixJ : {Ξ : Ctx} {i t c : RTm ⌊ Ξ ⌋} → Ξ ⊢ i ∷ El (SI n) → Ξ ⊢ t ∷ IMu (SI n) (SD sg) i → Ξ ⊢ c ∷ El (Cat i) →
         Ξ ⊢ ixJ i t c ∷ El J
  ⊢ixJ {Ξ} {i} {t} {c} di dt dc = ⊢conv p1 (csymᵀ (credᵀ (El-⌜Σ⌝ (SI n) B1)))
    where
      B2 : RTm (⌊ Ξ ⌋ ∙)
      B2 = renTm vs (Cat i)
      e2 : subTy (single t) (El B2) ≡ El (Cat i)
      e2 = cong El (wk-cancel-tm t (Cat i))
      tyB1 : (Ξ ▹ El (SI n)) ⊢ty El B1
      tyB1 = ty-El (⊢⌜Σ⌝ (⊢⌜IMu⌝ ⊢SI (⊢SD ok) (⊢varSI here (SI-wks 1))) ⊢wkC)
      tyB2 : (Ξ ▹ El (⌜IMu⌝ (SI n) (SD sg) i)) ⊢ty El B2
      tyB2 = ty-El (⊢wk {Ξ} {El (⌜IMu⌝ (SI n) (SD sg) i)} {Cat i} {U} (⊢Cat di))
      p2 : Ξ ⊢ pair t c ∷ Σ' (El (⌜IMu⌝ (SI n) (SD sg) i)) (El B2)
      p2 = ⊢pair tyB2 (⊢conv dt (csymᵀ (credᵀ El-⌜IMu⌝)))
                 (⊢-cast {Ξ} {c} {El (Cat i)} {subTy (single t) (El B2)} (sym e2) dc)
      p1 : Ξ ⊢ ixJ i t c ∷ Σ' (El (SI n)) (El B1)
      p1 = ⊢pair tyB1 di
                 (⊢-cast {Ξ} {pair t c} {El (⌜Σ⌝ (⌜IMu⌝ (SI n) (SD sg) i) B2)} {subTy (single i) (El B1)} (sym (e1 i))
                         (⊢conv p2 (csymᵀ (credᵀ (El-⌜Σ⌝ (⌜IMu⌝ (SI n) (SD sg) i) B2)))))

  -- an index's three components (the inverse of `⊢ixJ`)
  module UnJ {Ξ : Ctx} {x : RTm ⌊ Ξ ⌋} (dx : Ξ ⊢ x ∷ El J) where
    i0 t0 c0 : RTm ⌊ Ξ ⌋
    i0 = fst x
    t0 = fst (snd x)
    c0 = snd (snd x)
    private
      B2 : RTm (⌊ Ξ ⌋ ∙)
      B2 = renTm vs (Cat i0)
      dx' : Ξ ⊢ x ∷ Σ' (El (SI n)) (El B1)
      dx' = ⊢conv dx (credᵀ (El-⌜Σ⌝ (SI n) B1))
      d2 : Ξ ⊢ snd x ∷ Σ' (El (⌜IMu⌝ (SI n) (SD sg) i0)) (El B2)
      d2 = ⊢conv (⊢-cast {Ξ} {snd x} {subTy (single i0) (El B1)} {El (⌜Σ⌝ (⌜IMu⌝ (SI n) (SD sg) i0) B2)} (e1 i0) (⊢snd dx'))
                 (credᵀ (El-⌜Σ⌝ (⌜IMu⌝ (SI n) (SD sg) i0) B2))
    di0 : Ξ ⊢ i0 ∷ El (SI n)
    di0 = ⊢fst dx'
    dt0 : Ξ ⊢ t0 ∷ IMu (SI n) (SD sg) i0
    dt0 = ⊢conv (⊢fst d2) (credᵀ El-⌜IMu⌝)
    dc0 : Ξ ⊢ c0 ∷ El (Cat i0)
    dc0 = ⊢-cast {Ξ} {c0} {subTy (single t0) (El B2)} {El (Cat i0)} (cong El (wk-cancel-tm t0 (Cat i0))) (⊢snd d2)

  ----------------------------------------------------------------------
  -- 2. ★ THE FAMILY, from a row table and its typing.
  ----------------------------------------------------------------------

  module Family (row : ℕ → ℕ → Row)
                (rowOK : {s c k : ℕ} {shs : Shapes c} {sh : Shape} → NthG sg s shs → NthSh shs k sh → RowOK s sh (row s k)) where

    open Fib ok J J-sub ⊢J C C-sub ⊢C row using ( FIBM; ⊢FIBM; FIBM-sub; fib-β ) renaming ( FM to FMₓ )

    opaque
      FIBMₒ : RTm Δ
      FIBMₒ = FIBM

      ⊢FIBMₒ : {Γ : Ctx} → Γ ⊢ FIBMₒ ∷ MethTy (SI n) (SD sg) FM
      ⊢FIBMₒ = ⊢FIBM rowOK

      FIBMₒ-sub : (σ : Sub Δ Θ) → subTm σ (FIBMₒ {Δ}) ≡ FIBMₒ
      FIBMₒ-sub σ = FIBM-sub σ

      fib-βₒ : {s c₀ k : ℕ} {shs : Shapes c₀} {sh : Shape} {D j p c : RTm Δ} → NthG sg s shs → NthSh shs k sh →
               app (ielim D (pair (tag s) j) FIBMₒ (conₗ k p)) c ⟶* Row.R (row s k) j p c
      fib-βₒ {D = D} {j = j} {p = p} {c = c} ng nh = fib-β {D = D} {j = j} {p = p} {c₀ = c} ng nh

    -- ★ THE FIBRE FUNCTION and the family
    DF : RTm Δ
    DF = lam (app (ielim (SD sg) (fst (var vz)) FIBMₒ (fst (snd (var vz)))) (snd (snd (var vz))))

    KF : RTm Δ → RTy Δ
    KF x = IMu J DF x

    DF-sub : (σ : Sub Δ Θ) → subTm σ (DF {Δ}) ≡ DF
    DF-sub {Δ} σ = cong₂ (λ D M → lam (app (ielim D (fst (var vz)) M (fst (snd (var vz)))) (snd (snd (var vz)))))
                         {x = subTm (extS σ) (SD {Δ = Δ ∙} sg)} {x' = SD sg} {y = subTm (extS σ) (FIBMₒ {Δ ∙})} {y' = FIBMₒ}
                         (SD-sub (extS σ) sg) (FIBMₒ-sub (extS σ))

    module _ {Γ : Ctx} where
      private
        dv : (Γ ▹ El J) ⊢ var vz ∷ El J
        dv = ⊢-cast {Γ ▹ El J} {var vz} {renTy vs (El J)} {El J} (cong El (J-ren vs)) (⊢var here)
        open UnJ dv
        dI : (Γ ▹ El J) ⊢ ielim (SD sg) i0 FIBMₒ t0 ∷ iinst i0 t0 FM
        dI = ⊢ielim {Γ ▹ El J} {SI n} {SD sg} {FM} {FIBMₒ} {i0} {t0} ⊢SI (⊢SD ok) ⊢FM ⊢FIBMₒ di0 dt0
        eI : iinst i0 t0 FM ≡ Π (El (Cat i0)) (Desc J)
        eI = trans {x = iinst i0 t0 FM} {y = subTy (single t0 ∘ₛ extS (single i0)) FM} {z = Π (El (Cat i0)) (Desc J)}
                   (subTy-subTy {τ = single t0} {σ = extS (single i0)} FM)
                   (trans (FM-sub (single t0 ∘ₛ extS (single i0)))
                          (cong (λ z → Π (El (Cat z)) (Desc J)) {x = subTm (single t0) (renTm vs i0)} {y = i0}
                                (wk-cancel-tm t0 i0)))
        bodyD : (Γ ▹ El J) ⊢ app (ielim (SD sg) i0 FIBMₒ t0) c0 ∷ Desc (renTm vs J)
        bodyD = ⊢-cast {Γ ▹ El J} {app (ielim (SD sg) i0 FIBMₒ t0) c0} {subTy (single c0) (Desc J)} {Desc (renTm vs J)}
                       (trans (cong Desc (J-sub (single c0))) (cong Desc (sym (J-ren vs))))
                       (⊢app {Γ ▹ El J} {El (Cat i0)} {Desc J} {ielim (SD sg) i0 FIBMₒ t0} {c0}
                             (⊢-cast {Γ ▹ El J} {ielim (SD sg) i0 FIBMₒ t0} {iinst i0 t0 FM} {Π (El (Cat i0)) (Desc J)} eI dI) dc0)

      -- ★ A WELL-FORMED FAMILY
      ⊢DF : Γ ⊢ DF ∷ DescF J
      ⊢DF = ⊢lam (ty-El ⊢J) bodyD

      ty-KF : {x : RTm ⌊ Γ ⌋} → Γ ⊢ x ∷ El J → Γ ⊢ty KF x
      ty-KF dx = ty-IMu ⊢J ⊢DF dx

    -- the fibre function at an index is the case on its subject
    DF-β : (i t c : RTm Δ) → app DF (ixJ i t c) ⟶* app (ielim (SD sg) i FIBMₒ t) c
    DF-β {Δ} i t c =
      step (β B x)
        (subst (λ z → z ⟶* app (ielim (SD sg) i FIBMₒ t) c) (sym e)
          (⟶*-trans {t = app (ielim (SD sg) (fst x) FIBMₒ (fst (snd x))) (snd (snd x))}
                    {u = app (ielim (SD sg) i FIBMₒ t) (snd (snd x))} {v = app (ielim (SD sg) i FIBMₒ t) c}
            (⟶*-appˡ (⟶*-trans {t = ielim (SD sg) (fst x) FIBMₒ (fst (snd x))} {u = ielim (SD sg) i FIBMₒ (fst (snd x))}
                                {v = ielim (SD sg) i FIBMₒ t}
                        (⟶*-ielimⁱ (step (βfst i (pair t c)) done))
                        (⟶*-ielimᵗ (⟶*-trans {t = fst (snd x)} {u = fst (pair t c)} {v = t}
                                      (⟶*-fst (step (βsnd i (pair t c)) done)) (step (βfst t c) done)))))
            (⟶*-appʳ (⟶*-trans {t = snd (snd x)} {u = snd (pair t c)} {v = c}
                       (⟶*-snd (step (βsnd i (pair t c)) done)) (step (βsnd t c) done)))))
      where
        x = ixJ i t c
        B : RTm (Δ ∙)
        B = app (ielim (SD sg) (fst (var vz)) FIBMₒ (fst (snd (var vz)))) (snd (snd (var vz)))
        e : subTm (single x) B ≡ app (ielim (SD sg) (fst x) FIBMₒ (fst (snd x))) (snd (snd x))
        e = cong₂ (λ D M → app (ielim D (fst x) M (fst (snd x))) (snd (snd x)))
                  {x = subTm (single x) (SD {Δ = Δ ∙} sg)} {x' = SD sg} {y = subTm (single x) (FIBMₒ {Δ ∙})} {y' = FIBMₒ}
                  (SD-sub (single x) sg) (FIBMₒ-sub (single x))

    -- ★ at a canonical subject, the fibre IS the row
    fibF : {s c₀ k : ℕ} {shs : Shapes c₀} {sh : Shape} {j p c : RTm Δ} → NthG sg s shs → NthSh shs k sh →
           app DF (ixJ (pair (tag s) j) (conₗ k p) c) ⟶* Row.R (row s k) j p c
    fibF {s = s} {k = k} {j = j} {p} {c} ng nh =
      ⟶*-trans (DF-β (pair (tag s) j) (conₗ k p) c) (fib-βₒ {D = SD sg} {j = j} {p = p} {c = c} ng nh)

  -- ★ THE FAMILY, from its table: the rows and their typings, in the
  --   signature's order (`RowsOKG`).  This is the form a family should be
  --   written in; `Family` is what it compiles to.
  module FamilyT (t : RowsOKG zero sg) =
    Family (rowIn t) (okOf t)
