-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- OCP-0009 · Lib — ★★★ THE GENERIC TRAVERSAL, assembled: the one method
-- of a `Lib/Syn` syntax at the traversal's motive, and the traversal
--
--     trav t e f  :  Syn s e        for  t : Syn s d,  f : Fin d → V e
--
-- for ANY signature and ANY kit (`Lib/SynTrav`).  Renaming and
-- substitution (`Lib/SynRen`, `Lib/SynSub`) are its two instances.
--
-- ★ The variable rows are the kit's (`NODE`); every other row is the
--   generic node rebuild (`⊢mT-f`).  The kit's variable sort must be
--   where the signature's variables live (`VarsAt`).
--
-- `--safe`, ZERO axioms.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Lib.SynTravM where

open import normalizer.Syntax.Types using ( _≡_; refl; sym; trans; cong; cong₂; subst; _×_; _,_ )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax hiding ( Fin )
open import DirectedHoTT.Spec.Typing hiding ( _×_; _,,_ )
open import DirectedHoTT.Metatheory.RedCong using ( red→≅ᵀ; ⟶ᵀ*-IMu; ⟶ᵀ*-Πˡ; ⟶*-pairˡ )
open import DirectedHoTT.Metatheory.TySub using ( ⊢wk; ⊢-cast )
open import DirectedHoTT.Metatheory.Premises using ( mot-ren; ⊢wkD )
open import DirectedHoTT.Lib.Sugar using ( Cons; []; _∷_; selF; subC; tag; conₗ; selF-β; nth-sub; Lt )
open import DirectedHoTT.Lib.Tel
open import DirectedHoTT.Lib.TelAt using ( allSD; nth-⌜⌝ₛₛ )
open import DirectedHoTT.Lib.MethAt
open import DirectedHoTT.Lib.FinFam using ( FinD; FinI )
open import DirectedHoTT.Lib.Sorted using ( σₛ; ιₛ; ⊢ιₛ; PerS; []ₚ; _∷ₚ_; ⊢sortMeth; ⊢methₛ; SortT )
open import DirectedHoTT.Lib.Syn
open import DirectedHoTT.Lib.SynView
open import DirectedHoTT.Lib.SynTrav

private
  variable
    Γ : Cx
    n : ℕ

-- the signature's variables all live in sort `v`
VarsAt : {n : ℕ} → Sig n → ℕ → Set
VarsAt sg v = {s c k : ℕ} {shs : Shapes c} → NthG sg s shs → NthSh shs k vʰ → v ≡ s

-- `j +' k` counts `j` on from `k`, head case definitional
infixl 30 _+'_
_+'_ : ℕ → ℕ → ℕ
zero  +' k = k
suc j +' k = j +' suc k

+'-suc : (j k : ℕ) → j +' suc k ≡ suc (j +' k)
+'-suc zero    k = refl
+'-suc (suc j) k = +'-suc j (suc k)

+'-zero : (j : ℕ) → j +' zero ≡ j
+'-zero zero    = refl
+'-zero (suc j) = trans (+'-suc j zero) (cong suc (+'-zero j))

module TravM {sg : Sig n} (ok : SigOK n sg) (κ : Kit n sg) (vok : VarsAt sg (Kit.vsort κ)) where
  open Kit κ
  open Trav ok κ

  ------------------------------------------------------------------------
  -- 1. THE VARIABLE ROW: its value, as a node.
  ------------------------------------------------------------------------

  ⊢mTv : {Γ : Ctx} {s k c : ℕ} {shs : Shapes c} → NthG sg s shs → NthSh shs k vʰ →
         (Γ ▹ El ⌜Nat⌝) ⊢ mTv ∷ MethKAt (renTm vs (SI n)) (renTm vs (SD sg)) (wk1M TM) (ιₛ s)
                                        (subTm (σₛ s) ⌜ tel vʰ (var vz) ⌝ᵗ) k
  ⊢mTv {Γ = Γ} {s = s} {k = k} ng nh =
    ⊢lam dPay (⊢lam dHyp (⊢-cast (sym eqT) BODY))
    where
      Γ' = Γ ▹ El ⌜Nat⌝
      ιx = ιₛ {Δ = ⌊ Γ ⌋} s
      C = subTm (σₛ s) ⌜ tel vʰ (var vz) ⌝ᵗ
      dix : Γ' ⊢ ιx ∷ El (SI n)
      dix = ⊢ιₛ ⊢⌜Nat⌝ (nthG-lt ng)
      dC : Γ' ⊢ C ∷ Desc (SI n)
      dC = ⊢tel ⊢SI (telOK vᵒʰ dix)
      dD' = ⊢wkD {B = El ⌜Nat⌝} (⊢SD {Γ = Γ} ok)
      dPay = ty-El (⊢dpay ⊢SI dD' dC)
      dHyp = ty-DIh ⊢SI (⊢wkD dD') (mot-ren there (mot-ren there (⊢TM {Γ = Γ}))) (⊢wk dC) (⊢var here)
      τ = atS ιx (conₗ k (var (vs vz))) ₛ∘ᵣ extR (extR vs)
      eqT = trans (subTy-renTy TM) (TM-sub τ)
      ι₃ = renTm vs (renTm vs (renTm vs ιx))
      ι₄ = r4 ιx
      Pay = El (dpay (renTm vs (SI n)) (renTm vs (SD sg)) C)
      Hyp = DIh (renTm vs (renTm vs (SD sg))) (wk1M (wk1M TM)) (renTm vs C) (var vz)
      Γ₂ = (Γ' ▹ Pay) ▹ Hyp
      Γ₄ = (Γ₂ ▹ El ⌜Nat⌝) ▹ Env (snd ι₃) (var vz)
      p₄ e₄ f₄ j₄ : RTm ⌊ Γ₄ ⌋
      p₄ = var (vs (vs (vs vz)))
      e₄ = var (vs vz)
      f₄ = var vz
      j₄ = var (vs (vs (vs (vs vz))))
      dp : Γ₄ ⊢ p₄ ∷ PayV vʰ ι₄ (SI n) (SD sg)
      dp = ⊢conv (⊢-cast (cong₂ (λ D X → El (dpay (SI n) D X)) SD-r4 (tel-r4 s vʰ)) (⊢var (there (there (there here)))))
                 (red→≅ᵀ (payV-red vʰ ι₄ (SI n) (SD sg)))
      dx : Γ₄ ⊢ fst p₄ ∷ FinI j₄
      dx = ⊢conv (⊢fst dp) (ctrnᵀ (credᵀ El-⌜IMu⌝) (credᵀ (ξ-IMuⁱ (βsnd _ _))))
      de : Γ₄ ⊢ e₄ ∷ El ⌜Nat⌝
      de = ⊢var (there here)
      df : Γ₄ ⊢ f₄ ∷ Env j₄ e₄
      df = ⊢conv (⊢-cast (Env-ren vs (snd ι₃) (var vz)) (⊢var here))
                 (red→≅ᵀ (⟶ᵀ*-Πˡ (⟶ᵀ*-IMu (step (βsnd _ _) done))))
      NODEv : Γ₄ ⊢ app (app NODE e₄) (app f₄ (fst p₄)) ∷ SK sg s e₄
      NODEv = subst (λ z → Γ₄ ⊢ app (app NODE e₄) (app f₄ (fst p₄)) ∷ SK sg z e₄) (vok ng nh)
                    (⊢NODE· de (⊢Env· df dx))
      BODY : Γ₂ ⊢ lam (lam (app (app NODE e₄) (app f₄ (fst p₄))))
                 ∷ Π (El ⌜Nat⌝) (Π (Env (snd ι₃) (var vz))
                                   (IMu (SI n) (SD sg) (pair (fst ι₄) (var (vs vz)))))
      BODY = ⊢lam (ty-El ⊢⌜Nat⌝)
               (⊢lam (ty-Env (⊢depth (⊢wk (⊢wk (⊢wk dix)))) (⊢var here))
                 (⊢conv (⊢-cast (cong (λ z → IMu (SI n) (SD sg) (pair z e₄)) (sym (tagr4 s))) NODEv)
                        (csymᵀ (red→≅ᵀ (⟶ᵀ*-IMu (⟶*-pairˡ (step (βfst _ _) done)))))))

  ------------------------------------------------------------------------
  -- 2. ONE SORT'S METHODS, and the whole signature's.
  ------------------------------------------------------------------------

  mTs : {c : ℕ} → Shapes c → ℕ → Cons (Γ ∙) c
  mTs []ˢʰ         k = []
  mTs (sh ∷ˢʰ shs) k = mT sh k ∷ mTs shs (suc k)

  sortMs : {m : ℕ} → Sig m → Cons Γ m
  sortMs []ᵍ         = []
  sortMs (shs ∷ᵍ sg') = lam (methAt (mTs shs zero)) ∷ sortMs sg'

  private
    -- a shape's method, typed: the variable, or a fields row
    ⊢mT : {Γ : Ctx} {s k c : ℕ} {shs : Shapes c} {sh : Shape} → ShOK n sh → NthG sg s shs → NthSh shs k sh →
          (Γ ▹ El ⌜Nat⌝) ⊢ mT sh k ∷ MethKAt (renTm vs (SI n)) (renTm vs (SD sg)) (wk1M TM) (ιₛ s)
                                             (subTm (σₛ s) ⌜ tel sh (var vz) ⌝ᵗ) k
    ⊢mT (fᵒʰ []ᶠ)       ng nh = ⊢mT-f []ᶠ ng nh
    ⊢mT (fᵒʰ (f ∷ᶠ fs)) ng nh = ⊢mT-f (f ∷ᶠ fs) ng nh
    ⊢mT vᵒʰ             ng nh = ⊢mTv ng nh

    perT : {Γ : Ctx} {s c c' k : ℕ} {shsAll : Shapes c} {shs : Shapes c'} →
           NthG sg s shsAll → ShsOK n shs →
           ({j : ℕ} {sh : Shape} → NthSh shs j sh → NthSh shsAll (j +' k) sh) →
           PerKAt (Γ ▹ El ⌜Nat⌝) (renTm vs (SI n)) (renTm vs (SD sg)) (wk1M TM) (ιₛ s)
                  (selF (subC (σₛ s) ⌜ tels shsAll ⌝ₛ)) k (mTs shs k)
    perT ng []ᵒˢ look = []ₐ
    perT {s = s} ng (shok ∷ᵒˢ oks) look =
      (selF-β (nth-sub (σₛ s) (nth-⌜⌝ (nth-tels (look nthʰ-z)))) , ⊢mT shok ng (look nthʰ-z))
      ∷ₐ perT ng oks (λ n' → look (nthʰ-s n'))

    perS : {Γ : Ctx} {m s₀ : ℕ} {sg' : Sig m} →
           SigOK n sg' → ({j c : ℕ} {shs : Shapes c} → NthG sg' j shs → NthG sg (j +' s₀) shs) →
           PerS Γ (SortT (SI n) (SD sg) TM ⌜Nat⌝) s₀ (sortMs sg')
    perS []ᵒᵍ look = []ₚ
    perS {Γ = Γ} (oks ∷ᵒᵍ okss) look =
      ⊢sortMeth ⊢⌜Nat⌝ (allSD ⊢SI (sigOK ok)) ⊢TM (nth-⌜⌝ₛₛ (nth-stels (look nthᵍ-z)))
                (perT (look nthᵍ-z) oks (λ {j} n' → subst (λ m → NthSh _ m _) (sym (+'-zero j)) n'))
      ∷ₚ perS okss (λ n' → look (nthᵍ-s n'))

  ------------------------------------------------------------------------
  -- 3. ★★★ THE TRAVERSAL.
  ------------------------------------------------------------------------

  TRAVM : RTm Γ
  TRAVM = methAt (sortMs sg)

  ⊢TRAVM : {Γ : Ctx} → Γ ⊢ TRAVM ∷ MethTy (SI n) (SD sg) TM
  ⊢TRAVM = ⊢methₛ ⊢⌜Nat⌝ (⊢SD ok) ⊢TM (perS ok (λ {j} n' → subst (λ m → NthG _ m _) (sym (+'-zero j)) n'))

  -- `t : Syn s d` rebuilt at depth `e` through `f : Fin d → V e`
  trav : ℕ → RTm Γ → RTm Γ → RTm Γ → RTm Γ → RTm Γ
  trav s d t e f = app (app (ielim (SD sg) (pair (tag s) d) TRAVM t) e) f

  ⊢trav : {Γ : Ctx} {s : ℕ} {d t e f : RTm ⌊ Γ ⌋} → Lt s n →
          Γ ⊢ d ∷ El ⌜Nat⌝ → Γ ⊢ t ∷ SK sg s d → Γ ⊢ e ∷ El ⌜Nat⌝ → Γ ⊢ f ∷ Env d e →
          Γ ⊢ trav s d t e f ∷ SK sg s e
  ⊢trav {s = s} {d = d} lt dd dt de df =
    ⊢conv (⊢TM· (⊢ielim ⊢SI (⊢SD ok) ⊢TM ⊢TRAVM (⊢ix lt dd) dt) de
                (⊢conv df (csymᵀ (red→≅ᵀ (⟶ᵀ*-Πˡ (⟶ᵀ*-IMu (step (βsnd _ _) done)))))))
          (red→≅ᵀ (⟶ᵀ*-IMu (⟶*-pairˡ (step (βfst _ _) done))))
