------------------------------------------------------------------------
-- OCP-0009 · Lib — ★ SUBSTITUTION of a `Lib/Syn` syntax: the traversal at
-- the kit whose values are TERMS of the variable sort.
--
--     WK = weaken (`Lib/SynRen`)   V0 = the variable node `var fzero`
--     NODE e t = t                 (a variable node BECOMES its value)
--
-- and the environment of `single u`:
--
--     SINGLE d u = λ x. case x of fzero ↦ u ; fsuc y ↦ var y
--
-- `--safe`, ZERO axioms.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Lib.SynSub where

open import normalizer.Syntax.Types using ( _≡_; refl; sym; trans; cong; cong₂; subst; _,_ )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax hiding ( Fin )
open import DirectedHoTT.Spec.Typing hiding ( _×_; _,,_ )
open import DirectedHoTT.Metatheory.RedCong using ( red→≅ᵀ; ⟶ᵀ*-El )
open import DirectedHoTT.Metatheory.TySub using ( ⊢wk; ⊢-cast; wk-cancel-tm )
open import DirectedHoTT.Metatheory.Premises using ( mot-ren )
open import DirectedHoTT.Lib.Sugar using ( Cons; []; _∷_; conₗ; tag; Lt; nth-z; nth-s; []ᵈ; selF; subC )
open import DirectedHoTT.Lib.Tel
open import DirectedHoTT.Lib.TelAt using ( ⊢payAt )
open import DirectedHoTT.Lib.MethAt
open import DirectedHoTT.Lib.NatFib
open import DirectedHoTT.Lib.FinFam
open import DirectedHoTT.Lib.Syn
open import DirectedHoTT.Lib.SynTrav
open import DirectedHoTT.Lib.SynTravM
open import DirectedHoTT.Lib.SynRen

private
  variable
    Γ : Cx
    n c : ℕ

module Sub {sg : Sig n} (ok : SigOK n sg) {v kv : ℕ} {shs : Shapes c}
           (ngv : NthG sg v shs) (nhv : NthSh shs kv vʰ) (vok : VarsAt sg v) where

  private
    module R = Ren ok ngv nhv vok

  VFs : RTm Γ
  VFs = lam (⌜IMu⌝ (SI n) (SD sg) (pair (tag v) (var vz)))

  VFs-sub : {Γ Δ : Cx} (σ : Sub Γ Δ) → subTm σ (VFs {Γ}) ≡ VFs {Δ}
  VFs-sub σ = cong lam (cong₂ (λ D t → ⌜IMu⌝ (SI n) D (pair t (var vz))) (SD-sub (extS σ) sg) (tag-sub (extS σ) v))

  -- a value bound by a binder, seen from under it
  VatR : {Γ : Cx} (e : RTm Γ) → renTy vs (Vat (VFs {Γ}) e) ≡ Vat VFs (renTm vs e)
  VatR e = trans (sym (subTy-var vs (Vat VFs e)))
                 (cong (λ X → El (app X (subTm ⟨ vs ⟩ᵣ e))) (VFs-sub ⟨ vs ⟩ᵣ))
           ◾ cong (λ z → El (app VFs z)) (subTm-var vs e)
    where
      open import DirectedHoTT.Metatheory.Fundamental.Syntactic using ( ⟨_⟩ᵣ; subTy-var; subTm-var )
      _◾_ : {A : Set} {a b c : A} → a ≡ b → b ≡ c → a ≡ c
      _◾_ = trans

  hereV : {Γ : Ctx} {e : RTm ⌊ Γ ⌋} → (Γ ▹ Vat VFs e) ⊢ var vz ∷ Vat VFs (renTm vs e)
  hereV {e = e} = ⊢-cast (VatR e) (⊢var here)

  -- a value IS a term of the variable sort
  toSK : {Γ : Ctx} {e t : RTm ⌊ Γ ⌋} → Γ ⊢ t ∷ Vat VFs e → Γ ⊢ t ∷ SK sg v e
  toSK {e = e} dt =
    ⊢-cast (cong₂ (λ D x → IMu (SI n) D (pair x e)) (SD-sub (single e) sg) (tag-sub (single e) v))
      (⊢conv dt (ctrnᵀ (credᵀ (ξ-El (β _ e))) (credᵀ El-⌜IMu⌝)))

  fromSK : {Γ : Ctx} {e t : RTm ⌊ Γ ⌋} → Γ ⊢ t ∷ SK sg v e → Γ ⊢ t ∷ Vat VFs e
  fromSK {e = e} dt =
    ⊢conv (⊢-cast (sym (cong₂ (λ D x → IMu (SI n) D (pair x e)) (SD-sub (single e) sg) (tag-sub (single e) v))) dt)
          (csymᵀ (ctrnᵀ (credᵀ (ξ-El (β _ e))) (credᵀ El-⌜IMu⌝)))

  -- the variable node at `x : Fin e`
  vnode : RTm Γ → RTm Γ
  vnode x = conₗ kv (pair x unit)

  ⊢vnode : {Γ : Ctx} {e x : RTm ⌊ Γ ⌋} → Γ ⊢ e ∷ El ⌜Nat⌝ → Γ ⊢ x ∷ FinI e → Γ ⊢ vnode x ∷ SK sg v e
  ⊢vnode de dx = ⊢conSyn ok ngv nhv de (a-v dx)

  subKit : Kit n sg
  subKit = record
    { vsort = v
    ; VF    = VFs
    ; WK    = lam (lam (R.wk v (var (vs vz)) (var vz)))
    ; V0    = lam (vnode ffz)
    ; NODE  = lam (lam (var vz))
    ; VF-sub = VFs-sub
    ; ⊢VF   = ⊢VFs
    ; ⊢WK   = ⊢lam (ty-El ⊢⌜Nat⌝) (⊢lam (ty-El (⊢app ⊢VFs (⊢var here)))
                 (fromSK (R.⊢wkS lt (⊢var (there here)) (toSK hereV))))
    ; ⊢V0   = ⊢lam (ty-El ⊢⌜Nat⌝) (fromSK (⊢vnode (⊢isuc (⊢var here)) (⊢ffz (⊢var here))))
    ; ⊢NODE = ⊢lam (ty-El ⊢⌜Nat⌝) (⊢lam (ty-El (⊢app ⊢VFs (⊢var here))) (toSK hereV))
    }
    where
      lt = nthG-lt ngv
      ⊢VFs : {Γ : Ctx} → Γ ⊢ VFs ∷ Π (El ⌜Nat⌝) U
      ⊢VFs = ⊢lam (ty-El ⊢⌜Nat⌝) (⊢⌜IMu⌝ ⊢SI (⊢SD ok) (⊢ix lt (⊢var here)))

  open TravM ok subKit vok public
  open Trav ok subKit using ( Env; Env-ren; Vat-sub; predT; ⊢predT; ty-Vat; ty-Env ) public

  ------------------------------------------------------------------------
  -- ★ `single u`: SINGLE d u = λ x. case x of fzero ↦ u ; fsuc y ↦ var y
  --   (a case on the fibred `Fin`, `u` passed as an argument so the
  --   method is closed — as `LIFT`'s environment is)
  ------------------------------------------------------------------------

  -- the case's motive:  M(i, x) = V (pred i) → V (pred i)
  SMot : RTy ((Γ ∙) ∙)
  SMot = Π (Vat VFs (predT (var (vs vz)))) (Vat VFs (predT (var (vs (vs vz)))))

  SMot-sub : {Δ : Cx} (τ : Sub ((Γ ∙) ∙) Δ) →
             subTy τ SMot ≡ Π (Vat VFs (predT (τ (vs vz)))) (Vat VFs (predT (renTm vs (τ (vs vz)))))
  SMot-sub τ = cong₂ Π (Vat-sub τ (predT (var (vs vz)))) (Vat-sub (extS τ) (predT (var (vs (vs vz)))))

  -- at `suc m`: fzero ↦ λ u. u ; fsuc y ↦ λ u. var y
  sz ss : RTm (Γ ∙)
  sz = lam (lam (lam (var vz)))
  ss = lam (lam (lam (vnode (fst (var (vs (vs vz)))))))

  SM : RTm Γ
  SM = methN (methAt []) (methAt (sz ∷ ss ∷ []))

  private
    bodyTyS : (k : ℕ) → subTy (atS (nsuc (var vz)) (conₗ k (var (vs vz)))) (wk1M (SMot {Γ}))
              ≡ Π (Vat VFs (predT (nsuc (var (vs (vs vz)))))) (Vat VFs (predT (nsuc (var (vs (vs (vs vz)))))))
    bodyTyS k = trans (subTy-renTy SMot) (SMot-sub _)

  ⊢SM : {Γ : Ctx} → Γ ⊢ SM ∷ MethTy ⌜Nat⌝ FinD SMot
  ⊢SM {Γ} = ⊢methN ⊢FinD dM (⊢caseZ []ᵈ dS dM []ₐ) (⊢caseS []ᵈ dS dM perS)
    where
      dS = allD (⊢wk ⊢⌜Nat⌝) (FinOK {Γ})
      dM : motCtx Γ ⌜Nat⌝ FinD ⊢ty SMot
      dM = ty-Π (ty-Vat (⊢predT (⊢var (there here)))) (ty-Vat (⊢predT (⊢var (there (there here)))))
      perS : PerKAt (Γ ▹ El ⌜Nat⌝) ⌜Nat⌝ (renTm vs FinD) (wk1M SMot) (nsuc (var vz))
                    (selF (subC τS ⌜ FinTs ⌝ₛ)) zero (sz ∷ ss ∷ [])
      perS = entN {Ts = FinTs} {T = fzeroT} []ᵈ FinOK dM nthᵗ-z
               (⊢-cast (sym (bodyTyS zero))
                 (⊢lam (ty-Vat (⊢predT (⊢isuc (⊢var (there (there here)))))) hereV))
          ∷ₐ entN {Ts = FinTs} {T = fsucT} []ᵈ FinOK dM (nthᵗ-s nthᵗ-z)
               (⊢-cast (sym (bodyTyS (suc zero)))
                 (⊢lam (ty-Vat (⊢predT (⊢isuc (⊢var (there (there here))))))
                   (⊢conv (fromSK (⊢vnode (⊢wk (⊢var (there (there here))))
                                          (⊢wk (⊢fst (⊢payAt {I = ⌜Nat⌝} {D = renTm vs FinD} {M = wk1M SMot}
                                                             {σ = τS} {T = fsucT})))))
                          (csymᵀ (credᵀ (ξ-El (ξ-appʳ (natrec-suc _ _ _))))))))
          ∷ₐ []ₐ

  SINGLE : RTm Γ
  SINGLE = lam (lam (lam (app (ielim FinD (nsuc (var (vs (vs vz)))) SM (var vz)) (var (vs vz)))))

  -- ★ `SINGLE d u : Fin (suc d) → V d`
  ⊢SINGLE : {Γ : Ctx} → Γ ⊢ SINGLE ∷ Π (El ⌜Nat⌝) (Π (Vat VFs (var vz)) (Env (nsuc (var (vs vz))) (var (vs vz))))
  ⊢SINGLE {Γ} = ⊢lam (ty-El ⊢⌜Nat⌝) (⊢lam (ty-Vat (⊢var here))
                  (⊢lam (ty-IMu ⊢⌜Nat⌝ ⊢FinD (⊢isuc (⊢var (there here)))) body))
    where
      Γ3 : Ctx
      Γ3 = ((Γ ▹ El ⌜Nat⌝) ▹ Vat VFs (var vz)) ▹ FinI (nsuc (var (vs vz)))
      d3 : RTm ⌊ Γ3 ⌋
      d3 = var (vs (vs vz))
      τ3 : Sub ((⌊ Γ3 ⌋ ∙) ∙) ⌊ Γ3 ⌋
      τ3 = single (var vz) ∘ₛ extS (single (nsuc d3))
      d1 : Γ3 ⊢ ielim FinD (nsuc d3) SM (var vz) ∷ iinst (nsuc d3) (var vz) SMot
      d1 = ⊢ielim ⊢⌜Nat⌝ ⊢FinD (ty-Π (ty-Vat (⊢predT (⊢var (there here)))) (ty-Vat (⊢predT (⊢var (there (there here))))))
                  ⊢SM (⊢isuc (⊢var (there (there here)))) (⊢var here)
      d2 : Γ3 ⊢ ielim FinD (nsuc d3) SM (var vz) ∷ Π (Vat VFs (predT (nsuc d3))) (Vat VFs (predT (nsuc (var (vs (vs (vs vz)))))))
      d2 = ⊢-cast (trans (subTy-subTy SMot) (SMot-sub τ3)) d1
      du : Γ3 ⊢ var (vs vz) ∷ Vat VFs (predT (nsuc d3))
      du = ⊢conv (⊢-cast (trans (cong (renTy vs) (VatR (var vz))) (VatR (var (vs vz)))) (⊢var (there here)))
                 (csymᵀ (credᵀ (ξ-El (ξ-appʳ (natrec-suc _ _ _)))))
      body : Γ3 ⊢ app (ielim FinD (nsuc d3) SM (var vz)) (var (vs vz)) ∷ Vat VFs d3
      body = ⊢conv (⊢-cast (Vat-sub (single (var (vs vz))) (predT (nsuc (var (vs (vs (vs vz))))))) (⊢app d2 du))
                   (credᵀ (ξ-El (ξ-appʳ (natrec-suc _ _ _))))

  ------------------------------------------------------------------------
  -- ★ SUBSTITUTION, and `single u` applied: `t[u/0]`
  ------------------------------------------------------------------------

  sub : ℕ → RTm Γ → RTm Γ → RTm Γ → RTm Γ → RTm Γ
  sub = trav

  sub0 : ℕ → RTm Γ → RTm Γ → RTm Γ → RTm Γ
  sub0 s d t u = trav s (nsuc d) t d (app (app SINGLE d) u)

  ⊢sub0 : {Γ : Ctx} {s : ℕ} {d t u : RTm ⌊ Γ ⌋} → Lt s n →
          Γ ⊢ d ∷ El ⌜Nat⌝ → Γ ⊢ t ∷ SK sg s (nsuc d) → Γ ⊢ u ∷ SK sg v d → Γ ⊢ sub0 s d t u ∷ SK sg s d
  ⊢sub0 {d = d} {u = u} lt dd dt du =
    ⊢trav lt (⊢isuc dd) dt dd
      (⊢-cast eqE (⊢app (⊢-cast (cong (λ X → Π X (subTy (extS (single d)) (Env (nsuc (var (vs vz))) (var (vs vz)))))
                                      (Vat-sub (single d) (var vz)))
                                (⊢app ⊢SINGLE dd))
                        (fromSK du)))
    where
      eqE : subTy (single u) (subTy (extS (single d)) (Env (nsuc (var (vs vz))) (var (vs vz)))) ≡ Env (nsuc d) d
      eqE = trans (cong (subTy (single u)) (Env-sub' (extS (single d)) (nsuc (var (vs vz))) (var (vs vz))))
              (trans (Env-sub' (single u) (nsuc (renTm vs d)) (renTm vs d))
                     (cong₂ (λ a b → Env (nsuc a) b) (wk-cancel-tm u d) (wk-cancel-tm u d)))
        where open Trav ok subKit using () renaming ( Env-sub to Env-sub' )
