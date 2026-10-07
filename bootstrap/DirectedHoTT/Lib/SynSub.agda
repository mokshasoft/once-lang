-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- OCP-0009 · Lib — ★ SUBSTITUTION of a `Lib/Syn` syntax: the traversal at
-- the kit whose values are TERMS of the variable sort.
--
--     WK = weaken (`Lib/SynRen`)   V0 = the variable node `var fzero`
--     NODE e t = t                 (a variable node BECOMES its value)
--
-- and the environments of the σ-calculus: the identity `IDS d = λ x. var x`
-- and `single u = (IDS , u)` — `CONS` (`Lib/SynTrav`) applied:
--
--     SINGLE d u = CONS d d u (IDS d)
--
-- `--safe`, ZERO axioms.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
open import DirectedHoTT.Spec.Syntax using ( KSig; _<ˢ_; _<ˢ?_ )
open import Agda.Builtin.Nat using () renaming ( Nat to ℕ )
import DirectedHoTT.Spec.Typing as Ty
module DirectedHoTT.Lib.SynSub (𝒮 : KSig) (𝓃 : ℕ) (ok : Ty.EntriesOK 𝒮 𝓃) where

open import normalizer.Syntax.Types using ( _≡_; refl; sym; trans; cong; cong₂; subst; _,_ )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax
open import DirectedHoTT.Spec.Typing 𝒮 𝓃 hiding ( _×_; _,,_ )
open import DirectedHoTT.Metatheory.RedCong 𝒮 using ( red→≅ᵀ; ⟶ᵀ*-El )
open import DirectedHoTT.Metatheory.TySub 𝒮 𝓃 using ( ⊢wk; ⊢-cast; wk-cancel-tm )
open import DirectedHoTT.Metatheory.Premises 𝒮 𝓃 using ( mot-ren )
open import DirectedHoTT.Lib.Sugar 𝒮 𝓃 ok using ( Cons; []; _∷_; conₗ; tag; Lt; nth-z; nth-s; []ᵈ; selF; subC )
open import DirectedHoTT.Lib.Tel 𝒮 𝓃 ok
open import DirectedHoTT.Lib.TelAt 𝒮 𝓃 ok using ( ⊢payAt )
open import DirectedHoTT.Lib.MethAt 𝒮 𝓃 ok
open import DirectedHoTT.Lib.NatFib 𝒮 𝓃 ok
open import DirectedHoTT.Lib.NatCode 𝒮 𝓃
open import DirectedHoTT.Lib.Syn 𝒮 𝓃 ok
open import DirectedHoTT.Lib.SynTrav 𝒮 𝓃 ok
open import DirectedHoTT.Lib.SynTravM 𝒮 𝓃 ok
open import DirectedHoTT.Lib.SynRen 𝒮 𝓃 ok
import DirectedHoTT.Metatheory.Fundamental.Syntactic 𝒮 as ᴵSyntactic

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
  VFs-sub σ = cong lam (cong₃ (λ I D t → ⌜IMu⌝ I D (pair t (var vz))) (SI-sub (extS σ) n) (SD-sub (extS σ) sg) (tag-sub (extS σ) v))

  -- a value bound by a binder, seen from under it
  VatR : {Γ : Cx} (e : RTm Γ) → renTy vs (Vat (VFs {Γ}) e) ≡ Vat VFs (renTm vs e)
  VatR e = trans (sym (subTy-var vs (Vat VFs e)))
                 (cong (λ X → El (app X (subTm ⟨ vs ⟩ᵣ e))) (VFs-sub ⟨ vs ⟩ᵣ))
           ◾ cong (λ z → El (app VFs z)) (subTm-var vs e)
    where
      open ᴵSyntactic using ( ⟨_⟩ᵣ; subTy-var; subTm-var )
      _◾_ : {A : Set} {a b c : A} → a ≡ b → b ≡ c → a ≡ c
      _◾_ = trans

  hereV : {Γ : Ctx} {e : RTm ⌊ Γ ⌋} → (Γ ▹ Vat VFs e) ⊢ var vz ∷ Vat VFs (renTm vs e)
  hereV {e = e} = ⊢-cast (VatR e) (⊢var here)

  -- a value IS a term of the variable sort
  toSK : {Γ : Ctx} {e t : RTm ⌊ Γ ⌋} → Γ ⊢ t ∷ Vat VFs e → Γ ⊢ t ∷ SK sg v e
  toSK {e = e} dt = ⊢IMu→SK {sg = sg} {s = v} {d = e} (
    ⊢-cast (cong₃ (λ I D x → IMu I D (pair x e)) (SI-sub (single e) n) (SD-sub (single e) sg) (tag-sub (single e) v))
      (⊢conv dt (ctrnᵀ (credᵀ (ξ-El (β _ e))) (credᵀ El-⌜IMu⌝))))

  fromSK : {Γ : Ctx} {e t : RTm ⌊ Γ ⌋} → Γ ⊢ t ∷ SK sg v e → Γ ⊢ t ∷ Vat VFs e
  fromSK {e = e} dt =
    ⊢conv (⊢-cast (sym (cong₃ (λ I D x → IMu I D (pair x e)) (SI-sub (single e) n) (SD-sub (single e) sg) (tag-sub (single e) v))) (⊢SK→IMu {sg = sg} {s = v} {d = e} dt))
          (csymᵀ (ctrnᵀ (credᵀ (ξ-El (β _ e))) (credᵀ El-⌜IMu⌝)))

  -- the variable node at `x : Fin e`
  vnode : RTm Γ → RTm Γ
  vnode x = conₗ kv (pair x unit)

  ⊢vnode : {Γ : Ctx} {e x : RTm ⌊ Γ ⌋} → Γ ⊢ e ∷ El ⌜Nat⌝ → Γ ⊢ x ∷ Fin e → Γ ⊢ vnode x ∷ SK sg v e
  ⊢vnode de dx = ⊢conSyn ok ngv nhv de (a-v dx)

  subKit : Kit n sg
  subKit = record
    { vsort = v
    ; VF    = VFs
    ; WK    = lam (lam (R.wk v (var (vs vz)) (var vz)))
    ; V0    = lam (vnode fzero)
    ; NODE  = lam (lam (var vz))
    ; VF-sub = VFs-sub
    ; ⊢VF   = ⊢VFs
    ; ⊢WK   = ⊢lam (ty-El ⊢⌜Nat⌝) (⊢lam (ty-El (⊢app ⊢VFs (⊢var here)))
                 (fromSK (R.⊢wkS lt (⊢var (there here)) (toSK hereV))))
    ; ⊢V0   = ⊢lam (ty-El ⊢⌜Nat⌝) (fromSK (⊢vnode (⊢isuc (⊢var here)) (⊢fzero (fromI (⊢var here)))))
    ; ⊢NODE = ⊢lam (ty-El ⊢⌜Nat⌝) (⊢lam (ty-El (⊢app ⊢VFs (⊢var here))) (toSK hereV))
    }
    where
      lt = nthG-lt ngv
      ⊢VFs : {Γ : Ctx} → Γ ⊢ VFs ∷ Π (El ⌜Nat⌝) U
      ⊢VFs = ⊢lam (ty-El ⊢⌜Nat⌝) (⊢⌜IMu⌝ ⊢SI (⊢SD ok) (⊢ix lt (⊢var here)))

  open TravM ok subKit vok public
  open Trav ok subKit using ( Env; Env-ren; Vat-sub; predT; ⊢predT; ty-Vat; ty-Env; CONS; ⊢CONS· ) public

  ------------------------------------------------------------------------
  -- ★ THE IDENTITY ENVIRONMENT, and `single u = (id , u)`
  ------------------------------------------------------------------------

  -- IDS = λ x. var x : Env d d
  IDS : RTm Γ
  IDS = lam (vnode (var vz))

  ⊢IDS : {Γ : Ctx} {d : RTm ⌊ Γ ⌋} → Γ ⊢ d ∷ El ⌜Nat⌝ → Γ ⊢ IDS ∷ Env d d
  ⊢IDS dd = ⊢lam (ty-Fin (fromI dd)) (fromSK (⊢vnode (⊢wk dd) (⊢var here)))

  SINGLE : RTm Γ
  SINGLE = lam (lam (app (app (app (app CONS (var (vs vz))) (var (vs vz))) (var vz)) IDS))

  -- ★ `SINGLE d u : Fin (suc d) → V d`
  ⊢SINGLE : {Γ : Ctx} → Γ ⊢ SINGLE ∷ Π (El ⌜Nat⌝) (Π (Vat VFs (var vz)) (Env (nsuc (var (vs vz))) (var (vs vz))))
  ⊢SINGLE {Γ} = ⊢lam (ty-El ⊢⌜Nat⌝) (⊢lam (ty-Vat (⊢var here)) body)
    where
      Γ2 : Ctx
      Γ2 = (Γ ▹ El ⌜Nat⌝) ▹ Vat VFs (var vz)
      d2 : RTm ⌊ Γ2 ⌋
      d2 = var (vs vz)
      dd2 : Γ2 ⊢ d2 ∷ El ⌜Nat⌝
      dd2 = ⊢var (there here)
      body : Γ2 ⊢ app (app (app (app CONS d2) d2) (var vz)) IDS ∷ Env (nsuc d2) d2
      body = ⊢CONS· {Γ2} {d2} {d2} {var vz} {IDS} dd2 dd2 hereV (⊢IDS dd2)

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
