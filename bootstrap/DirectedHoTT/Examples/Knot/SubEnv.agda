-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- OCP-0009 · KNOT — the kernel's NAMED SUBSTITUTIONS, object-level: the
-- environments `Spec/Typing` uses in its rules (`nrs`, `pairS`, `fsucS`,
-- `methS`, `iinst`'s double instantiation, `MethTy`'s double lift), each
-- a `CONS`/`LIFT` of `Lib/SynSub`'s σ-calculus, and the types they build.
--
-- ★ Every operation is OPAQUE (`context-form-mismatch-opaque`): its body
--   is a traversal carrying the substitution method, so a transparent one
--   is compared by normalisation whenever two syntactic forms of one
--   context meet.  The interface is its typing and its closedness.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Knot.SubEnv where

open import normalizer.Syntax.Types using ( _≡_; refl; sym; trans; cong; cong₂ )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax hiding ( Fin )
open import DirectedHoTT.Spec.Typing hiding ( _×_; _,,_ )
open import DirectedHoTT.Lib.Sugar using ( Lt; lt-z; lt-s; v₀; _,ₚ_ )
open import DirectedHoTT.Lib.FinFam using ( FinI; FinD; ⊢FinD; ffz; ffs; ⊢ffz; ⊢ffs; ⊢isuc )
open import DirectedHoTT.Lib.Syn
open import DirectedHoTT.Metatheory.TySub using ( ⊢wk )
open import DirectedHoTT.Examples.Knot.Sig
open import DirectedHoTT.Examples.Knot.Ctors
open import DirectedHoTT.Examples.Knot.Ren using ( wk; ⊢wkS; wk-sub )
open import DirectedHoTT.Examples.Knot.Sub
open import DirectedHoTT.Lib.SynTrav using ( module Trav )
open Trav KOK subKit using ( LIFT; ⊢LIFT· )

private
  variable
    Γ Δ Θ : Cx

  app⁴ : RTm Γ → RTm Γ → RTm Γ → RTm Γ → RTm Γ → RTm Γ
  app⁴ f a b c d = app (app (app (app f a) b) c) d

  app³ : RTm Γ → RTm Γ → RTm Γ → RTm Γ → RTm Γ
  app³ f a b c = app (app (app f a) b) c

------------------------------------------------------------------------
-- 1. The environments.
------------------------------------------------------------------------

-- `vs^k` : Env d (d + k)
WK1 WK2 WK3 : RTm Γ
WK1 = lam (vnode (ffs v₀))
WK2 = lam (vnode (ffs (ffs v₀)))
WK3 = lam (vnode (ffs (ffs (ffs v₀))))

module _ {Ξ : Ctx} {d : RTm ⌊ Ξ ⌋} (dd : Ξ ⊢ d ∷ El ⌜Nat⌝) where
  private
    dd' : (Ξ ▹ FinI d) ⊢ renTm vs d ∷ El ⌜Nat⌝
    dd' = ⊢wk dd
  ⊢WK1 : Ξ ⊢ WK1 ∷ Env d (nsuc d)
  ⊢WK1 = ⊢lam (ty-IMu ⊢⌜Nat⌝ ⊢FinD dd) (fromSK (⊢vnode (⊢isuc dd') (⊢ffs dd' (⊢var here))))
  ⊢WK2 : Ξ ⊢ WK2 ∷ Env d (nsuc (nsuc d))
  ⊢WK2 = ⊢lam (ty-IMu ⊢⌜Nat⌝ ⊢FinD dd) (fromSK (⊢vnode (⊢isuc (⊢isuc dd')) (⊢ffs (⊢isuc dd') (⊢ffs dd' (⊢var here)))))
  ⊢WK3 : Ξ ⊢ WK3 ∷ Env d (nsuc (nsuc (nsuc d)))
  ⊢WK3 = ⊢lam (ty-IMu ⊢⌜Nat⌝ ⊢FinD dd)
               (fromSK (⊢vnode (⊢isuc (⊢isuc (⊢isuc dd'))) (⊢ffs (⊢isuc (⊢isuc dd')) (⊢ffs (⊢isuc dd') (⊢ffs dd' (⊢var here))))))

-- the variables `0 , 1 , 2` at depth `d + k`
v0 v1 v2 : RTm Γ
v0 = kvar ffz
v1 = kvar (ffs ffz)
v2 = kvar (ffs (ffs ffz))

module _ {Ξ : Ctx} {d : RTm ⌊ Ξ ⌋} (dd : Ξ ⊢ d ∷ El ⌜Nat⌝) where
  ⊢v0 : Ξ ⊢ v0 ∷ K 1 (nsuc d)
  ⊢v0 = ⊢kvar (⊢isuc dd) (⊢ffz dd)
  ⊢v1 : Ξ ⊢ v1 ∷ K 1 (nsuc (nsuc d))
  ⊢v1 = ⊢kvar (⊢isuc (⊢isuc dd)) (⊢ffs (⊢isuc dd) (⊢ffz dd))
  ⊢v2 : Ξ ⊢ v2 ∷ K 1 (nsuc (nsuc (nsuc d)))
  ⊢v2 = ⊢kvar (⊢isuc (⊢isuc (⊢isuc dd))) (⊢ffs (⊢isuc (⊢isuc dd)) (⊢ffs (⊢isuc dd) (⊢ffz dd)))

-- nrs    : Env (j+1) (j+2)   0 ↦ suc 1 , x+1 ↦ x+2
-- pairS  : Env (j+1) (j+2)   0 ↦ (1 , 0) , x+1 ↦ x+2
-- fsucS  : Env (j+1) (j+1)   0 ↦ fsuc 0 , x+1 ↦ x+1
-- methS  : Env (j+2) (j+3)   0 ↦ con 1 , 1 ↦ 2 , x+2 ↦ x+3
-- inst2  : Env (j+2) j       0 ↦ t , 1 ↦ i , x+2 ↦ x
-- lift2  : Env (j+2) (j+4)   0 ↦ 0 , 1 ↦ 1 , x+2 ↦ x+4
ENRS EPAIR EFSUC EMETH ELIFT2 : RTm Γ → RTm Γ
ENRS j = app⁴ CONS (nsuc (nsuc j)) j (knsuc v1) WK2
EPAIR j = app⁴ CONS (nsuc (nsuc j)) j (kpair v1 v0) WK2
EFSUC j = app⁴ CONS (nsuc j) j (kfsuc v0) WK1
EMETH j = app⁴ CONS (nsuc (nsuc (nsuc j))) (nsuc j) (kcon v1) (app⁴ CONS (nsuc (nsuc (nsuc j))) j v2 WK3)
ELIFT2 j = app³ LIFT (nsuc (nsuc (nsuc j))) (nsuc j) (app³ LIFT (nsuc (nsuc j)) j WK2)

EINST : RTm Γ → RTm Γ → RTm Γ → RTm Γ
EINST j i t = app⁴ CONS j (nsuc j) t (app⁴ CONS j j i IDS)

module _ {Ξ : Ctx} {j : RTm ⌊ Ξ ⌋} (dj : Ξ ⊢ j ∷ El ⌜Nat⌝) where
  private
    dj1 = ⊢isuc dj
    dj2 = ⊢isuc dj1
    dj3 = ⊢isuc dj2
  ⊢ENRS : Ξ ⊢ ENRS j ∷ Env (nsuc j) (nsuc (nsuc j))
  ⊢ENRS = ⊢CONS· dj2 dj (fromSK (⊢knsuc dj2 (⊢v1 dj))) (⊢WK2 dj)
  ⊢EPAIR : Ξ ⊢ EPAIR j ∷ Env (nsuc j) (nsuc (nsuc j))
  ⊢EPAIR = ⊢CONS· dj2 dj (fromSK (⊢kpair dj2 (⊢v1 dj) (⊢v0 dj1))) (⊢WK2 dj)
  ⊢EFSUC : Ξ ⊢ EFSUC j ∷ Env (nsuc j) (nsuc j)
  ⊢EFSUC = ⊢CONS· dj1 dj (fromSK (⊢kfsuc dj1 (⊢v0 dj))) (⊢WK1 dj)
  ⊢EMETH : Ξ ⊢ EMETH j ∷ Env (nsuc (nsuc j)) (nsuc (nsuc (nsuc j)))
  ⊢EMETH = ⊢CONS· dj3 dj1 (fromSK (⊢kcon dj3 (⊢v1 dj1))) (⊢CONS· dj3 dj (fromSK (⊢v2 dj)) (⊢WK3 dj))
  ⊢ELIFT2 : Ξ ⊢ ELIFT2 j ∷ Env (nsuc (nsuc j)) (nsuc (nsuc (nsuc (nsuc j))))
  ⊢ELIFT2 = ⊢LIFT· dj3 dj1 (⊢LIFT· dj2 dj (⊢WK2 dj))
  ⊢EINST : {i t : RTm ⌊ Ξ ⌋} → Ξ ⊢ i ∷ K 1 j → Ξ ⊢ t ∷ K 1 j → Ξ ⊢ EINST j i t ∷ Env (nsuc (nsuc j)) j
  ⊢EINST di dt = ⊢CONS· dj dj1 (fromSK dt) (⊢CONS· dj dj (fromSK di) (⊢IDS dj))

------------------------------------------------------------------------
-- 2. Closedness.
------------------------------------------------------------------------

private
  CONS-sub : (σ : Sub Δ Θ) → subTm σ (CONS {Δ}) ≡ CONS
  CONS-sub σ = refl

  LIFT-sub : (σ : Sub Δ Θ) → subTm σ (LIFT {Δ}) ≡ LIFT
  LIFT-sub σ = refl

  IDS-sub : (σ : Sub Δ Θ) → subTm σ (IDS {Δ}) ≡ IDS
  IDS-sub σ = refl

trav-sub : (σ : Sub Δ Θ) (s : ℕ) (d t e f : RTm Δ) → subTm σ (trav s d t e f) ≡ trav s (subTm σ d) (subTm σ t) (subTm σ e) (subTm σ f)
trav-sub σ s d t e f = c3 (SD-sub σ KSig) (tag-sub σ s) (TRAVMs-sub σ)
  where
    c3 : {D D' T T' M M' : RTm _} → D ≡ D' → T ≡ T' → M ≡ M' →
         app (app (ielim D (T ,ₚ (subTm σ d)) M (subTm σ t)) (subTm σ e)) (subTm σ f)
         ≡ app (app (ielim D' (T' ,ₚ (subTm σ d)) M' (subTm σ t)) (subTm σ e)) (subTm σ f)
    c3 refl refl refl = refl

ENRS-sub : (σ : Sub Δ Θ) (j : RTm Δ) → subTm σ (ENRS j) ≡ ENRS (subTm σ j)
ENRS-sub σ j = cong (λ C → app⁴ C (nsuc (nsuc (subTm σ j))) (subTm σ j) (knsuc v1) WK2) (CONS-sub σ)

EPAIR-sub : (σ : Sub Δ Θ) (j : RTm Δ) → subTm σ (EPAIR j) ≡ EPAIR (subTm σ j)
EPAIR-sub σ j = cong (λ C → app⁴ C (nsuc (nsuc (subTm σ j))) (subTm σ j) (kpair v1 v0) WK2) (CONS-sub σ)

EFSUC-sub : (σ : Sub Δ Θ) (j : RTm Δ) → subTm σ (EFSUC j) ≡ EFSUC (subTm σ j)
EFSUC-sub σ j = cong (λ C → app⁴ C (nsuc (subTm σ j)) (subTm σ j) (kfsuc v0) WK1) (CONS-sub σ)

EMETH-sub : (σ : Sub Δ Θ) (j : RTm Δ) → subTm σ (EMETH j) ≡ EMETH (subTm σ j)
EMETH-sub σ j = cong (λ C → app⁴ C (nsuc (nsuc (nsuc (subTm σ j)))) (nsuc (subTm σ j)) (kcon v1)
                                   (app⁴ C (nsuc (nsuc (nsuc (subTm σ j)))) (subTm σ j) v2 WK3)) (CONS-sub σ)

ELIFT2-sub : (σ : Sub Δ Θ) (j : RTm Δ) → subTm σ (ELIFT2 j) ≡ ELIFT2 (subTm σ j)
ELIFT2-sub σ j = cong (λ L → app³ L (nsuc (nsuc (nsuc (subTm σ j)))) (nsuc (subTm σ j)) (app³ L (nsuc (nsuc (subTm σ j))) (subTm σ j) WK2))
                      (LIFT-sub σ)

EINST-sub : (σ : Sub Δ Θ) (j i t : RTm Δ) → subTm σ (EINST j i t) ≡ EINST (subTm σ j) (subTm σ i) (subTm σ t)
EINST-sub σ j i t = cong₂ (λ C I → app⁴ C (subTm σ j) (nsuc (subTm σ j)) (subTm σ t) (app⁴ C (subTm σ j) (subTm σ j) (subTm σ i) I))
                          (CONS-sub σ) (IDS-sub σ)

------------------------------------------------------------------------
-- 3. ★ THE OPERATIONS (opaque), typed and closed.
------------------------------------------------------------------------

opaque
  -- M[nrs] (natrec's successor case), P[pairS] (psplit), P[fsucS] (fcase)
  nrsK pairSK fsucSK methSK lift2K : RTm Γ → RTm Γ → RTm Γ
  nrsK j M = trav 0 (nsuc j) M (nsuc (nsuc j)) (ENRS j)
  pairSK j P = trav 0 (nsuc j) P (nsuc (nsuc j)) (EPAIR j)
  fsucSK j P = trav 0 (nsuc j) P (nsuc j) (EFSUC j)
  methSK j M = trav 0 (nsuc (nsuc j)) M (nsuc (nsuc (nsuc j))) (EMETH j)
  lift2K j M = trav 0 (nsuc (nsuc j)) M (nsuc (nsuc (nsuc (nsuc j)))) (ELIFT2 j)

  -- iinst i t M
  iinstK : RTm Γ → RTm Γ → RTm Γ → RTm Γ → RTm Γ
  iinstK j i t M = trav 0 (nsuc (nsuc j)) M j (EINST j i t)

  ⊢nrsK : {Ξ : Ctx} {j M : RTm ⌊ Ξ ⌋} → Ξ ⊢ j ∷ El ⌜Nat⌝ → Ξ ⊢ M ∷ K 0 (nsuc j) → Ξ ⊢ nrsK j M ∷ K 0 (nsuc (nsuc j))
  ⊢nrsK dj dM = ⊢trav lt-z (⊢isuc dj) dM (⊢isuc (⊢isuc dj)) (⊢ENRS dj)
  ⊢pairSK : {Ξ : Ctx} {j P : RTm ⌊ Ξ ⌋} → Ξ ⊢ j ∷ El ⌜Nat⌝ → Ξ ⊢ P ∷ K 0 (nsuc j) → Ξ ⊢ pairSK j P ∷ K 0 (nsuc (nsuc j))
  ⊢pairSK dj dP = ⊢trav lt-z (⊢isuc dj) dP (⊢isuc (⊢isuc dj)) (⊢EPAIR dj)
  ⊢fsucSK : {Ξ : Ctx} {j P : RTm ⌊ Ξ ⌋} → Ξ ⊢ j ∷ El ⌜Nat⌝ → Ξ ⊢ P ∷ K 0 (nsuc j) → Ξ ⊢ fsucSK j P ∷ K 0 (nsuc j)
  ⊢fsucSK dj dP = ⊢trav lt-z (⊢isuc dj) dP (⊢isuc dj) (⊢EFSUC dj)
  ⊢methSK : {Ξ : Ctx} {j M : RTm ⌊ Ξ ⌋} → Ξ ⊢ j ∷ El ⌜Nat⌝ → Ξ ⊢ M ∷ K 0 (nsuc (nsuc j)) → Ξ ⊢ methSK j M ∷ K 0 (nsuc (nsuc (nsuc j)))
  ⊢methSK dj dM = ⊢trav lt-z (⊢isuc (⊢isuc dj)) dM (⊢isuc (⊢isuc (⊢isuc dj))) (⊢EMETH dj)
  ⊢lift2K : {Ξ : Ctx} {j M : RTm ⌊ Ξ ⌋} → Ξ ⊢ j ∷ El ⌜Nat⌝ → Ξ ⊢ M ∷ K 0 (nsuc (nsuc j)) → Ξ ⊢ lift2K j M ∷ K 0 (nsuc (nsuc (nsuc (nsuc j))))
  ⊢lift2K dj dM = ⊢trav lt-z (⊢isuc (⊢isuc dj)) dM (⊢isuc (⊢isuc (⊢isuc (⊢isuc dj)))) (⊢ELIFT2 dj)
  ⊢iinstK : {Ξ : Ctx} {j i t M : RTm ⌊ Ξ ⌋} → Ξ ⊢ j ∷ El ⌜Nat⌝ → Ξ ⊢ i ∷ K 1 j → Ξ ⊢ t ∷ K 1 j → Ξ ⊢ M ∷ K 0 (nsuc (nsuc j)) → Ξ ⊢ iinstK j i t M ∷ K 0 j
  ⊢iinstK dj di dt dM = ⊢trav lt-z (⊢isuc (⊢isuc dj)) dM dj (⊢EINST dj di dt)

opaque
  unfolding nrsK pairSK fsucSK methSK lift2K iinstK
  nrsK-sub : (σ : Sub Δ Θ) (j M : RTm Δ) → subTm σ (nrsK j M) ≡ nrsK (subTm σ j) (subTm σ M)
  nrsK-sub σ j M = trans (trav-sub σ 0 (nsuc j) M (nsuc (nsuc j)) (ENRS j))
                         (cong (trav 0 (nsuc (subTm σ j)) (subTm σ M) (nsuc (nsuc (subTm σ j)))) (ENRS-sub σ j))
  pairSK-sub : (σ : Sub Δ Θ) (j P : RTm Δ) → subTm σ (pairSK j P) ≡ pairSK (subTm σ j) (subTm σ P)
  pairSK-sub σ j P = trans (trav-sub σ 0 (nsuc j) P (nsuc (nsuc j)) (EPAIR j))
                           (cong (trav 0 (nsuc (subTm σ j)) (subTm σ P) (nsuc (nsuc (subTm σ j)))) (EPAIR-sub σ j))
  fsucSK-sub : (σ : Sub Δ Θ) (j P : RTm Δ) → subTm σ (fsucSK j P) ≡ fsucSK (subTm σ j) (subTm σ P)
  fsucSK-sub σ j P = trans (trav-sub σ 0 (nsuc j) P (nsuc j) (EFSUC j))
                           (cong (trav 0 (nsuc (subTm σ j)) (subTm σ P) (nsuc (subTm σ j))) (EFSUC-sub σ j))
  methSK-sub : (σ : Sub Δ Θ) (j M : RTm Δ) → subTm σ (methSK j M) ≡ methSK (subTm σ j) (subTm σ M)
  methSK-sub σ j M = trans (trav-sub σ 0 (nsuc (nsuc j)) M (nsuc (nsuc (nsuc j))) (EMETH j))
                           (cong (trav 0 (nsuc (nsuc (subTm σ j))) (subTm σ M) (nsuc (nsuc (nsuc (subTm σ j))))) (EMETH-sub σ j))
  lift2K-sub : (σ : Sub Δ Θ) (j M : RTm Δ) → subTm σ (lift2K j M) ≡ lift2K (subTm σ j) (subTm σ M)
  lift2K-sub σ j M = trans (trav-sub σ 0 (nsuc (nsuc j)) M (nsuc (nsuc (nsuc (nsuc j)))) (ELIFT2 j))
                           (cong (trav 0 (nsuc (nsuc (subTm σ j))) (subTm σ M) (nsuc (nsuc (nsuc (nsuc (subTm σ j)))))) (ELIFT2-sub σ j))
  iinstK-sub : (σ : Sub Δ Θ) (j i t M : RTm Δ) → subTm σ (iinstK j i t M) ≡ iinstK (subTm σ j) (subTm σ i) (subTm σ t) (subTm σ M)
  iinstK-sub σ j i t M = trans (trav-sub σ 0 (nsuc (nsuc j)) M j (EINST j i t))
                               (cong (trav 0 (nsuc (nsuc (subTm σ j))) (subTm σ M) (subTm σ j)) (EINST-sub σ j i t))

------------------------------------------------------------------------
-- 4. ★ MethTy I D M, object-level (depth `j`; `M` at `j+2`).
------------------------------------------------------------------------

opaque
  MethTyK : RTm Γ → RTm Γ → RTm Γ → RTm Γ → RTm Γ
  MethTyK j I D M =
    kPi (kEl I)
      (kPi (kEl (kdpay (wk 1 j I) (wk 1 j D) (kapp (wk 1 j D) v0)))
         (kPi (kDIh (wk 1 (nsuc j) (wk 1 j D)) (lift2K j M) (kapp (wk 1 (nsuc j) (wk 1 j D)) v1) v0)
            (methSK j M)))

  ⊢MethTyK : {Ξ : Ctx} {j I D M : RTm ⌊ Ξ ⌋} → Ξ ⊢ j ∷ El ⌜Nat⌝ → Ξ ⊢ I ∷ K 1 j → Ξ ⊢ D ∷ K 1 j →
             Ξ ⊢ M ∷ K 0 (nsuc (nsuc j)) → Ξ ⊢ MethTyK j I D M ∷ K 0 j
  ⊢MethTyK {Ξ} {j} {I} {D} {M} dj dI dD dM =
    ⊢kPi dj (⊢kEl dj dI)
      (⊢kPi dj1 (⊢kEl dj1 (⊢kdpay dj1 (⊢wkS (lt-s lt-z) dj dI) dD1 (⊢kapp dj1 dD1 (⊢v0 dj))))
         (⊢kPi dj2 (⊢kDIh dj2 dD2 (⊢lift2K dj dM) (⊢kapp dj2 dD2 (⊢v1 dj)) (⊢v0 dj1))
            (⊢methSK dj dM)))
    where
      dj1 : Ξ ⊢ nsuc j ∷ El ⌜Nat⌝
      dj1 = ⊢isuc dj
      dj2 : Ξ ⊢ nsuc (nsuc j) ∷ El ⌜Nat⌝
      dj2 = ⊢isuc dj1
      dD1 : Ξ ⊢ wk 1 j D ∷ K 1 (nsuc j)
      dD1 = ⊢wkS (lt-s lt-z) dj dD
      dD2 : Ξ ⊢ wk 1 (nsuc j) (wk 1 j D) ∷ K 1 (nsuc (nsuc j))
      dD2 = ⊢wkS (lt-s lt-z) dj1 dD1

opaque
  unfolding MethTyK
  MethTyK-sub : (σ : Sub Δ Θ) (j I D M : RTm Δ) → subTm σ (MethTyK j I D M) ≡ MethTyK (subTm σ j) (subTm σ I) (subTm σ D) (subTm σ M)
  MethTyK-sub σ j I D M =
    c5 (wk-sub σ 1 j I) (wk-sub σ 1 j D)
       (trans (wk-sub σ 1 (nsuc j) (wk 1 j D)) (cong (wk 1 (nsuc (subTm σ j))) (wk-sub σ 1 j D)))
       (lift2K-sub σ j M) (methSK-sub σ j M)
    where
      c5 : {a a' b b' c c' m m' n n' : RTm _} → a ≡ a' → b ≡ b' → c ≡ c' → m ≡ m' → n ≡ n' →
           kPi (kEl (subTm σ I)) (kPi (kEl (kdpay a b (kapp b v0))) (kPi (kDIh c m (kapp c v1) v0) n))
           ≡ kPi (kEl (subTm σ I)) (kPi (kEl (kdpay a' b' (kapp b' v0))) (kPi (kDIh c' m' (kapp c' v1) v0) n'))
      c5 refl refl refl refl refl = refl

------------------------------------------------------------------------
-- 5. The reduction rules' substitutions: `t[x , y]` at sort 1
--    (`psplit-β`'s single2, `natrec-suc`'s double instantiation),
--    `pwShift` (`tr-pw`), and `renTy (extR (extR vs))` (`DIh-ρ`).
------------------------------------------------------------------------

-- pwShift : Env (j+2) (j+2)   0 ↦ 1 , x+1 ↦ x+1
EPWS : RTm Γ → RTm Γ
EPWS j = app⁴ CONS (nsuc (nsuc j)) (nsuc j) v1 WK1

-- extR (extR vs) : Env (j+2) (j+3)
ELIFTW : RTm Γ → RTm Γ
ELIFTW j = app³ LIFT (nsuc (nsuc j)) (nsuc j) (app³ LIFT (nsuc j) j WK1)

module _ {Ξ : Ctx} {j : RTm ⌊ Ξ ⌋} (dj : Ξ ⊢ j ∷ El ⌜Nat⌝) where
  ⊢EPWS : Ξ ⊢ EPWS j ∷ Env (nsuc (nsuc j)) (nsuc (nsuc j))
  ⊢EPWS = ⊢CONS· (⊢isuc (⊢isuc dj)) (⊢isuc dj) (fromSK (⊢v1 dj)) (⊢WK1 (⊢isuc dj))
  ⊢ELIFTW : Ξ ⊢ ELIFTW j ∷ Env (nsuc (nsuc j)) (nsuc (nsuc (nsuc j)))
  ⊢ELIFTW = ⊢LIFT· (⊢isuc (⊢isuc dj)) (⊢isuc dj) (⊢LIFT· (⊢isuc dj) dj (⊢WK1 dj))

EPWS-sub : (σ : Sub Δ Θ) (j : RTm Δ) → subTm σ (EPWS j) ≡ EPWS (subTm σ j)
EPWS-sub σ j = cong (λ C → app⁴ C (nsuc (nsuc (subTm σ j))) (nsuc (subTm σ j)) v1 WK1) (CONS-sub σ)

ELIFTW-sub : (σ : Sub Δ Θ) (j : RTm Δ) → subTm σ (ELIFTW j) ≡ ELIFTW (subTm σ j)
ELIFTW-sub σ j = cong (λ L → app³ L (nsuc (nsuc (subTm σ j))) (nsuc (subTm σ j)) (app³ L (nsuc (subTm σ j)) (subTm σ j) WK1)) (LIFT-sub σ)

opaque
  iinstTmK : RTm Γ → RTm Γ → RTm Γ → RTm Γ → RTm Γ
  iinstTmK j i t M = trav 1 (nsuc (nsuc j)) M j (EINST j i t)

  pwShK wk2uK : RTm Γ → RTm Γ → RTm Γ
  pwShK j t = trav 1 (nsuc (nsuc j)) t (nsuc (nsuc j)) (EPWS j)
  wk2uK j M = trav 0 (nsuc (nsuc j)) M (nsuc (nsuc (nsuc j))) (ELIFTW j)

  ⊢iinstTmK : {Ξ : Ctx} {j i t M : RTm ⌊ Ξ ⌋} → Ξ ⊢ j ∷ El ⌜Nat⌝ → Ξ ⊢ i ∷ K 1 j → Ξ ⊢ t ∷ K 1 j → Ξ ⊢ M ∷ K 1 (nsuc (nsuc j)) → Ξ ⊢ iinstTmK j i t M ∷ K 1 j
  ⊢iinstTmK dj di dt dM = ⊢trav (lt-s lt-z) (⊢isuc (⊢isuc dj)) dM dj (⊢EINST dj di dt)

  ⊢pwShK : {Ξ : Ctx} {j t : RTm ⌊ Ξ ⌋} → Ξ ⊢ j ∷ El ⌜Nat⌝ → Ξ ⊢ t ∷ K 1 (nsuc (nsuc j)) → Ξ ⊢ pwShK j t ∷ K 1 (nsuc (nsuc j))
  ⊢pwShK dj dt = ⊢trav (lt-s lt-z) (⊢isuc (⊢isuc dj)) dt (⊢isuc (⊢isuc dj)) (⊢EPWS dj)

  ⊢wk2uK : {Ξ : Ctx} {j M : RTm ⌊ Ξ ⌋} → Ξ ⊢ j ∷ El ⌜Nat⌝ → Ξ ⊢ M ∷ K 0 (nsuc (nsuc j)) → Ξ ⊢ wk2uK j M ∷ K 0 (nsuc (nsuc (nsuc j)))
  ⊢wk2uK dj dM = ⊢trav lt-z (⊢isuc (⊢isuc dj)) dM (⊢isuc (⊢isuc (⊢isuc dj))) (⊢ELIFTW dj)

opaque
  unfolding iinstTmK pwShK wk2uK
  iinstTmK-sub : (σ : Sub Δ Θ) (j i t M : RTm Δ) → subTm σ (iinstTmK j i t M) ≡ iinstTmK (subTm σ j) (subTm σ i) (subTm σ t) (subTm σ M)
  iinstTmK-sub σ j i t M = trans (trav-sub σ 1 (nsuc (nsuc j)) M j (EINST j i t))
                                 (cong (trav 1 (nsuc (nsuc (subTm σ j))) (subTm σ M) (subTm σ j)) (EINST-sub σ j i t))
  pwShK-sub : (σ : Sub Δ Θ) (j t : RTm Δ) → subTm σ (pwShK j t) ≡ pwShK (subTm σ j) (subTm σ t)
  pwShK-sub σ j t = trans (trav-sub σ 1 (nsuc (nsuc j)) t (nsuc (nsuc j)) (EPWS j))
                          (cong (trav 1 (nsuc (nsuc (subTm σ j))) (subTm σ t) (nsuc (nsuc (subTm σ j)))) (EPWS-sub σ j))
  wk2uK-sub : (σ : Sub Δ Θ) (j M : RTm Δ) → subTm σ (wk2uK j M) ≡ wk2uK (subTm σ j) (subTm σ M)
  wk2uK-sub σ j M = trans (trav-sub σ 0 (nsuc (nsuc j)) M (nsuc (nsuc (nsuc j))) (ELIFTW j))
                          (cong (trav 0 (nsuc (nsuc (subTm σ j))) (subTm σ M) (nsuc (nsuc (nsuc (subTm σ j))))) (ELIFTW-sub σ j))
