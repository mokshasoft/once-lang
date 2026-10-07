-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- OCP-0009 · Lib — ★ RENAMING of a `Lib/Syn` syntax: the traversal at the
-- kit whose values are VARIABLES (`Fin e`).
--
--     WK = fsuc     V0 = fzero     NODE e x = the variable node `var x`
--
-- and WEAKENING (`renTm vs`) is renaming by `λ x. fsuc x`.
--
-- `--safe`, ZERO axioms.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
open import DirectedHoTT.Spec.Syntax using ( KSig; _<ˢ_; _<ˢ?_ )
open import Agda.Builtin.Nat using () renaming ( Nat to ℕ )
import DirectedHoTT.Spec.Typing as Ty
module DirectedHoTT.Lib.SynRen (𝒮 : KSig) (𝓃 : ℕ) (ok : Ty.EntriesOK 𝒮 𝓃) where

open import normalizer.Syntax.Types using ( _≡_; refl; sym; trans; cong; subst )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import Agda.Builtin.Bool using ( Bool; true; false )
open import DirectedHoTT.Spec.Syntax
open import DirectedHoTT.Spec.Typing 𝒮 𝓃 hiding ( _×_; _,,_ )
open import DirectedHoTT.Metatheory.TySub 𝒮 𝓃 using ( ⊢wk; ⊢-cast )
open import DirectedHoTT.Lib.Sugar 𝒮 𝓃 ok using ( conₗ; tag; Lt )
open import DirectedHoTT.Lib.NatCode 𝒮 𝓃
open import DirectedHoTT.Lib.Syn 𝒮 𝓃 ok
open import DirectedHoTT.Lib.SynTrav 𝒮 𝓃 ok
open import DirectedHoTT.Lib.SynTravM 𝒮 𝓃 ok

private
  variable
    Γ : Cx
    n c : ℕ

------------------------------------------------------------------------
-- 1. WHERE THE VARIABLES LIVE, decided.
------------------------------------------------------------------------

private
  isV : Shape → Bool
  isV vʰ = true
  isV _  = false

  noV : {c : ℕ} → Shapes c → Bool
  noV []ˢʰ         = true
  noV (sh ∷ˢʰ shs) with isV sh
  ... | true  = false
  ... | false = noV shs

  eqℕ : ℕ → ℕ → Bool
  eqℕ zero    zero    = true
  eqℕ (suc a) (suc b) = eqℕ a b
  eqℕ _       _       = false

  -- every sort but `v` has no variable row
  pick : Bool → Bool → Bool → Bool
  pick true  _     r = r
  pick false true  r = r
  pick false false r = false

  varsAtB : {m : ℕ} → Sig m → ℕ → ℕ → Bool
  varsAtB []ᵍ         v s = true
  varsAtB (shs ∷ᵍ sg) v s = pick (eqℕ v s) (noV shs) (varsAtB sg v (suc s))

  eqℕ-sound : (a b : ℕ) → eqℕ a b ≡ true → a ≡ b
  eqℕ-sound zero    zero    e = refl
  eqℕ-sound (suc a) (suc b) e = cong suc (eqℕ-sound a b e)

  absurdB : {A : Set} → false ≡ true → A
  absurdB ()

  noV-sound : {c k : ℕ} (shs : Shapes c) → noV shs ≡ true → NthSh shs k vʰ → false ≡ true
  noV-sound (vʰ ∷ˢʰ shs)          () nthʰ-z
  noV-sound ([]ʰ ∷ˢʰ shs)         e (nthʰ-s nt) = noV-sound shs e nt
  noV-sound ((f ∷ʰ sh) ∷ˢʰ shs)   e (nthʰ-s nt) = noV-sound shs e nt
  noV-sound (vʰ ∷ˢʰ shs)          () (nthʰ-s nt)

  -- case on a boolean, remembering which (the `inspect` idiom)
  bcase : {X : Set} (a : Bool) → (a ≡ true → X) → (a ≡ false → X) → X
  bcase true  t f = t refl
  bcase false t f = f refl

  pick-rest : (a b r : Bool) → pick a b r ≡ true → r ≡ true
  pick-rest true  b     r e = e
  pick-rest false true  r e = e

  pick-head : (a b r : Bool) → pick a b r ≡ true → a ≡ false → b ≡ true
  pick-head false true  r e f = refl

  -- the sort counter runs alongside the signature
  sound : {m : ℕ} (sg : Sig m) (v s₀ : ℕ) → varsAtB sg v s₀ ≡ true →
          {s c k : ℕ} {shs : Shapes c} → NthG sg s shs → NthSh shs k vʰ → v ≡ s +' s₀
  sound (shs ∷ᵍ sg) v s₀ e nthᵍ-z nt =
    bcase (eqℕ v s₀) (eqℕ-sound v s₀)
          (λ f → absurdB (noV-sound shs (pick-head (eqℕ v s₀) (noV shs) _ e f) nt))
  sound (shs ∷ᵍ sg) v s₀ e (nthᵍ-s ng) nt =
    sound sg v (suc s₀) (pick-rest (eqℕ v s₀) (noV shs) _ e) ng nt

-- ★ a concrete signature's variable sort, by `refl`
varsAt : {m : ℕ} (sg : Sig m) (v : ℕ) → varsAtB sg v zero ≡ true → VarsAt sg v
varsAt sg v e {s = s} ng nt = trans (sound sg v zero e ng nt) (+'-zero s)

------------------------------------------------------------------------
-- 2. THE RENAMING KIT.
------------------------------------------------------------------------

module Ren {sg : Sig n} (ok : SigOK n sg) {v kv : ℕ} {shs : Shapes c}
           (ngv : NthG sg v shs) (nhv : NthSh shs kv vʰ) (vok : VarsAt sg v) where

  VFr : RTm Γ
  VFr = lam (⌜Fin⌝ (var vz))

  -- a value IS a variable
  vf≅ : {e : RTm Γ} → Vat VFr e ≅ᵀ Fin e
  vf≅ {e = e} = ctrnᵀ (credᵀ (ξ-El (β _ e))) (credᵀ El-⌜Fin⌝)

  renKit : Kit n sg
  renKit = record
    { vsort = v
    ; VF    = VFr
    ; WK    = lam (lam (fsuc (var vz)))
    ; V0    = lam fzero
    ; NODE  = lam (lam (conₗ kv (pair (var vz) unit)))
    ; VF-sub = λ σ → refl
    ; ⊢VF   = ⊢lam (ty-El ⊢⌜Nat⌝) (⊢⌜Fin⌝ (fromI (⊢var here)))
    ; ⊢WK   = ⊢lam (ty-El ⊢⌜Nat⌝) (⊢lam (ty-El (⊢app ⊢VFr (⊢var here)))
                 (⊢conv (⊢fsuc (⊢conv (⊢var here) vf≅)) (csymᵀ vf≅)))
    ; ⊢V0   = ⊢lam (ty-El ⊢⌜Nat⌝) (⊢conv (⊢fzero (fromI (⊢var here))) (csymᵀ vf≅))
    ; ⊢NODE = ⊢lam (ty-El ⊢⌜Nat⌝) (⊢lam (ty-El (⊢app ⊢VFr (⊢var here)))
                 (⊢conSyn ok ngv nhv (⊢var (there here)) (a-v (⊢conv (⊢var here) vf≅))))
    }
    where
      ⊢VFr : {Γ : Ctx} → Γ ⊢ VFr ∷ Π (El ⌜Nat⌝) U
      ⊢VFr = ⊢lam (ty-El ⊢⌜Nat⌝) (⊢⌜Fin⌝ (fromI (⊢var here)))

  open TravM ok renKit vok public

  -- ★ RENAMING: `t : Syn s d` through `ρ : Fin d → Fin e`
  ren : ℕ → RTm Γ → RTm Γ → RTm Γ → RTm Γ → RTm Γ
  ren = trav

  -- the weakening environment `λ x. fsuc x : Fin d → Fin (suc d)`
  WKρ : RTm Γ
  WKρ = lam (fsuc (var vz))

  ⊢WKρ : {Γ : Ctx} {d : RTm ⌊ Γ ⌋} → Γ ⊢ d ∷ El ⌜Nat⌝ → Γ ⊢ WKρ ∷ Trav.Env ok renKit d (nsuc d)
  ⊢WKρ dd = ⊢lam (ty-Fin (fromI dd)) (⊢conv (⊢fsuc (⊢var here)) (csymᵀ vf≅))

  -- ★ WEAKENING: `renTm vs`, object-level
  wk : ℕ → RTm Γ → RTm Γ → RTm Γ
  wk s d t = trav s d t (nsuc d) WKρ

  ⊢wkS : {Γ : Ctx} {s : ℕ} {d t : RTm ⌊ Γ ⌋} → Lt s n →
         Γ ⊢ d ∷ El ⌜Nat⌝ → Γ ⊢ t ∷ SK sg s d → Γ ⊢ wk s d t ∷ SK sg s (nsuc d)
  ⊢wkS lt dd dt = ⊢trav lt dd dt (⊢isuc dd) (⊢WKρ dd)
