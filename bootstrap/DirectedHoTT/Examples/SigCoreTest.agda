-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- OCP-0009 · EXAMPLES — ★ `Examples/SigCore`'s DECODER IS FAITHFUL: the
-- Lib-form decoder has the Lib's `SD` normal form; the decoder gives, at
-- every constructor tested, the Lib's telescope (the λ-calculus; the
-- Knot, every field kind, both sorts) and the arities.  Each `refl` was
-- checked against a deliberately wrong right-hand side.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.SigCoreTest where
open import DirectedHoTT.Spec.Syntax using ( ∅ᴷ )
open import DirectedHoTT.Examples.Sig0 using ( wf₀; ok₀; refs₀; tbl₀; tok₀ )
open import normalizer.Syntax.Types using ( _≡_; refl; _×_; _,_ )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import Agda.Builtin.List using ( List; []; _∷_ )
open import DirectedHoTT.Spec.Syntax using ( ε; _∙; vz; vs )
import DirectedHoTT.Spec.Syntax as R
open import DirectedHoTT.Lib.NatNum ∅ᴷ 0 using ( num )
open import DirectedHoTT.Lib.Sugar ∅ᴷ 0 ok₀ using ( tag )
open import DirectedHoTT.Lib.Tel ∅ᴷ 0 ok₀ using ( ⌜_⌝ᵗ )
import DirectedHoTT.Lib.Syn ∅ᴷ 0 ok₀ as L
open import DirectedHoTT.Examples.Knot.Sig using ( sh-kPi; sh-kFin; sh-kvar; sh-klam; sh-kref; sh-knatrec )
open import DirectedHoTT.Examples.SigCore
open import DirectedHoTT.Examples.SigCoreEval

private
  -- a sort and a variable depth
  ixK : ℕ → R.RTm (ε R.∙)
  ixK s = R.pair (tag s) (R.var vz)

  -- constructor k of sort s: the core's telescope, and the Lib's
  coreTel : ℕ → ℕ → ℕ → ℕ → ℕ → R.RTm (ε R.∙)
  coreTel n v sg s k = ⟪ #tel ⟫ ⋆ (num n ∷ tag v ∷ tag s ∷ R.app (R.snd (R.app ⟪ sg ⟫ (tag s))) (tag k) ∷ ixK s ∷ [])
  libTel : ℕ → L.Shape → R.RTm (ε R.∙)
  libTel s sh = ⌜ L.tel sh (ixK s) ⌝ᵗ

-- (1) the Lib-form decoder IS the Lib's `SD` (the λ-calculus, whole)
sd-lib : nfOf {ε} (⟪ #SD ⟫ ⋆ (num 1 ∷ tag 0 ∷ ⟪ #lamΣ ⟫ ∷ [])) ≡ nfOf (L.SD libΣ)
sd-lib = refl

-- (2) the decoder, constructor by constructor: the λ-calculus …
sd-faithful : (nfOf (coreTel 1 0 #lamΣ 0 0) ≡ nfOf (libTel 0 L.vʰ))
            × ((nfOf (coreTel 1 0 #lamΣ 0 1) ≡ nfOf (libTel 0 (L.rec 0 1 L.∷ʰ L.[]ʰ)))
            × (nfOf (coreTel 1 0 #lamΣ 0 2) ≡ nfOf (libTel 0 (L.rec 0 0 L.∷ʰ L.rec 0 0 L.∷ʰ L.[]ʰ))))
sd-faithful = refl , (refl , refl)

-- … and the KNOT: every field kind (variable, binder, cross-sort, nat, cls),
--   both sorts, the arities.  (The WHOLE `KD` by normal form OOMs the type
--   checker: 4.7 min at the cgroup's cap, 2026-10-05.)
kd-arity : (nfOf {ε} (R.fst (R.app ⟪ #KΣ ⟫ (tag 0))) ≡ num 13) × (nfOf {ε} (R.fst (R.app ⟪ #KΣ ⟫ (tag 1))) ≡ num 39)
kd-arity = refl , refl

kd-faithful : (nfOf (coreTel 2 1 #KΣ 0 2) ≡ nfOf (libTel 0 sh-kPi)) × ((nfOf (coreTel 2 1 #KΣ 0 12) ≡ nfOf (libTel 0 sh-kFin))
            × ((nfOf (coreTel 2 1 #KΣ 1 0) ≡ nfOf (libTel 1 sh-kvar)) × ((nfOf (coreTel 2 1 #KΣ 1 1) ≡ nfOf (libTel 1 sh-klam))
            × ((nfOf (coreTel 2 1 #KΣ 1 38) ≡ nfOf (libTel 1 sh-kref)) × (nfOf (coreTel 2 1 #KΣ 1 21) ≡ nfOf (libTel 1 sh-knatrec))))))
kd-faithful = refl , (refl , (refl , (refl , (refl , refl))))

