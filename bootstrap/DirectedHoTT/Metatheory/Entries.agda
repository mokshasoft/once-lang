-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- OCP-0009 · dHoTT — ★ THE SIGNATURE'S ENTRIES, for the metatheory
--   (PLAN-REF, D082).
--
-- From the signature's context formation (`Spec/SigWf`: each entry typed
-- in its prefix) to the two things the metatheory reads:
--
--   · `sigOK m`  — every entry below m is typed at bound m (subject
--     reduction unfolds a reference to its body): the prefix derivation,
--     moved up by `Metatheory/SigMono`;
--   · `refsOK m` — every reference below m is REDUCIBLE (the oracle
--     `fund` reads), by induction on m: entry m is `fund` AT m on its own
--     derivation, with the oracle below m from the induction hypothesis,
--     then one δ expansion.  Acyclicity is exactly what makes this an
--     induction: the derivation of entry m uses only the names before it.
--
-- `--safe`, ZERO axioms.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
open import DirectedHoTT.Spec.Syntax using ( KSig; _<ˢ_; <-here; <-there )
module DirectedHoTT.Metatheory.Entries (𝒮 : KSig) where
open import normalizer.Syntax.Types using ( _,_ )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.SigWf using ( WfUpTo )
import DirectedHoTT.Spec.Typing as Ty
import DirectedHoTT.Metatheory.SigMono as SigMono
import DirectedHoTT.Metatheory.Fundamental as F
open import DirectedHoTT.Metatheory.Fundamental.Semantic 𝒮 using ( RefsOK )
open import DirectedHoTT.Metatheory.LogicalRelation 𝒮 using ( dfst; dsnd; exp₁; snr-δ )

-- an entry typed at bound a is typed at any larger bound
moveEntry : (a b : ℕ) → (∀ {d} → d <ˢ a → d <ˢ b) → {e : ℕ} → Ty.EntryOK 𝒮 a e → Ty.EntryOK 𝒮 b e
moveEntry a b inc (Ty.entryOK t u) = Ty.entryOK (SigMono.monoTy 𝒮 a b inc t) (SigMono.mono 𝒮 a b inc u)

sigOK : (m : ℕ) → WfUpTo 𝒮 m → Ty.SigOK 𝒮 m
sigOK (suc m) (w , e) <-here      = moveEntry m (suc m) <-there e
sigOK (suc m) (w , e) (<-there p) = moveEntry m (suc m) <-there (sigOK m w p)

-- the names below m are in the signature, so δ fires on each
refsOK : (m : ℕ) → (∀ {d} → d <ˢ m → d <ˢ KSig.size 𝒮) → WfUpTo 𝒮 m → RefsOK m
refsOK (suc m) inS (w , e) <-here x₀ =
  let r = F.fund 𝒮 m (sigOK m w) (refsOK m (λ p → inS (<-there p)) w) (Ty.okBody e) x₀ (F.⊩ˢ-ε 𝒮 m (sigOK m w) (refsOK m (λ p → inS (<-there p)) w)) in
  dfst r , exp₁ (dfst r) (snr-δ (inS <-here)) (dsnd r)
refsOK (suc m) inS (w , e) (<-there p) x₀ = refsOK m (λ q → inS (<-there q)) w p x₀
