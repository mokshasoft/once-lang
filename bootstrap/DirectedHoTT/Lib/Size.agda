-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- OCP-0009 · Lib — SIZES SHRINK UNDER THE PEELS (PLAN-FAITHFUL F6).
--
-- A decoder whose subject does not shrink (a conversion's `ctrn`, a
-- typing's `⊢conv`) recurses on FUEL: the inhabitant's size `sz`.  Every
-- peel of a payload — a node's payload, a pair's halves — is smaller.
--
-- `--safe`, ZERO axioms.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
open import DirectedHoTT.Spec.Syntax using ( Defs; _<ˢ_; _<ˢ?_ )
open import DirectedHoTT.Spec.SigWf using ( WfK )
import DirectedHoTT.Metatheory.Entries as Entries
module DirectedHoTT.Lib.Size (𝒮 : Defs) (wf : WfK 𝒮) where

-- ★ PLAN-REF: at a well-formed signature, all its names
private
  n = Defs.size 𝒮
  ok = Entries.sigOK 𝒮 n wf
  refs = Entries.refsOK 𝒮 n (λ p → p) wf


open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax hiding ( Fin )
open import normalizer.Syntax.Types using ( _≡_; refl )
open import DirectedHoTT.Metatheory.Canonicity 𝒮 wf using ( sz; _≤_; s≤s; ≤-refl; ≤-trans; ≤-suc; un≤; ≤+ˡ; ≤+ʳ )
open import DirectedHoTT.Lib.Sugar 𝒮 n ok using ( tag; conₗ )

-- the payload of a node is smaller than the node
szp : (k : ℕ) (p : RTm ε) {f : ℕ} → sz (conₗ k p) ≤ suc f → sz p ≤ f
szp k p h = ≤-trans (≤-trans (≤+ʳ (sz (tag {ε} k)) (sz p)) (≤-suc ≤-refl)) (un≤ h)

-- …and so are a pair's halves
szˡ : (a r : RTm ε) {f : ℕ} → sz (pair a r) ≤ suc f → sz a ≤ f
szˡ a r h = ≤-trans (≤+ˡ (sz a) (sz r)) (un≤ h)

szʳ : (a r : RTm ε) {f : ℕ} → sz (pair a r) ≤ suc f → sz r ≤ f
szʳ a r h = ≤-trans (≤+ʳ (sz a) (sz r)) (un≤ h)

------------------------------------------------------------------------
-- ★ Well-founded recursion on sizes: a premise is a STRICT subterm of
--   the inhabitant, so `sz r < sz k`.  `Acc` keeps the recursion
--   structural through the decoders' `▷` lambdas (measured: fuel
--   threaded through a lambda is invisible to the termination checker).
------------------------------------------------------------------------


infix 4 _<_
_<_ : ℕ → ℕ → Set
m < n = suc m ≤ n

data Acc (n : ℕ) : Set where
  acc : ((m : ℕ) → m < n → Acc m) → Acc n

private
  wf' : (n m : ℕ) → m < n → Acc m
  wf' (suc n) m (s≤s m≤n) = acc (λ k k<m → wf' n k (≤-trans k<m m≤n))

<-wf : (n : ℕ) → Acc n
<-wf n = acc (wf' n)

-- a node's payload, a pair's halves: strictly smaller
sz-con< : (k : ℕ) (q : RTm ε) → sz q < sz (conₗ k q)
sz-con< k q = s≤s (≤-suc (≤+ʳ (sz (tag {ε} k)) (sz q)))

sz-pairˡ< : (a b : RTm ε) → sz a < sz (pair a b)
sz-pairˡ< a b = s≤s (≤+ˡ (sz a) (sz b))

sz-pairʳ< : (a b : RTm ε) → sz b < sz (pair a b)
sz-pairʳ< a b = s≤s (≤+ʳ (sz a) (sz b))

<-trans : {l m n : ℕ} → l < m → m < n → l < n
<-trans p q = ≤-trans p (≤-trans (≤-suc ≤-refl) q)

<-≤ : {l m n : ℕ} → l < m → m ≤ n → l < n
<-≤ p q = ≤-trans p q

-- …through a peel's equation: a bound on the payload bounds its halves
<ˡ : {x a b : RTm ε} {N : ℕ} → x ≡ pair a b → sz x < N → sz a < N
<ˡ {a = a} {b} refl h = <-trans (sz-pairˡ< a b) h

<ʳ : {x a b : RTm ε} {N : ℕ} → x ≡ pair a b → sz x < N → sz b < N
<ʳ {a = a} {b} refl h = <-trans (sz-pairʳ< a b) h

-- …and a row's payload is below its inhabitant
<ᶜ : {x q : RTm ε} {i N : ℕ} → x ≡ conₗ i q → sz x ≤ N → sz q < N
<ᶜ {q = q} {i} refl h = <-≤ (sz-con< i q) h
