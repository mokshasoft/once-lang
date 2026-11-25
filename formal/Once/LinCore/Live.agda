-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.LinCore.Live — plan 0.146 B1.6 item 3 (D470): THE CELLS A VALUE HOLDS
-- ARE LIVE BLOCKS. For every cell a value holds, the machine's allocator has
-- its block at the size the lowering allocated it (a μ node `1 ⊔` its layer's
-- words, a closure or a ν its header and contents) and has not freed it. So
-- the image's free of a cell it holds passes the machine's free gate
-- (`Flat.block-base?`): the block is live and of the size the free names.
-- Stated per value over the machine's sizes (`Layout.wsz`), not over the ids'
-- (the spike's `words`, generic in the base widths).
------------------------------------------------------------------------

{-# OPTIONS --guardedness #-}

open import Data.Nat using (ℕ; zero; suc; _+_; _⊔_; _<_; _≡ᵇ_; _<ᵇ_; s≤s; z≤n)
open import Data.Nat.Properties using (≡⇒≡ᵇ; <⇒<ᵇ)
open import Data.Bool using (Bool; true; false; not; _∧_; T)
open import Data.Product using (_×_; _,_)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans)
open import Once.Spec.Numerics using (TargetNum)
open import Once.LinCore.Flat using (Base)
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.SMCore using (AllocState; module AllocState)
open import Once.CCC.Machine.Flat using (module FlatMachine)

module Once.LinCore.Live
  (fmt : TargetNum)
  (bw : Base → ℕ)
  where

open import Once.LinCore.Core fmt using (LTy; LF∙; μt; Coalg; _⊗t_)
open import Once.LinCore.Values fmt bw using (MV; mone; mpair; minl; minr; mbase; mmu; mct; mfn; mnu; Id; serial; hdr; wsz)
open import Once.LinCore.Code fmt bw using (Stk; []ˢ; _∷ˢ_; Slots; []ᵉ; vw; ln; Cfg; _∥_)
open import Once.Memory.HeapAddress using (heap-loc; mkHeapRef)
open import Once.CCC.Machine.Locations using (AtDynamic)
open import Once.CCC.Machine.SMCore using (SV-Ptr)

module _ {FS : FrameSemantics} where
  open AllocState {FS} using (block-size; freed)

  -- a cell's block: allocated at `n` words and not freed
  LiveB : AllocState {FS} → ℕ → Id → Set
  LiveB al n i = (block-size al (serial i) ≡ n) × (freed al (serial i) ≡ false)

  -- every cell a value holds, at the size the lowering allocates it
  LiveV : ∀ {A} → AllocState {FS} → MV A → Set
  LiveV al mone          = ⊤
  LiveV al (mpair a b)   = LiveV al a × LiveV al b
  LiveV al (minl a)      = LiveV al a
  LiveV al (minr b)      = LiveV al b
  LiveV al (mbase _)     = ⊤
  LiveV al (mmu {F} i v) = LiveB al (1 ⊔ wsz (LF∙ F (μt F))) i × LiveV al v
  LiveV al (mct x)       = LiveV al x
  LiveV al (mfn {X = X} i _ x) = LiveB al (hdr + wsz X) i × LiveV al x
  LiveV al (mnu {F} {S} i p)   = LiveB al (hdr + wsz (Coalg F S ⊗t S)) i × LiveV al p

  -- every cell a configuration mentions (its slots' views and values, its operands)
  LiveE : ∀ {Es} → AllocState {FS} → Slots Es → Set
  LiveE al []ᵉ         = ⊤
  LiveE al (vw e es)   = LiveV al e × LiveE al es
  LiveE al (ln e x es) = (LiveV al e × LiveV al x) × LiveE al es

  LiveS : ∀ {S} → AllocState {FS} → Stk S → Set
  LiveS al []ˢ       = ⊤
  LiveS al (v ∷ˢ os) = LiveV al v × LiveS al os

  LiveC : ∀ {sh} → AllocState {FS} → Cfg sh → Set
  LiveC al (es ∥ os) = LiveE al es × LiveS al os

  -- ★ a live block of a positive size passes the machine's free gate at its base
  -- (`Words.Rel.cellPtr i`)
  live-gate : ∀ (al : AllocState {FS}) {n} i → 0 < n → LiveB al n i
            → FlatMachine.block-base? {FS} n (SV-Ptr (AtDynamic (heap-loc (mkHeapRef (serial i)) 0))) al ≡ true
  live-gate al {n} i pos (sz , fr) =
    cong₄ (λ a b c d → a ∧ b ∧ c ∧ not d) refl (trans (cong (_≡ᵇ n) sz) (T-true (≡⇒≡ᵇ n n refl))) (T-true (<⇒<ᵇ pos)) fr
    where
      T-true : ∀ {b} → T b → b ≡ true
      T-true {true} _ = refl
      cong₄ : ∀ {A B C D E : Set} (f : A → B → C → D → E) {a a′ b b′ c c′ d d′}
            → a ≡ a′ → b ≡ b′ → c ≡ c′ → d ≡ d′ → f a b c d ≡ f a′ b′ c′ d′
      cong₄ f refl refl refl refl = refl
