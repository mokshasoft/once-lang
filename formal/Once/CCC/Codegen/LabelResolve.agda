-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.LabelResolve — WHERE A JUMP LANDS.
--
-- `find-label-sound` (Flat.agda:465) is the SOUNDNESS direction: given
-- `find-label prog ℓ ≡ just j`, it says what sits at `j`. The CONVERSE did not
-- exist — `grep find-label-complete` returns nothing — and it is what a
-- label-bearing correctness clause actually needs: the jump this fragment
-- emitted lands on the label this fragment defined, not on an earlier one.
--
-- This is the `once`-namespace mirror of the `thunk`-namespace lemmas in
-- `BlockLayout` (`ft-hit`, `block-resolves`, `NoThunk`/`no-thunk-miss`). The
-- two scans are structurally identical — `fl-go`/`fl-at`/`fl-label-match`
-- against `ft-go`/`ft-at`/`ft-match`, differing only in `label-of?` versus
-- `thunk-of?` — because a jump target and a body entry are different
-- provenances (D082) over the same machinery.
--
-- It serves TWO open obligations, which is why it is its own module:
--   * `obs-correct-case` (plan 0.88) — the only label-bearing per-constructor
--     postulate left, and Class D's stated blocker;
--   * `entry-no-thunks` (plan 0.93 S4) uses the thunk twin already.
--
-- With-free in `Flat`'s own style (D092/D094): the `fl-at`/`fl-label-match`
-- dispatch is mirrored by an auxiliary per layer, so each reduces without a
-- `with` under an abstract head.
------------------------------------------------------------------------

open import Once.CanonicalName using (CanonicalName)

module Once.CCC.Codegen.LabelResolve (o : CanonicalName) where

open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ; suc; _+_)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

open import Once.CCC.Label using (LabelId; _≡ᵇᴵ_; ≡ᵇᴵ-true; ≡ᵇᴵ-refl)
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.SMCore
  using (AbstractTrace; AbstractInstr; instr-ctrl; c-label)
open import Once.CCC.Machine.Flat using (module FlatMachine)

module Resolve {FS : FrameSemantics} where
  open FlatMachine {FS}
    using (find-label; fl-go; fl-at; fl-label-match; label-of?; fl-go-++-miss)

  ------------------------------------------------------------------------
  -- The scan HITS a label it is standing on.
  ------------------------------------------------------------------------

  fl-hit : ∀ (ℓ : LabelId) (rest : AbstractTrace) (i : ℕ)
         → fl-go (instr-ctrl (c-label ℓ) ∷ rest) ℓ i ≡ just i
  fl-hit ℓ rest i rewrite ≡ᵇᴵ-refl ℓ = refl

  ------------------------------------------------------------------------
  -- FROM A SYNTACTIC FACT TO THE SCAN'S MISS.
  --
  -- `NoLabel ℓ t` is the LIST statement an emitter induction can produce:
  -- every instruction either defines no label or defines a different one.
  -- `fl-go-++-miss` wants the SCAN statement; this bridges them, exactly as
  -- `no-thunk-miss` does on the thunk side.
  ------------------------------------------------------------------------

  NoLabel : LabelId → AbstractTrace → Set
  NoLabel ℓ = All (λ i → ¬ (label-of? i ≡ just ℓ))

  no-label-miss  : ∀ (ℓ : LabelId) (t : AbstractTrace) (i : ℕ)
                 → NoLabel ℓ t → fl-go t ℓ i ≡ nothing
  no-label-at    : ∀ (mo : Maybe LabelId) (ℓ : LabelId) (t : AbstractTrace) (i : ℕ)
                 → ¬ (mo ≡ just ℓ) → NoLabel ℓ t → fl-at mo t ℓ i ≡ nothing
  no-label-match : ∀ (b : Bool) (m ℓ : LabelId) (t : AbstractTrace) (i : ℕ)
                 → (m ≡ᵇᴵ ℓ) ≡ b → ¬ (m ≡ ℓ) → NoLabel ℓ t
                 → fl-label-match b t ℓ i ≡ nothing

  no-label-miss ℓ []       i _         = refl
  no-label-miss ℓ (x ∷ t') i (px ∷ pt) = no-label-at (label-of? x) ℓ t' i px pt

  no-label-at (just m) ℓ t i ne nl =
    no-label-match (m ≡ᵇᴵ ℓ) m ℓ t i refl (λ eq → ne (cong just eq)) nl
  no-label-at nothing  ℓ t i _  nl = no-label-miss ℓ t (suc i) nl

  -- `true` would mean `m ≡ ℓ`, which the hypothesis forbids.
  no-label-match true  m ℓ t i beq ne nl = ⊥-elim (ne (≡ᵇᴵ-true m ℓ beq))
  no-label-match false m ℓ t i _   _  nl = no-label-miss ℓ t (suc i) nl

  ------------------------------------------------------------------------
  -- THE CONVERSE OF `find-label-sound`: a jump lands where the label is.
  --
  -- Given that nothing earlier defines `ℓ`, the scan resolves to exactly the
  -- prefix's length — the position the label actually occupies.
  ------------------------------------------------------------------------

  label-resolves : ∀ (pre : AbstractTrace) (ℓ : LabelId) (post : AbstractTrace)
                 → NoLabel ℓ pre
                 → find-label (pre ++ instr-ctrl (c-label ℓ) ∷ post) ℓ
                   ≡ just (length pre + 0)
  label-resolves pre ℓ post nl =
    trans (fl-go-++-miss pre (instr-ctrl (c-label ℓ) ∷ post) ℓ 0
             (no-label-miss ℓ pre 0 nl))
          (fl-hit ℓ post (length pre + 0))
