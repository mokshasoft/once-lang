-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.ThunkScope — CONTAINMENT FOR THE *THUNK* NAMESPACE.
--
-- `LabelScope` bounds every `once`-namespace label an emitted fragment
-- MENTIONS. It says nothing about `c-thunk`: `once-label-of`
-- (LabelScope.agda:83-89) sends `c-thunk` to `nothing`, because the two are
-- different provenances (D082) — jump targets versus body entries.
--
-- `entry-no-thunks` needs the other one. `find-thunk` scans for `c-thunk`
-- markers, so "no earlier marker carries this block's label" is a fact about
-- THUNK labels, and nothing in the tree bounded them.
--
-- THE TRACE CHANNEL IS NEARLY EMPTY, which is what makes this tractable.
-- `curry`, `Ana` and `in-ν` put their bodies in the BLOCKS list; their emitted
-- traces carry `instr-load-code-addr`, not `c-thunk` (LabelScope's own comment
-- at :566-569 notes the same asymmetry from the `once` side). The ONLY emitted
-- `c-thunk` is `cata-body`'s (IRToTrace.agda:262-267), spliced inline for all
-- four cata strategies.
--
-- So every other constructor is discharged by a DECIDER — `CataIRSlotStable`'s
-- `all-stable?-sound refl` idiom — rather than by a hand-written `All` of
-- vacuous witnesses, one per instruction.
------------------------------------------------------------------------

module Once.CCC.Codegen.ThunkScope where

open import Data.Bool using (Bool; true; false; _∧_)
open import Data.Nat using (ℕ; _≤_; _<_)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)
open import Data.Empty using (⊥; ⊥-elim)

open import Once.CCC.Label using (LabelId; idx)
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.SMCore
  using (AbstractTrace; AbstractInstr; instr-ctrl; c-thunk)
open import Once.CCC.Machine.Flat using (module FlatMachine)

module Scope {FS : FrameSemantics} where
  open FlatMachine {FS} using (thunk-of?)

  ------------------------------------------------------------------------
  -- The predicate, and its decider.
  ------------------------------------------------------------------------

  -- A record for `LabelIn`'s reason: at a use site the goal must keep the
  -- INSTRUCTION rigid, which a reducing function would not.
  record ThunkIn (lo hi : ℕ) (i : AbstractInstr) : Set where
    constructor mkThunkIn
    field in-range : ∀ (m : LabelId) → thunk-of? i ≡ just m → (lo ≤ idx m) × (idx m < hi)
  open ThunkIn public

  ThunksIn : ℕ → ℕ → AbstractTrace → Set
  ThunksIn lo hi = All (ThunkIn lo hi)

  -- THE DECIDER, defined THROUGH `thunk-of?` rather than by pattern-matching
  -- the 31 `AbstractInstr` constructors. That is what makes the soundness proof
  -- two cases instead of 31: `with thunk-of? i` splits on the RESULT, and the
  -- catch-all never has to reduce on an abstract instruction.
  is-none : Maybe LabelId → Bool
  is-none (just _) = false
  is-none nothing  = true

  no-thunk? : AbstractInstr → Bool
  no-thunk? i = is-none (thunk-of? i)

  all-no-thunk? : AbstractTrace → Bool
  all-no-thunk? []       = true
  all-no-thunk? (i ∷ is) = no-thunk? i ∧ all-no-thunk? is

  no-thunk?-sound : ∀ (i : AbstractInstr) → no-thunk? i ≡ true → thunk-of? i ≡ nothing
  no-thunk?-sound i eq with thunk-of? i
  ... | nothing = refl

  -- An instruction that is not a marker is in EVERY range, vacuously.
  thunk-none-in : ∀ {lo hi} (i : AbstractInstr) → thunk-of? i ≡ nothing → ThunkIn lo hi i
  thunk-none-in i eq = mkThunkIn λ m teq → ⊥-elim (none≢just (trans (sym eq) teq))
    where
      none≢just : ∀ {m : LabelId} → (nothing {A = LabelId}) ≡ just m → ⊥
      none≢just ()

  -- …so a thunk-free trace is, at any range. This is the one-liner every
  -- non-cata clause of the induction below uses: `all-no-thunk-in _ refl`.
  all-no-thunk-in : ∀ {lo hi} (t : AbstractTrace) → all-no-thunk? t ≡ true → ThunksIn lo hi t
  all-no-thunk-in []       _  = []
  all-no-thunk-in (i ∷ is) eq = go (no-thunk? i) refl eq
    where
      go : ∀ (b : Bool) → no-thunk? i ≡ b → (b ∧ all-no-thunk? is) ≡ true
         → ∀ {lo hi} → ThunksIn lo hi (i ∷ is)
      go true  beq eqs = thunk-none-in i (no-thunk?-sound i beq) ∷ all-no-thunk-in is eqs
      go false _   ()
