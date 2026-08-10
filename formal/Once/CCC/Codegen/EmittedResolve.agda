-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.CCC.Codegen.EmittedResolve   (D100, second half)
--
-- RESOLVING IS NOT ENOUGH — IT MUST RESOLVE TO THE INTENDED LABEL.
--
-- `EmittedWF.labels-resolvable` says every reference is a MEMBER of the
-- defined set. That is the `ld` fact ("no undefined reference") and, on its
-- own, it buys nothing about control flow: with a label defined twice a jump
-- still resolves — possibly to a stranger's definition.
--
-- WHY NOTHING IN THE STACK COULD SAY OTHERWISE. Every existing statement about
-- label resolution is the SOUND direction:
--
--   `find-label-sound`  — what the scan finds carries that label
--   `find-thunk-sound`  — what the call scan finds is a body entry for it
--   `find-label-corr` / `find-thunk-corr` — the flat scan and the concrete
--                         scan land on the SAME block
--
-- All three are true of the FIRST match, whether or not it is the right one.
-- `FlatComposition` even records this as a simplification ("no label-uniqueness
-- argument anywhere") — and it is a simplification, because two first-match
-- scans agree with each other regardless. That is exactly the blindness D100
-- named at the assembler: the meaning of the program is DEFINED by the scan on
-- both sides, so no internal theorem can be false. "Intended" exists only at
-- the emitter — the `c-label end` emitted in the same literal list as the
-- `c-jmp end` that names it.
--
-- What was missing is the COMPLETE direction: the definition the emitter put at
-- position `j` is what the scan returns. That direction is FALSE without
-- uniqueness (an earlier duplicate shadows it) and true with it — which is the
-- second, sharper reason `EmittedWF.labels-unique` is load-bearing. It is not
-- only what keeps `as` from rejecting the file; it is what makes every
-- reference mean what the emitter meant.
--
-- So `labels-unique` and `labels-resolvable` are a MATCHED PAIR (cf. the
-- `Window` weakening and `do-thunk`'s clear): membership without uniqueness
-- names a definition that need not be yours, and uniqueness without membership
-- does not give you one at all. Together they say: exactly one definition
-- exists, hence it is the one your own clause emitted.
--
-- Both scans get the theorem, and the `thunk` one is if anything the more
-- consequential: it is what `instr-load-code-addr` puts in a closure's code
-- cell, so a shadowed body entry is a call into the WRONG closure body — with
-- both machines agreeing about it.
------------------------------------------------------------------------

open import Once.CCC.FrameSemantics using (FrameSemantics)

module Once.CCC.Codegen.EmittedResolve (FS : FrameSemantics) where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.All using (All) renaming (lookup to all-lookup)
open import Data.List.Relation.Unary.AllPairs using (AllPairs; _∷_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ; ∈-++⁺ʳ)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-identityʳ; +-suc)
open import Data.Product using (proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; subst)

open import Once.CCC.Label using (Label; once; thunk; LabelId; _≡ᵇᴵ_; ≡ᵇᴵ-true; ≡ᵇᴵ-refl)
open import Once.CCC.Machine.SMCore using
  ( AbstractInstr; AbstractTrace; instr-ctrl; c-label; c-thunk )
open import Once.CCC.Machine.Flat using (module FlatMachine)
open import Once.CCC.Codegen.EmittedWF using (labels-def; labels-def-i)

open FlatMachine {FS} using
  ( fetch
  ; label-of?; fl-go; fl-at; fl-label-match; find-label; label-of?-sound
  ; thunk-of?; ft-go; ft-at; ft-match;   find-thunk; thunk-of?-sound )

------------------------------------------------------------------------
-- Plumbing: a defining occurrence at a position contributes its name.
--
-- One lemma per provenance rather than one generic one — `labels-def-i` gives
-- `once m` for a `c-label` and `thunk m` for a `c-thunk`, and keeping them
-- apart is what makes the two clash arguments below reduce.
------------------------------------------------------------------------

label-at→∈ : ∀ (t : AbstractTrace) (m : LabelId) (j : ℕ)
           → fetch t j ≡ just (instr-ctrl (c-label m))
           → once m ∈ labels-def t
label-at→∈ [] m zero    ()
label-at→∈ [] m (suc j) ()
label-at→∈ (x ∷ is) m zero    eq rewrite just-injective eq = here refl
label-at→∈ (x ∷ is) m (suc j) eq =
  ∈-++⁺ʳ (labels-def-i x) (label-at→∈ is m j eq)

thunk-at→∈ : ∀ (t : AbstractTrace) (m : LabelId) (b : ℕ) (j : ℕ)
           → fetch t j ≡ just (instr-ctrl (c-thunk m b))
           → thunk m ∈ labels-def t
thunk-at→∈ [] m b zero    ()
thunk-at→∈ [] m b (suc j) ()
thunk-at→∈ (x ∷ is) m b zero    eq rewrite just-injective eq = here refl
thunk-at→∈ (x ∷ is) m b (suc j) eq =
  ∈-++⁺ʳ (labels-def-i x) (thunk-at→∈ is m b j eq)

-- Dropping a prefix from an `AllPairs`: the IH below is about the tail of the
-- trace, whose defined labels are the tail of the appended list.
allpairs-drop : ∀ (xs ys : List Label) → AllPairs _≢_ (xs ++ ys) → AllPairs _≢_ ys
allpairs-drop []       ys ap        = ap
allpairs-drop (x ∷ xs) ys (_ ∷ ap) = allpairs-drop xs ys ap

-- The clash itself: a head that also occurs in the tail contradicts distinctness.
head-clash : ∀ (ℓ : Label) (ys : List Label)
           → AllPairs _≢_ (ℓ ∷ ys) → ℓ ∈ ys → ⊥
head-clash ℓ ys (px ∷ _) mem = all-lookup px mem refl

------------------------------------------------------------------------
-- THE JUMP SCAN IS COMPLETE — under uniqueness.
--
-- Read it as the converse of `find-label-sound`: that one says the scan's
-- answer carries the label, this one says the label's (unique) definition IS
-- the scan's answer. Only together do they pin the jump to a position.
--
-- The `true` branch of the match is where uniqueness is spent: if the head
-- were ALSO a `c-label m`, the trace would define `once m` twice.
------------------------------------------------------------------------

fl-go-complete : ∀ (t : AbstractTrace) (m : LabelId) (acc j : ℕ)
               → AllPairs _≢_ (labels-def t)
               → fetch t j ≡ just (instr-ctrl (c-label m))
               → fl-go t m acc ≡ just (acc + j)
fl-go-complete [] m acc zero    ap ()
fl-go-complete [] m acc (suc j) ap ()
fl-go-complete (x ∷ is) m acc zero ap eq
  rewrite just-injective eq | ≡ᵇᴵ-refl m = cong just (sym (+-identityʳ acc))
fl-go-complete (x ∷ is) m acc (suc j) ap eq = step (label-of? x) refl
  where
    ap-is : AllPairs _≢_ (labels-def is)
    ap-is = allpairs-drop (labels-def-i x) (labels-def is) ap

    ih : fl-go is m (suc acc) ≡ just (suc acc + j)
    ih = fl-go-complete is m (suc acc) j ap-is eq

    past : fl-go is m (suc acc) ≡ just (acc + suc j)
    past = trans ih (cong just (sym (+-suc acc j)))

    -- The head is a `c-label m` too — so `once m` is defined twice.
    clash : label-of? x ≡ just m → ⊥
    clash lo-eq =
      head-clash (once m) (labels-def is)
        (subst (λ i → AllPairs _≢_ (labels-def (i ∷ is)))
               (label-of?-sound x m lo-eq) ap)
        (label-at→∈ is m j eq)

    match : ∀ (m' : LabelId) → label-of? x ≡ just m' → ∀ (b : Bool) → (m' ≡ᵇᴵ m) ≡ b
          → fl-label-match b is m acc ≡ just (acc + suc j)
    match m' lo-eq false _  = past
    match m' lo-eq true  be =
      ⊥-elim (clash (trans lo-eq (cong just (≡ᵇᴵ-true m' m be))))

    step : ∀ (lo : Maybe LabelId) → label-of? x ≡ lo
         → fl-at lo is m acc ≡ just (acc + suc j)
    step nothing   _     = past
    step (just m') lo-eq = match m' lo-eq (m' ≡ᵇᴵ m) refl

-- THE statement: the definition the emitter placed at `j` is where a jump to
-- that label goes. FALSE without `labels-unique` — that is the point.
find-label-complete : ∀ (t : AbstractTrace) (m : LabelId) (j : ℕ)
                    → AllPairs _≢_ (labels-def t)
                    → fetch t j ≡ just (instr-ctrl (c-label m))
                    → find-label t m ≡ just j
find-label-complete t m j ap eq = fl-go-complete t m 0 j ap eq

------------------------------------------------------------------------
-- THE CALL SCAN IS COMPLETE — the same, over the `thunk` provenance.
--
-- This is the consequential twin. `instr-load-code-addr ℓ` puts the resolution
-- of `find-thunk … ℓ` in a closure's code cell, so without uniqueness a closure
-- can carry the address of a DIFFERENT body — and `find-thunk-corr` would still
-- hold, because the concrete `lea` scans the same way and lands on the same
-- wrong block.
------------------------------------------------------------------------

ft-go-complete : ∀ (t : AbstractTrace) (m : LabelId) (b : ℕ) (acc j : ℕ)
               → AllPairs _≢_ (labels-def t)
               → fetch t j ≡ just (instr-ctrl (c-thunk m b))
               → ft-go t m acc ≡ just (acc + j)
ft-go-complete [] m b acc zero    ap ()
ft-go-complete [] m b acc (suc j) ap ()
ft-go-complete (x ∷ is) m b acc zero ap eq
  rewrite just-injective eq | ≡ᵇᴵ-refl m = cong just (sym (+-identityʳ acc))
ft-go-complete (x ∷ is) m b acc (suc j) ap eq = step (thunk-of? x) refl
  where
    ap-is : AllPairs _≢_ (labels-def is)
    ap-is = allpairs-drop (labels-def-i x) (labels-def is) ap

    past : ft-go is m (suc acc) ≡ just (acc + suc j)
    past = trans (ft-go-complete is m b (suc acc) j ap-is eq)
                 (cong just (sym (+-suc acc j)))

    clash : thunk-of? x ≡ just m → ⊥
    clash to-eq =
      head-clash (thunk m) (labels-def is)
        (subst (λ i → AllPairs _≢_ (labels-def (i ∷ is)))
               (proj₂ (thunk-of?-sound x m to-eq)) ap)
        (thunk-at→∈ is m b j eq)

    match : ∀ (m' : LabelId) → thunk-of? x ≡ just m' → ∀ (c : Bool) → (m' ≡ᵇᴵ m) ≡ c
          → ft-match c is m acc ≡ just (acc + suc j)
    match m' to-eq false _  = past
    match m' to-eq true  ce =
      ⊥-elim (clash (trans to-eq (cong just (≡ᵇᴵ-true m' m ce))))

    step : ∀ (to : Maybe LabelId) → thunk-of? x ≡ to
         → ft-at to is m acc ≡ just (acc + suc j)
    step nothing   _     = past
    step (just m') to-eq = match m' to-eq (m' ≡ᵇᴵ m) refl

find-thunk-complete : ∀ (t : AbstractTrace) (m : LabelId) (b : ℕ) (j : ℕ)
                    → AllPairs _≢_ (labels-def t)
                    → fetch t j ≡ just (instr-ctrl (c-thunk m b))
                    → find-thunk t m ≡ just j
find-thunk-complete t m b j ap eq = ft-go-complete t m b 0 j ap eq
