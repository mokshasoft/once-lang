------------------------------------------------------------------------
-- OCP-0009 · LIB — ★★★ THE SAME-SORT FOLD **REDUCES** TO THE NUMERAL OF
-- ITS SUM, FOR AN ARBITRARY CONSTRUCTOR.
--
--     szsSum-red : AllIH r 0 C ihs n → szsSum r C ihs ⟶* num n
--
-- ★ WHY A LEMMA AND NOT 30 CHAINS.  `Examples/Knot/SzAgree` shows the
--   chain for one recursive row; it is ten lines of `⟶*-natrecⁿ`,
--   `⟶*-natrecᶻ`, `βfst`, `βsnd` and `plus-num`, and its SHAPE depends
--   only on the row's field list — which is data the fold already walks.
--   So the plumbing is proved once, by the same induction the fold
--   itself does, and each row is left with the one thing that really is
--   row-specific: handing over its children's induction hypotheses.
--
-- ⚠ THE ACCUMULATOR IS AN INDEX, NOT A RESULT.  `szsTail` folds LEFT TO
--   RIGHT, so the running total has to be threaded INTO `AllIH` rather
--   than summed up out of it.  Summed out, the natural statement would
--   associate to the RIGHT — `m + (rest)` — and every use would owe an
--   associativity rearrangement against `szb`, whose clauses associate
--   to the left.  This is the same trap the accumulator ORDER was
--   (`Lib/IFold`'s `ifStep`), one level up.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Lib.ISzRed where
open import Agda.Builtin.Nat using ( zero; suc; _+_ ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax
  using ( Cx; _∙; RTm; ICon; iι; iρ; iκ; fst; snd; nzero )
open import DirectedHoTT.Spec.Typing using ( _⟶*_; done )
open import DirectedHoTT.Spec.Variance using ( 𝔹; true; false )
open import DirectedHoTT.Metatheory.Confluence
  using ( ⟶*-trans; ⟶*-natrecᶻ; ⟶*-natrecⁿ )
open import DirectedHoTT.Lib.NatNum using ( num; plus-num )
import DirectedHoTT.Lib.IFold as IF
open IF using ( Maybeℕ; sameSortAt )
open import DirectedHoTT.Lib.ISzSort
  using ( szsStep; szsTail; szsSum; szsSumStep )

-- what one field contributes to the running total
addIf : 𝔹 → ℕ → ℕ → ℕ
addIf true  a m = a + m
addIf false a m = a

------------------------------------------------------------------------
-- THE HYPOTHESES A ROW SUPPLIES: one reduction per RECURSIVE field.
--
-- ⚠ EVERY `iρ` CARRIES ONE, COUNTED OR NOT.  The IH tuple has a slot per
--   recursive field regardless of `pick`, and the walk has to step past
--   the slot either way — `addIf` decides only whether the slot's value
--   joins the total, never whether the slot is there.
------------------------------------------------------------------------

data AllIH {Γ : Cx} (r : Maybeℕ) : {Δ : Cx} → ℕ → ICon Δ → RTm Γ → ℕ → Set where
  aih-ι : {a : ℕ} {Δ : Cx} {ihs : RTm Γ} → AllIH r a (iι {Δ}) ihs a
  aih-κ : {a : ℕ} {Δ : Cx} {κ : RTm Δ} {C : ICon (Δ ∙)} {ihs : RTm Γ} {n : ℕ} →
          AllIH r a C ihs n → AllIH r a (iκ κ C) ihs n
  aih-ρ : {a : ℕ} {Δ : Cx} {j : RTm Δ} {C : ICon (Δ ∙)} {ihs : RTm Γ}
          {m n : ℕ} →
          fst ihs ⟶* num m →
          AllIH r (addIf (sameSortAt r j) a m) C (snd ihs) n →
          AllIH r a (iρ j C) ihs n

------------------------------------------------------------------------
-- ⚠ THE BOOLEAN IS TAKEN AS AN ARGUMENT, exactly as in `Lib/IFold`.
--   `szsStep b` and this lemma must reduce on the SAME `b`; a `with`
--   here would abstract over a different one.
------------------------------------------------------------------------

szsStep-red : {Γ : Cx} (b : 𝔹) {acc h : RTm Γ} {a m : ℕ} →
              acc ⟶* num a → h ⟶* num m →
              szsStep b acc h ⟶* num (addIf b a m)
szsStep-red true  {a = a} {m = m} ha hm =
  -- `plusTm acc h = natrec h _ acc` — the accumulator is the SCRUTINEE
  -- and the new child is the ZERO branch, so they reduce through
  -- different congruences before `plus-num` finishes the addition.
  ⟶*-trans (⟶*-natrecⁿ ha) (⟶*-trans (⟶*-natrecᶻ hm) (plus-num a m))
szsStep-red false ha hm = ha

szsTail-red : {Γ : Cx} (r : Maybeℕ) {Δ : Cx} (C : ICon Δ)
              {acc ihs : RTm Γ} {a n : ℕ} →
              acc ⟶* num a → AllIH r a C ihs n →
              szsTail r C acc ihs ⟶* num n
szsTail-red r iι       ha aih-ι      = ha
szsTail-red r (iκ κ C) ha (aih-κ h)  = szsTail-red r C ha h
szsTail-red r (iρ j C) ha (aih-ρ hm h) =
  szsTail-red r C (szsStep-red (sameSortAt r j) ha hm) h

-- ⚠ `szsSum` SEEDS with the first COUNTED field instead of starting at
--   `nzero`, which is what keeps a trailing `+ 0` out of the emitted
--   term.  It costs nothing here: `addIf true 0 m` is `0 + m`, and that
--   is `m` definitionally.
szsSum-red : {Γ : Cx} (r : Maybeℕ) {Δ : Cx} (C : ICon Δ)
             {ihs : RTm Γ} {n : ℕ} →
             AllIH r 0 C ihs n → szsSum r C ihs ⟶* num n
-- ⚠ NO `j` HERE.  The field's index does not appear in the conclusion —
--   only the BOOLEAN it was turned into does — so an implicit `j` would
--   be a meta with nothing to solve it.
szsSumStep-red : {Γ : Cx} (b : 𝔹) (r : Maybeℕ) {Δ : Cx}
                 (C : ICon (Δ ∙)) {ihs : RTm Γ} {m n : ℕ} →
                 fst ihs ⟶* num m →
                 AllIH r (addIf b 0 m) C (snd ihs) n →
                 szsSumStep b r C ihs ⟶* num n

szsSum-red r iι       aih-ι        = done
szsSum-red r (iκ κ C) (aih-κ h)    = szsSum-red r C h
szsSum-red r (iρ j C) (aih-ρ hm h) =
  szsSumStep-red (sameSortAt r j) r C hm h

szsSumStep-red true  r C hm h = szsTail-red r C hm h
szsSumStep-red false r C hm h = szsSum-red r C h
