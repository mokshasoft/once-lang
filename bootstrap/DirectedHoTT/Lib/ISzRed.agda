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
open import DirectedHoTT.Metatheory.RedCong
  using ( ⟶*-trans; ⟶*-natrecᶻ; ⟶*-natrecⁿ )
open import DirectedHoTT.Lib.NatNum using ( num; plus-num )
import DirectedHoTT.Lib.IFold as IF
open IF using ( Maybeℕ; sameSortAt )
open import DirectedHoTT.Lib.ISzSort using ( szsStep; szsTail; szsSum; szsSumStep )

-- what one field contributes to the running total
addIf : 𝔹 → ℕ → ℕ → ℕ
addIf true  a m = a + m
addIf false a m = a

------------------------------------------------------------------------
-- ★★★ WHAT ONE RECURSIVE FIELD OWES — WHICH DEPENDS ON WHETHER IT IS
-- COUNTED.
--
-- ⚠⚠ THE `false` CASE IS THE ENTIRE POINT OF THE SAME-SORT MEASURE.
--   `szsStep false acc h` discards `h` without looking at it, so a
--   skipped field owes NO reduction — only the step past its slot.
--
--   Were `false` to demand `h ⟶* num m` as well, the measure would buy
--   nothing: `cTm-var`'s child is a `Var`, `cTm-cMu`'s is a `Desc`,
--   `cTm-cIMu`'s are an `IDesc` and a `Ty`.  Producing a numeral for
--   any of them means proving the agreement AT THAT SORT — so the `RTm`
--   induction would drag in all seven sorts and all 53 rows, which is
--   exactly the mutual induction that counting same-sort children was
--   chosen to avoid.
------------------------------------------------------------------------

data OK : Set where
  ok : OK

IHof : {Γ : Cx} → 𝔹 → RTm Γ → ℕ → Set
IHof true  h m = h ⟶* num m
IHof false h m = OK

------------------------------------------------------------------------
-- THE HYPOTHESES A ROW SUPPLIES: one node per FIELD.
--
-- ⚠ EVERY `iρ` GETS A NODE, COUNTED OR NOT.  The IH tuple has a slot
--   per recursive field regardless of `pick`, and the walk has to step
--   past the slot either way — `addIf` and `IHof` decide only what the
--   slot CONTRIBUTES, never whether it is THERE.
--
-- ⚠ `m` IS EXPLICIT.  At a skipped field `IHof false _ m` is `OK` and
--   `addIf false a m` is `a`, so nothing mentions `m` — left implicit
--   it is a meta with nothing to solve it.  Skipped fields pass `0`.
------------------------------------------------------------------------

data AllIH {Γ : Cx} (r : Maybeℕ) : {Δ : Cx} → ℕ → ICon Δ → RTm Γ → ℕ → Set where
  aih-ι : {a : ℕ} {Δ : Cx} {ihs : RTm Γ} → AllIH r a (iι {Δ}) ihs a
  aih-κ : {a : ℕ} {Δ : Cx} {κ : RTm Δ} {C : ICon (Δ ∙)} {ihs : RTm Γ} {n : ℕ} →
          AllIH r a C ihs n → AllIH r a (iκ κ C) ihs n
  aih-ρ : {a : ℕ} {Δ : Cx} {j : RTm Δ} {C : ICon (Δ ∙)} {ihs : RTm Γ} {n : ℕ}
          (m : ℕ) →
          IHof (sameSortAt r j) (fst ihs) m →
          AllIH r (addIf (sameSortAt r j) a m) C (snd ihs) n →
          AllIH r a (iρ j C) ihs n

------------------------------------------------------------------------
-- ⚠ THE BOOLEAN IS TAKEN AS AN ARGUMENT, exactly as in `Lib/IFold`.
--   `szsStep b` and this lemma must reduce on the SAME `b`.  A `with`
--   would abstract over a different one, and `rewrite` is unavailable:
--   this project's `_≡_` is not bound as `BUILTIN EQUALITY`.
--
--   Applied to `sameSortAt r j`, each of these has exactly the type the
--   corresponding clause's goal unfolds to — so no transport is needed
--   anywhere in this file.
------------------------------------------------------------------------

szsStep-red : {Γ : Cx} (b : 𝔹) {acc h : RTm Γ} {a m : ℕ} →
              acc ⟶* num a → IHof b h m →
              szsStep b acc h ⟶* num (addIf b a m)
szsStep-red true  {a = a} {m = m} ha hm =
  -- `plusTm acc h = natrec h _ acc` — the accumulator is the SCRUTINEE
  -- and the new child is the ZERO branch, so they reduce through
  -- different congruences before `plus-num` finishes the addition.
  ⟶*-trans (⟶*-natrecⁿ ha) (⟶*-trans (⟶*-natrecᶻ hm) (plus-num a m))
szsStep-red false ha ok = ha

szsTail-red : {Γ : Cx} (r : Maybeℕ) {Δ : Cx} (C : ICon Δ)
              {acc ihs : RTm Γ} {a n : ℕ} →
              acc ⟶* num a → AllIH r a C ihs n →
              szsTail r C acc ihs ⟶* num n
szsTail-red r iι       ha aih-ι         = ha
szsTail-red r (iκ κ C) ha (aih-κ h)     = szsTail-red r C ha h
szsTail-red r (iρ j C) ha (aih-ρ m hm h) =
  szsTail-red r C (szsStep-red (sameSortAt r j) ha hm) h

-- ⚠ `szsSum` SEEDS with the first COUNTED field instead of starting at
--   `nzero`, which is what keeps a trailing `+ 0` out of the emitted
--   term.  It costs nothing here: `addIf true 0 m` is `0 + m`, and that
--   is `m` definitionally.
szsSum-red : {Γ : Cx} (r : Maybeℕ) {Δ : Cx} (C : ICon Δ)
             {ihs : RTm Γ} {n : ℕ} →
             AllIH r 0 C ihs n → szsSum r C ihs ⟶* num n
szsSumStep-red : {Γ : Cx} (b : 𝔹) (r : Maybeℕ) {Δ : Cx}
                 (C : ICon (Δ ∙)) {ihs : RTm Γ} (m : ℕ) {n : ℕ} →
                 IHof b (fst ihs) m →
                 AllIH r (addIf b 0 m) C (snd ihs) n →
                 szsSumStep b r C ihs ⟶* num n

szsSum-red r iι       aih-ι              = done
szsSum-red r (iκ κ C) (aih-κ h)          = szsSum-red r C h
szsSum-red r (iρ j C) (aih-ρ m hm h)     =
  szsSumStep-red (sameSortAt r j) r C m hm h

szsSumStep-red true  r C m hm h = szsTail-red r C hm h
szsSumStep-red false r C m hm h = szsSum-red r C h
