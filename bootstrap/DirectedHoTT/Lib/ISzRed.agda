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

------------------------------------------------------------------------
-- ★★★ THE `AllIH` FAMILY AND THE THREE LEMMAS OVER IT NOW COME FROM
--   `Lib/IFoldRed`, which is `Lib/IFold`'s reduction twin.  This module
--   carried its own copy until 2026-09-11 and `Lib/IOccRed` a second,
--   differing in FOUR knobs; the bodies were identical line for line.
--   ⇒ what is left here is the ONE client-specific lemma, `szsStep-red`,
--     which is where the arithmetic lives.
--
-- ★ AND THE UNIT LAW THIS FILE ALREADY KNEW ABOUT.  The old `szsSum-red`
--   note read: *"`addIf true 0 m` is `0 + m`, and that is `m`
--   definitionally"* — true here and for `maxℕ`, and false for an
--   abstract `nop`.  `Lib/IFoldRed` takes it as `nop-unitˡ`, which is
--   the first ALGEBRAIC law in this library tree (`FUTURE.md`'s audit
--   found 57 laws and every one a TYPING law).
------------------------------------------------------------------------

open import DirectedHoTT.Lib.IFoldRed as IFR using ( OK; ok; comb; IHof )
-- ★ re-exported: `Knot/SzAgree`'s skipped-field rows are written `ok`.
open IFR using ( OK; ok ) public
open import normalizer.Syntax.Types using ( refl )

SzExt : Cx → Set
SzExt _ = OK

SzHolds : {Γ : Cx} → SzExt Γ → RTm Γ → ℕ → Set
SzHolds _ h m = h ⟶* num m

szsStep-red : {Γ : Cx} (b : 𝔹) (e : SzExt Γ) {acc h : RTm Γ} (a m : ℕ) →
              SzHolds e acc a → IHof SzHolds b e h m →
              SzHolds e (szsStep b acc h) (comb _+_ b a m)
-- `plusTm acc h = natrec h _ acc` — the accumulator is the SCRUTINEE and
-- the new child is the ZERO branch, so they reduce through different
-- congruences before `plus-num` finishes the addition.
szsStep-red true  e a m ha hm =
  ⟶*-trans (⟶*-natrecⁿ ha) (⟶*-trans (⟶*-natrecᶻ hm) (plus-num a m))
szsStep-red false e a m ha ok = ha

open import DirectedHoTT.Lib.ISzSort using ( module SzR )

open SzR.Red SzExt SzHolds _+_ szsStep-red (λ _ → done) (λ m → refl) public
  renaming ( ifTail-red    to szsTail-red
           ; ifSum-red     to szsSum-red
           ; ifSumStep-red to szsSumStep-red )
