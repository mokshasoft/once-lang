------------------------------------------------------------------------
-- OCP-0009 · EXAMPLES — ⬜ SPIKE: ONE ROW OF THE `sz` AGREEMENT.
--
--     szsTm i ⌈ t ⌉  ⟶*  ⌜ sz t ⌝
--
-- ★ THE POINT OF DOING ONE ROW FIRST.  `Lib/ISzSort` makes the two
--   measures AGREE AS NUMBERS (`Examples/Knot/SzProbe`, 30 rows), which
--   is necessary but says nothing about whether the encoded fold
--   REDUCES to that number.  This file is the reduction half, on the
--   simplest possible row, to fix the chain's shape and cost before it
--   is written thirty times.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Knot.SzAgree where
open import Agda.Builtin.Nat using ( zero; suc; _+_ ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax
  using ( Cx; RTm; nzero; icon; ielim; app; pair; unit; idrefl; ⌜Nat⌝
        ; fst; snd; nsuc; var; vz )
open import DirectedHoTT.Spec.Typing
  using ( _⟶_; _⟶*_; done; step; ι-ielim; β; βfst; βsnd )
open import DirectedHoTT.Metatheory.Confluence
  using ( ⟶*-trans; ⟶*-appˡ; ⟶*-fst; ⟶*-snd; ⟶*-nsuc
        ; ⟶*-natrecᶻ; ⟶*-natrecⁿ; ⟶*-ielimᵗ )
open import DirectedHoTT.Lib.NatNum using ( num; plus-num )
open import DirectedHoTT.Metatheory.Canonicity using ( sz )
open import DirectedHoTT.Lib.ISzSort using ( szsMeths-sel )
open import DirectedHoTT.Examples.Knot.Sorts using ( sTm )
open import DirectedHoTT.Examples.Knot.Desc using ( KnotD )
open import DirectedHoTT.Examples.Knot.Tags
  using ( tagTm-nzero; memTm-nzero; tagTm-app; memTm-app )
open import DirectedHoTT.Examples.Knot.Ctors using ( Tm-nzeroK; Tm-appK )
open import DirectedHoTT.Examples.Knot.SzS using ( szsTm; szsMethsK )

-- ⚠ THE INDEX IS ARBITRARY.  `ι-ielim` does not inspect it, and the
--   method discards it at the first `β` — so the agreement does NOT
--   depend on the encoded term sitting at its own index.  (It does for
--   TYPING; that is `⊢szsTm`'s business, not this one's.)
agree-nzero : {Γ Γ' : Cx} (i : RTm Γ') →
              szsTm i (Tm-nzeroK {Γ'}) ⟶* num (sz {Γ} nzero)
agree-nzero i =
  step (ι-ielim KnotD i szsMethsK tagTm-nzero (pair (idrefl ⌜Nat⌝ sTm) unit))
       (⟶*-trans sel3 (⟶*-trans β₁ (⟶*-trans β₂ β₃)))
  where
    -- the METHOD is selected out of the 53-tuple, in ONE step per row
    sel3 = ⟶*-appˡ (⟶*-appˡ (⟶*-appˡ
             (szsMeths-sel KnotD tagTm-nzero memTm-nzero)))
    -- ⚠ THEN THREE `β`s, INNERMOST FIRST.  The term is
    --   `app (app (app m i) p) ihs`; only `app m i` has a `lam` in head
    --   position, so each `β` is reached through one fewer `⟶*-appˡ`
    --   than the one before.
    β₁ = ⟶*-appˡ (⟶*-appˡ (step (β _ _) done))
    β₂ = ⟶*-appˡ (step (β _ _) done)
    β₃ = step (β _ _) done

------------------------------------------------------------------------
-- ★★★ AND THE ROW THAT ACTUALLY RECURSES.
--
--     szb (app f a) = sz f + sz a
--
-- ⚠ THE INDEX THE CHILDREN ARE ELIMINATED AT IS NOT `i`.  `cTm-app`'s
--   fields carry `pair sTm (snd (var vz))`, and `isingle i` sends
--   `var vz` to `i` — so the recursive calls land at
--   `pair sTm (snd i)`.  That is why the statement quantifies over the
--   index: an `i`-specific one could not feed itself.
--
-- ⚠ THE IH TUPLE IS A `pair`, SO ITS PROJECTIONS ARE REDEXES.  `fst`
--   and `snd` are term formers stepping by `βfst`/`βsnd`, not
--   meta-level projections — and they have to be taken through
--   `plusTm`'s `natrec`.
------------------------------------------------------------------------

agree-app : {Γ' : Cx} (i ef ea : RTm Γ') (nf na : ℕ) →
            ielim KnotD (pair sTm (snd i)) szsMethsK ef ⟶* num nf →
            ielim KnotD (pair sTm (snd i)) szsMethsK ea ⟶* num na →
            szsTm i (Tm-appK ef ea) ⟶* num (suc (nf + na))
agree-app i ef ea nf na hf ha =
  step (ι-ielim KnotD i szsMethsK tagTm-app
                (pair ef (pair ea (pair (idrefl ⌜Nat⌝ sTm) unit))))
       (⟶*-trans sel3 (⟶*-trans β₁ (⟶*-trans β₂ (⟶*-trans β₃ body))))
  where
    sel3 = ⟶*-appˡ (⟶*-appˡ (⟶*-appˡ
             (szsMeths-sel KnotD tagTm-app memTm-app)))
    β₁ = ⟶*-appˡ (⟶*-appˡ (step (β _ _) done))
    β₂ = ⟶*-appˡ (step (β _ _) done)
    β₃ = step (β _ _) done
    -- the accumulator is `plusTm (fst ihs) (fst (snd ihs))`, and
    -- `plusTm m n = natrec n _ m` — so the FIRST child is reached
    -- through `⟶*-natrecⁿ` and the SECOND through `⟶*-natrecᶻ`.
    -- ⚠ EACH CHILD IS PEELED **TWICE**.  `iihs` builds a tuple entry as
    --   `ielim … (fst p)` — the SCRUTINEE is a projection of the
    --   payload, not the child itself.  So each IH is reached by first
    --   reducing that scrutinee down to the child (through
    --   `⟶*-ielimᵗ`), and only then projecting the finished entry out
    --   of the IH tuple with `βfst`/`βsnd`.  Two peels per field, at
    --   different depths, and they are easy to confuse.
    hf' = ⟶*-trans (⟶*-ielimᵗ (step (βfst _ _) done)) hf
    ha' = ⟶*-trans (⟶*-ielimᵗ (⟶*-trans (⟶*-fst (step (βsnd _ _) done))
                                        (step (βfst _ _) done))) ha
    body = ⟶*-nsuc
             (⟶*-trans (⟶*-natrecⁿ (⟶*-trans (step (βfst _ _) done) hf'))
               (⟶*-trans (⟶*-natrecᶻ
                            (⟶*-trans (⟶*-fst (step (βsnd _ _) done))
                                      (⟶*-trans (step (βfst _ _) done) ha')))
                         (plus-num nf na)))
