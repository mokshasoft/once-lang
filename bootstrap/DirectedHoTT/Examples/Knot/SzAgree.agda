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
open import DirectedHoTT.Lib.NatNum using ( num )
open import DirectedHoTT.Lib.IFold using ( rowSort )
open import DirectedHoTT.Lib.ISzRed
  using ( AllIH; aih-ι; aih-κ; aih-ρ; szsSum-red )
open import DirectedHoTT.Metatheory.Canonicity using ( sz )
open import DirectedHoTT.Lib.ISzSort using ( szsMeths-sel )
open import DirectedHoTT.Examples.Knot.Sorts using ( sTm )
open import DirectedHoTT.Examples.Knot.Desc using ( KnotD; cTm-app )
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
    -- ⚠ EACH CHILD IS PEELED **TWICE**, AT DIFFERENT DEPTHS.  `iihs`
    --   builds a tuple entry as `ielim … (fst p)`, so the entry has to
    --   be projected out of the IH TUPLE (`βfst`/`βsnd` at the top) and
    --   its SCRUTINEE reduced from a projection of the payload down to
    --   the child (`⟶*-ielimᵗ`, one level in).  Two peels, easy to
    --   confuse, and the only genuinely row-specific work left.
    hf' = ⟶*-trans (step (βfst _ _) done)
                   (⟶*-trans (⟶*-ielimᵗ (step (βfst _ _) done)) hf)
    ha' = ⟶*-trans (⟶*-fst (step (βsnd _ _) done))
            (⟶*-trans (step (βfst _ _) done)
              (⟶*-trans (⟶*-ielimᵗ (⟶*-trans (⟶*-fst (step (βsnd _ _) done))
                                             (step (βfst _ _) done)))
                        ha))
    -- ★ and the whole `natrec`/`plus-num` plumbing is now ONE call.
    body = ⟶*-nsuc (szsSum-red (rowSort cTm-app) cTm-app
                               (aih-ρ hf' (aih-ρ ha' (aih-κ aih-ι))))
