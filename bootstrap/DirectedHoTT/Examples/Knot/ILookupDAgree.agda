------------------------------------------------------------------------
-- OCP-0009 · KNOT — ★★★ `ilookupDK` AGREES WITH `ilookupD`.
--
-- ⚠ GENERATED FROM `Knot/LookupDAgree` BY SUBSTITUTION and green on the
--   first port — `Desc`→`IDesc`, 42→47, and `enICon`'s SECOND context
--   argument (`ICon (ε ∙)`, not `ICon Θ`).  The two proofs are the same
--   proof; if one changes, re-port rather than re-derive.
--
--   ilookupD inil    _       = dι
--   ilookupD (C ◂ D) zero    = C
--   ilookupD (C ◂ D) (suc k) = ilookupD D k
--
-- ★ TWO ROWS, not 53: `ilookupDK` eliminates an ENCODED `Desc`, and
--   `Knot/Map` gives that sort two constructors.  Row 41 (`dnil`) is
--   covered by the JUNK method, whose body IS `DCon-iK` — `LookupD`'s
--   header calls that "a pleasant surprise", and it makes `dnil`'s row
--   free.
--
-- ★ THE THIRD CLAUSE IS ON THE ℕ, not on the description: `lookupCons`
--   is a `natrec`, so the `C ◃ D` row splits zero/suc and the suc branch
--   IS the IH applied to the predecessor.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Knot.ILookupDAgree where

open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax
  using ( Cx; ε; _∙; RTm; IDesc; inil; _◂_; ICon; ilookupD; app; ielim; pair )
open import DirectedHoTT.Spec.Typing
  using ( _⟶*_; done; step; β; βfst; βsnd; natrec-zero; natrec-suc )
open import DirectedHoTT.Lib.RedChain using ( _»_ )
open import DirectedHoTT.Metatheory.RedCong
  using ( ⟶*-appˡ; ⟶*-fst; ⟶*-ielimᵗ; ⟶*-ielimⁱ; ⟶*-pairʳ )
open import DirectedHoTT.Lib.IHeadRed using ( ihead-red )
open import DirectedHoTT.Lib.IMeths
  using ( cdTake; methsFrom-sel; methsFrom-past; sel-here; inCD; tt )
open import DirectedHoTT.Examples.Knot.Tags using ( tagIDesc-nil; tagIDesc-cons )
open import normalizer.Syntax.Types using ( _≡_; refl; cong; cong₂ )
open import DirectedHoTT.Spec.Typing using ( wk-single )
open import DirectedHoTT.Lib.ICast using ( ⟶*-castₗ; ⟶*-castᵣ )
open import DirectedHoTT.Lib.Wk using ( sub-w²-single; towerJ; pw^; w; cong₃ )
open import DirectedHoTT.Spec.Syntax
  using ( fst; snd; var; vz; vs; natrec; nzero; nsuc; iihs; isingle; ilookupD; iext; subTm
        ; idrefl; ⌜Nat⌝; unit )
open import DirectedHoTT.Lib.NatNum using ( num )
open import DirectedHoTT.Examples.Knot.Sorts using ( len; sIDesc )
open import DirectedHoTT.Examples.Knot.Desc using ( KnotD )
open import DirectedHoTT.Examples.Knot.Map using ( enIDesc; enICon )
open import DirectedHoTT.Examples.Knot.ILookupD using ( ilookupMethsK )

ilookupD-agree : {Θ : Cx} (i : RTm Θ) (D : IDesc) (k : ℕ) →
                app (ielim KnotD i ilookupMethsK (enIDesc {Θ} D)) (num k)
                ⟶* enICon {ε ∙} {Θ} (ilookupD D k)
-- ★ ROW `dnil` — tag 41, inside `methsFrom`'s 42-row prefix, so the
--   JUNK method answers.  And its body IS `DCon-iK`, which is
--   `enICon dι` — no cast, exactly as `ihs-agree`'s `dι`.
ilookupD-agree i inil      k       =
  ⟶*-appˡ
    (ihead-red KnotD ilookupMethsK tagIDesc-nil i _
      (methsFrom-sel (cdTake 47 KnotD) tagIDesc-nil
                     (inCD (cdTake 47 KnotD) tagIDesc-nil tt))
      done)
  » ⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (step (β _ _) done)))
  » ⟶*-appˡ (⟶*-appˡ (step (β _ _) done))
  » ⟶*-appˡ (step (β _ _) done)
  » step (β _ _) done
-- ★ ROW `C ◃ D` at ZERO — `natrec-zero` then one projection.
ilookupD-agree i (C ◂ D)   zero    =
  ⟶*-appˡ
    (ihead-red KnotD ilookupMethsK tagIDesc-cons i _
      (methsFrom-past (cdTake 47 KnotD) 0 » sel-here _ _)
      done)
  » ⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (step (β _ _) done)))
  » ⟶*-appˡ (⟶*-appˡ (step (β _ _) done))
  » ⟶*-appˡ (step (β _ _) done)
  » step (β _ _) done
  » step (natrec-zero _ _) done
  -- ⚠ the payload passed under TWO binders (the IH and the ℕ), so the
  --   projection lands on a two-rung tower — `ihs-agree`'s countdown.
  » ⟶*-castᵣ (sub-w²-single {a = num zero} {b = IHS} (enICon C))
             (step (βfst _ _) done)
  where
    IHS : RTm _
    IHS = iihs KnotD ilookupMethsK (isingle i) (ilookupD KnotD tagIDesc-cons)
               (pair (enICon C)
                     (pair (enIDesc D) (pair (idrefl ⌜Nat⌝ sIDesc) unit)))
-- ★ ROW `C ◃ D` at SUCC — `natrec-suc`, then the IH.
ilookupD-agree i (C ◂ D)   (suc k) =
  ⟶*-appˡ
    (ihead-red KnotD ilookupMethsK tagIDesc-cons i _
      (methsFrom-past (cdTake 47 KnotD) 0 » sel-here _ _)
      done)
  » ⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (step (β _ _) done)))
  » ⟶*-appˡ (⟶*-appˡ (step (β _ _) done))
  » ⟶*-appˡ (step (β _ _) done)
  » step (β _ _) done
  -- ★★ CLEAN BEFORE `natrec-suc`, NOT AFTER.  Reducing first leaves the
  --   βs' four substitutions AND natrec-suc's two stacked on one slot;
  --   cleaning first means `natrec-suc` acts on a body already in normal
  --   form and owes only its own two rungs.
  -- ⚠ THE SUC BRANCH IS TWO BINDERS DEEPER, so its IH slot is `pw^ 2`
  --   where the zero branch's payload is `sub-w²-single`.
  » ⟶*-castₗ
      (cong₃ natrec
             (cong fst (sub-w²-single {a = num (suc k)} {b = IHS} PAY))
             (cong (λ z → app (fst (snd z)) (var (vs vz)))
                   (pw^ {u = num (suc k)} 2 IHS))
             refl)
   (   step (natrec-suc _ _ _) done
  -- ⚠ TWO SLOTS, not one: `natrec-suc` substitutes BOTH its binders, so
  --   the IH owes two rungs and the predecessor one.
  » ⟶*-castₗ (cong₂ (λ z nn → app (fst (snd z)) nn)
                    (sub-w²-single {a = natrec (fst PAY) SBOD (num k)}
                                   {b = num k} IHS)
                    (wk-single {v = natrec (fst PAY) SBOD (num k)} (num k)))
  (   ⟶*-appˡ (⟶*-fst (step (βsnd _ _) done))
  » ⟶*-appˡ (step (βfst _ _) done)
  -- ★ the recursive eliminator's SCRUTINEE is `fst (snd pay)` — the
  --   tail `Desc` — so two more projections before the IH applies.
  » ⟶*-appˡ (⟶*-ielimᵗ (⟶*-fst (step (βsnd _ _) done)))
  » ⟶*-appˡ (⟶*-ielimᵗ (step (βfst _ _) done))
  » ilookupD-agree (subTm (iext (isingle i) (fst PAY)) (pair sIDesc (snd (var (vs vz))))) D k))
  where
    PAY : RTm _
    PAY = pair (enICon C) (pair (enIDesc D) (pair (idrefl ⌜Nat⌝ sIDesc) unit))
    IHS : RTm _
    IHS = iihs KnotD ilookupMethsK (isingle i) (ilookupD KnotD tagIDesc-cons) PAY
    SBOD : RTm _
    SBOD = app (fst (snd (w (w IHS)))) (var (vs vz))

------------------------------------------------------------------------
-- ★★★ AT THE LEDGER'S NAME.
------------------------------------------------------------------------

open import DirectedHoTT.Examples.Knot.ILookupD using ( ilookupDK )

iilookupDK-agree : {Θ : Cx} (n : RTm Θ) (D : IDesc) (k : ℕ) →
                 ilookupDK n (enIDesc D) (num k) ⟶* enICon {ε ∙} {Θ} (ilookupD D k)
iilookupDK-agree n D k = ilookupD-agree (pair sIDesc n) D k
