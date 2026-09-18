------------------------------------------------------------------------
-- OCP-0009 · KNOT — ★★★ `lookupDK` AGREES WITH `lookupD`.
--
--   lookupD dnil    _       = dι
--   lookupD (C ◃ D) zero    = C
--   lookupD (C ◃ D) (suc k) = lookupD D k
--
-- ★ TWO ROWS, not 53: `lookupDK` eliminates an ENCODED `Desc`, and
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
module DirectedHoTT.Examples.Knot.LookupDAgree where

open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax
  using ( Cx; RTm; Desc; dnil; _◃_; DCon; lookupD; app; ielim; pair )
open import DirectedHoTT.Spec.Typing
  using ( _⟶*_; done; step; β; βfst; βsnd; natrec-zero; natrec-suc )
open import DirectedHoTT.Lib.RedChain using ( _»_ )
open import DirectedHoTT.Metatheory.RedCong
  using ( ⟶*-appˡ; ⟶*-fst; ⟶*-ielimᵗ; ⟶*-ielimⁱ; ⟶*-pairʳ )
open import DirectedHoTT.Lib.IHeadRed using ( ihead-red )
open import DirectedHoTT.Lib.IMeths
  using ( cdTake; methsFrom-sel; methsFrom-past; sel-here; inCD; tt )
open import DirectedHoTT.Examples.Knot.Tags using ( tagDesc-nil; tagDesc-cons )
open import normalizer.Syntax.Types using ( _≡_; refl; cong; cong₂ )
open import DirectedHoTT.Spec.Typing using ( wk-single )
open import DirectedHoTT.Lib.ICast using ( ⟶*-castₗ; ⟶*-castᵣ )
open import DirectedHoTT.Lib.Wk using ( sub-w²-single; towerJ; pw^; w; cong₃ )
open import DirectedHoTT.Spec.Syntax
  using ( fst; snd; var; vz; vs; natrec; nzero; nsuc; iihs; isingle; ilookupD; iext; subTm
        ; idrefl; ⌜Nat⌝; unit )
open import DirectedHoTT.Lib.NatNum using ( num )
open import DirectedHoTT.Examples.Knot.Sorts using ( len; sDesc )
open import DirectedHoTT.Examples.Knot.Desc using ( KnotD )
open import DirectedHoTT.Examples.Knot.Map using ( enDesc; enDCon )
open import DirectedHoTT.Examples.Knot.LookupD using ( lookupMethsK )

lookupD-agree : {Θ : Cx} (i : RTm Θ) (D : Desc) (k : ℕ) →
                app (ielim KnotD i lookupMethsK (enDesc {Θ} D)) (num k)
                ⟶* enDCon {Θ} (lookupD D k)
-- ★ ROW `dnil` — tag 41, inside `methsFrom`'s 42-row prefix, so the
--   JUNK method answers.  And its body IS `DCon-iK`, which is
--   `enDCon dι` — no cast, exactly as `ihs-agree`'s `dι`.
lookupD-agree i dnil      k       =
  ⟶*-appˡ
    (ihead-red KnotD lookupMethsK tagDesc-nil i _
      (methsFrom-sel (cdTake 42 KnotD) tagDesc-nil
                     (inCD (cdTake 42 KnotD) tagDesc-nil tt))
      done)
  » ⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (step (β _ _) done)))
  » ⟶*-appˡ (⟶*-appˡ (step (β _ _) done))
  » ⟶*-appˡ (step (β _ _) done)
  » step (β _ _) done
-- ★ ROW `C ◃ D` at ZERO — `natrec-zero` then one projection.
lookupD-agree i (C ◃ D)   zero    =
  ⟶*-appˡ
    (ihead-red KnotD lookupMethsK tagDesc-cons i _
      (methsFrom-past (cdTake 42 KnotD) 0 » sel-here _ _)
      done)
  » ⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (step (β _ _) done)))
  » ⟶*-appˡ (⟶*-appˡ (step (β _ _) done))
  » ⟶*-appˡ (step (β _ _) done)
  » step (β _ _) done
  » step (natrec-zero _ _) done
  -- ⚠ the payload passed under TWO binders (the IH and the ℕ), so the
  --   projection lands on a two-rung tower — `ihs-agree`'s countdown.
  » ⟶*-castᵣ (sub-w²-single {a = num zero} {b = IHS} (enDCon C))
             (step (βfst _ _) done)
  where
    IHS : RTm _
    IHS = iihs KnotD lookupMethsK (isingle i) (ilookupD KnotD tagDesc-cons)
               (pair (enDCon C)
                     (pair (enDesc D) (pair (idrefl ⌜Nat⌝ sDesc) unit)))
-- ★ ROW `C ◃ D` at SUCC — `natrec-suc`, then the IH.
lookupD-agree i (C ◃ D)   (suc k) =
  ⟶*-appˡ
    (ihead-red KnotD lookupMethsK tagDesc-cons i _
      (methsFrom-past (cdTake 42 KnotD) 0 » sel-here _ _)
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
  » lookupD-agree (subTm (iext (isingle i) (fst PAY)) (pair sDesc (snd (var (vs vz))))) D k))
  where
    PAY : RTm _
    PAY = pair (enDCon C) (pair (enDesc D) (pair (idrefl ⌜Nat⌝ sDesc) unit))
    IHS : RTm _
    IHS = iihs KnotD lookupMethsK (isingle i) (ilookupD KnotD tagDesc-cons) PAY
    SBOD : RTm _
    SBOD = app (fst (snd (w (w IHS)))) (var (vs vz))

------------------------------------------------------------------------
-- ★★★ AT THE LEDGER'S NAME.
------------------------------------------------------------------------

open import DirectedHoTT.Examples.Knot.LookupD using ( lookupDK )

lookupDK-agree : {Θ : Cx} (n : RTm Θ) (D : Desc) (k : ℕ) →
                 lookupDK n (enDesc D) (num k) ⟶* enDCon {Θ} (lookupD D k)
lookupDK-agree n D k = lookupD-agree (pair sDesc n) D k
