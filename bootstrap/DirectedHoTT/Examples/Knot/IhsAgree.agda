------------------------------------------------------------------------
-- OCP-0009 · KNOT — ★★★ `ihsK` AND `fieldsK` AGREE WITH `ihs`/`fields`.
--
--   ihsK-agree    : ihsK ⌈|Γ|⌉ ⌈C⌉ ⌈D⌉ ⌈ms⌉ ⌈p⌉   ⟶* ⌈ ihs D ms C p ⌉
--   fieldsK-agree : fieldsK ⌈|Γ|⌉ ⌈D⌉ ⌈ms⌉ ⌈C⌉ ⌈m⌉ ⌈p⌉
--                                                ⟶* ⌈ fields D ms C m p ⌉
--
-- Discharges two ledger entries.  ⚠ `IHS-ATTEMPTS.md` §2 has the log;
-- it took FIVE attempts, and the two that mattered were predicted there
-- before any of them was run.
--
--   meta   ihs D ms dι       p = unit
--          ihs D ms (dρ C)   p = pair (elim D ms (fst p)) (ihs D ms C (snd p))
--          ihs D ms (dκ A C) p = ihs D ms C (snd p)
--
-- ★★★ THREE CASES, NOT 53.  `ihsK` eliminates an ENCODED `DCon`, and
--   `Knot/Map` gives that sort three constructors, so rows 0–42 and
--   46–52 of `ihsMethsK` are UNREACHABLE by any `enDCon`.
--
-- ★★★ THE INDEX IS QUANTIFIED.  `OCC-ATTEMPTS` 25–28: pinning the index
--   in a ROW statement is what created the need for an index peel and
--   cost six refuted mechanisms.  `iihs` hands each child
--   `subTm (isingle i) (pair s (snd (var vz)))`, so a row pinned at a
--   particular index cannot apply to any child.  ⇒ the row-level
--   statement quantifies `i`; the TOP-LEVEL `ihsK-agree` ties it to
--   `pair sDCon (num (len Γ))`.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Knot.IhsAgree where

open import DirectedHoTT.Spec.Syntax
  using ( Cx; RTm; Desc; DCon; dι; dρ; dκ; app; ielim; ihs )
open import DirectedHoTT.Spec.Typing using ( _⟶*_; done; step; β )
open import DirectedHoTT.Lib.RedChain using ( _»_ )
open import DirectedHoTT.Metatheory.RedCong using ( ⟶*-appˡ )
open import DirectedHoTT.Lib.IHeadRed using ( ihead-red )
open import DirectedHoTT.Lib.IMeths
  using ( cdTake; methsFrom-sel; methsFrom-past; sel-here; sel-there; inCD; tt )
open import DirectedHoTT.Spec.Typing using ( βfst )
open import DirectedHoTT.Spec.Syntax using ( pair; fst; snd; icon )
open import DirectedHoTT.Metatheory.RedCong
  using ( ⟶*-icon; ⟶*-pairˡ; ⟶*-pairʳ; ⟶*-ielimᵗ; ⟶*-fst )
open import DirectedHoTT.Spec.Typing using ( βsnd )
open import DirectedHoTT.Spec.Syntax using ( iihs; isingle; idrefl; ⌜Nat⌝; unit )
open import DirectedHoTT.Examples.Knot.Desc using ( cDCon-rho; cDCon-kap )
open import DirectedHoTT.Examples.Knot.Map using ( enTy )
open import DirectedHoTT.Examples.Knot.Sorts using ( sDCon )
open import DirectedHoTT.Examples.Knot.Ctors using ( Tm-pairK; Tm-elimK; Tm-fstK; Tm-sndK )
open import DirectedHoTT.Lib.ICast using ( ⟶*-castₗ )
open import DirectedHoTT.Lib.Wk using ( towerJ; towerJ⁵; sub-w²-single )
open import DirectedHoTT.Spec.Typing using ( wk-single )
open import normalizer.Syntax.Types using ( _≡_; refl )

cong₄' : {Γ : Cx} {a a' b b' c c' d d' : RTm Γ}
         (f : RTm Γ → RTm Γ → RTm Γ → RTm Γ → RTm Γ) →
         a ≡ a' → b ≡ b' → c ≡ c' → d ≡ d' → f a b c d ≡ f a' b' c' d'
cong₄' f refl refl refl refl = refl

-- ★ descend into `Tm-pairK`'s SECOND component — `Tm-pairK a b =
--   icon tagTm-pair (pair a (pair b (pair (idrefl ⌜Nat⌝ sTm) unit)))`,
--   so it is `ConSAgree.inCon`'s three-layer descent.
inPairR : {Γ : Cx} {a b b' : RTm Γ} → b ⟶* b' → Tm-pairK a b ⟶* Tm-pairK a b'
inPairR r = ⟶*-icon (⟶*-pairʳ (⟶*-pairˡ r))
open import DirectedHoTT.Examples.Knot.Tags using ( tagDCon-i; tagDCon-rho; tagDCon-kap )
open import DirectedHoTT.Lib.NatNum using ( num )
open import DirectedHoTT.Examples.Knot.Sorts using ( len )
open import DirectedHoTT.Examples.Knot.Desc using ( KnotD )
open import DirectedHoTT.Examples.Knot.Map using ( enTm; enDesc; enDCon )
open import DirectedHoTT.Examples.Knot.IhsMeths using ( ihsMethsK )

ihs-agree : {Γ Θ : Cx} (i : RTm Θ) (D : Desc) (ms : RTm Γ) (C : DCon) (p : RTm Γ) →
            app (app (app (app (ielim KnotD i ihsMethsK (enDCon C))
                               (num (len Γ)))
                          (enDesc D))
                     (enTm ms))
                (enTm p)
            ⟶* enTm {Γ} {Θ} (ihs D ms C p)
-- ★ ROW `dι` — `ihs D ms dι p = unit`, and the method is the JUNK one:
--   tag 43 sits INSIDE `methsFrom`'s 44-row prefix, so the selection is
--   `methsFrom-sel`, not `methsFrom-past`.  ⚠ `Knot/RenSpec:110` is the
--   precedent; `OccAgree` uses `methsAt-*` because its tuple is built
--   with `methsAt`.
--
-- ⚠ SEVEN βs, peeling 6·5·4·3·2·1·0 `appˡ`s — three from `⊢methLam`
--   (index, payload, IH) and four motive passengers (n, D, ms, p).
--   `SUBTM` step 8's `4·3·2·1·0` is the same count one motive smaller.
ihs-agree i D ms dι       p =
  ⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (⟶*-appˡ
    (ihead-red KnotD ihsMethsK tagDCon-i i _
      (methsFrom-sel (cdTake 44 KnotD) tagDCon-i
                     (inCD (cdTake 44 KnotD) tagDCon-i tt))
      done))))
  » ⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (step (β _ _) done))))))
  » ⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (step (β _ _) done)))))
  » ⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (step (β _ _) done))))
  » ⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (step (β _ _) done)))
  » ⟶*-appˡ (⟶*-appˡ (step (β _ _) done))
  » ⟶*-appˡ (step (β _ _) done)
  » step (β _ _) done
-- ★ ROW `dρ` — `ihs D ms (dρ C) p =
--     pair (elim D ms (fst p)) (ihs D ms C (snd p))`.
--
-- ★★★ THE FIRST COMPONENT IS EQUAL ON THE NOSE.  `enTm (elim D ms
--   (fst p)) = Tm-elimK ⌈D⌉ ⌈ms⌉ (Tm-fstK ⌈p⌉)`, which is exactly what
--   `ihsRho`'s body builds — no object-level `elim` PROGRAM is involved,
--   only the encoding congruence.  ⇒ all the work is the second.
--
-- ★★★ AND THE CHILD'S INDEX IS `pair sDCon (snd i)`, NOT `i`.  `iihs`
--   hands the recursive field `subTm (isingle i) (pair sDCon (snd (var
--   vz)))`.  THIS is why the statement quantifies the index — a row
--   pinned at `i` could never apply here (`OCC-ATTEMPTS` 28).
ihs-agree {Γ} i D ms (dρ C)   p =
  ⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (⟶*-appˡ
    (ihead-red KnotD ihsMethsK tagDCon-rho i _
      (methsFrom-past (cdTake 44 KnotD) 0 » sel-here _ _)
      done))))
  » ⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (step (β _ _) done))))))
  » ⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (step (β _ _) done)))))
  » ⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (step (β _ _) done))))
  » ⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (step (β _ _) done)))
  » ⟶*-appˡ (⟶*-appˡ (step (β _ _) done))
  » ⟶*-appˡ (step (β _ _) done)
  » step (β _ _) done
  -- ★★ THE SEVEN βs LEAVE A WEAKENING TOWER, one rung per binder the
  --   slot is passed under: `p` none, `ms` one (`wk-single`), `D` two
  --   (`sub-w²-single`), `n` three (`towerJ`), the IH four (`towerJ⁵`).
  --   ⚠ `Knot/Ihs.⊢ihsAppK` pays `towerJ p ms D n` for the very same
  --     slot — the typing side already counted this.
  » ⟶*-castₗ
      (cong₄' (λ nn DD mm ii →
                 Tm-pairK (Tm-elimK DD mm (Tm-fstK (enTm p)))
                          (app (app (app (app (fst ii) nn) DD) mm)
                               (Tm-sndK (enTm p))))
              (towerJ (enTm p) (enTm ms) (enDesc D) (num (len Γ)))
              (sub-w²-single {a = enTm p} {b = enTm ms} (enDesc D))
              (wk-single {v = enTm p} (enTm ms))
              -- ⚠ SPELLED OUT, not `_`.  Left a meta this is
              --   `meta-standing-for-a-computation`: the tower's landing
              --   value is the head-red's own `iihs` term, and nothing
              --   downstream pins it.
              (towerJ⁵ (enTm p) (enTm ms) (enDesc D) (num (len Γ))
                       (iihs KnotD ihsMethsK (isingle i) cDCon-rho
                             (pair (enDCon C)
                                   (pair (idrefl ⌜Nat⌝ sDCon) unit)))))
  -- ★ the IH slot: `fst ihs` off a LITERAL pair (`iihs` computes on the
  --   concrete `cDCon-rho`), then `fst payload` off another.
   (   inPairR (⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (step (βfst _ _) done)))))
  » inPairR (⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (⟶*-appˡ
      (⟶*-ielimᵗ (step (βfst _ _) done))))))
  » inPairR (ihs-agree (pair sDCon (snd i)) D ms C (snd p)))
-- ★ ROW `dκ` — `ihs D ms (dκ A C) p = ihs D ms C (snd p)`: the field is
--   SKIPPED, so there is no `Tm-pairK` and the row IS its own IH.
--
-- ⚠ `cDCon-kap` HAS TWO `iρ` FIELDS — the `Ty` that `ihs` skips and the
--   `DCon` tail — so the IH is `fst (snd ihs)`, one projection deeper
--   than `dρ`'s.  (`Knot/IhsKap`'s header says the same for the typing.)
--
-- ★ AND THE CHILD'S INDEX IS THE SAME `pair sDCon (snd i)`: the tail's
--   code reads `snd (var (vs vz))` under `iext (isingle i) (fst p)`, and
--   `iext σ v (vs x) = σ x` takes that straight back to `i`.
ihs-agree {Γ} i D ms (dκ A C) p =
  ⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (⟶*-appˡ
    (ihead-red KnotD ihsMethsK tagDCon-kap i _
      (methsFrom-past (cdTake 44 KnotD) 1 » sel-there 0 _ _ (sel-here _ _))
      done))))
  » ⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (step (β _ _) done))))))
  » ⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (step (β _ _) done)))))
  » ⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (step (β _ _) done))))
  » ⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (step (β _ _) done)))
  » ⟶*-appˡ (⟶*-appˡ (step (β _ _) done))
  » ⟶*-appˡ (step (β _ _) done)
  » step (β _ _) done
  » ⟶*-castₗ
      (cong₄' (λ nn DD mm ii →
                 app (app (app (app (fst (snd ii)) nn) DD) mm)
                     (Tm-sndK (enTm p)))
              (towerJ (enTm p) (enTm ms) (enDesc D) (num (len Γ)))
              (sub-w²-single {a = enTm p} {b = enTm ms} (enDesc D))
              (wk-single {v = enTm p} (enTm ms))
              (towerJ⁵ (enTm p) (enTm ms) (enDesc D) (num (len Γ))
                       (iihs KnotD ihsMethsK (isingle i) cDCon-kap
                             (pair (enTy A)
                                   (pair (enDCon C)
                                         (pair (idrefl ⌜Nat⌝ sDCon) unit))))))
   (   ⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (⟶*-fst (step (βsnd _ _) done)))))
  » ⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (step (βfst _ _) done))))
  » ⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (⟶*-appˡ
      (⟶*-ielimᵗ (⟶*-fst (step (βsnd _ _) done))))))
  » ⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (⟶*-appˡ
      (⟶*-ielimᵗ (step (βfst _ _) done)))))
  » ihs-agree (pair sDCon (snd i)) D ms C (snd p))

------------------------------------------------------------------------
-- ★★★ THE LEDGER'S OWN NAME — `ihsK`, with the index TIED.
--
-- ⚠ THE ROW STATEMENT AND THIS ONE ARE DIFFERENT STATEMENTS, and
--   conflating them is what `OCC-ATTEMPTS` 28 records as the root error
--   of that whole investigation: the rows QUANTIFY the index because
--   `iihs` hands each child `pair sDCon (snd i)`; only the top-level
--   theorem may tie it, because only here is the scrutinee the caller's.
------------------------------------------------------------------------

open import DirectedHoTT.Examples.Knot.Ihs using ( ihsK; fieldsK )

ihsK-agree : {Γ Θ : Cx} (D : Desc) (ms : RTm Γ) (C : DCon) (p : RTm Γ) →
             ihsK {Θ} (num (len Γ)) (enDCon C) (enDesc D) (enTm ms) (enTm p)
             ⟶* enTm {Γ} {Θ} (ihs D ms C p)
ihsK-agree {Γ} D ms C p = ihs-agree (pair sDCon (num (len Γ))) D ms C p

------------------------------------------------------------------------
-- ★★★ AND `fieldsK`, WHICH ITS LEDGER ENTRY CALLED CORRECTLY:
--   *"a COROLLARY, NOT NEW CONTENT … two `Tm-appK` congruences over
--     `ihsK`'s.  ⇒ BLOCKED ON `ihsK` — discharge that and this follows;
--     there is no separate induction to do."*
--
--     fields D ms C m p = app (app m p) (ihs D ms C p)   -- `Spec/Syntax:1000`
--
-- ★ ONE congruence, not two: `app (app m p) _` is a `Tm-appK` whose
--   FIRST argument is already the answer, so only the second descends.
------------------------------------------------------------------------

open import DirectedHoTT.Spec.Syntax using ( fields )
open import DirectedHoTT.Examples.Knot.Ctors using ( Tm-appK )

inAppR : {Γ : Cx} {a b b' : RTm Γ} → b ⟶* b' → Tm-appK a b ⟶* Tm-appK a b'
inAppR r = ⟶*-icon (⟶*-pairʳ (⟶*-pairˡ r))

fieldsK-agree : {Γ Θ : Cx} (D : Desc) (ms : RTm Γ) (C : DCon) (m p : RTm Γ) →
                fieldsK {Θ} (num (len Γ)) (enDesc D) (enTm ms) (enDCon C)
                        (enTm m) (enTm p)
                ⟶* enTm {Γ} {Θ} (fields D ms C m p)
fieldsK-agree D ms C m p = inAppR (ihsK-agree D ms C p)
