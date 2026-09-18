------------------------------------------------------------------------
-- OCP-0009 · KNOT — ★★★ `iihsK` AND `ifieldsK` AGREE WITH `iihs`/`ifields`.
--
--   iihsK-agree    : iihsK ⌈|Γ|⌉ ⌈|Δ|⌉ ⌈D⌉ ⌈ms⌉ s ⌈C⌉ ⌈p⌉
--                      ⟶* ⌈ iihs D ms σ C p ⌉        (given Represents σ s)
--   ifieldsK-agree : … ⟶* ⌈ ifields D i ms σ C m p ⌉
--
-- Discharges the last two entries of the `ι-ielim` chain.  `ihs-agree`'s
-- shape plus the two things indexing adds — a `Represents` hypothesis
-- that GROWS (`iext-Represents`) and a recursive index that is
-- substituted (`sub-agree`).  `IHS-ATTEMPTS.md` §5 has the log.
--
--   iihs D ms σ iι       p = unit
--   iihs D ms σ (iρ j C) p = pair (ielim D (subTm σ j) ms (fst p))
--                                 (iihs D ms (iext σ (fst p)) C (snd p))
--   iihs D ms σ (iκ κ C) p = iihs D ms (iext σ (fst p)) C (snd p)
--
-- ★ `ihs-agree`'s shape with TWO additions, and both are what indexing
--   means here: the SUBSTITUTION rides as a `Represents` hypothesis, and
--   the `iρ` row's recursive index is `subTm σ j` — so the row composes
--   `sub-agree` where `ihs`'s composed nothing.
--
-- ★★★ THE INDEX IS PINNED HERE, AND THAT IS NOT `OCC-ATTEMPTS` 28's
--   MISTAKE.  `iihsRho` READS the index (`snd ⟨i⟩` is the ICon's own
--   depth), so quantifying it away is not available.  What made pinning
--   fatal for `occ` was that the child's index is a term the row cannot
--   control (`subTm (isingle i) …`).  Here it IS controllable:
--   `cICon-rho`'s tail sits at `pair sICon (nsuc (snd ⟨i⟩))`, so with
--   `⟨i⟩ = pair sICon ⌈|Δ|⌉` one `βsnd` under `⟶*-ielimⁱ` takes the
--   child to `pair sICon ⌈|Δ ∙|⌉` — the IH's own form, since
--   `len (Δ ∙) = suc (len Δ)` is DEFINITIONAL.
--   ⇒ the rule is not "never pin"; it is "pin only what the child can
--     be REDUCED to".
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Knot.IihsAgree where

open import DirectedHoTT.Spec.Syntax
  using ( Cx; _∙; RTm; Sub; IDesc; ICon; iι; iρ; iκ; iihs; app; ielim; pair; snd )
open import DirectedHoTT.Spec.Typing using ( _⟶*_; done; step; β )
open import DirectedHoTT.Lib.RedChain using ( _»_ )
open import DirectedHoTT.Metatheory.RedCong using ( ⟶*-appˡ )
open import DirectedHoTT.Lib.IHeadRed using ( ihead-red )
open import DirectedHoTT.Lib.IMeths
  using ( cdTake; methsFrom-sel; methsFrom-past; sel-here; sel-there; inCD; tt )
open import DirectedHoTT.Examples.Knot.Tags using ( tagICon-i; tagICon-rho; tagICon-kap )
open import DirectedHoTT.Examples.Knot.Sorts using ( sICon )
open import DirectedHoTT.Spec.Syntax using ( var; vz; vs; subTm; extS; fst; nsuc )
open import DirectedHoTT.Spec.Typing using ( single; wk-single; βfst; βsnd )
open import DirectedHoTT.Lib.Wk
  using ( pw^; towerJ; towerJ⁵; sub-w²-single; cong₄; cong₅; cong₆ )
open import DirectedHoTT.Spec.Syntax
  using ( Sub; iihs; isingle; idrefl; ⌜Nat⌝; unit; lam )
open import DirectedHoTT.Examples.Knot.Desc using ( cICon-rho; cICon-kap )
open import DirectedHoTT.Lib.ICast using ( ⟶*-castₗ; ⟶*-castᵣ )
open import DirectedHoTT.Metatheory.RedCong
  using ( ⟶*-icon; ⟶*-pairˡ; ⟶*-pairʳ; ⟶*-ielimᵗ; ⟶*-ielimⁱ; ⟶*-fst; ⟶*-nsuc )
open import normalizer.Syntax.Types using ( _≡_; refl; cong; trans )
open import DirectedHoTT.Examples.Knot.Ctors using ( Tm-fstK; Tm-sndK )
open import DirectedHoTT.Examples.Knot.IExt using ( iextK )
open import DirectedHoTT.Examples.Knot.IExtRep
  using ( iext-Represents; ⟶*-subTmAtK; ⟶*-subTmAtKᵈ; iextK-sub; subTmAtK-sub )
open import DirectedHoTT.Examples.Knot.SubAgreeTie using ( sub-agree )
open import DirectedHoTT.Examples.Knot.SubApp using ( subTmAtK )
open import DirectedHoTT.Examples.Knot.Ctors using ( Tm-pairK; Tm-ielimK )

-- ★ the two descents into `Tm-pairK`, and the three into `Tm-ielimK`.
inPairL : {Γ : Cx} {a a' b : RTm Γ} → a ⟶* a' → Tm-pairK a b ⟶* Tm-pairK a' b
inPairL r = ⟶*-icon (⟶*-pairˡ r)

inPairR : {Γ : Cx} {a b b' : RTm Γ} → b ⟶* b' → Tm-pairK a b ⟶* Tm-pairK a b'
inPairR r = ⟶*-icon (⟶*-pairʳ (⟶*-pairˡ r))

inIelim0 : {Γ : Cx} {a a' b c d : RTm Γ} →
           a ⟶* a' → Tm-ielimK a b c d ⟶* Tm-ielimK a' b c d
inIelim0 r = ⟶*-icon (⟶*-pairˡ r)

inIelim1 : {Γ : Cx} {a b b' c d : RTm Γ} →
           b ⟶* b' → Tm-ielimK a b c d ⟶* Tm-ielimK a b' c d
inIelim1 r = ⟶*-icon (⟶*-pairʳ (⟶*-pairˡ r))

inIelim2 : {Γ : Cx} {a b c c' d : RTm Γ} →
           c ⟶* c' → Tm-ielimK a b c d ⟶* Tm-ielimK a b c' d
inIelim2 r = ⟶*-icon (⟶*-pairʳ (⟶*-pairʳ (⟶*-pairˡ r)))

------------------------------------------------------------------------
-- ★★★ THE SEVEN-FOLD NATURALITY LIFTER.
--
-- ⚠ THE βs APPLY SEVEN SUBSTITUTIONS, and a method body that CALLS a
--   `lam`-building program meets every one of them.  `iextK` and
--   `subTmAtK` are both such calls and both are 4-ary, so the lift is
--   ONE lemma taking the program's own naturality as a hypothesis.
--   ⇒ `abstract-the-substituted-terms`: the seven substitutions stay
--     abstract and the program stays a parameter, so nothing unfolds.
------------------------------------------------------------------------

nat7 : (F : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ → RTm Γ → RTm Γ) →
       ({Γ Δ : Cx} (τ : Sub Γ Δ) (a b c d : RTm Γ) →
          subTm τ (F a b c d) ≡ F (subTm τ a) (subTm τ b) (subTm τ c) (subTm τ d)) →
       {Γ0 Γ1 Γ2 Γ3 Γ4 Γ5 Γ6 Γ7 : Cx}
       (τ0 : Sub Γ1 Γ0) (τ1 : Sub Γ2 Γ1) (τ2 : Sub Γ3 Γ2) (τ3 : Sub Γ4 Γ3)
       (τ4 : Sub Γ5 Γ4) (τ5 : Sub Γ6 Γ5) (τ6 : Sub Γ7 Γ6)
       (a b c d : RTm Γ7) →
       subTm τ0 (subTm τ1 (subTm τ2 (subTm τ3 (subTm τ4 (subTm τ5 (subTm τ6 (F a b c d)))))))
       ≡ F (subTm τ0 (subTm τ1 (subTm τ2 (subTm τ3 (subTm τ4 (subTm τ5 (subTm τ6 a)))))))
           (subTm τ0 (subTm τ1 (subTm τ2 (subTm τ3 (subTm τ4 (subTm τ5 (subTm τ6 b)))))))
           (subTm τ0 (subTm τ1 (subTm τ2 (subTm τ3 (subTm τ4 (subTm τ5 (subTm τ6 c)))))))
           (subTm τ0 (subTm τ1 (subTm τ2 (subTm τ3 (subTm τ4 (subTm τ5 (subTm τ6 d)))))))
nat7 F hF τ0 τ1 τ2 τ3 τ4 τ5 τ6 a b c d =
  trans (cong (λ z → subTm τ0 (subTm τ1 (subTm τ2 (subTm τ3 (subTm τ4 (subTm τ5 z))))))
              (hF τ6 a b c d))
  (trans (cong (λ z → subTm τ0 (subTm τ1 (subTm τ2 (subTm τ3 (subTm τ4 z)))))
               (hF τ5 _ _ _ _))
  (trans (cong (λ z → subTm τ0 (subTm τ1 (subTm τ2 (subTm τ3 z))))
               (hF τ4 _ _ _ _))
  (trans (cong (λ z → subTm τ0 (subTm τ1 (subTm τ2 z)))
               (hF τ3 _ _ _ _))
  (trans (cong (λ z → subTm τ0 (subTm τ1 z)) (hF τ2 _ _ _ _))
  (trans (cong (subTm τ0) (hF τ1 _ _ _ _))
         (hF τ0 _ _ _ _))))))

------------------------------------------------------------------------
-- ★ TWO DEEPER TOWERS.  `Lib/Wk` stops at `towerJ⁵` (de Bruijn 4) and
--   its own header says these *"are iterates of one lemma and want
--   INDEXING, not listing"*.  `iihsRho` reads the PAYLOAD at 5 and the
--   ambient INDEX at 6, so the list needs two more entries — written the
--   same way, as `pw^` counted down.
--   ⬜ They belong in `Lib/Wk` beside the others, and the indexed form
--     belongs there more; left local pending a second customer
--     (`judge-abstractions-at-the-use-site`).
------------------------------------------------------------------------

tower⁶ : {Γ : Cx} (a b c d e J : RTm Γ) →
         subTm (single a)
           (subTm (extS (single b))
             (subTm (extS (extS (single c)))
               (subTm (extS (extS (extS (single d))))
                 (subTm (extS (extS (extS (extS (single e)))))
                   (subTm (extS (extS (extS (extS (extS (single J))))))
                          (var (vs (vs (vs (vs (vs vz)))))))))))
         ≡ J
tower⁶ a b c d e J =
  trans (cong (λ z → subTm (single a) (subTm (extS (single b))
                       (subTm (extS (extS (single c)))
                         (subTm (extS (extS (extS (single d)))) z))))
              (pw^ {u = e} 4 J))
  (trans (cong (λ z → subTm (single a) (subTm (extS (single b))
                        (subTm (extS (extS (single c))) z)))
               (pw^ {u = d} 3 J))
  (trans (cong (λ z → subTm (single a) (subTm (extS (single b)) z))
               (pw^ {u = c} 2 J))
  (trans (cong (subTm (single a)) (pw^ {u = b} 1 J))
         (wk-single {v = a} J))))

tower⁷ : {Γ : Cx} (a b c d e f J : RTm Γ) →
         subTm (single a)
           (subTm (extS (single b))
             (subTm (extS (extS (single c)))
               (subTm (extS (extS (extS (single d))))
                 (subTm (extS (extS (extS (extS (single e)))))
                   (subTm (extS (extS (extS (extS (extS (single f))))))
                     (subTm (extS (extS (extS (extS (extS (extS (single J)))))))
                            (var (vs (vs (vs (vs (vs (vs vz))))))))))))) ≡ J
tower⁷ a b c d e f J =
  trans (cong (λ z → subTm (single a) (subTm (extS (single b))
                       (subTm (extS (extS (single c)))
                         (subTm (extS (extS (extS (single d))))
                           (subTm (extS (extS (extS (extS (single e))))) z)))))
              (pw^ {u = f} 5 J))
  (trans (cong (λ z → subTm (single a) (subTm (extS (single b))
                        (subTm (extS (extS (single c)))
                          (subTm (extS (extS (extS (single d)))) z))))
               (pw^ {u = e} 4 J))
  (trans (cong (λ z → subTm (single a) (subTm (extS (single b))
                        (subTm (extS (extS (single c))) z)))
               (pw^ {u = d} 3 J))
  (trans (cong (λ z → subTm (single a) (subTm (extS (single b)) z))
               (pw^ {u = c} 2 J))
  (trans (cong (subTm (single a)) (pw^ {u = b} 1 J))
         (wk-single {v = a} J)))))
open import DirectedHoTT.Lib.NatNum using ( num )
open import DirectedHoTT.Examples.Knot.Sorts using ( len )
open import DirectedHoTT.Examples.Knot.Desc using ( KnotD )
open import DirectedHoTT.Examples.Knot.Map using ( enTm; enIDesc; enICon )
open import DirectedHoTT.Examples.Knot.IihsMeths using ( iihsMethsK )
open import DirectedHoTT.Examples.Knot.SubAgree using ( Represents )

iihs-agree : {Γ Δ Θ : Cx} (D : IDesc) (ms : RTm Γ) {σ : Sub Δ Γ} {s : RTm Θ} →
             Represents σ s → (C : ICon Δ) (p : RTm Γ) →
             app (app (app (app (ielim KnotD (pair sICon (num (len Δ)))
                                       iihsMethsK (enICon C))
                                (num (len Γ)))
                           s)
                      (pair (enIDesc D) (enTm ms)))
                 (enTm p)
             ⟶* enTm {Γ} {Θ} (iihs D ms σ C p)

-- ★ ROW `iι` — `iihs D ms σ iι p = unit`, and tag 48 sits INSIDE
--   `methsFrom`'s 49-row prefix, so the junk method IS the right answer
--   (`ihs-agree`'s `dι` one description over).
iihs-agree D ms h iι       p =
  ⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (⟶*-appˡ
    (ihead-red KnotD iihsMethsK tagICon-i (pair sICon (num (len _))) _
      (methsFrom-sel (cdTake 49 KnotD) tagICon-i
                     (inCD (cdTake 49 KnotD) tagICon-i tt))
      done))))
  » ⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (step (β _ _) done))))))
  » ⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (step (β _ _) done)))))
  » ⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (step (β _ _) done))))
  » ⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (step (β _ _) done)))
  » ⟶*-appˡ (⟶*-appˡ (step (β _ _) done))
  » ⟶*-appˡ (step (β _ _) done)
  » step (β _ _) done
-- ★ ROW `iρ` — `iihs D ms σ (iρ j C) p =
--     pair (ielim D (subTm σ j) ms (fst p)) (iihs D ms (iext σ (fst p)) C (snd p))`.
--
-- ★★★ THIS IS WHERE THE INDEXED SIDE COMPOSES ANOTHER PROGRAM.  `ihs`'s
--   `dρ` row built `Tm-elimK ⌈D⌉ ⌈ms⌉ (Tm-fstK ⌈p⌉)` — encoding
--   congruences only.  Here the recursive index is `subTm σ j`, so the
--   row runs `subTmAtK` and its agreement is `Knot/SubAgreeTie.sub-agree`.
--   ⇒ the ledger entry's *"its adequacy is `ihsK`'s PLUS the commutation
--     of `iextK` and `subTmAtK`"* is exactly right, and both are now
--     discharged.
--
-- ⚠ SIX TOWER SLOTS: the `iρ` row reads the PAYLOAD (de Bruijn 5) as
--   well as the ambient INDEX (6), where `iκ` reads only the index.
iihs-agree {Γ} {Δ} {Θ} D ms {σ = σ} {s = s} h (iρ j C) p =
  ⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (⟶*-appˡ
    (ihead-red KnotD iihsMethsK tagICon-rho (pair sICon (num (len Δ))) _
      (methsFrom-past (cdTake 49 KnotD) 0 » sel-here _ _)
      done))))
  » ⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (step (β _ _) done))))))
  » ⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (step (β _ _) done)))))
  » ⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (step (β _ _) done))))
  » ⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (step (β _ _) done)))
  » ⟶*-appˡ (⟶*-appˡ (step (β _ _) done))
  » ⟶*-appˡ (step (β _ _) done)
  » step (β _ _) done
  -- ★★ TWO CALLS, TWO SLOTS.  `subTmAtK` hides `subMethsK` and `iextK`
  --   builds a `lam`; neither survives the βs as an ambient tower, and
  --   `nat7` lifts both out by their own naturality.
  » ⟶*-castₗ
      (cong₅ (λ nn aa ii tt' ee →
                 Tm-pairK
                   (Tm-ielimK (fst aa) tt' (snd aa) (Tm-fstK (enTm p)))
                   (app (app (app (app (fst (snd ii)) nn) ee) aa)
                        (Tm-sndK (enTm p))))
              (towerJ (enTm p) (pair (enIDesc D) (enTm ms)) s (num (len Γ)))
              (wk-single {v = enTm p} (pair (enIDesc D) (enTm ms)))
              (towerJ⁵ (enTm p) (pair (enIDesc D) (enTm ms)) s (num (len Γ)) IHS)
              (trans (nat7 subTmAtK subTmAtK-sub T0 T1 T2 T3 T4 T5 T6
                                  (snd (var (vs (vs (vs (vs (vs (vs vz))))))))
                                  (var (vs (vs (vs vz)))) (var (vs (vs vz)))
                                  (fst (var (vs (vs (vs (vs (vs vz))))))))
                     (cong₄ subTmAtK
                            (cong snd (tower⁷ (enTm p) (pair (enIDesc D) (enTm ms))
                                              s (num (len Γ)) IHS PAY IX))
                            (towerJ (enTm p) (pair (enIDesc D) (enTm ms)) s (num (len Γ)))
                            (sub-w²-single {a = enTm p}
                                           {b = pair (enIDesc D) (enTm ms)} s)
                            (cong fst (tower⁶ (enTm p) (pair (enIDesc D) (enTm ms))
                                              s (num (len Γ)) IHS PAY))))
              (trans (nat7 iextK iextK-sub T0 T1 T2 T3 T4 T5 T6
                                  (snd (var (vs (vs (vs (vs (vs (vs vz))))))))
                                  (var (vs (vs (vs vz)))) (var (vs (vs vz)))
                                  (Tm-fstK (var vz)))
                     (cong₄ iextK
                            (cong snd (tower⁷ (enTm p) (pair (enIDesc D) (enTm ms))
                                              s (num (len Γ)) IHS PAY IX))
                            (towerJ (enTm p) (pair (enIDesc D) (enTm ms)) s (num (len Γ)))
                            (sub-w²-single {a = enTm p}
                                           {b = pair (enIDesc D) (enTm ms)} s)
                            refl)))
   (   -- ★ the FIRST component: three projections and `sub-agree`.
       inPairL (inIelim0 (step (βfst _ _) done))
  » inPairL (inIelim2 (step (βsnd _ _) done))
  » inPairL (inIelim1 (⟶*-subTmAtKᵈ (step (βsnd _ _) done)))
  » inPairL (inIelim1 (⟶*-subTmAtK (step (βfst _ _) done)))
  » inPairL (inIelim1 (sub-agree h j))
       -- ★ the SECOND: `ihs-agree`'s IH chain, plus the index peel that
       --   takes the child from `nsuc (snd ⟨i⟩)` to `⌈|Δ ∙|⌉`.
  » inPairR (⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (⟶*-fst (step (βsnd _ _) done))))))
  » inPairR (⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (step (βfst _ _) done)))))
  » inPairR (⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (⟶*-appˡ
      (⟶*-ielimⁱ (⟶*-pairʳ (⟶*-nsuc (step (βsnd _ _) done))))))))
  » inPairR (⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (⟶*-appˡ
      (⟶*-ielimᵗ (⟶*-fst (step (βsnd _ _) done)))))))
  » inPairR (⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (⟶*-appˡ
      (⟶*-ielimᵗ (step (βfst _ _) done))))))
  » inPairR (iihs-agree D ms (iext-Represents (snd (pair sICon (num (len Δ))))
                                              (fst p) h) C (snd p)))
      where
        -- ⚠ EVERY SLOT SPELLED OUT.  Left as `_` this clause reported
        --   UNSOLVED METAS and not one type error — which by
        --   `typing-lemma-already-counted-the-tower` means the chain is
        --   right and only the landing values are unnamed.  The seven
        --   substitutions are the βs' own, innermost-first.
        PAY : RTm Θ
        PAY = pair (enTm j) (pair (enICon C) (pair (idrefl ⌜Nat⌝ sICon) unit))
        IX  : RTm Θ
        IX  = pair sICon (num (len Δ))
        IHS : RTm Θ
        IHS = iihs KnotD iihsMethsK (isingle IX) cICon-rho PAY
        T0 : Sub (Θ ∙) Θ
        T0 = single (enTm p)
        T1 : Sub ((Θ ∙) ∙) (Θ ∙)
        T1 = extS (single (pair (enIDesc D) (enTm ms)))
        T2 : Sub (((Θ ∙) ∙) ∙) ((Θ ∙) ∙)
        T2 = extS (extS (single s))
        T3 : Sub ((((Θ ∙) ∙) ∙) ∙) (((Θ ∙) ∙) ∙)
        T3 = extS (extS (extS (single (num (len Γ)))))
        T4 : Sub (((((Θ ∙) ∙) ∙) ∙) ∙) ((((Θ ∙) ∙) ∙) ∙)
        T4 = extS (extS (extS (extS (single IHS))))
        T5 : Sub ((((((Θ ∙) ∙) ∙) ∙) ∙) ∙) (((((Θ ∙) ∙) ∙) ∙) ∙)
        T5 = extS (extS (extS (extS (extS (single PAY)))))
        T6 : Sub (((((((Θ ∙) ∙) ∙) ∙) ∙) ∙) ∙) ((((((Θ ∙) ∙) ∙) ∙) ∙) ∙)
        T6 = extS (extS (extS (extS (extS (extS (single IX))))))
-- ★ ROW `iκ` — `iihs D ms σ (iκ κ C) p = iihs D ms (iext σ (fst p)) C
--   (snd p)`: the field is skipped and the row IS its own IH, at the
--   EXTENDED substitution.  That extension is the whole content of
--   indexing here, and `Knot/IExtRep.iext-Represents` is exactly it.
--
-- ⚠ `cICon-kap` HAS TWO `iρ` FIELDS (the `Tm` and the `ICon` tail), so
--   the IH is `fst (snd ihs)` — `Knot/IihsKap`'s header says the same.
iihs-agree {Γ} {Δ} {Θ} D ms {σ = σ} {s = s} h (iκ κ C) p =
  ⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (⟶*-appˡ
    (ihead-red KnotD iihsMethsK tagICon-kap (pair sICon (num (len Δ))) _
      (methsFrom-past (cdTake 49 KnotD) 1 » sel-there 0 _ _ (sel-here _ _))
      done))))
  » ⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (step (β _ _) done))))))
  » ⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (step (β _ _) done)))))
  » ⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (step (β _ _) done))))
  » ⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (step (β _ _) done)))
  » ⟶*-appˡ (⟶*-appˡ (step (β _ _) done))
  » ⟶*-appˡ (step (β _ _) done)
  » step (β _ _) done
  -- ★★ THE `iextK` CALL IS **ONE SLOT**, not four.  Its arguments sit
  --   under `iextK`'s own `lam`, so the βs reach them one binder deeper
  --   than the ambient slots and no ambient tower describes them.
  --   `nat7 iextK iextK-sub` lifts `iextK` out first; then the ordinary
  --   towers apply to its arguments.
  » ⟶*-castₗ
      (cong₄ (λ nn aa ii ee →
                 app (app (app (app (fst (snd ii)) nn) ee) aa)
                     (Tm-sndK (enTm p)))
              (towerJ (enTm p) (pair (enIDesc D) (enTm ms)) s (num (len Γ)))
              (wk-single {v = enTm p} (pair (enIDesc D) (enTm ms)))
              (towerJ⁵ (enTm p) (pair (enIDesc D) (enTm ms)) s (num (len Γ)) IHS)
              (trans (nat7 iextK iextK-sub T0 T1 T2 T3 T4 T5 T6
                                  (snd (var (vs (vs (vs (vs (vs (vs vz)))))))) 
                                  (var (vs (vs (vs vz)))) (var (vs (vs vz)))
                                  (Tm-fstK (var vz)))
                     (cong₄ iextK
                            (cong snd (tower⁷ (enTm p) (pair (enIDesc D) (enTm ms))
                                              s (num (len Γ)) IHS PAY IX))
                            (towerJ (enTm p) (pair (enIDesc D) (enTm ms)) s (num (len Γ)))
                            (sub-w²-single {a = enTm p}
                                           {b = pair (enIDesc D) (enTm ms)} s)
                            refl)))
   (   ⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (⟶*-fst (step (βsnd _ _) done)))))
  » ⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (step (βfst _ _) done))))
  » ⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (⟶*-appˡ
      (⟶*-ielimⁱ (⟶*-pairʳ (⟶*-nsuc (step (βsnd _ _) done)))))))
  » ⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (⟶*-appˡ
      (⟶*-ielimᵗ (⟶*-fst (step (βsnd _ _) done))))))
  » ⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (⟶*-appˡ
      (⟶*-ielimᵗ (step (βfst _ _) done)))))
  » iihs-agree D ms (iext-Represents (snd (pair sICon (num (len Δ))))
                                     (fst p) h) C (snd p))
      where
        -- ⚠ EVERY SLOT SPELLED OUT.  Left as `_` this clause reported
        --   UNSOLVED METAS and not one type error — which by
        --   `typing-lemma-already-counted-the-tower` means the chain is
        --   right and only the landing values are unnamed.  The seven
        --   substitutions are the βs' own, innermost-first.
        PAY : RTm Θ
        PAY = pair (enTm κ) (pair (enICon C) (pair (idrefl ⌜Nat⌝ sICon) unit))
        IX  : RTm Θ
        IX  = pair sICon (num (len Δ))
        IHS : RTm Θ
        IHS = iihs KnotD iihsMethsK (isingle IX) cICon-kap PAY
        T0 : Sub (Θ ∙) Θ
        T0 = single (enTm p)
        T1 : Sub ((Θ ∙) ∙) (Θ ∙)
        T1 = extS (single (pair (enIDesc D) (enTm ms)))
        T2 : Sub (((Θ ∙) ∙) ∙) ((Θ ∙) ∙)
        T2 = extS (extS (single s))
        T3 : Sub ((((Θ ∙) ∙) ∙) ∙) (((Θ ∙) ∙) ∙)
        T3 = extS (extS (extS (single (num (len Γ)))))
        T4 : Sub (((((Θ ∙) ∙) ∙) ∙) ∙) ((((Θ ∙) ∙) ∙) ∙)
        T4 = extS (extS (extS (extS (single IHS))))
        T5 : Sub ((((((Θ ∙) ∙) ∙) ∙) ∙) ∙) (((((Θ ∙) ∙) ∙) ∙) ∙)
        T5 = extS (extS (extS (extS (extS (single PAY)))))
        T6 : Sub (((((((Θ ∙) ∙) ∙) ∙) ∙) ∙) ∙) ((((((Θ ∙) ∙) ∙) ∙) ∙) ∙)
        T6 = extS (extS (extS (extS (extS (extS (single IX))))))

------------------------------------------------------------------------
-- ★★★ THE LEDGER'S OWN NAMES — `iihsK` and `ifieldsK`.
--
--     iihsK n dd D ms σ C p
--       = app (app (app (app (ielim KnotD (pair sICon dd) iihsMethsK C) n) σ)
--                  (pair D ms)) p
--
-- ★ `dd` IS `⌈|Δ|⌉` HERE AND NOWHERE ELSE.  The rows quantify over `Δ`
--   and the eliminator's index is built from it, so tying it is exactly
--   what the wrapper does.
------------------------------------------------------------------------

open import DirectedHoTT.Examples.Knot.Iihs using ( iihsK; ifieldsK )
open import DirectedHoTT.Spec.Syntax using ( ifields )
open import DirectedHoTT.Examples.Knot.Ctors using ( Tm-appK )

iihsK-agree : {Γ Δ Θ : Cx} (D : IDesc) (ms : RTm Γ) {σ : Sub Δ Γ} {s : RTm Θ} →
              Represents σ s → (C : ICon Δ) (p : RTm Γ) →
              iihsK {Θ} (num (len Γ)) (num (len Δ)) (enIDesc D) (enTm ms) s
                    (enICon C) (enTm p)
              ⟶* enTm {Γ} {Θ} (iihs D ms σ C p)
iihsK-agree D ms h C p = iihs-agree D ms h C p

------------------------------------------------------------------------
-- ★★★ AND `ifieldsK` — the ledger called it, as it called `fieldsK`:
--   *"THE SAME COROLLARY ONE DESCRIPTION OVER … THREE `Tm-appK`
--     congruences over `iihsK`'s.  ⇒ BLOCKED ON `iihsK`."*
--
--     ifields D i ms σ C m p = app (app (app m i) p) (iihs D ms σ C p)
--
-- ★ ONE congruence, not three — same correction as `fieldsK`: the inner
--   `app (app m i) p` is ALREADY the answer, so only the last argument
--   descends.  ⚠ `ifieldsK` fixes the ICon's depth to `num 1` in
--   `Knot/KAdapt`; here the wrapper is used at its GENERAL depth, which
--   is why this states `ifieldsK` directly and not the adapter.
------------------------------------------------------------------------

inAppR : {Γ : Cx} {a b b' : RTm Γ} → b ⟶* b' → Tm-appK a b ⟶* Tm-appK a b'
inAppR r = ⟶*-icon (⟶*-pairʳ (⟶*-pairˡ r))

ifieldsK-agree :
  {Γ Δ Θ : Cx} (D : IDesc) (i ms : RTm Γ) {σ : Sub Δ Γ} {s : RTm Θ} →
  Represents σ s → (C : ICon Δ) (m p : RTm Γ) →
  ifieldsK {Θ} (num (len Γ)) (num (len Δ)) (enIDesc D) (enTm i) (enTm ms) s
           (enICon C) (enTm m) (enTm p)
  ⟶* enTm {Γ} {Θ} (ifields D i ms σ C m p)
ifieldsK-agree D i ms h C m p = inAppR (iihsK-agree D ms h C p)
