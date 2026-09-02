------------------------------------------------------------------------
-- OCP-0009 · EXAMPLES — ★★★ `payTy`, OBJECT-LEVEL.
--
--     payTy : Desc → DCon → RTy Γ           `Spec/Syntax:1068`
--     payTy D dι       = Unit
--     payTy D (dρ C)   = Σ' (Mu D)    (payTy D C)
--     payTy D (dκ A C) = Σ' (εwkTy A) (payTy D C)
--
-- ⚠ `⊢con`'s payload premise names it, together with `lookupD`.
--
-- ★★★ `D` RIDES IN THE MOTIVE, and that is a decision.  It is a
--   PARAMETER of the recursion (the walk is on the `DCon`), so it could
--   equally be a free variable of the method tuple — but then every
--   method would have to weaken it past `⊢methLam`'s three binders, and
--   every typing would pay three `⊢wk`s for it.  Putting it in the
--   motive makes it `var vz` inside each method instead, and the
--   recursive field's IH becomes a FUNCTION applied to `D`.
--   ⇒ the same move `lookupD` makes for its ℕ, for the same reason.
--
-- ★ THE MOTIVE READS THE INDEX (`snd ⟨i⟩` in both halves), so unlike
--   `Knot/ILookupD` this one WILL pay the `βsnd` conversion — that is
--   what an index-dependent motive costs, and `Knot/ILookupD`'s header
--   records the contrast.
--
-- ⚠ AND THE SECOND Σ COMPONENT SITS ONE BINDER DEEPER.  `Σ' A B` has
--   `B : RTy (Γ ∙)` while the IH answers at the ambient depth, so each
--   recursive answer is weakened by `wkK`.  `dκ`'s field type is an
--   `RTy ε` (`KNOT`: `rec("sTy", lit 0)`), so it needs `εwkK` — the
--   0 → n direction, which is exactly what `Knot/EWk` is for.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Knot.PayTy where
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax
  using ( Cx; ε; _∙; vz; vs; RTy; RTm; var; lam; snd; pair; Π; Nat
        ; ICon; IDesc; εwkTy; IMu; app; fst; iρ; iκ; iι
        ; ⌜Id⌝; ⌜Nat⌝; isingle; iext; unit; _◂_; ielim; nzero; subTm )
open import DirectedHoTT.Spec.Typing
  using ( Ctx; ◇; _▹_; ⌊_⌋; _⊢_∷_; _⊢ty_; ⊢var; here; there
        ; ⊢snd; ⊢lam; ty-Π; ty-IMu; IConWf; imethTy
        ; ⊢app; ⊢fst; ⊢unit; imethsTy; imethsTyFrom; IDescWfFrom; ⊢ielim
        ; ξ-pairʳ; βsnd; done; step; single; wk-single )
open import DirectedHoTT.Lib.Wk using ( sub-w-single )
open import DirectedHoTT.Metatheory.SubjectReduction using ( ⊢-cast )
open import normalizer.Syntax.Types using ( cong; trans; sym )
open import DirectedHoTT.Lib.IPay
  using ( ⊢methLam; ⊢ihHere; ⊢ihSkipρ; ⊢methsFrom; ⊢methsCons
        ; idwfDrop; splTake; Split; spl-nil; spl-step )
open import DirectedHoTT.Lib.IMeths using ( cdTake; cdRest; methsFrom )
open import DirectedHoTT.Examples.Knot.Sorts
  using ( IPair; ⊢IPair; sTy; ⊢sTy; sDesc; ⊢sDesc; sDCon; ⊢sDCon; ⊢ixP )
open import DirectedHoTT.Examples.Knot.Desc using ( KnotD; K )
open import DirectedHoTT.Examples.Knot.Wf using ( KnotWf )
open import DirectedHoTT.Examples.Knot.Ctors using ( Ty-UnitK; Ty-SgK; Ty-MuK )
open import DirectedHoTT.Examples.Knot.CtorsV using ( ⊢Ty-UnitKv; ⊢Ty-SgKv; ⊢Ty-MuKv )
open import DirectedHoTT.Examples.Knot.Wk using ( wkK; ⊢wkKat )
open import DirectedHoTT.Lib.ICast using ( muFwd; muBwd* )
open import DirectedHoTT.Examples.Knot.Desc using ( cDCon-rho; cDCon-kap )
open import DirectedHoTT.Examples.Knot.Wf using ( cDCon-rhoWf; cDCon-kapWf )
open import DirectedHoTT.Examples.Knot.EWk using ( εwkK; ⊢εwkK )
open import DirectedHoTT.Examples.Knot.SubMot using ( sortMap-ty )
open import DirectedHoTT.Examples.Knot.Tags using ( tagDCon-rho; tagDCon-kap )

------------------------------------------------------------------------
-- ★ THE MOTIVE — `Knot/Single`'s shape: a `Π` whose domain is the
--   parameter and whose codomain is the answer, both at `snd ⟨i⟩`.
------------------------------------------------------------------------

payTyMotK : {Γ : Cx} → RTy ((Γ ∙) ∙)
payTyMotK =
  Π (IMu KnotD IPair (pair sDesc (snd (var (vs vz)))))
    (IMu KnotD IPair (pair sTy (snd (var (vs (vs vz))))))

⊢payTyMotK : {Γ : Ctx} →
             ((Γ ▹ εwkTy IPair) ▹ IMu KnotD IPair (var vz)) ⊢ty payTyMotK
⊢payTyMotK =
  ty-Π (ty-IMu KnotWf (⊢ixP ⊢sDesc (⊢snd (⊢var (there here)))))
       (ty-IMu KnotWf (⊢ixP ⊢sTy (⊢snd (⊢var (there (there here))))))

------------------------------------------------------------------------
-- ★ THE CONSTANT ROWS.  ⚠ `dι`'s own answer IS `Unit`, so the junk
--   method serves it too — 51 junk rows and TWO real ones (`dρ`, `dκ`),
--   which are ADJACENT at 44 and 45.
------------------------------------------------------------------------

payTyJunk : {Γ : Cx} → RTm Γ
payTyJunk = lam (lam (lam (lam Ty-UnitK)))

⊢payTyJunk : {Γ : Ctx} (k : ℕ) (C : ICon (ε ∙)) →
             IConWf KnotD IPair (◇ ▹ εwkTy IPair) C →
             Γ ⊢ payTyJunk ∷ imethTy KnotD IPair k C payTyMotK
⊢payTyJunk k C wC =
  ⊢methLam KnotD IPair k C KnotWf wC ⊢IPair ⊢payTyMotK
    (⊢lam (ty-IMu KnotWf (⊢ixP ⊢sDesc (⊢snd (⊢var (there (there here))))))
          (⊢Ty-UnitKv _ (⊢snd (⊢var (there (there (there here)))))))

------------------------------------------------------------------------
-- ★★★ `dρ` — `Σ' (Mu D) (payTy D C)`.  ⚠ `Σ'`'s second component sits
--   one binder deeper than the IH answers, hence `⊢wkKat`.
------------------------------------------------------------------------

payTyRho : {Γ : Cx} → RTm Γ
payTyRho =
  lam (lam (lam (lam
    (Ty-SgK (Ty-MuK (var vz))
            (wkK (pair sTy (snd (var (vs (vs (vs vz))))))
                 (app (fst (var (vs vz))) (var vz)))))))

⊢payTyRho : {Γ : Ctx} →
            Γ ⊢ payTyRho
              ∷ imethTy KnotD IPair tagDCon-rho cDCon-rho payTyMotK
⊢payTyRho =
  ⊢methLam KnotD IPair tagDCon-rho cDCon-rho KnotWf cDCon-rhoWf
           ⊢IPair ⊢payTyMotK
    (⊢lam (ty-IMu KnotWf (⊢ixP ⊢sDesc (⊢snd (⊢var (there (there here))))))
      (⊢Ty-SgKv _ (⊢snd (⊢var (there (there (there here)))))
        (⊢Ty-MuKv _ (⊢snd (⊢var (there (there (there here))))) (⊢var here))
        (⊢wkKat ⊢sTy (⊢snd (⊢var (there (there (there here)))))
          (muFwd (ξ-pairʳ (βsnd sDCon (snd (var (vs (vs (vs vz))))))) 
            (⊢app (⊢ihHere
                     {D = KnotD} {I = IPair}
                     {σ = isingle (var (vs (vs (vs vz))))}
                     {j = pair sDCon (snd (var vz))}
                     (iκ (⌜Id⌝ ⌜Nat⌝ (fst (var (vs vz))) sDCon) iι)
                     {q = var (vs (vs vz))} {M = payTyMotK}
                     (⊢var (there here)))
                  (muBwd* (step (ξ-pairʳ (βsnd sDCon (snd (var (vs (vs (vs vz))))))) done)
                          (⊢var here)))))))

------------------------------------------------------------------------
-- ★★★ `dκ` — `Σ' (εwkTy A) (payTy D C)`.  ⚠ TWO weakenings, and they
--   are DIFFERENT ones: `A` is an `RTy ε` so it climbs from depth 0
--   (`εwkK`), while the recursive answer climbs ONE slot (`⊢wkKat`).
--   The first field's IH is junk (a `Desc → Ty` at depth 0); only the
--   second field's is used, reached by `⊢ihSkipρ` then `⊢ihHere`.
------------------------------------------------------------------------

payTyKap : {Γ : Cx} → RTm Γ
payTyKap =
  lam (lam (lam (lam
    (Ty-SgK (εwkK sTy (snd (var (vs (vs (vs vz))))) (fst (var (vs (vs vz)))))
            (wkK (pair sTy (snd (var (vs (vs (vs vz))))))
                 (app (fst (snd (var (vs vz)))) (var vz)))))))

⊢payTyKap : {Γ : Ctx} →
            Γ ⊢ payTyKap
              ∷ imethTy KnotD IPair tagDCon-kap cDCon-kap payTyMotK
⊢payTyKap =
  ⊢methLam KnotD IPair tagDCon-kap cDCon-kap KnotWf cDCon-kapWf
           ⊢IPair ⊢payTyMotK
    (⊢lam (ty-IMu KnotWf (⊢ixP ⊢sDesc (⊢snd (⊢var (there (there here))))))
      (⊢Ty-SgKv _ (⊢snd (⊢var (there (there (there here)))))
        (⊢εwkK ⊢sTy sortMap-ty (⊢snd (⊢var (there (there (there here)))))
               (⊢fst (⊢var (there (there here)))))
        (⊢wkKat ⊢sTy (⊢snd (⊢var (there (there (there here)))))
          (muFwd (ξ-pairʳ (βsnd sDCon (snd (var (vs (vs (vs vz)))))))
            (⊢app (⊢ihHere
                     {D = KnotD} {I = IPair}
                     {σ = iext (isingle (var (vs (vs (vs vz)))))
                               (fst (var (vs (vs vz))))}
                     {j = pair sDCon (snd (var (vs vz)))}
                     (iκ (⌜Id⌝ ⌜Nat⌝ (fst (var (vs (vs vz)))) sDCon) iι)
                     {q = snd (var (vs (vs vz)))} {M = payTyMotK}
                     (⊢ihSkipρ
                        {D = KnotD} {I = IPair}
                        {σ = isingle (var (vs (vs (vs vz))))}
                        {j = pair sTy nzero}
                        (iρ (pair sDCon (snd (var (vs vz))))
                          (iκ (⌜Id⌝ ⌜Nat⌝ (fst (var (vs (vs vz)))) sDCon) iι))
                        {q = var (vs (vs vz))} {M = payTyMotK}
                        (⊢var (there here))))
                  (muBwd* (step (ξ-pairʳ (βsnd sDCon (snd (var (vs (vs (vs vz))))))) done)
                          (⊢var here)))))))

------------------------------------------------------------------------
-- ★★★ THE TUPLE — junk 0–43 · row 44 · row 45 · junk 46–52.
--
-- ★ TWO REAL ROWS, AND THEY ARE ADJACENT, so the segmented shape of
--   `Knot/LookupD` nests: `⊢methsCons` twice, back to back, and only
--   ONE leading `methsFrom` run and ONE trailing one.  Each segment is
--   a NAMED description for the reason `Knot/Pw`'s header records —
--   left as `_`, `imethsTyFrom-wf` re-normalises a 53-row description
--   once per occurrence and OOM-kills.
------------------------------------------------------------------------

D46 : IDesc
D46 = cdRest (cdTake 46 KnotD)

D45' : IDesc
D45' = cDCon-kap ◂ D46

D44' : IDesc
D44' = cDCon-rho ◂ D45'

spl44 : Split KnotD 44 D44'
spl44 = splTake spl-nil (cdTake 44 KnotD)

wf45 : IDescWfFrom KnotD IPair D45'
wf45 = idwfDrop (spl-step spl44) KnotWf

wf46 : IDescWfFrom KnotD IPair D46
wf46 = idwfDrop (spl-step (spl-step spl44)) KnotWf

-- ★ the last seven rows, all junk.
payTyTail : {Γ : Cx} → RTm Γ
payTyTail = methsFrom (cdTake 7 D46) payTyJunk unit

⊢payTyTail : {Γ : Ctx} →
             Γ ⊢ payTyTail ∷ imethsTyFrom KnotD IPair payTyMotK 46 D46
⊢payTyTail =
  ⊢methsFrom KnotD IPair 46 (cdTake 7 D46) KnotWf wf46
             (spl-step (spl-step spl44))
             ⊢IPair ⊢payTyMotK (λ {k} {C} wC _ _ → ⊢payTyJunk k C wC)
             unit ⊢unit

payTyMid45 : {Γ : Cx} → RTm Γ
payTyMid45 = pair payTyKap payTyTail

⊢payTyMid45 : {Γ : Ctx} →
              Γ ⊢ payTyMid45 ∷ imethsTyFrom KnotD IPair payTyMotK 45 D45'
⊢payTyMid45 =
  ⊢methsCons KnotD IPair 45 {C = cDCon-kap} D46 KnotWf wf46
             (spl-step (spl-step spl44)) ⊢IPair ⊢payTyMotK
             ⊢payTyKap ⊢payTyTail

payTyMid44 : {Γ : Cx} → RTm Γ
payTyMid44 = pair payTyRho payTyMid45

⊢payTyMid44 : {Γ : Ctx} →
              Γ ⊢ payTyMid44 ∷ imethsTyFrom KnotD IPair payTyMotK 44 D44'
⊢payTyMid44 =
  ⊢methsCons KnotD IPair 44 {C = cDCon-rho} D45' KnotWf wf45
             (spl-step spl44) ⊢IPair ⊢payTyMotK
             ⊢payTyRho ⊢payTyMid45

payTyMethsK : {Γ : Cx} → RTm Γ
payTyMethsK = methsFrom (cdTake 44 KnotD) payTyJunk payTyMid44

⊢payTyMethsK : {Γ : Ctx} →
               Γ ⊢ payTyMethsK ∷ imethsTy KnotD IPair payTyMotK KnotD
⊢payTyMethsK =
  ⊢methsFrom KnotD IPair 0 (cdTake 44 KnotD) KnotWf KnotWf spl-nil
             ⊢IPair ⊢payTyMotK (λ {k} {C} wC _ _ → ⊢payTyJunk k C wC)
             payTyMid44 ⊢payTyMid44

------------------------------------------------------------------------
-- ★★★ `payTy`, AS A FUNCTION.  ⚠ THE ELIMINATED ARGUMENT IS THE `DCon`;
--   the `Desc` rides in the motive and is APPLIED afterwards.  That is
--   the same "put the second argument in the motive" move `Knot/LookupD`
--   makes for its ℕ — except here the passenger is itself an `IMu`, so
--   it costs a BACKWARD conversion on the way in (`muBwd*`) as well as
--   the forward one on the way out.
------------------------------------------------------------------------

payTyK : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ → RTm Γ
payTyK n c d = app (ielim KnotD (pair sDCon n) payTyMethsK c) d

⊢payTyK : {Γ : Ctx} {n c d : RTm ⌊ Γ ⌋} →
          Γ ⊢ n ∷ Nat → Γ ⊢ c ∷ K (pair sDCon n) → Γ ⊢ d ∷ K (pair sDesc n) →
          Γ ⊢ payTyK n c d ∷ K (pair sTy n)
⊢payTyK {n = n} {c = c} {d = d} dn dc dd =
  muFwd (ξ-pairʳ (βsnd sDCon n))
    (⊢-cast (cong (λ z → K (pair sTy (snd (pair sDCon z))))
                  (trans (cong (subTm (single d)) (sub-w-single {v = c} n))
                         (wk-single {v = d} n)))
      (⊢app (⊢ielim KnotWf ⊢payTyMotK (⊢ixP ⊢sDCon dn) ⊢payTyMethsK dc)
            -- ⚠ THE PASSENGER PAYS THE CONVERSION BACKWARDS, AND ONE
            --   RUNG OF THE DESCENT TOO: the motive's DOMAIN sits under
            --   the `Π`, so `⟨i⟩` reaches it as `subTm (single c) (w n)`.
            (⊢-cast (cong (λ z → K (pair sDesc (snd (pair sDCon z))))
                          (sym (wk-single {v = c} n)))
              (muBwd* (step (ξ-pairʳ (βsnd sDCon n)) done) dd))))
