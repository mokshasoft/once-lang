------------------------------------------------------------------------
-- OCP-0009 · EXAMPLES — ★★★ `lookupD`, OBJECT-LEVEL.
--
--     lookupD : Desc → ℕ → DCon             `Spec/Syntax:968`
--     lookupD dnil    _       = dι
--     lookupD (C ◃ D) zero    = C
--     lookupD (C ◃ D) (suc k) = lookupD D k
--
-- ⚠ `⊢con` names it (`payTy D (lookupD D k)`) and so does `ι-elim`.
--
-- ★★★ BUILT **GENERAL IN THE DEPTH**, deliberately, and the two callers
--   are why: the merged judgement block binds descriptions CLOSED (at 0)
--   while the `_⟶_` family binds them at the AMBIENT depth.  A depth-0
--   version would serve `⊢con` and be useless to `ι-elim`, and the
--   asymmetry is fatal — `εwkK` lifts `0 → n`, but bringing `ι-elim`'s
--   ambient `D` DOWN to 0 would need a strengthening, which does not
--   exist.  ⇒ the general form serves both; depth 0 is an instance.
--   `narrow-twin-shadows-general-form`, applied before being bitten.
--
-- ★ AND GENERALITY IS NEARLY FREE HERE, which is worth checking rather
--   than assuming: `cDesc-cons`'s fields are `rec sDCon ('D',)` and
--   `rec sDesc ('D',)` — BOTH at the ambient depth, unchanged.  The
--   recursion is DEPTH-PRESERVING, so there is none of the descent that
--   made `⊢Var-vsKt` and `Knot/Nrs` expensive.
--
-- ★ SHAPE: `Knot/Single`'s, not `Knot/Nrs`'s — the motive is a `Π`, so
--   every method has FOUR `lam`s.  ⚠ And unlike both, the two real rows
--   (`tagDesc-nil`/`tagDesc-cons`, 41 and 42 of 53) sit in the MIDDLE,
--   so the tuple needs a junk run on BOTH sides.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Knot.LookupD where
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax
  using ( Cx; ε; _∙; vz; vs; RTy; RTm; var; lam; snd; pair; Π; Nat
        ; ICon; IDesc; εwkTy; IMu; natrec; app; fst; iρ; iκ; iι
        ; ⌜Id⌝; ⌜Nat⌝; isingle; iext; unit; _◂_; ielim; subTm )
open import DirectedHoTT.Spec.Typing
  using ( Ctx; ◇; _▹_; ⌊_⌋; _⊢_∷_; _⊢ty_; ⊢var; here; there
        ; ⊢snd; ⊢lam; ty-Π; ty-Nat; ty-IMu; IConWf; imethTy
        ; ⊢natrec; ⊢app; ⊢fst; ξ-pairʳ; βsnd; ⊢unit
        ; imethsTy; imethsTyFrom; IDescWfFrom; ⊢ielim; single; wk-single )
open import DirectedHoTT.Lib.IPay
  using ( ⊢methLam; ⊢ihHere; ⊢ihSkipρ; ⊢methsFrom; ⊢methsCons
        ; idwfDrop; splTake; Split; spl-nil; spl-step )
open import DirectedHoTT.Lib.IMeths using ( cdTake; cdRest; methsFrom )
open import DirectedHoTT.Lib.Wk using ( sub-w-single )
open import DirectedHoTT.Metatheory.SubjectReduction using ( ⊢-cast )
open import normalizer.Syntax.Types using ( cong; trans )
open import DirectedHoTT.Lib.ICast using ( muFwd )
open import DirectedHoTT.Examples.Knot.Sorts
  using ( IPair; ⊢IPair; sDCon; ⊢sDCon; sDesc; ⊢sDesc; ⊢ixP )
open import DirectedHoTT.Examples.Knot.Desc using ( KnotD; K )
open import DirectedHoTT.Examples.Knot.Wf using ( KnotWf; cDesc-consWf )
open import DirectedHoTT.Examples.Knot.Desc using ( cDesc-cons )
open import DirectedHoTT.Examples.Knot.Tags using ( tagDesc-cons )
open import DirectedHoTT.Examples.Knot.Ctors using ( DCon-iK )
open import DirectedHoTT.Examples.Knot.CtorsV using ( ⊢DCon-iKv )

------------------------------------------------------------------------
-- ★ THE MOTIVE.  At index `⟨i⟩` the answer is a FUNCTION of the ℕ —
--   `lookupD` recurses on the DESCRIPTION and cases on the number, so
--   the number rides in the motive.  `Knot/SubMot` set that convention
--   for `subTm`; following it keeps the method machinery applicable.
------------------------------------------------------------------------

lookupMotK : {Γ : Cx} → RTy ((Γ ∙) ∙)
lookupMotK = Π Nat (IMu KnotD IPair (pair sDCon (snd (var (vs (vs vz))))))

⊢lookupMotK : {Γ : Ctx} →
              ((Γ ▹ εwkTy IPair) ▹ IMu KnotD IPair (var vz)) ⊢ty lookupMotK
⊢lookupMotK =
  ty-Π ty-Nat
       (ty-IMu KnotWf (⊢ixP ⊢sDCon (⊢snd (⊢var (there (there here))))))

------------------------------------------------------------------------
-- ★ THE 51 UNREACHABLE ROWS.  `dι` inhabits the codomain at EVERY index,
--   which is what makes a constant method possible at all — `Lib/IPay`'s
--   header is explicit that an ABSTRACT motive admits none.
------------------------------------------------------------------------

lookupJunk : {Γ : Cx} → RTm Γ
lookupJunk = lam (lam (lam (lam DCon-iK)))

⊢lookupJunk : {Γ : Ctx} (k : ℕ) (C : ICon (ε ∙)) →
              IConWf KnotD IPair (◇ ▹ εwkTy IPair) C →
              Γ ⊢ lookupJunk ∷ imethTy KnotD IPair k C lookupMotK
⊢lookupJunk k C wC =
  ⊢methLam KnotD IPair k C KnotWf wC ⊢IPair ⊢lookupMotK
    (⊢lam ty-Nat (⊢DCon-iKv _ (⊢snd (⊢var (there (there (there here)))))))

------------------------------------------------------------------------
-- ★★★ THE ONE REAL ROW — and there is only one, which is the first
--   pleasant surprise here.
--
--     lookupD dnil    _       = dι          ← IS the junk method
--     lookupD (C ◃ D) zero    = C
--     lookupD (C ◃ D) (suc k) = lookupD D k
--
--   `dnil`'s answer is `dι` at every `k`, which is exactly what
--   `lookupJunk` already is.  ⇒ 52 constant rows and ONE real one, where
--   `Knot/Nrs` and `Knot/Single` each had two.
--
-- ★ `cDesc-cons` has TWO `iρ` fields (the head `DCon` and the tail
--   `Desc`), so BOTH carry an IH.  The method reads the head from the
--   PAYLOAD and the tail's answer from the IH — `Knot/Pw`'s `pwHom`
--   pattern, which takes `fst (var vz)` of the IH tuple.
--
-- ⚠ AND THE `natrec` MOTIVE IS CONSTANT.  `lookupD D k`'s result type
--   does not mention `k`, so `M` is the target type WEAKENED, and all
--   three of `⊢natrec`'s substitutions collapse by `wk-singleTy`.  That
--   is the non-dependent case and it is why no ford appears here.
------------------------------------------------------------------------

lookupCons : {Γ : Cx} → RTm Γ
lookupCons =
  lam (lam (lam (lam
    (natrec (fst (var (vs (vs vz))))                          -- zero ↦ C
            (app (fst (snd (var (vs (vs (vs vz)))))) (var (vs vz)))
            (var vz)))))                                       -- on k

-- ★★★ THE IH TRANSPORT, DISCHARGED — and the recipe below is what the
--   remaining four `ielim`s will reuse verbatim.
--
-- ★ `Lib/IPay.⊢ihHere`/`⊢ihSkipρ`/`⊢ihSkipκ` reach any `iρ` field's IH.
--   Here: one `⊢ihSkipρ` past the head `DCon`, then `⊢ihHere`.
--
-- ⚠⚠ FIVE PINS AND ONE CONVERSION, measured by working it — and NONE of
--   them is optional, because `iihTy` is a FUNCTION and cannot be
--   inverted.  Every missing pin surfaces as `UnsolvedConstraints`, which
--   names nothing:
--
--     {D} {I}   the description and its index type
--     {σ}       the environment — and it STEPS with each skip:
--               `isingle ⟨i⟩` becomes `iext (isingle ⟨i⟩) (fst q)`
--     {j}       the field's own index, from the `ICon`
--     (C)       the telescope, explicit — this is the one that unfolds
--     {q}       the payload — ⚠ IT STEPS TOO: `q` becomes `snd q`.
--               σ and q move together, one field at a time; getting only
--               σ right type-checks nothing and reads as a mismatch deep
--               inside a substitution chain.
--     {M}       the motive, passed UNWEAKENED — `lookupMotK` mentions
--               only `var (vs (vs vz))`, which every `extR` fixes, so
--               the five weakenings `⊢methLam` and the `natrec` branch
--               impose all COMPUTE AWAY.
--
-- ★★★ AND THE LAST STEP IS A REDUCTION, NOT A PIN.  `iinst` puts the
--   field's own index into the motive's `⟨i⟩` slot, so the codomain
--   arrives as `pair sDCon (snd (pair sDesc (snd ⟨i⟩)))` where the target
--   says `pair sDCon (snd ⟨i⟩)`.  `snd (pair a b)` is a `βsnd` STEP in
--   this kernel — a `⟶`, not definitional equality — so it must be
--   CONVERTED.  The same `muFwd (ξ-pairʳ …)` `Knot/Nrs` pays, and it is
--   why chasing it as a unification problem never converges.

⊢lookupCons : {Γ : Ctx} →
              Γ ⊢ lookupCons
                ∷ imethTy KnotD IPair tagDesc-cons cDesc-cons lookupMotK
⊢lookupCons =
  ⊢methLam KnotD IPair tagDesc-cons cDesc-cons KnotWf cDesc-consWf
           ⊢IPair ⊢lookupMotK
    (⊢lam ty-Nat
      (⊢natrec (ty-IMu KnotWf
                  (⊢ixP ⊢sDCon (⊢snd (⊢var (there (there (there (there here))))))))
               (⊢fst (⊢var (there (there here))))
               -- ⚠ `s` lives under TWO more binders (the predecessor and
               --   `natrec`'s own IH), so the method's IH tuple is THREE
               --   back, not four.
               -- ★ THE TAIL'S IH, via `Lib/IPay`'s pickers: one
               --   `⊢ihSkipρ` past the head `DCon` field, then `⊢ihHere`.
               -- ⚠ THREE PINS, and each is forced — `iihTy` cannot be
               --   inverted, so a `_` leaves a stuck constraint.
               -- ★ `M` is passed UNWEAKENED: `lookupMotK` mentions only
               --   `var (vs (vs vz))`, which every `extR` fixes, so the
               --   five weakenings `⊢methLam` and the `natrec` branch
               --   impose all COMPUTE AWAY.
               -- ★★★ AND ONE CONVERSION, NOT A PIN.  `iinst` puts the
               --   field's own index into the motive's `⟨i⟩` slot, so the
               --   codomain arrives as `pair sDCon (snd (pair sDesc
               --   (snd ⟨i⟩)))` where the target says `pair sDCon
               --   (snd ⟨i⟩)`.  `snd (pair a b)` is a `βsnd` STEP in this
               --   kernel — a `⟶`, not definitional — so it must be
               --   converted.  Same `muFwd (ξ-pairʳ …)` `Knot/Nrs` pays.
               (muFwd (ξ-pairʳ (βsnd sDesc (snd (var (vs (vs (vs (vs (vs vz)))))))))
                 (⊢app (⊢ihHere
                        {D = KnotD} {I = IPair}
                        {σ = iext (isingle (var (vs (vs (vs (vs (vs vz)))))))
                                  (fst (var (vs (vs (vs (vs vz))))))}
                        {j = pair sDesc (snd (var (vs vz)))}
                        (iκ (⌜Id⌝ ⌜Nat⌝ (fst (var (vs (vs vz)))) sDesc) iι)
                        -- ⚠ AFTER A SKIP THE PAYLOAD STEPS TOO: `iihTy`
                        --   recurses at `snd q`, not `q`.  σ and q move
                        --   together, one field at a time.
                        {q = snd (var (vs (vs (vs (vs vz)))))} {M = lookupMotK}
                        (⊢ihSkipρ {D = KnotD} {I = IPair} {σ = isingle (var (vs (vs (vs (vs (vs vz))))))}
                                   {j = pair sDCon (snd (var vz))} (iρ (pair sDesc (snd (var (vs vz))))
                                    (iκ (⌜Id⌝ ⌜Nat⌝ (fst (var (vs (vs vz)))) sDesc)
                                     iι))
                           {q = var (vs (vs (vs (vs vz))))} {M = lookupMotK}
                           (⊢var (there (there (there here))))))
                     (⊢var (there here))))
               (⊢var here)))

------------------------------------------------------------------------
-- ★★★ THE TUPLE — SEGMENTED, `Knot/Pw`'s shape but through the LIBRARY.
--
-- Row 42 (`tagDesc-cons`) is the only real one, so the tuple is
--   rows 0–41 junk · row 42 · rows 43–52 junk.
--
-- ⚠⚠ EVERY SEGMENT IS A **NAMED** DESCRIPTION.  `Knot/Pw`'s header
--   records why: left as `_` for `imethsTyFrom-wf` to solve, this
--   OOM-KILLED — with `-c` too, so it was volume, not the collector.
--   Each meta makes Agda re-normalise a `cdTake`/`cdRest` against a
--   53-row description, once per occurrence.
--
-- ★ AND THE MIDDLE ROW GOES THROUGH `⊢methsCons`, not a hand-rolled
--   `⊢pair`/`⊢-cast` pair.  `Knot/Pw` spells that chain out three times —
--   it predates the lemma — and `Lib/IPay.⊢methsCons` is exactly it.
--   ⬜ `Knot/Pw` could be shortened the same way.
------------------------------------------------------------------------

D43 : IDesc
D43 = cdRest (cdTake 43 KnotD)

D42' : IDesc
D42' = cDesc-cons ◂ D43

spl42 : Split KnotD 42 D42'
spl42 = splTake spl-nil (cdTake 42 KnotD)

wf43 : IDescWfFrom KnotD IPair D43
wf43 = idwfDrop (spl-step spl42) KnotWf

-- ★ the last ten rows, all `dι`.
lookupTail : {Γ : Cx} → RTm Γ
lookupTail = methsFrom (cdTake 10 D43) lookupJunk unit

⊢lookupTail : {Γ : Ctx} →
              Γ ⊢ lookupTail ∷ imethsTyFrom KnotD IPair lookupMotK 43 D43
⊢lookupTail =
  ⊢methsFrom KnotD IPair 43 (cdTake 10 D43) KnotWf wf43 (spl-step spl42)
             ⊢IPair ⊢lookupMotK (λ {k} {C} wC _ _ → ⊢lookupJunk k C wC)
             unit ⊢unit

-- ★ row 42 in front of them
lookupMid : {Γ : Cx} → RTm Γ
lookupMid = pair lookupCons lookupTail

⊢lookupMid : {Γ : Ctx} →
             Γ ⊢ lookupMid ∷ imethsTyFrom KnotD IPair lookupMotK 42 D42'
⊢lookupMid =
  ⊢methsCons KnotD IPair 42 {C = cDesc-cons} D43 KnotWf wf43
             (spl-step spl42) ⊢IPair ⊢lookupMotK ⊢lookupCons ⊢lookupTail

-- ★ …and the leading run of 42
lookupMethsK : {Γ : Cx} → RTm Γ
lookupMethsK = methsFrom (cdTake 42 KnotD) lookupJunk lookupMid

⊢lookupMethsK : {Γ : Ctx} →
                Γ ⊢ lookupMethsK ∷ imethsTy KnotD IPair lookupMotK KnotD
⊢lookupMethsK =
  ⊢methsFrom KnotD IPair 0 (cdTake 42 KnotD) KnotWf KnotWf spl-nil
             ⊢IPair ⊢lookupMotK (λ {k} {C} wC _ _ → ⊢lookupJunk k C wC)
             lookupMid ⊢lookupMid

------------------------------------------------------------------------
-- ★★★ `lookupD`, AS A FUNCTION.  ⚠ The `ielim` lands at the motive, a
--   `Π Nat …`, so the ℕ is APPLIED afterwards — the number rides in the
--   motive precisely so the recursion can be on the description.
------------------------------------------------------------------------

lookupDK : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ → RTm Γ
lookupDK n d k = app (ielim KnotD (pair sDesc n) lookupMethsK d) k

⊢lookupDK : {Γ : Ctx} {n d k : RTm ⌊ Γ ⌋} →
            Γ ⊢ n ∷ Nat → Γ ⊢ d ∷ K (pair sDesc n) → Γ ⊢ k ∷ Nat →
            Γ ⊢ lookupDK n d k ∷ K (pair sDCon n)
⊢lookupDK {n = n} {d = d} {k = k} dn dd dk =
  -- ⚠ THE SAME `βsnd` AS IN THE METHOD: `iinst` puts `pair sDesc n` into
  --   the motive's `⟨i⟩` slot, so the codomain reads `snd (pair sDesc n)`
  --   where the caller says `n`.  A `⟶` step, so a CONVERSION.
  muFwd (ξ-pairʳ (βsnd sDesc n))
    -- ⚠ AND ONE CAST BEFORE IT: `iinst` weakens the index TWICE past the
    --   motive's two binders and the `⊢app` instantiates them back, so
    --   `n` arrives as `subTm (single k) (subTm (extS (single d)) (w (w n)))`.
    --   `sub-w-single` clears the inner pair, `wk-single` the outer —
    --   the same two-rung descent `⊢Var-vsKt` pays.
    (⊢-cast (cong (λ z → K (pair sDCon (snd (pair sDesc z))))
                  (trans (cong (subTm (single k)) (sub-w-single {v = d} n))
                         (wk-single {v = k} n)))
      (⊢app (⊢ielim KnotWf ⊢lookupMotK (⊢ixP ⊢sDesc dn) ⊢lookupMethsK dd) dk))
