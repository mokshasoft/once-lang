------------------------------------------------------------------------
-- OCP-0009 · EXAMPLES — ★★★ `pwBody`, OBJECT-LEVEL.
--
--     pwBody (⌜Π⌝ γ δ)     = δ
--     pwBody (⌜Hom⌝ C a b) = ⌜Hom⌝ (pwBody C) (app (w a) vz) (app (w b) vz)
--     pwBody t             = renTm vs t
--
-- ★★★ IT IS `renTm vs` WITH TWO ROWS OVERRIDDEN.
--
--     pwBody (⌜Π⌝ γ δ)     = δ
--     pwBody (⌜Hom⌝ C a b) = ⌜Hom⌝ (pwBody C) (app (w a) vz) (app (w b) vz)
--     pwBody t             = renTm vs t          ← the DEFAULT clause
--
-- ⚠⚠ AND FOR MONTHS THIS HEADER SAID *"the default clause `renTm vs t`
--   IS `wkK`'s method"* — WHICH IS FALSE, and is bug #4 of
--   `PLAN-RENAMING.md`.  `Knot/Wk.wkK` is derived by `Lib/IWk` as a
--   generic depth-bumping fold; a tag-preserving fold can only implement
--   the renaming that is STABLE UNDER `extR`, which is the outermost
--   insertion, not `renTm vs`.  The two agree on CLOSED terms and only
--   there — so 51 of the 53 rows computed the wrong function on any code
--   with a free variable, which is every code `⊢tr`'s premises admit.
--
-- ★★★ THE FIX IS TO WRITE THE CLAUSE DOWN.  A method receives the row's
--   PAYLOAD, so it can rebuild `icon k p` — the very term the clause is
--   about — and rename it with `Knot/RenTm`'s `renTmK` at `vsRenK`.  No
--   induction, no IH, no classification, and SORT-GENERIC because the
--   renaming takes its sort as an argument.
--
-- ⇒ `Lib/IWk`'s methods and its `WkIx` (`rides`/`pinned`) decoding are
--   GONE from this module.  That decoding existed to reverse-engineer
--   binding structure out of index arithmetic, and it is exactly where
--   the wrong renaming got chosen.  Only `Mot`/`sh` remain.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Knot.PwBody where
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax
  using ( Cx; ε; _∙; vz; vs; RTy; RTm; var; lam; fst; snd; pair; nsuc
        ; ⌜IMu⌝; ⌜Nat⌝; jsub; IDesc; ICon; εwkTy )
open import DirectedHoTT.Spec.Typing
  using ( Ctx; ◇; _▹_; ⌊_⌋; _⊢_∷_; _⊢ty_; ⊢var; here; there
        ; ⊢fst; ⊢snd; ⊢nsuc; ⊢jsub; ⊢⌜IMu⌝; imethTy
        ; βfst; βsnd; ξ-nsuc; ξ-pairˡ; ξ-pairʳ )
open import DirectedHoTT.Lib.IPay using ( ⊢methLam )
open import DirectedHoTT.Lib.IWk
-- ★ ONLY `Mot`/`sh` NOW.  The weakening METHODS and the `WkIx`
--   classification are gone: `pwDefault` rebuilds and renames, so
--   nothing here decodes binding out of index arithmetic.
  using ( Mot; wkdRest
        ; imethsTyFromMot-wf; wfDrop; splDrop )
open import DirectedHoTT.Lib.ICast using ( toMu; fromMu; fordAs; muFwd )
open import DirectedHoTT.Lib.ArithComm using ( symN; ⊢symN )
open import DirectedHoTT.Lib.Strong using ( elAsNat; natAsEl )
open import DirectedHoTT.Examples.Knot.Sorts
  using ( IPair; ⊢IPair; sTm; ⊢sTm; ⊢ixP )
open import DirectedHoTT.Examples.Knot.Desc using ( KnotD; K; cTm-cPi; cTm-cHom )
open import DirectedHoTT.Examples.Knot.Wf using ( KnotWf; cTm-cPiWf; cTm-cHomWf )
open import DirectedHoTT.Examples.Knot.Tags using ( tagTm-cPi; tagTm-cHom )
open import DirectedHoTT.Examples.Knot.Wk
  using ( ⊢MotK; ⊢shIPair )
open import DirectedHoTT.Examples.Knot.WkSub using ( wkTmK; ⊢wkTmK )
open import DirectedHoTT.Examples.Knot.RenTm
  using ( renTmK; ⊢renTmK; ⊢renAppAt; vsRenK; ⊢vsRenK; payRenR )
open import DirectedHoTT.Lib.IPay
  using ( ⊢methLam; ⊢methsAt; ⊢methsCons; idwfDrop; splTake; spl-step; Split )
open import DirectedHoTT.Lib.IMeths using ( methsAt; cdTake; cdRest )
open import DirectedHoTT.Spec.Syntax using ( icon; ipayTy; isingle; app; renTy; unit; IDesc )
open import DirectedHoTT.Spec.Typing using ( ⊢unit )
open import DirectedHoTT.Spec.Typing using ( ⊢icon; IConWf; imethTy; ◇ )
open import DirectedHoTT.Spec.Syntax using ( _∈ID_; ilookupD )
open import DirectedHoTT.Examples.Knot.Pw
  using ( D20; D21; D22; D23; spl20; spl21; spl22; spl23 )
open import DirectedHoTT.Lib.IPay using ( idwfDrop; Split; spl-nil )
open import DirectedHoTT.Spec.Typing using ( imethsTy; imethsTyFrom; ⊢pair; ⊢ielim )
open import DirectedHoTT.Spec.Syntax using ( ielim )
open import DirectedHoTT.Metatheory.SubjectReduction using ( ⊢-cast; ren-ty )
open import normalizer.Syntax.Types using ( sym; _≡_; cong; trans )
open import DirectedHoTT.Lib.Wk using ( wk-singleTy )
open import DirectedHoTT.Lib.IWk using ( sh )
open import DirectedHoTT.Spec.Typing using ( wk-single )
open import DirectedHoTT.Spec.Syntax using ( Σ'; Nat )
open import normalizer.Syntax.Types using ( cong )
open import DirectedHoTT.Examples.Knot.Ctors using ( Tm-cHomK; Tm-appK; Tm-varK )
open import DirectedHoTT.Examples.Knot.CtorsV using ( ⊢Tm-cHomKv; ⊢Tm-appKv; ⊢Tm-varKv )
open import DirectedHoTT.Examples.Knot.Build using ( Var-vzK; ⊢Var-vzKt )

------------------------------------------------------------------------
-- ★★ `⌜Π⌝` — RETURN THE CODOMAIN, and pay the row's SORT FORD.
--
-- The row is
--     iρ (sTm , snd ⟨i⟩) (iρ (sTm , nsuc (snd ⟨i⟩)) (iκ (⌜Id⌝ ⌜Nat⌝ (fst ⟨i⟩) sTm) iι))
-- so `δ` already sits at `nsuc (snd ⟨i⟩)` — the depth the motive wants.
-- ⚠ WHAT DOES NOT MATCH IS THE **SORT**: the motive asks for
--   `sh ⟨i⟩ = (fst ⟨i⟩ , nsuc (snd ⟨i⟩))` and `δ` is at `sTm`.  Those
--   agree only through the row's own ford, and a ford is PROPOSITIONAL —
--   so this is `jsub`, not `ixConv`, which converts along a REDUCTION.
--
-- ★ payload = (γ , (δ , (ford , unit))), so `δ = fst (snd p)` and the
--   ford is `fst (snd (snd p))`.
------------------------------------------------------------------------

pwPi : {Γ : Cx} → RTm Γ
pwPi =
  lam (lam (lam
    (jsub (⌜IMu⌝ KnotD IPair
             (pair (var vz) (nsuc (snd (var (vs (vs (vs vz))))))))
          (symN (fst (var (vs (vs vz)))) (fst (snd (snd (var (vs vz))))))
          (fst (snd (var (vs vz)))))))

⊢pwPi : {Γ : Ctx} →
        Γ ⊢ pwPi ∷ imethTy KnotD IPair tagTm-cPi cTm-cPi (Mot KnotD IPair)
⊢pwPi =
  ⊢methLam KnotD IPair tagTm-cPi cTm-cPi KnotWf cTm-cPiWf ⊢IPair ⊢MotK
    (fromMu (⊢jsub dmot (natAsEl ⊢sTm) (natAsEl dfi) dsym
                   (toMu (⊢fst (⊢snd dp)))))
  where
    dix  = ⊢var (there (there here))
    dp   = ⊢var (there here)
    dfi  = ⊢fst dix
    dmot = ⊢⌜IMu⌝ KnotWf (⊢ixP (elAsNat (⊢var here))
                               (⊢nsuc (⊢snd (⊢var (there (there (there here)))))))
    dsym = ⊢symN dfi ⊢sTm (fordAs (⊢fst (⊢snd (⊢snd dp))))

------------------------------------------------------------------------
-- ★★★ `⌜Hom⌝` — THE ROW THAT RECURSES, and the only real work here.
--
--     pwBody (⌜Hom⌝ C a b) = ⌜Hom⌝ (pwBody C) (app (w a) vz) (app (w b) vz)
--
-- ⚠ THREE DIFFERENT SOURCES IN ONE TERM: the code comes from the **IH**
--   (`pwBody C`, already computed), the endpoints from the **PAYLOAD**
--   (weakened, then applied to the new variable).  A fold that only ever
--   read its IH tuple could not write this row.
--
-- ⚠ AND EVERY PIECE ARRIVES AT `sh (sTm , d)` RATHER THAN
--   `(sTm , nsuc d)` — `sh` is a projection pair, so each needs the same
--   two β-steps (`βfst`, `βsnd`).  That is the `WK` post the emitter's
--   table already applies to `⊢wkK`; here it is written out.
------------------------------------------------------------------------

-- ⚠ THE THREE BINDERS, BY NAME.  Inside a method body `⊢methLam` has
--   bound the index, the payload and the IH tuple, in that order, so
--   `var vz` is the IH and `var (vs (vs vz))` the index.  Writing the
--   de Bruijn spines inline is how the first version of this term ended
--   up unbalanced.
pwIx pwPay pwIH : {Γ : Cx} → RTm (Γ ∙ ∙ ∙)
pwIx  = var (vs (vs vz))
pwPay = var (vs vz)
pwIH  = var vz

-- the row's depth `d`, and one application `app (w x) vz` at `nsuc d`
pwDep : {Γ : Cx} → RTm (Γ ∙ ∙ ∙)
pwDep = snd pwIx

-- ⚠⚠ `wkTmK`, NOT `wkK`.  The rule is `app (renTm vs s) (var vz)`
--   (`Spec/Typing:359`) — `s` is a rule VARIABLE, so it is OPEN, and the
--   two weakenings differ on exactly those.  `Knot/Wk.wkK` is the
--   identity on de Bruijn indices; see `PLAN-RENAMING.md` §0.
-- ★ AND IT DROPS THE `shred`.  `wkK` lands at `sh (pair sTm d)` and owes
--   two β-steps; `wkTmK d` lands at `pair sTm (nsuc d)` on the nose.
pwApp : {Γ : Cx} → RTm (Γ ∙ ∙ ∙) → RTm (Γ ∙ ∙ ∙)
pwApp x = Tm-appK (wkTmK pwDep x) (Tm-varK (Var-vzK pwDep))

pwHom : {Γ : Cx} → RTm Γ
pwHom =
  lam (lam (lam
    (jsub (⌜IMu⌝ KnotD IPair (pair (var vz) (nsuc (snd (var (vs (vs (vs vz))))))))
          (symN (fst pwIx) (fst (snd (snd (snd pwPay)))))
          (Tm-cHomK (fst pwIH)
                    (pwApp (fst (snd pwPay)))
                    (pwApp (fst (snd (snd pwPay))))))))

⊢pwHom : {Γ : Ctx} →
         Γ ⊢ pwHom ∷ imethTy KnotD IPair tagTm-cHom cTm-cHom (Mot KnotD IPair)
⊢pwHom =
  ⊢methLam KnotD IPair tagTm-cHom cTm-cHom KnotWf cTm-cHomWf ⊢IPair ⊢MotK
    (fromMu (⊢jsub dmot (natAsEl ⊢sTm) (natAsEl dfi) dsym
                   (toMu (⊢Tm-cHomKv _ (⊢nsuc dd) dihC dapa dapb))))
  where
    dix  = ⊢var (there (there here))
    dp   = ⊢var (there here)
    dih  = ⊢var here
    dd   = ⊢snd dix
    dfi  = ⊢fst dix
    -- ★ the two β-steps, once — every component needs them.
    shred : {Γ : Ctx} {t : RTm ⌊ Γ ⌋} {d : RTm ⌊ Γ ⌋} →
            Γ ⊢ t ∷ K (pair (fst (pair sTm d)) (nsuc (snd (pair sTm d)))) →
            Γ ⊢ t ∷ K (pair sTm (nsuc d))
    shred x = muFwd (ξ-pairʳ (ξ-nsuc (βsnd _ _))) (muFwd (ξ-pairˡ (βfst _ _)) x)
    dihC = shred (⊢fst dih)
    da   = ⊢fst (⊢snd dp)
    db   = ⊢fst (⊢snd (⊢snd dp))
    -- ⚠ INLINED, NOT A LOCAL `dap`.  A `where`-bound helper with an
    --   implicit term argument left `_t` unsolved at both call sites —
    --   the payload projection is not determined by the RESULT type.
    dapa = ⊢Tm-appKv _ (⊢nsuc dd) (⊢wkTmK dd da)
                     (⊢Tm-varKv _ (⊢nsuc dd) (⊢Var-vzKt dd))
    dapb = ⊢Tm-appKv _ (⊢nsuc dd) (⊢wkTmK dd db)
                     (⊢Tm-varKv _ (⊢nsuc dd) (⊢Var-vzKt dd))
    dmot = ⊢⌜IMu⌝ KnotWf (⊢ixP (elAsNat (⊢var here))
                               (⊢nsuc (⊢snd (⊢var (there (there (there here)))))))
    dsym = ⊢symN dfi ⊢sTm (fordAs (⊢fst (⊢snd (⊢snd (⊢snd dp)))))

------------------------------------------------------------------------
-- ★★★ THE TUPLE — WEAKENING'S WALK, INTERRUPTED TWICE.
--
--     rows  0–19   `decDesc`-computed (weakening)
--     row   20     `pwPi`      ← override
--     row   21     computed    (`⌜Σ⌝` takes the default)
--     row   22     `pwHom`     ← override
--     rows  23–50  computed, then `wkTail`'s two `Var` rows
--
-- ⚠ ROW 21 IS NOT WRITTEN OUT.  Extracting its `WkCon` from
--   `decCon vz cTm-cSg` would need the `nothing` case discharged; a
--   ONE-ROW bounded walk (`wkdTake 1 D21`) computes the very same method
--   and needs no such thing.
------------------------------------------------------------------------
-- ★★★ THE DEFAULT ROW, REBUILT — AND IT IS THE META-LEVEL CLAUSE.
--
--     pwBody t = renTm vs t            (Spec/Variance:1006)
--
-- ⚠⚠ THE 51 DEFAULT ROWS USED `Lib/IWk`'s METHODS, AND `Lib/IWk` IS NOT
--   `renTm vs` (`PLAN-RENAMING.md` §0, bug #4).  It is the identity on
--   de Bruijn indices, so `pwBodyK` computed the wrong function on any
--   code containing a free variable — which is every code `⊢tr`'s
--   premises admit.
--
-- ★★★ AND THE FIX IS TO WRITE THE CLAUSE DOWN.  A method receives the
--   row's PAYLOAD, so it can REBUILD `icon k p` — that is the very term
--   the clause is about — and apply `renTmAtK` at `vsRenK`.  ⇒ no
--   induction, no IH, no classification.
--
-- ★★ WHICH DELETES `Lib/IWk` FROM THIS MODULE.  `WkIx`'s `rides`/
--   `pinned` decoding existed to reverse-engineer binding structure out
--   of index arithmetic, and it is exactly where the wrong renaming got
--   chosen.  Rebuilding needs none of it: the method is SORT-GENERIC
--   because `renTmAtK` takes the sort as an argument.
------------------------------------------------------------------------

pwDefault : {Γ : Cx} → ℕ → RTm Γ
pwDefault k =
  lam (lam (lam
    (app (app (renTmK (var (vs (vs vz))) (icon k (var (vs vz))))
              (nsuc (snd (var (vs (vs vz))))))
         (vsRenK (snd (var (vs (vs vz))))))))

⊢pwDefault : {Γ : Ctx} (k : ℕ) (C : ICon (ε ∙)) →
             IConWf KnotD IPair (◇ ▹ εwkTy IPair) C →
             k ∈ID KnotD → ilookupD KnotD k ≡ C →
             Γ ⊢ pwDefault k ∷ imethTy KnotD IPair k C (Mot KnotD IPair)
⊢pwDefault k C wC mem look =
  ⊢methLam KnotD IPair k C KnotWf wC ⊢IPair ⊢MotK
    -- ⚠ `{i}`/`{u}` PINNED: they sit under `iinst`, which is two
    --   `subTy`s and so not injective (`pin-implicits-on-defined-set-types`).
    (⊢renAppAt {i = var (vs (vs vz))} {u = icon k (var (vs vz))}
               (⊢renTmK (⊢var (there (there here)))
                        (⊢icon KnotWf mem (⊢var (there (there here)))
                               -- ⚠ TWO CASTS, AND THE FIRST IS THE ONE
                               --   a CONCRETE row never needs: at an
                               --   abstract `C` the payload type is
                               --   stuck, so the weakening past the IH
                               --   binder must be pushed through by
                               --   hand (`payRenR`).  `Knot/PayTy` and
                               --   friends skip it because `ipayTy`
                               --   COMPUTES at their concrete rows.
                               (⊢-cast (trans (trans (cong (renTy vs)
                                                           (payRenR (var vz) C))
                                                     (payRenR (var (vs vz)) C))
                                              (cong (ipayTy KnotD IPair
                                                       (isingle (var (vs (vs vz)))))
                                                    (sym look)))
                                       (⊢var (there here)))))
               (⊢nsuc (⊢snd (⊢var (there (there here)))))
               (⊢vsRenK (⊢snd (⊢var (there (there here))))))

------------------------------------------------------------------------

-- ⚠⚠ REBUILT 2026-09-03 (`PLAN-RENAMING.md` bug #4).  The 51 default
--   rows were `Lib/IWk`'s methods, i.e. the WRONG WEAKENING; they are
--   now `pwDefault`, which is the meta-level clause written out.  The
--   two overrides are unchanged — the motive did not move.
--
-- ★ AND THE WALK IS `methsAt`, NOT `iwkMethsFrom`.  The default depends
--   on the ROW (it rebuilds `icon k p`), which is exactly what
--   `Lib/IMeths.methsAt` is for; `Lib/IWk`'s classification apparatus
--   drops out of this module entirely.

PD21 : IDesc
PD21 = cdRest (cdTake 21 KnotD)

PD22 : IDesc
PD22 = cdRest (cdTake 22 KnotD)

PD23 : IDesc
PD23 = cdRest (cdTake 23 KnotD)

pspl20 : Split KnotD 20 (cdRest (cdTake 20 KnotD))
pspl20 = splTake spl-nil (cdTake 20 KnotD)

pspl21 : Split KnotD 21 PD21
pspl21 = spl-step pspl20

pspl22 : Split KnotD 22 PD22
pspl22 = spl-step pspl21

pspl23 : Split KnotD 23 PD23
pspl23 = spl-step pspl22

pwTail : {Γ : Cx} → RTm Γ
pwTail = methsAt (cdTake 30 PD23) pwDefault 23 unit

⊢pwTail : {Γ : Ctx} →
          Γ ⊢ pwTail ∷ imethsTyFrom KnotD IPair (Mot KnotD IPair) 23 PD23
⊢pwTail =
  ⊢methsAt KnotD IPair 23 (cdTake 30 PD23) KnotWf (idwfDrop pspl23 KnotWf)
           pspl23 ⊢IPair ⊢MotK
           (λ {k} {C} wC mem look → ⊢pwDefault k C wC mem look) unit ⊢unit

pwMid22 : {Γ : Cx} → RTm Γ
pwMid22 = pair pwHom pwTail

⊢pwMid22 : {Γ : Ctx} →
           Γ ⊢ pwMid22 ∷ imethsTyFrom KnotD IPair (Mot KnotD IPair) 22 PD22
⊢pwMid22 =
  ⊢methsCons KnotD IPair 22 {C = cTm-cHom} PD23 KnotWf
             (idwfDrop pspl23 KnotWf) pspl23 ⊢IPair ⊢MotK ⊢pwHom ⊢pwTail

pwMid21 : {Γ : Cx} → RTm Γ
pwMid21 = methsAt (cdTake 1 PD21) pwDefault 21 pwMid22

⊢pwMid21 : {Γ : Ctx} →
           Γ ⊢ pwMid21 ∷ imethsTyFrom KnotD IPair (Mot KnotD IPair) 21 PD21
⊢pwMid21 =
  ⊢methsAt KnotD IPair 21 (cdTake 1 PD21) KnotWf (idwfDrop pspl21 KnotWf)
           pspl21 ⊢IPair ⊢MotK
           (λ {k} {C} wC mem look → ⊢pwDefault k C wC mem look)
           pwMid22 ⊢pwMid22

pwMid20 : {Γ : Cx} → RTm Γ
pwMid20 = pair pwPi pwMid21

⊢pwMid20 : {Γ : Ctx} →
           Γ ⊢ pwMid20 ∷ imethsTyFrom KnotD IPair (Mot KnotD IPair) 20
                                      (cdRest (cdTake 20 KnotD))
⊢pwMid20 =
  ⊢methsCons KnotD IPair 20 {C = cTm-cPi} PD21 KnotWf
             (idwfDrop pspl21 KnotWf) pspl21 ⊢IPair ⊢MotK ⊢pwPi ⊢pwMid21

pwBodyMethsK : {Γ : Cx} → RTm Γ
pwBodyMethsK = methsAt (cdTake 20 KnotD) pwDefault 0 pwMid20

⊢pwBodyMethsK : {Γ : Ctx} →
                Γ ⊢ pwBodyMethsK ∷ imethsTy KnotD IPair (Mot KnotD IPair) KnotD
⊢pwBodyMethsK =
  ⊢methsAt KnotD IPair 0 (cdTake 20 KnotD) KnotWf KnotWf spl-nil ⊢IPair ⊢MotK
           (λ {k} {C} wC mem look → ⊢pwDefault k C wC mem look)
           pwMid20 ⊢pwMid20

------------------------------------------------------------------------
-- ★★ `pwBody`, AS AN ELIMINATOR.  Same shape as `wkK` — the motive is
--   the same, so the result index is `sh ⟨i⟩` and the cast is `wkK`'s.
------------------------------------------------------------------------

pwBodyK : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ
pwBodyK i t = ielim KnotD i pwBodyMethsK t

-- ★ SAME CAST AS `⊢wkK` — same motive, so the same `wk-single` round
--   trip on the result index.
⊢pwBodyK : {Γ : Ctx} {i t : RTm ⌊ Γ ⌋} →
           Γ ⊢ i ∷ Σ' Nat Nat → Γ ⊢ t ∷ K i → Γ ⊢ pwBodyK i t ∷ K (sh i)
⊢pwBodyK {i = i} di dt =
  ⊢-cast (cong (λ z → K (sh z)) (wk-single i))
         (⊢ielim KnotWf ⊢MotK di ⊢pwBodyMethsK dt)

