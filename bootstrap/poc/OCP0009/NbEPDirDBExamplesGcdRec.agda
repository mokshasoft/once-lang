------------------------------------------------------------------------
-- OCP-0009 — GAP A, EQUATION 3: gcd's RECURSIVE STEP, INTERNALLY.
--
-- ⚠ SPLIT OUT OF `…GcdEqs` FOR COST, 2026-08-17.  `irr-ind` instantiated at
--   gcd's step is a big term — a `natrec` over four leaves carrying the
--   whole `irrT` motive — and adding it to `…GcdEqs` OOM-killed a module
--   that is otherwise 5s.  Alone it has room.  ⭐ Same isolation that took
--   `leaf₃s` from an OOM to 10s and `split2` from an OOM to 4.8s: one big
--   term per module when the term is big enough.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPDirDBExamplesGcdRec where

open import normalizer.Syntax.Types using ( _≡_; refl; trans; cong; sym )
open import poc.OCP0009.NbEPDirDBPi
  using ( Cx; ε; _∙; vz; vs
        ; RTy; El; Hom; Nat; Id
        ; RTm; var; nzero; nsuc; app; pair; fst; snd; ⌜Nat⌝
        ; subTm )
open import poc.OCP0009.NbEPDirDBType
  using ( Ctx; ◇; _▹_; ⌊_⌋; single; _⊢_∷_; ⊢app; ⊢nsuc; ⊢nzero; ⊢conv; csymᵀ
        ; _⟶*_; done )
open import poc.OCP0009.NbEPDirDBSubj using ( ⊢-cast; ⊢[] )
open import poc.OCP0009.NbEPDirDBLR using ( wk-single )
open import poc.OCP0009.NbEPDirDBLibWk using ( w )
open import poc.OCP0009.NbEPDirDBLibAmrec
  using ( Prv; prv; prvTm; prvOk; idToRed; idOfRed )
open import poc.OCP0009.NbEPDirDBLibPair using ( PairT; asN )
open import poc.OCP0009.NbEPDirDBLibArithComm using ( transN; ⊢transN )
open import poc.OCP0009.NbEPDirDBInj using ( red→≅ᵀ; ⟶ᵀ*-Homʳ )
open import poc.OCP0009.NbEPDirDBLibNat using ( ⊢plus )
open import poc.OCP0009.NbEPDirDBLibMonus using ( monusTm )
open import poc.OCP0009.NbEPDirDBLibStrong using ( reflTm; ⊢le-refl )
open import poc.OCP0009.NbEPDirDBExamplesGcdStep
  using ( msr; ⊢msr; recCert; gcd-gt-term; descConv; gt-mh-1 )
open import poc.OCP0009.NbEPDirDBLibArithMonus using ( ⊢desc-left )
open import poc.OCP0009.NbEPDirDBLibNat using ( plusTm )
open import poc.OCP0009.NbEPDirDBExamplesGcdStepExtA using ( gcdStepExt )
open import poc.OCP0009.NbEPDirDBExamplesGcdEqs using ( module GcdEqAt )

module GcdRecAt (Δ : Ctx) where

  open GcdEqAt Δ public

  ------------------------------------------------------------------------
  -- ★★ THE IRRELEVANCE WITNESS, AT THE TWO BOUNDS.
  --
  -- `irr-ind` proves it as a `Π Nat` — quantified over the SECOND bound —
  -- and one application lands it where the recursive step needs it: the
  -- auxiliary seeded at `x` and run to bound `k` agrees with the auxiliary
  -- seeded at `y` and run to bound `n₂`, at every carrier and both
  -- certificates.  ⭐ THIS is what nothing weaker gives, and what
  -- `StepExt` was ultimately for.
  --
  -- ⚠⚠ COMMENTED OUT — IT OOM-KILLS, and this is now a CLEAN measurement:
  --   detached, uninterrupted, on a quiet box, exit 143 with zero errors
  --   logged.  Earlier attempts were all under contention and I twice said
  --   so as if that excused it; it does not — the cost is real.
  --   ⚠ AND THE `.agdai` LIES: one exists for this module, but it PREDATES
  --   the source by 42s and is from the CONDITIONAL version.  An interface
  --   file is only evidence if it postdates the source.
  --
  -- ★★ BISECTED 2026-08-17, and the mechanism is now precise:
  --
  --     `irr-ind gcdStepExt dx dy dk`   returned, never opened   EXIT 0
  --     `⊢app (prvOk (irr-ind …)) dn₂`  ⊢app forces it open      OOM
  --     the same, ALONE in its own module                        OOM
  --
  --   ⇒ THE COST IS `prvOk` FORCING THE `Prv` OPEN.  Returning it never
  --   looks inside; `prvOk` must expose `prv e d`, and `d` is `irr-ind`'s
  --   four-leaf `⊢natrec` elaborated at gcd's step.  ⚠ AND MODULE
  --   ISOLATION DOES NOT HELP — the lever that rescued `leaf₃s` and
  --   `split2` fails here, because this is ONE definition rather than an
  --   accumulation of them.
  --
  -- ⚠ AND A HYPOTHESIS THAT WAS TESTED AND IS WRONG.  I read the bisect as
  --   "`prvOk` FORCES the `Prv` open, and `Prv` is a `data` type so the
  --   projection must pattern-match".  The fix that follows is to make
  --   `Prv` a RECORD, whose eta makes `prvOk p`'s type follow from `p`'s
  --   type with no unfolding.  Done, and `…LibAmrec` stayed green — but
  --   `irrAt` STILL OOMs.  Reverted; the forcing is not the cost, or not
  --   all of it.
  --
  -- ⇒ WHAT IS ACTUALLY KNOWN, and it is less than I claimed twice:
  --     * `irr-ind gcdStepExt …` RETURNED is free (EXIT 0);
  --     * `⊢app` on it OOMs, with or without the `irrT-sub` cast, in its
  --       own module, and with `Prv` as a record;
  --     * module isolation does not help — this is ONE definition.
  --   The mechanism inside `⊢app` is NOT yet identified.  ⚠ Do not repeat
  --   the two explanations already falsified: it is not `irr-ind`'s
  --   instantiation as such, and it is not `prvOk`'s pattern match.
  --
  -- ⚠⚠ AND PROFILING CANNOT SETTLE IT, which is itself worth knowing.
  --   `--profile=all` prints only on COMPLETION, so a check that OOMs
  --   yields nothing.  Tried, 2026-08-17:
  --     `--profile=all` at the default 5500M cap        OOM, no profile
  --     …with `AGDA_SAFE_MEM_MAX=6200M`                 OOM, no profile
  --     …with 4000M RAM + `AGDA_SAFE_SWAP_MAX=5G`       OOM, no profile
  --   ⇒ it is not MARGINALLY over the cap; ~9GB of headroom does not
  --   finish it.  So `agda-perf-is-mutual-block-size`'s advice to profile
  --   does not apply to a term that cannot be elaborated at all.
  --
  -- ⭐⭐ AND THE CONTROLLED PROBE SETTLED THE CAUSE — `…ExamplesIrrProbe`,
  --   green:
  --
  --     `⊢app (prvOk (irr-ind ext …)) dn₂`  at a TRIVIAL step   EXIT 0
  --     the same, at `gcdStepExt`                               OOM
  --
  --   SAME carrier, code, measure and `⊢app`; the ONLY variable is which
  --   `StepExt` is supplied.  ⇒ `irr-ind` is NOT inherently large — gcd's
  --   step is what makes it large, because `irr-ind` APPLIES `ext` and
  --   `idOfRed` pattern-matches the result, forcing that proof to reduce
  --   once per leaf.  For the trivial step that is three lines; for gcd it
  --   is the whole three-split assembly.
  --
  -- ⚠ THAT ALSO KILLED THE FIX I RECOMMENDED TWICE (opaque leaves in
  --   `LibAmrec`): the leaves are not the problem.
  --
  -- ⚠⚠ AND THE FIX THE PROBE POINTS AT WAS TRIED AND FAILED TOO.  Make
  --   `gcdStepExt` OPAQUE so `irr-ind` cannot unfold it — which REQUIRES
  --   `Prv` to be a RECORD, since `idOfRed` must still match a `Prv` that
  --   cannot reduce, and only eta allows that.  Both changes typecheck
  --   (`…LibAmrec` EXIT 0, `…GcdStepExtA` EXIT 0) — and `irrAt` STILL OOMs.
  --   Reverted.
  --
  --   ⇒ blocking the UNFOLDING is not sufficient, so the cost is not (only)
  --   `ext`'s definition being inlined.  FOUR fixes now proposed and
  --   falsified.  The next honest step is to profile the CHEAP probe
  --   (`…ExamplesIrrProbe` completes, so `--profile=all` works there) and
  --   compare its cost breakdown against a slightly-enlarged step, growing
  --   the step until it OOMs — that finds WHICH FEATURE of gcd's step
  --   crosses the line, which no experiment so far has isolated.
  --   Kept verbatim so the discharge is not lost; the theorem below takes
  --   the witness as a HYPOTHESIS instead, which verifies that every
  --   interface in the recursive step lines up and isolates the remaining
  --   problem to producing this ONE term.
  --   ⚠ `Green ≠ meaningful`: nothing below proves anything about gcd until
  --   this is discharged.
  ------------------------------------------------------------------------

--   irrAt : {x y k n₂ : RTm ⌊ Δ ⌋} (dx : Δ ⊢ x ∷ PairT) (dy : Δ ⊢ y ∷ PairT)
--           (dk : Δ ⊢ k ∷ Nat) (dn₂ : Δ ⊢ n₂ ∷ Nat) →
--           Δ ⊢ app (prvTm (irr-ind gcdStepExt dx dy dk)) n₂ ∷ irrT idR x y k n₂
--   irrAt {x = x} {y = y} {k = k} {n₂ = n₂} dx dy dk dn₂ =
--     ⊢-cast (trans (irrT-sub vs idR (λ v → refl) x y (w k) (var vz))
--                   (cong (λ u → irrT idR x y u n₂) (wk-single {v = n₂} k)))
--            (⊢app (prvOk (irr-ind gcdStepExt dx dy dk)) dn₂)

  ------------------------------------------------------------------------
  -- ★★★★★ GAP A, EQUATION 3 — CONDITIONAL on the witness above.
  --
  -- ⚠ EVERY PIECE IS ITS OWN Def inside a parameterised sub-module, not a
  --   `where` block.  As one term this ran 75 MINUTES without finishing;
  --   the rule that has held all session is one big term per Def.
  ------------------------------------------------------------------------

  module GtEq {a' b' d : RTm ⌊ Δ ⌋}
              (da : Δ ⊢ a' ∷ Nat) (db : Δ ⊢ b' ∷ Nat) (dd : Δ ⊢ d ∷ Nat)
              (mh : monusTm (nsuc a') (nsuc b') ⟶* nsuc d) where

    X = gX a' b'
    Y = PAIRᵍ a' b'
    K = gK a' b'
    IHt = gIH a' b'
    CRT = recCert (gcd-gt-term a' b' d IHt mh)

    ⊢X = ⊢gX da db
    ⊢Y = ⊢PAIRᵍ da db
    ⊢K = ⊢plus da (⊢nsuc db)

    dμX = ⊢[] ⊢msr ⊢X
    dμY = ⊢[] ⊢msr ⊢Y

    -- μ X ≤ suc K, from the measure's own reduction
    dP : Δ ⊢ reflTm (subTm (single X) msr)
           ∷ Hom Nat (subTm (single X) msr) (nsuc K)
    dP = ⊢conv (⊢le-refl dμX) (red→≅ᵀ (⟶ᵀ*-Homʳ (μ-ss a' b')))

    -- ⭐⭐ THE RECURSIVE CALL'S CERTIFICATE, TYPED — AND IT IS ONE
    --    `⊢desc-left`.  This is the whole payoff of making `gcd-gt-term`
    --    produce the certificate CLEAN at construction: `recCert` IS
    --    `gtCert a' b'`, which is exactly what `⊢desc-left` derives, so
    --    there is nothing to peel and nothing to compare.  Two `⊢conv`s
    --    remain and both are measure bookkeeping: `descConv` moves the
    --    measure across the pair's projections, and `μ-pair` computes the
    --    carrier's own measure.
    dQ : Δ ⊢ CRT ∷ Hom Nat (nsuc (subTm (single Y) msr)) (subTm (single X) msr)
    dQ = ⊢conv (⊢conv (⊢desc-left da db)
                      (csymᵀ (descConv (monusTm (nsuc a') (nsuc b')) (nsuc b')
                                       (plusTm (nsuc a') (nsuc b')))))
               (csymᵀ (red→≅ᵀ (⟶ᵀ*-Homʳ (μ-pair (nsuc a') (nsuc b')))))

    -- ⚠ SIGNED.  `⊢descS-at`'s `x` occurs ONLY in the subject, so nothing
    --   determines it from the arguments — the standing rule again.
    dC₁ : Δ ⊢ descS-at X X K (reflTm (subTm (single X) msr)) Y CRT
            ∷ Hom Nat (subTm (single Y) msr) K
    dC₁ = ⊢descS-at {x = X} {a = X} {k = K}
                    {p = reflTm (subTm (single X) msr)} {y = Y} {q = CRT}
                    dμY dμX ⊢K dQ dP
    dC₂ = ⊢le-refl dμY

    MID = app (app (auxIH X K) Y)
              (descS-at X X K (reflTm (subTm (single X) msr)) Y CRT)

    -- 1+2: unfold gcd, then reduce the IH application to the auxiliary
    s1 : Prv Δ (Id (El ⌜Nat⌝) (app amrecTm X) MID)
    s1 = idToRed done
           (ih-app X X K (reflTm (subTm (single X) msr)) Y CRT)
           (gcd-gt-call da db mh)

    -- 3: irrelevance, then read the right-hand side back as `gcd Y`
    s2 : {t : RTm ⌊ Δ ⌋} →
         Δ ⊢ t ∷ irrT idR X Y K (subTm (single Y) msr) →
         Prv Δ (Id (El ⌜Nat⌝) MID (app amrecTm Y))
    -- ⚠ `c₁`/`c₂` EXPLICIT: they occur only under `subTm` in `irrElim`'s
    --   conclusion, so leaving them `_` blocks (the standing rule).
    s2 dirr = idOfRed done (amrec-β Y)
                (irrElim {θ = idR} {x = X} {y = Y} dirr Y
                         (descS-at X X K (reflTm (subTm (single X) msr)) Y CRT)
                         (reflTm (subTm (single Y) msr))
                         ⊢Y dC₁ dC₂)

    dA = asN (⊢amrecPt ⊢X)
    dB = asN (appAux ⊢X ⊢K ⊢Y dC₁)
    dC = asN (⊢amrecPt ⊢Y)

    gcd-gt-eq : {t : RTm ⌊ Δ ⌋} →
                Δ ⊢ t ∷ irrT idR X Y K (subTm (single Y) msr) →
                Prv Δ (Id (El ⌜Nat⌝) (app amrecTm X) (app amrecTm Y))
    gcd-gt-eq dirr =
      prv (transN (app amrecTm X) (prvTm s1) (prvTm (s2 dirr)))
          (⊢transN dA dB dC (prvOk s1) (prvOk (s2 dirr)))

    ------------------------------------------------------------------------
    -- ★★★★★ …AND THE WITNESS, DISCHARGED.  GAP A, EQUATION 3, UNCONDITIONAL.
    --
    -- `irr-at` performs the elimination inside `AmTΠ`, where `stp` and `ext`
    -- are still VARIABLES; here it is a pure instantiation.  Two things had
    -- to be true at once, and only the pair works:
    --
    --   * the ⊢app is elaborated at an ABSTRACT step   (5.8×, `…AbsProbe`)
    --   * `irr-at` returns `Prv`, so no type ever names the witness term
    --     (the raw `⊢` form kills `…LibAmrec`: EXIT 143, twice)
    ------------------------------------------------------------------------

    irrW : Prv Δ (irrT idR X Y K (subTm (single Y) msr))
    irrW = irr-at gcdStepExt ⊢X ⊢Y ⊢K dμY

    gcd-gt-eq! : Prv Δ (Id (El ⌜Nat⌝) (app amrecTm X) (app amrecTm Y))
    gcd-gt-eq! = gcd-gt-eq (prvOk irrW)

  ------------------------------------------------------------------------
  -- ★★★★★ NON-VACUITY FOR EQUATION 3 — an INSTANCE, not just a theorem.
  --
  -- ⚠ WHY THIS IS NOT OPTIONAL.  `…GcdStep`'s own post-mortem records two
  --   lemmas that were `--safe`, hole-free, green — and VACUOUS, because
  --   their premise could not be satisfied where they were stated.  A
  --   conditional `gcd-gt-eq!` invites exactly that reading, so here it is
  --   INSTANTIATED against a real `mh`.
  --
  -- ★ THE REACH, stated so the result is not over-read: `mh` forces the
  --   descent to land on a SUCCESSOR, and `monusTm` recurses on its SECOND
  --   argument, so discharging it needs that argument to be a NUMERAL.
  --   Equation 3 therefore holds for an ARBITRARY `a` (here `suc (suc d)`,
  --   with `d` a genuine variable) and a NUMERAL `b` (here `suc zero`).
  --   ⚠ NOT both arguments arbitrary — that is what equation 4 needs and
  --   what the propositional route is for.
  --
  -- ⭐ WHAT IS NEW HERE is the IRRELEVANCE hypothesis being gone.  The `mh`
  --   limit is pre-existing and independent; `irr-at` did not widen it.
  ------------------------------------------------------------------------

  module GtEqAt1 {d : RTm ⌊ Δ ⌋} (dd : Δ ⊢ d ∷ Nat) where

    open GtEq {a' = nsuc d} {b' = nzero} {d = d}
              (⊢nsuc dd) ⊢nzero dd (gt-mh-1 d) public

------------------------------------------------------------------------
-- ⚠⚠ CORRECTION TO c367f5d3's MESSAGE — THERE WAS NO REGRESSION.
--
-- That commit reports `…GcdEqs` going 7.8s → 6m14s when `irr-at` was added
-- to its export list, and calls it a 48× regression.  THAT IS WRONG.
--
-- Measured properly — deleting ONLY `…GcdEqs`'s own `.agdai` in both arms,
-- so dependencies are equally warm, and `irr-at` present-vs-absent is the
-- only difference:
--
--     cold, WITHOUT irr-at   8.23s
--     cold, WITH    irr-at   8.05s      ⇒ identical, no regression
--
-- ★ WHERE THE 6m14s CAME FROM: that run was the FIRST `…GcdEqs` check after
--   `…LibAmrec` had been rebuilt, so it re-typechecked the dependency chain.
--   Every number it was compared against ran WARM.  Cold-vs-warm, not
--   with-vs-without.
--
-- ⚠ THE RULE ALREADY EXISTED AND WAS NOT APPLIED: time Agda cold or not at
--   all; a second `check.sh` run understates ~3×, and only DELETING the
--   `.agdai` gives a cold reading (touching it does not).
--
-- ⇒ A leaf-module "isolation" of `irr-at` was built to fix this and then
--   ABORTED once the premise evaporated.  Do not rebuild it for performance
--   reasons; there is nothing to fix.  `open … public` is likewise NOT the
--   cause — tested, 7.4s public vs 7.1s not.
------------------------------------------------------------------------
