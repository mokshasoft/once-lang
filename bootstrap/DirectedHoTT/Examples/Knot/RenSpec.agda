------------------------------------------------------------------------
-- OCP-0009 · EXAMPLES — ★★★ THE **POINTWISE SPECIFICATIONS** OF THE
-- RENAMING AND SUBSTITUTION VALUES.
--
-- `PLAN-RENAMING.md` §5: once a renaming is a VALUE rather than a fold
-- with its choice inlined, its specification is pointwise and small —
--
--     app ⌈σ⌉ ⌈vz⌉   ⟶*  ⌈ σ vz ⌉
--     app ⌈σ⌉ ⌈vs x⌉ ⟶*  ⌈ σ (vs x) ⌉
--
-- and `Knot/Wk.wkK` CANNOT BE GIVEN ONE AT ALL, because it is not a
-- function you can apply: it is a fold with the renaming baked in.  That
-- is the difference the whole arc turns on, and this module is the half
-- of it that can be written down.
--
-- ★★ AND IT IS THE SHAPE THE NORMALIZER ALREADY USES.  On
--   `origin/plan-0.76-context-indexed-composition`,
--   `Theory/Spec/AlgebraSpec` states its laws as
--   `alg ∘ inj-N ⟶* In ∘ inj-N` — per position, pointwise, a REDUCTION.
--   `SatisfiesSpec` discharges all fifteen in 78 lines, 14 of them
--   trivial.  `PLAN-RENAMING.md` §11.4/§11.5.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Knot.RenSpec where
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax
  using ( Cx; RTm; app; lam; var; vz; vs; renTm; nsuc; pair; subTm )
open import DirectedHoTT.Spec.Typing
  using ( _⟶*_; done; step; β; single; wk-single )
open import DirectedHoTT.Lib.ICast using ( ⟶*-castᵣ; ⟶*-castₗ )
open import DirectedHoTT.Lib.Wk using ( sub-w³-single; sub-w²-single )
open import normalizer.Syntax.Types using ( _≡_; refl; cong; cong₂; trans )
open import DirectedHoTT.Examples.Knot.RenTm
  using ( vsRenK )
open import DirectedHoTT.Examples.Knot.Single
  using ( singleSK; singleK; singleMethsK; singleId; singleVs )
open import DirectedHoTT.Examples.Knot.RenMot
  using ( extRK; extRNK; extRMethsK; constMethR; extRVs )
open import DirectedHoTT.Examples.Knot.Build using ( Var-vzK; Var-vsK )
open import DirectedHoTT.Examples.Knot.Ctors using ( Tm-varK; Tm-nsucK )
open import DirectedHoTT.Examples.Knot.Nrs using ( nrsK; nrsMeths )
open import DirectedHoTT.Lib.ArithComm using ( symN )
open import DirectedHoTT.Spec.Syntax using ( fst; snd; jsub; ⌜IMu⌝; ilookupD )
open import DirectedHoTT.Examples.Knot.Sorts using ( IPair )
open import DirectedHoTT.Examples.Knot.Desc using ( KnotD; cVar-vz; cVar-vs )
open import DirectedHoTT.Examples.Knot.Tags using ( tagVar-vz; tagVar-vs )
open import DirectedHoTT.Examples.Knot.Sorts using ( sVar )
open import DirectedHoTT.Spec.Syntax
  using ( icon; idrefl; ⌜Nat⌝; unit; iihs; isingle; ielim )
open import DirectedHoTT.Spec.Typing using ( ι-ielim; βfst; jsub-refl; ξ-jsubᵖ )
open import DirectedHoTT.Metatheory.Confluence
  using ( ⟶*-appˡ; ⟶*-appʳ; ⟶*-icon; ⟶*-pairˡ; ⟶*-pairʳ; ⟶*-jsubᵖ )
open import DirectedHoTT.Lib.IMeths
  using ( methsFrom-sel; methsFrom-past; cdTake; inCD; tt
        ; sel-here; sel-there )

-- ★ transitivity, spelled as an operator — `Knot/SzAgree` defines the
--   same one locally; a third customer moves it to a reduction lib.
infixr 5 _»_
_»_ : {Γ : Cx} {t u v : RTm Γ} → t ⟶* u → u ⟶* v → t ⟶* v
done      » q = q
(step r p) » q = step r (p » q)

------------------------------------------------------------------------
-- ★★★ `vs`, AND IT IS ONE β-STEP.
--
--     vsRenK n = lam (Var-vsK (w n) (var vz))
--
-- ⚠ ONE LAW, NOT TWO.  `vsRenK` does not CASE on its argument — it is
--   the renaming `x ↦ vs x`, uniformly — so `vz` and `vs y` are the same
--   clause.  `single`/`extR`/`nrs` all case, and each owes two.
--
-- ★★★ AND THIS IS EXACTLY WHAT `Knot/Wk.wkK` CANNOT SAY.  There is no
--   `app wkK x` to reduce: `wkK` is `ielim`, and its renaming exists
--   only as the shape of `Lib/IWk`'s 53 derived methods.  ⇒ the defect
--   was not that the law went unproved; it was that the law was
--   UNSTATABLE.
------------------------------------------------------------------------

vsRenK-app : {Γ : Cx} (n x : RTm Γ) →
             app (vsRenK n) x ⟶* Var-vsK n x
vsRenK-app n x =
  ⟶*-castᵣ (cong (λ z → Var-vsK z x) (wk-single {v = x} n))
           (step (β _ _) done)

------------------------------------------------------------------------
-- ★★★ `extR ρ vz = vz` — THE FIRST LAW THAT CASES ON THE VARIABLE.
--
-- ⚠ FIVE THINGS HAPPEN, and they are the template for every remaining
--   law and for step 3's `sub-agree`:
--     1. β through `extRNK`'s own `lam`
--     2. `ι-ielim` fires on `Var-vzK m = icon tagVar-vz p`
--     3. `ifields` IS the application spine (`Spec/Syntax:1233`, `refl`)
--     4. `Lib/IMeths.methsFrom-sel` picks method 51 out of the tuple
--     5. five βs — `⊢methLam`'s three binders, then the motive's two
------------------------------------------------------------------------

extRK-vz : {Γ : Cx} (i m : RTm Γ) →
           extRK i (Var-vzK m) ⟶*
             app (app (app constMethR i)
                      (pair m (pair (idrefl ⌜Nat⌝ sVar)
                                    (pair (idrefl ⌜Nat⌝ (nsuc m)) unit))))
                 (iihs KnotD extRMethsK (isingle i) cVar-vz
                       (pair m (pair (idrefl ⌜Nat⌝ sVar)
                                     (pair (idrefl ⌜Nat⌝ (nsuc m)) unit))))
extRK-vz i m =
  step (ι-ielim KnotD i extRMethsK tagVar-vz _)
       (⟶*-appˡ (⟶*-appˡ (⟶*-appˡ
         (methsFrom-sel (cdTake 52 KnotD) tagVar-vz
                        (inCD (cdTake 52 KnotD) tagVar-vz tt)))))

-- ★ …and the five βs that finish it: `⊢methLam`'s three binders (index,
--   payload, IH tuple), then the motive's two (`n`, `ρ`).  `constMethR`
--   ignores all but `n`, so the answer is `Var-vzK n`.
extRNK-vz : {Γ : Cx} (d n rn m : RTm Γ) →
            app (extRNK d n rn) (Var-vzK m) ⟶* Var-vzK n
extRNK-vz d n rn m =
  -- ⚠ AND ONE CAST AT THE END, the `wk-single` round trip TWICE: `extRNK`
  --   weakens `n` past its own `lam` and the method's `n` binder is
  --   instantiated back, once for each.
  ⟶*-castᵣ
    (cong Var-vzK
      (trans (wk-single {v = subTm (single (Var-vzK m)) (renTm vs rn)}
                        (subTm (single (Var-vzK m)) (renTm vs n)))
             (wk-single {v = Var-vzK m} n)))
  (step (β _ _)
    -- ⚠ THE SPINE IS FIVE APPLICATIONS DEEP: `extRK-vz` leaves three
    --   (method · index · payload · IHs) and `extRNK` supplies two more
    --   (`n`, `ρ`).  So the β-steps peel 4·3·2·1·0 `appˡ`s, not 2·2·2·1·0.
    (⟶*-appˡ (⟶*-appˡ (extRK-vz _ _)) »
     ⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (step (β _ _) done)))) »
     ⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (step (β _ _) done))) »
     ⟶*-appˡ (⟶*-appˡ (step (β _ _) done)) »
     ⟶*-appˡ (step (β _ _) done) »
     step (β _ _) done))

------------------------------------------------------------------------
-- ★★★ `extR ρ (vs x) = vs (ρ x)` — AND IT LANDS **PAST** THE WALK.
--
-- ⚠ Row 52 is the tail of `extRMethsK = methsFrom (cdTake 52 KnotD)
--   constMethR (pair extRVs unit)`, so `methsFrom-sel` cannot reach it:
--   the walk covers 0–51.  `methsFrom-past` steps over the whole prefix
--   and `βfst` takes the head of the tail.  ⇒ the two selection lemmas
--   are not alternatives — a SEGMENTED tuple needs both.
------------------------------------------------------------------------

extRK-vs : {Γ : Cx} (i m x : RTm Γ) →
           extRK i (Var-vsK m x) ⟶*
             app (app (app extRVs i)
                      (pair m (pair x (pair (idrefl ⌜Nat⌝ sVar)
                                            (pair (idrefl ⌜Nat⌝ (nsuc m)) unit)))))
                 (iihs KnotD extRMethsK (isingle i) cVar-vs
                       (pair m (pair x (pair (idrefl ⌜Nat⌝ sVar)
                                             (pair (idrefl ⌜Nat⌝ (nsuc m)) unit)))))
extRK-vs i m x =
  step (ι-ielim KnotD i extRMethsK tagVar-vs _)
       (⟶*-appˡ (⟶*-appˡ (⟶*-appˡ
         (methsFrom-past (cdTake 52 KnotD) zero » step (βfst _ _) done))))

-- ★ reducing INSIDE the `vs` constructor's argument.  `Var-vsK m x` is
--   `icon tagVar-vs (pair m (pair x …))`, so the congruence is three
--   deep; naming it once keeps the law readable.
inVs : {Γ : Cx} {m x x' : RTm Γ} → x ⟶* x' → Var-vsK m x ⟶* Var-vsK m x'
inVs r = ⟶*-icon (⟶*-pairʳ (⟶*-pairˡ r))

------------------------------------------------------------------------
-- ⬜ `extR ρ (vs x) = vs (ρ x)` — THE HEAD REDUCTION IS ABOVE; THE TAIL
--   IS PARKED, AND THE REASON IS WORTH RECORDING.
--
-- After the five βs the answer reads
--
--     Var-vsK ⟨n⟩ (app ⟨ρ⟩ (jsub _ (symN _ (predN _ (fst (snd (snd (snd p))))))
--                                (fst (snd p))))
--
-- and BOTH the ford and `x` are PROJECTION CHAINS out of the payload.
-- `fst`/`snd` of a literal pair are REDEXES in this kernel, not
-- definitional, so each level costs a `βfst`/`βsnd` under a congruence.
--
-- ★ Then three `jsub-refl`s clear the transports — `Var-vsK`'s depth
--   ford IS `idrefl` (`Knot/Build:222`), so `predN`, `symN` and the
--   outer `jsub` all fire.  ⇒ the transports the ROW needs in order to
--   TYPECHECK compute away when the row meets a real constructor, which
--   is what makes the Forded encoding faithful and not merely well-typed.
--
-- ⚠ THE GRIND IS THE PROJECTIONS, NOT THE IDEA, and it is the SAME grind
--   at all 53 rows of step 3's `sub-agree`.  ⇒ build the projection
--   helper THERE, where it pays 53 times, and come back for this law.
--   `Knot/SzAgree` writes the chains out per row
--   (`⟶*-fst (⟶*-snd done » step (βsnd _ _) done) » step (βfst _ _) done`),
--   which is exactly the thing to factor.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- ★★★ `extR ρ (vs x) = vs (ρ x)`, COMPLETE — the parked law, unparked
--   by `Lib/IMeths`'s `sel-here`/`sel-there`.
--
-- ★★ AND THE FORDS COMPUTE AWAY.  `Var-vsK`'s depth ford IS `idrefl`
--   (`Knot/Build:222`), so once the projection reaches it,
--
--       predN _ (idrefl …)   ⟶  reflN _  = idrefl …
--       symN  _ (idrefl …)   ⟶  reflN _  = idrefl …
--       jsub  _ (idrefl …) x ⟶  x
--
--   ⇒ the transports the ROW needs in order to TYPECHECK vanish when the
--     row meets a real constructor.  That is what makes the Forded
--     encoding FAITHFUL rather than merely well-typed, and it is only
--     visible from a REDUCTION proof — never from the typing.
------------------------------------------------------------------------

extRNK-vs : {Γ : Cx} (d n rn m x : RTm Γ) →
            app (extRNK d n rn) (Var-vsK m x) ⟶* Var-vsK n (app rn x)
extRNK-vs d n rn m x =
  ⟶*-castᵣ
    (cong₂ (λ a b → Var-vsK a (app b x))
      (trans (wk-single {v = subTm (single (Var-vsK m x)) (renTm vs rn)}
                        (subTm (single (Var-vsK m x)) (renTm vs n)))
             (wk-single {v = Var-vsK m x} n))
      (wk-single {v = Var-vsK m x} rn))
  (step (β _ _)
    (⟶*-appˡ (⟶*-appˡ (extRK-vs _ _ _)) »
     ⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (step (β _ _) done)))) »
     ⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (step (β _ _) done))) »
     ⟶*-appˡ (⟶*-appˡ (step (β _ _) done)) »
     ⟶*-appˡ (step (β _ _) done) »
     step (β _ _) done »
     -- the DEPTH FORD, read out of the payload at slot 3
     -- ⚠ `symN a p` and `predN a p` ARE `jsub _ p _`, so reducing inside
     --   them is `⟶*-jsubᵖ` again — three deep, not three different
     --   congruences.
     inVs (⟶*-appʳ (⟶*-jsubᵖ (⟶*-jsubᵖ (⟶*-jsubᵖ
       (sel-there 2 _ _ (sel-there 1 _ _ (sel-there 0 _ _ (sel-here _ _)))))))) »
     -- …then the three transports fire, innermost first
     inVs (⟶*-appʳ (⟶*-jsubᵖ (⟶*-jsubᵖ (step (jsub-refl _ _ _ _) done)))) »
     inVs (⟶*-appʳ (⟶*-jsubᵖ (step (jsub-refl _ _ _ _) done))) »
     inVs (⟶*-appʳ (step (jsub-refl _ _ _ _) done)) »
     -- …and `x` itself, at slot 1.  ⚠ IT COMES BACK WEAKENED THREE TIMES
     --   AND SUBSTITUTED BACK THREE TIMES — a payload field is weakened
     --   past every binder that follows it, and each `⊢app` puts one
     --   back.  `Lib/Wk.sub-w³-single` is that round trip, and it is
     --   `towerA`/`towerJ`'s shape at a TERM instead of a variable.
     inVs (⟶*-appʳ (⟶*-castᵣ (sub-w³-single x)
                             (sel-there 0 _ _ (sel-here _ _))))))

------------------------------------------------------------------------
-- ★★★ `single u vz = u` — THE SAME TEMPLATE, ONE APPLICATION SHALLOWER.
--
-- ⚠ `singleMotK` has ONE passenger where `extRMotK` has two, so the
--   spine is FOUR applications and the βs peel 3·2·1·0 `appˡ`s.  ★ That
--   count is the only thing that changes between these proofs; the six
--   mechanisms are identical.
--
-- ★ Row 51 is PAST the walk here too — `methsFrom (cdTake 51 KnotD)
--   singleId singleTail` covers 0–50 — so it is `methsFrom-past` again,
--   then `βfst` for `sel 0` of the tail.
------------------------------------------------------------------------

singleSK-vz : {Γ : Cx} (i m : RTm Γ) →
              singleSK i (Var-vzK m) ⟶*
                app (app (app singleId i)
                         (pair m (pair (idrefl ⌜Nat⌝ sVar)
                                       (pair (idrefl ⌜Nat⌝ (nsuc m)) unit))))
                    (iihs KnotD singleMethsK (isingle i) cVar-vz
                          (pair m (pair (idrefl ⌜Nat⌝ sVar)
                                        (pair (idrefl ⌜Nat⌝ (nsuc m)) unit))))
singleSK-vz i m =
  step (ι-ielim KnotD i singleMethsK tagVar-vz _)
       (⟶*-appˡ (⟶*-appˡ (⟶*-appˡ
         (methsFrom-past (cdTake 51 KnotD) zero » step (βfst _ _) done))))

singleK-vz : {Γ : Cx} (n u m : RTm Γ) →
             app (singleK n u) (Var-vzK m) ⟶* u
singleK-vz n u m =
  ⟶*-castᵣ (wk-single {v = Var-vzK m} u)
    (step (β _ _)
      (⟶*-appˡ (singleSK-vz _ _) »
       ⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (step (β _ _) done))) »
       ⟶*-appˡ (⟶*-appˡ (step (β _ _) done)) »
       ⟶*-appˡ (step (β _ _) done) »
       step (β _ _) done))

------------------------------------------------------------------------
-- ★★★ `single u (vs x) = var x` — the transports again, one binder up.
------------------------------------------------------------------------

singleSK-vs : {Γ : Cx} (i m x : RTm Γ) →
              singleSK i (Var-vsK m x) ⟶*
                app (app (app singleVs i)
                         (pair m (pair x (pair (idrefl ⌜Nat⌝ sVar)
                                               (pair (idrefl ⌜Nat⌝ (nsuc m)) unit)))))
                    (iihs KnotD singleMethsK (isingle i) cVar-vs
                          (pair m (pair x (pair (idrefl ⌜Nat⌝ sVar)
                                                (pair (idrefl ⌜Nat⌝ (nsuc m)) unit)))))
singleSK-vs i m x =
  step (ι-ielim KnotD i singleMethsK tagVar-vs _)
       (⟶*-appˡ (⟶*-appˡ (⟶*-appˡ
         (methsFrom-past (cdTake 51 KnotD) (suc zero) »
          sel-there 0 _ _ (sel-here _ _)))))

-- ★ reducing inside `Tm-varK`'s argument.
inVar : {Γ : Cx} {x x' : RTm Γ} → x ⟶* x' → Tm-varK x ⟶* Tm-varK x'
inVar r = ⟶*-icon (⟶*-pairˡ r)

singleK-vs : {Γ : Cx} (n u m x : RTm Γ) →
             app (singleK n u) (Var-vsK m x) ⟶* Tm-varK x
singleK-vs n u m x =
  step (β _ _)
    (⟶*-appˡ (singleSK-vs _ _ _) »
     ⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (step (β _ _) done))) »
     ⟶*-appˡ (⟶*-appˡ (step (β _ _) done)) »
     ⟶*-appˡ (step (β _ _) done) »
     step (β _ _) done »
     inVar (⟶*-jsubᵖ (⟶*-jsubᵖ (⟶*-jsubᵖ
       (sel-there 2 _ _ (sel-there 1 _ _ (sel-there 0 _ _ (sel-here _ _)))))))  »
     inVar (⟶*-jsubᵖ (⟶*-jsubᵖ (step (jsub-refl _ _ _ _) done))) »
     inVar (⟶*-jsubᵖ (step (jsub-refl _ _ _ _) done)) »
     inVar (step (jsub-refl _ _ _ _) done) »
     inVar (⟶*-castᵣ (sub-w²-single x) (sel-there 0 _ _ (sel-here _ _))))

------------------------------------------------------------------------
-- ★★★ `nrs vz = nsuc (var (vs vz))` AND `nrs (vs x) = var (vs (vs x))`
--   — the RAISING substitution, and the shallowest spine of the three.
--
-- ⚠ `nrsMotK` has NO passenger at all (`IMu … (pair sTm (nsuc (snd ⟨i⟩)))`),
--   so the spine is THREE applications and the βs peel 2·1·0 `appˡ`s.
--   ⇒ across the three substitutions the only thing that varies is the
--     passenger count: `extR` 2, `single` 1, `nrs` 0, and the spine and
--     the descent depth follow from it.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- ⬜ `nrs` — PARKED, AND THE REASON IS SPECIFIC, NOT "MORE OF THE SAME".
--
-- `nrsMotK` has NO passenger, so the spine is THREE applications and the
-- βs peel 2·1·0 `appˡ`s.  Everything down to and including the three
-- `jsub-refl` transports follows the `extR`/`single` template.
--
-- ⚠⚠ WHAT RESISTS IS THE **ORDER** OF THE LAST STEP.  The payload
--   arrives as `subTm σ₁ (subTm σ₂ (subTm σ₃ (var (vs vz))))` and
--   collapses to the literal pair only PROPOSITIONALLY (`wk-single`),
--   so `fst` has no pair to reduce against until the equality has been
--   applied — which means `⟶*-castₗ` (move the SOURCE), not `⟶*-castᵣ`
--   (move the target).  ★ In `extR` and `single` the same collapse
--   happened to be definitional, so the question never arose.
--
--   Three attempts at the cast did not land it: `cong fst (wk-single
--   {v = ihs} pay)` has visibly the right type and Agda still reports the
--   source unequal, which says the mismatch is EARLIER in the chain than
--   the last step — one of the `inNsucVar` endpoints, not the projection.
--
-- ⇒ ★ IT IS A DIAGNOSIS PROBLEM, NOT A MISSING LEMMA.  Every piece
--   exists; what is needed is to print the chain's intermediate
--   endpoints, which is a `--interaction`/hole exercise rather than more
--   reduction machinery.  Parked deliberately at that boundary.
--
-- ⚠ AND `nrs` IS THE ONLY ONE LEFT: `vsRenK`, `extR` (both rows) and
--   `single` (both rows) are COMPLETE above.
------------------------------------------------------------------------
