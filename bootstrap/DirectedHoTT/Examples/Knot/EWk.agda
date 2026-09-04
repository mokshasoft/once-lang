------------------------------------------------------------------------
-- OCP-0009 · EXAMPLES — ★★★ `εwkTm`, OBJECT-LEVEL: a CLOSED term at any
--                       depth.
--
--     εwkTm : RTm ε → RTm Γ        `Spec/Syntax:1104`
--     εwkTm = subTm εsub
--
-- ⚠ THE MERGE NEEDS IT TWICE OVER.  `icw-clo`'s subject IS `εwkTm {Θ} c`
--   — the rule cannot be encoded without it — and separately the merged
--   block reads one CLOSED description at two different depths
--   (`⊢icon`'s premise sits at the ambient depth, `idwf-cons`'s at 1),
--   which is the same reindexing.
--
-- ★★★ AND IT IS FIFTEEN LINES, BECAUSE OF TWO THINGS THAT ALREADY
--   LANDED — neither of which was done for this:
--
--   1. `Knot/SubApp.⊢subAtK` takes its SOURCE and TARGET depths
--      INDEPENDENTLY.  It was generalised for `nrs`, which RAISES; the
--      narrow twin (`dd = nsuc m`) could not have expressed
--      `SubTy 0 n` at all.
--   2. `Var 0` IS EMPTY, so the substitution ITSELF is trivial: a
--      `SubTy 0 n` is a function nothing can ever call, and ANY body of
--      the right type inhabits it.  `Tm-nzeroK` exists at every depth.
--
-- ⇒ the object-level empty substitution is a `lam` around a nullary
--   former, and `εwk` is `subAtK` at it.  ⚠ Read that as a measurement
--   of the generalisation, not of this module.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Knot.EWk where
open import DirectedHoTT.Spec.Syntax using ( Cx; RTm; lam; pair; Nat; renTm; vs )
open import DirectedHoTT.Spec.Typing using ( Ctx; ⌊_⌋; _⊢_∷_; _⟶*_; ⊢lam; ty-IMu )
open import DirectedHoTT.Examples.Knot.Desc using ( K )
open import DirectedHoTT.Examples.Knot.Wf using ( KnotWf )
open import DirectedHoTT.Examples.Knot.Sorts
  using ( ⊢ixP; sVar; ⊢sVar; sTm; ⊢sTm; num; ⊢num )
open import DirectedHoTT.Examples.Knot.Ctors using ( Tm-nzeroK )
open import DirectedHoTT.Examples.Knot.CtorsV using ( ⊢Tm-nzeroKv )
open import DirectedHoTT.Examples.Knot.Terms using ( SubTy )
open import DirectedHoTT.Examples.Knot.SubApp using ( subAtK; ⊢subAtK )
open import DirectedHoTT.Examples.Knot.SubMot using ( sortMap )
open import DirectedHoTT.Metatheory.TySub using ( ⊢wk )

------------------------------------------------------------------------
-- ★ THE EMPTY SUBSTITUTION.  ⚠ Its BODY is junk on purpose: the domain
--   `K (sVar , 0)` has no closed inhabitant, so no well-typed call can
--   ever reach it.  Same argument `Knot/Nrs`'s 51 junk rows run on.
------------------------------------------------------------------------

εsubK : {Γ : Cx} → RTm Γ
εsubK = lam Tm-nzeroK

⊢εsubK : {Γ : Ctx} {n : RTm ⌊ Γ ⌋} →
         Γ ⊢ n ∷ Nat → Γ ⊢ εsubK ∷ SubTy (num 0) n
⊢εsubK dn =
  ⊢lam (ty-IMu KnotWf (⊢ixP ⊢sVar (⊢num 0)))
       (⊢Tm-nzeroKv _ (⊢wk dn))

------------------------------------------------------------------------
-- ★★ …AND THE WEAKENING, AT ANY SORT.  The `sortMap s ⟶* s` premise is
--   the one `⊢subAtK` always asks for; `Knot/SubMot` proves it at all
--   seven sorts, so every instance is available.
------------------------------------------------------------------------

εwkK : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ → RTm Γ
εwkK s n t = subAtK s (num 0) n εsubK t

⊢εwkK : {Γ : Ctx} {s n t : RTm ⌊ Γ ⌋} →
        Γ ⊢ s ∷ Nat → sortMap s ⟶* s → Γ ⊢ n ∷ Nat →
        Γ ⊢ t ∷ K (pair s (num 0)) →
        Γ ⊢ εwkK s n t ∷ K (pair s n)
⊢εwkK ds st dn dt = ⊢subAtK ds st (⊢num 0) dn (⊢εsubK dn) dt

------------------------------------------------------------------------
-- ★★ `isingle`, OBJECT-LEVEL — and it is `εsubK`'s sibling.
--
--     isingle : RTm Γ → Sub (ε ∙) Γ        `Spec/Syntax:1122`
--     isingle i vz     = i
--     isingle i (vs ())
--
-- ⚠ `⊢icon`'s payload premise names it, and so does `ι-ielim`.
--
-- ★ THE SAME REASON IT IS SMALL: a substitution out of a ONE-VARIABLE
--   scope is a function whose answer does not depend on its argument —
--   `Var 1` has exactly one inhabitant and the `vs` case is refuted.  So
--   the object-level form is a `lam` that IGNORES its variable, and the
--   only work is weakening `i` past the binder.
-- ⚠ It is NOT `εsubK`'s reason, though the shape matches: there the
--   domain is EMPTY, here it is a singleton.  Both make the body free;
--   only one of them makes it unreachable.
------------------------------------------------------------------------

isingleK : {Γ : Cx} → RTm Γ → RTm Γ
isingleK i = lam (renTm vs i)

-- ⚠ `n` EXPLICIT: the emitted TERM does not mention the depth (a `lam`
--   ignoring its variable needs none), so the emitter hands it over
--   through the `DX` role — the index term, then its derivation.
⊢isingleK : {Γ : Ctx} (n : RTm ⌊ Γ ⌋) {i : RTm ⌊ Γ ⌋} →
            Γ ⊢ n ∷ Nat → Γ ⊢ i ∷ K (pair sTm n) →
            Γ ⊢ isingleK i ∷ SubTy (num 1) n
⊢isingleK _ dn di =
  ⊢lam (ty-IMu KnotWf (⊢ixP ⊢sVar (⊢num 1))) (⊢wk di)
