------------------------------------------------------------------------
-- OCP-0009 · LIB — WALKING A DESCRIPTION'S METHOD TUPLE: A COMPUTED
-- PREFIX AND A GIVEN TAIL.
--
-- ★ WHY THIS IS A LIBRARY AND NOT AN EXAMPLE.  It arrived in
--   `Examples/Knot/SubMot`, where it was written for `extS`'s 51 + 2
--   split — but nothing in it mentions the knot, a motive, or a sort.
--   It is `Lib/IWk`'s `WkDesc`/`wkdLen`/`wkdRest` with the
--   CLASSIFICATION removed: what is left is the walk itself.
--
--   ⚠ A library wanting to import an example is the signal that the
--   example holds something general.  Here it did.
--
-- ★★ THE ESCAPE HATCH IS STRUCTURAL, NOT BOOKKEEPING.  A method tuple is
--   RIGHT-NESTED, so "computed rows then given rows" is just where the
--   nest stops — one constructor and one tail argument.  No row is
--   named, and the description needs no particular ordering; ordering
--   only decides how MUCH gets computed.
--
-- ⚠ AND UNLIKE `Lib/IWk` THERE IS NOTHING TO DECIDE.  `Lib/IWk` must
--   CLASSIFY each row because a weakening method depends on the row's
--   fields.  A caller whose method does not — `extS`'s do-nothing rows —
--   needs only a LENGTH, made type-safe by being indexed by the
--   description it walks.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Lib.IMeths where
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax using ( Cx; ε; _∙; RTm; pair; ICon; IDesc; _◂_; inil )

data CDesc : IDesc → Set where
  cd-stop : (E : IDesc) → CDesc E
  cd-cons : {C : ICon (ε ∙)} {E : IDesc} → CDesc E → CDesc (C ◂ E)

-- WHICH rows are left …
cdRest : {E : IDesc} → CDesc E → IDesc
cdRest (cd-stop E) = E
cdRest (cd-cons W) = cdRest W

-- … and at WHAT position the tail starts.  ⚠ The partner of `cdRest`:
--   together they say exactly what the caller's tail must be typed at.
cdPos : {E : IDesc} → CDesc E → ℕ → ℕ
cdPos (cd-stop E) j = j
cdPos (cd-cons W) j = cdPos W (suc j)

-- ★ take the first `n` rows — TOTAL: it stops early if the description
--   runs out, so no caller has to prove the description is long enough.
cdTake : ℕ → (E : IDesc) → CDesc E
cdTake zero    E       = cd-stop E
cdTake (suc n) inil    = cd-stop inil
cdTake (suc n) (C ◂ E) = cd-cons (cdTake n E)

------------------------------------------------------------------------
-- ★★★ THE TUPLE ITSELF — one method repeated over the prefix, then a
-- caller-supplied tail.
--
-- ⚠⚠ GENERIC IN THE METHOD, which `Knot/SubMot`'s version was not: it
--   named `constMeth`, and `constMeth` names `extMotK`.  A second
--   customer with a different motive could not reuse a line of it.
--   ★ The walk never inspects the method, so there was never a reason
--     for it to know which one.
------------------------------------------------------------------------

methsFrom : {Γ : Cx} {E : IDesc} → CDesc E → RTm Γ → RTm Γ → RTm Γ
methsFrom (cd-stop E) m t = t
methsFrom (cd-cons W) m t = pair m (methsFrom W m t)
