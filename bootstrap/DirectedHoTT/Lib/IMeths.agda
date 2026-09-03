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
open import Agda.Builtin.Nat using ( zero; suc; _+_ ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax using ( Cx; ε; _∙; RTm; pair; ICon; IDesc; _◂_; inil; sel )
open import DirectedHoTT.Spec.Typing
  using ( _⟶_; _⟶*_; done; step; ξ-fst; ξ-snd; βfst; βsnd )
open import DirectedHoTT.Lib.ICast using ( ⟶*-castᵣ )
open import normalizer.Syntax.Types using ( _≡_; refl; sym; cong )

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

------------------------------------------------------------------------
-- ★★★ …AND THE SAME WALK WITH A **PER-ROW** METHOD.
--
-- ⚠ `methsFrom` GIVES EVERY ROW THE SAME TERM, which is right when the
--   motive makes 52 of 53 rows do nothing (`Knot/Single`) and useless
--   when the answer depends on the ROW: `pw? (⌜Π⌝ γ δ) = true`,
--   `pw? (⌜Hom⌝ C a b) = pw? C`, everything else `false`.
--
-- ★ AND THE OVERRIDES ARE IN THE MIDDLE OF THE TABLE, not at its end, so
--   the prefix-plus-tail split cannot reach them — `cTm-cPi` and
--   `cTm-cHom` are rows 102 and 104 of `KNOT`.  A FUNCTION of the tag
--   reaches any row without ordering the description around the
--   customer.
--
-- ⚠ `methsFrom W m` is `methsAt W (λ _ → m)`; the constant case is kept
--   because its TYPING is strictly simpler — one derivation, not one per
--   tag — and `Knot/Single` wants exactly that.
------------------------------------------------------------------------

methsAt : {Γ : Cx} {E : IDesc} → CDesc E → (ℕ → RTm Γ) → ℕ → RTm Γ → RTm Γ
methsAt (cd-stop E) mth j t = t
methsAt (cd-cons W) mth j t = pair (mth j) (methsAt W mth (suc j) t)

------------------------------------------------------------------------
-- ★★★ SELECTING A METHOD OUT OF THE TUPLE — the lemma every `agree`
-- needs, and the one thing `Lib/IFold` had that nothing else could use.
--
-- ⚠⚠ `Lib/IFold.Fold.ifMeths-sel` is the same lemma for `ifMeths`, and
--   it is INSIDE A PARAMETERISED MODULE, so `Knot/SzAgree` is the only
--   customer it can ever have.  `methsAt`/`methsFrom` build the tuples
--   everything else uses, and until now nothing could reduce through
--   one — which is precisely why `sz` is the only agreement in the
--   development (`FUTURE.md` D′, `PLAN-RENAMING.md` §9).
--
-- ★ `selCong` is written here for the THIRD time (`Lib/IFold`, and again
--   through `Lib/ISz`/`Lib/ISzSort`'s renamings).  It depends only on
--   `ξ-fst`/`ξ-snd`, so this is its home.
------------------------------------------------------------------------

-- ⚠ ONE ARITHMETIC FACT, and the STATEMENT was chosen to need only one:
--   `methsAt-sel` concludes at `mth (k + j)`, not `mth (j + k)`, because
--   `_+_` recurses on its FIRST argument — so the zero case is
--   definitional and only the successor moves a `suc`.
+suc : (k j : ℕ) → (k + suc j) ≡ suc (k + j)
+suc zero    j = refl
+suc (suc k) j = cong suc (+suc k j)

selCong : {Γ : Cx} (k : ℕ) {ms ms' : RTm Γ} → ms ⟶ ms' → sel k ms ⟶ sel k ms'
selCong zero    r = ξ-fst r
selCong (suc k) r = selCong k (ξ-snd r)

-- ★ …and the selection.  ⚠ THE PREMISE IS THE **WALK**, not the
--   description: `methsAt` recurses on `W`, so what must not run out is
--   `W`.  `InCD W k` says row `k` of the walk exists — which is exactly
--   when `sel k` lands on a method rather than in the tail.
data InCD : {E : IDesc} → CDesc E → ℕ → Set where
  hereCD  : {C : ICon (ε ∙)} {E : IDesc} {W : CDesc E} → InCD (cd-cons {C = C} W) zero
  thereCD : {C : ICon (ε ∙)} {E : IDesc} {W : CDesc E} {k : ℕ} →
            InCD W k → InCD (cd-cons {C = C} W) (suc k)

methsAt-sel : {Γ : Cx} {E : IDesc} (W : CDesc E) {mth : ℕ → RTm Γ}
              (j k : ℕ) {tl : RTm Γ} → InCD W k →
              sel k (methsAt W mth j tl) ⟶* mth (k + j)
methsAt-sel (cd-cons W) j zero    hereCD      = step (βfst _ _) done
methsAt-sel (cd-cons W) {mth = mth} j (suc k) (thereCD p) =
  ⟶*-castᵣ (cong mth (+suc k j))
           (step (selCong k (βsnd _ _)) (methsAt-sel W (suc j) k p))

-- ★ the constant walk is the per-row one at a constant function, so its
--   selection is the same lemma.  ⚠ `methsFrom W m ≡ methsAt W (λ _ → m)`
--   is `refl` (see this module's header), so nothing is re-proved.
-- ⚠ PROVED, NOT DERIVED.  `methsFrom` has its own recursion — it carries
--   no position counter — so `methsFrom W m ≡ methsAt W (λ _ → m) j` is
--   not `refl` and the derivation does not typecheck.  ★ The direct proof
--   is SHORTER anyway: no arithmetic, because there is no `j` to move.
methsFrom-sel : {Γ : Cx} {E : IDesc} (W : CDesc E) {m : RTm Γ}
                (k : ℕ) {tl : RTm Γ} → InCD W k →
                sel k (methsFrom W m tl) ⟶* m
methsFrom-sel (cd-cons W) zero    hereCD      = step (βfst _ _) done
methsFrom-sel (cd-cons W) (suc k) (thereCD p) =
  step (selCong k (βsnd _ _)) (methsFrom-sel W k p)
