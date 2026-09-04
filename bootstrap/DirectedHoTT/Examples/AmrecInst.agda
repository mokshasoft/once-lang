-- OCP-0009 · EXAMPLES — INSTANTIATING `⊢amrec` AT A CONCRETE CARRIER.
--
-- ⚠ PROMOTED FROM A SPIKE 2026-08-21.  Standing rule: finished library AND
--   finished EXAMPLES material does not live in a `Spike*` module.
--
-- ⚠⚠ AND IT WAS NOT MERELY MISNAMED — IT WAS UNGUARDED.  `sweep.sh` gathers
--   `Spike*` as PROBES and, at target `all` (kernel + libs + examples),
--   does not build them at all.  This file was green when moved, but
--   nothing had been checking that.  ⇒ a result kept in a Spike is a result
--   nobody is watching.
--
-- ★ THE FIRST CALL OF `sub-lemma` IN THE EXAMPLES.  Task #11 says
--   carrier-genericity "has never been cashed out" — `sub-lemma` is
--   called NOWHERE, so neither `⊢amrec` nor `⊢lexrec` has ever been used
--   at a concrete carrier, and "carrier-generic" is a property of the
--   STATEMENT only.  This is the smallest thing that changes that.
--
-- ⚠ AND IT HAS TO COME FIRST, not last.  `⊢amrec`'s premise is
--   `Γ₄ ⊢ x ∷ El (var (vs (vs (vs vz))))` — `El` of a CONTEXT VARIABLE.
--   All four of Γ₄'s slots (`cA : U`, `cP : Π (El cA) U`,
--   `μ : Π (El cA) Nat`, `stp : AStepT`) CONSUME an `El cA`; none
--   produces one.  So no such `x` exists and the premise is
--   unsatisfiable AT Γ₄ — the combinator cannot be applied until Γ₄ has
--   been instantiated.  Same fact the lexrec handoff recorded for
--   `⊢lexrec-nzero` ("unstatable, not broken"), but it is a property of
--   the whole Γ₄/Γ₅ packaging, not of that one corollary.
--
-- THE DATA, at the ℕ carrier (the simplest possible, to isolate the
-- instantiation machinery from the recursion being interesting):
--     cA := ⌜Nat⌝            so `El cA` reduces to `Nat`
--     cP := lam ⌜Nat⌝        the CONSTANT motive, `P x = Nat`
--     μ  := lam (var vz)     the identity measure
--     stp                    ignores the IH and returns 0
--
-- ⚠ β IS A REDUCTION, NOT AGDA COMPUTATION.  `app (lam t) u` does not
--   compute to `subTm (single u) t` at the Agda level — it steps by `β`
--   in `_⟶_`.  So every place the instantiated motive or measure is
--   APPLIED needs a `⊢conv` through `ξ-El`/`β`, and that is the tax the
--   use site pays.  Counting those conversions is the point of the
--   spike: they are what a caller of `⊢amrec` has to write.
--
-- ★★ RESULT — 2.0 s / 0.35 GB, 43 non-comment lines, GREEN FIRST TRY.
--   Instantiation itself is CHEAP and mechanical: four terms, four
--   derivations, one four-case `Sub⊢`, and `sub-lemma` does the rest.
--   The two conversions (`elNat`, `elCP`) are the whole β tax.
--
-- ⚠ BUT `⊢amrec` ITSELF IS STILL NOT CALLED, and cannot be.  What is
--   instantiated below is `⊢aAux`, the BOUNDED AUXILIARY, whose premise
--   `Γ₄ ⊢ n ∷ Nat` IS satisfiable.  `⊢amrec` needs `Γ₄ ⊢ x ∷ El cA`,
--   which is not — and weakening Γ₄ with an `x` slot does not help,
--   because `⊢amrec` is stated AT Γ₄ and would have to be re-derived at
--   the extended context.  ⇒ the usable shape is `⊢aAux` + extend +
--   instantiate; `⊢amrec`'s packaging is the part that does not compose.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.AmrecInst where
open import normalizer.Syntax.Types using ( _≡_; refl; sym; subst )
open import DirectedHoTT.Spec.Syntax
  using ( Cx; ε; _∙; Var; vz; vs
        ; RTy; El; Nat; U; Hom
        ; RTm; var; lam; app; nzero; nsuc; ⌜Nat⌝
        ; Π; Sub; subTy; subTm; renTy; renTm )
open import DirectedHoTT.Spec.Typing
  using ( Ctx; ◇; _▹_; ⌊_⌋; single
        ; _⊢_∷_; ⊢var; here; there; ⊢conv; ⊢nzero; ⊢nsuc
        ; ⊢lam; ⊢app; ⊢⌜Nat⌝
        ; _⊢ty_; ty-El; ty-Nat; ty-U; ty-Π; ty-Hom
        ; _⟶_; β; _⟶ᵀ_; El-⌜Nat⌝; ξ-El
        ; _≅ᵀ_; credᵀ; csymᵀ; ctrnᵀ )
open import DirectedHoTT.Metatheory.RedCong using ( red→≅ᵀ; _⟶ᵀ*_; doneᵀ; stepᵀ )
open import DirectedHoTT.Metatheory.TySub using ( sub-lemma; Sub⊢ )
open import DirectedHoTT.Examples.Dogfood
  using ( Γ₄; AStepT; AIHT; aAuxMot; aAuxTm; ⊢aAux )

------------------------------------------------------------------------
-- 1. THE INSTANTIATION DATA — context-polymorphic, so the SAME term and
--    the SAME derivation serve at every depth the spine visits.
------------------------------------------------------------------------

cAt cPt μt stpt : {Γ : Cx} → RTm Γ
cAt  = ⌜Nat⌝
cPt  = lam ⌜Nat⌝
μt   = lam (var vz)
stpt = lam (lam nzero)

σ₄ : Sub ⌊ Γ₄ ⌋ ⌊ ◇ ⌋
σ₄ vz                = stpt
σ₄ (vs vz)           = μt
σ₄ (vs (vs vz))      = cPt
σ₄ (vs (vs (vs vz))) = cAt

------------------------------------------------------------------------
-- 2. THE CONVERSIONS THE CALLER PAYS FOR.
------------------------------------------------------------------------

-- `El ⌜Nat⌝ ≅ᵀ Nat`
elNat : {Γ : Cx} → El (cAt {Γ}) ≅ᵀ Nat
elNat = red→≅ᵀ (stepᵀ El-⌜Nat⌝ doneᵀ)

-- ★ the CONSTANT motive APPLIED: `El (app cP u) ≅ᵀ Nat`, by β then
--   El-⌜Nat⌝.  Every use of the motive costs this one.
elCP : {Γ : Cx} (u : RTm Γ) → El (app cPt u) ≅ᵀ Nat
elCP u = red→≅ᵀ (stepᵀ (ξ-El (β ⌜Nat⌝ u)) (stepᵀ El-⌜Nat⌝ doneᵀ))

------------------------------------------------------------------------
-- 3. THE FOUR SLOT DERIVATIONS.
------------------------------------------------------------------------

dcA : {Γ : Ctx} → Γ ⊢ cAt ∷ U
dcA = ⊢⌜Nat⌝

dcP : {Γ : Ctx} → Γ ⊢ cPt ∷ Π (El cAt) U
dcP = ⊢lam (ty-El ⊢⌜Nat⌝) ⊢⌜Nat⌝

dμ : {Γ : Ctx} → Γ ⊢ μt ∷ Π (El cAt) Nat
dμ = ⊢lam (ty-El ⊢⌜Nat⌝) (⊢conv (⊢var here) elNat)

-- the instantiated IH type: `(y : A) → μ y < μ x → P y`, with x the
-- variable the step's first ⊢lam bound.
AIHTσ : RTy (ε ∙)
AIHTσ =
  Π (El cAt)
    (Π (Hom Nat (nsuc (app μt (var vz))) (app μt (var (vs vz))))
       (El (app cPt (var (vs vz)))))

⊢AIHTσ : (◇ ▹ El cAt) ⊢ty AIHTσ
⊢AIHTσ =
  ty-Π (ty-El ⊢⌜Nat⌝)
    (ty-Π (ty-Hom ty-Nat (⊢nsuc (⊢app dμ (⊢var here)))
                         (⊢app dμ (⊢var (there here))))
          (ty-El (⊢app dcP (⊢var (there here)))))

dstp : ◇ ⊢ stpt ∷ subTy σ₄ (renTy vs AStepT)
dstp =
  ⊢lam (ty-El ⊢⌜Nat⌝)
    (⊢lam ⊢AIHTσ (⊢conv ⊢nzero (csymᵀ (elCP (var (vs vz))))))

------------------------------------------------------------------------
-- 4. THE SUBSTITUTION IS TYPED — this is `#11`'s missing call.
------------------------------------------------------------------------

σ₄⊢ : Sub⊢ Γ₄ ◇ σ₄
σ₄⊢ here                         = dstp
σ₄⊢ (there here)                 = dμ
σ₄⊢ (there (there here))         = dcP
σ₄⊢ (there (there (there here))) = dcA

------------------------------------------------------------------------
-- 5. …AND THE BOUNDED AUXILIARY, INSTANTIATED.  A CLOSED term.
------------------------------------------------------------------------

⊢auxσ : {n : RTm ⌊ Γ₄ ⌋} → Γ₄ ⊢ n ∷ Nat →
        ◇ ⊢ subTm σ₄ (aAuxTm n) ∷ subTy σ₄ (subTy (single n) aAuxMot)
⊢auxσ dn = sub-lemma (⊢aAux dn) σ₄⊢
