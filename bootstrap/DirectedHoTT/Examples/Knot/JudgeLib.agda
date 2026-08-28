------------------------------------------------------------------------
-- OCP-0009 · EXAMPLES — THE CONVERSIONS EVERY JUDGEMENT ROW NEEDS.
--
-- A judgement is encoded as an `IDesc` whose rows are Forded: each index
-- component gets an `iκ (⌜Id⌝ …)` field.  ⚠ THE FIELDS ARE **CODES**, so
-- everything inhabiting one is typed at `El <code>`, while the things
-- actually built — a `Ctx`, a `Var`, an `RTy` — are typed at `IMu …`.
-- Each field therefore costs one `El-⌜IMu⌝` conversion in each
-- direction, and each depth ford one `El-⌜Nat⌝`.
--
-- ★ THESE ARE NOT PER-JUDGEMENT.  `Examples/Knot/Lookup` grew them for
--   `_∋_∷_` and they are stated only in terms of the CODE, so they serve
--   any row of any judgement over these two families.
--
-- ⚠ AND `toCn`/`toKn` WERE THE SAME FUNCTION, as were `fromCn`/`fromKn`
--   — `El-⌜IMu⌝` does not care which description it is unfolding.  The
--   duplication read as "`CtxD` needs its own pair, because `toKn` is
--   `KnotD`'s", which is false: `toMu`/`fromMu` cover both, and the
--   description is inferred.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Knot.JudgeLib where
open import DirectedHoTT.Spec.Syntax
  using ( Cx; RTm; RTy; IDesc; IMu; El; ⌜Nat⌝; ⌜Id⌝; ⌜IMu⌝ )
open import DirectedHoTT.Spec.Typing
  using ( Ctx; ⌊_⌋; _⊢_∷_; ⊢conv; _⟶_
        ; csymᵀ; credᵀ; El-⌜IMu⌝; ξ-IMu )
open import DirectedHoTT.Lib.ArithComm using ( IdN; elIdN )

-- ★ THE DESCRIPTION AND ITS INDEX TYPE ARE IMPLICIT, and that is the
--   whole point: one pair of conversions for `KnotD`, `CtxD`, and every
--   judgement description that comes later.
toMu : {Γ : Ctx} {D : IDesc} {I : RTy Cx.ε} {i t : RTm ⌊ Γ ⌋} →
       Γ ⊢ t ∷ IMu D I i → Γ ⊢ t ∷ El (⌜IMu⌝ D I i)
toMu d = ⊢conv d (csymᵀ (credᵀ El-⌜IMu⌝))

fromMu : {Γ : Ctx} {D : IDesc} {I : RTy Cx.ε} {i t : RTm ⌊ Γ ⌋} →
         Γ ⊢ t ∷ El (⌜IMu⌝ D I i) → Γ ⊢ t ∷ IMu D I i
fromMu d = ⊢conv d (credᵀ El-⌜IMu⌝)

-- a DEPTH ford's inhabitant, read as the `Id` it is
fordAs : {Γ : Ctx} {a b t : RTm ⌊ Γ ⌋} →
         Γ ⊢ t ∷ El (⌜Id⌝ ⌜Nat⌝ a b) → Γ ⊢ t ∷ IdN a b
fordAs {a = a} {b = b} d = ⊢conv d (elIdN a b)

-- ★ a value built at one index, retyped at an index it REDUCES to.
--   `wkK`'s result index is `sh (pair sTy m)` where the ford wants
--   `pair sTy (nsuc m)` — two β-steps, the same two every time.
muFwd : {Γ : Ctx} {D : IDesc} {I : RTy Cx.ε} {i i' t : RTm ⌊ Γ ⌋} →
        i ⟶ i' → Γ ⊢ t ∷ IMu D I i → Γ ⊢ t ∷ IMu D I i'
muFwd r d = ⊢conv d (credᵀ (ξ-IMu r))
