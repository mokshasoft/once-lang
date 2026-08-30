------------------------------------------------------------------------
-- OCP-0009 · LIB — THE CONVERSIONS EVERY JUDGEMENT ROW NEEDS.
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

-- ⚠⚠ MOVED OUT OF `Examples/Knot/JudgeLib` 2026-08-30.  It mentioned
--   the knot ONLY IN COMMENTS: `toMu`/`fromMu`/`fordAs`/`muFwd`/`muBwd*`
--   are stated for an arbitrary `D`/`I`, and by the time the judgement
--   layer was generated it had FOURTEEN importers across four different
--   descriptions.  ★ The Lib/Examples inversion, third sighting — see
--   `FUTURE.md`'s "general lemmas stranded in examples".

{-# OPTIONS --safe #-}
module DirectedHoTT.Lib.ICast where
open import DirectedHoTT.Spec.Syntax
  using ( Cx; RTm; RTy; IDesc; IMu; El; ⌜Nat⌝; ⌜Id⌝; ⌜IMu⌝ )
open import DirectedHoTT.Spec.Typing
  using ( Ctx; ⌊_⌋; _⊢_∷_; ⊢conv; _⟶_; _⟶*_
        ; csymᵀ; credᵀ; El-⌜IMu⌝; ξ-IMu )
open import DirectedHoTT.Metatheory.Injectivity using ( red→≅ᵀ; ⟶ᵀ*-IMu )
open import DirectedHoTT.Lib.ArithComm using ( IdN; elIdN )
open import normalizer.Syntax.Types using ( _≡_; refl )

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

------------------------------------------------------------------------
-- ★ THE SAME MOVE ALONG A REDUCTION SEQUENCE, BOTH WAYS.
--
-- ⚠ `muFwd` takes ONE step, which is all `Knot/Lookup` needed.  An index
--   that reduces over several steps — `sortMap s ⟶* s` is six — needs
--   the `⟶*` form, and `subTm` needs it BACKWARDS: a value built at the
--   row's own sort has to be read at the motive's `sortMap`ped one,
--   which is the reduction run in reverse.  ★ Free, because `≅ᵀ` is
--   symmetric; nothing here inverts a REDUCTION.
--
-- ⚠ ONLY THE BACKWARD ONE EXISTS.  A forward `muFwd*` was written at the
--   same time and had NO consumer — `tools/check-formers.sh` gate 6
--   flagged it.  Symmetry is not a reason to ship a lemma.
------------------------------------------------------------------------

muBwd* : {Γ : Ctx} {D : IDesc} {I : RTy Cx.ε} {i i' t : RTm ⌊ Γ ⌋} →
         i ⟶* i' → Γ ⊢ t ∷ IMu D I i' → Γ ⊢ t ∷ IMu D I i
muBwd* r d = ⊢conv d (csymᵀ (red→≅ᵀ (⟶ᵀ*-IMu r)))

------------------------------------------------------------------------
-- ★★★ A REDUCTION'S ENDPOINTS, MOVED BY AN `≡`.
--
-- ⚠ NOT INTERCHANGEABLE WITH A CONVERSION.  These do not convert
--   anything — they say the SAME reduction, with an endpoint renamed.
--   They appear whenever a lemma is stated at one endpoint and the goal
--   names it differently: `predSndPair` proved at the pair, needed under
--   a substitution; `isSucs-sub` an `≡` where a `⟶*` has to start.
--
-- ⚠ Each was written LOCAL "pending a second customer" — one in
--   `Knot/SubMot`, its mirror in `Lib/ISub`, three days apart, neither
--   knowing about the other.  ⇒ that IS the second customer; they are
--   here now.
------------------------------------------------------------------------

⟶*-castᵣ : {Γ : Cx} {a b b' : RTm Γ} → b ≡ b' → a ⟶* b → a ⟶* b'
⟶*-castᵣ refl r = r

⟶*-castₗ : {Γ : Cx} {a a' b : RTm Γ} → a ≡ a' → a' ⟶* b → a ⟶* b
⟶*-castₗ refl r = r
