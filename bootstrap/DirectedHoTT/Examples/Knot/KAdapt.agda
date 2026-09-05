------------------------------------------------------------------------
-- OCP-0009 · KNOT — ★★★ KERNEL-ORDER ADAPTERS.
--
-- `tools/gen-knot.py`'s `_SUBST_CT` renames a HEAD; it cannot permute
-- ARGUMENTS.  Two of step 5's object-level functions do not take the
-- kernel's argument order:
--
--     payTy   D C       ↦  payTyK   n C D            ★ Desc/DCon SWAPPED
--     ipayTy  D I σ C   ↦  ipayTyK  dd C n σ D I     ★ 4 args → 6, permuted
--
-- ★★★ SO THE ADAPTATION IS WRITTEN HERE, IN AGDA, WHERE IT IS CHECKED.
--   The alternative — teaching the generator to permute — puts the
--   argument order in a Python table that nothing type-checks, and a
--   wrong permutation there would surface as a mis-typed GENERATED PROOF
--   rather than as a generator error.  ⚠ Adding a `FIELD_SORT` row for
--   the un-permuted names does exactly that, which is why the generator
--   now says not to.
--
-- ⚠ `lookupD`/`ilookupD` need NO adapter: they are already in kernel
--   order and want only the depth prefix `_PRE_N` already supplies.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Knot.KAdapt where
open import DirectedHoTT.Spec.Syntax using ( Cx; RTm; pair; nzero; Nat )
open import DirectedHoTT.Spec.Typing using ( Ctx; _⊢_∷_; ⌊_⌋ )
open import DirectedHoTT.Examples.Knot.Desc using ( K )
open import DirectedHoTT.Examples.Knot.Terms using ( SubTy )
open import DirectedHoTT.Examples.Knot.Sorts
  using ( sTy; sDesc; sDCon; sIDesc; sICon )
open import DirectedHoTT.Examples.Knot.PayTy using ( payTyK; ⊢payTyK )
open import DirectedHoTT.Examples.Knot.IPayTy using ( ipayTyK; ⊢ipayTyK )

-- ★ `payTy D C`, in the kernel's order, with the depth in front.
payTyKᵏ : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ → RTm Γ
payTyKᵏ n D C = payTyK n C D

⊢payTyKᵏ : {Γ : Ctx} {n D C : RTm ⌊ Γ ⌋} →
           Γ ⊢ n ∷ Nat → Γ ⊢ D ∷ K (pair sDesc n) → Γ ⊢ C ∷ K (pair sDCon n) →
           Γ ⊢ payTyKᵏ n D C ∷ K (pair sTy n)
⊢payTyKᵏ dn dD dC = ⊢payTyK dn dC dD

-- ★ `ipayTy D I σ C`, likewise.  ⚠ TWO depths in front: the ICon's own
--   (`dd`) and the target (`n`) — the kernel writes neither, exactly as
--   with `subTmAtK`/`extNK`.
ipayTyKᵏ : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ → RTm Γ → RTm Γ → RTm Γ → RTm Γ
ipayTyKᵏ dd n D I σ C = ipayTyK dd C n σ D I

⊢ipayTyKᵏ : {Γ : Ctx} {dd n D I σ C : RTm ⌊ Γ ⌋} →
            Γ ⊢ dd ∷ Nat → Γ ⊢ n ∷ Nat →
            Γ ⊢ D ∷ K (pair sIDesc n) → Γ ⊢ I ∷ K (pair sTy nzero) →
            Γ ⊢ σ ∷ SubTy dd n → Γ ⊢ C ∷ K (pair sICon dd) →
            Γ ⊢ ipayTyKᵏ dd n D I σ C ∷ K (pair sTy n)
⊢ipayTyKᵏ ddd dn dD dI dσ dC = ⊢ipayTyK ddd dC dn dσ dD dI
