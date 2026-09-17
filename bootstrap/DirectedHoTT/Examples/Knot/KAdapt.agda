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
open import DirectedHoTT.Examples.Knot.Ihs using ( fieldsK; ⊢fieldsK )
open import DirectedHoTT.Examples.Knot.Sel using ( selK; ⊢selK )
open import DirectedHoTT.Examples.Knot.Sorts using ( sTm )

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


------------------------------------------------------------------------
-- ★★★ STEP 3's TWO REDUCTION ROWS — `ι-elim`'s heads.
--
--   ι-elim : elim D ms (con k p) ⟶ fields D ms (lookupD D k) (sel k ms) p
--
-- `RedRows`' computed `NOT EMITTED` block names exactly these two:
--     ι-elim    unmapped ['fields', 'sel']
--     ι-ielim   unmapped ['ifields', 'sel']
-- ⇒ `sel` serves BOTH, so this adapter unblocks half of `ι-ielim` too;
--   the other half waits on `ifieldsK`/`iihsK`.
------------------------------------------------------------------------

-- ★ `fields D ms C m p` — the TERM is already in kernel order, so this
--   is the identity on terms.  ⚠ ONLY the TYPING permutes: `⊢fieldsK`
--   takes its `DCon` premise BEFORE its `Desc` one, and a generator
--   table that fed them positionally would hand `dD` where `dC` is due —
--   a mis-typed GENERATED PROOF, which is the failure this module exists
--   to prevent.
fieldsKᵏ : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ → RTm Γ → RTm Γ → RTm Γ → RTm Γ
fieldsKᵏ n D ms C m p = fieldsK n D ms C m p

⊢fieldsKᵏ : {Γ : Ctx} {n D ms C m p : RTm ⌊ Γ ⌋} →
            Γ ⊢ n ∷ Nat → Γ ⊢ D ∷ K (pair sDesc n) → Γ ⊢ ms ∷ K (pair sTm n) →
            Γ ⊢ C ∷ K (pair sDCon n) → Γ ⊢ m ∷ K (pair sTm n) →
            Γ ⊢ p ∷ K (pair sTm n) →
            Γ ⊢ fieldsKᵏ n D ms C m p ∷ K (pair sTm n)
⊢fieldsKᵏ dn dD dms dC dm dp = ⊢fieldsK dn dC dD dms dm dp

-- ★ `sel k ms` — the term needs no depth, but `⊢selK` does: the result
--   sits at `K (pair sTm n)` and nothing in `sel k ms` mentions `n`.
--   ⇒ absorb it, exactly as `_PRE_N`'s depth prefixes do elsewhere, so
--     the role list and the premise list have the same length.
selKᵏ : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ → RTm Γ
selKᵏ n k ms = selK k ms

⊢selKᵏ : {Γ : Ctx} {n k ms : RTm ⌊ Γ ⌋} →
         Γ ⊢ n ∷ Nat → Γ ⊢ k ∷ Nat → Γ ⊢ ms ∷ K (pair sTm n) →
         Γ ⊢ selKᵏ n k ms ∷ K (pair sTm n)
⊢selKᵏ dn dk dms = ⊢selK dn dk dms
