------------------------------------------------------------------------
-- OCP-0009 · EXAMPLES — ⚠ SPIKE SUPPORT: the PER-TAG PAYLOAD's family.
--
-- `JUDGEMENT-ATTEMPTS` §10.5 recommends splitting the merged judgement's
-- index by WHO READS IT: keep flat and projectable the five slots
-- consumers already read, and put the merge-only subjects behind ONE
-- per-tag payload
--
--     IJudge = Σ' Nat (Σ' Ctx (Σ' Tm (Σ' Ty (Σ' Nat (IMu IxD INat ⟨tag⟩)))))
--
-- §10.6 left the COST of that sixth slot unmeasured.  This module is the
-- payload family a width-6 measurement needs, at its SMALLEST: one
-- constructor, no fields.
--
-- ★ THE DUMMY IS AVAILABLE AT EVERY TAG, and that is the whole trick —
--   `iι` targets the AMBIENT index, so `icon zero unit` inhabits
--   `IMu IxD INat i` for ANY `i`.  The same property the width spike
--   relied on when it padded with each sort's NULLARY former, and the
--   reason a padded slot can be typed without knowing the row's tag.
--
-- ⚠ THIS IS NOT THE REAL `IxD`.  The real one has a constructor per
--   merged judgement, each Fording its index to its own tag and carrying
--   that judgement's own subjects.  This one exists to measure WIDTH,
--   which is what the 43 typing rows would pay: exactly one dummy.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Knot.IxD where
open import Agda.Builtin.Nat using ( zero ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax
  using ( Cx; ε; _∙; RTy; RTm; IMu; unit; icon; Nat
        ; ICon; IDesc; iι; inil; _◂_; hereID )
open import DirectedHoTT.Spec.Typing
  using ( Ctx; ⌊_⌋; _⊢_∷_; ⊢unit; ⊢icon
        ; IConWf; iwf-ι; IDescWf; idwf-nil; idwf-cons )
open import DirectedHoTT.Examples.Knot.Sorts using ( toI )
open import DirectedHoTT.Examples.Knot.CtxD using ( INat )

-- the one constructor: no fields, available at every index
cIx : ICon (ε ∙)
cIx = iι

IxD : IDesc
IxD = cIx ◂ inil

IxWf : IDescWf INat IxD
IxWf = idwf-cons iwf-ι idwf-nil

-- ★ the payload TYPE at any index — `ipayTy … iι = Unit`, so the value
--   is `unit` and its typing is `⊢unit`.
IxUnitK : {Γ : Cx} → RTm Γ
IxUnitK = icon zero unit

-- ⚠ `d` EXPLICIT, to match the emitter's `DX` role, which hands a slot
--   the index TERM and then its derivation — the same shape every
--   nullary knot former's `…Kv` lemma takes.
⊢IxUnitK : {Δ : Ctx} (d : RTm ⌊ Δ ⌋) →
           Δ ⊢ d ∷ Nat → Δ ⊢ IxUnitK ∷ IMu IxD INat d
⊢IxUnitK _ dd = ⊢icon IxWf hereID (toI dd) ⊢unit
