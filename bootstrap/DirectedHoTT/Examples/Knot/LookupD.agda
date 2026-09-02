------------------------------------------------------------------------
-- OCP-0009 · EXAMPLES — ★★★ `lookupD`, OBJECT-LEVEL.
--
--     lookupD : Desc → ℕ → DCon             `Spec/Syntax:968`
--     lookupD dnil    _       = dι
--     lookupD (C ◃ D) zero    = C
--     lookupD (C ◃ D) (suc k) = lookupD D k
--
-- ⚠ `⊢con` names it (`payTy D (lookupD D k)`) and so does `ι-elim`.
--
-- ★★★ BUILT **GENERAL IN THE DEPTH**, deliberately, and the two callers
--   are why: the merged judgement block binds descriptions CLOSED (at 0)
--   while the `_⟶_` family binds them at the AMBIENT depth.  A depth-0
--   version would serve `⊢con` and be useless to `ι-elim`, and the
--   asymmetry is fatal — `εwkK` lifts `0 → n`, but bringing `ι-elim`'s
--   ambient `D` DOWN to 0 would need a strengthening, which does not
--   exist.  ⇒ the general form serves both; depth 0 is an instance.
--   `narrow-twin-shadows-general-form`, applied before being bitten.
--
-- ★ AND GENERALITY IS NEARLY FREE HERE, which is worth checking rather
--   than assuming: `cDesc-cons`'s fields are `rec sDCon ('D',)` and
--   `rec sDesc ('D',)` — BOTH at the ambient depth, unchanged.  The
--   recursion is DEPTH-PRESERVING, so there is none of the descent that
--   made `⊢Var-vsKt` and `Knot/Nrs` expensive.
--
-- ★ SHAPE: `Knot/Single`'s, not `Knot/Nrs`'s — the motive is a `Π`, so
--   every method has FOUR `lam`s.  ⚠ And unlike both, the two real rows
--   (`tagDesc-nil`/`tagDesc-cons`, 41 and 42 of 53) sit in the MIDDLE,
--   so the tuple needs a junk run on BOTH sides.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Knot.LookupD where
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax
  using ( Cx; ε; _∙; vz; vs; RTy; RTm; var; lam; snd; pair; Π; Nat
        ; ICon; IDesc; εwkTy; IMu )
open import DirectedHoTT.Spec.Typing
  using ( Ctx; ◇; _▹_; ⌊_⌋; _⊢_∷_; _⊢ty_; ⊢var; here; there
        ; ⊢snd; ⊢lam; ty-Π; ty-Nat; ty-IMu; IConWf; imethTy )
open import DirectedHoTT.Lib.IPay using ( ⊢methLam )
open import DirectedHoTT.Examples.Knot.Sorts
  using ( IPair; ⊢IPair; sDCon; ⊢sDCon; ⊢ixP )
open import DirectedHoTT.Examples.Knot.Desc using ( KnotD )
open import DirectedHoTT.Examples.Knot.Wf using ( KnotWf )
open import DirectedHoTT.Examples.Knot.Ctors using ( DCon-iK )
open import DirectedHoTT.Examples.Knot.CtorsV using ( ⊢DCon-iKv )

------------------------------------------------------------------------
-- ★ THE MOTIVE.  At index `⟨i⟩` the answer is a FUNCTION of the ℕ —
--   `lookupD` recurses on the DESCRIPTION and cases on the number, so
--   the number rides in the motive.  `Knot/SubMot` set that convention
--   for `subTm`; following it keeps the method machinery applicable.
------------------------------------------------------------------------

lookupMotK : {Γ : Cx} → RTy ((Γ ∙) ∙)
lookupMotK = Π Nat (IMu KnotD IPair (pair sDCon (snd (var (vs (vs vz))))))

⊢lookupMotK : {Γ : Ctx} →
              ((Γ ▹ εwkTy IPair) ▹ IMu KnotD IPair (var vz)) ⊢ty lookupMotK
⊢lookupMotK =
  ty-Π ty-Nat
       (ty-IMu KnotWf (⊢ixP ⊢sDCon (⊢snd (⊢var (there (there here))))))

------------------------------------------------------------------------
-- ★ THE 51 UNREACHABLE ROWS.  `dι` inhabits the codomain at EVERY index,
--   which is what makes a constant method possible at all — `Lib/IPay`'s
--   header is explicit that an ABSTRACT motive admits none.
------------------------------------------------------------------------

lookupJunk : {Γ : Cx} → RTm Γ
lookupJunk = lam (lam (lam (lam DCon-iK)))

⊢lookupJunk : {Γ : Ctx} (k : ℕ) (C : ICon (ε ∙)) →
              IConWf KnotD IPair (◇ ▹ εwkTy IPair) C →
              Γ ⊢ lookupJunk ∷ imethTy KnotD IPair k C lookupMotK
⊢lookupJunk k C wC =
  ⊢methLam KnotD IPair k C KnotWf wC ⊢IPair ⊢lookupMotK
    (⊢lam ty-Nat (⊢DCon-iKv _ (⊢snd (⊢var (there (there (there here)))))))
