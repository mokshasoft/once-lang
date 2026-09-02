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
        ; ICon; IDesc; εwkTy; IMu; natrec; app; fst )
open import DirectedHoTT.Spec.Typing
  using ( Ctx; ◇; _▹_; ⌊_⌋; _⊢_∷_; _⊢ty_; ⊢var; here; there
        ; ⊢snd; ⊢lam; ty-Π; ty-Nat; ty-IMu; IConWf; imethTy
        ; ⊢natrec; ⊢app; ⊢fst )
open import DirectedHoTT.Lib.IPay using ( ⊢methLam )
open import DirectedHoTT.Examples.Knot.Sorts
  using ( IPair; ⊢IPair; sDCon; ⊢sDCon; ⊢ixP )
open import DirectedHoTT.Examples.Knot.Desc using ( KnotD )
open import DirectedHoTT.Examples.Knot.Wf using ( KnotWf; cDesc-consWf )
open import DirectedHoTT.Examples.Knot.Desc using ( cDesc-cons )
open import DirectedHoTT.Examples.Knot.Tags using ( tagDesc-cons )
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

------------------------------------------------------------------------
-- ★★★ THE ONE REAL ROW — and there is only one, which is the first
--   pleasant surprise here.
--
--     lookupD dnil    _       = dι          ← IS the junk method
--     lookupD (C ◃ D) zero    = C
--     lookupD (C ◃ D) (suc k) = lookupD D k
--
--   `dnil`'s answer is `dι` at every `k`, which is exactly what
--   `lookupJunk` already is.  ⇒ 52 constant rows and ONE real one, where
--   `Knot/Nrs` and `Knot/Single` each had two.
--
-- ★ `cDesc-cons` has TWO `iρ` fields (the head `DCon` and the tail
--   `Desc`), so BOTH carry an IH.  The method reads the head from the
--   PAYLOAD and the tail's answer from the IH — `Knot/Pw`'s `pwHom`
--   pattern, which takes `fst (var vz)` of the IH tuple.
--
-- ⚠ AND THE `natrec` MOTIVE IS CONSTANT.  `lookupD D k`'s result type
--   does not mention `k`, so `M` is the target type WEAKENED, and all
--   three of `⊢natrec`'s substitutions collapse by `wk-singleTy`.  That
--   is the non-dependent case and it is why no ford appears here.
------------------------------------------------------------------------

lookupCons : {Γ : Cx} → RTm Γ
lookupCons =
  lam (lam (lam (lam
    (natrec (fst (var (vs (vs vz))))                          -- zero ↦ C
            (app (fst (snd (var (vs (vs (vs vz)))))) (var (vs vz)))
            (var vz)))))                                       -- on k

-- ⬜ `⊢lookupCons` — NEXT, and the obstacle is now SOLVED IN `Lib/`;
--   what is left is this call site's plumbing.
--
-- ★★★ THE TRANSPORT IS LIFTED: `Lib/IPay.⊢ihHere`/`⊢ihSkipρ`/`⊢ihSkipκ`
--   reach any `iρ` field's IH in any constructor.  `⊢ihSkipκ` is the
--   IDENTITY (a κ field contributes no IH, so `iihTy` skips it
--   definitionally) and `⊢ihSkipρ` costs the single `wk-singleTy` that
--   cancels the tail's weakening.  Every remaining `ielim` over the knot
--   needs exactly these.
--
-- ⚠⚠ AND THE CALL SITE MUST PIN THREE THINGS, because `iihTy` IS A
--   FUNCTION AND CANNOT BE INVERTED — a `_` in any of them leaves a
--   stuck constraint, never an error you can read:
--     · the `ICon` at each step   ✅ done below in the parked block
--     · `q`, the payload variable ✅ `var (vs (vs (vs (vs vz))))`
--     · `M`, the motive           ⬜ THE ONE REMAINING — it is
--       `lookupMotK` weakened as `⊢methLam` weakens it
--       (`renTy (extR (extR vs))`, twice) and then once more per binder
--       the `natrec` branch adds.
--   ⇒ `pin-implicits-on-defined-set-types`, third instance in this tree.
--
-- ★ Everything else in the row is settled: the term type-checks, the de
--   Bruijn positions are confirmed, and the `natrec` motive is constant.
--
-- The term above type-checks and the derivation is written; what it
-- still owes is ONE transport, and it is the one every real method in
-- this family pays:
--
--   `⊢app`'s function argument is the IH for the TAIL field, whose type
--   is the motive at that field's index — i.e. `iatCon` applied, which
--   presents as
--
--       pair (subTm (single ⟨k⟩) (subTm (extS (single (fst p))) (renTm … )))
--
--   where the motive wants `pair sDCon (snd ⟨i⟩)`.  ⇒ the same
--   `iatCon`-shaped retype `Knot/Nrs`'s `⊢nrsVz`/`⊢nrsVs` and
--   `Knot/Single`'s `⊢singleVs` discharge, and `Lib/ISub`'s
--   `⊢fordMapK`/`⊢motAppK` are what they use.
--
-- ⚠ THE de BRUIJN POSITIONS ARE SETTLED and cost one round: `⊢methLam`'s
--   body sits at THREE binders (index · payload · IH), the motive's `Π`
--   adds a fourth (`k`), and `natrec`'s successor branch adds TWO more
--   (the predecessor and `natrec`'s own IH) — so inside `s` the method's
--   IH tuple is THREE back, not four.  That is written down here because
--   it is the part that is easy to get wrong twice.
--
-- ★ AND THE MOTIVE IS CONSTANT, so none of `⊢natrec`'s three
--   substitutions needs a ford — only the IH's index does.

{- TODO — see the note above.
⊢lookupCons : {Γ : Ctx} →
              Γ ⊢ lookupCons
                ∷ imethTy KnotD IPair tagDesc-cons cDesc-cons lookupMotK
⊢lookupCons =
  ⊢methLam KnotD IPair tagDesc-cons cDesc-cons KnotWf cDesc-consWf
           ⊢IPair ⊢lookupMotK
    (⊢lam ty-Nat
      (⊢natrec (ty-IMu KnotWf
                  (⊢ixP ⊢sDCon (⊢snd (⊢var (there (there (there (there here))))))))
               (⊢fst (⊢var (there (there here))))
               -- ⚠ `s` lives under TWO more binders (the predecessor and
               --   `natrec`'s own IH), so the method's IH tuple is THREE
               --   back, not four.
               (⊢app (⊢fst (⊢snd (⊢var (there (there (there here))))))
                     (⊢var (there here)))
               (⊢var here)))
-}
