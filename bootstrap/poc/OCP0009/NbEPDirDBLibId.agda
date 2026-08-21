------------------------------------------------------------------------
-- OCP-0009 · WF LIBRARY — SYMMETRY OF `Id`, AND ITS `Prv` LIFT.
--
-- ★ `sym` IS DERIVED, NOT PRIMITIVE.  `jsub` at the family `λ y. Id y t`,
--   seeded with reflexivity.  The symmetric axis gets it from `jsub`
--   alone — contrast the directed axis, which needed a former (`ap`).
--
-- ⚠ WHY THIS MODULE EXISTS.  `…LibAmrecInd` carried a verbatim copy of
--   `symTm`/`⊢sym`, because a LIBRARY MAY NOT IMPORT AN EXAMPLE and the
--   only other copy was in `…ExamplesId`.  Step 6 of `amrec-ind` (`ihToPW`)
--   needs the `Prv`-level lift: the induction hypothesis lands at the
--   `amrec y` end and the goal is at the call end, so it must be turned
--   round.  That is `prvSym`, and it is spent by every gcd client.
--
-- ⚠ `…ExamplesId` KEEPS ITS OWN DERIVATION, deliberately.  It is the
--   pedagogical exhibit ("derived, not primitive") and doubles as an
--   INDEPENDENT re-derivation — the same role `agree-aIHTat'` plays for
--   `…LibRec`.  It is not dead duplication, and it is not this module's
--   client: `⊢symId`/`prvSym` are exercised through `amrecInd`.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPDirDBLibId where

open import normalizer.Syntax.Types using ( _≡_; refl; sym; cong )
open import poc.OCP0009.NbEPDirDBPi
  using ( Cx; RTm; El; U; var; vz; vs; jsub; Id; ⌜Id⌝; idrefl; ⌜Id⌝-cong₃
        ; renTm )
open import poc.OCP0009.NbEPDirDBType
  using ( Ctx; ⌊_⌋; _⊢_∷_; ⊢var; here; ⊢jsub
        ; ⊢⌜Id⌝; ⊢idrefl; ⊢conv; csymᵀ; credᵀ; El-⌜Id⌝ )
open import poc.OCP0009.NbEPDirDBSubj using ( ⊢wk; ⊢-cast; wk-cancel-tm )
open import poc.OCP0009.NbEPDirDBLibAmrec using ( Prv; prv )

------------------------------------------------------------------------
-- ★ THE TERM, and its typing.
------------------------------------------------------------------------

symTm : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ → RTm Γ
symTm c t p = jsub (⌜Id⌝ (renTm vs c) (var vz) (renTm vs t)) p (idrefl c t)

⊢symId : {Γ : Ctx} {c t u p : RTm ⌊ Γ ⌋} →
         Γ ⊢ c ∷ U → Γ ⊢ t ∷ El c → Γ ⊢ u ∷ El c →
         Γ ⊢ p ∷ Id (El c) t u →
         Γ ⊢ symTm c t p ∷ Id (El c) u t
⊢symId {c = c} {t = t} {u = u} {p = p} dc dt du dp =
  ⊢conv
    (⊢-cast (cong El (⌜Id⌝-cong₃ (wk-cancel-tm u c) refl (wk-cancel-tm u t)))
      (⊢jsub (⊢⌜Id⌝ (⊢wk dc) (⊢var here) (⊢wk dt))
             dt du dp
             (⊢-cast (cong El (sym (⌜Id⌝-cong₃ (wk-cancel-tm t c) refl
                                               (wk-cancel-tm t t))))
                     (⊢conv (⊢idrefl dc dt)
                            (csymᵀ (credᵀ (El-⌜Id⌝ c t t)))))))
    (credᵀ (El-⌜Id⌝ c u t))

------------------------------------------------------------------------
-- ★ …AND THE `Prv` LIFT, which is the form `amrec-ind` actually calls.
------------------------------------------------------------------------

prvSym : {Γ : Ctx} {c t u : RTm ⌊ Γ ⌋} →
         Γ ⊢ c ∷ U → Γ ⊢ t ∷ El c → Γ ⊢ u ∷ El c →
         Prv Γ (Id (El c) t u) → Prv Γ (Id (El c) u t)
prvSym {c = c} {t = t} dc dt du (prv e d) = prv (symTm c t e) (⊢symId dc dt du d)
