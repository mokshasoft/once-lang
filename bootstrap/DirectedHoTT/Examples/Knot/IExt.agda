------------------------------------------------------------------------
-- OCP-0009 · KNOT — ★★★ `iext` AND `iinst`, BOTH BY FACTORISATION.
--
--     iext σ t vz     = t          iinst i t M =
--     iext σ t (vs x) = σ x          subTy (single t) (subTy (extS (single i)) M)
--
-- ⚠ `iext` IS A `Var` ELIMINATOR IN THE SPEC AND NEED NOT BE ONE HERE:
--
--       iext σ t  ≡  single t ∘ extS σ
--
--     vz     `extS σ vz = var vz`, and `subTm (single t) (var vz) = t`
--     vs y   `extS σ (vs y) = w (σ y)`, and `single t` cancels the `w`
--
--   ⇒ the same move `Knot/IConS` makes for `iconS`, and for the same
--     reason: a composition of functions that already exist beats a new
--     eliminator.  ⬜ And it owes the same extra obligation — the
--     FACTORISATION, before any agreement lemma.
--
-- ★ `iinst` needs no trick: it is two `subTyAtK`s, written down.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Knot.IExt where
open import DirectedHoTT.Spec.Syntax
  using ( Cx; RTm; vz; vs; var; lam; app; pair; nsuc; renTm; Nat )
open import DirectedHoTT.Spec.Typing
  using ( Ctx; ⌊_⌋; _⊢_∷_; ⊢var; here; ⊢lam; ⊢app; ⊢nsuc; ty-IMu
        ; wk-single )
open import DirectedHoTT.Metatheory.TySub using ( ⊢wk; ⊢-cast )
open import normalizer.Syntax.Types using ( cong )
open import DirectedHoTT.Examples.Knot.Sorts
  using ( IPair; sTm; ⊢sTm; sTy; ⊢sTy; sVar; ⊢sVar; ⊢ixP )
open import DirectedHoTT.Examples.Knot.Desc using ( KnotD; K )
open import DirectedHoTT.Examples.Knot.Wf using ( KnotWf )
open import DirectedHoTT.Examples.Knot.Terms using ( SubTy )
open import DirectedHoTT.Lib.Wk using ( ren-w )
open import DirectedHoTT.Spec.Syntax using ( Π; RTy )
open import DirectedHoTT.Spec.Typing using ( _▹_ )

-- ★★ WEAKENING A `SubTy` IS NOT DEFINITIONAL, and this is its SECOND
--   customer.  `SubTy d n = Π (K (pair sVar d)) (K (pair sTm (w n)))`,
--   so `renTy vs` puts `extR vs` on the codomain's own `w n` and
--   `ren-w` is what commutes them.  `Knot/SubMot.⊢extNK` pays the same
--   cast inline, with a comment calling it one of "TWO CONVERSIONS ON
--   THE INPUT, of DIFFERENT KINDS".
-- ⬜ IT BELONGS IN `Knot/Terms`, beside `ty-SubTy` and `subBwd` — the two
--   service lemmas whose header says they exist "for the same reason
--   `SubTy` is here".  Left local only because `Terms` is deep enough
--   that touching it re-checks the whole tree; promote at consolidation.
⊢wkSubTy : {Γ : Ctx} {A : RTy ⌊ Γ ⌋} (d n : RTm ⌊ Γ ⌋) {sb : RTm ⌊ Γ ⌋} →
           Γ ⊢ sb ∷ SubTy d n →
           (Γ ▹ A) ⊢ renTm vs sb ∷ SubTy (renTm vs d) (renTm vs n)
⊢wkSubTy d n dsb =
  ⊢-cast (cong (λ z → Π (K (pair sVar (renTm vs d))) (K (pair sTm z)))
               (ren-w {ρ = vs} n))
         (⊢wk dsb)
open import DirectedHoTT.Examples.Knot.Single using ( singleK; ⊢singleK )
open import DirectedHoTT.Examples.Knot.SubMot using ( extNK; ⊢extNK )
open import DirectedHoTT.Examples.Knot.SubApp
  using ( subTmAtK; ⊢subTmAtK; subTyAtK; ⊢subTyAtK )

-- ★ `iext σ t : Sub (Δ ∙) Γ` — it CONSES, so the target depth is
--   unchanged and only the source rises.
iextK : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ → RTm Γ → RTm Γ
iextK dd n σ t =
  lam (subTmAtK (nsuc (renTm vs n)) (renTm vs n)
                (singleK (renTm vs n) (renTm vs t))
                (app (extNK (renTm vs dd) (renTm vs n) (renTm vs σ))
                     (var vz)))

⊢iextK : {Γ : Ctx} {dd n σ t : RTm ⌊ Γ ⌋} →
         Γ ⊢ dd ∷ Nat → Γ ⊢ n ∷ Nat → Γ ⊢ σ ∷ SubTy dd n →
         Γ ⊢ t ∷ K (pair sTm n) →
         Γ ⊢ iextK dd n σ t ∷ SubTy (nsuc dd) n
⊢iextK {n = n} ddd dn dσ dt =
  ⊢lam (ty-IMu KnotWf (⊢ixP ⊢sVar (⊢nsuc ddd)))
    (⊢subTmAtK (⊢nsuc (⊢wk dn)) (⊢wk dn)
               (⊢singleK (⊢wk dn) (⊢wk dt))
               -- ⚠ the same `wk-single` `Knot/IConS` pays: a `SubTy`'s
               --   codomain weakens its target, and `⊢app` substitutes
               --   the argument back into it.
               (⊢-cast (cong (λ z → K (pair sTm (nsuc z)))
                             (wk-single {v = var vz} (renTm vs n)))
                 (⊢app (⊢extNK (⊢wk ddd) (⊢wk dn) (⊢wkSubTy _ _ dσ)) (⊢var here))))

-- ★ `iinst i t M` — instantiate the TWO-slot motive at index and scrutinee.
iinstK : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ → RTm Γ → RTm Γ
iinstK n i t M =
  subTyAtK (nsuc n) n (singleK n t)
           (subTyAtK (nsuc (nsuc n)) (nsuc n) (extNK (nsuc n) n (singleK n i)) M)

⊢iinstK : {Γ : Ctx} {n i t M : RTm ⌊ Γ ⌋} →
          Γ ⊢ n ∷ Nat → Γ ⊢ i ∷ K (pair sTm n) → Γ ⊢ t ∷ K (pair sTm n) →
          Γ ⊢ M ∷ K (pair sTy (nsuc (nsuc n))) →
          Γ ⊢ iinstK n i t M ∷ K (pair sTy n)
⊢iinstK dn di dt dM =
  ⊢subTyAtK (⊢nsuc dn) dn (⊢singleK dn dt)
    (⊢subTyAtK (⊢nsuc (⊢nsuc dn)) (⊢nsuc dn)
               (⊢extNK (⊢nsuc dn) dn (⊢singleK dn di)) dM)
