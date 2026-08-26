------------------------------------------------------------------------
-- OCP-0009 · EXAMPLES — ★★★ SPIKE: CAN AN `ielim` PRODUCE AN ELEMENT OF
-- ITS OWN FAMILY AT A **SHIFTED INDEX**?
--
-- HANDOFF-2026-08-26 step A, second half — the gate on the judgement
-- layer.  `_∋_∷_`'s `here` is
--
--     here : (Γ ▹ A) ∋ vz ∷ renTy vs A
--
-- so its index mentions `renTy`, a FUNCTION of an encoded term.  For the
-- judgement to be describable, weakening must EXIST object-level: an
-- `ielim` returning a KNOT ELEMENT at a different index.  `Lib/IFold`
-- does not reach it — that folds into a CONSTANT `Nat` motive, and this
-- needs a motive that MOVES THE INDEX.
--
-- ★ THE SMALLEST THING WITH BOTH FEATURES is `wkFin : Fin n → Fin (suc n)`
--   over `Examples/Scoped`'s `Fin`: two constructors, and
--
--     M(i, t) = Fin (suc ⟨i⟩)
--
--   is a motive that mentions the INDEX slot and lands in the family
--   being eliminated.
--
-- ⚠ AND THE SECOND CONSTRUCTOR IS WHERE IT BITES.  `fsuc`'s index is
--   known only through a FORDING CONSTRAINT — `⟨i⟩ ≡ suc m` is an `Id`,
--   PROPOSITIONAL — so using the IH at the index the answer needs is a
--   TRANSPORT, not a conversion.  Fording made the description cheap
--   (§3); this is where that debt is called in.
--
-- ★★★ RESULT: IT WORKS, AND THE TRANSPORT IS ONE `⊢jsub`.
--   `jsub (⌜IMu⌝ FinD INat ⟨-⟩) (sym ford) ih : Fin ⟨i⟩`.  ⚠ AND IT
--   WORKS ONLY BECAUSE `⌜IMu⌝` IS A CODE: `⊢jsub` transports along a
--   CODE family, so an index family with no code could not be
--   transported and object-level weakening would be blocked here.  That
--   is §12's `⌜IMu⌝`-in-`U` decision being cashed, years of plan later.
--
-- ⇒ OBJECT-LEVEL RENAMING OVER AN ENCODED INDEXED FAMILY IS FEASIBLE.
--   The judgement layer's gate is open; what remains is BULK plus the
--   same transport once per Forded recursive field.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.WkFin where
open import normalizer.Syntax.Types using ( _≡_; cong )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax
  using ( Cx; ε; _∙; vz; vs
        ; RTy; U; El; Σ'; Unit; Nat; IMu
        ; RTm; var; lam; pair; fst; snd; unit; nzero; nsuc
        ; ⌜Nat⌝; ⌜Id⌝; ⌜IMu⌝; idrefl; icon; ielim; isingle; jsub; iihs
        ; ICon; IDesc; hereID; thereID; εwkTy )
open import DirectedHoTT.Spec.Typing
  using ( Ctx; ◇; _▹_; ⌊_⌋; wk-single
        ; _⊢_∷_; ⊢var; here; there; ⊢conv; ⊢pair; ⊢fst; ⊢snd; ⊢unit
        ; ⊢nzero; ⊢nsuc; ⊢⌜Nat⌝; ⊢⌜Id⌝; ⊢⌜IMu⌝; ⊢idrefl; ⊢icon; ⊢lam
        ; _⊢ty_; ty-El; ty-Unit; ty-Nat; ty-Σ; ty-Π; ty-IMu
        ; imethTy; imethsTy; ⊢ielim; IDescWf
        ; _⟶*_; done; step; β; βfst; ξ-appˡ; ι-ielim
        ; _≅ᵀ_; csymᵀ; ctrnᵀ; credᵀ; El-⌜Id⌝; El-⌜IMu⌝; ⊢jsub )
open import DirectedHoTT.Metatheory.SubjectReduction
  using ( ⊢-cast; isingle-Sub⊢; iihTy-wf )
open import DirectedHoTT.Lib.IPay using ( ipayTy-wf )
open import DirectedHoTT.Lib.ArithComm using ( IdN; symN; ⊢symN )
open import DirectedHoTT.Examples.Scoped
  using ( INat; FinD; FinWf; Fin; fzeroC; fsucC; fzeroWf; fsucWf
        ; toI; fromI; toFin )

------------------------------------------------------------------------
-- 1. ★★★ THE MOTIVE THAT MOVES THE INDEX.
--
--     M(i, t) = Fin (suc i)
--
-- Every motive in the development so far has been CONSTANT (`Nat`) or a
-- `Π` into a constant.  This one lands in the family being eliminated,
-- at an index one greater than the scrutinee's.
------------------------------------------------------------------------

-- ⚠ CONTEXT-GENERIC: a method's motive lives at the METHOD's ambient,
--   not at `ε`.
wkMot : {Γ : Cx} → RTy ((Γ ∙) ∙)
wkMot = IMu FinD INat (nsuc (var (vs vz)))

⊢wkMot : {Γ : Ctx} → ((Γ ▹ εwkTy INat) ▹ IMu FinD INat (var vz)) ⊢ty wkMot
⊢wkMot = ty-IMu FinWf (toI (⊢nsuc (fromI (⊢var (there here)))))

------------------------------------------------------------------------
-- 2. THE `fzero` METHOD.
--
-- ⚠⚠ THE PAYLOAD ⊢ty IS BUILT **CONCRETELY**, NOT VIA `Lib/IPay`.
--   Routing it through `ipayTy-wf` here leaves `subTm εsub _t = ⌜Nat⌝`
--   unsolved — `icw-clo`'s closed code is unrecoverable because `εwkTm`
--   is a DEFINED function and so not injective.
--
--   ★ AND THAT IS THE SAME STATIC/DYNAMIC RULE AGAIN.  `Lib/IFold` calls
--     `ipayTy-wf` at an ABSTRACT `C` and it is exactly right there; here
--     `C` is the CONCRETE `fzeroC`, so the generic lemma has to be
--     unfolded against a known constructor and its own implicits go
--     unrecoverable.  A generic lemma is only generic if its argument
--     stays abstract — the third time that rule has decided a design
--     choice today, and the first time it points AWAY from the lemma.
------------------------------------------------------------------------

tyPayFz : {Γ : Ctx} →
          (Γ ▹ El ⌜Nat⌝) ⊢ty
          Σ' (El ⌜Nat⌝) (Σ' (El (⌜Id⌝ ⌜Nat⌝ (var (vs vz)) (nsuc (var vz)))) Unit)
tyPayFz =
  ty-Σ (ty-El ⊢⌜Nat⌝)
    (ty-Σ (ty-El (⊢⌜Id⌝ ⊢⌜Nat⌝ (⊢var (there here))
                               (toI (⊢nsuc (fromI (⊢var here))))))
          ty-Unit)

wkFzero : {Γ : Cx} → RTm Γ
wkFzero =
  lam (lam (lam
    (icon zero
      (pair (var (vs (vs vz)))                       -- m := the index
        (pair (idrefl ⌜Nat⌝ (nsuc (var (vs (vs vz)))))
              unit)))))

⊢wkFzero : {Γ : Ctx} → Γ ⊢ wkFzero ∷ imethTy FinD INat zero fzeroC wkMot
⊢wkFzero =
  ⊢lam (ty-El ⊢⌜Nat⌝)
    (⊢lam tyPayFz
      (⊢lam ty-Unit
        (⊢icon FinWf hereID
               (toI (⊢nsuc (fromI (⊢var (there (there here))))))
               (⊢pair (ty-Σ (ty-El (⊢⌜Id⌝ ⊢⌜Nat⌝
                                     (toI (⊢nsuc (fromI (⊢var (there (there (there here)))))))
                                     (toI (⊢nsuc (fromI (⊢var here))))))
                            ty-Unit)
                      (⊢var (there (there here)))
                      (⊢pair ty-Unit
                             (⊢conv (⊢idrefl ⊢⌜Nat⌝
                                      (toI (⊢nsuc (fromI (⊢var (there (there here)))))))
                                    (csymᵀ (credᵀ (El-⌜Id⌝ ⌜Nat⌝
                                                    (nsuc (var (vs (vs vz))))
                                                    (nsuc (var (vs (vs vz))))))))
                             ⊢unit)))))

------------------------------------------------------------------------
-- 3. ★★★ THE `fsuc` METHOD — WHERE FORDING'S DEBT IS CALLED IN.
--
-- `fsuc`'s own index is known only as `⟨i⟩ ≡ suc m`, an `Id` — so it is
-- PROPOSITIONAL.  The IH arrives at `Fin (suc m)` and the answer is
-- wanted at `Fin ⟨i⟩`.  Those are the same type only up to that `Id`, so
-- the step is a TRANSPORT and not a conversion:
--
--     jsub (⌜IMu⌝ FinD INat ⟨-⟩) (sym ford) ih   :  Fin ⟨i⟩
--
-- ★ `⊢jsub` is CODE-INDEXED, and `⌜IMu⌝` is a code — which is exactly
--   why §12 put `⌜IMu⌝` in `U` in the first place.  Had the index family
--   had no code, this step would not exist and object-level weakening
--   would be blocked here.
------------------------------------------------------------------------

tyPayFs : {Γ : Ctx} →
          (Γ ▹ El ⌜Nat⌝) ⊢ty
          Σ' (El ⌜Nat⌝)
            (Σ' (IMu FinD INat (var vz))
               (Σ' (El (⌜Id⌝ ⌜Nat⌝ (var (vs (vs vz))) (nsuc (var (vs vz))))) Unit))
tyPayFs =
  ty-Σ (ty-El ⊢⌜Nat⌝)
    (ty-Σ (ty-IMu FinWf (⊢var here))
      (ty-Σ (ty-El (⊢⌜Id⌝ ⊢⌜Nat⌝ (⊢var (there (there here)))
                                 (toI (⊢nsuc (fromI (⊢var (there here)))))))
            ty-Unit))

-- ⚠ TWO binders in, not one: the IH tuple sits after the index AND the
--   payload, so `⊢var here` is the PAYLOAD and `⊢fst` reaches `m`.
tyIHFs : {Γ : Ctx} →
         ((Γ ▹ El ⌜Nat⌝) ▹
          Σ' (El ⌜Nat⌝)
            (Σ' (IMu FinD INat (var vz))
               (Σ' (El (⌜Id⌝ ⌜Nat⌝ (var (vs (vs vz))) (nsuc (var (vs vz))))) Unit)))
         ⊢ty _
tyIHFs = ty-Σ (ty-IMu FinWf (toI (⊢nsuc (fromI (⊢fst (⊢var here)))))) ty-Unit

wkFsuc : {Γ : Cx} → RTm Γ
wkFsuc =
  lam (lam (lam
    (icon (suc zero)
      (pair (var (vs (vs vz)))                        -- m' := the index
        (pair (jsub (⌜IMu⌝ FinD INat (var vz))        -- transport the IH
                    (symN (var (vs (vs vz)))
                          (fst (snd (snd (var (vs vz))))))
                    (fst (var vz)))
          (pair (idrefl ⌜Nat⌝ (nsuc (var (vs (vs vz)))))
                unit))))))

-- `El (⌜IMu⌝ FinD INat n) ≅ᵀ Fin n`, the direction `Scoped.toFin` lacks
fromFin : {Γ : Ctx} {n t : RTm ⌊ Γ ⌋} →
          Γ ⊢ t ∷ El (⌜IMu⌝ FinD INat n) → Γ ⊢ t ∷ Fin n
fromFin d = ⊢conv d (credᵀ El-⌜IMu⌝)

⊢wkFsuc : {Γ : Ctx} → Γ ⊢ wkFsuc ∷ imethTy FinD INat (suc zero) fsucC wkMot
⊢wkFsuc =
  ⊢lam (ty-El ⊢⌜Nat⌝)
    (⊢lam tyPayFs
      (⊢lam tyIHFs
        (⊢icon FinWf (thereID hereID)
               (toI (⊢nsuc (fromI (⊢var (there (there here))))))
               (⊢pair (ty-Σ (ty-IMu FinWf (⊢var here))
                            (ty-Σ (ty-El (⊢⌜Id⌝ ⊢⌜Nat⌝
                                           (toI (⊢nsuc (fromI (⊢var (there (there (there (there here))))))))
                                           (toI (⊢nsuc (fromI (⊢var (there here)))))))
                                  ty-Unit))
                      (⊢var (there (there here)))
                      (⊢pair (ty-Σ (ty-El (⊢⌜Id⌝ ⊢⌜Nat⌝
                                            (toI (⊢nsuc (fromI (⊢var (there (there (there here)))))))
                                            (toI (⊢nsuc (fromI (⊢var (there (there (there here)))))))))
                                   ty-Unit)
                             -- ★★★ THE TRANSPORT.  `Fin (suc m) → Fin ⟨i⟩`,
                             --   along the ford read BACKWARDS.
                             (fromFin
                               (⊢jsub (⊢⌜IMu⌝ FinWf (⊢var here))
                                      (toI (⊢nsuc (fromI (⊢fst (⊢var (there here))))))
                                      (⊢var (there (there here)))
                                      (⊢symN (fromI (⊢var (there (there here))))
                                             (⊢nsuc (fromI (⊢fst (⊢var (there here)))))
                                             (⊢conv (⊢fst (⊢snd (⊢snd (⊢var (there here)))))
                                                    (credᵀ (El-⌜Id⌝ ⌜Nat⌝ _ _))))
                                      (toFin (⊢fst (⊢var here)))))
                             (⊢pair ty-Unit
                                    (⊢conv (⊢idrefl ⊢⌜Nat⌝
                                             (toI (⊢nsuc (fromI (⊢var (there (there here)))))))
                                           (csymᵀ (credᵀ (El-⌜Id⌝ ⌜Nat⌝ _ _))))
                                    ⊢unit))))))

------------------------------------------------------------------------
-- 4. ★★★ AND `wkFin` ITSELF.
------------------------------------------------------------------------

tyΠFz : {Γ : Ctx} → Γ ⊢ty imethTy FinD INat zero fzeroC wkMot
tyΠFz = ty-Π (ty-El ⊢⌜Nat⌝)
          (ty-Π tyPayFz
            (ty-Π ty-Unit
              (ty-IMu FinWf (toI (⊢nsuc (fromI (⊢var (there (there here)))))))))

tyΠFs : {Γ : Ctx} → Γ ⊢ty imethTy FinD INat (suc zero) fsucC wkMot
tyΠFs = ty-Π (ty-El ⊢⌜Nat⌝)
          (ty-Π tyPayFs
            (ty-Π tyIHFs
              (ty-IMu FinWf (toI (⊢nsuc (fromI (⊢var (there (there here)))))))))

wkMeths : {Γ : Cx} → RTm Γ
wkMeths = pair wkFzero (pair wkFsuc unit)

⊢wkMeths : {Γ : Ctx} → Γ ⊢ wkMeths ∷ imethsTy FinD INat wkMot FinD
⊢wkMeths =
  ⊢pair (ty-Σ tyΠFs ty-Unit) ⊢wkFzero
    (⊢pair ty-Unit ⊢wkFsuc ⊢unit)

-- ★★★ OBJECT-LEVEL WEAKENING: `Fin n → Fin (suc n)`, by `ielim`.
wkFinTm : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ
wkFinTm n k = ielim FinD n wkMeths k

⊢wkFinTm : {Γ : Ctx} {n k : RTm ⌊ Γ ⌋} →
           Γ ⊢ n ∷ El ⌜Nat⌝ → Γ ⊢ k ∷ Fin n →
           Γ ⊢ wkFinTm n k ∷ Fin (nsuc n)
-- ⚠ ONE `wk-single`.  `iinst n k M` weakens the index past the scrutinee
--   binder and substitutes it back, and that round trip is propositional
--   — the same residue every concrete use of a two-slot motive pays.
⊢wkFinTm {n = n} dn dk =
  ⊢-cast (cong (λ z → IMu FinD INat (nsuc z)) (wk-single n))
         (⊢ielim FinWf ⊢wkMot dn ⊢wkMeths dk)

------------------------------------------------------------------------
-- 5. ★★ …AND IT COMPUTES.  THE FORCING RUNG.
--
-- ⚠ A TYPING DERIVATION IS NOT A FUNCTION.  `⊢wkFinTm` says the term
--   inhabits the right type; it does not say `ielim` ever fires on it.
--   `fz : Fin 1` weakens to `fzero` at index 2 — five steps, one
--   `ι-ielim`, one method selection, three βs.
------------------------------------------------------------------------

fzPay : {Γ : Cx} → RTm Γ
fzPay = pair nzero (pair (idrefl ⌜Nat⌝ (nsuc nzero)) unit)

wk-fz : {Γ : Cx} →
        wkFinTm {Γ} (nsuc nzero) (icon zero fzPay)
          ⟶* icon zero (pair (nsuc nzero)
                             (pair (idrefl ⌜Nat⌝ (nsuc (nsuc nzero))) unit))
wk-fz =
  step (ι-ielim FinD (nsuc nzero) wkMeths zero fzPay)
  (step (ξ-appˡ (ξ-appˡ (ξ-appˡ (βfst wkFzero (pair wkFsuc unit)))))
  (step (ξ-appˡ (ξ-appˡ (β _ (nsuc nzero))))
  (step (ξ-appˡ (β _ fzPay))
  (step (β _ (iihs FinD wkMeths (isingle (nsuc nzero)) fzeroC fzPay)) done))))
