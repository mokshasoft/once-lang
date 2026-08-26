------------------------------------------------------------------------
-- OCP-0009 · LIB — ★★★ `sz` FOR AN ARBITRARY INDEXED DESCRIPTION.
--
-- ⚠⚠ THE POINT IS THAT NOTHING HERE IS PER-CONSTRUCTOR.  `Examples/Knot`
--   built `sz` by ENUMERATING 53 methods and then 53 tuple rungs; that
--   is 147s and ~1300 generated lines, and two attempts to speed it up
--   by making a RUNG generic both made it worse (see `gen-knot.py`).
--   The enumeration was never removable from the rung, because it lives
--   in the CONSUMER.  It is removable HERE, by noticing that the methods
--   are not arbitrary data:
--
--       every method is  `lam (lam (lam (suc <sum of the IH entries>)))`
--
--   and the sum is determined by the `ICon`'s RECURSIVE fields.  So the
--   method is COMPUTED from the constructor, the tuple is COMPUTED from
--   the description, and both proofs are one induction at an ABSTRACT
--   description — which is the condition a generic lemma needs in order
--   to actually be generic.
--
-- ★ CONSTANT `Nat` MOTIVE throughout: `iinst i t Nat` IS `Nat`, so the
--   IH tuple is a nest of `Σ' Nat` and the method's codomain is free.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Lib.ISz where
open import normalizer.Syntax.Types using ( _≡_; refl; sym; trans; cong )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax
  using ( Cx; ε; _∙; vz; vs; var; RTy; RTm; Unit; Σ'; El; IMu; Nat; Π
        ; lam; pair; fst; snd; unit; nzero; nsuc
        ; ICon; IDesc; iι; iρ; iκ; inil; _◂_
        ; ipayTy; Sub; extS; subTm; subTy; renTy; isingle; iext
        ; εwkTy; εwk-ren; ipayTy-ren; ipayTy-cong )
open import DirectedHoTT.Spec.Typing
  using ( Ctx; ◇; _▹_; ⌊_⌋
        ; _⊢_∷_; ⊢var; here; there; ⊢lam; ⊢pair; ⊢fst; ⊢snd; ⊢unit
        ; ⊢nzero; ⊢nsuc
        ; _⊢ty_; ty-Unit; ty-Σ; ty-Nat
        ; IConWf; iwf-ι; iwf-ρ; iwf-κ
        ; IDescWf; IDescWfFrom; idwf-nil; idwf-cons
        ; imethTy; imethsTyFrom; iihTy )
open import DirectedHoTT.Metatheory.SubjectReduction
  using ( ⊢-cast; ren-ty; isingle-Sub⊢; iihTy-wf; iihTy-ren; iihTy-cong )
open import DirectedHoTT.Lib.Wk using ( wk-singleTy )
open import DirectedHoTT.Lib.Nat using ( plusTm; ⊢plus )
open import DirectedHoTT.Lib.IPay using ( ipayTy-wf; imethsTyFromNat-wf )

------------------------------------------------------------------------
-- 1. THE SUM OVER AN IH TUPLE — one `plus` per RECURSIVE field.
--
-- ⚠ κ fields contribute NOTHING and must not step the projection:
--   `iihTy` skips them outright, so the tuple has one entry per `iρ`
--   and the recursion here has to mirror that exactly.
------------------------------------------------------------------------

szSum : {Γ Δ : Cx} → ICon Δ → RTm Γ → RTm Γ
szSum iι       ih = nzero
szSum (iρ j C) ih = plusTm (fst ih) (szSum C (snd ih))
szSum (iκ κ C) ih = szSum C ih

-- ⚠ THE TELESCOPE IS A `Cx`, NOT A `Ctx`.  Indexed by a `Ctx Θ` the
--   recursion cannot solve its own implicit: only `⌊ Θ ⌋` appears, `⌊_⌋`
--   is not injective, and `⌊ Θ ⌋ ∙ = ⌊ Θ\' ⌋` does not determine `Θ\'`.
⊢szSum : {Γ : Ctx} {Δ : Cx} (D : IDesc) (I : RTy ε) (σ : Sub Δ ⌊ Γ ⌋)
         (C : ICon Δ) (q ih : RTm ⌊ Γ ⌋) →
         Γ ⊢ ih ∷ iihTy D I σ C q Nat → Γ ⊢ szSum C ih ∷ Nat
⊢szSum D I σ iι       q ih d = ⊢nzero
⊢szSum D I σ (iρ j C) q ih d =
  ⊢plus (⊢fst d)
        (⊢szSum D I (iext σ (fst q)) C (snd q) (snd ih)
                (⊢-cast (wk-singleTy {v = fst ih}
                                     (iihTy D I (iext σ (fst q)) C (snd q) Nat))
                        (⊢snd d)))
⊢szSum D I σ (iκ κ C) q ih d = ⊢szSum D I (iext σ (fst q)) C (snd q) ih d

------------------------------------------------------------------------
-- 2. THE METHOD, COMPUTED FROM THE CONSTRUCTOR.
--
-- ⚠ THE CONTEXTS ARE PINNED.  `⊢lam`'s body lives one binder deeper and
--   left implicit those contexts are metas that never solve.
------------------------------------------------------------------------

szMethod : {Γ Δ : Cx} → ICon Δ → RTm Γ
szMethod C = lam (lam (lam (nsuc (szSum C (var vz)))))

⊢szMethod : {Γ : Ctx} (D : IDesc) (I : RTy ε) (k : ℕ) (C : ICon (ε ∙)) →
            IDescWf I D → IConWf D I (◇ ▹ εwkTy I) C →
            ({Δ : Ctx} → Δ ⊢ty εwkTy I) →
            Γ ⊢ szMethod C ∷ imethTy D I k C Nat
⊢szMethod {Γ = Γ} D I k C wD wC tI =
  ⊢lam tI
    (⊢lam (ipayTy-wf {Γ = Γ ▹ εwkTy I} D I (isingle (var vz)) C
                     wD wC (isingle-Sub⊢ (⊢-cast (εwk-ren vs I) (⊢var here))))
      (⊢lam (iihTy-wf {Γ = (Γ ▹ εwkTy I) ▹ ipayTy D I (isingle (var vz)) C}
                      D I Nat (isingle (var (vs vz))) C (var vz) wC
                      (isingle-Sub⊢ (⊢-cast (trans (cong (renTy vs) (εwk-ren vs I))
                                                   (εwk-ren vs I))
                                            (⊢var (there here)))) ty-Nat
                      (⊢-cast (trans (ipayTy-ren vs D I (isingle (var vz)) C)
                                     (ipayTy-cong D I C (λ { vz → refl ; (vs ()) })))
                              (⊢var here)))
        -- ⚠ the IH-tuple variable, RETYPED.  `⊢var here` hands back
        --   `renTy vs (iihTy … (isingle (var (vs vz))) C (var vz) …)`,
        --   and the sum is stated one binder out.  `iihTy-ren` moves the
        --   renaming inside; `iihTy-cong` then identifies the two
        --   environments, which agree POINTWISE and not definitionally.
        (⊢nsuc (⊢szSum D I (isingle (var (vs (vs vz)))) C (var (vs vz)) (var vz)
                 (⊢-cast (trans (iihTy-ren vs D I (isingle (var (vs vz))) C
                                           (var vz) Nat)
                                (iihTy-cong D I C (var (vs vz)) Nat
                                            (λ { vz → refl ; (vs ()) })))
                         (⊢var here))))))

------------------------------------------------------------------------
-- 3. ★★★ THE TUPLE, COMPUTED FROM THE DESCRIPTION.  ONE induction, and
--    the description stays a VARIABLE throughout — which is the whole
--    reason this is O(n) where the enumerated version is O(n²).
------------------------------------------------------------------------

szMeths : {Γ : Cx} → IDesc → RTm Γ
szMeths inil    = unit
szMeths (C ◂ E) = pair (szMethod C) (szMeths E)

⊢szMeths : {Γ : Ctx} (D : IDesc) (I : RTy ε) (j : ℕ) (E : IDesc) →
           IDescWf I D → IDescWfFrom D I E →
           ({Δ : Ctx} → Δ ⊢ty εwkTy I) →
           Γ ⊢ szMeths E ∷ imethsTyFrom D I Nat j E
⊢szMeths D I j inil    wD idwf-nil        tI = ⊢unit
⊢szMeths D I j (C ◂ E) wD (idwf-cons wC wE) tI =
  ⊢pair (ren-ty (imethsTyFromNat-wf D I (suc j) E wD wE tI) there)
        (⊢szMethod D I j C wD wC tI)
        (⊢-cast (sym (wk-singleTy {v = szMethod C}
                                  (imethsTyFrom D I Nat (suc j) E)))
                (⊢szMeths D I (suc j) E wD wE tI))
