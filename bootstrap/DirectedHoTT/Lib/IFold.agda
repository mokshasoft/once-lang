------------------------------------------------------------------------
-- OCP-0009 · LIB — ★★★ A FOLD OVER AN INDEXED DESCRIPTION, at a
-- CONSTANT `Nat` motive, parametric in the ALGEBRA.
--
--     ifMeths D  :  the method tuple for `ielim D _ ifMeths _ ∷ Nat`
--
-- `Lib/ISz` is now this module at `z = 0`, `op = +`, `nd = suc`;
-- `Lib/IDepth` is it at `op = max`.
--
-- ⚠ THE MOTIVE STAYS `Nat`, deliberately.  An abstract constant motive
--   `A` would need `subTy σ A ≡ A` threaded as a parameter, where `Nat`
--   is stable DEFINITIONALLY.  Generalise the motive when something wants
--   a non-`Nat` fold, not before.
--
-- ★★ NOTHING HERE IS PER-CONSTRUCTOR.  The method is COMPUTED from the
--   `ICon` and the tuple from the `IDesc`, both by ONE induction with the
--   description a VARIABLE.  See `tools/gen-knot.py`'s step-3 note for the
--   measurement that forced this shape (enumerated 147s → computed 5s) and
--   for the two ways of half-doing it that are WORSE than either.
--
-- ⚠ NO TRAILING `op _ z`, and it is not cosmetic.  A constructor with `r`
--   recursive fields folds to `op xᵣ (… (op x₂ x₁))`, and one with a
--   SINGLE field folds to `x₁` itself rather than `op x₁ z`.  `plusTm a b`
--   recurses on `a`, so a trailing `+ 0` would cost `x₁` REDUCTION steps
--   at every node — which on a unary-recursive syntax (`lam`, `nsuc`, …)
--   turns an O(n) measure into O(n²).  This is the one place where the
--   object-level complexity of a generic fold can differ from the
--   hand-written measure it replaces, so it is worth stating.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Lib.IFold where
open import normalizer.Syntax.Types using ( _≡_; refl; sym; trans; cong )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax
  using ( Cx; ε; _∙; vz; vs; var; RTy; RTm; Unit; Σ'; El; IMu; Nat; Π
        ; lam; pair; fst; snd; unit; nzero; nsuc
        ; ICon; IDesc; iι; iρ; iκ; inil; _◂_
        ; ipayTy; Sub; extS; subTm; subTy; renTy; isingle; iext
        ; sel; ilookupD; _∈ID_; hereID; thereID
        ; εwkTy; εwk-ren; ipayTy-ren; ipayTy-cong )
open import DirectedHoTT.Spec.Typing
  using ( Ctx; ◇; _▹_; ⌊_⌋
        ; _⊢_∷_; ⊢var; here; there; ⊢lam; ⊢pair; ⊢fst; ⊢snd; ⊢unit
        ; _⊢ty_; ty-Unit; ty-Σ; ty-Nat
        ; IConWf; iwf-ι; iwf-ρ; iwf-κ
        ; IDescWf; IDescWfFrom; idwf-nil; idwf-cons
        ; imethTy; imethsTyFrom; iihTy
        ; _⟶_; _⟶*_; done; step; βfst; βsnd; ξ-fst; ξ-snd )
open import DirectedHoTT.Metatheory.SubjectReduction
  using ( ⊢-cast; ren-ty; isingle-Sub⊢; iihTy-wf; iihTy-ren; iihTy-cong )
open import DirectedHoTT.Lib.Wk using ( wk-singleTy )
open import DirectedHoTT.Lib.IPay using ( ipayTy-wf; imethsTyFromNat-wf )

------------------------------------------------------------------------
-- ★ THE ALGEBRA.  `z` for a constructor with NO recursive fields, `op` to
--   absorb one child into the accumulator, `nd` to wrap the whole node.
--   ⚠ All three must be CONTEXT-POLYMORPHIC: they are used under the
--   method's three binders, at a depth the caller never names.
------------------------------------------------------------------------

module Fold
  (z   : {Γ : Cx} → RTm Γ)
  (op  : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ)
  (nd  : {Γ : Cx} → RTm Γ → RTm Γ)
  (⊢z  : {Γ : Ctx} → Γ ⊢ z ∷ Nat)
  (⊢op : {Γ : Ctx} {a b : RTm ⌊ Γ ⌋} →
         Γ ⊢ a ∷ Nat → Γ ⊢ b ∷ Nat → Γ ⊢ op a b ∷ Nat)
  (⊢nd : {Γ : Ctx} {a : RTm ⌊ Γ ⌋} → Γ ⊢ a ∷ Nat → Γ ⊢ nd a ∷ Nat)
  where

  -- the accumulator pass: `acc` already holds at least one child
  ifTail : {Γ Δ : Cx} → ICon Δ → RTm Γ → RTm Γ → RTm Γ
  ifTail iι       acc ih = acc
  ifTail (iρ j C) acc ih = ifTail C (op (fst ih) acc) (snd ih)
  ifTail (iκ κ C) acc ih = ifTail C acc ih

  -- ★ the FIRST recursive field seeds the accumulator, which is what
  --   removes the trailing `op _ z`.
  ifSum : {Γ Δ : Cx} → ICon Δ → RTm Γ → RTm Γ
  ifSum iι       ih = z
  ifSum (iρ j C) ih = ifTail C (fst ih) (snd ih)
  ifSum (iκ κ C) ih = ifSum C ih

  -- ⚠ THE TELESCOPE IS A `Cx`, NOT A `Ctx`.  Indexed by a `Ctx Θ` the
  --   recursion cannot solve its own implicit: only `⌊ Θ ⌋` occurs, `⌊_⌋`
  --   is not injective, and `⌊ Θ ⌋ ∙ = ⌊ Θ' ⌋` does not determine `Θ'`.
  ⊢ifTail : {Γ : Ctx} {Δ : Cx} (D : IDesc) (I : RTy ε) (σ : Sub Δ ⌊ Γ ⌋)
            (C : ICon Δ) (q acc ih : RTm ⌊ Γ ⌋) →
            Γ ⊢ acc ∷ Nat → Γ ⊢ ih ∷ iihTy D I σ C q Nat →
            Γ ⊢ ifTail C acc ih ∷ Nat
  ⊢ifTail D I σ iι       q acc ih da d = da
  ⊢ifTail D I σ (iρ j C) q acc ih da d =
    ⊢ifTail D I (iext σ (fst q)) C (snd q) (op (fst ih) acc) (snd ih)
            (⊢op (⊢fst d) da)
            (⊢-cast (wk-singleTy {v = fst ih}
                                 (iihTy D I (iext σ (fst q)) C (snd q) Nat))
                    (⊢snd d))
  ⊢ifTail D I σ (iκ κ C) q acc ih da d =
    ⊢ifTail D I (iext σ (fst q)) C (snd q) acc ih da d

  ⊢ifSum : {Γ : Ctx} {Δ : Cx} (D : IDesc) (I : RTy ε) (σ : Sub Δ ⌊ Γ ⌋)
           (C : ICon Δ) (q ih : RTm ⌊ Γ ⌋) →
           Γ ⊢ ih ∷ iihTy D I σ C q Nat → Γ ⊢ ifSum C ih ∷ Nat
  ⊢ifSum D I σ iι       q ih d = ⊢z
  ⊢ifSum D I σ (iρ j C) q ih d =
    ⊢ifTail D I (iext σ (fst q)) C (snd q) (fst ih) (snd ih)
            (⊢fst d)
            (⊢-cast (wk-singleTy {v = fst ih}
                                 (iihTy D I (iext σ (fst q)) C (snd q) Nat))
                    (⊢snd d))
  ⊢ifSum D I σ (iκ κ C) q ih d =
    ⊢ifSum D I (iext σ (fst q)) C (snd q) ih d

  ------------------------------------------------------------------------
  -- THE METHOD, COMPUTED FROM THE CONSTRUCTOR.
  -- ⚠ CONTEXTS PINNED: `⊢lam`'s body lives one binder deeper, and left
  --   implicit those contexts are metas that never solve.
  ------------------------------------------------------------------------

  ifMethod : {Γ Δ : Cx} → ICon Δ → RTm Γ
  ifMethod C = lam (lam (lam (nd (ifSum C (var vz)))))

  ⊢ifMethod : {Γ : Ctx} (D : IDesc) (I : RTy ε) (k : ℕ) (C : ICon (ε ∙)) →
              IDescWf I D → IConWf D I (◇ ▹ εwkTy I) C →
              ({Δ : Ctx} → Δ ⊢ty εwkTy I) →
              Γ ⊢ ifMethod C ∷ imethTy D I k C Nat
  ⊢ifMethod {Γ = Γ} D I k C wD wC tI =
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
          -- ⚠ the IH-tuple variable, RETYPED: `⊢var here` hands back
          --   `renTy vs (iihTy …)` and the fold is stated one binder out.
          --   `iihTy-ren` moves the renaming inside, `iihTy-cong` then
          --   identifies the two environments — pointwise, not definitionally.
          (⊢nd (⊢ifSum D I (isingle (var (vs (vs vz)))) C (var (vs vz)) (var vz)
                 (⊢-cast (trans (iihTy-ren vs D I (isingle (var (vs vz))) C
                                           (var vz) Nat)
                                (iihTy-cong D I C (var (vs vz)) Nat
                                            (λ { vz → refl ; (vs ()) })))
                         (⊢var here))))))

  ------------------------------------------------------------------------
  -- ★★★ THE TUPLE, COMPUTED FROM THE DESCRIPTION.  ONE induction, and the
  --    description stays a VARIABLE — the condition a generic lemma needs
  --    in order to actually BE generic.
  ------------------------------------------------------------------------

  ifMeths : {Γ : Cx} → IDesc → RTm Γ
  ifMeths inil    = unit
  ifMeths (C ◂ E) = pair (ifMethod C) (ifMeths E)

  ⊢ifMeths : {Γ : Ctx} (D : IDesc) (I : RTy ε) (j : ℕ) (E : IDesc) →
             IDescWf I D → IDescWfFrom D I E →
             ({Δ : Ctx} → Δ ⊢ty εwkTy I) →
             Γ ⊢ ifMeths E ∷ imethsTyFrom D I Nat j E
  ⊢ifMeths D I j inil    wD idwf-nil          tI = ⊢unit
  ⊢ifMeths D I j (C ◂ E) wD (idwf-cons wC wE) tI =
    ⊢pair (ren-ty (imethsTyFromNat-wf D I (suc j) E wD wE tI) there)
          (⊢ifMethod D I j C wD wC tI)
          (⊢-cast (sym (wk-singleTy {v = ifMethod C}
                                    (imethsTyFrom D I Nat (suc j) E)))
                  (⊢ifMeths D I (suc j) E wD wE tI))

  ------------------------------------------------------------------------
  -- ★★★ SELECTING A METHOD OUT OF THE TUPLE, IN **ONE** STEP PER ROW.
  --
  -- ⚠⚠ WHY THIS IS NOT COSMETIC.  `sel k ms` is `fst (sndᵏ ms)`, and
  --   `fst`/`snd` are TERM FORMERS stepping by `βfst`/`βsnd` — not
  --   meta-level projections.  So reaching row `k` of the tuple by hand
  --   costs `k+1` reduction steps, and the `sz` agreement
  --   (`szTm ⌈t⌉ ⟶* ⌜ sz t ⌝`) over 53 rows would be ~1400 selection steps
  --   alone: **O(n²)**, the shape `Knot/Tags` records for `∈ID`.
  --
  -- ★ ONE INDUCTION REMOVES IT.  Each row then costs ONE selection step
  --   plus the fixed tail (three βs for the method's binders, then the IH
  --   projections), so the agreement becomes O(n) chains of constant
  --   length.  ⇒ the 53 rows are bulk of a size worth doing, rather than a
  --   quadratic wall.
  ------------------------------------------------------------------------

  -- a reduction under `sel k`, i.e. under `fst (sndᵏ ⟨-⟩)`
  selCong : {Γ : Cx} (k : ℕ) {ms ms' : RTm Γ} → ms ⟶ ms' → sel k ms ⟶ sel k ms'
  selCong zero    r = ξ-fst r
  selCong (suc k) r = selCong k (ξ-snd r)

  -- ★ …and the selection itself.  ⚠ The `k ∈ID E` premise is what stops it
  --   falling off the end of the list, exactly as on `⊢icon`.
  ifMeths-sel : {Γ : Cx} (E : IDesc) (k : ℕ) → k ∈ID E →
                sel k (ifMeths {Γ = Γ} E) ⟶* ifMethod (ilookupD E k)
  ifMeths-sel (C ◂ E) zero    hereID      = step (βfst _ _) done
  ifMeths-sel (C ◂ E) (suc k) (thereID p) =
    step (selCong k (βsnd _ _)) (ifMeths-sel E k p)
