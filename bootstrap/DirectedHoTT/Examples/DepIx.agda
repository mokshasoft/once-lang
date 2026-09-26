------------------------------------------------------------------------
-- OCP-0009 · EXAMPLES — ★★★ SPIKE: A **DEPENDENT INDEX TELESCOPE**.
--
-- HANDOFF-2026-08-26 step A, first half.  Every judgement of this kernel
-- is a RELATION indexed by subjects that are themselves syntax:
-- `_∋_∷_` by `(Ctx, Var, RTy)`, `_⊢ty_` by `(Ctx, RTy)`.  Encoding any of
-- them therefore needs an index type whose LATER components are typed by
-- its EARLIER ones.  Every index in the development so far has been
-- NON-dependent — `⌜Nat⌝`, or `PairIx`'s `⌜Σ⌝ ⌜Nat⌝ ⌜Nat⌝`.
--
--     I  =  ⌜Σ⌝ ⌜Nat⌝ (⌜IMu⌝ ⌜Nat⌝ TmD (var vz))   -- a depth, and a term AT it
--
-- ★ The index is a CODE (D073), and `⌜Σ⌝` BINDS, so the second component
--   mentions the first as `var vz`.  `El-⌜Σ⌝` decodes it to a dependent
--   `Σ'`, and `⊢snd` lands at `Tm (fst i)` DEFINITIONALLY — the
--   dependency costs nothing to read.
--
-- THE FAMILY, one constructor, chosen because it needs BOTH mechanisms
-- at once:
--
--     islam : (b : Tm (suc d)) → IsLam (d , lam b)
--
--   * the field `b` is a NESTED FAMILY at a COMPUTED index (a σ-field
--     of code `⌜IMu⌝`, at `suc (fst i)` rather than at the ambient);
--   * the target index is computed, so the TERM component is FORDED —
--     and its `Id` is at an `IMu` type, not at `Nat`, which no previous
--     ford has been.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.DepIx where
open import normalizer.Syntax.Types using ( _≡_; sym; subst )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax hiding ( Fin )
open import DirectedHoTT.Spec.Typing hiding ( _×_; _,,_ )
open import DirectedHoTT.Metatheory.TySub using ( ⊢wk )
open import DirectedHoTT.Lib.Sugar using ( conₗ; Dₗ )
open import DirectedHoTT.Lib.Tel
open import DirectedHoTT.Examples.Scoped
  using ( TmD; ⊢TmD; Tm; toI; ⊢isuc; tlam; ⊢tlam; tvar; ⊢tvar; ⊢ffz; fz; idTm; ⊢idTm )

------------------------------------------------------------------------
-- 1. ★★★ THE DEPENDENT INDEX CODE.
------------------------------------------------------------------------

TmC : {Γ : Cx} → RTm Γ → RTm Γ
TmC n = ⌜IMu⌝ ⌜Nat⌝ TmD n

⊢TmC : {Γ : Ctx} {n : RTm ⌊ Γ ⌋} → Γ ⊢ n ∷ El ⌜Nat⌝ → Γ ⊢ TmC n ∷ U
⊢TmC = ⊢⌜IMu⌝ ⊢⌜Nat⌝ ⊢TmD

IPT : {Γ : Cx} → RTm Γ
IPT = ⌜Σ⌝ ⌜Nat⌝ (TmC (var vz))

⊢IPT : {Γ : Ctx} → Γ ⊢ IPT ∷ U
⊢IPT = ⊢⌜Σ⌝ ⊢⌜Nat⌝ (⊢TmC (⊢var here))

-- `Tm n ≅ᵀ El (TmC n)` — the one conversion a family-typed field or ford costs
toMu : {Γ : Ctx} {n t : RTm ⌊ Γ ⌋} → Γ ⊢ t ∷ Tm n → Γ ⊢ t ∷ El (TmC n)
toMu d = ⊢conv d (csymᵀ (credᵀ El-⌜IMu⌝))

fromMu : {Γ : Ctx} {n t : RTm ⌊ Γ ⌋} → Γ ⊢ t ∷ El (TmC n) → Γ ⊢ t ∷ Tm n
fromMu d = ⊢conv d (credᵀ El-⌜IMu⌝)

unI : {Γ : Ctx} {i : RTm ⌊ Γ ⌋} → Γ ⊢ i ∷ El IPT → Γ ⊢ i ∷ Σ' (El ⌜Nat⌝) (El (TmC (var vz)))
unI d = ⊢conv d (credᵀ (El-⌜Σ⌝ _ _))

⊢π₁ : {Γ : Ctx} {i : RTm ⌊ Γ ⌋} → Γ ⊢ i ∷ El IPT → Γ ⊢ fst i ∷ El ⌜Nat⌝
⊢π₁ d = ⊢fst (unI d)

-- ⚠ `⊢snd` lands at `El (subTm (single (fst i)) (TmC (var vz)))`, which
--   COMPUTES to `El (TmC (fst i))` — the dependency is definitional.
⊢π₂ : {Γ : Ctx} {i : RTm ⌊ Γ ⌋} → Γ ⊢ i ∷ El IPT → Γ ⊢ snd i ∷ El (TmC (fst i))
⊢π₂ d = ⊢snd (unI d)

⊢ixP : {Γ : Ctx} {n t : RTm ⌊ Γ ⌋} → Γ ⊢ n ∷ El ⌜Nat⌝ → Γ ⊢ t ∷ Tm n → Γ ⊢ pair n t ∷ El IPT
⊢ixP dn dt = ⊢conv (⊢pair (ty-El (⊢TmC (⊢var here))) dn (toMu dt)) (csymᵀ (credᵀ (El-⌜Σ⌝ _ _)))

------------------------------------------------------------------------
-- 2. THE DESCRIPTION — one telescope over the index `i`, its ford tail
--    stated GENERIC IN THE INDEX TERM (the pending substitution leaves
--    `i` weakened-then-instantiated under the body's binder).
------------------------------------------------------------------------

-- ⟨i⟩ ≡ lam b, at the family's own code
fordT : {Δ : Cx} → RTm Δ → RTm Δ → Tel Δ
fordT J b = tσ (⌜Id⌝ (TmC (fst J)) (snd J) (tlam b)) tι

islamT : {Γ : Cx} → Tel (Γ ∙)
islamT = tσ (TmC (nsuc (fst (var vz))))              -- b : Tm (suc d)
           (fordT (var (vs vz)) (var vz))

IsLamTs : {Γ : Cx} → Tels (Γ ∙) 1
IsLamTs = islamT ∷ᵗ []ᵗ

IsLamD : {Γ : Cx} → RTm Γ
IsLamD = Dₗ ⌜ IsLamTs ⌝ₛ

IsLam : {Γ : Cx} → RTm Γ → RTy Γ
IsLam i = IMu IPT IsLamD i

------------------------------------------------------------------------
-- 3. WELL-FORMEDNESS — the whole question, in two fields.
------------------------------------------------------------------------

fordOK : {Γ : Ctx} {J b : RTm ⌊ Γ ⌋} → Γ ⊢ J ∷ El IPT → Γ ⊢ b ∷ El (TmC (nsuc (fst J))) →
         TelOK Γ IPT (fordT J b)
fordOK dJ db =
  ok-σ (⊢⌜Id⌝ (⊢TmC (⊢π₁ dJ)) (⊢π₂ dJ) (toMu (⊢tlam (⊢π₁ dJ) (fromMu db)))) ok-ι

islamOK : {Γ : Ctx} → TelOK (Γ ▹ El IPT) IPT islamT
islamOK = ok-σ (⊢TmC (⊢isuc (⊢π₁ (⊢var here)))) (fordOK (⊢var (there here)) (⊢var here))

IsLamOK : {Γ : Ctx} → AllOK (Γ ▹ El IPT) IPT IsLamTs
IsLamOK = islamOK ∷ᵒ []ᵒ

⊢IsLamD : {Γ : Ctx} → Γ ⊢ IsLamD ∷ DescF IPT
⊢IsLamD = ⊢Dₜ ⊢IPT IsLamOK

------------------------------------------------------------------------
-- 4. ⚠⚠ INHABITATION — WITHOUT IT §3 SAYS NOTHING.
--
-- A description can be well-formed and EMPTY (`Examples/Vec.
-- no-cons-at-zero`).  Below, `islam` inhabits `IsLam (n , λ. b)` at
-- EVERY depth and body — so the telescope is inhabited, not merely
-- admissible.
--
-- ★ AND THIS IS WHERE THE DEPENDENCY IS PAID FOR.  At a concrete
--   `pair n t` the field's type mentions `fst ⟨i⟩` and the ford mentions
--   BOTH `fst ⟨i⟩` (inside the `⌜IMu⌝` CODE) and `snd ⟨i⟩` (as an
--   endpoint): three congruences — `ξ-⌜IMu⌝ⁱ`, `ξ-⌜Id⌝ᶜ`, `ξ-⌜Id⌝ˡ`.
------------------------------------------------------------------------

islam : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ
islam n b = conₗ zero (pair b (pair (idrefl (TmC n) (tlam b)) unit))

module _ {Γ : Ctx} {n b : RTm ⌊ Γ ⌋} (dn : Γ ⊢ n ∷ El ⌜Nat⌝) (db : Γ ⊢ b ∷ Tm (nsuc n)) where
  private
    i = pair n (tlam b)
    di : Γ ⊢ i ∷ El IPT
    di = ⊢ixP dn (⊢tlam dn db)

    -- the BODY field: `fst (pair n t)` must step
    bodyAt : Γ ⊢ b ∷ El (TmC (nsuc (fst i)))
    bodyAt = ⊢conv (toMu db) (csymᵀ (credᵀ (ξ-El (ξ-⌜IMu⌝ⁱ (ξ-nsuc (βfst n (tlam b)))))))

    -- the FORD: the code's `fst` AND the endpoint's `snd` both step
    fordAt : Γ ⊢ idrefl (TmC n) (tlam b) ∷ El (⌜Id⌝ (TmC (fst i)) (snd i) (tlam b))
    fordAt =
      ⊢conv (⊢idrefl (⊢TmC dn) (toMu (⊢tlam dn db)))
            (csymᵀ (ctrnᵀ (credᵀ (ξ-El (ξ-⌜Id⌝ᶜ (ξ-⌜IMu⌝ⁱ (βfst n (tlam b))))))
                     (ctrnᵀ (credᵀ (ξ-El (ξ-⌜Id⌝ˡ (βsnd n (tlam b)))))
                            (credᵀ (El-⌜Id⌝ (TmC n) (tlam b) (tlam b))))))

    fpay = pair (idrefl (TmC n) (tlam b)) unit

  -- ★★★ `islam : IsLam (n , λ. b)`
  ⊢islam : Γ ⊢ islam n b ∷ IsLam (pair n (tlam b))
  ⊢islam =
    ⊢conₜ ⊢IPT IsLamOK nthᵗ-z di
      (⊢payσ ⊢IPT ⊢IsLamD (ok-σ (⊢TmC (⊢isuc (⊢π₁ di))) (fordOK (⊢wk di) (⊢var here))) bodyAt
        (subst (λ J → Γ ⊢ fpay ∷ El (dpay IPT IsLamD ⌜ fordT J b ⌝ᵗ)) (sym (wk-single {v = b} i))
          (⊢payσ ⊢IPT ⊢IsLamD (fordOK di bodyAt) fordAt (⊢payι ⊢IPT ⊢IsLamD ⊢unit))))

-- `islam : IsLam (0 , λx. x)` — a closed inhabitant
⊢islam₀ : ◇ ⊢ islam nzero (tvar fz) ∷ IsLam (pair nzero idTm)
⊢islam₀ = ⊢islam z (⊢tvar (⊢isuc z) (⊢ffz z))
  where z = toI ⊢nzero
