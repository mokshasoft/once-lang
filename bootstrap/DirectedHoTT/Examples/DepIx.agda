------------------------------------------------------------------------
-- OCP-0009 · EXAMPLES — ★★★ SPIKE: A **DEPENDENT INDEX TELESCOPE**.
--
-- HANDOFF-2026-08-26 step A, first half.  Every judgement of this kernel
-- is a RELATION indexed by subjects that are themselves syntax:
-- `_∋_∷_` by `(Ctx, Var, RTy)`, `_⊢ty_` by `(Ctx, RTy)`.  Encoding any of
-- them therefore needs an index type whose LATER components are typed by
-- its EARLIER ones.  Every index in the development so far has been
-- NON-dependent — `El ⌜Nat⌝`, or §14's `Σ' Nat Nat` — so this has never
-- been tested, and everything downstream of it is blocked on the answer.
--
--     I  =  Σ' (El ⌜Nat⌝) (Tm ⟨d⟩)          -- a depth, and a term AT it
--
-- ⚠ `I : RTy ε` must be CLOSED, and it is: `Σ'` BINDS, so the second
--   component may mention the first as `var vz` while the whole thing
--   still mentions no ambient variable.  That is the observation the
--   spike turns on.
--
-- THE FAMILY, one constructor, chosen because it needs BOTH mechanisms
-- at once:
--
--     islam : (b : Tm (suc d)) → IsLam (d , lam b)
--
--   * the field `b` is a NESTED FAMILY at a COMPUTED index (§12's
--     `icw-imu`, at `suc ⟨d⟩` rather than at the ambient);
--   * the target index is computed, so the TERM component is FORDED —
--     and its `Id` is at an `IMu` type, not at `Nat`, which no previous
--     ford has been.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.DepIx where
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax
  using ( Cx; ε; _∙; vz; vs
        ; RTy; U; El; Σ'; Unit; Nat; IMu
        ; RTm; var; pair; fst; snd; unit; nzero; nsuc
        ; ⌜Nat⌝; ⌜Id⌝; ⌜IMu⌝; idrefl; icon
        ; ICon; IDesc; iι; iρ; iκ; inil; _◂_
        ; hereID; thereID )
open import DirectedHoTT.Spec.Typing
  using ( Ctx; ◇; _▹_; ⌊_⌋
        ; _⊢_∷_; ⊢var; here; there; ⊢conv; ⊢pair; ⊢fst; ⊢snd; ⊢unit
        ; ⊢nzero; ⊢nsuc; ⊢⌜Nat⌝; ⊢⌜Id⌝; ⊢⌜IMu⌝; ⊢idrefl; ⊢icon
        ; _⊢ty_; ty-El; ty-Unit; ty-Nat; ty-Σ; ty-IMu
        ; _≅ᵀ_; csymᵀ; ctrnᵀ; credᵀ
        ; El-⌜Id⌝; El-⌜IMu⌝; ξ-El; ξ-⌜Id⌝ᶜ; ξ-⌜Id⌝ˡ; ξ-⌜IMu⌝; ξ-nsuc
        ; βfst; βsnd
        ; IConWf; iwf-ι; iwf-ρ; iwf-κ
        ; ICodeWf; icw-clo; icw-ford; icw-imu
        ; IDescWf; idwf-nil; idwf-cons )
open import DirectedHoTT.Examples.Scoped
  using ( INat; TmD; TmWf; Tm; toI; fromI; tlam; ⊢tlam; tvar; ⊢tvar
        ; fz; ⊢fz; idTm; ⊢idTm )

------------------------------------------------------------------------
-- 1. ★★★ THE DEPENDENT INDEX TYPE.
------------------------------------------------------------------------

IPT : RTy ε
IPT = Σ' (El ⌜Nat⌝) (IMu TmD INat (var vz))

⊢IPT : {Γ : Ctx} → Γ ⊢ty Σ' (El ⌜Nat⌝) (IMu TmD INat (var vz))
⊢IPT = ty-Σ (ty-El ⊢⌜Nat⌝) (ty-IMu TmWf (⊢var here))

-- the two projections of the ambient index, at `k` binders in
--   ⚠ `⊢snd` lands at `subTy (single (fst i)) (IMu TmD INat (var vz))`,
--     which COMPUTES to `Tm (fst i)` — the dependency is definitional
--     here, and that is what makes the telescope usable at all.
ixTm : {Γ : Ctx} {i : RTm ⌊ Γ ⌋} →
       Γ ⊢ i ∷ Σ' (El ⌜Nat⌝) (IMu TmD INat (var vz)) →
       Γ ⊢ snd i ∷ Tm (fst i)
ixTm d = ⊢snd d

-- `Tm n ≅ᵀ El (⌜IMu⌝ TmD INat n)` — the one conversion a family-typed
-- field or ford costs.
toMu : {Γ : Ctx} {n t : RTm ⌊ Γ ⌋} →
       Γ ⊢ t ∷ Tm n → Γ ⊢ t ∷ El (⌜IMu⌝ TmD INat n)
toMu d = ⊢conv d (csymᵀ (credᵀ El-⌜IMu⌝))

fromMu : {Γ : Ctx} {n t : RTm ⌊ Γ ⌋} →
         Γ ⊢ t ∷ El (⌜IMu⌝ TmD INat n) → Γ ⊢ t ∷ Tm n
fromMu d = ⊢conv d (credᵀ El-⌜IMu⌝)

------------------------------------------------------------------------
-- 2. THE DESCRIPTION.
------------------------------------------------------------------------

islamC : ICon (ε ∙)
islamC =
  iκ (⌜IMu⌝ TmD INat (nsuc (fst (var vz))))              -- b : Tm (suc d)
   (iκ (⌜Id⌝ (⌜IMu⌝ TmD INat (fst (var (vs vz))))         -- ⟨t⟩ ≡ lam b
             (snd (var (vs vz)))
             (tlam (var vz)))
    iι)

IsLamD : IDesc
IsLamD = islamC ◂ inil

IsLam : {Γ : Cx} → RTm Γ → RTy Γ
IsLam i = IMu IsLamD IPT i

------------------------------------------------------------------------
-- 3. WELL-FORMEDNESS — the whole question, in two rows.
------------------------------------------------------------------------

islamWf : IConWf IsLamD IPT (◇ ▹ IPT) islamC
islamWf =
  iwf-κ (⌜IMu⌝ TmD INat (nsuc (fst (var vz))))
        (icw-imu (nsuc (fst (var vz))) TmWf)
        (⊢⌜IMu⌝ TmWf (toI (⊢nsuc (fromI (⊢fst (⊢var here))))))
   (iwf-κ (⌜Id⌝ (⌜IMu⌝ TmD INat (fst (var (vs vz))))
                (snd (var (vs vz)))
                (tlam (var vz)))
          (icw-ford (⌜IMu⌝ TmD INat (fst (var (vs vz))))
                    (snd (var (vs vz)))
                    (tlam (var vz)))
          (⊢⌜Id⌝ (⊢⌜IMu⌝ TmWf (⊢fst (⊢var (there here))))
                 (toMu (ixTm (⊢var (there here))))
                 (toMu (⊢tlam (⊢fst (⊢var (there here)))
                              (fromMu (⊢var here)))))
          iwf-ι)

IsLamWf : IDescWf IPT IsLamD
IsLamWf = idwf-cons islamWf idwf-nil

------------------------------------------------------------------------
-- 4. ⚠⚠ INHABITATION — WITHOUT IT §3 SAYS NOTHING.
--
-- `IsLamWf` says the WF judgement accepts a dependent index telescope.
-- It does NOT say anything lives at one, and a description can be
-- well-formed and EMPTY (`Examples/Vec.no-cons-at-zero` proves that
-- hazard on purpose).  Below, `islam` at the concrete index
-- `(0 , λx. x)` — so the telescope is inhabited, not merely admissible.
--
-- ★ AND THIS IS WHERE THE DEPENDENCY IS PAID FOR.  At a concrete
--   `pair n t` BOTH components must STEP before anything matches:
--   the field's type mentions `fst ⟨i⟩` and the ford mentions BOTH
--   `fst ⟨i⟩` (inside the `⌜IMu⌝` CODE) and `snd ⟨i⟩` (as an endpoint).
--   That is three congruence rules — `ξ-⌜IMu⌝`, `ξ-⌜Id⌝ᶜ`, `ξ-⌜Id⌝ˡ` —
--   where a non-dependent index needed one.
------------------------------------------------------------------------

⊢ixP2 : {Γ : Ctx} {n t : RTm ⌊ Γ ⌋} →
        Γ ⊢ n ∷ El ⌜Nat⌝ → Γ ⊢ t ∷ Tm n →
        Γ ⊢ pair n t ∷ Σ' (El ⌜Nat⌝) (IMu TmD INat (var vz))
⊢ixP2 dn dt = ⊢pair (ty-IMu TmWf (⊢var here)) dn dt

-- the BODY field, at a concrete index: `fst (pair n t)` must step
bodyAt : {Γ : Ctx} {n t b : RTm ⌊ Γ ⌋} → Γ ⊢ n ∷ El ⌜Nat⌝ →
         Γ ⊢ b ∷ Tm (nsuc n) →
         Γ ⊢ b ∷ El (⌜IMu⌝ TmD INat (nsuc (fst (pair n t))))
bodyAt {n = n} {t = t} dn db =
  ⊢conv (toMu db)
        (csymᵀ (credᵀ (ξ-El (ξ-⌜IMu⌝ (ξ-nsuc (βfst n t))))))

-- the FORD, at a concrete index: the code's `fst` AND the endpoint's
-- `snd` both step, then `El-⌜Id⌝` lands it.
fordAt : {Γ : Ctx} {n t : RTm ⌊ Γ ⌋} → Γ ⊢ n ∷ El ⌜Nat⌝ → Γ ⊢ t ∷ Tm n →
         Γ ⊢ idrefl (⌜IMu⌝ TmD INat n) t
           ∷ El (⌜Id⌝ (⌜IMu⌝ TmD INat (fst (pair n t))) (snd (pair n t)) t)
fordAt {n = n} {t = t} dn dt =
  ⊢conv (⊢idrefl (⊢⌜IMu⌝ TmWf dn) (toMu dt))
        (csymᵀ (ctrnᵀ (credᵀ (ξ-El (ξ-⌜Id⌝ᶜ (ξ-⌜IMu⌝ (βfst n t)))))
                 (ctrnᵀ (credᵀ (ξ-El (ξ-⌜Id⌝ˡ (βsnd n t))))
                        (credᵀ (El-⌜Id⌝ (⌜IMu⌝ TmD INat n) t t)))))

-- ⚠ the ford's ⊢ty premise sits ONE BINDER deeper (inside the payload's
--   `Σ'`), so its index terms live at the EXTENDED context.  Here they are
--   CLOSED, so `⊢ixP2` — which is context-generic — serves at both depths
--   and nothing needs weakening.
tyFord₀ : {Γ : Ctx} →
          (Γ ▹ El (⌜IMu⌝ TmD INat (nsuc (fst (pair nzero idTm))))) ⊢ty
          Σ' (El (⌜Id⌝ (⌜IMu⌝ TmD INat (fst (pair nzero idTm)))
                       (snd (pair nzero idTm)) (tlam (var vz)))) Unit
tyFord₀ =
  ty-Σ (ty-El (⊢⌜Id⌝ (⊢⌜IMu⌝ TmWf (⊢fst (⊢ixP2 (toI ⊢nzero) ⊢idTm)))
                     (toMu (⊢snd (⊢ixP2 (toI ⊢nzero) ⊢idTm)))
                     (toMu (⊢tlam (⊢fst (⊢ixP2 (toI ⊢nzero) ⊢idTm))
                                  (fromMu (⊢var here))))))
       ty-Unit

islam : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ
islam n b = icon zero (pair b (pair (idrefl (⌜IMu⌝ TmD INat n) (tlam b)) unit))

-- ★★★ `islam : IsLam (0 , λx. x)` — the telescope is INHABITED.
⊢islam₀ : ◇ ⊢ islam nzero (tvar fz) ∷ IsLam (pair nzero idTm)
⊢islam₀ =
  ⊢icon IsLamWf hereID (⊢ixP2 (toI ⊢nzero) ⊢idTm)
    (⊢pair tyFord₀
           (bodyAt (toI ⊢nzero) (⊢tvar (toI (⊢nsuc ⊢nzero)) ⊢fz))
           (⊢pair ty-Unit (fordAt (toI ⊢nzero) ⊢idTm) ⊢unit))
