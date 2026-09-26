------------------------------------------------------------------------
-- OCP-0009 · EXAMPLES — ⬜ SPIKE: THE MOTIVE `subTm` NEEDS.
--
--     M(i, t) = ∀n. (Fin ⟨i⟩ → Tm n) → Tm n
--
-- `PLAN-JUDGEMENT` step 2 ends at `subTm`, and calls this motive
-- "a `Π` over `Nat` and a `Tm` codomain added to what `KripkeIx`
-- already does — both ordinary".  ★ THIS FILE CHECKS THAT, because two
-- of the last three estimates in this plan were wrong.
--
-- ⚠ WHAT IS GENUINELY NEW vs `Examples/KripkeIx`, whose motive is
--   `(Fin ⟨i⟩ → Nat) → Nat`:
--
--   1. THE CODOMAIN IS AN `IMu`, NOT `Nat` — and its index is a variable
--      bound INSIDE the motive.  `KripkeIx`'s codomain is closed.
--   2. THE `∀n` IS A BINDER THE MOTIVE ITSELF INTRODUCES, so every index
--      in it sits one deeper than the `ielim` binder layout suggests —
--      the ambient index moves from `vs vz` to `vs (vs vz)`.
--
-- ⚠ AND WHY THE `∀n` IS THERE AT ALL: `subTm σ (lam t) = lam (subTm
--   (extS σ) t)`, so the recursive call is at a substitution into a
--   DEEPER context.  The result type must therefore not fix the target
--   depth — hence quantifying over it.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.KripkeSub where
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax hiding ( Fin )
open import DirectedHoTT.Spec.Typing hiding ( _×_; _,,_ )
open import DirectedHoTT.Lib.Sugar using ( conₗ; MethK )
open import DirectedHoTT.Lib.Tel
open import DirectedHoTT.Examples.Scoped
  using ( TmD; ⊢TmD; Tm; lamT; lamOK; FinD; ⊢FinD; FinI; ⊢isuc; ffz; ⊢ffz; tlam; ⊢tlam; tvar; ⊢tvar )

------------------------------------------------------------------------
-- ★★★ THE MOTIVE.
--
-- Binder layout.  The motive is checked at `Γ ▹ El ⌜Nat⌝ ▹ Tm (var vz)`,
-- so `vz` is the SCRUTINEE and `vs vz` the ambient INDEX.  Under the
-- motive's own `Π (El ⌜Nat⌝)`, everything shifts by one:
--
--     n = vz · t = vs vz · i = vs (vs vz)
--
-- and under the inner `Π (Fin i) _`, `n` is `vs vz` again.
------------------------------------------------------------------------

sMot : {Γ : Cx} → RTy ((Γ ∙) ∙)
sMot = Π (El ⌜Nat⌝) (Π (Π (FinI (var (vs (vs vz)))) (Tm (var (vs vz)))) (Tm (var (vs vz))))

⊢sMot : {Γ : Ctx} → ((Γ ▹ El ⌜Nat⌝) ▹ Tm (var vz)) ⊢ty sMot
⊢sMot =
  ty-Π (ty-El ⊢⌜Nat⌝)
    (ty-Π (ty-Π (ty-IMu ⊢⌜Nat⌝ ⊢FinD (⊢var (there (there here))))
                (ty-IMu ⊢⌜Nat⌝ ⊢TmD (⊢var (there here))))
          (ty-IMu ⊢⌜Nat⌝ ⊢TmD (⊢var (there here))))

------------------------------------------------------------------------
-- ★ A `Fin` ZERO AT A **VARIABLE** DEPTH is simply `Scoped.ffz n`:
--   under D074 its constructor telescopes are depth-generic, so the
--   variable-index twin the one-telescope form needed (and its
--   `wk-single` round trip) is gone.  Every `Tm` at a variable depth
--   bottoms out at `tvar` of a `Fin`, and `Fin (suc n)` has exactly this.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- ★★★ THE `lam` METHOD — WHERE THE DEPTH ACTUALLY SHIFTS.
--
--     subTm σ (lam b) = lam (subTm (extS σ) b)
--
-- ⚠⚠ THIS IS THE MANOEUVRE `KripkeIx` CANNOT TEST.  Its motive has no
--   `n`, so its IH differs from the method's own only in the DOMAIN.
--   Here the IH must also be used at a different CODOMAIN DEPTH: `ih` is
--   applied at `suc n`, yielding a `Tm (suc n)`, and `tlam` brings it
--   back to `Tm n`.
--
-- Binder layout: `i` `p` `h` from the eliminator, then the motive's own
-- `n` and `σ`.
--     σ = vz · n = vs vz · h = vs² vz · p = vs³ vz · i = vs⁴ vz
--
-- ⚠ THE EXTENSION IS STUBBED, deliberately, exactly as `KripkeIx` stubs
--   its valuation with `λ_. 0`: the stub still has to have the right
--   type, `Fin (suc i) → Tm (suc n)`, so the shift is genuinely checked.
------------------------------------------------------------------------

sLam : {Γ : Cx} → RTm Γ
sLam = lam (lam (lam (lam (lam
         (tlam (app (app (fst (var (vs (vs vz)))) (nsuc (var (vs vz))))
                    (lam (tvar (ffz (var (vs (vs vz))))))))))))

module _ {Γ : Ctx} where
  private
    H  = HypCtx Γ ⌜Nat⌝ TmD sMot lamT
    Hn = H ▹ El ⌜Nat⌝
    Hσ = Hn ▹ Π (FinI (var (vs (vs (vs vz))))) (Tm (var (vs vz)))
    dn : Hσ ⊢ var (vs vz) ∷ El ⌜Nat⌝
    dn = ⊢var (there here)
    di : Hσ ⊢ var (vs (vs (vs (vs vz)))) ∷ El ⌜Nat⌝
    di = ⊢var (there (there (there (there here))))

  -- the stub extension: `Fin (suc i) → Tm (suc n)`
  ⊢stub : Hσ ⊢ lam (tvar (ffz (var (vs (vs vz))))) ∷ Π (FinI (nsuc (var (vs (vs (vs (vs vz))))))) (Tm (nsuc (var (vs (vs vz)))))
  ⊢stub = ⊢lam (ty-IMu ⊢⌜Nat⌝ ⊢FinD (⊢isuc di))
            (⊢tvar (⊢isuc (⊢var (there (there here)))) (⊢ffz (⊢var (there (there here)))))

  ⊢sLam : Γ ⊢ sLam ∷ MethK ⌜Nat⌝ TmD sMot ⌜ lamT ⌝ᵗ (suc zero)
  ⊢sLam =
    ⊢methT {T = lamT} {s = conₗ (suc zero) (var (vs vz))} ⊢⌜Nat⌝ ⊢TmD ⊢sMot lamOK
      (⊢lam (ty-El ⊢⌜Nat⌝)
        (⊢lam (ty-Π (ty-IMu ⊢⌜Nat⌝ ⊢FinD (⊢var (there (there (there here)))))
                    (ty-IMu ⊢⌜Nat⌝ ⊢TmD (⊢var (there here))))
          -- ★ the IH at `suc n`, then `tlam` back down to `Tm n`
          (⊢tlam dn (⊢app (⊢app (⊢fst (⊢var (there (there here)))) (⊢isuc dn)) ⊢stub))))

------------------------------------------------------------------------
-- ⬜ WHAT THIS SPIKE DID **NOT** DO, deliberately.
--
-- The `var` and `app` methods and the assembled `ielim` are not here.
-- Both are strictly easier shapes than `lam` — neither shifts the depth,
-- so both are `KripkeIx`'s existing shape plus the extra `n` binder —
-- and building them against the STUBBED extension would be throwaway:
-- step 2 needs them against the real `extS`, once the `Fin` eliminator
-- exists.  `Examples/KripkeIx` already shows an `ielim` closing and
-- COMPUTING at a Kripke motive; nothing here casts doubt on that.
--
-- ★★★ WHAT IT DID SETTLE: the motive `∀n. (Fin ⟨i⟩ → Tm n) → Tm n` is
--   well-formed, and its HARDEST method — the one whose IH lands at a
--   different depth — type-checks.  That was the open question.
------------------------------------------------------------------------
