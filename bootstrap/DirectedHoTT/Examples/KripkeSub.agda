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
open import normalizer.Syntax.Types using ( _≡_; cong; sym )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax
  using ( Cx; ε; _∙; vz; vs; RTy; RTm; var; lam; app; fst; snd; pair; unit
        ; nsuc; nzero; icon; idrefl; renTm; ⌜Id⌝
        ; Nat; Unit; Σ'; Π; IMu; El; ⌜Nat⌝; εwkTy )
open import DirectedHoTT.Spec.Typing
  using ( Ctx; ◇; _▹_; ⌊_⌋; _⊢_∷_; _⊢ty_; ⊢var; here; there
        ; ty-Nat; ty-Π; ty-IMu; ty-Unit; ty-Σ; ⊢⌜Nat⌝; ty-El; wk-single
        ; ⊢lam; ⊢app; ⊢fst; ⊢nsuc; ⊢nzero; ⊢pair; ⊢unit; ⊢icon; ⊢idrefl
        ; ⊢conv; csymᵀ; credᵀ; El-⌜Id⌝; ⊢⌜Id⌝; imethTy )
open import DirectedHoTT.Metatheory.SubjectReduction using ( ⊢wk; ⊢-cast )
open import DirectedHoTT.Spec.Syntax using ( hereID )
open import DirectedHoTT.Examples.Scoped
  using ( INat; TmD; TmWf; Tm; FinD; FinWf; Fin; toI; fromI
        ; lamC; tyPayLam; tlam; ⊢tlam; tvar; ⊢tvar )

------------------------------------------------------------------------
-- ★★★ THE MOTIVE.
--
-- Binder layout.  The motive is checked at
--     Θ = Γ ▹ εwkTy INat ▹ IMu TmD INat (var vz)
-- so `vz` is the SCRUTINEE and `vs vz` the ambient INDEX.  Under the
-- motive's own `Π Nat`, everything shifts by one:
--
--     n = vz · t = vs vz · i = vs (vs vz)
--
-- and under the inner `Π (Fin i) _`, `n` is `vs vz` again.
------------------------------------------------------------------------

sMot : {Γ : Cx} → RTy ((Γ ∙) ∙)
sMot = Π Nat (Π (Π (IMu FinD INat (var (vs (vs vz))))
                   (IMu TmD INat (var (vs vz))))
                (IMu TmD INat (var (vs vz))))

⊢sMot : {Γ : Ctx} →
        ((Γ ▹ εwkTy INat) ▹ IMu TmD INat (var vz)) ⊢ty sMot
⊢sMot =
  ty-Π ty-Nat
    (ty-Π (ty-Π (ty-IMu FinWf (⊢var (there (there here))))
                (ty-IMu TmWf (toI (⊢var (there here)))))
          (ty-IMu TmWf (toI (⊢var (there here)))))

------------------------------------------------------------------------
-- ⚠ A `Fin` ZERO AT A **VARIABLE** DEPTH, which `Examples/Scoped` does
--   not have: its `fz` is `Fin 1` on purpose ("with the index a numeral
--   the payload's weakenings compute away").
--
-- ★ AND IT IS NEEDED FOR A REASON WORTH RECORDING: the stub below has
--   to inhabit `Tm (suc n)` at a VARIABLE `n`, and every `Tm` at a
--   variable depth bottoms out at `tvar` of a `Fin` — `tlam` wants a
--   deeper `Tm`, `tapp` two more.  `Fin n` at a variable `n` has no
--   inhabitant, and correctly so (`Fin 0` is empty); `Fin (suc n)` has
--   exactly this one.  Same variable-index twin as `Knot/Build`'s
--   `⊢Var-vzKv`.
------------------------------------------------------------------------

fzv : {Γ : Cx} → RTm Γ → RTm Γ
fzv n = icon zero (pair n (pair (idrefl ⌜Nat⌝ (nsuc n)) unit))

reflSv : {Γ : Ctx} {n : RTm ⌊ Γ ⌋} → Γ ⊢ n ∷ El ⌜Nat⌝ →
         Γ ⊢ idrefl ⌜Nat⌝ (nsuc n) ∷ El (⌜Id⌝ ⌜Nat⌝ (nsuc n) (nsuc n))
reflSv {n = n} dn =
  ⊢conv (⊢idrefl ⊢⌜Nat⌝ (toI (⊢nsuc (fromI dn))))
        (csymᵀ (credᵀ (El-⌜Id⌝ ⌜Nat⌝ (nsuc n) (nsuc n))))

tyFzv : {Γ : Ctx} {n : RTm ⌊ Γ ⌋} → Γ ⊢ n ∷ El ⌜Nat⌝ →
        (Γ ▹ El ⌜Nat⌝) ⊢ty
        Σ' (El (⌜Id⌝ ⌜Nat⌝ (nsuc (renTm vs n)) (nsuc (var vz)))) Unit
tyFzv dn = ty-Σ (ty-El (⊢⌜Id⌝ ⊢⌜Nat⌝ (toI (⊢nsuc (fromI (⊢wk dn))))
                               (toI (⊢nsuc (fromI (⊢var here))))))
                ty-Unit

-- ⚠ THE ROUND TRIP DOES NOT COMPUTE AT A VARIABLE DEPTH.  The payload's
--   ford field is stated with the index WEAKENED, and instantiating it
--   leaves `subTm (single n) (renTm vs n)` — which is `n` only by
--   `wk-single`, not definitionally.  At `Scoped`'s numeral `fz` this
--   never appears; it is the whole cost of the variable-index twin.
⊢fzv : {Γ : Ctx} {n : RTm ⌊ Γ ⌋} → Γ ⊢ n ∷ El ⌜Nat⌝ →
       Γ ⊢ fzv n ∷ Fin (nsuc n)
⊢fzv {n = n} dn =
  ⊢icon FinWf hereID (toI (⊢nsuc (fromI dn)))
    (⊢pair (tyFzv dn) dn
      (⊢pair ty-Unit
        (⊢-cast (cong (λ z → El (⌜Id⌝ ⌜Nat⌝ (nsuc z) (nsuc n)))
                      (sym (wk-single n)))
                (reflSv dn))
        ⊢unit))

------------------------------------------------------------------------
-- ★★★ THE `lam` METHOD — WHERE THE DEPTH ACTUALLY SHIFTS.
--
--     subTm σ (lam b) = lam (subTm (extS σ) b)
--
-- ⚠⚠ THIS IS THE MANOEUVRE `KripkeIx` CANNOT TEST.  Its motive has no
--   `n`, so its IH differs from the method's own only in the DOMAIN
--   (`Fin (suc i)` vs `Fin i`).  Here the IH must also be used at a
--   different CODOMAIN DEPTH: `ih` is applied at `suc n`, yielding a
--   `Tm (suc n)`, and `tlam` is what brings it back to `Tm n`.  If the
--   motive were wrong, this is where it would show.
--
-- Binder layout: `i` `p` `ih` from the eliminator, then the motive's own
-- `n` and `σ`.
--     σ = vz · n = vs vz · ih = vs² vz · p = vs³ vz · i = vs⁴ vz
--
-- ⚠ THE EXTENSION IS STUBBED, and deliberately, exactly as `KripkeIx`
--   stubs its valuation with `λ_. 0`.  A real `extS` needs the `Fin`
--   eliminator — a SEPARATE step-2 prerequisite — and supplying it here
--   would test nothing further about the MOTIVE, which is all this file
--   is for.  The stub still has to have the right type,
--   `Fin (suc i) → Tm (suc n)`, so the shift is genuinely checked.
------------------------------------------------------------------------

sLam : {Γ : Cx} → RTm Γ
sLam = lam (lam (lam (lam (lam
         (tlam (app (app (fst (var (vs (vs vz)))) (nsuc (var (vs vz))))
                    (lam (tvar (fzv (var (vs (vs vz))))))))))))

⊢sLam : {Γ : Ctx} → Γ ⊢ sLam ∷ imethTy TmD INat (suc zero) lamC sMot
⊢sLam =
  ⊢lam (ty-El ⊢⌜Nat⌝)
    (⊢lam tyPayLam
      (⊢lam (ty-Σ (ty-Π ty-Nat
                     (ty-Π (ty-Π (ty-IMu FinWf (toI (⊢nsuc (fromI (⊢var (there (there here)))))))
                                 (ty-IMu TmWf (toI (⊢var (there here)))))
                           (ty-IMu TmWf (toI (⊢var (there here))))))
                  ty-Unit)
        (⊢lam ty-Nat
          (⊢lam (ty-Π (ty-IMu FinWf (⊢var (there (there (there here)))))
                      (ty-IMu TmWf (toI (⊢var (there here)))))
            -- ★ the IH at `suc n`, then `tlam` back down to `Tm n`
            (⊢tlam (toI (⊢var (there here)))
              (⊢app (⊢app (⊢fst (⊢var (there (there here))))
                          (⊢nsuc (⊢var (there here))))
                    (⊢lam (ty-IMu FinWf (toI (⊢nsuc (fromI (⊢var (there (there (there (there here)))))))))
                          (⊢tvar (toI (⊢nsuc (⊢var (there (there here)))))
                                 (⊢fzv (toI (⊢var (there (there here)))))))))))))


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
