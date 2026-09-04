------------------------------------------------------------------------
-- OCP-0009 · EXAMPLES — ★★★ SPIKE: A **KRIPKE MOTIVE**, i.e. one whose
-- Π DOMAIN MENTIONS THE INDEX.
--
-- `Examples/WkTm` showed weakening needs no such thing: weakening at the
-- outside shifts the index uniformly, so a plain `Tm (suc ⟨i⟩)` motive
-- serves.  What DOES force a function-of-the-index motive is
-- `subTy (single u)` — `⊢app`'s index, and hence the gate on `_⊢_∷_`:
--
--     subTm σ (lam t) = lam (subTm (extS σ) t)
--
-- the recursive call is at a DIFFERENT substitution, so the motive must
-- quantify over it, and its type mentions the index.
--
-- ★ THE SMALLEST HONEST TEST of that shape, needing no helper:
--
--     M(i, t) = (Fin ⟨i⟩ → Nat) → Nat
--
--   The domain mentions `⟨i⟩`, so under `lam` the IH's domain is
--   `Fin (suc ⟨i⟩) → Nat` — DIFFERENT from the method's own — and using
--   the IH means supplying a function at the shifted domain.  That is
--   precisely the manoeuvre `subTm`'s `lam` case performs.
--
-- ⚠ WHAT IT IS NOT.  This is a SHAPE test.  The function it computes
--   (sum the valuation over free occurrences, counting bound variables
--   as 0) is real but uninteresting; the point is the motive, and the
--   `lam` case supplying `λ_. 0` at the shifted domain rather than a
--   genuine extension is deliberate — an extension would need a `Fin`
--   eliminator and would test nothing further about the motive.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.KripkeIx where
open import normalizer.Syntax.Types using ( _≡_; cong )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax
  using ( Cx; ε; _∙; vz; vs
        ; RTy; U; El; Σ'; Unit; Nat; Π; IMu
        ; RTm; var; lam; app; pair; fst; snd; unit; nzero; nsuc
        ; ⌜Nat⌝; ⌜IMu⌝; icon; ielim; εwkTy; isingle; iihs )
open import DirectedHoTT.Spec.Typing
  using ( Ctx; ◇; _▹_; ⌊_⌋; wk-single
        ; _⊢_∷_; ⊢var; here; there; ⊢conv; ⊢pair; ⊢fst; ⊢snd; ⊢unit
        ; ⊢nzero; ⊢nsuc; ⊢⌜Nat⌝; ⊢lam; ⊢app; ⊢ielim
        ; _⊢ty_; ty-El; ty-Unit; ty-Nat; ty-Σ; ty-Π; ty-IMu
        ; imethTy; imethsTy
        ; _⟶*_; done; step; β; βfst; ξ-appˡ; ι-ielim )
open import DirectedHoTT.Metatheory.TySub using ( ⊢-cast )
open import DirectedHoTT.Lib.Nat using ( plusTm; ⊢plus )
open import DirectedHoTT.Examples.Scoped
  using ( INat; TmD; TmWf; Tm; FinD; FinWf; Fin; varC; lamC; appC
        ; tyPayVar; tyPayLam; tyPayApp; toI; fromI )
open import DirectedHoTT.Examples.WkFin using ( fromFin )
open import DirectedHoTT.Examples.Scoped using ( tvar; fz )

------------------------------------------------------------------------
-- 1. ★★★ THE KRIPKE MOTIVE.  `(Fin ⟨i⟩ → Nat) → Nat`.
------------------------------------------------------------------------

kMot : {Γ : Cx} → RTy ((Γ ∙) ∙)
kMot = Π (Π (IMu FinD INat (var (vs vz))) Nat) Nat

⊢kMot : {Γ : Ctx} → ((Γ ▹ εwkTy INat) ▹ IMu TmD INat (var vz)) ⊢ty kMot
⊢kMot = ty-Π (ty-Π (ty-IMu FinWf (⊢var (there here))) ty-Nat) ty-Nat

------------------------------------------------------------------------
-- 2. THE THREE METHODS.
--
-- Binder layout inside a method: `i` `p` `ih`, then the motive's own `ρ`.
--   ρ = vz · ih = vs vz · p = vs vs vz · i = vs vs vs vz
------------------------------------------------------------------------

-- var k : look the variable up in the valuation
kVar : {Γ : Cx} → RTm Γ
kVar = lam (lam (lam (lam (app (var vz) (fst (var (vs (vs vz))))))))

⊢kVar : {Γ : Ctx} → Γ ⊢ kVar ∷ imethTy TmD INat zero varC kMot
⊢kVar =
  ⊢lam (ty-El ⊢⌜Nat⌝)
    (⊢lam tyPayVar
      (⊢lam ty-Unit
        (⊢lam (ty-Π (ty-IMu FinWf (⊢var (there (there here)))) ty-Nat)
          (⊢app (⊢var here) (fromFin (⊢fst (⊢var (there (there here)))))))))

-- ★★ lam b : use the IH AT THE SHIFTED DOMAIN.  `ih` expects a
--    `Fin (suc ⟨i⟩) → Nat` where `ρ` is a `Fin ⟨i⟩ → Nat`.
kLam : {Γ : Cx} → RTm Γ
kLam = lam (lam (lam (lam (app (fst (var (vs vz))) (lam nzero)))))

⊢kLam : {Γ : Ctx} → Γ ⊢ kLam ∷ imethTy TmD INat (suc zero) lamC kMot
⊢kLam =
  ⊢lam (ty-El ⊢⌜Nat⌝)
    (⊢lam tyPayLam
      (⊢lam (ty-Σ (ty-Π (ty-Π (ty-IMu FinWf (toI (⊢nsuc (fromI (⊢var (there here)))))) ty-Nat)
                        ty-Nat)
                  ty-Unit)
        (⊢lam (ty-Π (ty-IMu FinWf (⊢var (there (there here)))) ty-Nat)
          (⊢app (⊢fst (⊢var (there here)))
                (⊢lam (ty-IMu FinWf (toI (⊢nsuc (fromI (⊢var (there (there (there here))))))))
                      ⊢nzero)))))

-- app f a : both IHs at the SAME domain, so `ρ` is passed twice
kApp : {Γ : Cx} → RTm Γ
kApp = lam (lam (lam (lam
         (plusTm (app (fst (var (vs vz))) (var vz))
                 (app (fst (snd (var (vs vz)))) (var vz))))))

⊢kApp : {Γ : Ctx} → Γ ⊢ kApp ∷ imethTy TmD INat (suc (suc zero)) appC kMot
⊢kApp =
  ⊢lam (ty-El ⊢⌜Nat⌝)
    (⊢lam tyPayApp
      (⊢lam (ty-Σ (ty-Π (ty-Π (ty-IMu FinWf (⊢var (there here))) ty-Nat) ty-Nat)
                  (ty-Σ (ty-Π (ty-Π (ty-IMu FinWf (⊢var (there (there here)))) ty-Nat) ty-Nat)
                        ty-Unit))
        (⊢lam (ty-Π (ty-IMu FinWf (⊢var (there (there here)))) ty-Nat)
          (⊢plus (⊢app (⊢fst (⊢var (there here))) (⊢var here))
                 (⊢app (⊢fst (⊢snd (⊢var (there here)))) (⊢var here))))))

------------------------------------------------------------------------
-- 3. ★★★ THE ELIMINATION ITSELF, AT A KRIPKE MOTIVE.
------------------------------------------------------------------------

tyΠkVar : {Γ : Ctx} → Γ ⊢ty imethTy TmD INat zero varC kMot
tyΠkVar = ty-Π (ty-El ⊢⌜Nat⌝)
            (ty-Π tyPayVar
              (ty-Π ty-Unit
                (ty-Π (ty-Π (ty-IMu FinWf (⊢var (there (there here)))) ty-Nat) ty-Nat)))

tyΠkLam : {Γ : Ctx} → Γ ⊢ty imethTy TmD INat (suc zero) lamC kMot
tyΠkLam = ty-Π (ty-El ⊢⌜Nat⌝)
            (ty-Π tyPayLam
              (ty-Π (ty-Σ (ty-Π (ty-Π (ty-IMu FinWf (toI (⊢nsuc (fromI (⊢var (there here)))))) ty-Nat)
                                ty-Nat)
                          ty-Unit)
                (ty-Π (ty-Π (ty-IMu FinWf (⊢var (there (there here)))) ty-Nat) ty-Nat)))

tyΠkApp : {Γ : Ctx} → Γ ⊢ty imethTy TmD INat (suc (suc zero)) appC kMot
tyΠkApp = ty-Π (ty-El ⊢⌜Nat⌝)
            (ty-Π tyPayApp
              (ty-Π (ty-Σ (ty-Π (ty-Π (ty-IMu FinWf (⊢var (there here))) ty-Nat) ty-Nat)
                          (ty-Σ (ty-Π (ty-Π (ty-IMu FinWf (⊢var (there (there here)))) ty-Nat) ty-Nat)
                                ty-Unit))
                (ty-Π (ty-Π (ty-IMu FinWf (⊢var (there (there here)))) ty-Nat) ty-Nat)))

kMeths : {Γ : Cx} → RTm Γ
kMeths = pair kVar (pair kLam (pair kApp unit))

⊢kMeths : {Γ : Ctx} → Γ ⊢ kMeths ∷ imethsTy TmD INat kMot TmD
⊢kMeths =
  ⊢pair (ty-Σ tyΠkLam (ty-Σ tyΠkApp ty-Unit)) ⊢kVar
    (⊢pair (ty-Σ tyΠkApp ty-Unit) ⊢kLam
      (⊢pair ty-Unit ⊢kApp ⊢unit))

-- ★★★ `Tm n → (Fin n → Nat) → Nat`, by `ielim` at a KRIPKE motive.
kEval : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ
kEval n t = ielim TmD n kMeths t

⊢kEval : {Γ : Ctx} {n t : RTm ⌊ Γ ⌋} →
         Γ ⊢ n ∷ El ⌜Nat⌝ → Γ ⊢ t ∷ Tm n →
         Γ ⊢ kEval n t ∷ Π (Π (Fin n) Nat) Nat
⊢kEval {n = n} dn dt =
  ⊢-cast (cong (λ z → Π (Π (IMu FinD INat z) Nat) Nat) (wk-single n))
         (⊢ielim TmWf ⊢kMot dn ⊢kMeths dt)

------------------------------------------------------------------------
-- 4. ★★ …AND IT COMPUTES.  A KRIPKE motive is a `Π`, so the method's
--    result is a FUNCTION — `ι-ielim` still has to fire and deliver it.
------------------------------------------------------------------------

kVarPay : {Γ : Cx} → RTm Γ
kVarPay = pair fz unit

kEval-var : {Γ : Cx} →
            kEval {Γ} (nsuc nzero) (tvar fz)
              ⟶* lam (app (var vz) (fst kVarPay))
kEval-var =
  step (ι-ielim TmD (nsuc nzero) kMeths zero kVarPay)
  (step (ξ-appˡ (ξ-appˡ (ξ-appˡ (βfst kVar (pair kLam (pair kApp unit))))))
  (step (ξ-appˡ (ξ-appˡ (β _ (nsuc nzero))))
  (step (ξ-appˡ (β _ kVarPay))
  (step (β _ (iihs TmD kMeths (isingle (nsuc nzero)) varC kVarPay)) done))))
