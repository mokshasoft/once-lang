------------------------------------------------------------------------
-- OCP-0009 · EXAMPLES — ★★★ OBJECT-LEVEL WEAKENING FOR A SYNTAX.
--
--     wkTmTm : Tm n → Tm (suc n)
--
-- One rung up from `Examples/WkFin`: `Tm` HAS A BINDER, which `Fin` does
-- not, and this is the shape `_∋_∷_`'s `renTy vs A` actually needs.
--
-- ★★ AND IT NEEDS NO KRIPKE MOTIVE.  Weakening AT THE OUTSIDE shifts the
--   index uniformly, so `M(i,t) = Tm (suc ⟨i⟩)` still serves: under
--   `lam` the body is at `suc ⟨i⟩` and its IH is the SAME function one
--   index higher.  ⇒ what forces a motive that is a FUNCTION OF THE
--   RENAMING is `subTy (single u)` (⊢app's index), not binders as such.
--   That distinction is the useful output of this file.
--
-- ⚠ AND `TmD` IS FORD-FREE — its constructors target the ambient index
--   with `iι`, where `Fin`'s `fzero`/`fsuc` constrain theirs.  So no
--   method here needs the `⊢jsub` transport `WkFin` needed; the
--   transport is reached only THROUGH `wkFinTm`, in the `var` case.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.WkTm where
open import normalizer.Syntax.Types using ( _≡_; cong )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax
  using ( Cx; ε; _∙; vz; vs
        ; RTy; U; El; Σ'; Unit; Nat; IMu
        ; RTm; var; lam; pair; fst; snd; unit; nzero; nsuc
        ; ⌜Nat⌝; ⌜IMu⌝; icon; ielim; isingle; iihs
        ; ICon; IDesc; hereID; thereID; εwkTy )
open import DirectedHoTT.Spec.Typing
  using ( Ctx; ◇; _▹_; ⌊_⌋; wk-single
        ; _⊢_∷_; ⊢var; here; there; ⊢conv; ⊢pair; ⊢fst; ⊢snd; ⊢unit
        ; ⊢nzero; ⊢nsuc; ⊢⌜Nat⌝; ⊢lam; ⊢icon; ⊢ielim
        ; _⊢ty_; ty-El; ty-Unit; ty-Nat; ty-Σ; ty-Π; ty-IMu
        ; imethTy; imethsTy; IDescWf
        ; _⟶*_; done; step; β; βfst; βsnd; ξ-appˡ; ι-ielim )
open import DirectedHoTT.Metatheory.TySub using ( ⊢-cast )
open import DirectedHoTT.Examples.Scoped
  using ( INat; TmD; TmWf; Tm; varC; lamC; appC
        ; tvar; tlam; tapp; ⊢tvar; ⊢tlam; ⊢tapp
        ; tyPayVar; tyPayLam; tyPayApp; toI; fromI; toFin )
open import DirectedHoTT.Examples.WkFin using ( wkFinTm; ⊢wkFinTm; fromFin )

------------------------------------------------------------------------
-- 1. THE MOTIVE — the same index shift as `WkFin`'s.
------------------------------------------------------------------------

wkTmMot : {Γ : Cx} → RTy ((Γ ∙) ∙)
wkTmMot = IMu TmD INat (nsuc (var (vs vz)))

⊢wkTmMot : {Γ : Ctx} →
           ((Γ ▹ εwkTy INat) ▹ IMu TmD INat (var vz)) ⊢ty wkTmMot
⊢wkTmMot = ty-IMu TmWf (toI (⊢nsuc (fromI (⊢var (there here)))))

------------------------------------------------------------------------
-- 2. THE THREE METHODS.  ⚠ payload ⊢ty's come from `Scoped` — CONCRETE,
--    per `WkFin`'s finding that `Lib/IPay` cannot be used at a concrete
--    constructor.  They already exist there, for `msize`.
------------------------------------------------------------------------

-- var : Fin n → Tm n   ↦   var (wkFin k) : Tm (suc n)
wkVar : {Γ : Cx} → RTm Γ
wkVar = lam (lam (lam
          (tvar (wkFinTm (var (vs (vs vz))) (fst (var (vs vz)))))))

⊢wkVar : {Γ : Ctx} → Γ ⊢ wkVar ∷ imethTy TmD INat zero varC wkTmMot
⊢wkVar =
  ⊢lam (ty-El ⊢⌜Nat⌝)
    (⊢lam tyPayVar
      (⊢lam ty-Unit
        (⊢tvar (toI (⊢nsuc (fromI (⊢var (there (there here))))))
               (⊢wkFinTm (⊢var (there (there here)))
                         (fromFin (⊢fst (⊢var (there here))))))))

-- lam : Tm (suc n) → Tm n   ↦   lam ⟨ih⟩ : Tm (suc n)
wkLam : {Γ : Cx} → RTm Γ
wkLam = lam (lam (lam (tlam (fst (var vz)))))

⊢wkLam : {Γ : Ctx} → Γ ⊢ wkLam ∷ imethTy TmD INat (suc zero) lamC wkTmMot
⊢wkLam =
  ⊢lam (ty-El ⊢⌜Nat⌝)
    (⊢lam tyPayLam
      (⊢lam (ty-Σ (ty-IMu TmWf (toI (⊢nsuc (⊢nsuc (fromI (⊢var (there here)))))))
                  ty-Unit)
        (⊢tlam (toI (⊢nsuc (fromI (⊢var (there (there here))))))
               (⊢fst (⊢var here)))))

-- app : Tm n → Tm n → Tm n   ↦   app ⟨ih₁⟩ ⟨ih₂⟩ : Tm (suc n)
wkApp : {Γ : Cx} → RTm Γ
wkApp = lam (lam (lam (tapp (fst (var vz)) (fst (snd (var vz))))))

⊢wkApp : {Γ : Ctx} → Γ ⊢ wkApp ∷ imethTy TmD INat (suc (suc zero)) appC wkTmMot
⊢wkApp =
  ⊢lam (ty-El ⊢⌜Nat⌝)
    (⊢lam tyPayApp
      (⊢lam (ty-Σ (ty-IMu TmWf (toI (⊢nsuc (fromI (⊢var (there here))))))
                  (ty-Σ (ty-IMu TmWf (toI (⊢nsuc (fromI (⊢var (there (there here)))))))
                        ty-Unit))
        (⊢tapp (toI (⊢nsuc (fromI (⊢var (there (there here))))))
               (⊢fst (⊢var here))
               (⊢fst (⊢snd (⊢var here))))))

------------------------------------------------------------------------
-- 3. ★★★ `wkTm` ITSELF.
------------------------------------------------------------------------

tyΠVar : {Γ : Ctx} → Γ ⊢ty imethTy TmD INat zero varC wkTmMot
tyΠVar = ty-Π (ty-El ⊢⌜Nat⌝)
           (ty-Π tyPayVar
             (ty-Π ty-Unit
               (ty-IMu TmWf (toI (⊢nsuc (fromI (⊢var (there (there here)))))))))

tyΠLam : {Γ : Ctx} → Γ ⊢ty imethTy TmD INat (suc zero) lamC wkTmMot
tyΠLam = ty-Π (ty-El ⊢⌜Nat⌝)
           (ty-Π tyPayLam
             (ty-Π (ty-Σ (ty-IMu TmWf (toI (⊢nsuc (⊢nsuc (fromI (⊢var (there here)))))))
                         ty-Unit)
               (ty-IMu TmWf (toI (⊢nsuc (fromI (⊢var (there (there here)))))))))

tyΠApp : {Γ : Ctx} → Γ ⊢ty imethTy TmD INat (suc (suc zero)) appC wkTmMot
tyΠApp = ty-Π (ty-El ⊢⌜Nat⌝)
           (ty-Π tyPayApp
             (ty-Π (ty-Σ (ty-IMu TmWf (toI (⊢nsuc (fromI (⊢var (there here))))))
                         (ty-Σ (ty-IMu TmWf (toI (⊢nsuc (fromI (⊢var (there (there here)))))))
                               ty-Unit))
               (ty-IMu TmWf (toI (⊢nsuc (fromI (⊢var (there (there here)))))))))

wkTmMeths : {Γ : Cx} → RTm Γ
wkTmMeths = pair wkVar (pair wkLam (pair wkApp unit))

⊢wkTmMeths : {Γ : Ctx} → Γ ⊢ wkTmMeths ∷ imethsTy TmD INat wkTmMot TmD
⊢wkTmMeths =
  ⊢pair (ty-Σ tyΠLam (ty-Σ tyΠApp ty-Unit)) ⊢wkVar
    (⊢pair (ty-Σ tyΠApp ty-Unit) ⊢wkLam
      (⊢pair ty-Unit ⊢wkApp ⊢unit))

-- ★★★ OBJECT-LEVEL WEAKENING FOR THE SYNTAX: `Tm n → Tm (suc n)`.
wkTmTm : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ
wkTmTm n t = ielim TmD n wkTmMeths t

⊢wkTmTm : {Γ : Ctx} {n t : RTm ⌊ Γ ⌋} →
          Γ ⊢ n ∷ El ⌜Nat⌝ → Γ ⊢ t ∷ Tm n →
          Γ ⊢ wkTmTm n t ∷ Tm (nsuc n)
⊢wkTmTm {n = n} dn dt =
  ⊢-cast (cong (λ z → IMu TmD INat (nsuc z)) (wk-single n))
         (⊢ielim TmWf ⊢wkTmMot dn ⊢wkTmMeths dt)
