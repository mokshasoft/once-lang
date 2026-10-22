-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.SpecFront.Terms — the generators' core definitions, the
-- compiler's and the Spec's, are related (plan 0.121 §3.6, F4).
--
-- Each side defines a generator by the same core term (`Lang.Core.Derived`
-- was transcribed from `Spec.Core.Derived`), so related types give related
-- terms; a definition that moves an argument under a binder is related
-- because renaming is (`TmR-ren`).
------------------------------------------------------------------------

open import Data.Nat using (ℕ)
open import Once.Internal.Contract using (ISig)
import Once.Internal.Core.PolyTy as LP
import Once.Spec.Type as ST

module Once.Adequacy.SpecFront.Terms {Fs : ISig} {s : ℕ} (S : LP.Sig Fs s) {m : ℕ} {Δ : ST.KCtx m} where

open import Data.Fin using (Fin; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst)

import Once.Internal.Type as LT

import Once.Spec.Type as LT
import Once.Spec.Grade as LG
import Once.Spec.Grade as SG
import Once.Spec.Core.Syntax as SC
import Once.Spec.Core.Derived as SD
import Once.Internal.Core.Syntax S as L
import Once.Internal.Core.Derived S as LD
open import Once.Adequacy.SpecGrammar.Conv using (qS; πS; φS; kS)
open import Once.Adequacy.SpecCore.Type
open import Once.Adequacy.SpecCore.TermR S
open import Once.Adequacy.SpecFront.Types Δ using (⟦⟧-R)

------------------------------------------------------------------------
-- Renaming
------------------------------------------------------------------------

private
  ext-eq : ∀ {n n′} {ρ ρ′ : Fin n → Fin n′} → (∀ i → ρ i ≡ ρ′ i) → ∀ i → L.extR ρ i ≡ SC.ext {S = S′} {m = m} ρ′ i
  ext-eq e zero    = refl
  ext-eq e (suc i) = cong suc (e i)

TmR-ren : ∀ {n n′} {t : L.Tm n} {t′} (ρ ρ′ : Fin n → Fin n′) → (∀ i → ρ i ≡ ρ′ i)
        → TmR Δ t t′ → TmR Δ (L.ren ρ t) (SC.ren {S = S′} {m = m} ρ′ t′)
TmR-ren ρ ρ′ e (r-var i) = subst (λ j → TmR Δ (L.var (ρ i)) (SC.var j)) (e i) (r-var (ρ i))
TmR-ren ρ ρ′ e (r-lam a t) = r-lam a (TmR-ren (L.extR ρ) (SC.ext {S = S′} {m = m} ρ′) (ext-eq e) t)
TmR-ren ρ ρ′ e (r-app f x) = r-app (TmR-ren ρ ρ′ e f) (TmR-ren ρ ρ′ e x)
TmR-ren ρ ρ′ e (r-let x b) = r-let (TmR-ren ρ ρ′ e x) (TmR-ren (L.extR ρ) (SC.ext {S = S′} {m = m} ρ′) (ext-eq e) b)
TmR-ren ρ ρ′ e r-unit = r-unit
TmR-ren ρ ρ′ e (r-pair a b) = r-pair (TmR-ren ρ ρ′ e a) (TmR-ren ρ ρ′ e b)
TmR-ren ρ ρ′ e (r-fst p) = r-fst (TmR-ren ρ ρ′ e p)
TmR-ren ρ ρ′ e (r-snd p) = r-snd (TmR-ren ρ ρ′ e p)
TmR-ren ρ ρ′ e (r-inl b a) = r-inl b (TmR-ren ρ ρ′ e a)
TmR-ren ρ ρ′ e (r-inr a b) = r-inr a (TmR-ren ρ ρ′ e b)
TmR-ren ρ ρ′ e (r-case x l r) =
  r-case (TmR-ren ρ ρ′ e x) (TmR-ren (L.extR ρ) (SC.ext {S = S′} {m = m} ρ′) (ext-eq e) l) (TmR-ren (L.extR ρ) (SC.ext {S = S′} {m = m} ρ′) (ext-eq e) r)
TmR-ren ρ ρ′ e (r-absurd a x) = r-absurd a (TmR-ren ρ ρ′ e x)
TmR-ren ρ ρ′ e (r-roll f t) = r-roll f (TmR-ren ρ ρ′ e t)
TmR-ren ρ ρ′ e (r-fold f a t) = r-fold f (TmR-ren ρ ρ′ e a) (TmR-ren ρ ρ′ e t)
TmR-ren ρ ρ′ e (r-unfold f c t) = r-unfold f (TmR-ren ρ ρ′ e c) (TmR-ren ρ ρ′ e t)
TmR-ren ρ ρ′ e (r-out t) = r-out (TmR-ren ρ ρ′ e t)
TmR-ren ρ ρ′ e (r-iter f t) = r-iter (TmR-ren ρ ρ′ e f) (TmR-ren ρ ρ′ e t)
TmR-ren ρ ρ′ e (r-coerce a b t) = r-coerce a b (TmR-ren ρ ρ′ e t)
TmR-ren ρ ρ′ e (r-lit l) = r-lit l
TmR-ren ρ ρ′ e (r-prim p t) = r-prim p (TmR-ren ρ ρ′ e t)
TmR-ren ρ ρ′ e (r-sigop a) = r-sigop a
TmR-ren ρ ρ′ e (r-ref d i) = r-ref d i

TmR-wk : ∀ {n} {t : L.Tm n} {t′} → TmR Δ t t′ → TmR Δ (L.wk t) (SC.wk t′)
TmR-wk = TmR-ren suc suc (λ _ → refl)

------------------------------------------------------------------------
-- The generators
------------------------------------------------------------------------

module _ {n : ℕ} where

  private
    Many-arr : ∀ {A A′ B B′} π → TyR Δ A A′ → TyR Δ B B′
             → TyR Δ (A LT.⇒[ LG.mk-kind LG.Many π ] B) (A′ ST.⇒[ SG.mk-kind SG.Many (πS π) ] B′)
    Many-arr π a b = r-⇒ refl a b

  idᶜ-R : ∀ {A A′} π → TyR Δ A A′ → TmR Δ (LD.idᶜ {n} A π) (SD.idᶜ A′ (πS π))
  idᶜ-R π a = r-lam a (r-var zero)

  terminalᶜ-R : ∀ {A A′} π → TyR Δ A A′ → TmR Δ (LD.terminalᶜ {n} A π) (SD.terminalᶜ A′ (πS π))
  terminalᶜ-R π a = r-lam a r-unit

  initialᶜ-R : ∀ {A A′} π → TyR Δ A A′ → TmR Δ (LD.initialᶜ {n} A π) (SD.initialᶜ A′ (πS π))
  initialᶜ-R π a = r-lam r-void (r-absurd a (r-var zero))

  fstᶜ-R : ∀ {A A′ B B′} π → TyR Δ A A′ → TyR Δ B B′ → TmR Δ (LD.fstᶜ {n} A B π) (SD.fstᶜ A′ B′ (πS π))
  fstᶜ-R π a b = r-lam (r-* a b) (r-fst (r-var zero))

  sndᶜ-R : ∀ {A A′ B B′} π → TyR Δ A A′ → TyR Δ B B′ → TmR Δ (LD.sndᶜ {n} A B π) (SD.sndᶜ A′ B′ (πS π))
  sndᶜ-R π a b = r-lam (r-* a b) (r-snd (r-var zero))

  inlᶜ-R : ∀ {A A′ B B′} π → TyR Δ A A′ → TyR Δ B B′ → TmR Δ (LD.inlᶜ {n} A B π) (SD.inlᶜ A′ B′ (πS π))
  inlᶜ-R π a b = r-lam a (r-inl b (r-var zero))

  inrᶜ-R : ∀ {A A′ B B′} π → TyR Δ A A′ → TyR Δ B B′ → TmR Δ (LD.inrᶜ {n} A B π) (SD.inrᶜ A′ B′ (πS π))
  inrᶜ-R π a b = r-lam b (r-inr a (r-var zero))

  applyᶜ-R : ∀ {A A′ B B′} → TyR Δ A A′ → TyR Δ B B′ → TmR Δ (LD.applyᶜ {n} A B) (SD.applyᶜ A′ B′)
  applyᶜ-R a b = r-lam (r-* (Many-arr LG.pure a b) a) (r-app (r-fst (r-var zero)) (r-snd (r-var zero)))

  applyEffᶜ-R : ∀ {A A′ B B′} π → TyR Δ A A′ → TyR Δ B B′ → TmR Δ (LD.applyEffᶜ {n} π A B) (SD.applyEffᶜ (πS π) A′ B′)
  applyEffᶜ-R π a b =
    r-lam (r-* (Many-arr π a b) a) (r-lam r-unit (r-app (r-fst (r-var (suc zero))) (r-snd (r-var (suc zero)))))

  inᶜ-R : ∀ {F F′} → FunR Δ F F′ → TmR Δ (LD.inᶜ {n} F) (SD.inᶜ F′)
  inᶜ-R f = r-lam (⟦⟧-R f (r-μ f)) (r-roll f (r-var zero))

  outᶜ-R : ∀ {F F′} → FunR Δ F F′ → TmR Δ (LD.outᶜ {n} F) (SD.outᶜ F′)
  outᶜ-R f = r-lam (r-ν refl f) (r-out (r-var zero))

  outActᶜ-R : ∀ {F F′} → FunR Δ F F′ → TmR Δ (LD.outEffᶜ {n} LG.actᶠ F) (SD.outActᶜ F′)
  outActᶜ-R f = r-lam (r-ν refl f) (r-lam r-unit (r-out (r-var (suc zero))))

  composeᶜ-R : ∀ {A A′} π {f g : L.Tm n} {f′ g′} → TyR Δ A A′ → TmR Δ f f′ → TmR Δ g g′
             → TmR Δ (LD.composeᶜ A π f g) (SD.composeᶜ A′ (πS π) f′ g′)
  composeᶜ-R π a f g =
    r-let f (r-let (TmR-wk g) (r-lam a (r-app (r-var (suc (suc zero))) (r-app (r-var (suc zero)) (r-var zero)))))

  pairᶜ-R : ∀ {A A′} π {f g : L.Tm n} {f′ g′} → TyR Δ A A′ → TmR Δ f f′ → TmR Δ g g′
          → TmR Δ (LD.pairᶜ A π f g) (SD.pairᶜ A′ (πS π) f′ g′)
  pairᶜ-R π a f g =
    r-let f (r-let (TmR-wk g) (r-lam a (r-pair (r-app (r-var (suc (suc zero))) (r-var zero)) (r-app (r-var (suc zero)) (r-var zero)))))

  caseᶜ-R : ∀ {A A′ B B′} π {f g : L.Tm n} {f′ g′} → TyR Δ A A′ → TyR Δ B B′ → TmR Δ f f′ → TmR Δ g g′
          → TmR Δ (LD.caseᶜ A B π f g) (SD.caseᶜ A′ B′ (πS π) f′ g′)
  caseᶜ-R π a b f g =
    r-let f (r-let (TmR-wk g) (r-lam (r-+ a b)
      (r-case (r-var zero) (r-app (r-var (suc (suc (suc zero)))) (r-var zero)) (r-app (r-var (suc (suc zero))) (r-var zero)))))

  curryᶜ-R : ∀ {A A′ B B′} π₀ π {f : L.Tm n} {f′} → TyR Δ A A′ → TyR Δ B B′ → TmR Δ f f′
           → TmR Δ (LD.curryᶜ A B π₀ π f) (SD.curryᶜ A′ B′ (πS π₀) (πS π) f′)
  curryᶜ-R π₀ π a b f =
    r-let f (r-lam a (r-lam b (r-app (r-var (suc (suc zero))) (r-pair (r-var (suc zero)) (r-var zero)))))

  cataᶜ-R : ∀ {F F′} π {alg : L.Tm n} {alg′} → FunR Δ F F′ → TmR Δ alg alg′
          → TmR Δ (LD.cataᶜ F π alg) (SD.cataᶜ F′ (πS π) alg′)
  cataᶜ-R π f a = r-let a (r-lam (r-μ f) (r-fold f (r-var (suc zero)) (r-var zero)))

  loopᶜ-R : ∀ {A A′} {c : L.Tm n} {c′} → TyR Δ A A′ → TmR Δ c c′ → TmR Δ (LD.loopᶜ A c) (SD.loopᶜ A′ c′)
  loopᶜ-R a c = r-let c (r-lam a (r-iter (r-var (suc zero)) (r-var zero)))

  anaᶜ-R : ∀ {F F′ A A′} π₀ {c : L.Tm n} {c′} → FunR Δ F F′ → TyR Δ A A′ → TmR Δ c c′
         → TmR Δ (LD.anaᶜ F A π₀ c) (SD.anaᶜ F′ A′ (πS π₀) c′)
  anaᶜ-R π₀ f a c = r-lam a (r-unfold f (TmR-wk c) (r-var zero))

  effAppᶜ-R : ∀ π {f x : L.Tm n} {f′ x′} → TmR Δ f f′ → TmR Δ x x′
            → TmR Δ (LD.effAppᶜ π f x) (SD.effAppᶜ (πS π) f′ x′)
  effAppᶜ-R π f x = r-lam r-unit (r-app (TmR-wk f) (TmR-wk x))
