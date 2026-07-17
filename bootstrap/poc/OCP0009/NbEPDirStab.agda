------------------------------------------------------------------------
-- OCP-0009 · dHoTT step 12 — CwF STABILITY: type formers commute with subst
--
-- The last CwF hygiene: every type former is STABLE under substitution —
-- `(A ⊕ B)[σ] ≡ (A[σ]) ⊕ (B[σ])`, and likewise `Σ`. This is what lets a
-- substitution push through a type, the coherence a real type theory needs.
--
-- `×⁺` is the clean case: both sides have DEFINITIONALLY equal `fam`/`act`
-- (`×` has η, and both substitution and the former act by `σ.homₛ`), so only
-- the `actid`/`act⨾` PROOF fields differ — they agree by `funext` + `uip`, the
-- `DirCwFL.subst-∘` pattern. `funext` (three flavours) threaded — stays `--safe`.
--
-- Scope note: `+⁺` and the dependent `Σ⁺`/`Π⁺` are NOT this clean — `⊎` has no
-- η, so their `act` fields are only PROPOSITIONALLY equal, and the record
-- equality must then compare the `act` fields themselves. That comparison
-- runs into a real AGDA ELABORATION limitation: assigning a bound
-- implicit-argument function (`∀ {x y} → …`) to the implicit `act` field of a
-- reconstructed `Ty⁺` record triggers `MetaCannotDependOn`, across `record{}`,
-- explicit implicit-λ, copatterns, and explicit-index encodings alike. So
-- `×⁺-[]` (the η case) is the clean representative; the non-η laws are blocked
-- by tooling, not by mathematics (a `Ty⁺`-with-explicit-`act` wrapper type, or
-- a specialized `funext`, would unblock them).
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPDirStab where

open import normalizer.Syntax.Types using ( _≡_; refl; inj₁; inj₂ )
open import poc.OCP0009.NbEPDirCwF using ( Ctx; Ty⁺; Sub; _[_]⁺ )
open import poc.OCP0009.NbEPDirCwFL using ( _≡₁_; cong₂₁ )
open import poc.OCP0009.NbEPDirTy using ( _×⁺_; _+⁺_ )
open import poc.OCP0009.NbEPDirSig using ( uip )
open import poc.OCP0009.NbEPDirTyExt using ( cong₁; module W )

module _
  (funext  : ∀ {A : Set} {B : A → Set} {f g : (x : A) → B x} →
             (∀ x → f x ≡ g x) → f ≡ g)
  (funextᵢ : ∀ {A : Set} {B : A → Set} {f g : ∀ {x} → B x} →
             (∀ x → f {x} ≡ g {x}) → (λ {x} → f {x}) ≡ (λ {x} → g {x}))
  (funextᵢ₃ : ∀ {A B C : Set} {D : A → B → C → Set}
              {f g : ∀ {x y z} → D x y z} →
              (∀ x y z → f {x} {y} {z} ≡ g {x} {y} {z}) →
              (λ {x} {y} {z} → f {x} {y} {z}) ≡ (λ {x} {y} {z} → g {x} {y} {z}))
  where

  -- Product commutes with substitution.
  ×⁺-[] : ∀ {Δ Γ} (A B : Ty⁺ Γ) (σ : Sub Δ Γ) →
          ((A ×⁺ B) [ σ ]⁺) ≡₁ ((A [ σ ]⁺) ×⁺ (B [ σ ]⁺))
  ×⁺-[] {Δ} A B σ = cong₂₁ mk eqa eqc
    where
    open Ty⁺ ((A ×⁺ B) [ σ ]⁺) ; open Ctx Δ
    mk : (∀ {x} (p : fam x) → act idₒ p ≡ p)
       → (∀ {x y z} (f : x ⇒ y) (g : y ⇒ z) (p : fam x) →
            act (f ⨾ g) p ≡ act g (act f p))
       → Ty⁺ Δ
    mk pa pc = record { fam = fam ; act = act ; actid = pa ; act⨾ = pc }
    eqa = funextᵢ (λ _ → funext (λ _ → uip _ _))
    eqc = funextᵢ₃ (λ _ _ _ → funext (λ _ → funext (λ _ → funext (λ _ → uip _ _))))

  -- Sum commutes with substitution — the `act` fields are only propositionally
  -- equal (`⊎` has no η), so we go through the `Ty⁺` EXTENSIONALITY wrapper
  -- (`NbEPDirTyExt.W`): compare `act` as functions (case-split under `funext`),
  -- transport back by `cong₁ toTy⁺`.
  +⁺-[] : ∀ {Δ Γ} (A B : Ty⁺ Γ) (σ : Sub Δ Γ) →
          ((A +⁺ B) [ σ ]⁺) ≡₁ ((A [ σ ]⁺) +⁺ (B [ σ ]⁺))
  +⁺-[] {Δ} A B σ =
    cong₁ toTy⁺
      (Ty⁺ᵉ-≡ (Ty⁺.fam LHS)
              (λ x y → Ty⁺.act LHS {x} {y}) (λ x y → Ty⁺.act RHS {x} {y})
              (λ x → Ty⁺.actid LHS {x}) (λ x → Ty⁺.actid RHS {x})
              (λ x y z → Ty⁺.act⨾ LHS {x} {y} {z}) (λ x y z → Ty⁺.act⨾ RHS {x} {y} {z})
              (funext (λ _ → funext (λ _ → funext (λ _ → funext
                (λ { (inj₁ _) → refl ; (inj₂ _) → refl }))))))
    where
    LHS = (A +⁺ B) [ σ ]⁺
    RHS = (A [ σ ]⁺) +⁺ (B [ σ ]⁺)
    open W funext Δ
