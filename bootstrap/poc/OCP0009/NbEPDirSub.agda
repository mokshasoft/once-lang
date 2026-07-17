------------------------------------------------------------------------
-- OCP-0009 · dHoTT step 11 — the SUBSTITUTION CALCULUS, and `Σ⁺` completed
--
-- The last structural piece of the directed CwF: substituting a TERM into a
-- type (reindexing along a section), which is what `Σ⁺`'s pairing and second
-- projection need. The clean lever: a section `a : Tm Γ A` IS a substitution
-- `extend-id a : Sub Γ (Γ ▷ A)` (into the comprehension), so reindexing `B`
-- along it is just `B [ extend-id a ]⁺` — no bespoke machinery.
--
--   * `_[_]ᵗ`     — term substitution (`Tm Γ A → (σ : Sub Δ Γ) → Tm Δ A[σ]`);
--   * `extend-id` — the section-as-substitution `Γ ⇒ (Γ ▷ A)`;
--   * `pairΣ`     — dependent pairing `(a : Tm Γ A)(b : Tm Γ B[a]) → Tm Γ Σ⁺`;
--   * `sndΣ`      — the SECOND projection, into `B` reindexed along `fstΣ`;
--   * `Σβ₁`/`Σβ₂`/`Ση` — the computation/uniqueness rules (β and η), which
--     land DEFINITIONALLY at the term component (`refl`) — the pairing is a
--     genuine iso `Tm Γ Σ⁺ ≅ Σ (Tm Γ A) (Tm Γ B[-])`.
--
-- The naturality of `pairΣ`/`sndΣ` is the transport-heavy part — the fibre
-- component moves along the base's `nat` — closed by `Σ≡` + a local `subst`-
-- law (`sa`) + `Σ`-projection (`Σ-snd≡`), the same toolkit as `Σ⁺` itself.
-- With this, `Σ⁺` joins `Π⁺` as a COMPLETE directed dependent type former.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPDirSub where

open import normalizer.Syntax.Types
  using ( _≡_; refl; sym; trans; cong; subst; Σ; _,_ )
open Σ
open import poc.OCP0009.NbEPDirCwF using ( Ctx; Ty⁺; Tm; Sub; _▷_; _[_]⁺ )
open import poc.OCP0009.NbEPDirSig using ( Σ⁺; fstΣ; Σ≡; uip )

------------------------------------------------------------------------
-- Term substitution, and the section-as-substitution.
------------------------------------------------------------------------

_[_]ᵗ : ∀ {Δ Γ} {A : Ty⁺ Γ} → Tm Γ A → (σ : Sub Δ Γ) → Tm Δ (A [ σ ]⁺)
a [ σ ]ᵗ = record { tm  = λ x → Tm.tm a (Sub.obₛ σ x)
                  ; nat = λ g → Tm.nat a (Sub.homₛ σ g) }

extend-id : ∀ {Γ} (A : Ty⁺ Γ) → Tm Γ A → Sub Γ (Γ ▷ A)
extend-id {Γ} A a = record
  { obₛ   = λ x → (x , Tm.tm a x)
  ; homₛ  = λ g → (g , Tm.nat a g)
  ; homid = Σ≡ refl (uip _ _)
  ; hom⨾  = λ f g → Σ≡ refl (uip _ _) }
  where open Ctx Γ

------------------------------------------------------------------------
-- `Σ⁺` intro/elim over a fixed `A`, `B`.
------------------------------------------------------------------------

module _ {Γ : Ctx} (A : Ty⁺ Γ) (B : Ty⁺ (Γ ▷ A)) where
  private module Γ = Ctx Γ ; module A = Ty⁺ A ; module B = Ty⁺ B
  open Γ using ( Ob; _⇒_ )

  -- Moving `B.act (g , refl)` along a fibre equality is `B.act (g , e)`.
  sa : ∀ {x y a₀ v} (g : x ⇒ y) (e : A.act g a₀ ≡ v) (w : B.fam (x , a₀)) →
       subst (λ w' → B.fam (y , w')) e (B.act (g , refl) w) ≡ B.act (g , e) w
  sa g refl w = refl

  -- The second component of a `Σ`-equality (transported).
  Σ-snd≡ : ∀ {S : Set} {C : S → Set} {a₁ a₂ : S} {b₁ : C a₁} {b₂ : C a₂}
           (e : (a₁ , b₁) ≡ (a₂ , b₂)) → subst C (cong fst e) b₁ ≡ b₂
  Σ-snd≡ refl = refl

  -- Dependent pairing.
  pairΣ : (a : Tm Γ A) → Tm Γ (B [ extend-id A a ]⁺) → Tm Γ (Σ⁺ A B)
  pairΣ a b = record
    { tm  = λ x → (Tm.tm a x , Tm.tm b x)
    ; nat = λ {x} {y} g →
        Σ≡ (Tm.nat a g)
           (trans (sa g (Tm.nat a g) (Tm.tm b x)) (Tm.nat b g)) }

  -- The second projection: into `B` reindexed along the first projection.
  sndΣ : (p : Tm Γ (Σ⁺ A B)) → Tm Γ (B [ extend-id A (fstΣ A B p) ]⁺)
  sndΣ p = record
    { tm  = λ x → snd (Tm.tm p x)
    ; nat = λ {x} {y} g →
        trans (sym (sa g (cong fst (Tm.nat p g)) (snd (Tm.tm p x))))
              (Σ-snd≡ (Tm.nat p g)) }

  ----------------------------------------------------------------------
  -- β and η — all definitional at the term component. The pairing is an iso
  -- `Tm Γ (Σ⁺ A B) ≅ Σ (Tm Γ A) (λ a → Tm Γ (B [ extend-id A a ]⁺))`.
  ----------------------------------------------------------------------

  Σβ₁ : (a : Tm Γ A) (b : Tm Γ (B [ extend-id A a ]⁺)) (x : Ob) →
        Tm.tm (fstΣ A B (pairΣ a b)) x ≡ Tm.tm a x
  Σβ₁ a b x = refl

  Σβ₂ : (a : Tm Γ A) (b : Tm Γ (B [ extend-id A a ]⁺)) (x : Ob) →
        Tm.tm (sndΣ (pairΣ a b)) x ≡ Tm.tm b x
  Σβ₂ a b x = refl

  Ση : (p : Tm Γ (Σ⁺ A B)) (x : Ob) →
       Tm.tm (pairΣ (fstΣ A B p) (sndΣ p)) x ≡ Tm.tm p x
  Ση p x = refl
