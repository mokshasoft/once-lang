------------------------------------------------------------------------
-- OCP-0009 · dHoTT step 12d — the op-lift, and `Π⁺` stability (a finding)
--
-- The Cat→Cat substitution machinery for `Π⁺`, and an honest finding about
-- its stability.
--
--   * `_↑⁻_`    — the OP-lift `σ ↑⁻ A : (Δ ▷⁻ A[σ]⁻) ⇒ (Γ ▷⁻ A)` reindexing the
--                 op-Grothendieck (the `Π⁺` analogue of `NbEPDirStab._↑_`);
--   * `Π⁺-restr` — the RESTRICTION MAP `(Π⁺ 𝒞 A B)[σ] ⇛ Π⁺ 𝒟 (A[σ]⁻)(B[σ↑⁻])`
--                 (via a substitution `σ` that is a functor `⌊𝒟⌋ → ⌊𝒞⌋`): a
--                 `𝒞`-future-cone at `σ x` RESTRICTS to a `𝒟`-cone at `x` by
--                 `h' ↦ σ.homₛ h'`.
--
-- THE FINDING: `Π⁺` is NOT stable — `(Π⁺ 𝒞 A B)[σ]` and `Π⁺ 𝒟 (A[σ])(B[σ↑⁻])`
-- are NOT `≡₁`, and NOT EVEN ISO in general (so only LAX-stable, not pseudo).
-- The future-cone fibre indexes over the BASE CATEGORY's morphisms (`h : x ⇒ y`
-- in `𝒞` vs `𝒟`); under a Cat→Cat substitution the index SET changes, so
-- `restrict` (whiskering by `σ`) is neither injective nor surjective for a
-- general functor `σ` — no inverse. This is the failure of BECK–CHEVALLEY for
-- the right-Kan-extension `Π`: it commutes with base change only under exactness
-- conditions (e.g. `σ` an iso). Strict/pseudo stability needs Hofmann
-- strictification, or a FIXED base (substitution not changing the `Cat`). What
-- genuinely holds is the canonical LAX comparison `restrict-⇛` (below).
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPDirPiSub where

open import normalizer.Syntax.Types using ( _≡_; refl; sym; trans; cong; subst; Σ; _,_ )
open Σ
open import poc.OCP0009.NbEPDirCwF using ( Ctx; Cat; ⌊_⌋; Ty⁺; Ty⁻; Sub; _[_]⁻; _[_]⁺ )
open import poc.OCP0009.NbEPDirSig using ( Σ≡; uip )
open import poc.OCP0009.NbEPDirPiG using ( _▷⁻_; Πfib; Π⁺ )
open import poc.OCP0009.NbEPDirCwFJ using ( _⇛_ )

------------------------------------------------------------------------
-- The op-lift.
------------------------------------------------------------------------

_↑⁻_ : ∀ {Δ Γ} (σ : Sub Δ Γ) (A : Ty⁻ Γ) → Sub (Δ ▷⁻ (A [ σ ]⁻)) (Γ ▷⁻ A)
σ ↑⁻ A = record
  { obₛ   = λ p → (Sub.obₛ σ (fst p) , snd p)
  ; homₛ  = λ m → (Sub.homₛ σ (fst m) , snd m)
  ; homid = Σ≡ (Sub.homid σ) (uip _ _)
  ; hom⨾  = λ f g → Σ≡ (Sub.hom⨾ σ (fst f) (fst g)) (uip _ _) }

------------------------------------------------------------------------
-- The restriction of cones: a `𝒞`-future-cone at `σ x` RESTRICTS to a
-- `𝒟`-cone at `x`, by whiskering with `σ`. The `coh` (wedge) is rebuilt from
-- the source cone's `coh` + `σ`'s functoriality (`hom⨾`). This is the fibre
-- component of the canonical stability map — the direction that DOES exist.
------------------------------------------------------------------------

module _ {Δ Γ : Ctx} (σ : Sub Δ Γ) (A : Ty⁻ Γ) (B : Ty⁺ (Γ ▷⁻ A)) where
  private module σ = Sub σ

  restrict : ∀ {x} → Πfib A B (σ.obₛ x) → Πfib (A [ σ ]⁻) (B [ σ ↑⁻ A ]⁺) x
  restrict G = record
    { ap  = λ y' h' a' → Πfib.ap G (σ.obₛ y') (σ.homₛ h') a'
    ; coh = λ y' z' h' k' a' →
        trans (Πfib.coh G (σ.obₛ y') (σ.obₛ z') (σ.homₛ h') (σ.homₛ k') a')
              (cong (λ m → Πfib.ap G (σ.obₛ z') m a') (sym (σ.hom⨾ h' k'))) }

------------------------------------------------------------------------
-- The full lax comparison as a MORPHISM of types (`_⇛_`): `restrict` is
-- natural. Needs `funext` (for `Πfib` equality — the `coh` field is a prop).
------------------------------------------------------------------------

module _
  (funext : ∀ {A : Set} {B : A → Set} {f g : (x : A) → B x} →
            (∀ x → f x ≡ g x) → f ≡ g)
  where

  -- Πfib extensionality: equal `ap` ⟹ equal fibre (`coh` is a proposition).
  module _ {Δ : Ctx} {A : Ty⁻ Δ} {B : Ty⁺ (Δ ▷⁻ A)} where
    private module A = Ty⁻ A ; module B = Ty⁺ B
    open Ctx Δ

    Πfib-ext : ∀ {x} (p q : Πfib A B x) → Πfib.ap p ≡ Πfib.ap q → p ≡ q
    Πfib-ext p q e = go (Πfib.ap p) (Πfib.ap q) (Πfib.coh p) (Πfib.coh q) e
                        (funext (λ y → funext (λ z → funext (λ h → funext (λ k →
                          funext (λ a → uip _ _))))))
      where
      C : ∀ {x} → ((y : Ob) (h : x ⇒ y) (a : A.fam y) → B.fam (y , a)) → Set
      C {x} ap = (y z : Ob) (h : x ⇒ y) (k : y ⇒ z) (a : A.fam z) →
                 B.act (k , refl) (ap y h (A.act k a)) ≡ ap z (h ⨾ k) a
      mk : ∀ {x} (ap : (y : Ob) (h : x ⇒ y) (a : A.fam y) → B.fam (y , a)) →
           C ap → Πfib A B x
      mk ap coh = record { ap = ap ; coh = coh }
      go : ∀ {x} (ap ap' : (y : Ob) (h : x ⇒ y) (a : A.fam y) → B.fam (y , a))
           (coh : C ap) (coh' : C ap') (e : ap ≡ ap') →
           subst C e coh ≡ coh' → mk ap coh ≡ mk ap' coh'
      go ap .ap coh .coh refl refl = refl

  restrict-⇛ : (𝒟 𝒞 : Cat) (σ : Sub ⌊ 𝒟 ⌋ ⌊ 𝒞 ⌋)
               (A : Ty⁻ ⌊ 𝒞 ⌋) (B : Ty⁺ (⌊ 𝒞 ⌋ ▷⁻ A)) →
               (Π⁺ funext 𝒞 A B [ σ ]⁺) ⇛ Π⁺ funext 𝒟 (A [ σ ]⁻) (B [ σ ↑⁻ A ]⁺)
  restrict-⇛ 𝒟 𝒞 σ A B = record
    { comp    = restrict σ A B
    ; natural = λ f G →
        Πfib-ext _ _
          (funext (λ y' → funext (λ h' → funext (λ a' →
            cong (λ m → Πfib.ap G (Sub.obₛ σ y') m a') (Sub.hom⨾ σ f h'))))) }
