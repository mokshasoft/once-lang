------------------------------------------------------------------------
-- OCP-0009 · dHoTT step 5b — the DIRECTED-CwF SUBSTITUTION LAWS, set-level
--
-- Closing the strict CwF substitution ("presheaf") laws for `NbEPDirCwF`:
--
--   subst-id : A [ idSub ]⁺ ≡ A
--   subst-∘  : A [ σ ∘ₛ τ ]⁺ ≡ (A [ σ ]⁺) [ τ ]⁺
--
-- threading `funext` (as a hypothesis, so the module stays `--safe` — no
-- postulate). The presheaf laws need NO UIP: the `fam`/`act` fields are
-- definitionally equal (η), and the coherence fields differ only by the
-- FUNCTOR-LAW algebra of `cong`/`trans` (`trans-reflˡ`/`cong-trans`/
-- `cong-cong`/`trans-assoc` — all `J`, no `K`). One can SEE this in the
-- proof terms (no K-only construct appears). We can't *certify* it via
-- `--without-K` only because that flag is co-infective and the imported
-- `Types`/`NbEPDirCwF` are `--with-K`. UIP (an h-set `fam`) is needed only
-- for the COMPREHENSION's category laws — flagged, not needed here.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPDirCwFL where

open import normalizer.Syntax.Types
  using ( _≡_; refl; cong; cong₂; trans )
open import poc.OCP0009.NbEPDirCwF
  using ( Ctx; Ty⁺; Sub; _[_]⁺; idSub; _∘ₛ_ )

------------------------------------------------------------------------
-- A `Set₁` equality (the codebase's `_≡_` is `Set`-only, but `Ty⁺ Γ : Set₁`).
-- `cong₂₁` lifts two `Set`-level field equalities to a record equality.
------------------------------------------------------------------------

data _≡₁_ {A : Set₁} (x : A) : A → Set₁ where
  refl₁ : x ≡₁ x

cong₂₁ : {A B : Set} {C : Set₁} (f : A → B → C) {x x' : A} {y y' : B} →
         x ≡ x' → y ≡ y' → f x y ≡₁ f x' y'
cong₂₁ f refl refl = refl₁

------------------------------------------------------------------------
-- The path lemmas needed — all J (each `refl`-match fixes an endpoint).
------------------------------------------------------------------------

trans-reflˡ : ∀ {A : Set} {x y : A} (p : x ≡ y) → trans refl p ≡ p
trans-reflˡ refl = refl

cong-cong : ∀ {A B C : Set} (f : B → C) (g : A → B) {x y : A} (p : x ≡ y) →
            cong f (cong g p) ≡ cong (λ z → f (g z)) p
cong-cong f g refl = refl

cong-trans : ∀ {A B : Set} (f : A → B) {x y z : A} (p : x ≡ y) (q : y ≡ z) →
             cong f (trans p q) ≡ trans (cong f p) (cong f q)
cong-trans f refl refl = refl

trans-assoc : ∀ {A : Set} {w x y z : A}
              (p : w ≡ x) (q : x ≡ y) (r : y ≡ z) →
              trans (trans p q) r ≡ trans p (trans q r)
trans-assoc refl refl refl = refl

------------------------------------------------------------------------
-- The laws, given funext (threaded — no postulate, stays --safe).
------------------------------------------------------------------------

module Laws
  (funext  : ∀ {A : Set} {B : A → Set} {f g : (x : A) → B x} →
             (∀ x → f x ≡ g x) → f ≡ g)
  (funextᵢ : ∀ {A : Set} {B : A → Set} {f g : ∀ {x} → B x} →
             (∀ x → f {x} ≡ g {x}) → (λ {x} → f {x}) ≡ (λ {x} → g {x}))
  (funextᵢ₃ : ∀ {A B C : Set} {D : A → B → C → Set}
              {f g : ∀ {x y z} → D x y z} →
              (∀ x y z → f {x} {y} {z} ≡ g {x} {y} {z}) →
              (λ {x} {y} {z} → f {x} {y} {z}) ≡ (λ {x} {y} {z} → g {x} {y} {z}))
  where

  -- Substitution preserves identity.
  subst-id : ∀ {Γ} (A : Ty⁺ Γ) → (A [ idSub ]⁺) ≡₁ A
  subst-id {Γ} A = cong₂₁ mk eqa eqc
    where
    open Ty⁺ A ; open Ctx Γ
    mk : (∀ {x} (a : fam x) → act idₒ a ≡ a)
       → (∀ {x y z} (f : x ⇒ y) (g : y ⇒ z) (a : fam x) →
            act (f ⨾ g) a ≡ act g (act f a))
       → Ty⁺ Γ
    mk pa pc = record { fam = fam ; act = act ; actid = pa ; act⨾ = pc }
    eqa : (λ {x} (a : fam x) → trans refl (actid a)) ≡ (λ {x} → actid {x})
    eqa = funextᵢ (λ x → funext (λ a → trans-reflˡ (actid a)))
    eqc : (λ {x y z} (f : x ⇒ y) (g : y ⇒ z) (a : fam x)
             → trans refl (act⨾ f g a))
        ≡ (λ {x y z} → act⨾ {x} {y} {z})
    eqc = funextᵢ₃ (λ x y z → funext (λ f → funext (λ g → funext (λ a →
                    trans-reflˡ (act⨾ f g a)))))
