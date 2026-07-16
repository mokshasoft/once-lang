------------------------------------------------------------------------
-- OCP-0009 · dHoTT step 5 — a DIRECTED CwF (variance-annotated substitution)
--
-- The base of dependent type theory is a CwF: contexts + substitutions
-- (a category), types-in-context, terms, and comprehension (context
-- extension). Directed dependent types sit on a DIRECTED CwF, whose one
-- difference from the symmetric base is that contexts are directed
-- CATEGORIES (not groupoids) and types carry VARIANCE — the dependent
-- generalization of `NbEPDirV`'s `×→`/`⇒→`.
--
--   * `Ctx`        — a directed context = a category (data; coherence laws
--                    elided in this structural POC);
--   * `Ty⁺` / `Ty⁻` — COVARIANT / CONTRAVARIANT types (functors Γ → Set,
--                    forward / backward), i.e. variance-annotated families;
--   * `Sub`        — a substitution = a functor;
--   * `_[_]⁺`/`_[_]⁻` — SUBSTITUTION RESPECTS VARIANCE: a covariant type
--                    substitutes to a covariant type (functorially), a
--                    contravariant to a contravariant — proven, not posited;
--   * `_▷_`        — comprehension = the Grothendieck construction (the
--                    category of elements), with projection `p` and the
--                    generic variable `q` whose naturality IS the extension
--                    coherence.
--
-- This is the base `NbEPDirJ`'s directed `Id`/`Hom` and `NbEPDirC`'s catas
-- would live over, once given directed type formers.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPDirCwF where

open import normalizer.Syntax.Types
  using ( Σ; _,_; _≡_; refl; cong; trans )
open Σ  -- fst / snd

------------------------------------------------------------------------
-- Contexts: directed = a category.
------------------------------------------------------------------------

record Ctx : Set₁ where
  field
    Ob  : Set
    _⇒_ : Ob → Ob → Set
    idₒ : ∀ {x} → x ⇒ x
    _⨾_ : ∀ {x y z} → x ⇒ y → y ⇒ z → x ⇒ z

------------------------------------------------------------------------
-- Types-in-context, WITH VARIANCE (functors Γ → Set).
------------------------------------------------------------------------

record Ty⁺ (Γ : Ctx) : Set₁ where
  open Ctx Γ
  field
    fam   : Ob → Set
    act   : ∀ {x y} → x ⇒ y → fam x → fam y          -- COVARIANT: forward
    actid : ∀ {x} (a : fam x) → act idₒ a ≡ a
    act⨾  : ∀ {x y z} (f : x ⇒ y) (g : y ⇒ z) (a : fam x) →
            act (f ⨾ g) a ≡ act g (act f a)

record Ty⁻ (Γ : Ctx) : Set₁ where
  open Ctx Γ
  field
    fam   : Ob → Set
    act   : ∀ {x y} → x ⇒ y → fam y → fam x          -- CONTRAVARIANT: backward
    actid : ∀ {x} (a : fam x) → act idₒ a ≡ a
    act⨾  : ∀ {x y z} (f : x ⇒ y) (g : y ⇒ z) (a : fam z) →
            act (f ⨾ g) a ≡ act f (act g a)

------------------------------------------------------------------------
-- Substitutions = functors.
------------------------------------------------------------------------

record Sub (Δ Γ : Ctx) : Set where
  field
    obₛ   : Ctx.Ob Δ → Ctx.Ob Γ
    homₛ  : ∀ {x y} → Ctx._⇒_ Δ x y → Ctx._⇒_ Γ (obₛ x) (obₛ y)
    homid : ∀ {x} → homₛ (Ctx.idₒ Δ {x}) ≡ Ctx.idₒ Γ
    hom⨾  : ∀ {x y z} (f : Ctx._⇒_ Δ x y) (g : Ctx._⇒_ Δ y z) →
            homₛ (Ctx._⨾_ Δ f g) ≡ Ctx._⨾_ Γ (homₛ f) (homₛ g)

------------------------------------------------------------------------
-- Substitution RESPECTS VARIANCE (functorial, per variance).
------------------------------------------------------------------------

_[_]⁺ : ∀ {Δ Γ} → Ty⁺ Γ → Sub Δ Γ → Ty⁺ Δ
_[_]⁺ A σ = record
  { fam   = λ x → fam (obₛ x)
  ; act   = λ f a → act (homₛ f) a
  ; actid = λ a → trans (cong (λ h → act h a) homid) (actid a)
  ; act⨾  = λ f g a → trans (cong (λ h → act h a) (hom⨾ f g))
                            (act⨾ (homₛ f) (homₛ g) a) }
  where open Ty⁺ A ; open Sub σ

_[_]⁻ : ∀ {Δ Γ} → Ty⁻ Γ → Sub Δ Γ → Ty⁻ Δ
_[_]⁻ A σ = record
  { fam   = λ x → fam (obₛ x)
  ; act   = λ f a → act (homₛ f) a
  ; actid = λ a → trans (cong (λ h → act h a) homid) (actid a)
  ; act⨾  = λ f g a → trans (cong (λ h → act h a) (hom⨾ f g))
                            (act⨾ (homₛ f) (homₛ g) a) }
  where open Ty⁻ A ; open Sub σ

------------------------------------------------------------------------
-- Terms = sections (natural in the directed structure).
------------------------------------------------------------------------

record Tm (Γ : Ctx) (A : Ty⁺ Γ) : Set where
  open Ctx Γ ; open Ty⁺ A
  field
    tm  : (x : Ob) → fam x
    nat : ∀ {x y} (f : x ⇒ y) → act f (tm x) ≡ tm y

------------------------------------------------------------------------
-- Comprehension = the Grothendieck construction (category of elements).
------------------------------------------------------------------------

_▷_ : (Γ : Ctx) (A : Ty⁺ Γ) → Ctx
Γ ▷ A = record
  { Ob  = Σ Ob fam
  ; _⇒_ = λ p q → Σ (fst p ⇒ fst q) (λ f → act f (snd p) ≡ snd q)
  ; idₒ = idₒ , actid _
  ; _⨾_ = λ { (f , ef) (g , eg) →
              (f ⨾ g) , trans (act⨾ f g _) (trans (cong (act g) ef) eg) } }
  where open Ctx Γ ; open Ty⁺ A

-- The display projection.
p : ∀ {Γ} {A : Ty⁺ Γ} → Sub (Γ ▷ A) Γ
p = record { obₛ = fst ; homₛ = fst ; homid = refl ; hom⨾ = λ _ _ → refl }

-- The generic variable: its naturality IS the extension coherence.
q : ∀ {Γ} {A : Ty⁺ Γ} → Tm (Γ ▷ A) (A [ p ]⁺)
q = record { tm = snd ; nat = λ { (f , ef) → ef } }
