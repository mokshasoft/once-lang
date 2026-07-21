------------------------------------------------------------------------
-- OCP-0009 · dHoTT step 42 (M2) — object syntax with a directed Hom-type:
--   directed dependent type theory, directed CONSISTENCY, directed transport.
--
-- Semantic types are DIRECTED SETS (a carrier + a base one-step relation); the
-- directed identity `HomD` is their refl-trans closure.  Formers `Π`/`Hom`/`⊥`
-- are meta-functions (so no universe-positivity clash), and the object term
-- syntax `Tm` is defined MUTUALLY with its interpretation `⟦_⟧` by IR — so
-- dependency (and the Hom-type, which mentions `⟦x⟧`/`⟦y⟧`) needs NO syntactic
-- substitution.  `--safe`, zero axioms.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPDirDHoTT2 where

open import Agda.Builtin.Sigma using ( Σ; _,_; fst; snd )

data Empty : Set where
record ⊤ : Set where
  constructor tt
data Two : Set where
  t0 t1 : Two
data StpTwo : Two → Two → Set where
  arr : StpTwo t0 t1

------------------------------------------------------------------------
-- Directed sets (the semantic types) and the directed identity.
------------------------------------------------------------------------

record DirSet : Set₁ where
  constructor mkD
  field Car : Set
        St  : Car → Car → Set
open DirSet

infixr 5 _◃_
data HomD (A : DirSet) : Car A → Car A → Set where
  rfl : ∀ {x}     → HomD A x x
  _◃_ : ∀ {x y z} → St A x y → HomD A y z → HomD A x z

-- directed (covariant) transport / directed J.
transpD : (A : DirSet) (P : Car A → Set) → (∀ {x y} → St A x y → P x → P y) →
          ∀ {x y} → HomD A x y → P x → P y
transpD A P mono rfl     px = px
transpD A P mono (s ◃ h) px = transpD A P mono h (mono s px)

------------------------------------------------------------------------
-- Contexts + environment interpretation (induction-recursion).
------------------------------------------------------------------------

data Con : Set₁
⟦_⟧C : Con → Set

data Con where
  ε   : Con
  _▷_ : (Γ : Con) → (⟦ Γ ⟧C → DirSet) → Con

⟦ ε ⟧C     = ⊤
⟦ Γ ▷ A ⟧C = Σ ⟦ Γ ⟧C (λ γ → Car (A γ))

Ty : Con → Set₁
Ty Γ = ⟦ Γ ⟧C → DirSet

-- non-Hom type formers.
⊥T : ∀ {Γ} → Ty Γ
⊥T _ = mkD Empty (λ _ _ → Empty)

ιT : ∀ {Γ} → Ty Γ
ιT _ = mkD Two StpTwo

ΠT : ∀ {Γ} (A : Ty Γ) (B : Ty (Γ ▷ A)) → Ty Γ
ΠT A B γ = mkD ((x : Car (A γ)) → Car (B (γ , x))) (λ _ _ → Empty)

------------------------------------------------------------------------
-- Terms + interpretation + the Hom-type former (all mutual: the Hom-type and
-- `app`'s codomain both mention `⟦_⟧`).
------------------------------------------------------------------------

data Tm : (Γ : Con) → Ty Γ → Set₁
⟦_⟧ : ∀ {Γ A} → Tm Γ A → (γ : ⟦ Γ ⟧C) → Car (A γ)

-- the directed identity AS AN OBJECT TYPE.
HomT : ∀ {Γ} (A : Ty Γ) → Tm Γ A → Tm Γ A → Ty Γ
HomT A x y γ = mkD (HomD (A γ) (⟦ x ⟧ γ) (⟦ y ⟧ γ)) (λ _ _ → Empty)

data Tm where
  vz   : ∀ {Γ A} → Tm (Γ ▷ A) (λ γ → A (fst γ))
  vs   : ∀ {Γ A B} → Tm Γ A → Tm (Γ ▷ B) (λ γ → A (fst γ))
  lam  : ∀ {Γ} {A : Ty Γ} {B : Ty (Γ ▷ A)} → Tm (Γ ▷ A) B → Tm Γ (ΠT A B)
  app  : ∀ {Γ} {A : Ty Γ} {B : Ty (Γ ▷ A)} →
         Tm Γ (ΠT A B) → (u : Tm Γ A) → Tm Γ (λ γ → B (γ , ⟦ u ⟧ γ))
  hrfl : ∀ {Γ} {A : Ty Γ} (x : Tm Γ A) → Tm Γ (HomT A x x)

⟦ vz ⟧     (γ , a) = a
⟦ vs t ⟧   (γ , _) = ⟦ t ⟧ γ
⟦ lam t ⟧  γ       = λ x → ⟦ t ⟧ (γ , x)
⟦ app f u ⟧ γ      = ⟦ f ⟧ γ (⟦ u ⟧ γ)
⟦ hrfl x ⟧ γ       = rfl

------------------------------------------------------------------------
-- ★ directed CONSISTENCY, and the genuine DIRECTEDNESS of the identity.
------------------------------------------------------------------------

consistency : Tm ε ⊥T → Empty
consistency t = ⟦ t ⟧ tt

-- the identity on ι is genuinely DIRECTED: an arrow t0 ⟶ t1, none t1 ⟶ t0.
hom01 : HomD (ιT {ε} tt) t0 t1
hom01 = arr ◃ rfl

no-sym : HomD (ιT {ε} tt) t1 t0 → Empty
no-sym (() ◃ _)
