{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Metatheory.Trace — weak bisimilarity of traces is an equivalence
-- (given one on the values), and it is agreement at every depth.
--
-- Corecursive proofs keep the inductive part (how one visible step
-- arrives) out of the corecursion: a matching lemma returns first-order
-- evidence, and the corecursive call sits directly under the pair.
------------------------------------------------------------------------

open import Once.Spec.Signature using (Event)

module Once.Metatheory.Trace where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (∃-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (flip)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Once.Spec.Delay using (Delay; module Delay; now; _⇓_; now⇓; later⇓; _≈⟨_⟩_)
open import Once.Spec.Trace using (End; returned; halted; Tr; module Tr; EndRel; returned≈; halted≈; StepRel; _≈ᵗ⟨_⟩_; module _≈ᵗ⟨_⟩_)

open Delay using (step)
open Tr using (next)
open _≈ᵗ⟨_⟩_ using (same)

private
  S : Set → Set
  S X = End X ⊎ (Event × Tr X)

------------------------------------------------------------------------
-- An equivalence
------------------------------------------------------------------------

module _ {X : Set} {R : X → X → Set} where

  WB-refl  : (∀ x → R x x) → ∀ (t : Tr X) → t ≈ᵗ⟨ R ⟩ t
  reflStep : (∀ x → R x x) → ∀ (o : S X) → StepRel R (λ u u′ → u ≈ᵗ⟨ R ⟩ u′) o o
  same (WB-refl r t) = (λ o a → o , a , reflStep r o) , (λ o a → o , a , reflStep r o)
  reflStep r (inj₁ (returned x)) = returned≈ (r x)
  reflStep r (inj₁ halted)       = halted≈
  reflStep r (inj₂ (v , t))      = refl , WB-refl r t

  private
    flipEnd : ∀ {e e′} → (∀ {x y} → R x y → R y x) → EndRel R e e′ → EndRel R e′ e
    flipEnd s (returned≈ r) = returned≈ (s r)
    flipEnd s halted≈       = halted≈

  WB-sym  : (∀ {x y} → R x y → R y x) → ∀ {t t′ : Tr X} → t ≈ᵗ⟨ R ⟩ t′ → t′ ≈ᵗ⟨ R ⟩ t
  symStep : (∀ {x y} → R x y → R y x) → ∀ {o o′ : S X} → StepRel R (λ u u′ → u ≈ᵗ⟨ R ⟩ u′) o o′
          → StepRel R (λ u u′ → u ≈ᵗ⟨ R ⟩ u′) o′ o
  same (WB-sym s p) = (λ o a → turn (proj₂ (same p) o a)) , (λ o a → turn′ (proj₁ (same p) o a))
    where
      turn : ∀ {d : Delay (S X)} {o′} → ∃[ o ] (d ⇓ o × StepRel R _ o o′) → ∃[ o ] (d ⇓ o × StepRel R _ o′ o)
      turn (o , a , r) = o , a , symStep s r
      turn′ : ∀ {d : Delay (S X)} {o} → ∃[ o′ ] (d ⇓ o′ × StepRel R _ o o′) → ∃[ o′ ] (d ⇓ o′ × StepRel R _ o′ o)
      turn′ (o′ , a , r) = o′ , a , symStep s r
  symStep s {inj₁ e}       {inj₁ e′}        r          = flipEnd s r
  symStep s {inj₂ (v , t)} {inj₂ (v′ , t′)} (eq , p)   = sym eq , WB-sym s p
  symStep s {inj₁ _}       {inj₂ _}         ()
  symStep s {inj₂ _}       {inj₁ _}         ()

  -- Transitivity: match the middle trace's step, then corecursively.
  module _ (R-trans : ∀ {x y z} → R x y → R y z → R x z) where
    private
      endT : ∀ {e₁ e₂ e₃} → EndRel R e₁ e₂ → EndRel R e₂ e₃ → EndRel R e₁ e₃
      endT (returned≈ r) (returned≈ r′) = returned≈ (R-trans r r′)
      endT halted≈ halted≈ = halted≈

      -- The two steps compose: ends to ends, calls to the same call.
      data Comp : S X → S X → S X → Set where
        ends  : ∀ {e₁ e₂ e₃} → EndRel R e₁ e₂ → EndRel R e₂ e₃ → Comp (inj₁ e₁) (inj₁ e₂) (inj₁ e₃)
        calls : ∀ {v t₁ t₂ t₃} → t₁ ≈ᵗ⟨ R ⟩ t₂ → t₂ ≈ᵗ⟨ R ⟩ t₃ → Comp (inj₂ (v , t₁)) (inj₂ (v , t₂)) (inj₂ (v , t₃))

      comp : ∀ {o₁ o₂ o₃ : S X} → StepRel R (λ u u′ → u ≈ᵗ⟨ R ⟩ u′) o₁ o₂ → StepRel R (λ u u′ → u ≈ᵗ⟨ R ⟩ u′) o₂ o₃
           → Comp o₁ o₂ o₃
      comp {inj₁ _} {inj₁ _} {inj₁ _} r r′ = ends r r′
      comp {inj₂ _} {inj₂ _} {inj₂ _} (refl , p) (refl , q) = calls p q
      comp {inj₁ _} {inj₁ _} {inj₂ _} r ()
      comp {inj₁ _} {inj₂ _} () r′
      comp {inj₂ _} {inj₂ _} {inj₁ _} r ()
      comp {inj₂ _} {inj₁ _} () r′

    WB-trans  : ∀ {t₁ t₂ t₃ : Tr X} → t₁ ≈ᵗ⟨ R ⟩ t₂ → t₂ ≈ᵗ⟨ R ⟩ t₃ → t₁ ≈ᵗ⟨ R ⟩ t₃
    transStep : ∀ {o₁ o₂ o₃ : S X} → Comp o₁ o₂ o₃ → StepRel R (λ u u′ → u ≈ᵗ⟨ R ⟩ u′) o₁ o₃
    same (WB-trans {t₁} {t₂} {t₃} p q) = fw , bw
      where
        fw : ∀ o₁ → next t₁ ⇓ o₁ → ∃[ o₃ ] (next t₃ ⇓ o₃ × StepRel R _ o₁ o₃)
        fw o₁ a₁ = two (proj₁ (same p) o₁ a₁)
          where two : ∃[ o₂ ] (next t₂ ⇓ o₂ × StepRel R _ o₁ o₂) → ∃[ o₃ ] (next t₃ ⇓ o₃ × StepRel R _ o₁ o₃)
                two (o₂ , a₂ , r₁) = three r₁ (proj₁ (same q) o₂ a₂)
                  where three : StepRel R _ o₁ o₂ → ∃[ o₃ ] (next t₃ ⇓ o₃ × StepRel R _ o₂ o₃) → ∃[ o₃ ] (next t₃ ⇓ o₃ × StepRel R _ o₁ o₃)
                        three r₁ (o₃ , a₃ , r₂) = o₃ , a₃ , transStep (comp r₁ r₂)
        bw : ∀ o₃ → next t₃ ⇓ o₃ → ∃[ o₁ ] (next t₁ ⇓ o₁ × StepRel R _ o₁ o₃)
        bw o₃ a₃ = two (proj₂ (same q) o₃ a₃)
          where two : ∃[ o₂ ] (next t₂ ⇓ o₂ × StepRel R _ o₂ o₃) → ∃[ o₁ ] (next t₁ ⇓ o₁ × StepRel R _ o₁ o₃)
                two (o₂ , a₂ , r₂) = three r₂ (proj₂ (same p) o₂ a₂)
                  where three : StepRel R _ o₂ o₃ → ∃[ o₁ ] (next t₁ ⇓ o₁ × StepRel R _ o₁ o₂) → ∃[ o₁ ] (next t₁ ⇓ o₁ × StepRel R _ o₁ o₃)
                        three r₂ (o₁ , a₁ , r₁) = o₁ , a₁ , transStep (comp r₁ r₂)
    transStep (ends r r′)  = endT r r′
    transStep (calls p q) = refl , WB-trans p q

-- Weakly bisimilar at a relation implies at a larger one.
module _ {X : Set} {R R′ : X → X → Set} (h : ∀ {x y} → R x y → R′ x y) where
  WB-mono  : ∀ {t t′ : Tr X} → t ≈ᵗ⟨ R ⟩ t′ → t ≈ᵗ⟨ R′ ⟩ t′
  monoStep : ∀ {o o′ : S X} → StepRel R (λ u u′ → u ≈ᵗ⟨ R ⟩ u′) o o′ → StepRel R′ (λ u u′ → u ≈ᵗ⟨ R′ ⟩ u′) o o′
  same (WB-mono p) = (λ o a → go (proj₁ (same p) o a)) , (λ o a → go′ (proj₂ (same p) o a))
    where
      go : ∀ {d : Delay (S X)} {o} → ∃[ o′ ] (d ⇓ o′ × StepRel R _ o o′) → ∃[ o′ ] (d ⇓ o′ × StepRel R′ _ o o′)
      go (o′ , a , r) = o′ , a , monoStep r
      go′ : ∀ {d : Delay (S X)} {o′} → ∃[ o ] (d ⇓ o × StepRel R _ o o′) → ∃[ o ] (d ⇓ o × StepRel R′ _ o o′)
      go′ (o , a , r) = o , a , monoStep r
  monoStep {inj₁ _} {inj₁ _} (returned≈ r) = returned≈ (h r)
  monoStep {inj₁ _} {inj₁ _} halted≈       = halted≈
  monoStep {inj₂ _} {inj₂ _} (eq , p)      = eq , WB-mono p
  monoStep {inj₁ _} {inj₂ _} ()
  monoStep {inj₂ _} {inj₁ _} ()

------------------------------------------------------------------------
-- Delay: bind, and arrival through it
------------------------------------------------------------------------

bindD : ∀ {A B : Set} → Delay A → (A → Delay B) → Delay B
bindS : ∀ {A B : Set} → A ⊎ Delay A → (A → Delay B) → B ⊎ Delay B
step (bindD d f) = bindS (step d) f
bindS (inj₁ a) f = step (f a)
bindS (inj₂ d) f = inj₂ (bindD d f)

nowInv : ∀ {A : Set} {a b : A} → now a ⇓ b → a ≡ b
nowInv (now⇓ refl) = refl

private
  inj₁-inj : ∀ {A : Set} {x y : A} {B : Set} → _≡_ {A = A ⊎ B} (inj₁ x) (inj₁ y) → x ≡ y
  inj₁-inj refl = refl
  inj₂-inj : ∀ {A : Set} {d d′ : Delay A} → _≡_ {A = A ⊎ Delay A} (inj₂ d) (inj₂ d′) → d ≡ d′
  inj₂-inj refl = refl
  clash₁₂ : ∀ {A : Set} {x : A} {d} {C : Set} → _≡_ {A = A ⊎ Delay A} (inj₁ x) (inj₂ d) → C
  clash₁₂ ()

-- Arrival is deterministic.
⇓-det : ∀ {A : Set} {d : Delay A} {a b} → d ⇓ a → d ⇓ b → a ≡ b
⇓-det (now⇓ e)      (now⇓ e′)       = inj₁-inj (trans (sym e) e′)
⇓-det (now⇓ e)      (later⇓ e′ _)   = clash₁₂ (trans (sym e) e′)
⇓-det (later⇓ e _)  (now⇓ e′)       = clash₁₂ (trans (sym e′) e)
⇓-det (later⇓ e d⇓) (later⇓ e′ d⇓′) = ⇓-det d⇓ (subst (_⇓ _) (inj₂-inj (trans (sym e′) e)) d⇓′)

bind⇓ : ∀ {A B : Set} {d : Delay A} {f : A → Delay B} {a b} → d ⇓ a → f a ⇓ b → bindD d f ⇓ b
bind⇓ {f = f} (now⇓ e′) (now⇓ e″)     = now⇓ (trans (cong (λ s → bindS s f) e′) e″)
bind⇓ {f = f} (now⇓ e′) (later⇓ e″ x) = later⇓ (trans (cong (λ s → bindS s f) e′) e″) x
bind⇓ {f = f} (later⇓ e′ a⇓) b⇓       = later⇓ (cong (λ s → bindS s f) e′) (bind⇓ a⇓ b⇓)

-- What arrives through a bind came from an arrival of each part.
bind⇓⁻ : ∀ {A B : Set} (d : Delay A) (f : A → Delay B) {b} → bindD d f ⇓ b → ∃[ a ] (d ⇓ a × f a ⇓ b)
private
  go⁻ : ∀ {A B : Set} (d : Delay A) (f : A → Delay B) {b} {d₀ : Delay B} → step d₀ ≡ bindS (step d) f → d₀ ⇓ b
      → ∃[ a ] (d ⇓ a × f a ⇓ b)
  at⁻ : ∀ {A B : Set} (d : Delay A) (f : A → Delay B) {b} {d₀ : Delay B} (s : A ⊎ Delay A) → step d ≡ s
      → step d₀ ≡ bindS s f → d₀ ⇓ b → ∃[ a ] (d ⇓ a × f a ⇓ b)
  more⁻ : ∀ {A B : Set} {d d′ : Delay A} {f : A → Delay B} {b} → step d ≡ inj₂ d′ → ∃[ a ] (d′ ⇓ a × f a ⇓ b)
        → ∃[ a ] (d ⇓ a × f a ⇓ b)
  more⁻ es (a , a⇓ , b⇓) = a , later⇓ es a⇓ , b⇓
  go⁻ d f e b⇓ = at⁻ d f (step d) refl e b⇓
  at⁻ d f (inj₁ a)  es e (now⇓ e′)     = a , now⇓ es , now⇓ (trans (sym e) e′)
  at⁻ d f (inj₁ a)  es e (later⇓ e′ x) = a , now⇓ es , later⇓ (trans (sym e) e′) x
  at⁻ d f (inj₂ d′) es e (now⇓ e′)     = clash₁₂ (trans (sym e′) e)
  at⁻ d f (inj₂ d′) es e (later⇓ e′ x) = more⁻ es (go⁻ d′ f (cong step (inj₂-inj (trans (sym e′) e))) x)
bind⇓⁻ d f b⇓ = go⁻ d f refl b⇓

------------------------------------------------------------------------
-- Observation to a depth: the first `n` visible steps — calls, then the end
-- (`just`) or not yet (`nothing`, cut)
------------------------------------------------------------------------

Obs : Set → Set
Obs X = List Event × Maybe (End X)

pre     : ∀ {X} → ℕ → Tr X → Delay (Obs X)
preStep : ∀ {X} → ℕ → S X → Delay (Obs X)
pre zero    t = now ([] , nothing)
pre (suc n) t = bindD (next t) (preStep n)
preStep n (inj₁ e)       = now ([] , just e)
preStep n (inj₂ (v , t)) = bindD (pre n t) λ o → now (v ∷ proj₁ o , proj₂ o)

data MaybeEnd {X : Set} (R : X → X → Set) : Maybe (End X) → Maybe (End X) → Set where
  cut≈  : MaybeEnd R nothing nothing
  end≈  : ∀ {e e′} → EndRel R e e′ → MaybeEnd R (just e) (just e′)

ObsR : ∀ {X} → (X → X → Set) → Obs X → Obs X → Set
ObsR R o o′ = proj₁ o ≡ proj₁ o′ × MaybeEnd R (proj₂ o) (proj₂ o′)

Depth : ∀ {X} → (X → X → Set) → Tr X → Tr X → Set
Depth R t t′ = ∀ n → pre n t ≈⟨ ObsR R ⟩ pre n t′

------------------------------------------------------------------------
-- Agreement at every depth is weak bisimilarity
------------------------------------------------------------------------

-- What depth one shows of a next step.
FirstIs : ∀ {X} → S X → Obs X → Set
FirstIs (inj₁ e)       o′ = o′ ≡ ([] , just e)
FirstIs (inj₂ (v , _)) o′ = o′ ≡ (v ∷ [] , nothing)

private
  ∷-inj : ∀ {v v′ : Event} {l l′} → _≡_ {A = List Event} (v ∷ l) (v′ ∷ l′) → v ≡ v′ × l ≡ l′
  ∷-inj refl = refl , refl
  []≢∷ : ∀ {v : Event} {l} {C : Set} → _≡_ {A = List Event} [] (v ∷ l) → C
  []≢∷ ()

firstOf : ∀ {X} (t : Tr X) {o} → pre 1 t ⇓ o → ∃[ s ] (next t ⇓ s × FirstIs s o)
firstOf {X} t o⇓ = go (bind⇓⁻ (next t) (preStep 0) o⇓)
  where
    lift₀ : ∀ {v : Event} {o} → ∃[ o₀ ] (now {A = Obs X} ([] , nothing) ⇓ o₀ × now (v ∷ proj₁ o₀ , proj₂ o₀) ⇓ o)
          → o ≡ (v ∷ [] , nothing)
    lift₀ {v} (o₀ , p₀ , p₁) = trans (sym (nowInv p₁)) (cong (λ o₁ → v ∷ proj₁ o₁ , proj₂ o₁) (sym (nowInv p₀)))
    at : ∀ {o} (s : S X) → preStep 0 s ⇓ o → FirstIs s o
    at (inj₁ e)        p = sym (nowInv p)
    at (inj₂ (v , t₁)) p = lift₀ (bind⇓⁻ (now ([] , nothing)) _ p)
    go : ∀ {o} → ∃[ s ] (next t ⇓ s × preStep 0 s ⇓ o) → ∃[ s ] (next t ⇓ s × FirstIs s o)
    go (s , a , p) = s , a , at s p

seeFirst : ∀ {X} {t : Tr X} (s : S X) → next t ⇓ s → ∃[ o ] (pre 1 t ⇓ o × FirstIs s o)
seeFirst (inj₁ e)        a = _ , bind⇓ a (now⇓ refl) , refl
seeFirst (inj₂ (v , t₁)) a = _ , bind⇓ a (bind⇓ (now⇓ refl) (now⇓ refl)) , refl

-- A call's rest, observed one call shallower.
deeper : ∀ {X} {t : Tr X} {v t₁ n o} → next t ⇓ inj₂ (v , t₁) → pre n t₁ ⇓ o → pre (suc n) t ⇓ (v ∷ proj₁ o , proj₂ o)
deeper a o⇓ = bind⇓ a (bind⇓ o⇓ (now⇓ refl))

shallower : ∀ {X} {t : Tr X} {v t₁ n o′} → next t ⇓ inj₂ (v , t₁) → pre (suc n) t ⇓ o′
          → ∃[ o ] (pre n t₁ ⇓ o × o′ ≡ (v ∷ proj₁ o , proj₂ o))
shallower {X} {t} {v} {t₁} {n} a o′⇓ = go (bind⇓⁻ (next t) (preStep n) o′⇓)
  where
    inner : ∀ {o′} → ∃[ o ] (pre n t₁ ⇓ o × now (v ∷ proj₁ o , proj₂ o) ⇓ o′) → ∃[ o ] (pre n t₁ ⇓ o × o′ ≡ (v ∷ proj₁ o , proj₂ o))
    inner (o , o⇓ , n⇓) = o , o⇓ , sym (nowInv n⇓)
    sameS : ∀ {s o′} → inj₂ (v , t₁) ≡ s → preStep n s ⇓ o′ → ∃[ o ] (pre n t₁ ⇓ o × o′ ≡ (v ∷ proj₁ o , proj₂ o))
    sameS refl p = inner (bind⇓⁻ (pre n t₁) _ p)
    go : ∀ {o′} → ∃[ s ] (next t ⇓ s × preStep n s ⇓ o′) → ∃[ o ] (pre n t₁ ⇓ o × o′ ≡ (v ∷ proj₁ o , proj₂ o))
    go (s , a′ , p) = sameS (⇓-det a a′) p

module _ {X : Set} {R : X → X → Set} where
  -- After the same call on both sides, the rests agree at every depth.
  restDepth : ∀ {t t′ : Tr X} {v t₁ t₁′} → Depth R t t′ → next t ⇓ inj₂ (v , t₁) → next t′ ⇓ inj₂ (v , t₁′)
            → Depth R t₁ t₁′
  restDepth {t} {t′} {v} {t₁} {t₁′} p a a′ n = fw , bw
    where
      fw : ∀ o → pre n t₁ ⇓ o → ∃[ o′ ] (pre n t₁′ ⇓ o′ × ObsR R o o′)
      fw o o⇓ = step₁ (proj₁ (p (suc n)) _ (deeper {t = t} a o⇓))
        where
          fin : ∀ {o″} → ObsR R (v ∷ proj₁ o , proj₂ o) o″ → ∃[ o₁ ] (pre n t₁′ ⇓ o₁ × o″ ≡ (v ∷ proj₁ o₁ , proj₂ o₁))
              → ∃[ o′ ] (pre n t₁′ ⇓ o′ × ObsR R o o′)
          fin (eq , me) (o₁ , o₁⇓ , refl) = o₁ , o₁⇓ , proj₂ (∷-inj eq) , me
          step₁ : ∃[ o″ ] (pre (suc n) t′ ⇓ o″ × ObsR R (v ∷ proj₁ o , proj₂ o) o″) → ∃[ o′ ] (pre n t₁′ ⇓ o′ × ObsR R o o′)
          step₁ (o″ , o″⇓ , r) = fin r (shallower {t = t′} a′ o″⇓)
      bw : ∀ o′ → pre n t₁′ ⇓ o′ → ∃[ o ] (pre n t₁ ⇓ o × ObsR R o o′)
      bw o′ o′⇓ = step₁ (proj₂ (p (suc n)) _ (deeper {t = t′} a′ o′⇓))
        where
          fin : ∀ {o″} → ObsR R o″ (v ∷ proj₁ o′ , proj₂ o′) → ∃[ o₁ ] (pre n t₁ ⇓ o₁ × o″ ≡ (v ∷ proj₁ o₁ , proj₂ o₁))
              → ∃[ o ] (pre n t₁ ⇓ o × ObsR R o o′)
          fin (eq , me) (o₁ , o₁⇓ , refl) = o₁ , o₁⇓ , proj₂ (∷-inj eq) , me
          step₁ : ∃[ o″ ] (pre (suc n) t ⇓ o″ × ObsR R o″ (v ∷ proj₁ o′ , proj₂ o′)) → ∃[ o ] (pre n t₁ ⇓ o × ObsR R o o′)
          step₁ (o″ , o″⇓ , r) = fin r (shallower {t = t} a o″⇓)

  -- An end on one side: the same kind of end on the other.
  endMatch : ∀ {t t′ : Tr X} {e} → Depth R t t′ → next t ⇓ inj₁ e → ∃[ e′ ] (next t′ ⇓ inj₁ e′ × EndRel R e e′)
  endMatch {t} {t′} {e} p a = one (seeFirst {t = t} (inj₁ e) a)
    where
      decide : ∀ {o′} (s′ : S X) → next t′ ⇓ s′ → FirstIs s′ o′ → ObsR R ([] , just e) o′
             → ∃[ e′ ] (next t′ ⇓ inj₁ e′ × EndRel R e e′)
      decide (inj₁ e′)      a′ refl (_ , end≈ r) = e′ , a′ , r
      decide (inj₂ (v , _)) a′ refl (eq , _)     = []≢∷ eq
      two : ∃[ o′ ] (pre 1 t′ ⇓ o′ × ObsR R ([] , just e) o′) → ∃[ e′ ] (next t′ ⇓ inj₁ e′ × EndRel R e e′)
      two (o′ , o′⇓ , r) = three (firstOf t′ o′⇓)
        where three : ∃[ s′ ] (next t′ ⇓ s′ × FirstIs s′ o′) → ∃[ e′ ] (next t′ ⇓ inj₁ e′ × EndRel R e e′)
              three (s′ , a′ , fi) = decide s′ a′ fi r
      one : ∃[ o ] (pre 1 t ⇓ o × FirstIs (inj₁ e) o) → ∃[ e′ ] (next t′ ⇓ inj₁ e′ × EndRel R e e′)
      one (o , o⇓ , refl) = two (proj₁ (p 1) _ o⇓)

  -- A call on one side: the same call on the other, the rests agreeing.
  emitMatch : ∀ {t t′ : Tr X} {v t₁} → Depth R t t′ → next t ⇓ inj₂ (v , t₁)
            → ∃[ t₁′ ] (next t′ ⇓ inj₂ (v , t₁′) × Depth R t₁ t₁′)
  emitMatch {t} {t′} {v} {t₁} p a = one (seeFirst {t = t} (inj₂ (v , t₁)) a)
    where
      decide : ∀ {o′} (s′ : S X) → next t′ ⇓ s′ → FirstIs s′ o′ → ObsR R (v ∷ [] , nothing) o′
             → ∃[ t₁′ ] (next t′ ⇓ inj₂ (v , t₁′) × Depth R t₁ t₁′)
      decide (inj₁ e′)         a′ refl (eq , _) = []≢∷ (sym eq)
      decide (inj₂ (v′ , t₁′)) a′ refl (eq , _) = fin (proj₁ (∷-inj eq)) a′
        where fin : v ≡ v′ → next t′ ⇓ inj₂ (v′ , t₁′) → ∃[ t₁″ ] (next t′ ⇓ inj₂ (v , t₁″) × Depth R t₁ t₁″)
              fin refl a″ = t₁′ , a″ , restDepth {t = t} {t′} p a a″
      two : ∃[ o′ ] (pre 1 t′ ⇓ o′ × ObsR R (v ∷ [] , nothing) o′) → ∃[ t₁′ ] (next t′ ⇓ inj₂ (v , t₁′) × Depth R t₁ t₁′)
      two (o′ , o′⇓ , r) = three (firstOf t′ o′⇓)
        where three : ∃[ s′ ] (next t′ ⇓ s′ × FirstIs s′ o′) → ∃[ t₁′ ] (next t′ ⇓ inj₂ (v , t₁′) × Depth R t₁ t₁′)
              three (s′ , a′ , fi) = decide s′ a′ fi r
      one : ∃[ o ] (pre 1 t ⇓ o × FirstIs (inj₂ (v , t₁)) o) → ∃[ t₁′ ] (next t′ ⇓ inj₂ (v , t₁′) × Depth R t₁ t₁′)
      one (o , o⇓ , refl) = two (proj₁ (p 1) _ o⇓)

-- Symmetry of the depth relation.
private
  EndRel-flip : ∀ {X} {R : X → X → Set} {e e′} → EndRel R e e′ → EndRel (flip R) e′ e
  EndRel-flip (returned≈ r) = returned≈ r
  EndRel-flip halted≈ = halted≈
  EndRel-unflip : ∀ {X} {R : X → X → Set} {e e′} → EndRel (flip R) e′ e → EndRel R e e′
  EndRel-unflip (returned≈ r) = returned≈ r
  EndRel-unflip halted≈ = halted≈
  MaybeEnd-flip : ∀ {X} {R : X → X → Set} {e e′} → MaybeEnd R e e′ → MaybeEnd (flip R) e′ e
  MaybeEnd-flip cut≈ = cut≈
  MaybeEnd-flip (end≈ r) = end≈ (EndRel-flip r)
  ObsR-flip : ∀ {X} {R : X → X → Set} {o o′} → ObsR R o o′ → ObsR (flip R) o′ o
  ObsR-flip (eq , me) = sym eq , MaybeEnd-flip me

Depth-sym : ∀ {X} {R : X → X → Set} {t t′ : Tr X} → Depth R t t′ → Depth (flip R) t′ t
Depth-sym {R = R} {t} {t′} p n = (λ o o⇓ → turn₁ (proj₂ (p n) o o⇓)) , (λ o o⇓ → turn₂ (proj₁ (p n) o o⇓))
  where
    turn₁ : ∀ {o} → ∃[ o₁ ] (pre n t ⇓ o₁ × ObsR R o₁ o) → ∃[ o₁ ] (pre n t ⇓ o₁ × ObsR (flip R) o o₁)
    turn₁ (o₁ , a , r) = o₁ , a , ObsR-flip r
    turn₂ : ∀ {o} → ∃[ o₁ ] (pre n t′ ⇓ o₁ × ObsR R o o₁) → ∃[ o₁ ] (pre n t′ ⇓ o₁ × ObsR (flip R) o₁ o)
    turn₂ (o₁ , a , r) = o₁ , a , ObsR-flip r

-- THE CONVERSION: agreement at every depth gives weak bisimilarity. The
-- corecursive call sits directly under the pairs.
fromDepth : ∀ {X} {R : X → X → Set} {t t′ : Tr X} → Depth R t t′ → t ≈ᵗ⟨ R ⟩ t′
fwdD : ∀ {X} {R : X → X → Set} {t t′ : Tr X} → Depth R t t′ → ∀ o → next t ⇓ o
     → ∃[ o′ ] (next t′ ⇓ o′ × StepRel R (λ u u′ → u ≈ᵗ⟨ R ⟩ u′) o o′)
bwdD : ∀ {X} {R : X → X → Set} {t t′ : Tr X} → Depth R t t′ → ∀ o′ → next t′ ⇓ o′
     → ∃[ o ] (next t ⇓ o × StepRel R (λ u u′ → u ≈ᵗ⟨ R ⟩ u′) o o′)
same (fromDepth p) = (λ o a → fwdD p o a) , (λ o′ a′ → bwdD p o′ a′)
fwdD p (inj₁ e) a = inj₁ (proj₁ (endMatch p a)) , proj₁ (proj₂ (endMatch p a)) , proj₂ (proj₂ (endMatch p a))
fwdD p (inj₂ (v , t₁)) a =
  inj₂ (v , proj₁ (emitMatch p a)) , proj₁ (proj₂ (emitMatch p a)) , refl , fromDepth (proj₂ (proj₂ (emitMatch p a)))
bwdD p (inj₁ e′) a′ =
  inj₁ (proj₁ (endMatch (Depth-sym p) a′)) , proj₁ (proj₂ (endMatch (Depth-sym p) a′)) , EndRel-unflip (proj₂ (proj₂ (endMatch (Depth-sym p) a′)))
bwdD p (inj₂ (v , t₁′)) a′ =
  inj₂ (v , proj₁ (emitMatch (Depth-sym p) a′)) , proj₁ (proj₂ (emitMatch (Depth-sym p) a′)) , refl
  , fromDepth (Depth-sym (proj₂ (proj₂ (emitMatch (Depth-sym p) a′))))

-- And back: weak bisimilarity gives agreement at every depth.
toDepth : ∀ {X} {R : X → X → Set} {t t′ : Tr X} → t ≈ᵗ⟨ R ⟩ t′ → Depth R t t′
toDepth {X} {R} {t} {t′} w zero = (λ o o⇓ → base (nowInv o⇓)) , (λ o o⇓ → base′ (nowInv o⇓))
  where
    base : ∀ {o} → ([] , nothing) ≡ o → ∃[ o′ ] (pre zero t′ ⇓ o′ × ObsR R o o′)
    base refl = _ , now⇓ refl , refl , cut≈
    base′ : ∀ {o} → ([] , nothing) ≡ o → ∃[ o′ ] (pre zero t ⇓ o′ × ObsR R o′ o)
    base′ refl = _ , now⇓ refl , refl , cut≈
toDepth {X} {R} {t} {t′} w (suc n) = fw , bw
  where
    fw : ∀ o → pre (suc n) t ⇓ o → ∃[ o′ ] (pre (suc n) t′ ⇓ o′ × ObsR R o o′)
    fw o o⇓ = split (bind⇓⁻ (next t) (preStep n) o⇓)
      where
        endCase : ∀ {e e′} → ([] , just e) ≡ o → next t′ ⇓ inj₁ e′ → EndRel R e e′ → ∃[ o′ ] (pre (suc n) t′ ⇓ o′ × ObsR R o o′)
        endCase refl a′ r = _ , bind⇓ a′ (now⇓ refl) , refl , end≈ r
        callCase : ∀ {v t₁ t₁′} → next t′ ⇓ inj₂ (v , t₁′) → t₁ ≈ᵗ⟨ R ⟩ t₁′
                 → ∃[ o₁ ] (pre n t₁ ⇓ o₁ × now (v ∷ proj₁ o₁ , proj₂ o₁) ⇓ o) → ∃[ o′ ] (pre (suc n) t′ ⇓ o′ × ObsR R o o′)
        callCase {v} a′ w₁ (o₁ , o₁⇓ , q) = fin (nowInv q) (proj₁ (toDepth w₁ n) o₁ o₁⇓)
          where fin : (v ∷ proj₁ o₁ , proj₂ o₁) ≡ o → ∃[ o₁′ ] (pre n _ ⇓ o₁′ × ObsR R o₁ o₁′) → ∃[ o′ ] (pre (suc n) t′ ⇓ o′ × ObsR R o o′)
                fin refl (o₁′ , o₁′⇓ , eq , me) = _ , deeper {t = t′} a′ o₁′⇓ , cong (v ∷_) eq , me
        both : ∀ s → preStep n s ⇓ o → ∀ s′ → next t′ ⇓ s′ → StepRel R (λ u u′ → u ≈ᵗ⟨ R ⟩ u′) s s′ → ∃[ o′ ] (pre (suc n) t′ ⇓ o′ × ObsR R o o′)
        both (inj₁ e) p (inj₁ e′) a′ r = endCase (nowInv p) a′ r
        both (inj₂ (v , t₁)) p (inj₂ (.v , t₁′)) a′ (refl , w₁) = callCase a′ w₁ (bind⇓⁻ (pre n t₁) _ p)
        both (inj₁ _) p (inj₂ _) a′ ()
        both (inj₂ _) p (inj₁ _) a′ ()
        matched : ∀ {s} → preStep n s ⇓ o → ∃[ s′ ] (next t′ ⇓ s′ × StepRel R (λ u u′ → u ≈ᵗ⟨ R ⟩ u′) s s′) → ∃[ o′ ] (pre (suc n) t′ ⇓ o′ × ObsR R o o′)
        matched {s} p (s′ , a′ , r) = both s p s′ a′ r
        split : ∃[ s ] (next t ⇓ s × preStep n s ⇓ o) → ∃[ o′ ] (pre (suc n) t′ ⇓ o′ × ObsR R o o′)
        split (s , a , p) = matched p (proj₁ (same w) s a)
    bw : ∀ o′ → pre (suc n) t′ ⇓ o′ → ∃[ o ] (pre (suc n) t ⇓ o × ObsR R o o′)
    bw o′ o′⇓ = split (bind⇓⁻ (next t′) (preStep n) o′⇓)
      where
        endCase : ∀ {e e′} → ([] , just e′) ≡ o′ → next t ⇓ inj₁ e → EndRel R e e′ → ∃[ o ] (pre (suc n) t ⇓ o × ObsR R o o′)
        endCase refl a r = _ , bind⇓ a (now⇓ refl) , refl , end≈ r
        callCase : ∀ {v t₁ t₁′} → next t ⇓ inj₂ (v , t₁) → t₁ ≈ᵗ⟨ R ⟩ t₁′
                 → ∃[ o₁ ] (pre n t₁′ ⇓ o₁ × now (v ∷ proj₁ o₁ , proj₂ o₁) ⇓ o′) → ∃[ o ] (pre (suc n) t ⇓ o × ObsR R o o′)
        callCase {v} a w₁ (o₁ , o₁⇓ , q) = fin (nowInv q) (proj₂ (toDepth w₁ n) o₁ o₁⇓)
          where fin : (v ∷ proj₁ o₁ , proj₂ o₁) ≡ o′ → ∃[ o₀ ] (pre n _ ⇓ o₀ × ObsR R o₀ o₁) → ∃[ o ] (pre (suc n) t ⇓ o × ObsR R o o′)
                fin refl (o₀ , o₀⇓ , eq , me) = _ , deeper {t = t} a o₀⇓ , cong (v ∷_) eq , me
        both : ∀ s′ → preStep n s′ ⇓ o′ → ∀ s → next t ⇓ s → StepRel R (λ u u′ → u ≈ᵗ⟨ R ⟩ u′) s s′ → ∃[ o ] (pre (suc n) t ⇓ o × ObsR R o o′)
        both (inj₁ e′) p (inj₁ e) a r = endCase (nowInv p) a r
        both (inj₂ (v , t₁′)) p (inj₂ (.v , t₁)) a (refl , w₁) = callCase a w₁ (bind⇓⁻ (pre n t₁′) _ p)
        both (inj₁ _) p (inj₂ _) a ()
        both (inj₂ _) p (inj₁ _) a ()
        matched : ∀ {s′} → preStep n s′ ⇓ o′ → ∃[ s ] (next t ⇓ s × StepRel R (λ u u′ → u ≈ᵗ⟨ R ⟩ u′) s s′) → ∃[ o ] (pre (suc n) t ⇓ o × ObsR R o o′)
        matched {s′} p (s , a , r) = both s′ p s a r
        split : ∃[ s′ ] (next t′ ⇓ s′ × preStep n s′ ⇓ o′) → ∃[ o ] (pre (suc n) t ⇓ o × ObsR R o o′)
        split (s′ , a′ , p) = matched p (proj₂ (same w) s′ a′)
