{-# OPTIONS --safe #-}
------------------------------------------------------------------------
-- POC 0.120-B — behaviour as a coinductive trace.
--
-- A trace is the final coalgebra of `Delay ∘ (End + Event × −)`: after
-- finitely many silent steps it ends, or makes one call and goes on (or it
-- never does either). Sameness is its weak bisimilarity, built from
-- `Spec.Delay`'s `_≈⟨_⟩_`. Checks (guardedness under --safe):
--   * `toDepth`: weak bisimilarity gives agreement at every depth;
--   * `fromDepth`: agreement at every depth gives weak bisimilarity (what
--     today's compiler proofs produce);
--   * `WB-trans`: transitivity, corecursively.
------------------------------------------------------------------------

module POC0120.Traces (Event : Set) where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (∃-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Once.Spec.Delay using (Delay; module Delay; _⇓_; now⇓; later⇓; _≈⟨_⟩_)
open Delay using (step)

data End (X : Set) : Set where
  returned : X → End X
  halted   : End X

data EndRel {X : Set} (R : X → X → Set) : End X → End X → Set where
  returned≈ : ∀ {x y} → R x y → EndRel R (returned x) (returned y)
  halted≈   : EndRel R halted halted

record Tr (X : Set) : Set where
  coinductive
  field next : Delay (End X ⊎ (Event × Tr X))
open Tr

------------------------------------------------------------------------
-- Weak bisimilarity: the next visible step arrives on both sides, or on
-- neither; ends related, calls equal and the rests weakly bisimilar
------------------------------------------------------------------------

StepR : ∀ {X : Set} → (X → X → Set) → (Tr X → Tr X → Set) → End X ⊎ (Event × Tr X) → End X ⊎ (Event × Tr X) → Set
StepR R S (inj₁ e)        (inj₁ e′)         = EndRel R e e′
StepR R S (inj₂ (v , t))  (inj₂ (v′ , t′))  = v ≡ v′ × S t t′
StepR R S (inj₁ _)        (inj₂ _)          = ⊥
StepR R S (inj₂ _)        (inj₁ _)          = ⊥

record WB {X : Set} (R : X → X → Set) (t t′ : Tr X) : Set where
  coinductive
  field
    fwd : ∀ o → next t ⇓ o → ∃[ o′ ] (next t′ ⇓ o′ × StepR R (WB R) o o′)
    bwd : ∀ o′ → next t′ ⇓ o′ → ∃[ o ] (next t ⇓ o × StepR R (WB R) o o′)
open WB

------------------------------------------------------------------------
-- Delay: bind, and arrival through it
------------------------------------------------------------------------

private
  bindD : ∀ {A B : Set} → Delay A → (A → Delay B) → Delay B
  bindS : ∀ {A B : Set} → A ⊎ Delay A → (A → Delay B) → B ⊎ Delay B
  step (bindD d f) = bindS (step d) f
  bindS (inj₁ a) f = step (f a)
  bindS (inj₂ d) f = inj₂ (bindD d f)

  nowD : ∀ {A : Set} → A → Delay A
  step (nowD a) = inj₁ a

  -- Arrival is deterministic.
  ⇓-det : ∀ {A : Set} {d : Delay A} {a b} → d ⇓ a → d ⇓ b → a ≡ b
  ⇓-det (now⇓ e)     (now⇓ e′)      = inj₁-inj (trans (sym e) e′)
    where inj₁-inj : ∀ {A : Set} {x y : A} {B : Set} → _≡_ {A = A ⊎ B} (inj₁ x) (inj₁ y) → x ≡ y
          inj₁-inj refl = refl
  ⇓-det (now⇓ e)     (later⇓ e′ _)  = ⊥-elim (clash (trans (sym e) e′))
    where clash : ∀ {A : Set} {x : A} {d} → _≡_ {A = A ⊎ Delay A} (inj₁ x) (inj₂ d) → ⊥
          clash ()
  ⇓-det (later⇓ e _) (now⇓ e′)      = ⊥-elim (clash (trans (sym e′) e))
    where clash : ∀ {A : Set} {x : A} {d} → _≡_ {A = A ⊎ Delay A} (inj₁ x) (inj₂ d) → ⊥
          clash ()
  ⇓-det (later⇓ e d⇓) (later⇓ e′ d⇓′) = ⇓-det d⇓ (subst (_⇓ _) (inj₂-inj (trans (sym e′) e)) d⇓′)
    where inj₂-inj : ∀ {A : Set} {d d′ : Delay A} → _≡_ {A = A ⊎ Delay A} (inj₂ d) (inj₂ d′) → d ≡ d′
          inj₂-inj refl = refl

  bind⇓ : ∀ {A B : Set} {d : Delay A} {f : A → Delay B} {a b} → d ⇓ a → f a ⇓ b → bindD d f ⇓ b
  bind⇓′ : ∀ {A B : Set} {d : Delay A} {f : A → Delay B} {a b} {s} → step d ≡ s → d ⇓ a → f a ⇓ b → bindD d f ⇓ b
  bind⇓ {d = d} a⇓ b⇓ = bind⇓′ {d = d} refl a⇓ b⇓
  bind⇓′ {f = f} e (now⇓ e′) (now⇓ e″)      = now⇓ (trans (cong (λ s → bindS s f) e′) e″)
  bind⇓′ {f = f} e (now⇓ e′) (later⇓ e″ x)  = later⇓ (trans (cong (λ s → bindS s f) e′) e″) x
  bind⇓′ {f = f} e (later⇓ e′ a⇓) b⇓         = later⇓ (cong (λ s → bindS s f) e′) (bind⇓ a⇓ b⇓)

  -- What arrives through a bind came from an arrival of each part (by
  -- induction on the arrival, carrying what the delay is).
  bind⇓⁻ : ∀ {A B : Set} (d : Delay A) (f : A → Delay B) {b} → bindD d f ⇓ b → ∃[ a ] (d ⇓ a × f a ⇓ b)
  go⁻    : ∀ {A B : Set} (d : Delay A) (f : A → Delay B) {b} {d₀ : Delay B} → step d₀ ≡ bindS (step d) f → d₀ ⇓ b
         → ∃[ a ] (d ⇓ a × f a ⇓ b)
  at⁻    : ∀ {A B : Set} (d : Delay A) (f : A → Delay B) {b} {d₀ : Delay B} (s : A ⊎ Delay A) → step d ≡ s
         → step d₀ ≡ bindS s f → d₀ ⇓ b → ∃[ a ] (d ⇓ a × f a ⇓ b)
  bind⇓⁻ d f b⇓ = go⁻ d f refl b⇓
  go⁻ d f e b⇓ = at⁻ d f (step d) refl e b⇓
  at⁻ d f (inj₁ a)  es e (now⇓ e′)     = a , now⇓ es , now⇓ (trans (sym e) e′)
  at⁻ d f (inj₁ a)  es e (later⇓ e′ x) = a , now⇓ es , later⇓ (trans (sym e) e′) x
  at⁻ d f (inj₂ d′) es e (now⇓ e′)     = ⊥-elim (clash (trans (sym e′) e))
    where clash : ∀ {B : Set} {x : B} {d} → _≡_ {A = B ⊎ Delay B} (inj₁ x) (inj₂ d) → ⊥
          clash ()
  at⁻ d f (inj₂ d′) es e (later⇓ e′ x) = more (go⁻ d′ f (cong step (inj₂-inj (trans (sym e′) e))) x)
    where
      inj₂-inj : ∀ {B : Set} {d d″ : Delay B} → _≡_ {A = B ⊎ Delay B} (inj₂ d) (inj₂ d″) → d ≡ d″
      inj₂-inj refl = refl
      more : ∀ {b} → ∃[ a ] (d′ ⇓ a × f a ⇓ b) → ∃[ a ] (d ⇓ a × f a ⇓ b)
      more (a , a⇓ , b⇓) = a , later⇓ es a⇓ , b⇓

------------------------------------------------------------------------
-- Observation to a depth: the first `n` calls, then the end or `nothing`
-- (cut)
------------------------------------------------------------------------

Obs : Set → Set
Obs X = List Event × Maybe (End X)

pre : ∀ {X} → ℕ → Tr X → Delay (Obs X)
preStep : ∀ {X} → ℕ → End X ⊎ (Event × Tr X) → Delay (Obs X)
pre zero    t = nowD ([] , nothing)
pre (suc n) t = bindD (next t) (preStep n)
preStep n (inj₁ e)        = nowD ([] , just e)
preStep n (inj₂ (v , t))  = bindD (pre n t) λ o → nowD (v ∷ proj₁ o , proj₂ o)

data MaybeEnd {X : Set} (R : X → X → Set) : Maybe (End X) → Maybe (End X) → Set where
  cut≈  : MaybeEnd R nothing nothing
  end≈  : ∀ {e e′} → EndRel R e e′ → MaybeEnd R (just e) (just e′)

ObsR : ∀ {X} → (X → X → Set) → Obs X → Obs X → Set
ObsR R o o′ = proj₁ o ≡ proj₁ o′ × MaybeEnd R (proj₂ o) (proj₂ o′)

Depth : ∀ {X} → (X → X → Set) → Tr X → Tr X → Set
Depth R t t′ = ∀ n → pre n t ≈⟨ ObsR R ⟩ pre n t′

------------------------------------------------------------------------
-- From agreement at every depth to weak bisimilarity
------------------------------------------------------------------------

-- What depth one shows of a next step.
FirstIs : ∀ {X} → End X ⊎ (Event × Tr X) → Obs X → Set
FirstIs (inj₁ e)       o′ = o′ ≡ ([] , just e)
FirstIs (inj₂ (v , _)) o′ = o′ ≡ (v ∷ [] , nothing)

private
  nowInv : ∀ {A : Set} {a b : A} → nowD a ⇓ b → a ≡ b
  nowInv (now⇓ refl) = refl

  ∷-inj : ∀ {v v′ : Event} {l l′} → _≡_ {A = List Event} (v ∷ l) (v′ ∷ l′) → v ≡ v′ × l ≡ l′
  ∷-inj refl = refl , refl

firstOf : ∀ {X} (t : Tr X) {o} → pre 1 t ⇓ o → ∃[ s ] (next t ⇓ s × FirstIs s o)
firstOf {X} t o⇓ = go (bind⇓⁻ (next t) (preStep 0) o⇓)
  where
    at : ∀ {o} (s : End X ⊎ (Event × Tr X)) → preStep 0 s ⇓ o → FirstIs s o
    at (inj₁ e)       p = sym (nowInv p)
    at (inj₂ (v , t₁)) p = lift (bind⇓⁻ (nowD ([] , nothing)) _ p)
      where lift : ∀ {o} → ∃[ o₀ ] (nowD ([] , nothing) ⇓ o₀ × nowD (v ∷ proj₁ o₀ , proj₂ o₀) ⇓ o) → o ≡ (v ∷ [] , nothing)
            lift (o₀ , p₀ , p₁) = trans (sym (nowInv p₁)) (cong (λ o₁ → v ∷ proj₁ o₁ , proj₂ o₁) (sym (nowInv p₀)))
    go : ∀ {o} → ∃[ s ] (next t ⇓ s × preStep 0 s ⇓ o) → ∃[ s ] (next t ⇓ s × FirstIs s o)
    go (s , a , p) = s , a , at s p

seeFirst : ∀ {X} {t : Tr X} (s : End X ⊎ (Event × Tr X)) → next t ⇓ s → ∃[ o ] (pre 1 t ⇓ o × FirstIs s o)
seeFirst (inj₁ e)        a = _ , bind⇓ a (now⇓ refl) , refl
seeFirst (inj₂ (v , t₁)) a = _ , bind⇓ a (bind⇓ (now⇓ refl) (now⇓ refl)) , refl

-- A call's rest, observed one call shallower.
deeper : ∀ {X} {t : Tr X} {v t₁ n o} → next t ⇓ inj₂ (v , t₁) → pre n t₁ ⇓ o → pre (suc n) t ⇓ (v ∷ proj₁ o , proj₂ o)
deeper a o⇓ = bind⇓ a (bind⇓ o⇓ (now⇓ refl))

shallower : ∀ {X} {t : Tr X} {v t₁ n o′} → next t ⇓ inj₂ (v , t₁) → pre (suc n) t ⇓ o′
          → ∃[ o ] (pre n t₁ ⇓ o × o′ ≡ (v ∷ proj₁ o , proj₂ o))
shallower {X} {t} {v} {t₁} {n} a o′⇓ = go (bind⇓⁻ (next t) (preStep n) o′⇓)
  where
    inner : ∀ {o′} → ∃[ o ] (pre n t₁ ⇓ o × nowD (v ∷ proj₁ o , proj₂ o) ⇓ o′) → ∃[ o ] (pre n t₁ ⇓ o × o′ ≡ (v ∷ proj₁ o , proj₂ o))
    inner (o , o⇓ , n⇓) = o , o⇓ , sym (nowInv n⇓)
    same : ∀ {s o′} → inj₂ (v , t₁) ≡ s → preStep n s ⇓ o′ → ∃[ o ] (pre n t₁ ⇓ o × o′ ≡ (v ∷ proj₁ o , proj₂ o))
    same refl p = inner (bind⇓⁻ (pre n t₁) _ p)
    go : ∀ {o′} → ∃[ s ] (next t ⇓ s × preStep n s ⇓ o′) → ∃[ o ] (pre n t₁ ⇓ o × o′ ≡ (v ∷ proj₁ o , proj₂ o))
    go (s , a′ , p) = same (⇓-det a a′) p

------------------------------------------------------------------------
-- Symmetry of the relations
------------------------------------------------------------------------

flipR : ∀ {X : Set} → (X → X → Set) → X → X → Set
flipR R x y = R y x

EndRel-flip : ∀ {X} {R : X → X → Set} {e e′} → EndRel R e e′ → EndRel (flipR R) e′ e
EndRel-flip (returned≈ r) = returned≈ r
EndRel-flip halted≈ = halted≈

MaybeEnd-flip : ∀ {X} {R : X → X → Set} {e e′} → MaybeEnd R e e′ → MaybeEnd (flipR R) e′ e
MaybeEnd-flip cut≈ = cut≈
MaybeEnd-flip (end≈ r) = end≈ (EndRel-flip r)

ObsR-flip : ∀ {X} {R : X → X → Set} {o o′} → ObsR R o o′ → ObsR (flipR R) o′ o
ObsR-flip (eq , me) = sym eq , MaybeEnd-flip me

Depth-sym : ∀ {X} {R : X → X → Set} {t t′ : Tr X} → Depth R t t′ → Depth (flipR R) t′ t
Depth-sym {R = R} {t} {t′} p n = (λ o o⇓ → turn₁ (proj₂ (p n) o o⇓)) , (λ o o⇓ → turn₂ (proj₁ (p n) o o⇓))
  where
    turn₁ : ∀ {o} → ∃[ o₁ ] (pre n t ⇓ o₁ × ObsR R o₁ o) → ∃[ o₁ ] (pre n t ⇓ o₁ × ObsR (flipR R) o o₁)
    turn₁ (o₁ , a , r) = o₁ , a , ObsR-flip r
    turn₂ : ∀ {o} → ∃[ o₁ ] (pre n t′ ⇓ o₁ × ObsR R o o₁) → ∃[ o₁ ] (pre n t′ ⇓ o₁ × ObsR (flipR R) o₁ o)
    turn₂ (o₁ , a , r) = o₁ , a , ObsR-flip r

------------------------------------------------------------------------
-- Agreement at every depth gives weak bisimilarity
------------------------------------------------------------------------

private
  []≢∷ : ∀ {v : Event} {l} → _≡_ {A = List Event} [] (v ∷ l) → ⊥
  []≢∷ ()

-- After the same call on both sides, the rests agree at every depth.
restDepth : ∀ {X} {R : X → X → Set} {t t′ : Tr X} {v t₁ t₁′} → Depth R t t′ → next t ⇓ inj₂ (v , t₁) → next t′ ⇓ inj₂ (v , t₁′)
          → Depth R t₁ t₁′
restDepth {X} {R} {t} {t′} {v} {t₁} {t₁′} p a a′ n = fw , bw
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
endMatch : ∀ {X} {R : X → X → Set} {t t′ : Tr X} {e} → Depth R t t′ → next t ⇓ inj₁ e
         → ∃[ e′ ] (next t′ ⇓ inj₁ e′ × EndRel R e e′)
endMatch {X} {R} {t} {t′} {e} p a = one (seeFirst {t = t} (inj₁ e) a)
  where
    decide : ∀ {o′} (s′ : End X ⊎ (Event × Tr X)) → next t′ ⇓ s′ → FirstIs s′ o′ → ObsR R ([] , just e) o′
           → ∃[ e′ ] (next t′ ⇓ inj₁ e′ × EndRel R e e′)
    decide (inj₁ e′)       a′ refl (_ , end≈ r) = e′ , a′ , r
    decide (inj₂ (v , _))  a′ refl (eq , _)     = ⊥-elim ([]≢∷ eq)
    two : ∃[ o′ ] (pre 1 t′ ⇓ o′ × ObsR R ([] , just e) o′) → ∃[ e′ ] (next t′ ⇓ inj₁ e′ × EndRel R e e′)
    two (o′ , o′⇓ , r) = three (firstOf t′ o′⇓)
      where three : ∃[ s′ ] (next t′ ⇓ s′ × FirstIs s′ o′) → ∃[ e′ ] (next t′ ⇓ inj₁ e′ × EndRel R e e′)
            three (s′ , a′ , fi) = decide s′ a′ fi r
    one : ∃[ o ] (pre 1 t ⇓ o × FirstIs (inj₁ e) o) → ∃[ e′ ] (next t′ ⇓ inj₁ e′ × EndRel R e e′)
    one (o , o⇓ , refl) = two (proj₁ (p 1) _ o⇓)

-- A call on one side: the same call on the other, the rests agreeing.
emitMatch : ∀ {X} {R : X → X → Set} {t t′ : Tr X} {v t₁} → Depth R t t′ → next t ⇓ inj₂ (v , t₁)
          → ∃[ t₁′ ] (next t′ ⇓ inj₂ (v , t₁′) × Depth R t₁ t₁′)
emitMatch {X} {R} {t} {t′} {v} {t₁} p a = one (seeFirst {t = t} (inj₂ (v , t₁)) a)
  where
    decide : ∀ {o′} (s′ : End X ⊎ (Event × Tr X)) → next t′ ⇓ s′ → FirstIs s′ o′ → ObsR R (v ∷ [] , nothing) o′
           → ∃[ t₁′ ] (next t′ ⇓ inj₂ (v , t₁′) × Depth R t₁ t₁′)
    decide (inj₁ e′)        a′ refl (eq , _) = ⊥-elim ([]≢∷ (sym eq))
    decide (inj₂ (v′ , t₁′)) a′ refl (eq , _) = fin (proj₁ (∷-inj eq)) a′
      where fin : v ≡ v′ → next t′ ⇓ inj₂ (v′ , t₁′) → ∃[ t₁″ ] (next t′ ⇓ inj₂ (v , t₁″) × Depth R t₁ t₁″)
            fin refl a″ = t₁′ , a″ , restDepth {t = t} {t′} p a a″
    two : ∃[ o′ ] (pre 1 t′ ⇓ o′ × ObsR R (v ∷ [] , nothing) o′) → ∃[ t₁′ ] (next t′ ⇓ inj₂ (v , t₁′) × Depth R t₁ t₁′)
    two (o′ , o′⇓ , r) = three (firstOf t′ o′⇓)
      where three : ∃[ s′ ] (next t′ ⇓ s′ × FirstIs s′ o′) → ∃[ t₁′ ] (next t′ ⇓ inj₂ (v , t₁′) × Depth R t₁ t₁′)
            three (s′ , a′ , fi) = decide s′ a′ fi r
    one : ∃[ o ] (pre 1 t ⇓ o × FirstIs (inj₂ (v , t₁)) o) → ∃[ t₁′ ] (next t′ ⇓ inj₂ (v , t₁′) × Depth R t₁ t₁′)
    one (o , o⇓ , refl) = two (proj₁ (p 1) _ o⇓)

-- THE CRUX: corecursively, the matched rests are weakly bisimilar. The
-- corecursive call sits directly under the pair constructors.
fromDepth : ∀ {X} {R : X → X → Set} {t t′ : Tr X} → Depth R t t′ → WB R t t′
fwd (fromDepth p) (inj₁ e) a = inj₁ (proj₁ (endMatch p a)) , proj₁ (proj₂ (endMatch p a)) , proj₂ (proj₂ (endMatch p a))
fwd (fromDepth p) (inj₂ (v , t₁)) a =
  inj₂ (v , proj₁ (emitMatch p a)) , proj₁ (proj₂ (emitMatch p a)) , refl , fromDepth (proj₂ (proj₂ (emitMatch p a)))
bwd (fromDepth p) (inj₁ e′) a′ =
  inj₁ (proj₁ (endMatch (Depth-sym p) a′)) , proj₁ (proj₂ (endMatch (Depth-sym p) a′)) , unflip (proj₂ (proj₂ (endMatch (Depth-sym p) a′)))
  where unflip : ∀ {X} {R : X → X → Set} {e e′} → EndRel (flipR R) e′ e → EndRel R e e′
        unflip (returned≈ r) = returned≈ r
        unflip halted≈ = halted≈
bwd (fromDepth p) (inj₂ (v , t₁′)) a′ =
  inj₂ (v , proj₁ (emitMatch (Depth-sym p) a′)) , proj₁ (proj₂ (emitMatch (Depth-sym p) a′)) , refl
  , fromDepth (Depth-sym (proj₂ (proj₂ (emitMatch (Depth-sym p) a′))))

------------------------------------------------------------------------
-- Weak bisimilarity gives agreement at every depth
------------------------------------------------------------------------

toDepth : ∀ {X} {R : X → X → Set} {t t′ : Tr X} → WB R t t′ → Depth R t t′
toDepth {X} {R} {t} {t′} w zero = (λ o o⇓ → base o⇓) , (λ o o⇓ → base′ o⇓)
  where
    base : ∀ {o} → nowD ([] , nothing) ⇓ o → ∃[ o′ ] (pre zero t′ ⇓ o′ × ObsR R o o′)
    base p with nowInv p
    ... | refl = _ , now⇓ refl , refl , cut≈
    base′ : ∀ {o} → nowD ([] , nothing) ⇓ o → ∃[ o′ ] (pre zero t ⇓ o′ × ObsR R o′ o)
    base′ p with nowInv p
    ... | refl = _ , now⇓ refl , refl , cut≈
toDepth {X} {R} {t} {t′} w (suc n) = fw , bw
  where
    fw : ∀ o → pre (suc n) t ⇓ o → ∃[ o′ ] (pre (suc n) t′ ⇓ o′ × ObsR R o o′)
    fw o o⇓ = split (bind⇓⁻ (next t) (preStep n) o⇓)
      where
        both : ∀ s → preStep n s ⇓ o → ∀ s′ → next t′ ⇓ s′ → StepR R (WB R) s s′ → ∃[ o′ ] (pre (suc n) t′ ⇓ o′ × ObsR R o o′)
        both (inj₁ e) p (inj₁ e′) a′ r with nowInv p
        ... | refl = _ , bind⇓ a′ (now⇓ refl) , refl , end≈ r
        both (inj₂ (v , t₁)) p (inj₂ (.v , t₁′)) a′ (refl , w₁) = rest (bind⇓⁻ (pre n t₁) _ p)
          where rest : ∃[ o₁ ] (pre n t₁ ⇓ o₁ × nowD (v ∷ proj₁ o₁ , proj₂ o₁) ⇓ o) → ∃[ o′ ] (pre (suc n) t′ ⇓ o′ × ObsR R o o′)
                rest (o₁ , o₁⇓ , q) with nowInv q | proj₁ (toDepth w₁ n) o₁ o₁⇓
                ... | refl | (o₁′ , o₁′⇓ , eq , me) = _ , deeper {t = t′} a′ o₁′⇓ , cong (v ∷_) eq , me
        both (inj₁ _) p (inj₂ _) a′ ()
        both (inj₂ _) p (inj₁ _) a′ ()
        split : ∃[ s ] (next t ⇓ s × preStep n s ⇓ o) → ∃[ o′ ] (pre (suc n) t′ ⇓ o′ × ObsR R o o′)
        split (s , a , p) with fwd w s a
        ... | (s′ , a′ , r) = both s p s′ a′ r
    bw : ∀ o′ → pre (suc n) t′ ⇓ o′ → ∃[ o ] (pre (suc n) t ⇓ o × ObsR R o o′)
    bw o′ o′⇓ = split (bind⇓⁻ (next t′) (preStep n) o′⇓)
      where
        both : ∀ s′ → preStep n s′ ⇓ o′ → ∀ s → next t ⇓ s → StepR R (WB R) s s′ → ∃[ o ] (pre (suc n) t ⇓ o × ObsR R o o′)
        both (inj₁ e′) p (inj₁ e) a r with nowInv p
        ... | refl = _ , bind⇓ a (now⇓ refl) , refl , end≈ r
        both (inj₂ (v , t₁′)) p (inj₂ (.v , t₁)) a (refl , w₁) = rest (bind⇓⁻ (pre n t₁′) _ p)
          where rest : ∃[ o₁ ] (pre n t₁′ ⇓ o₁ × nowD (v ∷ proj₁ o₁ , proj₂ o₁) ⇓ o′) → ∃[ o ] (pre (suc n) t ⇓ o × ObsR R o o′)
                rest (o₁ , o₁⇓ , q) with nowInv q | proj₂ (toDepth w₁ n) o₁ o₁⇓
                ... | refl | (o₀ , o₀⇓ , eq , me) = _ , deeper {t = t} a o₀⇓ , cong (v ∷_) eq , me
        both (inj₁ _) p (inj₂ _) a ()
        both (inj₂ _) p (inj₁ _) a ()
        split : ∃[ s′ ] (next t′ ⇓ s′ × preStep n s′ ⇓ o′) → ∃[ o ] (pre (suc n) t ⇓ o × ObsR R o o′)
        split (s′ , a′ , p) with bwd w s′ a′
        ... | (s , a , r) = both s′ p s a r

------------------------------------------------------------------------
-- Transitivity, corecursively
------------------------------------------------------------------------

module _ {X : Set} {R : X → X → Set} (R-trans : ∀ {x y z} → R x y → R y z → R x z) where
  private
    endT : ∀ {e₁ e₂ e₃} → EndRel R e₁ e₂ → EndRel R e₂ e₃ → EndRel R e₁ e₃
    endT (returned≈ r) (returned≈ r′) = returned≈ (R-trans r r′)
    endT halted≈ halted≈ = halted≈

    -- The other side's step, read as the same kind of step.
    endN : ∀ {d : Delay (End X ⊎ (Event × Tr X))} {S e} → ∃[ o′ ] (d ⇓ o′ × StepR R S (inj₁ e) o′) → ∃[ e′ ] (d ⇓ inj₁ e′ × EndRel R e e′)
    endN (inj₁ e′ , a , r) = e′ , a , r
    endN (inj₂ _ , a , ())
    endN′ : ∀ {d : Delay (End X ⊎ (Event × Tr X))} {S e′} → ∃[ o ] (d ⇓ o × StepR R S o (inj₁ e′)) → ∃[ e ] (d ⇓ inj₁ e × EndRel R e e′)
    endN′ (inj₁ e , a , r) = e , a , r
    endN′ (inj₂ _ , a , ())
    emitN : ∀ {d : Delay (End X ⊎ (Event × Tr X))} {S : Tr X → Tr X → Set} {v t₁} → ∃[ o′ ] (d ⇓ o′ × StepR R S (inj₂ (v , t₁)) o′)
          → ∃[ t₁′ ] (d ⇓ inj₂ (v , t₁′) × S t₁ t₁′)
    emitN (inj₁ _ , a , ())
    emitN (inj₂ (v , t₁′) , a , refl , s) = t₁′ , a , s
    emitN′ : ∀ {d : Delay (End X ⊎ (Event × Tr X))} {S : Tr X → Tr X → Set} {v t₁′} → ∃[ o ] (d ⇓ o × StepR R S o (inj₂ (v , t₁′)))
           → ∃[ t₁ ] (d ⇓ inj₂ (v , t₁) × S t₁ t₁′)
    emitN′ (inj₁ _ , a , ())
    emitN′ (inj₂ (v , t₁) , a , refl , s) = t₁ , a , s

  WB-trans : ∀ {t₁ t₂ t₃ : Tr X} → WB R t₁ t₂ → WB R t₂ t₃ → WB R t₁ t₃
  fwd (WB-trans p q) (inj₁ e) a =
    inj₁ (proj₁ E₂) , proj₁ (proj₂ E₂) , endT (proj₂ (proj₂ E₁)) (proj₂ (proj₂ E₂))
    where E₁ = endN (fwd p (inj₁ e) a)
          E₂ = endN (fwd q (inj₁ (proj₁ E₁)) (proj₁ (proj₂ E₁)))
  fwd (WB-trans p q) (inj₂ (v , u)) a =
    inj₂ (v , proj₁ M₂) , proj₁ (proj₂ M₂) , refl , WB-trans (proj₂ (proj₂ M₁)) (proj₂ (proj₂ M₂))
    where M₁ = emitN (fwd p (inj₂ (v , u)) a)
          M₂ = emitN (fwd q (inj₂ (v , proj₁ M₁)) (proj₁ (proj₂ M₁)))
  bwd (WB-trans p q) (inj₁ e) a =
    inj₁ (proj₁ E₁) , proj₁ (proj₂ E₁) , endT (proj₂ (proj₂ E₁)) (proj₂ (proj₂ E₂))
    where E₂ = endN′ (bwd q (inj₁ e) a)
          E₁ = endN′ (bwd p (inj₁ (proj₁ E₂)) (proj₁ (proj₂ E₂)))
  bwd (WB-trans p q) (inj₂ (v , u)) a =
    inj₂ (v , proj₁ M₁) , proj₁ (proj₂ M₁) , refl , WB-trans (proj₂ (proj₂ M₁)) (proj₂ (proj₂ M₂))
    where M₂ = emitN′ (bwd q (inj₂ (v , u)) a)
          M₁ = emitN′ (bwd p (inj₂ (v , proj₁ M₂)) (proj₁ (proj₂ M₂)))
