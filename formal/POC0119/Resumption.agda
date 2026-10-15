{-# OPTIONS --safe #-}
------------------------------------------------------------------------
-- POC (plan 0.119 §6 steps 1–2): T∞ X = νY. T (X + Y), the coinductive
-- resumption monad over the finite free monad T, and its observation into
-- the delay monad.
------------------------------------------------------------------------

open import Once.Spec.Signature using (Signature; Layer; call; Op; Event; eventOf)

module POC0119.Resumption (Σ : Signature) where

open import Data.List using (List; []; _∷_; _++_; [_])
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Once.Spec.Signature using (module Op)
open Op using (ans)
open import Once.Spec.Effect Σ using (Step; done; node; T; roll; returnT; _>>=T_)
open import Once.Spec.Observation Σ using (Interp; module Interp; History; resume)
open Interp using (answer)

------------------------------------------------------------------------
-- Blocks forever
------------------------------------------------------------------------

record T∞ (X : Set) : Set where
  coinductive
  field force : T (X ⊎ T∞ X)
open T∞

mapT : ∀ {X Y} → (X → Y) → T X → T Y
mapT f m = m >>=T λ x → returnT (f x)

return∞ : ∀ {X} → X → T∞ X
force (return∞ x) = returnT (inj₁ x)

-- bind: walk the first block; at its result splice in the continuation's
-- first block; at a boundary continue corecursively.
_>>=∞_    : ∀ {X Y} → T∞ X → (X → T∞ Y) → T∞ Y
bindBlock : ∀ {X Y} → T (X ⊎ T∞ X) → (X → T∞ Y) → T (Y ⊎ T∞ Y)
force (m >>=∞ f) = bindBlock (force m) f
bindBlock (roll (done (inj₁ x)))     f = force (f x)
bindBlock (roll (done (inj₂ m)))     f = roll (done (inj₂ (m >>=∞ f)))
bindBlock (roll (node (call o a k))) f = roll (node (call o a (λ b → bindBlock (k b) f)))

-- The lifts Id ⇒ T ⇒ T∞.
liftT : ∀ {X} → T X → T∞ X
force (liftT m) = mapT inj₁ m

-- Coherence, first instance: Id ⇒ T ⇒ T∞ is Id ⇒ T∞ (on the nose).
lift-coh : ∀ {X} (x : X) → force (liftT (returnT x)) ≡ force (return∞ x)
lift-coh x = refl

-- The loop: the plain anamorphism of νY. T (B + Y) — any coalgebra.
unfold    : ∀ {A B : Set} → (A → T (B ⊎ A)) → A → T∞ B
loopBlock : ∀ {A B : Set} → (A → T (B ⊎ A)) → T (B ⊎ A) → T (B ⊎ T∞ B)
force (unfold c a) = loopBlock c (c a)
loopBlock c (roll (done (inj₁ b)))     = returnT (inj₁ b)
loopBlock c (roll (done (inj₂ a)))     = roll (done (inj₂ (unfold c a)))
loopBlock c (roll (node (call o x k))) = roll (node (call o x (λ r → loopBlock c (k r))))

------------------------------------------------------------------------
-- Observation into the delay monad
------------------------------------------------------------------------

record Delay (A : Set) : Set where
  coinductive
  field step : A ⊎ Delay A
open Delay

data _⇓_ {A : Set} (d : Delay A) (a : A) : Set where
  now⇓   : step d ≡ inj₁ a → d ⇓ a
  later⇓ : ∀ {d′} → step d ≡ inj₂ d′ → d′ ⇓ a → d ⇓ a

-- Both arrive at the same value, or neither ever arrives.
_≈D_ : ∀ {A} → Delay A → Delay A → Set
d ≈D d′ = ∀ a → (d ⇓ a → d′ ⇓ a) × (d′ ⇓ a → d ⇓ a)

-- The first n events after the history h; a block boundary is one delay step.
module _ (ι : Interp) where
  events    : ∀ {X} → History → T∞ X → ℕ → Delay History
  blockStep : ∀ {X} → History → T (X ⊎ T∞ X) → ℕ → History ⊎ Delay History
  continue  : ∀ {X} → History → Maybe (T (X ⊎ T∞ X)) → ℕ → History ⊎ Delay History
  step (events h m n) = blockStep h (force m) n
  blockStep h _                          zero    = inj₁ h
  blockStep h (roll (done (inj₁ x)))     (suc n) = inj₁ h
  blockStep h (roll (done (inj₂ m)))     (suc n) = inj₂ (events h m (suc n))
  blockStep h (roll (node (call o a k))) (suc n) =
    continue (h ++ [ eventOf o a ]) (resume (ans o) (answer ι o h a) k) n
  continue h nothing  n = inj₁ h
  continue h (just t) n = blockStep h t n

  behaviour : ∀ {X} → T∞ X → ℕ → Delay History
  behaviour m n = events [] m n

------------------------------------------------------------------------
-- Step 2: the n-th observation has at most n events (PrefixFamily.bounded)
------------------------------------------------------------------------

open import Data.List using (length)
open import Data.List.Properties using (length-++)
open import Data.Nat using (_≤_; _+_)
open import Data.Nat.Properties using (m≤m+n; ≤-refl; ≤-trans; ≤-reflexive; +-assoc)
open import Data.Product using (Σ-syntax; ∃-syntax)
open import Relation.Binary.PropositionalEquality using (sym; trans; cong)

module Bound (ι : Interp) where
  private
    ev = events ι
    bs = blockStep ι
    ct = continue ι

  grow : ∀ (h : History) e n → length (h ++ [ e ]) + n ≡ length h + suc n
  grow h e n = trans (cong (_+ n) (length-++ h)) (+-assoc (length h) 1 n)

  block₁ : ∀ {X} h (t : T (X ⊎ T∞ X)) n h′ → bs h t n ≡ inj₁ h′ → length h′ ≤ length h + n
  cont₁  : ∀ {X} h (mt : Maybe (T (X ⊎ T∞ X))) n h′ → ct h mt n ≡ inj₁ h′ → length h′ ≤ length h + n
  block₁ h t                          zero    .h refl = m≤m+n _ _
  block₁ h (roll (done (inj₁ x)))     (suc n) .h refl = m≤m+n _ _
  block₁ h (roll (done (inj₂ m)))     (suc n) h′ ()
  block₁ h (roll (node (call o a k))) (suc n) h′ eq =
    ≤-trans (cont₁ (h ++ [ eventOf o a ]) (resume (ans o) (answer ι o h a) k) n h′ eq) (≤-reflexive (grow h (eventOf o a) n))
  cont₁ h nothing  n .h refl = m≤m+n _ _
  cont₁ h (just t) n h′ eq   = block₁ h t n h′ eq

  Next : ∀ {X} → History → ℕ → Delay History → Set
  Next {X} h n d = ∃[ h″ ] ∃[ m ] ∃[ n′ ] (d ≡ ev {X} h″ m n′ × length h″ + n′ ≤ length h + n)

  block₂ : ∀ {X} h (t : T (X ⊎ T∞ X)) n d → bs h t n ≡ inj₂ d → Next {X} h n d
  cont₂  : ∀ {X} h (mt : Maybe (T (X ⊎ T∞ X))) n d → ct h mt n ≡ inj₂ d → Next {X} h n d
  block₂ h t                          zero    d ()
  block₂ h (roll (done (inj₁ x)))     (suc n) d ()
  block₂ h (roll (done (inj₂ m)))     (suc n) d refl = h , m , suc n , refl , ≤-refl
  block₂ h (roll (node (call o a k))) (suc n) d eq with cont₂ (h ++ [ eventOf o a ]) (resume (ans o) (answer ι o h a) k) n d eq
  ... | h″ , m , n′ , e , le = h″ , m , n′ , e , ≤-trans le (≤-reflexive (grow h (eventOf o a) n))
  cont₂ h nothing  n d ()
  cont₂ h (just t) n d eq = block₂ h t n d eq

  bound  : ∀ {X} h (m : T∞ X) n h′ → ev h m n ⇓ h′ → length h′ ≤ length h + n
  bound′ : ∀ {X} h n h′ {d} → Next {X} h n d → d ⇓ h′ → length h′ ≤ length h + n
  bound h m n h′ (now⇓ eq)      = block₁ h (force m) n h′ eq
  bound h m n h′ (later⇓ eq d⇓) = bound′ h n h′ (block₂ h (force m) n _ eq) d⇓
  bound′ h n h′ (h″ , m , n′ , refl , le) d⇓ = ≤-trans (bound h″ m n′ h′ d⇓) le

  bounded : ∀ {X} (m : T∞ X) n tr → behaviour ι m n ⇓ tr → length tr ≤ n
  bounded m n tr d⇓ = bound [] m n tr d⇓

------------------------------------------------------------------------
-- Step 2: observing one event further only extends (PrefixFamily.coherent)
------------------------------------------------------------------------

open import Data.List.Properties using (++-assoc; ++-identityʳ)

Prefix : History → History → Set
Prefix u t = ∃[ rest ] (t ≡ u ++ rest)

prefix-refl : ∀ u → Prefix u u
prefix-refl u = [] , sym (++-identityʳ u)

prefix-trans : ∀ {u v w} → Prefix u v → Prefix v w → Prefix u w
prefix-trans {u} (r₁ , refl) (r₂ , refl) = r₁ ++ r₂ , ++-assoc u r₁ r₂

module Coh (ι : Interp) where
  private
    ev = events ι
    bs = blockStep ι
    ct = continue ι

  -- Where a block step leads always extends the history it started from.
  data Ext {X} (h : History) : History ⊎ Delay History → Set where
    e₁ : ∀ {t} → Prefix h t → Ext h (inj₁ t)
    e₂ : ∀ {h″ m k} → Prefix h h″ → Ext h (inj₂ (ev {X} h″ m k))

  weaken : ∀ {X h e r} → Ext {X} (h ++ [ e ]) r → Ext {X} h r
  weaken {h = h} {e} (e₁ p) = e₁ (prefix-trans ([ e ] , refl) p)
  weaken {h = h} {e} (e₂ p) = e₂ (prefix-trans ([ e ] , refl) p)

  extB : ∀ {X} h (t : T (X ⊎ T∞ X)) n → Ext {X} h (bs h t n)
  extC : ∀ {X} h (mt : Maybe (T (X ⊎ T∞ X))) n → Ext {X} h (ct h mt n)
  extB h t                          zero    = e₁ (prefix-refl h)
  extB h (roll (done (inj₁ x)))     (suc n) = e₁ (prefix-refl h)
  extB h (roll (done (inj₂ m)))     (suc n) = e₂ (prefix-refl h)
  extB h (roll (node (call o a k))) (suc n) =
    weaken (extC (h ++ [ eventOf o a ]) (resume (ans o) (answer ι o h a) k) n)
  extC h nothing  n = e₁ (prefix-refl h)
  extC h (just t) n = extB h t n

  ext  : ∀ {X} h (m : T∞ X) n t → ev h m n ⇓ t → Prefix h t
  ext₁ : ∀ {X h r t} → Ext {X} h r → r ≡ inj₁ t → Prefix h t
  ext₂ : ∀ {X h r d t} → Ext {X} h r → r ≡ inj₂ d → d ⇓ t → Prefix h t
  ext h m n t (now⇓ eq) = ext₁ (extB h (force m) n) eq
  ext h m n t (later⇓ eq d⇓) = ext₂ (extB h (force m) n) eq d⇓
  ext₁ (e₁ p) refl = p
  ext₂ (e₂ {h″} {m} {k} p) refl d⇓ = prefix-trans p (ext h″ m k _ d⇓)

  -- One block step at n+1 against the same step at n.
  data CohB {X} : History ⊎ Delay History → History ⊎ Delay History → Set where
    stop  : ∀ {t u} → Prefix u t → CohB (inj₁ t) (inj₁ u)
    early : ∀ {u h″ m k} → Prefix u h″ → CohB (inj₂ (ev {X} h″ m k)) (inj₁ u)
    same  : ∀ {h″ m k} → CohB (inj₂ (ev {X} h″ m (suc k))) (inj₂ (ev {X} h″ m k))

  toCoh : ∀ {X h r} → Ext {X} h r → CohB {X} r (inj₁ h)
  toCoh (e₁ p) = stop p
  toCoh (e₂ p) = early p

  cohB : ∀ {X} h (t : T (X ⊎ T∞ X)) n → CohB {X} (bs h t (suc n)) (bs h t n)
  cohC : ∀ {X} h (mt : Maybe (T (X ⊎ T∞ X))) n → CohB {X} (ct h mt (suc n)) (ct h mt n)
  cohB h t                          zero    = toCoh (extB h t 1)
  cohB h (roll (done (inj₁ x)))     (suc n) = stop (prefix-refl h)
  cohB h (roll (done (inj₂ m)))     (suc n) = same
  cohB h (roll (node (call o a k))) (suc n) =
    cohC (h ++ [ eventOf o a ]) (resume (ans o) (answer ι o h a) k) n
  cohC h nothing  n = stop (prefix-refl h)
  cohC h (just t) n = cohB h t n

  data Conv (t : History) : History ⊎ Delay History → Set where
    c₁ : Conv t (inj₁ t)
    c₂ : ∀ {d} → d ⇓ t → Conv t (inj₂ d)

  fromConv : ∀ {d r t} → step d ≡ r → Conv t r → d ⇓ t
  fromConv eq c₁      = now⇓ eq
  fromConv eq (c₂ d⇓) = later⇓ eq d⇓

  coh     : ∀ {X} h (m : T∞ X) n t′ → ev h m (suc n) ⇓ t′ → ∃[ t ] (Conv t (bs h (force m) n) × Prefix t t′)
  goNow   : ∀ {X r s t′} → CohB {X} r s → r ≡ inj₁ t′ → ∃[ t ] (Conv t s × Prefix t t′)
  goLater : ∀ {X r s d t′} → CohB {X} r s → r ≡ inj₂ d → d ⇓ t′ → ∃[ t ] (Conv t s × Prefix t t′)
  coh h m n t′ (now⇓ eq)      = goNow (cohB h (force m) n) eq
  coh h m n t′ (later⇓ eq d⇓) = goLater (cohB h (force m) n) eq d⇓
  goNow (stop {u = u} p) refl = u , c₁ , p
  goLater (early {u = u} {h″} {m} {k} p) refl d⇓ = u , c₁ , prefix-trans p (ext h″ m k _ d⇓)
  goLater (same {h″} {m} {k}) refl d⇓ with coh h″ m k _ d⇓
  ... | t , cv , p = t , c₂ (fromConv refl cv) , p

  coherent : ∀ {X} (m : T∞ X) n t′ → behaviour ι m (suc n) ⇓ t′ → ∃[ t ] (behaviour ι m n ⇓ t × Prefix t t′)
  coherent m n t′ d⇓ with coh [] m n t′ d⇓
  ... | t , cv , p = t , fromConv refl cv , p
