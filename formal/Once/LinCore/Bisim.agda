-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.LinCore.Bisim — BISIMILARITY of computations (plan 0.146 A15).
--
--   * `_≈_`: the same blocks, step for step, for every answer of the world,
--     ending in the same value (a loop's meaning is coinductive, so `≡` would
--     not do);
--   * `_≈[_]_`: the same, ending in values RELATED by `R`. A computation
--     that returns a function or a ν cannot be compared by `≡` without
--     function extensionality; A15 part 2 relates them by a logical relation
--     (`Pass.V`: arrows pointwise, a ν by bisimulation);
--   * `TR`: the same, for one finite block (`T`, the Spec's `M act`).
------------------------------------------------------------------------

{-# OPTIONS --guardedness #-}

open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (sym; subst)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Data.Product using (_×_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Sum.Relation.Binary.Pointwise using (Pointwise)
  renaming (inj₁ to ⊎₁; inj₂ to ⊎₂)
open import Once.Spec.Numerics using (TargetNum)
open import Once.IR.Semantics.Trace using (FFIAnswers)
open import Once.LinCore.Flat using (Base; FTy)

module Once.LinCore.Bisim
  (fmt : TargetNum) (ans : FFIAnswers)
  where

open import Once.LinCore.NbEPLinCore fmt ans

------------------------------------------------------------------------
-- 1. BISIMILARITY: the same blocks, step for step, for every answer of the
-- world.
------------------------------------------------------------------------

infix 4 _≈_
mutual
  record _≈_ {X : Set} (m m′ : T∞ X) : Set where
    coinductive
    field block≈ : Bl (block m) (block m′)

  data Bl {X : Set} : T (X ⊎ T∞ X) → T (X ⊎ T∞ X) → Set where
    ≈ret  : ∀ {x} → Bl (ret (inj₁ x)) (ret (inj₁ x))
    ≈step : ∀ {m m′} → m ≈ m′ → Bl (ret (inj₂ m)) (ret (inj₂ m′))
    ≈call : ∀ {s x k k′} → (∀ y → Bl (k y) (k′ y)) → Bl (call s x k) (call s x k′)
    ≈halt : ∀ {s x} → Bl (halt s x) (halt s x)
open _≈_ public

mutual
  ≈-refl : ∀ {X} {m : T∞ X} → m ≈ m
  block≈ (≈-refl {m = m}) = Bl-refl (block m)

  Bl-refl : ∀ {X} (b : T (X ⊎ T∞ X)) → Bl b b
  Bl-refl (ret (inj₁ x)) = ≈ret
  Bl-refl (ret (inj₂ m)) = ≈step ≈-refl
  Bl-refl (call s x k)   = ≈call (λ y → Bl-refl (k y))
  Bl-refl (halt s x)     = ≈halt

mutual
  ≈-sym : ∀ {X} {m m′ : T∞ X} → m ≈ m′ → m′ ≈ m
  block≈ (≈-sym p) = Bl-sym (block≈ p)

  Bl-sym : ∀ {X} {b b′ : T (X ⊎ T∞ X)} → Bl b b′ → Bl b′ b
  Bl-sym ≈ret      = ≈ret
  Bl-sym (≈step p) = ≈step (≈-sym p)
  Bl-sym (≈call f) = ≈call (λ y → Bl-sym (f y))
  Bl-sym ≈halt     = ≈halt

mutual
  ≈-trans : ∀ {X} {m m′ m″ : T∞ X} → m ≈ m′ → m′ ≈ m″ → m ≈ m″
  block≈ (≈-trans p q) = Bl-trans (block≈ p) (block≈ q)

  Bl-trans : ∀ {X} {b b′ b″ : T (X ⊎ T∞ X)} → Bl b b′ → Bl b′ b″ → Bl b b″
  Bl-trans ≈ret      ≈ret      = ≈ret
  Bl-trans (≈step p) (≈step q) = ≈step (≈-trans p q)
  Bl-trans (≈call f) (≈call g) = ≈call (λ y → Bl-trans (f y) (g y))
  Bl-trans ≈halt     ≈halt     = ≈halt

-- two computations with the same first block are bisimilar to the same things
≈-blk : ∀ {X} {m₁ m₂ m′ : T∞ X} → block m₁ ≡ block m₂ → m₂ ≈ m′ → m₁ ≈ m′
block≈ (≈-blk {m′ = m′} e q) = subst (λ b → Bl b (block m′)) (sym e) (block≈ q)

-- BIND respects it (the monad's congruence)
mutual
  >>=-cong : ∀ {X Y} {m m′ : T∞ X} {k k′ : X → T∞ Y} → m ≈ m′ → (∀ x → k x ≈ k′ x) → (m >>=∞ k) ≈ (m′ >>=∞ k′)
  block≈ (>>=-cong p kk) = bind-Bl (block≈ p) kk

  bind-Bl : ∀ {X Y} {b b′ : T (X ⊎ T∞ X)} {k k′ : X → T∞ Y} → Bl b b′ → (∀ x → k x ≈ k′ x)
          → Bl (bindBlock b k) (bindBlock b′ k′)
  bind-Bl (≈ret {x = x}) kk = block≈ (kk x)
  bind-Bl (≈step p)      kk = ≈step (>>=-cong p kk)
  bind-Bl (≈call f)      kk = ≈call (λ y → bind-Bl (f y) kk)
  bind-Bl ≈halt          kk = ≈halt

-- THE LOOP respects it
mutual
  iter-cong : ∀ {A B : Set} {f f′ : A → T∞ (B ⊎ A)} {m m′ : T∞ (B ⊎ A)}
            → (∀ a → f a ≈ f′ a) → m ≈ m′ → iterRun f m ≈ iterRun f′ m′
  block≈ (iter-cong ff p) = iter-Bl ff (block≈ p)

  iter-Bl : ∀ {A B : Set} {f f′ : A → T∞ (B ⊎ A)} {b b′ : T ((B ⊎ A) ⊎ T∞ (B ⊎ A))}
          → (∀ a → f a ≈ f′ a) → Bl b b′ → Bl (iterBlock f b) (iterBlock f′ b′)
  iter-Bl ff (≈ret {x = inj₁ b}) = ≈ret
  iter-Bl ff (≈ret {x = inj₂ a}) = ≈step (iter-cong ff (ff a))
  iter-Bl ff (≈step p)           = ≈step (iter-cong ff p)
  iter-Bl ff (≈call g)           = ≈call (λ y → iter-Bl ff (g y))
  iter-Bl ff ≈halt               = ≈halt

-- pairing a result with a fixed `e`, then dropping it again, is the result
mutual
  pair-drop : ∀ {X Y : Set} {m : T∞ X} (h : X → Y) (k : Y → T∞ X)
            → (∀ x → block (k (h x)) ≡ ret (inj₁ x)) → ((m >>=∞ λ x → return∞ (h x)) >>=∞ k) ≈ m
  block≈ (pair-drop {m = m} h k e) = pair-drop-Bl h k e (block m)

  pair-drop-Bl : ∀ {X Y : Set} (h : X → Y) (k : Y → T∞ X) → (∀ x → block (k (h x)) ≡ ret (inj₁ x))
               → (b : T (X ⊎ T∞ X)) → Bl (bindBlock (bindBlock b (λ x → return∞ (h x))) k) b
  pair-drop-Bl h k e (ret (inj₁ x)) = subst (λ c → Bl c (ret (inj₁ x))) (sym (e x)) ≈ret
  pair-drop-Bl h k e (ret (inj₂ m)) = ≈step (pair-drop h k e)
  pair-drop-Bl h k e (call s x c)   = ≈call (λ y → pair-drop-Bl h k e (c y))
  pair-drop-Bl h k e (halt s x)     = ≈halt

------------------------------------------------------------------------
-- 2. ★ BISIMILARITY UP TO A RELATION on the values returned.
------------------------------------------------------------------------

infix 4 _≈[_]_
mutual
  -- (heterogeneous, B1.3: the core's values against master's)
  record _≈[_]_ {X Y : Set} (m : T∞ X) (R : X → Y → Set) (m′ : T∞ Y) : Set where
    coinductive
    field blockR : BlR R (block m) (block m′)

  data BlR {X Y : Set} (R : X → Y → Set) : T (X ⊎ T∞ X) → T (Y ⊎ T∞ Y) → Set where
    ≈retR  : ∀ {x y} → R x y → BlR R (ret (inj₁ x)) (ret (inj₁ y))
    ≈stepR : ∀ {m m′} → m ≈[ R ] m′ → BlR R (ret (inj₂ m)) (ret (inj₂ m′))
    ≈callR : ∀ {s x k k′} → (∀ y → BlR R (k y) (k′ y)) → BlR R (call s x k) (call s x k′)
    ≈haltR : ∀ {s x} → BlR R (halt s x) (halt s x)
open _≈[_]_ public

ret≈R : ∀ {X Y} {R : X → Y → Set} {x y} → R x y → return∞ x ≈[ R ] return∞ y
blockR (ret≈R r) = ≈retR r

≈R-blk : ∀ {X Y} {R : X → Y → Set} {m₁ m₂ : T∞ X} {m′ : T∞ Y} → block m₁ ≡ block m₂ → m₂ ≈[ R ] m′ → m₁ ≈[ R ] m′
blockR (≈R-blk {R = R} {m′ = m′} e q) = subst (λ b → BlR R b (block m′)) (sym e) (blockR q)

-- BIND respects it: related results, related continuations
mutual
  >>=-congR : ∀ {X X′ Y Y′} {R : X → X′ → Set} {S : Y → Y′ → Set} {m : T∞ X} {m′ : T∞ X′}
              {k : X → T∞ Y} {k′ : X′ → T∞ Y′}
            → m ≈[ R ] m′ → (∀ {x y} → R x y → k x ≈[ S ] k′ y) → (m >>=∞ k) ≈[ S ] (m′ >>=∞ k′)
  blockR (>>=-congR p kk) = bind-BlR (blockR p) kk

  bind-BlR : ∀ {X X′ Y Y′} {R : X → X′ → Set} {S : Y → Y′ → Set} {b : T (X ⊎ T∞ X)} {b′ : T (X′ ⊎ T∞ X′)}
             {k : X → T∞ Y} {k′ : X′ → T∞ Y′}
           → BlR R b b′ → (∀ {x y} → R x y → k x ≈[ S ] k′ y) → BlR S (bindBlock b k) (bindBlock b′ k′)
  bind-BlR (≈retR r)  kk = blockR (kk r)
  bind-BlR (≈stepR p) kk = ≈stepR (>>=-congR p kk)
  bind-BlR (≈callR f) kk = ≈callR (λ y → bind-BlR (f y) kk)
  bind-BlR ≈haltR     kk = ≈haltR

fmap-congR : ∀ {X X′ Y Y′} {R : X → X′ → Set} {S : Y → Y′ → Set} {m : T∞ X} {m′ : T∞ X′} {f : X → Y} {f′ : X′ → Y′}
           → m ≈[ R ] m′ → (∀ {x y} → R x y → S (f x) (f′ y)) → fmap∞ f m ≈[ S ] fmap∞ f′ m′
fmap-congR p ff = >>=-congR p (λ r → ret≈R (ff r))

-- THE LOOP respects it: the states related by `RA`, the results by `RB`
mutual
  iter-congR : ∀ {A A′ B B′ : Set} {RA : A → A′ → Set} {RB : B → B′ → Set} {f : A → T∞ (B ⊎ A)} {f′ : A′ → T∞ (B′ ⊎ A′)}
               {m : T∞ (B ⊎ A)} {m′ : T∞ (B′ ⊎ A′)}
             → (∀ {a a′} → RA a a′ → f a ≈[ Pointwise RB RA ] f′ a′) → m ≈[ Pointwise RB RA ] m′
             → iterRun f m ≈[ RB ] iterRun f′ m′
  blockR (iter-congR ff p) = iter-BlR ff (blockR p)

  iter-BlR : ∀ {A A′ B B′ : Set} {RA : A → A′ → Set} {RB : B → B′ → Set} {f : A → T∞ (B ⊎ A)} {f′ : A′ → T∞ (B′ ⊎ A′)}
             {b : T ((B ⊎ A) ⊎ T∞ (B ⊎ A))} {b′ : T ((B′ ⊎ A′) ⊎ T∞ (B′ ⊎ A′))}
           → (∀ {a a′} → RA a a′ → f a ≈[ Pointwise RB RA ] f′ a′) → BlR (Pointwise RB RA) b b′
           → BlR RB (iterBlock f b) (iterBlock f′ b′)
  iter-BlR ff (≈retR (⊎₁ r)) = ≈retR r
  iter-BlR ff (≈retR (⊎₂ r)) = ≈stepR (iter-congR ff (ff r))
  iter-BlR ff (≈stepR p)     = ≈stepR (iter-congR ff p)
  iter-BlR ff (≈callR g)     = ≈callR (λ y → iter-BlR ff (g y))
  iter-BlR ff ≈haltR         = ≈haltR

-- the two kinds meet: plain bisimilarity on either side
mutual
  ≈-≈R : ∀ {X Y} {R : X → Y → Set} {m m′ : T∞ X} {m″ : T∞ Y} → m ≈ m′ → m′ ≈[ R ] m″ → m ≈[ R ] m″
  blockR (≈-≈R p q) = Bl-BlR (block≈ p) (blockR q)

  Bl-BlR : ∀ {X Y} {R : X → Y → Set} {b b′ : T (X ⊎ T∞ X)} {b″ : T (Y ⊎ T∞ Y)} → Bl b b′ → BlR R b′ b″ → BlR R b b″
  Bl-BlR ≈ret      (≈retR r)  = ≈retR r
  Bl-BlR (≈step p) (≈stepR q) = ≈stepR (≈-≈R p q)
  Bl-BlR (≈call f) (≈callR g) = ≈callR (λ y → Bl-BlR (f y) (g y))
  Bl-BlR ≈halt     ≈haltR     = ≈haltR

mutual
  ≈R-≈ : ∀ {X Y} {R : X → Y → Set} {m : T∞ X} {m′ m″ : T∞ Y} → m ≈[ R ] m′ → m′ ≈ m″ → m ≈[ R ] m″
  blockR (≈R-≈ p q) = BlR-Bl (blockR p) (block≈ q)

  BlR-Bl : ∀ {X Y} {R : X → Y → Set} {b : T (X ⊎ T∞ X)} {b′ b″ : T (Y ⊎ T∞ Y)} → BlR R b b′ → Bl b′ b″ → BlR R b b″
  BlR-Bl (≈retR r)  ≈ret      = ≈retR r
  BlR-Bl (≈stepR p) (≈step q) = ≈stepR (≈R-≈ p q)
  BlR-Bl (≈callR f) (≈call g) = ≈callR (λ y → BlR-Bl (f y) (g y))
  BlR-Bl ≈haltR     ≈halt     = ≈haltR

-- where `R` is `≡`, the two agree
mutual
  ≈R→≈ : ∀ {X} {R : X → X → Set} {m m′ : T∞ X} → (∀ {x y} → R x y → x ≡ y) → m ≈[ R ] m′ → m ≈ m′
  block≈ (≈R→≈ eq p) = BlR→Bl eq (blockR p)

  BlR→Bl : ∀ {X} {R : X → X → Set} {b b′ : T (X ⊎ T∞ X)} → (∀ {x y} → R x y → x ≡ y) → BlR R b b′ → Bl b b′
  BlR→Bl eq (≈retR {x = x} r) = subst (λ y → Bl (ret (inj₁ x)) (ret (inj₁ y))) (eq r) ≈ret
  BlR→Bl eq (≈stepR p)        = ≈step (≈R→≈ eq p)
  BlR→Bl eq (≈callR f)        = ≈call (λ y → BlR→Bl eq (f y))
  BlR→Bl eq ≈haltR            = ≈halt

mutual
  ≈→≈R : ∀ {X} {R : X → X → Set} {m m′ : T∞ X} → (∀ x → R x x) → m ≈ m′ → m ≈[ R ] m′
  blockR (≈→≈R rf p) = Bl→BlR rf (block≈ p)

  Bl→BlR : ∀ {X} {R : X → X → Set} {b b′ : T (X ⊎ T∞ X)} → (∀ x → R x x) → Bl b b′ → BlR R b b′
  Bl→BlR rf (≈ret {x = x}) = ≈retR (rf x)
  Bl→BlR rf (≈step p)      = ≈stepR (≈→≈R rf p)
  Bl→BlR rf (≈call f)      = ≈callR (λ y → Bl→BlR rf (f y))
  Bl→BlR rf ≈halt          = ≈haltR

-- ★ B1.3: two relations compose (the core against `Pass.ev`, `Pass.ev`
-- against master's `evalᴰ`)
mutual
  ≈R-∘ : ∀ {X Y Z} {R : X → Y → Set} {S : Y → Z → Set} {m : T∞ X} {m′ : T∞ Y} {m″ : T∞ Z}
       → m ≈[ R ] m′ → m′ ≈[ S ] m″ → m ≈[ (λ x z → Σ Y (λ y → R x y × S y z)) ] m″
  blockR (≈R-∘ p q) = BlR-∘ (blockR p) (blockR q)

  BlR-∘ : ∀ {X Y Z} {R : X → Y → Set} {S : Y → Z → Set} {b : T (X ⊎ T∞ X)} {b′ : T (Y ⊎ T∞ Y)} {b″ : T (Z ⊎ T∞ Z)}
        → BlR R b b′ → BlR S b′ b″ → BlR (λ x z → Σ Y (λ y → R x y × S y z)) b b″
  BlR-∘ (≈retR r)  (≈retR s)  = ≈retR (_ , r , s)
  BlR-∘ (≈stepR p) (≈stepR q) = ≈stepR (≈R-∘ p q)
  BlR-∘ (≈callR f) (≈callR g) = ≈callR (λ y → BlR-∘ (f y) (g y))
  BlR-∘ ≈haltR     ≈haltR     = ≈haltR

------------------------------------------------------------------------
-- 3. ONE FINITE BLOCK, up to a relation on its value (`T`, the Spec's
-- `M act`): the same calls, and related values where it returns.
------------------------------------------------------------------------

-- (heterogeneous: a block of seeds against a block of ν's, `Pass`)
data TR {X Y : Set} (R : X → Y → Set) : T X → T Y → Set where
  tret  : ∀ {x y} → R x y → TR R (ret x) (ret y)
  tcall : ∀ {s x k k′} → (∀ y → TR R (k y) (k′ y)) → TR R (call s x k) (call s x k′)
  thalt : ∀ {s x} → TR R (halt s x) (halt s x)

TR-bind : ∀ {X X′ Y Y′} {R : X → X′ → Set} {S : Y → Y′ → Set} {m : T X} {m′ : T X′}
          {k : X → T Y} {k′ : X′ → T Y′}
        → TR R m m′ → (∀ {x y} → R x y → TR S (k x) (k′ y)) → TR S (bindT m k) (bindT m′ k′)
TR-bind (tret r)  kk = kk r
TR-bind (tcall f) kk = tcall (λ y → TR-bind (f y) kk)
TR-bind thalt     kk = thalt

-- embedded, a related block is a related computation, and back
emb-TR : ∀ {X Y} {R : X → Y → Set} {a : T X} {b : T Y} → TR R a b → emb a ≈[ R ] emb b
blockR (emb-TR p) = embB-TR p
  where
  embB-TR : ∀ {X Y} {R : X → Y → Set} {a : T X} {b : T Y} → TR R a b → BlR R (embB a) (embB b)
  embB-TR (tret r)  = ≈retR r
  embB-TR (tcall f) = ≈callR (λ y → embB-TR (f y))
  embB-TR thalt     = ≈haltR

TR-emb : ∀ {X} {R : X → X → Set} (a b : T X) → emb a ≈[ R ] emb b → TR R a b
TR-emb a b p = go a b (blockR p)
  where
  go : ∀ {X} {R : X → X → Set} (a b : T X) → BlR R (embB a) (embB b) → TR R a b
  go (ret x)      (ret y)       (≈retR r)  = tret r
  go (call s x k) (call s′ y k′) (≈callR f) = tcall (λ z → go (k z) (k′ z) (f z))
  go (halt s x)   (halt s′ y)   ≈haltR     = thalt
  go (ret x)      (call s y k)  ()
  go (ret x)      (halt s y)    ()
  go (call s x k) (ret y)       ()
  go (call s x k) (halt s′ y)   ()
  go (halt s x)   (ret y)       ()
  go (halt s x)   (call s′ y k) ()
