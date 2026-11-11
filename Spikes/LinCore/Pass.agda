-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- LinCore.Pass — plan 0.146 A15, part 1 (D409): THE PASS, FIRST-ORDER.
--
-- A copy of `Once.IR`'s first-order constructors (everything but `curry`/
-- `apply`, `Ana`/`Out`/`in-ν` and `Call`, whose labels are the open design
-- question of part 2, D409), their meaning shaped as master's `evalᴰ`
-- (`Once.Denotation.DenotTrace`: a computation in `T∞`), the translation into
-- the linear core, and the theorem: the translation MEANS THE SAME, up to
-- BISIMILARITY of computations (a loop's meaning is coinductive, so `≡` would
-- not do).
--
-- The translation is the faithful one: `⟨f,g⟩` duplicates its input; a
-- fold's and a loop's environment is LENT to the body and COPIED per use (the
-- IR's algebra owns `E`); `fst`/`snd`/`terminal` drop. The cheaper choices (a
-- lent pair, no copy) are refinements of this translation, proved the same way.
------------------------------------------------------------------------

{-# OPTIONS --safe --guardedness #-}

open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (sym; subst)
open import Agda.Builtin.Sigma using (_,_)
open import Data.Product using (_×_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import LinCore.Flat using (FTy)

module LinCore.Pass
  (Base : Set) (⟦_⟧b : Base → Set)
  (Sig : Set) (sdom scod : Sig → FTy Base)
  where

open import LinCore.NbEPLinCore Base ⟦_⟧b Sig sdom scod

------------------------------------------------------------------------
-- 1. BISIMILARITY of computations: the same blocks, step for step, for every
-- answer of the world.
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
-- 2. THE IR, FIRST-ORDER: master's constructors, over the core's types.
------------------------------------------------------------------------

infixr 9 _∘_
data IR : LTy → LTy → Set where
  id       : ∀ {A} → IR A A
  _∘_      : ∀ {A B C} → IR B C → IR A B → IR A C
  ⟨_,_⟩    : ∀ {A B C} → IR A B → IR A C → IR A (B ⊗t C)
  fst      : ∀ {A B} → IR (A ⊗t B) A
  snd      : ∀ {A B} → IR (A ⊗t B) B
  inl      : ∀ {A B} → IR A (A ⊕t B)
  inr      : ∀ {A B} → IR B (A ⊕t B)
  case     : ∀ {A B C} → IR A C → IR B C → IR (A ⊕t B) C
  terminal : ∀ {A} → IR A One
  initial  : ∀ {A} → IR Zero A
  In       : ∀ F → IR (LF∙ F (μt F)) (μt F)
  out-μ    : ∀ F → IR (μt F) (LF∙ F (μt F))
  -- the parameterised fold (D131): the algebra reads a fixed environment
  Cata     : ∀ F {E A} → IR (E ⊗t LF∙ F A) A → IR (E ⊗t μt F) A
  -- the loop (D317): the round reads a fixed environment and the state
  Iter     : ∀ {E A B} → IR (E ⊗t A) (B ⊕t A) → IR (E ⊗t A) B
  const    : ∀ {b} → ⟦ b ⟧b → IR One (Bt b)
  SigOp    : (s : Sig) → IR ⌜ sdom s ⌝ ⌜ scod s ⌝

-- its meaning, clause for clause master's `evalᴰ`
ev : ∀ {A B} → IR A B → ⟦ A ⟧ → T∞ ⟦ B ⟧
ev id            a        = return∞ a
ev (g ∘ f)       a        = ev f a >>=∞ ev g
ev ⟨ f , g ⟩     a        = ev f a >>=∞ λ b → ev g a >>=∞ λ c → return∞ (b , c)
ev fst           (a , b)  = return∞ a
ev snd           (a , b)  = return∞ b
ev inl           a        = return∞ (inj₁ a)
ev inr           b        = return∞ (inj₂ b)
ev (case f g)    (inj₁ a) = ev f a
ev (case f g)    (inj₂ b) = ev g b
ev terminal      _        = return∞ tt
ev initial       ()
ev (In F)        x        = return∞ (inμ (coh F (μt F) x))
ev (out-μ F)     x        = return∞ (coh⁻¹ F (μt F) (outμ x))
ev (Cata F alg)  (e , x)  = cataC ε F (λ y → ev alg (e , coh⁻¹ F _ y)) x
ev (Iter body)   (e , a)  = iter∞ (λ a′ → ev body (e , a′)) a
ev (const v)     _        = return∞ v
ev (SigOp s)     x        = callT s x

------------------------------------------------------------------------
-- 3. THE TRANSLATION into the core (closed: nothing lent, no labels).
------------------------------------------------------------------------

-- drop the left of a pair
dropl : ∀ {Γ E A B} → Tm Γ E (A ⊗t B) B
dropl = lul ∘l (drop ⊗l lid)

-- a body that owns `E`, run where `E` is lent: copy it in
withE : ∀ {E A B} → LTm ε (E ⊗t A) B → Tm ε (One ⊗t E) A B
withE b = blift b ∘l (bsnd bcopy ⊗l lid) ∘l lul⁻

tr : ∀ {A B} → IR A B → LTm ε A B
tr id           = lid
tr (g ∘ f)      = tr g ∘l tr f
tr ⟨ f , g ⟩    = (tr f ⊗l tr g) ∘l dup
tr fst          = ρl ∘l (lid ⊗l drop)
tr snd          = dropl
tr inl          = linl
tr inr          = linr
tr (case f g)   = lcase (tr f) (tr g)
tr terminal     = drop
tr initial      = lzero
tr (In F)       = lIn
tr (out-μ F)    = lOutμ
tr (Cata F alg) = dropl ∘l lend (lcata F (withE (tr alg)))
tr (Iter body)  = dropl ∘l lend (liter (withE (tr body)))
tr (const v)    = lconst v
tr (SigOp s)    = lop s

------------------------------------------------------------------------
-- 4. ★ THE THEOREM: the translation means what the IR means.
------------------------------------------------------------------------

-- the fold respects bisimilar algebras
mutual
  cata-cong : ∀ F {X : Set} {alg alg′ : FS F X → T∞ X} → (∀ y → alg y ≈ alg′ y)
            → ∀ x → cataC ε F alg x ≈ cataC ε F alg′ x
  cata-cong F aa (inμ w) = >>=-cong (trav-cong F F aa w) aa

  trav-cong : ∀ F G {X : Set} {alg alg′ : FS F X → T∞ X} → (∀ y → alg y ≈ alg′ y)
            → ∀ w → travC ε F G alg w ≈ travC ε F G alg′ w
  trav-cong F Idf      aa y        = cata-cong F aa y
  trav-cong F Kone     aa y        = ≈-refl
  trav-cong F Kzero    aa ()
  trav-cong F (Kb _)   aa y        = ≈-refl
  trav-cong F (Kμ _)   aa y        = ≈-refl
  trav-cong F (G ⊕f H) aa (inj₁ y) = >>=-cong (trav-cong F G aa y) (λ _ → ≈-refl)
  trav-cong F (G ⊕f H) aa (inj₂ z) = >>=-cong (trav-cong F H aa z) (λ _ → ≈-refl)
  trav-cong F (G ⊗f H) aa (y , z)  = >>=-cong (trav-cong F G aa y) (λ u → >>=-cong (trav-cong F H aa z) (λ _ → ≈-refl))

pass-ok : ∀ {A B} (f : IR A B) (a : ⟦ A ⟧) → Lᶜ ε (tr f) tt a ≈ ev f a
pass-ok id           a        = ≈-refl
pass-ok (g ∘ f)      a        = >>=-cong (pass-ok f a) (pass-ok g)
pass-ok ⟨ f , g ⟩    a        = ≈-blk refl (>>=-cong (pass-ok f a) (λ b → >>=-cong (pass-ok g a) (λ c → ≈-refl)))
pass-ok fst          (a , b)  = ≈-blk refl ≈-refl
pass-ok snd          (a , b)  = ≈-blk refl ≈-refl
pass-ok inl          a        = ≈-refl
pass-ok inr          b        = ≈-refl
pass-ok (case f g)   (inj₁ a) = pass-ok f a
pass-ok (case f g)   (inj₂ b) = pass-ok g b
pass-ok terminal     _        = ≈-refl
pass-ok initial      ()
pass-ok (In F)       x        = ≈-refl
pass-ok (out-μ F)    x        = ≈-refl
pass-ok (Cata F {E} {R} alg) (e , x) =
  ≈-trans (pair-drop (e ,_) (λ p → Lᶜ ε (dropl {E = One} {A = E} {B = R}) tt p) (λ _ → refl))
          (cata-cong F (λ y → ≈-blk refl (pass-ok alg (e , coh⁻¹ F R y))) x)
pass-ok (Iter {E} {S} {R} body) (e , a) =
  ≈-trans (pair-drop (e ,_) (λ p → Lᶜ ε (dropl {E = One} {A = E} {B = R}) tt p) (λ _ → refl))
          (iter-cong (λ a′ → ≈-blk refl (pass-ok body (e , a′))) (≈-blk refl (pass-ok body (e , a))))
pass-ok (const v)    _        = ≈-refl
pass-ok (SigOp s)    x        = ≈-refl
