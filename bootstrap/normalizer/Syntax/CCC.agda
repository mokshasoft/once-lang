------------------------------------------------------------------------
-- CCC: Cartesian Closed Category with Recursion
--
-- This module defines the structure for proving:
--   1. CCC with cata has confluence and termination
--   2. Normal forms are unique
--   3. Fixpoint implies correctness
--
-- Imports Types module for the foundation (prelude, types, functors).
------------------------------------------------------------------------

module normalizer.Syntax.CCC where

open import normalizer.Syntax.Types public

------------------------------------------------------------------------
-- Terms (CCC + cata)
------------------------------------------------------------------------

data Term : Ty → Ty → Set where
  -- Category
  id       : ∀ {A} → Term A A
  _∘_      : ∀ {A B C} → Term B C → Term A B → Term A C
  -- Products
  fst      : ∀ {A B} → Term (A * B) A
  snd      : ∀ {A B} → Term (A * B) B
  ⟨_,_⟩    : ∀ {A B C} → Term C A → Term C B → Term C (A * B)
  -- Coproducts
  inl      : ∀ {A B} → Term A (A + B)
  inr      : ∀ {A B} → Term B (A + B)
  [_,_]    : ∀ {A B C} → Term A C → Term B C → Term (A + B) C
  -- Terminal
  terminal : ∀ {A} → Term A Unit
  -- Initial (Void is the initial object)
  initial  : ∀ {A} → Term Void A
  -- Exponentials
  curry    : ∀ {A B C} → Term (A * B) C → Term A (B ⇒ C)
  apply    : ∀ {A B} → Term ((A ⇒ B) * A) B
  -- Initial/Final algebra (recursion and corecursion)
  In       : ∀ {F} → Term (⟦ F ⟧F (μ F)) (μ F)
  Out      : ∀ {F} → Term (μ F) (⟦ F ⟧F (μ F))
  cata     : ∀ F {A} → Term (⟦ F ⟧F A) A → Term (μ F) A

infixr 9 _∘_

-- fmap: lift morphism through functor
fmap : ∀ F {A B} → Term A B → Term (⟦ F ⟧F A) (⟦ F ⟧F B)
fmap Id f = f
fmap (K _) _ = id
fmap (F ⊕ G) f = [ inl ∘ fmap F f , inr ∘ fmap G f ]
fmap (F ⊗ G) f = ⟨ fmap F f ∘ fst , fmap G f ∘ snd ⟩

------------------------------------------------------------------------
-- Part 3: Reduction (categorical laws)
------------------------------------------------------------------------

data _⟶_ : ∀ {A B} → Term A B → Term A B → Set where
  -- Identity
  id-left   : ∀ {A B} {f : Term A B} → (id ∘ f) ⟶ f
  id-right  : ∀ {A B} {f : Term A B} → (f ∘ id) ⟶ f
  -- Products
  fst-pair  : ∀ {A B C} {f : Term C A} {g : Term C B} → (fst ∘ ⟨ f , g ⟩) ⟶ f
  snd-pair  : ∀ {A B C} {f : Term C A} {g : Term C B} → (snd ∘ ⟨ f , g ⟩) ⟶ g
  eta-pair  : ∀ {A B} → ⟨ fst , snd ⟩ ⟶ id {A * B}
  -- Coproducts
  case-inl  : ∀ {A B C} {f : Term A C} {g : Term B C} → ([ f , g ] ∘ inl) ⟶ f
  case-inr  : ∀ {A B C} {f : Term A C} {g : Term B C} → ([ f , g ] ∘ inr) ⟶ g
  eta-case  : ∀ {A B} → [ inl , inr ] ⟶ id {A + B}
  -- Pair distribution over composition (CCC axiom)
  pair-comp : ∀ {A B C D} {f : Term B C} {g : Term B D} {h : Term A B} →
              (⟨ f , g ⟩ ∘ h) ⟶ ⟨ f ∘ h , g ∘ h ⟩
  -- Exponentials (curry/apply)
  curry-β   : ∀ {A B C} {f : Term (A * B) C} {g : Term A B} →
              (apply ∘ ⟨ curry f , g ⟩) ⟶ (f ∘ ⟨ id , g ⟩)
  -- Generalized curry-β (naturality of the exponential counit)
  -- This is a standard CCC law: apply ∘ (curry f × id) ∘ ⟨h, g⟩ = f ∘ ⟨h, g⟩
  curry-β-ext : ∀ {X A B C} {f : Term (A * B) C} {h : Term X A} {g : Term X B} →
              (apply ∘ ⟨ curry f ∘ h , g ⟩) ⟶ (f ∘ ⟨ h , g ⟩)
  curry-η   : ∀ {A B C} {f : Term A (B ⇒ C)} →
              curry (apply ∘ ⟨ f ∘ fst , snd ⟩) ⟶ f
  -- Catamorphism (the key recursion rule)
  cata-β    : ∀ {F A} {alg : Term (⟦ F ⟧F A) A} →
              (cata F alg ∘ In) ⟶ (alg ∘ fmap F (cata F alg))
  -- In and Out are inverses (F explicit to avoid computed type unification issues)
  out-in    : ∀ F → (Out {F} ∘ In {F}) ⟶ id {⟦ F ⟧F (μ F)}
  in-out    : ∀ F → (In {F} ∘ Out {F}) ⟶ id {μ F}
  -- Associativity (CCC axiom - both directions for flexibility)
  assoc-l   : ∀ {A B C D} {f : Term C D} {g : Term B C} {h : Term A B} →
              (f ∘ (g ∘ h)) ⟶ ((f ∘ g) ∘ h)
  assoc-r   : ∀ {A B C D} {f : Term C D} {g : Term B C} {h : Term A B} →
              ((f ∘ g) ∘ h) ⟶ (f ∘ (g ∘ h))
  -- Congruence rules (needed for ⟹→⟶*)
  ⟶-∘-l    : ∀ {A B C} {f f' : Term B C} {g : Term A B} →
              f ⟶ f' → (f ∘ g) ⟶ (f' ∘ g)
  ⟶-∘-r    : ∀ {A B C} {f : Term B C} {g g' : Term A B} →
              g ⟶ g' → (f ∘ g) ⟶ (f ∘ g')
  ⟶-pair-l : ∀ {A B C} {f f' : Term C A} {g : Term C B} →
              f ⟶ f' → ⟨ f , g ⟩ ⟶ ⟨ f' , g ⟩
  ⟶-pair-r : ∀ {A B C} {f : Term C A} {g g' : Term C B} →
              g ⟶ g' → ⟨ f , g ⟩ ⟶ ⟨ f , g' ⟩
  ⟶-case-l : ∀ {A B C} {f f' : Term A C} {g : Term B C} →
              f ⟶ f' → [ f , g ] ⟶ [ f' , g ]
  ⟶-case-r : ∀ {A B C} {f : Term A C} {g g' : Term B C} →
              g ⟶ g' → [ f , g ] ⟶ [ f , g' ]
  ⟶-cata   : ∀ {F A} {alg alg' : Term (⟦ F ⟧F A) A} →
              alg ⟶ alg' → cata F alg ⟶ cata F alg'
  ⟶-curry  : ∀ {A B C} {f f' : Term (A * B) C} →
              f ⟶ f' → curry f ⟶ curry f'

-- Reflexive-transitive closure
data _⟶*_ : ∀ {A B} → Term A B → Term A B → Set where
  done : ∀ {A B} {t : Term A B} → t ⟶* t
  step : ∀ {A B} {t u v : Term A B} → t ⟶ u → u ⟶* v → t ⟶* v

------------------------------------------------------------------------
-- Part 4: Parallel Reduction (for confluence proof)
------------------------------------------------------------------------

-- Parallel reduction: reduce ALL redexes at once
-- This is the Tait-Martin-Löf technique for proving confluence
data _⟹_ : ∀ {A B} → Term A B → Term A B → Set where
  -- Reflexivity for atoms
  ⟹-id       : ∀ {A} → id {A} ⟹ id
  ⟹-fst      : ∀ {A B} → fst {A} {B} ⟹ fst
  ⟹-snd      : ∀ {A B} → snd {A} {B} ⟹ snd
  ⟹-inl      : ∀ {A B} → inl {A} {B} ⟹ inl
  ⟹-inr      : ∀ {A B} → inr {A} {B} ⟹ inr
  ⟹-terminal : ∀ {A} → terminal {A} ⟹ terminal
  ⟹-initial  : ∀ {A} → initial {A} ⟹ initial
  ⟹-apply    : ∀ {A B} → apply {A} {B} ⟹ apply
  ⟹-In       : ∀ {F} → In {F} ⟹ In
  ⟹-Out      : ∀ {F} → Out {F} ⟹ Out

  -- Congruence for compound terms
  ⟹-∘    : ∀ {A B C} {f f' : Term B C} {g g' : Term A B} →
           f ⟹ f' → g ⟹ g' → (f ∘ g) ⟹ (f' ∘ g')
  ⟹-pair : ∀ {A B C} {f f' : Term C A} {g g' : Term C B} →
           f ⟹ f' → g ⟹ g' → ⟨ f , g ⟩ ⟹ ⟨ f' , g' ⟩
  ⟹-case : ∀ {A B C} {f f' : Term A C} {g g' : Term B C} →
           f ⟹ f' → g ⟹ g' → [ f , g ] ⟹ [ f' , g' ]
  ⟹-curry : ∀ {A B C} {f f' : Term (A * B) C} →
            f ⟹ f' → curry f ⟹ curry f'
  ⟹-cata : ∀ {F A} {alg alg' : Term (⟦ F ⟧F A) A} →
           alg ⟹ alg' → cata F alg ⟹ cata F alg'

  -- Beta reductions (the actual computation steps)
  ⟹-id-l    : ∀ {A B} {f f' : Term A B} →
              f ⟹ f' → (id ∘ f) ⟹ f'
  ⟹-id-r    : ∀ {A B} {f f' : Term A B} →
              f ⟹ f' → (f ∘ id) ⟹ f'
  ⟹-fst-β   : ∀ {A B C} {f f' : Term C A} {g g' : Term C B} →
              f ⟹ f' → g ⟹ g' → (fst ∘ ⟨ f , g ⟩) ⟹ f'
  ⟹-snd-β   : ∀ {A B C} {f f' : Term C A} {g g' : Term C B} →
              f ⟹ f' → g ⟹ g' → (snd ∘ ⟨ f , g ⟩) ⟹ g'
  ⟹-inl-β   : ∀ {A B C} {f f' : Term A C} {g g' : Term B C} →
              f ⟹ f' → g ⟹ g' → ([ f , g ] ∘ inl) ⟹ f'
  ⟹-inr-β   : ∀ {A B C} {f f' : Term A C} {g g' : Term B C} →
              f ⟹ f' → g ⟹ g' → ([ f , g ] ∘ inr) ⟹ g'
  ⟹-cata-β  : ∀ {F A} {alg alg' : Term (⟦ F ⟧F A) A} →
              alg ⟹ alg' → (cata F alg ∘ In) ⟹ (alg' ∘ fmap F (cata F alg'))

  -- Eta reductions
  ⟹-η-pair  : ∀ {A B} → ⟨ fst , snd ⟩ ⟹ id {A * B}
  ⟹-η-case  : ∀ {A B} → [ inl , inr ] ⟹ id {A + B}
  ⟹-η-curry : ∀ {A B C} {f f' : Term A (B ⇒ C)} →
              f ⟹ f' → curry (apply ∘ ⟨ f ∘ fst , snd ⟩) ⟹ f'

  -- Curry-apply beta
  ⟹-curry-β : ∀ {A B C} {f f' : Term (A * B) C} {g g' : Term A B} →
              f ⟹ f' → g ⟹ g' → (apply ∘ ⟨ curry f , g ⟩) ⟹ (f' ∘ ⟨ id , g' ⟩)

  -- Generalized curry-apply beta (naturality of exponential counit)
  ⟹-curry-β-ext : ∀ {X A B C} {f f' : Term (A * B) C} {h h' : Term X A} {g g' : Term X B} →
              f ⟹ f' → h ⟹ h' → g ⟹ g' → (apply ∘ ⟨ curry f ∘ h , g ⟩) ⟹ (f' ∘ ⟨ h' , g' ⟩)

  -- Out/In reductions (F explicit to avoid computed type unification issues)
  ⟹-out-in  : ∀ F → (Out {F} ∘ In {F}) ⟹ id {⟦ F ⟧F (μ F)}
  ⟹-in-out  : ∀ F → (In {F} ∘ Out {F}) ⟹ id {μ F}

  -- Associativity
  ⟹-assoc-l : ∀ {A B C D} {f f' : Term C D} {g g' : Term B C} {h h' : Term A B} →
              f ⟹ f' → g ⟹ g' → h ⟹ h' → (f ∘ (g ∘ h)) ⟹ ((f' ∘ g') ∘ h')
  ⟹-assoc-r : ∀ {A B C D} {f f' : Term C D} {g g' : Term B C} {h h' : Term A B} →
              f ⟹ f' → g ⟹ g' → h ⟹ h' → ((f ∘ g) ∘ h) ⟹ (f' ∘ (g' ∘ h'))

  -- Pair distribution over composition
  ⟹-pair-comp : ∀ {A B C D} {f f' : Term B C} {g g' : Term B D} {h h' : Term A B} →
                f ⟹ f' → g ⟹ g' → h ⟹ h' → (⟨ f , g ⟩ ∘ h) ⟹ ⟨ f' ∘ h' , g' ∘ h' ⟩

-- Parallel reduction is reflexive
⟹-refl : ∀ {A B} (t : Term A B) → t ⟹ t
⟹-refl id = ⟹-id
⟹-refl (f ∘ g) = ⟹-∘ (⟹-refl f) (⟹-refl g)
⟹-refl fst = ⟹-fst
⟹-refl snd = ⟹-snd
⟹-refl ⟨ f , g ⟩ = ⟹-pair (⟹-refl f) (⟹-refl g)
⟹-refl inl = ⟹-inl
⟹-refl inr = ⟹-inr
⟹-refl [ f , g ] = ⟹-case (⟹-refl f) (⟹-refl g)
⟹-refl terminal = ⟹-terminal
⟹-refl initial = ⟹-initial
⟹-refl (curry f) = ⟹-curry (⟹-refl f)
⟹-refl apply = ⟹-apply
⟹-refl In = ⟹-In
⟹-refl Out = ⟹-Out
⟹-refl (cata F alg) = ⟹-cata (⟹-refl alg)

-- Single step implies parallel
-- All cases are trivial: each reduction rule has a corresponding parallel reduction.
⟶→⟹ : ∀ {A B} {t u : Term A B} → t ⟶ u → t ⟹ u
⟶→⟹ id-left = ⟹-id-l (⟹-refl _)
⟶→⟹ id-right = ⟹-id-r (⟹-refl _)
⟶→⟹ fst-pair = ⟹-fst-β (⟹-refl _) (⟹-refl _)
⟶→⟹ snd-pair = ⟹-snd-β (⟹-refl _) (⟹-refl _)
⟶→⟹ eta-pair = ⟹-η-pair
⟶→⟹ case-inl = ⟹-inl-β (⟹-refl _) (⟹-refl _)
⟶→⟹ case-inr = ⟹-inr-β (⟹-refl _) (⟹-refl _)
⟶→⟹ eta-case = ⟹-η-case
⟶→⟹ cata-β = ⟹-cata-β (⟹-refl _)
⟶→⟹ (out-in F) = ⟹-out-in F
⟶→⟹ (in-out F) = ⟹-in-out F
⟶→⟹ assoc-l = ⟹-assoc-l (⟹-refl _) (⟹-refl _) (⟹-refl _)
⟶→⟹ assoc-r = ⟹-assoc-r (⟹-refl _) (⟹-refl _) (⟹-refl _)
⟶→⟹ pair-comp = ⟹-pair-comp (⟹-refl _) (⟹-refl _) (⟹-refl _)
⟶→⟹ curry-β = ⟹-curry-β (⟹-refl _) (⟹-refl _)
⟶→⟹ curry-β-ext = ⟹-curry-β-ext (⟹-refl _) (⟹-refl _) (⟹-refl _)
⟶→⟹ curry-η = ⟹-η-curry (⟹-refl _)
⟶→⟹ (⟶-∘-l r) = ⟹-∘ (⟶→⟹ r) (⟹-refl _)
⟶→⟹ (⟶-∘-r r) = ⟹-∘ (⟹-refl _) (⟶→⟹ r)
⟶→⟹ (⟶-pair-l r) = ⟹-pair (⟶→⟹ r) (⟹-refl _)
⟶→⟹ (⟶-pair-r r) = ⟹-pair (⟹-refl _) (⟶→⟹ r)
⟶→⟹ (⟶-case-l r) = ⟹-case (⟶→⟹ r) (⟹-refl _)
⟶→⟹ (⟶-case-r r) = ⟹-case (⟹-refl _) (⟶→⟹ r)
⟶→⟹ (⟶-cata r) = ⟹-cata (⟶→⟹ r)
⟶→⟹ (⟶-curry r) = ⟹-curry (⟶→⟹ r)

------------------------------------------------------------------------
-- Part 5: Diamond Property and Confluence
------------------------------------------------------------------------

-- Reflexive-transitive closure of parallel reduction
data _⟹*_ : ∀ {A B} → Term A B → Term A B → Set where
  done⟹ : ∀ {A B} {t : Term A B} → t ⟹* t
  step⟹ : ∀ {A B} {t u v : Term A B} → t ⟹ u → u ⟹* v → t ⟹* v

-- ⟶* implies ⟹*
⟶*→⟹* : ∀ {A B} {t u : Term A B} → t ⟶* u → t ⟹* u
⟶*→⟹* done = done⟹
⟶*→⟹* (step r rs) = step⟹ (⟶→⟹ r) (⟶*→⟹* rs)

-- Helper: transitivity of ⟶*
⟶*-trans : ∀ {A B} {t u v : Term A B} → t ⟶* u → u ⟶* v → t ⟶* v
⟶*-trans done q = q
⟶*-trans (step p ps) q = step p (⟶*-trans ps q)

-- Helper: lift ⟶* through composition (left)
⟶*-∘-l : ∀ {A B C} {f f' : Term B C} (g : Term A B) →
         f ⟶* f' → (f ∘ g) ⟶* (f' ∘ g)
⟶*-∘-l g done = done
⟶*-∘-l g (step r rs) = step (⟶-∘-l r) (⟶*-∘-l g rs)

-- Helper: lift ⟶* through composition (right)
⟶*-∘-r : ∀ {A B C} (f : Term B C) {g g' : Term A B} →
         g ⟶* g' → (f ∘ g) ⟶* (f ∘ g')
⟶*-∘-r f done = done
⟶*-∘-r f (step r rs) = step (⟶-∘-r r) (⟶*-∘-r f rs)

-- Helper: lift ⟶* through pair
⟶*-pair : ∀ {A B C} {f f' : Term C A} {g g' : Term C B} →
          f ⟶* f' → g ⟶* g' → ⟨ f , g ⟩ ⟶* ⟨ f' , g' ⟩
⟶*-pair done done = done
⟶*-pair done (step r rs) = step (⟶-pair-r r) (⟶*-pair done rs)
⟶*-pair (step r rs) gs = step (⟶-pair-l r) (⟶*-pair rs gs)

-- Helper: lift ⟶* through case
⟶*-case : ∀ {A B C} {f f' : Term A C} {g g' : Term B C} →
          f ⟶* f' → g ⟶* g' → [ f , g ] ⟶* [ f' , g' ]
⟶*-case done done = done
⟶*-case done (step r rs) = step (⟶-case-r r) (⟶*-case done rs)
⟶*-case (step r rs) gs = step (⟶-case-l r) (⟶*-case rs gs)

-- Helper: lift ⟶* through cata
⟶*-cata : ∀ F {A} {alg alg' : Term (⟦ F ⟧F A) A} →
          alg ⟶* alg' → cata F alg ⟶* cata F alg'
⟶*-cata F done = done
⟶*-cata F (step r rs) = step (⟶-cata r) (⟶*-cata F rs)

-- Helper: lift ⟶* through curry
⟶*-curry : ∀ {A B C} {f f' : Term (A * B) C} →
           f ⟶* f' → curry f ⟶* curry f'
⟶*-curry done = done
⟶*-curry (step r rs) = step (⟶-curry r) (⟶*-curry rs)

-- Helper: fmap preserves ⟶*
fmap-⟶* : ∀ F {A B} {f f' : Term A B} →
          f ⟶* f' → fmap F f ⟶* fmap F f'
fmap-⟶* Id rs = rs
fmap-⟶* (K _) _ = done
fmap-⟶* (F ⊕ G) rs = ⟶*-case (⟶*-∘-r inl (fmap-⟶* F rs)) (⟶*-∘-r inr (fmap-⟶* G rs))
fmap-⟶* (F ⊗ G) rs = ⟶*-pair (⟶*-∘-l fst (fmap-⟶* F rs)) (⟶*-∘-l snd (fmap-⟶* G rs))

-- Parallel implies multi-step (each parallel step is multiple single steps)
⟹→⟶* : ∀ {A B} {t u : Term A B} → t ⟹ u → t ⟶* u
⟹→⟶* ⟹-id = done
⟹→⟶* ⟹-fst = done
⟹→⟶* ⟹-snd = done
⟹→⟶* ⟹-inl = done
⟹→⟶* ⟹-inr = done
⟹→⟶* ⟹-terminal = done
⟹→⟶* ⟹-initial = done
⟹→⟶* ⟹-apply = done
⟹→⟶* (⟹-curry pf) = ⟶*-curry (⟹→⟶* pf)
⟹→⟶* ⟹-In = done
⟹→⟶* ⟹-Out = done
⟹→⟶* (⟹-∘ pf pg) = ⟶*-trans (⟶*-∘-l _ (⟹→⟶* pf)) (⟶*-∘-r _ (⟹→⟶* pg))
⟹→⟶* (⟹-pair pf pg) = ⟶*-pair (⟹→⟶* pf) (⟹→⟶* pg)
⟹→⟶* (⟹-case pf pg) = ⟶*-case (⟹→⟶* pf) (⟹→⟶* pg)
⟹→⟶* (⟹-cata {F} palg) = ⟶*-cata F (⟹→⟶* palg)
⟹→⟶* (⟹-id-l pf) = step id-left (⟹→⟶* pf)
⟹→⟶* (⟹-id-r pf) = step id-right (⟹→⟶* pf)
⟹→⟶* (⟹-fst-β pf pg) = ⟶*-trans (⟶*-∘-r fst (⟶*-pair (⟹→⟶* pf) (⟹→⟶* pg))) (step fst-pair done)
⟹→⟶* (⟹-snd-β pf pg) = ⟶*-trans (⟶*-∘-r snd (⟶*-pair (⟹→⟶* pf) (⟹→⟶* pg))) (step snd-pair done)
⟹→⟶* (⟹-inl-β pf pg) = ⟶*-trans (⟶*-∘-l inl (⟶*-case (⟹→⟶* pf) (⟹→⟶* pg))) (step case-inl done)
⟹→⟶* (⟹-inr-β pf pg) = ⟶*-trans (⟶*-∘-l inr (⟶*-case (⟹→⟶* pf) (⟹→⟶* pg))) (step case-inr done)
⟹→⟶* (⟹-cata-β {F} palg) =
  ⟶*-trans (⟶*-∘-l In (⟶*-cata F (⟹→⟶* palg)))
    (step cata-β done)
⟹→⟶* ⟹-η-pair = step eta-pair done
⟹→⟶* ⟹-η-case = step eta-case done
⟹→⟶* (⟹-η-curry pf) = ⟶*-trans (⟶*-curry (⟶*-∘-r apply (⟶*-pair (⟶*-∘-l fst (⟹→⟶* pf)) done))) (step curry-η done)
⟹→⟶* (⟹-curry-β pf pg) =
  -- (apply ∘ ⟨ curry f , g ⟩) ⟶* (f' ∘ ⟨ id , g' ⟩)
  ⟶*-trans (⟶*-∘-r apply (⟶*-pair (⟶*-curry (⟹→⟶* pf)) (⟹→⟶* pg)))
    (step curry-β done)
⟹→⟶* (⟹-curry-β-ext pf ph pg) =
  -- (apply ∘ ⟨ curry f ∘ h , g ⟩) ⟶* (f' ∘ ⟨ h' , g' ⟩)
  -- Step 1: apply curry-β-ext primitive
  -- Step 2: reduce f to f' on left, ⟨h,g⟩ to ⟨h',g'⟩ on right
  ⟶*-trans (step curry-β-ext done)
           (⟶*-trans (⟶*-∘-l _ (⟹→⟶* pf))
                     (⟶*-∘-r _ (⟶*-pair (⟹→⟶* ph) (⟹→⟶* pg))))
⟹→⟶* (⟹-out-in F) = step (out-in F) done
⟹→⟶* (⟹-in-out F) = step (in-out F) done
⟹→⟶* (⟹-assoc-l pf pg ph) =
  -- (f ∘ (g ∘ h)) ⟶* ((f' ∘ g') ∘ h')
  ⟶*-trans (⟶*-∘-l _ (⟹→⟶* pf))           -- (f ∘ ...) ⟶* (f' ∘ ...)
    (⟶*-trans (⟶*-∘-r _ (⟶*-∘-l _ (⟹→⟶* pg)))  -- (f' ∘ (g ∘ h)) ⟶* (f' ∘ (g' ∘ h))
      (⟶*-trans (⟶*-∘-r _ (⟶*-∘-r _ (⟹→⟶* ph))) -- (f' ∘ (g' ∘ h)) ⟶* (f' ∘ (g' ∘ h'))
        (step assoc-l done)))                    -- (f' ∘ (g' ∘ h')) ⟶ ((f' ∘ g') ∘ h')
⟹→⟶* (⟹-assoc-r pf pg ph) =
  -- ((f ∘ g) ∘ h) ⟶* (f' ∘ (g' ∘ h'))
  ⟶*-trans (⟶*-∘-l _ (⟶*-∘-l _ (⟹→⟶* pf)))  -- ((f ∘ g) ∘ h) ⟶* ((f' ∘ g) ∘ h)
    (⟶*-trans (⟶*-∘-l _ (⟶*-∘-r _ (⟹→⟶* pg))) -- ((f' ∘ g) ∘ h) ⟶* ((f' ∘ g') ∘ h)
      (⟶*-trans (⟶*-∘-r _ (⟹→⟶* ph))          -- ((f' ∘ g') ∘ h) ⟶* ((f' ∘ g') ∘ h')
        (step assoc-r done)))                  -- ((f' ∘ g') ∘ h') ⟶ (f' ∘ (g' ∘ h'))
⟹→⟶* (⟹-pair-comp pf pg ph) =
  -- (⟨ f , g ⟩ ∘ h) ⟶* ⟨ f' ∘ h' , g' ∘ h' ⟩
  ⟶*-trans (⟶*-∘-l _ (⟶*-pair (⟹→⟶* pf) (⟹→⟶* pg)))  -- (⟨ f , g ⟩ ∘ h) ⟶* (⟨ f' , g' ⟩ ∘ h)
    (⟶*-trans (⟶*-∘-r _ (⟹→⟶* ph))                   -- (⟨ f' , g' ⟩ ∘ h) ⟶* (⟨ f' , g' ⟩ ∘ h')
      (step pair-comp done))                          -- (⟨ f' , g' ⟩ ∘ h') ⟶ ⟨ f' ∘ h' , g' ∘ h' ⟩

-- ⟹* implies ⟶*
⟹*→⟶* : ∀ {A B} {t u : Term A B} → t ⟹* u → t ⟶* u
⟹*→⟶* done⟹ = done
⟹*→⟶* (step⟹ p ps) = ⟶*-trans (⟹→⟶* p) (⟹*→⟶* ps)

------------------------------------------------------------------------
-- Normal Form Definition
--
-- A term is in normal form if no reduction applies.
-- Defined here (in CCC) because it only depends on Term and ⟶.
------------------------------------------------------------------------

IsNormalForm : ∀ {A B} → Term A B → Set
IsNormalForm t = ∀ {u} → ¬ (t ⟶ u)

-- End of minimal CCC for Level0
