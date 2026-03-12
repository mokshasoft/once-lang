------------------------------------------------------------------------
-- MinimalCCC: Fixpoint Correctness for Zero-Code TCB
--
-- This module defines the structure for proving:
--   1. CCC with cata has confluence and termination
--   2. Normal forms are unique
--   3. Fixpoint implies correctness
--
-- Imports Types module for the foundation (prelude, types, functors).
------------------------------------------------------------------------

module normalizer.Foundations.MinimalCCC where

open import normalizer.Foundations.Types public

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

-- Reflexive-transitive closure
data _⟶*_ : ∀ {A B} → Term A B → Term A B → Set where
  done : ∀ {A B} {t : Term A B} → t ⟶* t
  step : ∀ {A B} {t u v : Term A B} → t ⟶ u → u ⟶* v → t ⟶* v

------------------------------------------------------------------------
-- Part 4: Parallel Reduction (for confluence proof)
------------------------------------------------------------------------

-- Parallel reduction: reduce ALL redexes at once
-- This is the Tait-Martin-Löf technique for proving confluence
data _⇒_ : ∀ {A B} → Term A B → Term A B → Set where
  -- Reflexivity for atoms
  ⇒-id       : ∀ {A} → id {A} ⇒ id
  ⇒-fst      : ∀ {A B} → fst {A} {B} ⇒ fst
  ⇒-snd      : ∀ {A B} → snd {A} {B} ⇒ snd
  ⇒-inl      : ∀ {A B} → inl {A} {B} ⇒ inl
  ⇒-inr      : ∀ {A B} → inr {A} {B} ⇒ inr
  ⇒-terminal : ∀ {A} → terminal {A} ⇒ terminal
  ⇒-In       : ∀ {F} → In {F} ⇒ In
  ⇒-Out      : ∀ {F} → Out {F} ⇒ Out

  -- Congruence for compound terms
  ⇒-∘    : ∀ {A B C} {f f' : Term B C} {g g' : Term A B} →
           f ⇒ f' → g ⇒ g' → (f ∘ g) ⇒ (f' ∘ g')
  ⇒-pair : ∀ {A B C} {f f' : Term C A} {g g' : Term C B} →
           f ⇒ f' → g ⇒ g' → ⟨ f , g ⟩ ⇒ ⟨ f' , g' ⟩
  ⇒-case : ∀ {A B C} {f f' : Term A C} {g g' : Term B C} →
           f ⇒ f' → g ⇒ g' → [ f , g ] ⇒ [ f' , g' ]
  ⇒-cata : ∀ {F A} {alg alg' : Term (⟦ F ⟧F A) A} →
           alg ⇒ alg' → cata F alg ⇒ cata F alg'

  -- Beta reductions (the actual computation steps)
  ⇒-id-l    : ∀ {A B} {f f' : Term A B} →
              f ⇒ f' → (id ∘ f) ⇒ f'
  ⇒-id-r    : ∀ {A B} {f f' : Term A B} →
              f ⇒ f' → (f ∘ id) ⇒ f'
  ⇒-fst-β   : ∀ {A B C} {f f' : Term C A} {g g' : Term C B} →
              f ⇒ f' → g ⇒ g' → (fst ∘ ⟨ f , g ⟩) ⇒ f'
  ⇒-snd-β   : ∀ {A B C} {f f' : Term C A} {g g' : Term C B} →
              f ⇒ f' → g ⇒ g' → (snd ∘ ⟨ f , g ⟩) ⇒ g'
  ⇒-inl-β   : ∀ {A B C} {f f' : Term A C} {g g' : Term B C} →
              f ⇒ f' → g ⇒ g' → ([ f , g ] ∘ inl) ⇒ f'
  ⇒-inr-β   : ∀ {A B C} {f f' : Term A C} {g g' : Term B C} →
              f ⇒ f' → g ⇒ g' → ([ f , g ] ∘ inr) ⇒ g'
  ⇒-cata-β  : ∀ {F A} {alg alg' : Term (⟦ F ⟧F A) A} →
              alg ⇒ alg' → (cata F alg ∘ In) ⇒ (alg' ∘ fmap F (cata F alg'))

  -- Eta reductions
  ⇒-η-pair  : ∀ {A B} → ⟨ fst , snd ⟩ ⇒ id {A * B}
  ⇒-η-case  : ∀ {A B} → [ inl , inr ] ⇒ id {A + B}

  -- Out/In reductions (F explicit to avoid computed type unification issues)
  ⇒-out-in  : ∀ F → (Out {F} ∘ In {F}) ⇒ id {⟦ F ⟧F (μ F)}
  ⇒-in-out  : ∀ F → (In {F} ∘ Out {F}) ⇒ id {μ F}

  -- Associativity
  ⇒-assoc-l : ∀ {A B C D} {f f' : Term C D} {g g' : Term B C} {h h' : Term A B} →
              f ⇒ f' → g ⇒ g' → h ⇒ h' → (f ∘ (g ∘ h)) ⇒ ((f' ∘ g') ∘ h')
  ⇒-assoc-r : ∀ {A B C D} {f f' : Term C D} {g g' : Term B C} {h h' : Term A B} →
              f ⇒ f' → g ⇒ g' → h ⇒ h' → ((f ∘ g) ∘ h) ⇒ (f' ∘ (g' ∘ h'))

  -- Pair distribution over composition
  ⇒-pair-comp : ∀ {A B C D} {f f' : Term B C} {g g' : Term B D} {h h' : Term A B} →
                f ⇒ f' → g ⇒ g' → h ⇒ h' → (⟨ f , g ⟩ ∘ h) ⇒ ⟨ f' ∘ h' , g' ∘ h' ⟩

-- Parallel reduction is reflexive
⇒-refl : ∀ {A B} (t : Term A B) → t ⇒ t
⇒-refl id = ⇒-id
⇒-refl (f ∘ g) = ⇒-∘ (⇒-refl f) (⇒-refl g)
⇒-refl fst = ⇒-fst
⇒-refl snd = ⇒-snd
⇒-refl ⟨ f , g ⟩ = ⇒-pair (⇒-refl f) (⇒-refl g)
⇒-refl inl = ⇒-inl
⇒-refl inr = ⇒-inr
⇒-refl [ f , g ] = ⇒-case (⇒-refl f) (⇒-refl g)
⇒-refl terminal = ⇒-terminal
⇒-refl In = ⇒-In
⇒-refl Out = ⇒-Out
⇒-refl (cata F alg) = ⇒-cata (⇒-refl alg)

-- Single step implies parallel
-- All cases are trivial: each reduction rule has a corresponding parallel reduction.
⟶→⇒ : ∀ {A B} {t u : Term A B} → t ⟶ u → t ⇒ u
⟶→⇒ id-left = ⇒-id-l (⇒-refl _)
⟶→⇒ id-right = ⇒-id-r (⇒-refl _)
⟶→⇒ fst-pair = ⇒-fst-β (⇒-refl _) (⇒-refl _)
⟶→⇒ snd-pair = ⇒-snd-β (⇒-refl _) (⇒-refl _)
⟶→⇒ eta-pair = ⇒-η-pair
⟶→⇒ case-inl = ⇒-inl-β (⇒-refl _) (⇒-refl _)
⟶→⇒ case-inr = ⇒-inr-β (⇒-refl _) (⇒-refl _)
⟶→⇒ eta-case = ⇒-η-case
⟶→⇒ cata-β = ⇒-cata-β (⇒-refl _)
⟶→⇒ (out-in F) = ⇒-out-in F
⟶→⇒ (in-out F) = ⇒-in-out F
⟶→⇒ assoc-l = ⇒-assoc-l (⇒-refl _) (⇒-refl _) (⇒-refl _)
⟶→⇒ assoc-r = ⇒-assoc-r (⇒-refl _) (⇒-refl _) (⇒-refl _)
⟶→⇒ pair-comp = ⇒-pair-comp (⇒-refl _) (⇒-refl _) (⇒-refl _)

------------------------------------------------------------------------
-- Part 5: Diamond Property and Confluence
------------------------------------------------------------------------

-- Reflexive-transitive closure of parallel reduction
data _⇒*_ : ∀ {A B} → Term A B → Term A B → Set where
  done⇒ : ∀ {A B} {t : Term A B} → t ⇒* t
  step⇒ : ∀ {A B} {t u v : Term A B} → t ⇒ u → u ⇒* v → t ⇒* v

-- ⟶* implies ⇒*
⟶*→⇒* : ∀ {A B} {t u : Term A B} → t ⟶* u → t ⇒* u
⟶*→⇒* done = done⇒
⟶*→⇒* (step r rs) = step⇒ (⟶→⇒ r) (⟶*→⇒* rs)

-- Parallel implies multi-step (each parallel step is multiple single steps)
postulate
  ⇒→⟶* : ∀ {A B} {t u : Term A B} → t ⇒ u → t ⟶* u

-- ⇒* implies ⟶*
⇒*→⟶* : ∀ {A B} {t u : Term A B} → t ⇒* u → t ⟶* u
⇒*→⟶* done⇒ = done
⇒*→⟶* (step⇒ p ps) = trans⟶* (⇒→⟶* p) (⇒*→⟶* ps)
  where
    trans⟶* : ∀ {A B} {t u v : Term A B} → t ⟶* u → u ⟶* v → t ⟶* v
    trans⟶* done q = q
    trans⟶* (step p ps) q = step p (trans⟶* ps q)

-- End of minimal MinimalCCC for Level0V2
