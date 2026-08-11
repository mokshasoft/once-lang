------------------------------------------------------------------------
-- Theory.Syntax.Bootstrap.CCTB.ParallelReduction
--
-- Parallel reduction on Takahashi's CCTB syntax, plus the bridges
-- connecting it to _⟶*_.
--
--   ⟶→⟹   : single step is a parallel step
--   ⟹→⟶*  : a parallel step expands to finitely many single steps
--   ⟶*→⟹* / ⟹*→⟶* : the closures agree.
--
-- Scope: the bridges. The diamond property of _⟹_ is proven elsewhere.
------------------------------------------------------------------------

module Theory.Syntax.Bootstrap.CCTB.ParallelReduction where

open import Theory.Syntax.Bootstrap.CCTB

------------------------------------------------------------------------
-- Parallel reduction.
------------------------------------------------------------------------

data _⟹_ : ∀ {A B} → Term A B → Term A B → Set where
  -- Atomic reflexivity
  ⟹-id       : ∀ {A}     → id {A} ⟹ id
  ⟹-fst      : ∀ {A B}   → fst {A} {B} ⟹ fst
  ⟹-snd      : ∀ {A B}   → snd {A} {B} ⟹ snd
  ⟹-terminal : ∀ {A}     → terminal {A} ⟹ terminal

  -- Congruence
  ⟹-∘    : ∀ {A B C} {f f' : Term B C} {g g' : Term A B} →
           f ⟹ f' → g ⟹ g' → (f ∘ g) ⟹ (f' ∘ g')
  ⟹-pair : ∀ {A B C} {f f' : Term C A} {g g' : Term C B} →
           f ⟹ f' → g ⟹ g' → ⟨ f , g ⟩ ⟹ ⟨ f' , g' ⟩

  -- β / η
  ⟹-id-l    : ∀ {A B} {f f' : Term A B} →
              f ⟹ f' → (id ∘ f) ⟹ f'
  ⟹-id-r    : ∀ {A B} {f f' : Term A B} →
              f ⟹ f' → (f ∘ id) ⟹ f'
  ⟹-fst-β   : ∀ {A B C} {f f' : Term C A} {g g' : Term C B} →
              f ⟹ f' → g ⟹ g' → (fst ∘ ⟨ f , g ⟩) ⟹ f'
  ⟹-snd-β   : ∀ {A B C} {f f' : Term C A} {g g' : Term C B} →
              f ⟹ f' → g ⟹ g' → (snd ∘ ⟨ f , g ⟩) ⟹ g'
  ⟹-η-pair  : ∀ {A B} → ⟨ fst {A} {B} , snd {A} {B} ⟩ ⟹ id

  -- Terminal uniqueness
  ⟹-term-unique : ∀ {A B} {f f' : Term A B} →
                  f ⟹ f' → (terminal ∘ f) ⟹ terminal

  -- Associativity (both directions)
  ⟹-assoc-l : ∀ {A B C D} {f f' : Term C D} {g g' : Term B C} {h h' : Term A B} →
              f ⟹ f' → g ⟹ g' → h ⟹ h' →
              (f ∘ (g ∘ h)) ⟹ ((f' ∘ g') ∘ h')
  ⟹-assoc-r : ∀ {A B C D} {f f' : Term C D} {g g' : Term B C} {h h' : Term A B} →
              f ⟹ f' → g ⟹ g' → h ⟹ h' →
              ((f ∘ g) ∘ h) ⟹ (f' ∘ (g' ∘ h'))

  -- Pair distribution
  ⟹-pair-comp : ∀ {A B C D} {f f' : Term C A} {g g' : Term C B} {h h' : Term D C} →
                f ⟹ f' → g ⟹ g' → h ⟹ h' →
                (⟨ f , g ⟩ ∘ h) ⟹ ⟨ f' ∘ h' , g' ∘ h' ⟩

infix 4 _⟹_

------------------------------------------------------------------------
-- Reflexivity.
------------------------------------------------------------------------

⟹-refl : ∀ {A B} (t : Term A B) → t ⟹ t
⟹-refl id         = ⟹-id
⟹-refl (f ∘ g)    = ⟹-∘ (⟹-refl f) (⟹-refl g)
⟹-refl terminal   = ⟹-terminal
⟹-refl fst        = ⟹-fst
⟹-refl snd        = ⟹-snd
⟹-refl ⟨ f , g ⟩  = ⟹-pair (⟹-refl f) (⟹-refl g)

------------------------------------------------------------------------
-- Bridge 1: single step → parallel step.
------------------------------------------------------------------------

⟶→⟹ : ∀ {A B} {t u : Term A B} → t ⟶ u → t ⟹ u
⟶→⟹ id-left        = ⟹-id-l (⟹-refl _)
⟶→⟹ id-right       = ⟹-id-r (⟹-refl _)
⟶→⟹ assoc-l        = ⟹-assoc-l (⟹-refl _) (⟹-refl _) (⟹-refl _)
⟶→⟹ assoc-r        = ⟹-assoc-r (⟹-refl _) (⟹-refl _) (⟹-refl _)
⟶→⟹ fst-pair       = ⟹-fst-β (⟹-refl _) (⟹-refl _)
⟶→⟹ snd-pair       = ⟹-snd-β (⟹-refl _) (⟹-refl _)
⟶→⟹ eta-pair       = ⟹-η-pair
⟶→⟹ pair-comp      = ⟹-pair-comp (⟹-refl _) (⟹-refl _) (⟹-refl _)
⟶→⟹ term-unique    = ⟹-term-unique (⟹-refl _)
⟶→⟹ (⟶-∘-l r)      = ⟹-∘ (⟶→⟹ r) (⟹-refl _)
⟶→⟹ (⟶-∘-r r)      = ⟹-∘ (⟹-refl _) (⟶→⟹ r)
⟶→⟹ (⟶-pair-l r)   = ⟹-pair (⟶→⟹ r) (⟹-refl _)
⟶→⟹ (⟶-pair-r r)   = ⟹-pair (⟹-refl _) (⟶→⟹ r)

------------------------------------------------------------------------
-- Helpers for lifting ⟶* through contexts.
------------------------------------------------------------------------

⟶*-trans : ∀ {A B} {t u v : Term A B} → t ⟶* u → u ⟶* v → t ⟶* v
⟶*-trans done        ys = ys
⟶*-trans (r ∷ rs)    ys = r ∷ ⟶*-trans rs ys

⟶*-∘-l : ∀ {A B C} {f f' : Term B C} (g : Term A B) →
         f ⟶* f' → (f ∘ g) ⟶* (f' ∘ g)
⟶*-∘-l g done       = done
⟶*-∘-l g (r ∷ rs)   = ⟶-∘-l r ∷ ⟶*-∘-l g rs

⟶*-∘-r : ∀ {A B C} (f : Term B C) {g g' : Term A B} →
         g ⟶* g' → (f ∘ g) ⟶* (f ∘ g')
⟶*-∘-r f done       = done
⟶*-∘-r f (r ∷ rs)   = ⟶-∘-r r ∷ ⟶*-∘-r f rs

⟶*-pair : ∀ {A B C} {f f' : Term C A} {g g' : Term C B} →
          f ⟶* f' → g ⟶* g' → ⟨ f , g ⟩ ⟶* ⟨ f' , g' ⟩
⟶*-pair done        done        = done
⟶*-pair done        (r ∷ rs)    = ⟶-pair-r r ∷ ⟶*-pair done rs
⟶*-pair (r ∷ rs)    gs          = ⟶-pair-l r ∷ ⟶*-pair rs gs

------------------------------------------------------------------------
-- Bridge 2: parallel step → finite single-step sequence.
------------------------------------------------------------------------

⟹→⟶* : ∀ {A B} {t u : Term A B} → t ⟹ u → t ⟶* u
⟹→⟶* ⟹-id       = done
⟹→⟶* ⟹-fst      = done
⟹→⟶* ⟹-snd      = done
⟹→⟶* ⟹-terminal = done
⟹→⟶* (⟹-∘ pf pg) =
  ⟶*-trans (⟶*-∘-l _ (⟹→⟶* pf)) (⟶*-∘-r _ (⟹→⟶* pg))
⟹→⟶* (⟹-pair pf pg) =
  ⟶*-pair (⟹→⟶* pf) (⟹→⟶* pg)
⟹→⟶* (⟹-id-l pf) =
  id-left ∷ ⟹→⟶* pf
⟹→⟶* (⟹-id-r pf) =
  id-right ∷ ⟹→⟶* pf
⟹→⟶* (⟹-fst-β pf pg) =
  ⟶*-trans (⟶*-∘-r fst (⟶*-pair (⟹→⟶* pf) (⟹→⟶* pg)))
           (fst-pair ∷ done)
⟹→⟶* (⟹-snd-β pf pg) =
  ⟶*-trans (⟶*-∘-r snd (⟶*-pair (⟹→⟶* pf) (⟹→⟶* pg)))
           (snd-pair ∷ done)
⟹→⟶* ⟹-η-pair =
  eta-pair ∷ done
⟹→⟶* (⟹-term-unique pf) =
  term-unique ∷ done
⟹→⟶* (⟹-assoc-l pf pg ph) =
  ⟶*-trans (⟶*-∘-l _ (⟹→⟶* pf))
    (⟶*-trans (⟶*-∘-r _ (⟶*-∘-l _ (⟹→⟶* pg)))
      (⟶*-trans (⟶*-∘-r _ (⟶*-∘-r _ (⟹→⟶* ph)))
        (assoc-l ∷ done)))
⟹→⟶* (⟹-assoc-r pf pg ph) =
  ⟶*-trans (⟶*-∘-l _ (⟶*-∘-l _ (⟹→⟶* pf)))
    (⟶*-trans (⟶*-∘-l _ (⟶*-∘-r _ (⟹→⟶* pg)))
      (⟶*-trans (⟶*-∘-r _ (⟹→⟶* ph))
        (assoc-r ∷ done)))
⟹→⟶* (⟹-pair-comp pf pg ph) =
  ⟶*-trans (⟶*-∘-l _ (⟶*-pair (⟹→⟶* pf) (⟹→⟶* pg)))
    (⟶*-trans (⟶*-∘-r _ (⟹→⟶* ph))
      (pair-comp ∷ done))

------------------------------------------------------------------------
-- Closures agree.
------------------------------------------------------------------------

data _⟹*_ : ∀ {A B} → Term A B → Term A B → Set where
  done⟹ : ∀ {A B} {t : Term A B} → t ⟹* t
  _∷⟹_  : ∀ {A B} {t u v : Term A B} → t ⟹ u → u ⟹* v → t ⟹* v

infix 4 _⟹*_

⟶*→⟹* : ∀ {A B} {t u : Term A B} → t ⟶* u → t ⟹* u
⟶*→⟹* done       = done⟹
⟶*→⟹* (r ∷ rs)   = ⟶→⟹ r ∷⟹ ⟶*→⟹* rs

⟹*→⟶* : ∀ {A B} {t u : Term A B} → t ⟹* u → t ⟶* u
⟹*→⟶* done⟹       = done
⟹*→⟶* (p ∷⟹ ps)   = ⟶*-trans (⟹→⟶* p) (⟹*→⟶* ps)
