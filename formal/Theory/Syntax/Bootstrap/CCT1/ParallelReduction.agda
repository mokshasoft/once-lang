------------------------------------------------------------------------
-- Theory.Syntax.Bootstrap.CCT1.ParallelReduction
--
-- Parallel reduction on Takahashi's CCT1 syntax, along with the two
-- bridges connecting it to _⟶*_:
--
--   ⟶→⟹   : single step is a parallel step
--   ⟹→⟶*  : a parallel step expands to finitely many single steps
--   ⟶*→⟹* : the reflexive-transitive closures agree.
--
-- Ported from bootstrap/normalizer/Syntax/CCC.agda
-- (stripped of the cata/In/Out CCT3 additions; kept only the CCT1
-- fragment).
--
-- This is the infrastructure for a Takahashi-style confluence proof.
-- The diamond property of _⟹_ itself — the payload that closes
-- confluence — is NOT proven here; that proof is the next step in
-- the chain (Theory.Syntax.Bootstrap.CCT1.Diamond).
------------------------------------------------------------------------

module Theory.Syntax.Bootstrap.CCT1.ParallelReduction where

open import Theory.Syntax.Bootstrap.CCT1

------------------------------------------------------------------------
-- Parallel reduction: reduce all in-situ redexes at once.
------------------------------------------------------------------------

data _⟹_ : ∀ {A B} → Term A B → Term A B → Set where
  -- Reflexivity for atoms
  ⟹-id       : ∀ {A} → id {A} ⟹ id
  ⟹-fst      : ∀ {A B} → fst {A} {B} ⟹ fst
  ⟹-snd      : ∀ {A B} → snd {A} {B} ⟹ snd
  ⟹-terminal : ∀ {A} → terminal {A} ⟹ terminal
  ⟹-apply    : ∀ {A B} → apply {A} {B} ⟹ apply

  -- Congruence for compound terms
  ⟹-∘    : ∀ {A B C} {f f' : Term B C} {g g' : Term A B} →
           f ⟹ f' → g ⟹ g' → (f ∘ g) ⟹ (f' ∘ g')
  ⟹-pair : ∀ {A B C} {f f' : Term C A} {g g' : Term C B} →
           f ⟹ f' → g ⟹ g' → ⟨ f , g ⟩ ⟹ ⟨ f' , g' ⟩
  ⟹-curry : ∀ {A B C} {f f' : Term (A × B) C} →
            f ⟹ f' → curry f ⟹ curry f'

  -- β-reductions: fire at the top, subterms parallel-reduce.
  ⟹-id-l    : ∀ {A B} {f f' : Term A B} →
              f ⟹ f' → (id ∘ f) ⟹ f'
  ⟹-id-r    : ∀ {A B} {f f' : Term A B} →
              f ⟹ f' → (f ∘ id) ⟹ f'
  ⟹-fst-β   : ∀ {A B C} {f f' : Term C A} {g g' : Term C B} →
              f ⟹ f' → g ⟹ g' → (fst ∘ ⟨ f , g ⟩) ⟹ f'
  ⟹-snd-β   : ∀ {A B C} {f f' : Term C A} {g g' : Term C B} →
              f ⟹ f' → g ⟹ g' → (snd ∘ ⟨ f , g ⟩) ⟹ g'

  -- η-reductions
  ⟹-η-pair  : ∀ {A B} → ⟨ fst {A} {B} , snd {A} {B} ⟩ ⟹ id
  ⟹-η-curry : ∀ {A B C} {f f' : Term A (B ⇒ C)} →
              f ⟹ f' → curry (apply ∘ ⟨ f ∘ fst , snd ⟩) ⟹ f'

  -- Curry β variants
  ⟹-curry-β : ∀ {A B C} {f f' : Term (A × B) C} {g g' : Term A B} →
              f ⟹ f' → g ⟹ g' →
              (apply ∘ ⟨ curry f , g ⟩) ⟹ (f' ∘ ⟨ id , g' ⟩)
  ⟹-curry-β-ext : ∀ {X A B C} {f f' : Term (A × B) C}
                    {h h' : Term X A} {g g' : Term X B} →
                  f ⟹ f' → h ⟹ h' → g ⟹ g' →
                  (apply ∘ ⟨ curry f ∘ h , g ⟩) ⟹ (f' ∘ ⟨ h' , g' ⟩)

  -- Terminal uniqueness
  ⟹-term-unique : ∀ {A B} {f f' : Term A B} →
                  f ⟹ f' → (terminal ∘ f) ⟹ terminal

  -- Associativity (both directions — Takahashi-style)
  ⟹-assoc-l : ∀ {A B C D} {f f' : Term C D} {g g' : Term B C} {h h' : Term A B} →
              f ⟹ f' → g ⟹ g' → h ⟹ h' →
              (f ∘ (g ∘ h)) ⟹ ((f' ∘ g') ∘ h')
  ⟹-assoc-r : ∀ {A B C D} {f f' : Term C D} {g g' : Term B C} {h h' : Term A B} →
              f ⟹ f' → g ⟹ g' → h ⟹ h' →
              ((f ∘ g) ∘ h) ⟹ (f' ∘ (g' ∘ h'))

  -- Pair distribution over composition
  ⟹-pair-comp : ∀ {A B C D} {f f' : Term C A} {g g' : Term C B} {h h' : Term D C} →
                f ⟹ f' → g ⟹ g' → h ⟹ h' →
                (⟨ f , g ⟩ ∘ h) ⟹ ⟨ f' ∘ h' , g' ∘ h' ⟩

infix 4 _⟹_

------------------------------------------------------------------------
-- Reflexivity of parallel reduction.
------------------------------------------------------------------------

⟹-refl : ∀ {A B} (t : Term A B) → t ⟹ t
⟹-refl id         = ⟹-id
⟹-refl (f ∘ g)    = ⟹-∘ (⟹-refl f) (⟹-refl g)
⟹-refl terminal   = ⟹-terminal
⟹-refl fst        = ⟹-fst
⟹-refl snd        = ⟹-snd
⟹-refl ⟨ f , g ⟩  = ⟹-pair (⟹-refl f) (⟹-refl g)
⟹-refl (curry f)  = ⟹-curry (⟹-refl f)
⟹-refl apply      = ⟹-apply

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
⟶→⟹ curry-β        = ⟹-curry-β (⟹-refl _) (⟹-refl _)
⟶→⟹ curry-β-ext    = ⟹-curry-β-ext (⟹-refl _) (⟹-refl _) (⟹-refl _)
⟶→⟹ curry-η        = ⟹-η-curry (⟹-refl _)
⟶→⟹ (⟶-∘-l r)      = ⟹-∘ (⟶→⟹ r) (⟹-refl _)
⟶→⟹ (⟶-∘-r r)      = ⟹-∘ (⟹-refl _) (⟶→⟹ r)
⟶→⟹ (⟶-pair-l r)   = ⟹-pair (⟶→⟹ r) (⟹-refl _)
⟶→⟹ (⟶-pair-r r)   = ⟹-pair (⟹-refl _) (⟶→⟹ r)
⟶→⟹ (⟶-curry r)    = ⟹-curry (⟶→⟹ r)

------------------------------------------------------------------------
-- Lifting ⟶* through context constructors.
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

⟶*-curry : ∀ {A B C} {f f' : Term (A × B) C} →
           f ⟶* f' → curry f ⟶* curry f'
⟶*-curry done     = done
⟶*-curry (r ∷ rs) = ⟶-curry r ∷ ⟶*-curry rs

------------------------------------------------------------------------
-- Bridge 2: parallel step → finite single-step sequence.
------------------------------------------------------------------------

⟹→⟶* : ∀ {A B} {t u : Term A B} → t ⟹ u → t ⟶* u
⟹→⟶* ⟹-id       = done
⟹→⟶* ⟹-fst      = done
⟹→⟶* ⟹-snd      = done
⟹→⟶* ⟹-terminal = done
⟹→⟶* ⟹-apply    = done
⟹→⟶* (⟹-∘ pf pg) =
  ⟶*-trans (⟶*-∘-l _ (⟹→⟶* pf)) (⟶*-∘-r _ (⟹→⟶* pg))
⟹→⟶* (⟹-pair pf pg) =
  ⟶*-pair (⟹→⟶* pf) (⟹→⟶* pg)
⟹→⟶* (⟹-curry pf) =
  ⟶*-curry (⟹→⟶* pf)
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
⟹→⟶* (⟹-η-curry pf) =
  ⟶*-trans
    (⟶*-curry (⟶*-∘-r apply
       (⟶*-pair (⟶*-∘-l fst (⟹→⟶* pf)) done)))
    (curry-η ∷ done)
⟹→⟶* (⟹-curry-β pf pg) =
  ⟶*-trans (⟶*-∘-r apply
              (⟶*-pair (⟶*-curry (⟹→⟶* pf)) (⟹→⟶* pg)))
           (curry-β ∷ done)
⟹→⟶* (⟹-curry-β-ext pf ph pg) =
  ⟶*-trans
    (curry-β-ext ∷ done)
    (⟶*-trans (⟶*-∘-l _ (⟹→⟶* pf))
              (⟶*-∘-r _ (⟶*-pair (⟹→⟶* ph) (⟹→⟶* pg))))
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
-- Reflexive-transitive closure of parallel reduction; agreement with _⟶*_.
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
