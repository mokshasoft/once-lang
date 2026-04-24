------------------------------------------------------------------------
-- Theory.Syntax.Bootstrap.CCT3.ParallelReduction
--
-- Parallel reduction on Takahashi's CCT3 syntax, plus bridges.
-- Extends CCT2's pattern with In / Out / cata / fmap constructors.
------------------------------------------------------------------------

{-# OPTIONS --no-positivity-check #-}

module Theory.Syntax.Bootstrap.CCT3.ParallelReduction where

open import Theory.Syntax.Bootstrap.CCT3

------------------------------------------------------------------------
-- Parallel reduction.
------------------------------------------------------------------------

data _⟹_ : ∀ {A B} → Term A B → Term A B → Set where
  ⟹-id       : ∀ {A}     → id {A} ⟹ id
  ⟹-fst      : ∀ {A B}   → fst {A} {B} ⟹ fst
  ⟹-snd      : ∀ {A B}   → snd {A} {B} ⟹ snd
  ⟹-terminal : ∀ {A}     → terminal {A} ⟹ terminal
  ⟹-apply    : ∀ {A B}   → apply {A} {B} ⟹ apply
  ⟹-inl      : ∀ {A B}   → inl {A} {B} ⟹ inl
  ⟹-inr      : ∀ {A B}   → inr {A} {B} ⟹ inr
  ⟹-initial  : ∀ {A}     → initial {A} ⟹ initial
  ⟹-In       : ∀ {F}     → In  {F} ⟹ In
  ⟹-Out      : ∀ {F}     → Out {F} ⟹ Out

  ⟹-∘    : ∀ {A B C} {f f' : Term B C} {g g' : Term A B} →
           f ⟹ f' → g ⟹ g' → (f ∘ g) ⟹ (f' ∘ g')
  ⟹-pair : ∀ {A B C} {f f' : Term C A} {g g' : Term C B} →
           f ⟹ f' → g ⟹ g' → ⟨ f , g ⟩ ⟹ ⟨ f' , g' ⟩
  ⟹-case : ∀ {A B C} {f f' : Term A C} {g g' : Term B C} →
           f ⟹ f' → g ⟹ g' → [ f , g ] ⟹ [ f' , g' ]
  ⟹-curry : ∀ {A B C} {f f' : Term (A × B) C} →
            f ⟹ f' → curry f ⟹ curry f'
  ⟹-cata : ∀ {F A} {alg alg' : Term (F A) A} →
           alg ⟹ alg' → cata {F} alg ⟹ cata {F} alg'
  ⟹-fmap : ∀ {F A B} {f f' : Term A B} →
           f ⟹ f' → fmap {F} f ⟹ fmap {F} f'

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
  ⟹-η-pair  : ∀ {A B} → ⟨ fst {A} {B} , snd {A} {B} ⟩ ⟹ id
  ⟹-η-case  : ∀ {A B} → [ inl {A} {B} , inr {A} {B} ] ⟹ id
  ⟹-η-curry : ∀ {A B C} {f f' : Term A (B ⇒ C)} →
              f ⟹ f' → curry (apply ∘ ⟨ f ∘ fst , snd ⟩) ⟹ f'

  ⟹-term-unique : ∀ {A B} {f f' : Term A B} →
                  f ⟹ f' → (terminal ∘ f) ⟹ terminal
  ⟹-init-unique : ∀ {A} {f : Term Void A} → f ⟹ initial

  ⟹-assoc-l : ∀ {A B C D} {f f' : Term C D} {g g' : Term B C} {h h' : Term A B} →
              f ⟹ f' → g ⟹ g' → h ⟹ h' →
              (f ∘ (g ∘ h)) ⟹ ((f' ∘ g') ∘ h')
  ⟹-assoc-r : ∀ {A B C D} {f f' : Term C D} {g g' : Term B C} {h h' : Term A B} →
              f ⟹ f' → g ⟹ g' → h ⟹ h' →
              ((f ∘ g) ∘ h) ⟹ (f' ∘ (g' ∘ h'))

  ⟹-pair-comp : ∀ {A B C D} {f f' : Term C A} {g g' : Term C B} {h h' : Term D C} →
                f ⟹ f' → g ⟹ g' → h ⟹ h' →
                (⟨ f , g ⟩ ∘ h) ⟹ ⟨ f' ∘ h' , g' ∘ h' ⟩
  ⟹-case-dist : ∀ {A B C D} {h h' : Term C D} {f f' : Term A C} {g g' : Term B C} →
                h ⟹ h' → f ⟹ f' → g ⟹ g' →
                (h ∘ [ f , g ]) ⟹ [ h' ∘ f' , h' ∘ g' ]

  ⟹-curry-β : ∀ {A B C} {f f' : Term (A × B) C} {g g' : Term A B} →
              f ⟹ f' → g ⟹ g' →
              (apply ∘ ⟨ curry f , g ⟩) ⟹ (f' ∘ ⟨ id , g' ⟩)
  ⟹-curry-β-ext : ∀ {X A B C} {f f' : Term (A × B) C}
                    {h h' : Term X A} {g g' : Term X B} →
                  f ⟹ f' → h ⟹ h' → g ⟹ g' →
                  (apply ∘ ⟨ curry f ∘ h , g ⟩) ⟹ (f' ∘ ⟨ h' , g' ⟩)

  ⟹-out-in  : ∀ {F} → (Out {F} ∘ In {F}) ⟹ id
  ⟹-in-out  : ∀ {F} → (In  {F} ∘ Out {F}) ⟹ id
  ⟹-cata-β  : ∀ {F A} {alg alg' : Term (F A) A} →
              alg ⟹ alg' →
              (cata {F} alg ∘ In {F}) ⟹ (alg' ∘ fmap {F} (cata {F} alg'))

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
⟹-refl (curry f)  = ⟹-curry (⟹-refl f)
⟹-refl apply      = ⟹-apply
⟹-refl initial    = ⟹-initial
⟹-refl inl        = ⟹-inl
⟹-refl inr        = ⟹-inr
⟹-refl [ f , g ]  = ⟹-case (⟹-refl f) (⟹-refl g)
⟹-refl In         = ⟹-In
⟹-refl Out        = ⟹-Out
⟹-refl (cata alg) = ⟹-cata (⟹-refl alg)
⟹-refl (fmap f)   = ⟹-fmap (⟹-refl f)

------------------------------------------------------------------------
-- ⟶* helpers.
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

⟶*-case : ∀ {A B C} {f f' : Term A C} {g g' : Term B C} →
          f ⟶* f' → g ⟶* g' → [ f , g ] ⟶* [ f' , g' ]
⟶*-case done       done       = done
⟶*-case done       (r ∷ rs)   = ⟶-case-r r ∷ ⟶*-case done rs
⟶*-case (r ∷ rs)   gs         = ⟶-case-l r ∷ ⟶*-case rs gs

⟶*-curry : ∀ {A B C} {f f' : Term (A × B) C} →
           f ⟶* f' → curry f ⟶* curry f'
⟶*-curry done     = done
⟶*-curry (r ∷ rs) = ⟶-curry r ∷ ⟶*-curry rs

⟶*-cata : ∀ {F A} {alg alg' : Term (F A) A} →
          alg ⟶* alg' → cata {F} alg ⟶* cata {F} alg'
⟶*-cata done     = done
⟶*-cata (r ∷ rs) = ⟶-cata r ∷ ⟶*-cata rs

⟶*-fmap : ∀ {F A B} {f f' : Term A B} →
          f ⟶* f' → fmap {F} f ⟶* fmap {F} f'
⟶*-fmap done     = done
⟶*-fmap (r ∷ rs) = ⟶-fmap r ∷ ⟶*-fmap rs

------------------------------------------------------------------------
-- Bridge 1.
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
⟶→⟹ case-inl       = ⟹-inl-β (⟹-refl _) (⟹-refl _)
⟶→⟹ case-inr       = ⟹-inr-β (⟹-refl _) (⟹-refl _)
⟶→⟹ eta-case       = ⟹-η-case
⟶→⟹ case-dist      = ⟹-case-dist (⟹-refl _) (⟹-refl _) (⟹-refl _)
⟶→⟹ initial-unique = ⟹-init-unique
⟶→⟹ curry-β        = ⟹-curry-β (⟹-refl _) (⟹-refl _)
⟶→⟹ curry-β-ext    = ⟹-curry-β-ext (⟹-refl _) (⟹-refl _) (⟹-refl _)
⟶→⟹ curry-η        = ⟹-η-curry (⟹-refl _)
⟶→⟹ out-in         = ⟹-out-in
⟶→⟹ in-out         = ⟹-in-out
⟶→⟹ cata-β         = ⟹-cata-β (⟹-refl _)
⟶→⟹ (⟶-∘-l r)      = ⟹-∘ (⟶→⟹ r) (⟹-refl _)
⟶→⟹ (⟶-∘-r r)      = ⟹-∘ (⟹-refl _) (⟶→⟹ r)
⟶→⟹ (⟶-pair-l r)   = ⟹-pair (⟶→⟹ r) (⟹-refl _)
⟶→⟹ (⟶-pair-r r)   = ⟹-pair (⟹-refl _) (⟶→⟹ r)
⟶→⟹ (⟶-case-l r)   = ⟹-case (⟶→⟹ r) (⟹-refl _)
⟶→⟹ (⟶-case-r r)   = ⟹-case (⟹-refl _) (⟶→⟹ r)
⟶→⟹ (⟶-curry r)    = ⟹-curry (⟶→⟹ r)
⟶→⟹ (⟶-cata r)     = ⟹-cata (⟶→⟹ r)
⟶→⟹ (⟶-fmap r)     = ⟹-fmap (⟶→⟹ r)

------------------------------------------------------------------------
-- Bridge 2.
------------------------------------------------------------------------

⟹→⟶* : ∀ {A B} {t u : Term A B} → t ⟹ u → t ⟶* u
⟹→⟶* ⟹-id       = done
⟹→⟶* ⟹-fst      = done
⟹→⟶* ⟹-snd      = done
⟹→⟶* ⟹-terminal = done
⟹→⟶* ⟹-apply    = done
⟹→⟶* ⟹-inl      = done
⟹→⟶* ⟹-inr      = done
⟹→⟶* ⟹-initial  = done
⟹→⟶* ⟹-In       = done
⟹→⟶* ⟹-Out      = done
⟹→⟶* (⟹-∘ pf pg) =
  ⟶*-trans (⟶*-∘-l _ (⟹→⟶* pf)) (⟶*-∘-r _ (⟹→⟶* pg))
⟹→⟶* (⟹-pair pf pg) =
  ⟶*-pair (⟹→⟶* pf) (⟹→⟶* pg)
⟹→⟶* (⟹-case pf pg) =
  ⟶*-case (⟹→⟶* pf) (⟹→⟶* pg)
⟹→⟶* (⟹-curry pf) =
  ⟶*-curry (⟹→⟶* pf)
⟹→⟶* (⟹-cata palg) =
  ⟶*-cata (⟹→⟶* palg)
⟹→⟶* (⟹-fmap pf) =
  ⟶*-fmap (⟹→⟶* pf)
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
⟹→⟶* (⟹-inl-β pf pg) =
  ⟶*-trans (⟶*-∘-l inl (⟶*-case (⟹→⟶* pf) (⟹→⟶* pg)))
           (case-inl ∷ done)
⟹→⟶* (⟹-inr-β pf pg) =
  ⟶*-trans (⟶*-∘-l inr (⟶*-case (⟹→⟶* pf) (⟹→⟶* pg)))
           (case-inr ∷ done)
⟹→⟶* ⟹-η-pair  = eta-pair ∷ done
⟹→⟶* ⟹-η-case  = eta-case ∷ done
⟹→⟶* (⟹-η-curry pf) =
  ⟶*-trans
    (⟶*-curry (⟶*-∘-r apply
       (⟶*-pair (⟶*-∘-l fst (⟹→⟶* pf)) done)))
    (curry-η ∷ done)
⟹→⟶* (⟹-term-unique pf) = term-unique ∷ done
⟹→⟶* ⟹-init-unique       = initial-unique ∷ done
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
⟹→⟶* (⟹-case-dist ph pf pg) =
  ⟶*-trans (⟶*-∘-l _ (⟹→⟶* ph))
    (⟶*-trans (⟶*-∘-r _ (⟶*-case (⟹→⟶* pf) (⟹→⟶* pg)))
      (case-dist ∷ done))
⟹→⟶* (⟹-curry-β pf pg) =
  ⟶*-trans (⟶*-∘-r apply
              (⟶*-pair (⟶*-curry (⟹→⟶* pf)) (⟹→⟶* pg)))
           (curry-β ∷ done)
⟹→⟶* (⟹-curry-β-ext pf ph pg) =
  ⟶*-trans
    (curry-β-ext ∷ done)
    (⟶*-trans (⟶*-∘-l _ (⟹→⟶* pf))
              (⟶*-∘-r _ (⟶*-pair (⟹→⟶* ph) (⟹→⟶* pg))))
⟹→⟶* ⟹-out-in          = out-in ∷ done
⟹→⟶* ⟹-in-out          = in-out ∷ done
⟹→⟶* (⟹-cata-β palg)   =
  ⟶*-trans (⟶*-∘-l _ (⟶*-cata (⟹→⟶* palg)))
           (cata-β ∷ done)

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
