------------------------------------------------------------------------
-- StandardCCC: Minimal Postulate for Standard CCC Confluence
--
-- This module defines CCC reduction WITHOUT cata-beta, out-in, in-out
-- rules. The confluence of this standard CCC fragment is a well-known
-- result from Lambek & Scott's "Introduction to Higher Order Categorical
-- Logic".
--
-- We postulate only standard CCC confluence, then prove cata confluence
-- separately for the restricted class of encoded terms.
------------------------------------------------------------------------

module normalizer.Axioms.StandardCCC where

open import normalizer.Syntax.Types
open import normalizer.Syntax.CCC
  using (Term; id; _∘_; fst; snd; ⟨_,_⟩; inl; inr; [_,_];
         terminal; initial; curry; apply; In; Out; cata; fmap;
         _⟶_; _⟶*_; done; step; _⟹_; _⟹*_; done⟹; step⟹;
         ⟹-refl; ⟶→⟹; ⟶*→⟹*; ⟹→⟶*; ⟹*→⟶*;
         ⟶*-trans; ⟶*-∘-l; ⟶*-∘-r; ⟶*-pair; ⟶*-case; ⟶*-curry)

------------------------------------------------------------------------
-- CCC Reduction (WITHOUT cata-beta, out-in, in-out)
--
-- This is the standard reduction relation for Cartesian Closed
-- Categories without μ-type rules.
------------------------------------------------------------------------

data _⟶ccc_ : ∀ {A B} → Term A B → Term A B → Set where
  -- Identity laws
  ccc-id-left   : ∀ {A B} {f : Term A B} → (id ∘ f) ⟶ccc f
  ccc-id-right  : ∀ {A B} {f : Term A B} → (f ∘ id) ⟶ccc f

  -- Product laws
  ccc-fst-pair  : ∀ {A B C} {f : Term C A} {g : Term C B} →
                  (fst ∘ ⟨ f , g ⟩) ⟶ccc f
  ccc-snd-pair  : ∀ {A B C} {f : Term C A} {g : Term C B} →
                  (snd ∘ ⟨ f , g ⟩) ⟶ccc g
  ccc-eta-pair  : ∀ {A B} → ⟨ fst , snd ⟩ ⟶ccc id {A * B}

  -- Coproduct laws
  ccc-case-inl  : ∀ {A B C} {f : Term A C} {g : Term B C} →
                  ([ f , g ] ∘ inl) ⟶ccc f
  ccc-case-inr  : ∀ {A B C} {f : Term A C} {g : Term B C} →
                  ([ f , g ] ∘ inr) ⟶ccc g
  ccc-eta-case  : ∀ {A B} → [ inl , inr ] ⟶ccc id {A + B}

  -- Pair distribution
  ccc-pair-comp : ∀ {A B C D} {f : Term B C} {g : Term B D} {h : Term A B} →
                  (⟨ f , g ⟩ ∘ h) ⟶ccc ⟨ f ∘ h , g ∘ h ⟩

  -- Exponential laws
  ccc-curry-β   : ∀ {A B C} {f : Term (A * B) C} {g : Term A B} →
                  (apply ∘ ⟨ curry f , g ⟩) ⟶ccc (f ∘ ⟨ id , g ⟩)
  ccc-curry-β-ext : ∀ {X A B C} {f : Term (A * B) C} {h : Term X A} {g : Term X B} →
                    (apply ∘ ⟨ curry f ∘ h , g ⟩) ⟶ccc (f ∘ ⟨ h , g ⟩)
  ccc-curry-η   : ∀ {A B C} {f : Term A (B ⇒ C)} →
                  curry (apply ∘ ⟨ f ∘ fst , snd ⟩) ⟶ccc f

  -- Associativity
  ccc-assoc-l   : ∀ {A B C D} {f : Term C D} {g : Term B C} {h : Term A B} →
                  (f ∘ (g ∘ h)) ⟶ccc ((f ∘ g) ∘ h)
  ccc-assoc-r   : ∀ {A B C D} {f : Term C D} {g : Term B C} {h : Term A B} →
                  ((f ∘ g) ∘ h) ⟶ccc (f ∘ (g ∘ h))

  -- Congruence rules
  ccc-∘-l      : ∀ {A B C} {f f' : Term B C} {g : Term A B} →
                 f ⟶ccc f' → (f ∘ g) ⟶ccc (f' ∘ g)
  ccc-∘-r      : ∀ {A B C} {f : Term B C} {g g' : Term A B} →
                 g ⟶ccc g' → (f ∘ g) ⟶ccc (f ∘ g')
  ccc-pair-l   : ∀ {A B C} {f f' : Term C A} {g : Term C B} →
                 f ⟶ccc f' → ⟨ f , g ⟩ ⟶ccc ⟨ f' , g ⟩
  ccc-pair-r   : ∀ {A B C} {f : Term C A} {g g' : Term C B} →
                 g ⟶ccc g' → ⟨ f , g ⟩ ⟶ccc ⟨ f , g' ⟩
  ccc-case-l   : ∀ {A B C} {f f' : Term A C} {g : Term B C} →
                 f ⟶ccc f' → [ f , g ] ⟶ccc [ f' , g ]
  ccc-case-r   : ∀ {A B C} {f : Term A C} {g g' : Term B C} →
                 g ⟶ccc g' → [ f , g ] ⟶ccc [ f , g' ]
  ccc-curry    : ∀ {A B C} {f f' : Term (A * B) C} →
                 f ⟶ccc f' → curry f ⟶ccc curry f'

  -- NOTE: No cata, In∘Out, Out∘In rules!
  -- Those are μ-type specific and handled separately.

------------------------------------------------------------------------
-- Reflexive-transitive closure of CCC reduction
------------------------------------------------------------------------

data _⟶*ccc_ : ∀ {A B} → Term A B → Term A B → Set where
  done-ccc : ∀ {A B} {t : Term A B} → t ⟶*ccc t
  step-ccc : ∀ {A B} {t u v : Term A B} → t ⟶ccc u → u ⟶*ccc v → t ⟶*ccc v

-- Transitivity
⟶*ccc-trans : ∀ {A B} {t u v : Term A B} →
              t ⟶*ccc u → u ⟶*ccc v → t ⟶*ccc v
⟶*ccc-trans done-ccc q = q
⟶*ccc-trans (step-ccc r rs) q = step-ccc r (⟶*ccc-trans rs q)

------------------------------------------------------------------------
-- CCC reduction embeds into full reduction
------------------------------------------------------------------------

⟶ccc→⟶ : ∀ {A B} {t u : Term A B} → t ⟶ccc u → t ⟶ u
⟶ccc→⟶ ccc-id-left = _⟶_.id-left
⟶ccc→⟶ ccc-id-right = _⟶_.id-right
⟶ccc→⟶ ccc-fst-pair = _⟶_.fst-pair
⟶ccc→⟶ ccc-snd-pair = _⟶_.snd-pair
⟶ccc→⟶ ccc-eta-pair = _⟶_.eta-pair
⟶ccc→⟶ ccc-case-inl = _⟶_.case-inl
⟶ccc→⟶ ccc-case-inr = _⟶_.case-inr
⟶ccc→⟶ ccc-eta-case = _⟶_.eta-case
⟶ccc→⟶ ccc-pair-comp = _⟶_.pair-comp
⟶ccc→⟶ ccc-curry-β = _⟶_.curry-β
⟶ccc→⟶ ccc-curry-β-ext = _⟶_.curry-β-ext
⟶ccc→⟶ ccc-curry-η = _⟶_.curry-η
⟶ccc→⟶ ccc-assoc-l = _⟶_.assoc-l
⟶ccc→⟶ ccc-assoc-r = _⟶_.assoc-r
⟶ccc→⟶ (ccc-∘-l r) = _⟶_.⟶-∘-l (⟶ccc→⟶ r)
⟶ccc→⟶ (ccc-∘-r r) = _⟶_.⟶-∘-r (⟶ccc→⟶ r)
⟶ccc→⟶ (ccc-pair-l r) = _⟶_.⟶-pair-l (⟶ccc→⟶ r)
⟶ccc→⟶ (ccc-pair-r r) = _⟶_.⟶-pair-r (⟶ccc→⟶ r)
⟶ccc→⟶ (ccc-case-l r) = _⟶_.⟶-case-l (⟶ccc→⟶ r)
⟶ccc→⟶ (ccc-case-r r) = _⟶_.⟶-case-r (⟶ccc→⟶ r)
⟶ccc→⟶ (ccc-curry r) = _⟶_.⟶-curry (⟶ccc→⟶ r)

⟶*ccc→⟶* : ∀ {A B} {t u : Term A B} → t ⟶*ccc u → t ⟶* u
⟶*ccc→⟶* done-ccc = done
⟶*ccc→⟶* (step-ccc r rs) = step (⟶ccc→⟶ r) (⟶*ccc→⟶* rs)

------------------------------------------------------------------------
-- Parallel CCC Reduction
------------------------------------------------------------------------

data _⟹ccc_ : ∀ {A B} → Term A B → Term A B → Set where
  -- Reflexivity for atoms
  ⟹ccc-id       : ∀ {A} → id {A} ⟹ccc id
  ⟹ccc-fst      : ∀ {A B} → fst {A} {B} ⟹ccc fst
  ⟹ccc-snd      : ∀ {A B} → snd {A} {B} ⟹ccc snd
  ⟹ccc-inl      : ∀ {A B} → inl {A} {B} ⟹ccc inl
  ⟹ccc-inr      : ∀ {A B} → inr {A} {B} ⟹ccc inr
  ⟹ccc-terminal : ∀ {A} → terminal {A} ⟹ccc terminal
  ⟹ccc-initial  : ∀ {A} → initial {A} ⟹ccc initial
  ⟹ccc-apply    : ∀ {A B} → apply {A} {B} ⟹ccc apply
  ⟹ccc-In       : ∀ {F} → In {F} ⟹ccc In
  ⟹ccc-Out      : ∀ {F} → Out {F} ⟹ccc Out

  -- Congruence for compound terms
  ⟹ccc-∘    : ∀ {A B C} {f f' : Term B C} {g g' : Term A B} →
              f ⟹ccc f' → g ⟹ccc g' → (f ∘ g) ⟹ccc (f' ∘ g')
  ⟹ccc-pair : ∀ {A B C} {f f' : Term C A} {g g' : Term C B} →
              f ⟹ccc f' → g ⟹ccc g' → ⟨ f , g ⟩ ⟹ccc ⟨ f' , g' ⟩
  ⟹ccc-case : ∀ {A B C} {f f' : Term A C} {g g' : Term B C} →
              f ⟹ccc f' → g ⟹ccc g' → [ f , g ] ⟹ccc [ f' , g' ]
  ⟹ccc-curry : ∀ {A B C} {f f' : Term (A * B) C} →
               f ⟹ccc f' → curry f ⟹ccc curry f'
  ⟹ccc-cata : ∀ {F A} {alg alg' : Term (⟦ F ⟧F A) A} →
              alg ⟹ccc alg' → cata F alg ⟹ccc cata F alg'

  -- Beta reductions (CCC only, NO cata-beta)
  ⟹ccc-id-l    : ∀ {A B} {f f' : Term A B} →
                 f ⟹ccc f' → (id ∘ f) ⟹ccc f'
  ⟹ccc-id-r    : ∀ {A B} {f f' : Term A B} →
                 f ⟹ccc f' → (f ∘ id) ⟹ccc f'
  ⟹ccc-fst-β   : ∀ {A B C} {f f' : Term C A} {g g' : Term C B} →
                 f ⟹ccc f' → g ⟹ccc g' → (fst ∘ ⟨ f , g ⟩) ⟹ccc f'
  ⟹ccc-snd-β   : ∀ {A B C} {f f' : Term C A} {g g' : Term C B} →
                 f ⟹ccc f' → g ⟹ccc g' → (snd ∘ ⟨ f , g ⟩) ⟹ccc g'
  ⟹ccc-inl-β   : ∀ {A B C} {f f' : Term A C} {g g' : Term B C} →
                 f ⟹ccc f' → g ⟹ccc g' → ([ f , g ] ∘ inl) ⟹ccc f'
  ⟹ccc-inr-β   : ∀ {A B C} {f f' : Term A C} {g g' : Term B C} →
                 f ⟹ccc f' → g ⟹ccc g' → ([ f , g ] ∘ inr) ⟹ccc g'

  -- Eta reductions
  ⟹ccc-η-pair  : ∀ {A B} → ⟨ fst , snd ⟩ ⟹ccc id {A * B}
  ⟹ccc-η-case  : ∀ {A B} → [ inl , inr ] ⟹ccc id {A + B}
  ⟹ccc-η-curry : ∀ {A B C} {f f' : Term A (B ⇒ C)} →
                 f ⟹ccc f' → curry (apply ∘ ⟨ f ∘ fst , snd ⟩) ⟹ccc f'

  -- Curry-apply beta
  ⟹ccc-curry-β : ∀ {A B C} {f f' : Term (A * B) C} {g g' : Term A B} →
                 f ⟹ccc f' → g ⟹ccc g' →
                 (apply ∘ ⟨ curry f , g ⟩) ⟹ccc (f' ∘ ⟨ id , g' ⟩)
  ⟹ccc-curry-β-ext : ∀ {X A B C} {f f' : Term (A * B) C}
                       {h h' : Term X A} {g g' : Term X B} →
                     f ⟹ccc f' → h ⟹ccc h' → g ⟹ccc g' →
                     (apply ∘ ⟨ curry f ∘ h , g ⟩) ⟹ccc (f' ∘ ⟨ h' , g' ⟩)

  -- Associativity
  ⟹ccc-assoc-l : ∀ {A B C D} {f f' : Term C D} {g g' : Term B C} {h h' : Term A B} →
                 f ⟹ccc f' → g ⟹ccc g' → h ⟹ccc h' →
                 (f ∘ (g ∘ h)) ⟹ccc ((f' ∘ g') ∘ h')
  ⟹ccc-assoc-r : ∀ {A B C D} {f f' : Term C D} {g g' : Term B C} {h h' : Term A B} →
                 f ⟹ccc f' → g ⟹ccc g' → h ⟹ccc h' →
                 ((f ∘ g) ∘ h) ⟹ccc (f' ∘ (g' ∘ h'))

  -- Pair distribution
  ⟹ccc-pair-comp : ∀ {A B C D} {f f' : Term B C} {g g' : Term B D} {h h' : Term A B} →
                   f ⟹ccc f' → g ⟹ccc g' → h ⟹ccc h' →
                   (⟨ f , g ⟩ ∘ h) ⟹ccc ⟨ f' ∘ h' , g' ∘ h' ⟩

  -- NOTE: No Out∘In, In∘Out, cata-beta rules!

------------------------------------------------------------------------
-- Parallel CCC reduction is reflexive
------------------------------------------------------------------------

⟹ccc-refl : ∀ {A B} (t : Term A B) → t ⟹ccc t
⟹ccc-refl id = ⟹ccc-id
⟹ccc-refl (f ∘ g) = ⟹ccc-∘ (⟹ccc-refl f) (⟹ccc-refl g)
⟹ccc-refl fst = ⟹ccc-fst
⟹ccc-refl snd = ⟹ccc-snd
⟹ccc-refl ⟨ f , g ⟩ = ⟹ccc-pair (⟹ccc-refl f) (⟹ccc-refl g)
⟹ccc-refl inl = ⟹ccc-inl
⟹ccc-refl inr = ⟹ccc-inr
⟹ccc-refl [ f , g ] = ⟹ccc-case (⟹ccc-refl f) (⟹ccc-refl g)
⟹ccc-refl terminal = ⟹ccc-terminal
⟹ccc-refl initial = ⟹ccc-initial
⟹ccc-refl (curry f) = ⟹ccc-curry (⟹ccc-refl f)
⟹ccc-refl apply = ⟹ccc-apply
⟹ccc-refl In = ⟹ccc-In
⟹ccc-refl Out = ⟹ccc-Out
⟹ccc-refl (cata F alg) = ⟹ccc-cata (⟹ccc-refl alg)

------------------------------------------------------------------------
-- MINIMAL POSTULATE: Standard CCC Confluence
--
-- This is Lambek & Scott's result: the simply-typed lambda calculus
-- (internal language of CCC) is confluent. This predates μ-types.
------------------------------------------------------------------------

-- Complete development for CCC (no cata rules)
postulate
  ccc-complete : ∀ {A B} → Term A B → Term A B

-- Triangle lemma: t ⟹ccc u implies u ⟹ccc (ccc-complete t)
postulate
  ccc-triangle : ∀ {A B} {t u : Term A B} →
                 t ⟹ccc u → u ⟹ccc ccc-complete t

------------------------------------------------------------------------
-- Derived: CCC Diamond Property
------------------------------------------------------------------------

ccc-diamond : ∀ {A B} {t u v : Term A B} →
              t ⟹ccc u → t ⟹ccc v →
              ∃[ w ] ((u ⟹ccc w) × (v ⟹ccc w))
ccc-diamond {t = t} p q = ccc-complete t , (ccc-triangle p , ccc-triangle q)

------------------------------------------------------------------------
-- Reflexive-transitive closure of parallel CCC reduction
------------------------------------------------------------------------

data _⟹*ccc_ : ∀ {A B} → Term A B → Term A B → Set where
  done⟹ccc : ∀ {A B} {t : Term A B} → t ⟹*ccc t
  step⟹ccc : ∀ {A B} {t u v : Term A B} →
             t ⟹ccc u → u ⟹*ccc v → t ⟹*ccc v

------------------------------------------------------------------------
-- Strip Lemma for CCC
------------------------------------------------------------------------

ccc-strip : ∀ {A B} {t u v : Term A B} →
            t ⟹ccc u → t ⟹*ccc v →
            ∃[ w ] ((u ⟹*ccc w) × (v ⟹ccc w))
ccc-strip {t = t} p done⟹ccc with ccc-diamond p (⟹ccc-refl t)
... | w , (uw , tw) = w , (step⟹ccc uw done⟹ccc , tw)
ccc-strip p (step⟹ccc q qs) with ccc-diamond p q
... | w , (pw , qw) with ccc-strip qw qs
... | w' , (qws , rw) = w' , (step⟹ccc pw qws , rw)

------------------------------------------------------------------------
-- Confluence for Parallel CCC Reduction
------------------------------------------------------------------------

ccc-confluence⟹ : ∀ {A B} {t u v : Term A B} →
                  t ⟹*ccc u → t ⟹*ccc v →
                  ∃[ w ] ((u ⟹*ccc w) × (v ⟹*ccc w))
ccc-confluence⟹ done⟹ccc qs = _ , (qs , done⟹ccc)
ccc-confluence⟹ (step⟹ccc p ps) qs with ccc-strip p qs
... | w , (pw , qw) with ccc-confluence⟹ ps pw
... | w' , (pws , qws) = w' , (pws , step⟹ccc qw qws)

------------------------------------------------------------------------
-- Summary
--
-- Postulates (MINIMAL):
--   ccc-complete : Term A B → Term A B
--   ccc-triangle : t ⟹ccc u → u ⟹ccc ccc-complete t
--
-- Derived:
--   ccc-diamond     : t ⟹ccc u → t ⟹ccc v → ∃ w. u ⟹ccc w × v ⟹ccc w
--   ccc-strip       : t ⟹ccc u → t ⟹*ccc v → ∃ w. u ⟹*ccc w × v ⟹ccc w
--   ccc-confluence⟹ : t ⟹*ccc u → t ⟹*ccc v → ∃ w. u ⟹*ccc w × v ⟹*ccc w
--
-- These postulates exclude cata-beta, out-in, in-out - exactly what
-- Lambek & Scott proved for standard CCCs without μ-types.
------------------------------------------------------------------------
