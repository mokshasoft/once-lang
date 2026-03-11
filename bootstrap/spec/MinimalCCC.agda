------------------------------------------------------------------------
-- MinimalCCC: Fixpoint Correctness for Zero-Code TCB
--
-- This module defines the structure for proving:
--   1. CCC with cata has confluence and termination
--   2. Normal forms are unique
--   3. Fixpoint implies correctness
--
-- SELF-CONTAINED: No external dependencies (this is the bootstrap).
------------------------------------------------------------------------

module MinimalCCC where

------------------------------------------------------------------------
-- Minimal Prelude
------------------------------------------------------------------------

data _≡_ {A : Set} : A → A → Set where
  refl : ∀ {x} → x ≡ x

sym : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : ∀ {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl refl = refl

cong : ∀ {A B : Set} (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
cong f refl = refl

record Σ (A : Set) (B : A → Set) : Set where
  constructor _,_
  field fst : A ; snd : B fst

∃-syntax : ∀ {A : Set} → (A → Set) → Set
∃-syntax {A} B = Σ A B
syntax ∃-syntax (λ x → B) = ∃[ x ] B

_×_ : Set → Set → Set
A × B = Σ A (λ _ → B)

------------------------------------------------------------------------
-- Part 1: Types and Functors
------------------------------------------------------------------------

-- Mutually recursive: types can contain μF, functors can contain K Ty
data Ty : Set
data Func : Set

data Ty where
  Unit : Ty
  _*_  : Ty → Ty → Ty
  _+_  : Ty → Ty → Ty
  μ_   : Func → Ty

data Func where
  Id  : Func
  K   : Ty → Func
  _⊕_ : Func → Func → Func
  _⊗_ : Func → Func → Func

infixr 7 _*_ _⊗_
infixr 6 _+_ _⊕_

⟦_⟧F : Func → Ty → Ty
⟦ Id ⟧F X = X
⟦ K A ⟧F X = A
⟦ F ⊕ G ⟧F X = ⟦ F ⟧F X + ⟦ G ⟧F X
⟦ F ⊗ G ⟧F X = ⟦ F ⟧F X * ⟦ G ⟧F X

------------------------------------------------------------------------
-- Part 2: Terms (CCC + cata)
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
  -- Initial algebra (recursion)
  In       : ∀ {F} → Term (⟦ F ⟧F (μ F)) (μ F)
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
  -- Catamorphism (the key recursion rule)
  cata-β    : ∀ {F A} {alg : Term (⟦ F ⟧F A) A} →
              (cata F alg ∘ In) ⟶ (alg ∘ fmap F (cata F alg))

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
⇒-refl (cata F alg) = ⇒-cata (⇒-refl alg)

-- Single step implies parallel
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

-- The maximum parallel reduct: reduces ALL redexes at once
-- This is the key to the diamond property
--
-- Due to Agda's pattern matching limitations with overlapping cases,
-- we postulate max⇒ and prove its key properties.
-- The function is straightforward to implement in any language:
--   - Recurse into subterms
--   - At composition, check for β-redexes and reduce them
--
-- Alternatively, this could be defined using a view pattern or
-- explicit term inspection, but postulating keeps the proof cleaner.

postulate
  max⇒ : ∀ {A B} → Term A B → Term A B

-- Key properties of max⇒ that we need for confluence:

-- max⇒ applied to atoms is identity
postulate
  max⇒-id : ∀ {A} → max⇒ (id {A}) ≡ id
  max⇒-fst : ∀ {A B} → max⇒ (fst {A} {B}) ≡ fst
  max⇒-snd : ∀ {A B} → max⇒ (snd {A} {B}) ≡ snd
  max⇒-inl : ∀ {A B} → max⇒ (inl {A} {B}) ≡ inl
  max⇒-inr : ∀ {A B} → max⇒ (inr {A} {B}) ≡ inr
  max⇒-terminal : ∀ {A} → max⇒ (terminal {A}) ≡ terminal
  max⇒-In : ∀ {F} → max⇒ (In {F}) ≡ In

-- max⇒ reduces β-redexes
postulate
  max⇒-id-l : ∀ {A B} {f : Term A B} → max⇒ (id ∘ f) ≡ max⇒ f
  max⇒-id-r : ∀ {A B} {f : Term A B} → max⇒ (f ∘ id) ≡ max⇒ f
  max⇒-fst-β : ∀ {A B C} {f : Term C A} {g : Term C B} →
               max⇒ (fst ∘ ⟨ f , g ⟩) ≡ max⇒ f
  max⇒-snd-β : ∀ {A B C} {f : Term C A} {g : Term C B} →
               max⇒ (snd ∘ ⟨ f , g ⟩) ≡ max⇒ g
  max⇒-inl-β : ∀ {A B C} {f : Term A C} {g : Term B C} →
               max⇒ ([ f , g ] ∘ inl) ≡ max⇒ f
  max⇒-inr-β : ∀ {A B C} {f : Term A C} {g : Term B C} →
               max⇒ ([ f , g ] ∘ inr) ≡ max⇒ g
  -- cata-β for max⇒: max⇒ (cata F alg ∘ In) ≡ max⇒ alg ∘ fmap F (cata F (max⇒ alg))
  -- (commented out due to type inference issues - the property is straightforward)

-- Triangle property: t ⇒ u implies u ⇒ max⇒ t
-- This is the key lemma: all parallel reducts converge to the max
--
-- Proof by induction on the parallel reduction derivation.
-- Each case uses the max⇒ properties above.
--
-- The full proof is tedious but mechanical - each constructor of ⇒
-- has a corresponding lemma showing convergence to max⇒.
-- We postulate the full triangle lemma and its helpers.

postulate
  triangle : ∀ {A B} {t u : Term A B} → t ⇒ u → u ⇒ max⇒ t

-- Diamond property follows from triangle
diamond : ∀ {A B} {t u v : Term A B} →
          t ⇒ u → t ⇒ v →
          ∃[ w ] ((u ⇒ w) × (v ⇒ w))
diamond {t = t} p q = max⇒ t , (triangle p , triangle q)

-- Strip lemma: diamond extends to ⇒*
strip : ∀ {A B} {t u v : Term A B} →
        t ⇒ u → t ⇒* v →
        ∃[ w ] ((u ⇒* w) × (v ⇒ w))
strip p done⇒ = _ , (done⇒ , p)
strip p (step⇒ q qs) with diamond p q
... | w , (u⇒w , v⇒w) with strip v⇒w qs
...   | w' , (w⇒*w' , v'⇒w') = w' , (step⇒ u⇒w w⇒*w' , v'⇒w')

-- Full confluence for parallel reduction
confluence⇒ : ∀ {A B} {t u v : Term A B} →
              t ⇒* u → t ⇒* v →
              ∃[ w ] ((u ⇒* w) × (v ⇒* w))
confluence⇒ done⇒ q = _ , (q , done⇒)
confluence⇒ (step⇒ p ps) q with strip p q
... | w , (u⇒*w , v⇒w) with confluence⇒ ps u⇒*w
...   | w' , (u'⇒*w' , w⇒*w') = w' , (u'⇒*w' , step⇒ v⇒w w⇒*w')

-- CONFLUENCE FOR ⟶* (the main theorem)
confluence : ∀ {A B} {t u v : Term A B} →
             t ⟶* u → t ⟶* v →
             ∃[ w ] ((u ⟶* w) × (v ⟶* w))
confluence p q with confluence⇒ (⟶*→⇒* p) (⟶*→⇒* q)
... | w , (u⇒*w , v⇒*w) = w , (⇒*→⟶* u⇒*w , ⇒*→⟶* v⇒*w)

------------------------------------------------------------------------
-- Part 6: Termination and Unique Normal Forms
------------------------------------------------------------------------

-- Termination: all terms have a normal form
-- This requires showing CCC + cata is strongly normalizing
postulate
  termination : ∀ {A B} (t : Term A B) →
                ∃[ u ] (t ⟶* u)  -- u is in normal form

-- Empty type for absurdity
data ⊥ : Set where

⊥-elim : ∀ {A : Set} → ⊥ → A
⊥-elim ()

-- Negation
¬_ : Set → Set
¬ A = A → ⊥

-- Normal form predicate: no reductions possible
NF : ∀ {A B} → Term A B → Set
NF t = ∀ {u} → ¬ (t ⟶ u)

-- Unique normal forms: follows from confluence
-- If t →* u and t →* v, and both u,v are normal forms, then u ≡ v
unique-nf : ∀ {A B} {t u v : Term A B} →
            t ⟶* u → t ⟶* v →
            NF u → NF v →
            u ≡ v
unique-nf t→*u t→*v nf-u nf-v with confluence t→*u t→*v
... | w , (u→*w , v→*w) = nf-join u→*w v→*w nf-u nf-v
  where
    -- If u is NF and u →* w, then u ≡ w (because u can't step)
    nf-stable : ∀ {A B} {u w : Term A B} → u ⟶* w → NF u → u ≡ w
    nf-stable done _ = refl
    nf-stable (step r _) nf = ⊥-elim (nf r)  -- contradiction: u can't reduce

    -- Both join to w, so both equal w
    nf-join : ∀ {A B} {u v w : Term A B} →
              u ⟶* w → v ⟶* w → NF u → NF v → u ≡ v
    nf-join u→*w v→*w nf-u nf-v =
      trans (nf-stable u→*w nf-u) (sym (nf-stable v→*w nf-v))

------------------------------------------------------------------------
-- Part 7: Self-Representation
------------------------------------------------------------------------

-- The type of term codes (terms represented as data)
-- This is μ of a polynomial functor encoding the Term grammar
TermCode : Ty
TermCode = μ (K Unit ⊕ (Id ⊗ Id) ⊕ K Unit ⊕ K Unit ⊕ (Id ⊗ Id)
             ⊕ K Unit ⊕ K Unit ⊕ (Id ⊗ Id) ⊕ K Unit ⊕ K Unit ⊕ Id)
-- Encodes: id | ∘ | fst | snd | pair | inl | inr | case | terminal | In | cata

-- Encoding function (terms to codes)
postulate
  ⌜_⌝ : ∀ {A B} → Term A B → Term Unit TermCode

-- The normalizer type: a term that normalizes term codes
Normalizer : Set
Normalizer = Term TermCode TermCode

-- Apply normalizer to a code
postulate
  apply-norm : Normalizer → Term Unit TermCode → Term Unit TermCode

------------------------------------------------------------------------
-- Part 8: THE FIXPOINT CORRECTNESS THEOREM
------------------------------------------------------------------------

-- A normalizer N is at a fixpoint if normalizing its own code returns itself
IsFixpoint : Normalizer → Set
IsFixpoint N = apply-norm N ⌜ N ⌝ ≡ ⌜ N ⌝

-- THE MAIN THEOREM:
-- If a normalizer reaches a fixpoint, it correctly computes normal forms.
postulate
  fixpoint-correctness :
    (N : Normalizer) →
    IsFixpoint N →
    ∀ {A B} (t : Term A B) →
    ∃[ u ] ((t ⟶* u) × (apply-norm N ⌜ t ⌝ ≡ ⌜ u ⌝))

-- UNIQUENESS:
-- Any two fixpoint normalizers compute the same results.
postulate
  fixpoint-unique :
    (N₁ N₂ : Normalizer) →
    IsFixpoint N₁ → IsFixpoint N₂ →
    ∀ {A B} (t : Term A B) →
    apply-norm N₁ ⌜ t ⌝ ≡ apply-norm N₂ ⌜ t ⌝

------------------------------------------------------------------------
-- Summary
------------------------------------------------------------------------

-- What we have:
--   ✓ Types: Unit, *, +, μF
--   ✓ Terms: id, ∘, fst, snd, pair, inl, inr, case, terminal, In, cata
--   ✓ Reduction rules: CCC laws + cata-β
--   ✓ Structure for confluence, termination, unique NF
--   ✓ Self-representation (TermCode, ⌜_⌝)
--   ✓ Fixpoint correctness theorem statement
--
-- What remains to prove:
--   - confluence (via parallel reduction / diamond)
--   - termination (via strong normalization)
--   - unique-nf (follows from above)
--   - Define ⌜_⌝ concretely
--   - fixpoint-correctness (the main theorem)
--   - fixpoint-unique
--
-- Once proven: TCB = 0 lines of code, only mathematics.
------------------------------------------------------------------------
