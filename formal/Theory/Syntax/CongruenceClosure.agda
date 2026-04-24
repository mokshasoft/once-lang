------------------------------------------------------------------------
-- Theory.Syntax.CongruenceClosure
--
-- Per-level congruence-closure modules. A congruence closure turns a
-- base relation _⇝_ into a relation closed under reduction-under-
-- subterm-constructors at that tower level.
--
-- WHY PER-LEVEL (and not fully compositional):
--
-- We cannot factor "congruence for _∘_" and "congruence for ⟨_,_⟩"
-- into separate stackable closures while also allowing reductions to
-- propagate through arbitrarily-nested term shapes. A term like
-- `⟨ curry (f ∘ g) , h ⟩` vs. `curry ⟨ f ∘ g , h ⟩` requires the
-- congruence constructors to be mutually recursive in a single data
-- type — any linear ordering of layered closures fails on one shape
-- or the other. So each level declares ONE data type that closes
-- under all subterm-carrying constructors available at that level.
--
-- Duplication: ∘-congˡ, ∘-congʳ, ⟨,⟩-congˡ, ⟨,⟩-congʳ are re-stated
-- in each level's module (since they operate on that level's Term).
-- This is structural duplication localized to this file — the β/η
-- rules themselves are defined once in CCTB.BaseRules and CCT1.BaseRules.
------------------------------------------------------------------------

module Theory.Syntax.CongruenceClosure where

------------------------------------------------------------------------
-- Congruence closure at CCTB: closes under ∘ and ⟨_,_⟩.
------------------------------------------------------------------------

module CCTB-Close
  (Ty    : Set)
  (_×_   : Ty → Ty → Ty)
  (Term  : Ty → Ty → Set)
  (_∘_   : ∀ {A B C} → Term B C → Term A B → Term A C)
  (⟨_,_⟩ : ∀ {A B C} → Term C A → Term C B → Term C (A × B))
  (_⇝_   : ∀ {A B}   → Term A B → Term A B → Set)
  where

  data Closed : ∀ {A B} → Term A B → Term A B → Set where
    base      : ∀ {A B} {f g : Term A B} → f ⇝ g → Closed f g
    ∘-congˡ   : ∀ {A B C} {f f' : Term B C} {g : Term A B} →
                Closed f f' → Closed (f ∘ g) (f' ∘ g)
    ∘-congʳ   : ∀ {A B C} {f : Term B C} {g g' : Term A B} →
                Closed g g' → Closed (f ∘ g) (f ∘ g')
    ⟨,⟩-congˡ : ∀ {A B C} {f f' : Term C A} {g : Term C B} →
                Closed f f' → Closed ⟨ f , g ⟩ ⟨ f' , g ⟩
    ⟨,⟩-congʳ : ∀ {A B C} {f : Term C A} {g g' : Term C B} →
                Closed g g' → Closed ⟨ f , g ⟩ ⟨ f , g' ⟩

------------------------------------------------------------------------
-- Congruence closure at CCT1: closes under ∘, ⟨_,_⟩, and curry.
------------------------------------------------------------------------

module CCT1-Close
  (Ty    : Set)
  (_×_   : Ty → Ty → Ty)
  (_⇒_   : Ty → Ty → Ty)
  (Term  : Ty → Ty → Set)
  (_∘_   : ∀ {A B C} → Term B C → Term A B → Term A C)
  (⟨_,_⟩ : ∀ {A B C} → Term C A → Term C B → Term C (A × B))
  (curry : ∀ {A B C} → Term (A × B) C → Term A (B ⇒ C))
  (_⇝_   : ∀ {A B}   → Term A B → Term A B → Set)
  where

  data Closed : ∀ {A B} → Term A B → Term A B → Set where
    base       : ∀ {A B} {f g : Term A B} → f ⇝ g → Closed f g
    ∘-congˡ    : ∀ {A B C} {f f' : Term B C} {g : Term A B} →
                 Closed f f' → Closed (f ∘ g) (f' ∘ g)
    ∘-congʳ    : ∀ {A B C} {f : Term B C} {g g' : Term A B} →
                 Closed g g' → Closed (f ∘ g) (f ∘ g')
    ⟨,⟩-congˡ  : ∀ {A B C} {f f' : Term C A} {g : Term C B} →
                 Closed f f' → Closed ⟨ f , g ⟩ ⟨ f' , g ⟩
    ⟨,⟩-congʳ  : ∀ {A B C} {f : Term C A} {g g' : Term C B} →
                 Closed g g' → Closed ⟨ f , g ⟩ ⟨ f , g' ⟩
    curry-cong : ∀ {A B C} {f f' : Term (A × B) C} →
                 Closed f f' → Closed (curry f) (curry f')

------------------------------------------------------------------------
-- Congruence closure at CCT2: closes under ∘, ⟨_,_⟩, curry, and [_,_].
------------------------------------------------------------------------

module CCT2-Close
  (Ty    : Set)
  (_×_   : Ty → Ty → Ty)
  (_⇒_   : Ty → Ty → Ty)
  (_⊎_   : Ty → Ty → Ty)
  (Term  : Ty → Ty → Set)
  (_∘_   : ∀ {A B C} → Term B C → Term A B → Term A C)
  (⟨_,_⟩ : ∀ {A B C} → Term C A → Term C B → Term C (A × B))
  (curry : ∀ {A B C} → Term (A × B) C → Term A (B ⇒ C))
  ([_,_] : ∀ {A B C} → Term A C → Term B C → Term (A ⊎ B) C)
  (_⇝_   : ∀ {A B}   → Term A B → Term A B → Set)
  where

  data Closed : ∀ {A B} → Term A B → Term A B → Set where
    base       : ∀ {A B} {f g : Term A B} → f ⇝ g → Closed f g
    ∘-congˡ    : ∀ {A B C} {f f' : Term B C} {g : Term A B} →
                 Closed f f' → Closed (f ∘ g) (f' ∘ g)
    ∘-congʳ    : ∀ {A B C} {f : Term B C} {g g' : Term A B} →
                 Closed g g' → Closed (f ∘ g) (f ∘ g')
    ⟨,⟩-congˡ  : ∀ {A B C} {f f' : Term C A} {g : Term C B} →
                 Closed f f' → Closed ⟨ f , g ⟩ ⟨ f' , g ⟩
    ⟨,⟩-congʳ  : ∀ {A B C} {f : Term C A} {g g' : Term C B} →
                 Closed g g' → Closed ⟨ f , g ⟩ ⟨ f , g' ⟩
    curry-cong : ∀ {A B C} {f f' : Term (A × B) C} →
                 Closed f f' → Closed (curry f) (curry f')
    [,]-congˡ  : ∀ {A B C} {f f' : Term A C} {g : Term B C} →
                 Closed f f' → Closed [ f , g ] [ f' , g ]
    [,]-congʳ  : ∀ {A B C} {f : Term A C} {g g' : Term B C} →
                 Closed g g' → Closed [ f , g ] [ f , g' ]

------------------------------------------------------------------------
-- Congruence closure at CCT3: closes under ∘, ⟨_,_⟩, curry, [_,_],
-- cata, and fmap (functor action on morphisms).
------------------------------------------------------------------------

module CCT3-Close
  (Ty    : Set)
  (_×_   : Ty → Ty → Ty)
  (_⇒_   : Ty → Ty → Ty)
  (_⊎_   : Ty → Ty → Ty)
  (μ     : (Ty → Ty) → Ty)
  (Term  : Ty → Ty → Set)
  (_∘_   : ∀ {A B C} → Term B C → Term A B → Term A C)
  (⟨_,_⟩ : ∀ {A B C} → Term C A → Term C B → Term C (A × B))
  (curry : ∀ {A B C} → Term (A × B) C → Term A (B ⇒ C))
  ([_,_] : ∀ {A B C} → Term A C → Term B C → Term (A ⊎ B) C)
  (cata  : ∀ {F : Ty → Ty} {A} → Term (F A) A → Term (μ F) A)
  (fmap  : ∀ {F : Ty → Ty} {A B} → Term A B → Term (F A) (F B))
  (_⇝_   : ∀ {A B}   → Term A B → Term A B → Set)
  where

  data Closed : ∀ {A B} → Term A B → Term A B → Set where
    base       : ∀ {A B} {f g : Term A B} → f ⇝ g → Closed f g
    ∘-congˡ    : ∀ {A B C} {f f' : Term B C} {g : Term A B} →
                 Closed f f' → Closed (f ∘ g) (f' ∘ g)
    ∘-congʳ    : ∀ {A B C} {f : Term B C} {g g' : Term A B} →
                 Closed g g' → Closed (f ∘ g) (f ∘ g')
    ⟨,⟩-congˡ  : ∀ {A B C} {f f' : Term C A} {g : Term C B} →
                 Closed f f' → Closed ⟨ f , g ⟩ ⟨ f' , g ⟩
    ⟨,⟩-congʳ  : ∀ {A B C} {f : Term C A} {g g' : Term C B} →
                 Closed g g' → Closed ⟨ f , g ⟩ ⟨ f , g' ⟩
    curry-cong : ∀ {A B C} {f f' : Term (A × B) C} →
                 Closed f f' → Closed (curry f) (curry f')
    [,]-congˡ  : ∀ {A B C} {f f' : Term A C} {g : Term B C} →
                 Closed f f' → Closed [ f , g ] [ f' , g ]
    [,]-congʳ  : ∀ {A B C} {f : Term A C} {g g' : Term B C} →
                 Closed g g' → Closed [ f , g ] [ f , g' ]
    cata-cong  : ∀ {F : Ty → Ty} {A} {alg alg' : Term (F A) A} →
                 Closed alg alg' → Closed (cata {F} alg) (cata {F} alg')
    fmap-cong  : ∀ {F : Ty → Ty} {A B} {f f' : Term A B} →
                 Closed f f' → Closed (fmap {F} f) (fmap {F} f')

------------------------------------------------------------------------
-- Congruence closure at CCT4: adds ana to CCT3.
------------------------------------------------------------------------

module CCT4-Close
  (Ty    : Set)
  (_×_   : Ty → Ty → Ty)
  (_⇒_   : Ty → Ty → Ty)
  (_⊎_   : Ty → Ty → Ty)
  (μ     : (Ty → Ty) → Ty)
  (ν     : (Ty → Ty) → Ty)
  (Term  : Ty → Ty → Set)
  (_∘_   : ∀ {A B C} → Term B C → Term A B → Term A C)
  (⟨_,_⟩ : ∀ {A B C} → Term C A → Term C B → Term C (A × B))
  (curry : ∀ {A B C} → Term (A × B) C → Term A (B ⇒ C))
  ([_,_] : ∀ {A B C} → Term A C → Term B C → Term (A ⊎ B) C)
  (cata  : ∀ {F : Ty → Ty} {A} → Term (F A) A → Term (μ F) A)
  (fmap  : ∀ {F : Ty → Ty} {A B} → Term A B → Term (F A) (F B))
  (ana   : ∀ {F : Ty → Ty} {A} → Term A (F A) → Term A (ν F))
  (_⇝_   : ∀ {A B}   → Term A B → Term A B → Set)
  where

  data Closed : ∀ {A B} → Term A B → Term A B → Set where
    base       : ∀ {A B} {f g : Term A B} → f ⇝ g → Closed f g
    ∘-congˡ    : ∀ {A B C} {f f' : Term B C} {g : Term A B} →
                 Closed f f' → Closed (f ∘ g) (f' ∘ g)
    ∘-congʳ    : ∀ {A B C} {f : Term B C} {g g' : Term A B} →
                 Closed g g' → Closed (f ∘ g) (f ∘ g')
    ⟨,⟩-congˡ  : ∀ {A B C} {f f' : Term C A} {g : Term C B} →
                 Closed f f' → Closed ⟨ f , g ⟩ ⟨ f' , g ⟩
    ⟨,⟩-congʳ  : ∀ {A B C} {f : Term C A} {g g' : Term C B} →
                 Closed g g' → Closed ⟨ f , g ⟩ ⟨ f , g' ⟩
    curry-cong : ∀ {A B C} {f f' : Term (A × B) C} →
                 Closed f f' → Closed (curry f) (curry f')
    [,]-congˡ  : ∀ {A B C} {f f' : Term A C} {g : Term B C} →
                 Closed f f' → Closed [ f , g ] [ f' , g ]
    [,]-congʳ  : ∀ {A B C} {f : Term A C} {g g' : Term B C} →
                 Closed g g' → Closed [ f , g ] [ f , g' ]
    cata-cong  : ∀ {F : Ty → Ty} {A} {alg alg' : Term (F A) A} →
                 Closed alg alg' → Closed (cata {F} alg) (cata {F} alg')
    fmap-cong  : ∀ {F : Ty → Ty} {A B} {f f' : Term A B} →
                 Closed f f' → Closed (fmap {F} f) (fmap {F} f')
    ana-cong   : ∀ {F : Ty → Ty} {A} {coalg coalg' : Term A (F A)} →
                 Closed coalg coalg' →
                 Closed (ana {F} coalg) (ana {F} coalg')
