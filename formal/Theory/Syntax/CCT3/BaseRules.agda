------------------------------------------------------------------------
-- Theory.Syntax.CCT3.BaseRules
--
-- Parameterized rules introduced at the CCT3 level (initial algebras,
-- μ-types). Three rules, grouped as β-rules:
--
--   out-in  : Out ∘ In ⟶ id                (β-direction of Lambek iso)
--   in-out  : In ∘ Out ⟶ id                (η-direction)
--   cata-β  : cata alg ∘ In ⟶ alg ∘ fmap F (cata alg)
--
-- Parameterized over a functor action at the type level (F : Ty → Ty)
-- and at the morphism level (fmap). Concrete syntaxes instantiate
-- these with their own type-level fixpoint constructor.
------------------------------------------------------------------------

module Theory.Syntax.CCT3.BaseRules where

module Rules
  (Ty     : Set)
  (Term   : Ty → Ty → Set)
  (id     : ∀ {A}     → Term A A)
  (_∘_    : ∀ {A B C} → Term B C → Term A B → Term A C)
  (μ      : (Ty → Ty) → Ty)
  (In     : ∀ {F : Ty → Ty} → Term (F (μ F)) (μ F))
  (Out    : ∀ {F : Ty → Ty} → Term (μ F) (F (μ F)))
  (cata   : ∀ {F : Ty → Ty} {A} → Term (F A) A → Term (μ F) A)
  (fmap   : ∀ {F : Ty → Ty} {A B} → Term A B → Term (F A) (F B))
  where

  data _⟶β_ : ∀ {A B} → Term A B → Term A B → Set where
    out-in : ∀ {F : Ty → Ty} →
             (Out {F} ∘ In {F}) ⟶β id
    in-out : ∀ {F : Ty → Ty} →
             (In  {F} ∘ Out {F}) ⟶β id
    cata-β : ∀ {F : Ty → Ty} {A} {alg : Term (F A) A} →
             (cata {F} alg ∘ In {F}) ⟶β (alg ∘ fmap {F} (cata {F} alg))

  infix 4 _⟶β_
