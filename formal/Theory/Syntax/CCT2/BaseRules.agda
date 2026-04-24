------------------------------------------------------------------------
-- Theory.Syntax.CCT2.BaseRules
--
-- Parameterized rules introduced at the CCT2 level (coproducts).
-- Split to mirror CCTB/CCT1 BaseRules:
--
--   _⟶β_  : β-rules for coproducts
--             case-inl : [f, g] ∘ inl ⟶ f
--             case-inr : [f, g] ∘ inr ⟶ g
--             eta-case : [inl, inr] ⟶ id
--
--   _⟶s_  : structural rules forced by the coproduct universal property
--             eta-case-gen  : [f ∘ inl, f ∘ inr] ⟶ f
--             case-dist     : h ∘ [f, g] ⟶ [h ∘ f, h ∘ g]
--             initial-unique: any f : Void → A reduces to initial
--
-- Any CCT2-carrying level instantiates this module to get the rules
-- on its own Term type.
------------------------------------------------------------------------

module Theory.Syntax.CCT2.BaseRules where

module Rules
  (Ty       : Set)
  (Unit     : Ty)
  (_×_      : Ty → Ty → Ty)
  (_⇒_      : Ty → Ty → Ty)
  (Void     : Ty)
  (_⊎_      : Ty → Ty → Ty)
  (Term     : Ty → Ty → Set)
  (id       : ∀ {A}     → Term A A)
  (_∘_      : ∀ {A B C} → Term B C → Term A B → Term A C)
  (initial  : ∀ {A}     → Term Void A)
  (inl      : ∀ {A B}   → Term A (A ⊎ B))
  (inr      : ∀ {A B}   → Term B (A ⊎ B))
  ([_,_]    : ∀ {A B C} → Term A C → Term B C → Term (A ⊎ B) C)
  where

  ---------------------------------------------------------------------
  -- β-rules: computational rewrites
  ---------------------------------------------------------------------

  data _⟶β_ : ∀ {A B} → Term A B → Term A B → Set where
    case-inl : ∀ {A B C} {f : Term A C} {g : Term B C} →
               ([ f , g ] ∘ inl) ⟶β f
    case-inr : ∀ {A B C} {f : Term A C} {g : Term B C} →
               ([ f , g ] ∘ inr) ⟶β g
    eta-case : ∀ {A B} → [ inl {A} {B} , inr {A} {B} ] ⟶β id

  infix 4 _⟶β_

  ---------------------------------------------------------------------
  -- Structural rules: forced by the coproduct universal property
  ---------------------------------------------------------------------

  data _⟶s_ : ∀ {A B} → Term A B → Term A B → Set where
    eta-case-gen   : ∀ {A B C} {f : Term (A ⊎ B) C} →
                     [ f ∘ inl , f ∘ inr ] ⟶s f
    case-dist      : ∀ {A B C D} {h : Term C D} {f : Term A C} {g : Term B C} →
                     (h ∘ [ f , g ]) ⟶s [ h ∘ f , h ∘ g ]
    initial-unique : ∀ {A} {f : Term Void A} → f ⟶s initial

  infix 4 _⟶s_
