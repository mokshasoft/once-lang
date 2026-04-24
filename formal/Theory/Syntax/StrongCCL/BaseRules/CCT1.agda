------------------------------------------------------------------------
-- Theory.Syntax.StrongCCL.BaseRules.CCT1
--
-- Base reduction rules introduced at the CCT1 level (exponentials):
--
--   β-rules (_⟶β_):
--     curry-β     : apply ∘ ⟨ curry f , g ⟩  ⟶  f ∘ ⟨ id , g ⟩
--
--   η-rules (_⟶η_):
--     curry-η     : curry (apply ∘ ⟨ f ∘ fst , snd ⟩)  ⟶  f
--     curry-apply : curry apply                        ⟶  id
--
-- Why curry-apply is a separate rule: it is derivable as an equation
-- (curry-η with f = id, then simplify via id-left/eta-pair/id-right),
-- but it is NOT reachable as a rewrite rule from the others in one
-- direction. Without curry-apply, the two paths
--     curry (apply ∘ ⟨ id ∘ fst , snd ⟩) →η id            (one step)
--     curry (apply ∘ ⟨ id ∘ fst , snd ⟩) →β* curry apply  (stuck)
-- diverge. Adding curry-apply closes the diagram.
--
-- The β-subset alone is Takahashi-confluent (see Diamond/Triangle).
-- β ∪ η is NOT Takahashi-confluent (the classical βη-tangle): we prove
-- it confluent via Newman's lemma (SN + local confluence).
------------------------------------------------------------------------

module Theory.Syntax.StrongCCL.BaseRules.CCT1 where

module Rules
  (Ty    : Set)
  (Unit  : Ty)
  (_×_   : Ty → Ty → Ty)
  (_⇒_   : Ty → Ty → Ty)
  (Term  : Ty → Ty → Set)
  (id    : ∀ {A}     → Term A A)
  (_∘_   : ∀ {A B C} → Term B C → Term A B → Term A C)
  (fst   : ∀ {A B}   → Term (A × B) A)
  (snd   : ∀ {A B}   → Term (A × B) B)
  (⟨_,_⟩ : ∀ {A B C} → Term C A → Term C B → Term C (A × B))
  (curry : ∀ {A B C} → Term (A × B) C → Term A (B ⇒ C))
  (apply : ∀ {A B}   → Term ((A ⇒ B) × A) B)
  where

  data _⟶β_ : ∀ {A B} → Term A B → Term A B → Set where
    curry-β : ∀ {A B C} {f : Term (A × B) C} {g : Term A B} →
              (apply ∘ ⟨ curry f , g ⟩) ⟶β (f ∘ ⟨ id , g ⟩)

  infix 4 _⟶β_

  data _⟶η_ : ∀ {A B} → Term A B → Term A B → Set where
    curry-η       : ∀ {A B C} {f : Term A (B ⇒ C)} →
                    curry (apply ∘ ⟨ f ∘ fst , snd ⟩) ⟶η f
    curry-apply   : ∀ {A B} →
                    curry (apply {A = A} {B = B}) ⟶η id
    curry-compose : ∀ {A B C D} {f : Term (A × B) C} {g : Term D A} →
                    (curry f ∘ g) ⟶η curry (f ∘ ⟨ g ∘ fst , snd ⟩)

  infix 4 _⟶η_
