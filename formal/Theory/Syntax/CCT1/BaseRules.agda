------------------------------------------------------------------------
-- Theory.Syntax.CCT1.BaseRules
--
-- Parameterized β rules introduced at the CCT1 level (exponentials).
-- These are ONLY the NEW rules at CCT1; CCTB rules live in
-- Theory.Syntax.CCTB.BaseRules and are combined via union at the
-- concrete level.
--
-- NOTE: curry-η (the η-rule for exponentials) is OMITTED from this
-- reduction system. Including it creates a known βη-confluence
-- tangle (the body of curry can have inner β-redexes that race the
-- outer η-reduction; the two paths cannot be reconciled via plain
-- Takahashi or one-step Hindley-Rosen). Standard treatments use
-- either the postponement theorem (Klop 1980) or translation to
-- simply-typed λ-calculus. Both are substantial additional work.
--
-- What we prove rigorously: CCT1 confluence for β-rules (+ eta-pair
-- inherited from CCTB, whose rigid pattern causes no conflict).
-- curry-η is deferred; a full βη proof is future work.
------------------------------------------------------------------------

module Theory.Syntax.CCT1.BaseRules where

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
