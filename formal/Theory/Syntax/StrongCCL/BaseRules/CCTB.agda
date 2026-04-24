------------------------------------------------------------------------
-- Theory.Syntax.StrongCCL.BaseRules.CCTB
--
-- Parameterized rules introduced at the CCTB level, split into:
--
--   _⟶β_  : the β/η rules for products and identity
--           (fst-pair, snd-pair, eta-pair, id-left, id-right).
--           These are the classical "computational" rewrites; the
--           β-only Takahashi confluence proof targets exactly this set.
--
--   _⟶s_  : the structural rules forced by the category / product
--           universal property (assoc, pair-dist). These are required
--           for confluence of the full CCC rewrite system — without
--           them, critical pairs involving curry-β vs curry-η at CCT1
--           do not close.
--
-- The split lets the β-only proof chain continue to operate on _⟶β_
-- while the full-CCC proof chain unions β and s and proves confluence
-- of the union via Newman (SN + local confluence).
--
-- NO congruence rules here — those live in
-- Theory.Syntax.CongruenceClosure, where they can be re-applied with
-- the full set of subterm-carrying constructors at each level.
--
-- Any level with the required CCTB generators (id, ∘, fst, snd, ⟨_,_⟩,
-- terminal) instantiates this module to get the rules on its own
-- Term type.
------------------------------------------------------------------------

module Theory.Syntax.StrongCCL.BaseRules.CCTB where

module Rules
  (Ty       : Set)
  (Unit     : Ty)
  (_×_      : Ty → Ty → Ty)
  (Term     : Ty → Ty → Set)
  (id       : ∀ {A}     → Term A A)
  (_∘_      : ∀ {A B C} → Term B C → Term A B → Term A C)
  (terminal : ∀ {A}     → Term A Unit)
  (fst      : ∀ {A B}   → Term (A × B) A)
  (snd      : ∀ {A B}   → Term (A × B) B)
  (⟨_,_⟩    : ∀ {A B C} → Term C A → Term C B → Term C (A × B))
  where

  -- β-rules: the minimal "computational" β-subset, unchanged so that the
  -- legacy β-only Takahashi proof continues to operate on this set.
  data _⟶β_ : ∀ {A B} → Term A B → Term A B → Set where
    fst-pair : ∀ {A B C} {f : Term C A} {g : Term C B} →
               (fst ∘ ⟨ f , g ⟩) ⟶β f
    snd-pair : ∀ {A B C} {f : Term C A} {g : Term C B} →
               (snd ∘ ⟨ f , g ⟩) ⟶β g
    eta-pair : ∀ {A B} → ⟨ fst {A} {B} , snd ⟩ ⟶β id
    id-left  : ∀ {A B} {f : Term A B} → (id ∘ f) ⟶β f
    id-right : ∀ {A B} {f : Term A B} → (f ∘ id) ⟶β f

  infix 4 _⟶β_

  -- Structural / universal-property rules beyond the β-subset. Required
  -- for full CCC confluence.
  data _⟶s_ : ∀ {A B} → Term A B → Term A B → Set where
    assoc        : ∀ {A B C D} {f : Term C D} {g : Term B C} {h : Term A B} →
                   ((f ∘ g) ∘ h) ⟶s (f ∘ (g ∘ h))
    pair-dist    : ∀ {A B C D} {f : Term C A} {g : Term C B} {h : Term D C} →
                   (⟨ f , g ⟩ ∘ h) ⟶s ⟨ f ∘ h , g ∘ h ⟩
    eta-pair-gen : ∀ {A B C} {h : Term C (A × B)} →
                   ⟨ fst ∘ h , snd ∘ h ⟩ ⟶s h
    term-unique  : ∀ {A B} {f : Term A B} → (terminal ∘ f) ⟶s terminal

  infix 4 _⟶s_
