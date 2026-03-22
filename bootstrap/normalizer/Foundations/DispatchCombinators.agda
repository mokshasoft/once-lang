------------------------------------------------------------------------
-- DispatchCombinators: Proof combinators for TermF position dispatch
--
-- This module provides reusable combinators for the common patterns
-- in is-id-pos-N and nstep-at-N proofs:
--
--   1. assoc-l-under: Left-associate and apply a reduction under ∘
--   2. reassoc-inr: Reassociate under inr on the right
--   3. reassoc-inr-In: Reassociate under inr ∘ In on the right
--
-- These factor out the repetitive `⟶1 assoc-l >> ⟶1 (⟶-∘-l X)` and
-- `∘-cong-right' inr (⟶1 assoc-r >> ...)` patterns.
------------------------------------------------------------------------

module normalizer.Foundations.DispatchCombinators where

open import normalizer.Foundations.ReductionCombinators public
open import normalizer.Foundations.Catamorphisms
  using (∘-cong-right'; ∘-cong-left'; ⟨⟩-cong)

open import normalizer.Foundations.CCC
  using (_∘_; inl; inr; In; assoc-l; assoc-r; ⟶-∘-l; [_,_]; ⟦_⟧F; μ_;
         ⟨_,_⟩; fst; snd; pair-comp; fst-pair; snd-pair; _+_)

------------------------------------------------------------------------
-- Left-association combinator
--
-- Common pattern: left-associate and apply a single-step reduction
-- under composition on the left side.
--
-- Given:  f ∘ (g ∘ h)   and   r : (f ∘ g) ⟶ f'
-- Result: f' ∘ h
--
--   f ∘ (g ∘ h)
--   ⟶ (f ∘ g) ∘ h      [assoc-l]
--   ⟶ f' ∘ h           [⟶-∘-l r]
------------------------------------------------------------------------

-- assoc-l : f ∘ (g ∘ h) ⟶ (f ∘ g) ∘ h
-- We want: after assoc-l, apply r : (f ∘ g) ⟶ f' under ∘ on the left
assoc-l-under : ∀ {A B C D} {f : Term C D} {g : Term B C} {h : Term A B} {f' : Term B D} →
                ((f ∘ g) ⟶ f') →
                (f ∘ (g ∘ h)) ⟶* (f' ∘ h)
assoc-l-under r = ⟶1 assoc-l >> ⟶1 (⟶-∘-l r)

------------------------------------------------------------------------
-- Right-congruence under inr
--
-- Common pattern: apply a reduction under `inr ∘ _` on the right.
--
-- Given:  g ⟶* g'
-- Result: (inr ∘ g) ⟶* (inr ∘ g')
--
-- Note: inr {A} {B} : Term B (A + B)
------------------------------------------------------------------------

under-inr : ∀ {X A B} {g g' : Term X B} →
            (g ⟶* g') →
            (inr {A} {B} ∘ g) ⟶* (inr ∘ g')
under-inr = ∘-cong-right' inr

------------------------------------------------------------------------
-- Right-congruence under In
------------------------------------------------------------------------

under-In : ∀ {F X} {h h' : Term X (⟦ F ⟧F (μ_ F))} →
           (h ⟶* h') →
           (In {F} ∘ h) ⟶* (In ∘ h')
under-In = ∘-cong-right' In

------------------------------------------------------------------------
-- Common proof step: navigate one level through case-inr
--
-- This encapsulates the very common pattern:
--   ⟶1 assoc-l >> ⟶1 (⟶-∘-l case-inr)
--
-- Which appears in every is-id-pos-N proof.
--
-- Given: [ f , g ] ∘ (inr ∘ t)
-- Result: g ∘ t
------------------------------------------------------------------------

open import normalizer.Foundations.CCC using (case-inr; case-inl)

-- [ f , g ] ∘ (inr ∘ t) ⟶* g ∘ t
step-case-inr : ∀ {A B C R} {f : Term B R} {g : Term C R} {t : Term A C} →
                ([ f , g ] ∘ (inr ∘ t)) ⟶* (g ∘ t)
step-case-inr = assoc-l-under case-inr

-- [ f , g ] ∘ (inl ∘ t) ⟶* f ∘ t
step-case-inl : ∀ {A B C R} {f : Term B R} {g : Term C R} {t : Term A B} →
                ([ f , g ] ∘ (inl ∘ t)) ⟶* (f ∘ t)
step-case-inl = assoc-l-under case-inl

------------------------------------------------------------------------
-- Associativity sandwich combinator
--
-- Very common pattern (118+ occurrences in RefoldIdempotent):
--   ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' t r) (step assoc-r done))
--
-- Given: (f ∘ g) ⟶* (h ∘ k)
-- Returns: f ∘ (g ∘ t) ⟶* h ∘ (k ∘ t)
--
-- Steps:
--   f ∘ (g ∘ t)
--   ⟶ (f ∘ g) ∘ t       [assoc-l]
--   ⟶* (h ∘ k) ∘ t      [∘-cong-left' t r]
--   ⟶ h ∘ (k ∘ t)       [assoc-r]
------------------------------------------------------------------------

assoc-sandwich : ∀ {A B C D E} {f : Term C D} {g : Term B C} {h : Term E D} {k : Term B E}
                 (t : Term A B) →
                 ((f ∘ g) ⟶* (h ∘ k)) →
                 (f ∘ (g ∘ t)) ⟶* (h ∘ (k ∘ t))
assoc-sandwich t r = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' t r) (step assoc-r done))

------------------------------------------------------------------------
-- Right-reassociation chain helpers
--
-- Pattern in is-id-pos-N proofs:
--   ⟶1 assoc-r >> ∘-cong-right' inr (⟶1 assoc-r >> ∘-cong-right' In (...))
--
-- reassoc-under-inr: Right-associate and continue under inr
-- reassoc-under-In: Right-associate and continue under In
------------------------------------------------------------------------

-- f ∘ (g ∘ h) ⟶* f ∘ result, where (g ∘ h) ⟶* result via assoc-r and inner reduction
reassoc-under-inr : ∀ {X A B C} {g : Term B C} {h : Term X B} {result : Term X C} →
                    ((g ∘ h) ⟶* result) →
                    (inr {A} ∘ (g ∘ h)) ⟶* (inr ∘ result)
reassoc-under-inr inner = ∘-cong-right' inr inner

reassoc-under-In : ∀ {F X} {g : Term X (⟦ F ⟧F (μ_ F))} {result : Term X (⟦ F ⟧F (μ_ F))} →
                   (g ⟶* result) →
                   (In {F} ∘ g) ⟶* (In ∘ result)
reassoc-under-In inner = ∘-cong-right' In inner

------------------------------------------------------------------------
-- Pair induction step combinator
--
-- Common pattern in RefoldIdempotent recursive cases (5 instances):
-- Reduces (fmap (Id ⊗ Id) c ∘ ⟨a, b⟩) to ⟨a, b⟩ using two IH proofs.
--
-- Given: c ∘ a ⟶* a  and  c ∘ b ⟶* b
-- Returns: ⟨ c ∘ fst , c ∘ snd ⟩ ∘ ⟨ a , b ⟩ ⟶* ⟨ a , b ⟩
--
-- Steps:
--   ⟨ c ∘ fst , c ∘ snd ⟩ ∘ ⟨ a , b ⟩
--   ⟶ ⟨ (c ∘ fst) ∘ ⟨a,b⟩ , (c ∘ snd) ∘ ⟨a,b⟩ ⟩   [pair-comp]
--   ⟶* ⟨ c ∘ a , c ∘ b ⟩                          [assoc-r, fst-pair, snd-pair]
--   ⟶* ⟨ a , b ⟩                                  [ih-a, ih-b]
------------------------------------------------------------------------

-- Note: Both pair components must have the same type A (e.g., TermCode')
pair-ih-step : ∀ {X A} {c : Term A A}
               {a : Term X A} {b : Term X A}
               (ih-a : (c ∘ a) ⟶* a)
               (ih-b : (c ∘ b) ⟶* b) →
               (⟨ c ∘ fst , c ∘ snd ⟩ ∘ ⟨ a , b ⟩) ⟶* ⟨ a , b ⟩
pair-ih-step {c = c} ih-a ih-b =
  ⟶*-trans (step pair-comp done)
    (⟨⟩-cong
      (⟶*-trans (step assoc-r done)
        (⟶*-trans (∘-cong-right' c (step fst-pair done))
          ih-a))
      (⟶*-trans (step assoc-r done)
        (⟶*-trans (∘-cong-right' c (step snd-pair done))
          ih-b)))

------------------------------------------------------------------------
-- Chained inr congruence combinators
--
-- Common pattern in RefoldIdempotent reduce-chain definitions:
--   ⟶*-trans r0 (∘-cong-right' inr
--     (⟶*-trans r1 (∘-cong-right' inr
--       (⟶*-trans r2 (∘-cong-right' inr r3)))))
--
-- These combinators compose a reduction with pushing it under inr.
------------------------------------------------------------------------

-- Compose reduction r0 with r1 pushed under inr
-- Given: t0 ⟶* inr ∘ t1 and t1 ⟶* t2
-- Returns: t0 ⟶* inr ∘ t2
-- Note: inr {A} {B} : Term B (A + B)
infixr 5 _>>inr_
_>>inr_ : ∀ {X A B} {t0 : Term X (A + B)} {t1 t2 : Term X B} →
          (t0 ⟶* (inr {A} {B} ∘ t1)) →
          (t1 ⟶* t2) →
          t0 ⟶* (inr ∘ t2)
r0 >>inr r1 = ⟶*-trans r0 (∘-cong-right' inr r1)

------------------------------------------------------------------------
-- Right-associativity under In
--
-- Common pattern in step2 definitions:
--   ⟶*-trans (step assoc-r done) (∘-cong-right' In reduce-chain)
--
-- Given: (In ∘ x) ∘ y  and  x ∘ y ⟶* result
-- Returns: (In ∘ x) ∘ y ⟶* In ∘ result
------------------------------------------------------------------------

assoc-r-In : ∀ {F X Y} {x : Term Y (⟦ F ⟧F (μ_ F))} {y : Term X Y} {result : Term X (⟦ F ⟧F (μ_ F))} →
             ((x ∘ y) ⟶* result) →
             ((In {F} ∘ x) ∘ y) ⟶* (In ∘ result)
assoc-r-In inner = ⟶*-trans (step assoc-r done) (∘-cong-right' In inner)

------------------------------------------------------------------------
-- fmap (K X ⊗ K Y) elimination
--
-- Common pattern in terminal position proofs (6 instances):
--   ∘-cong-left' payload (fmap-KK-id X Y f) >> ⟶1 id-left
--
-- Reduces: (fmap (K X ⊗ K Y) f) ∘ payload ⟶* payload
------------------------------------------------------------------------

open import normalizer.Foundations.Catamorphisms using (fmap-KK-id)
open import normalizer.Foundations.CCC using (id; id-left; K; _⊗_; fmap; _*_)

fmap-KK-elim : ∀ {A B X Y} {payload : Term A (X * Y)} {f : Term B B} →
               ((fmap (K X ⊗ K Y) f) ∘ payload) ⟶* payload
fmap-KK-elim {X = X} {Y = Y} {payload = payload} {f = f} =
  ⟶*-trans (∘-cong-left' payload (fmap-KK-id X Y f)) (step id-left done)
