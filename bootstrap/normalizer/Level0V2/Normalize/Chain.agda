------------------------------------------------------------------------
-- Normalize.Chain: Reduction proof infrastructure
--
-- Provides the Chain type for writing reduction proofs with explicit
-- intermediate terms. This avoids deep nesting and helps type-checking.
------------------------------------------------------------------------

module normalizer.Level0V2.Normalize.Chain where

open import normalizer.Foundations.Types public
open import normalizer.Foundations.MinimalCCC public
open import normalizer.Foundations.Encoding public
open import normalizer.Foundations.ReductionCombinators public
open import normalizer.Level0V2.NoRedex hiding (is-id) public
open import normalizer.Level0V2.Normalizer
  using (∘-cong-left'; ∘-cong-right'; ⟨⟩-cong) public

------------------------------------------------------------------------
-- Common helper lemmas
------------------------------------------------------------------------

-- swap reduces pairs: ⟨ snd , fst ⟩ ∘ ⟨ a , b ⟩ ⟶* ⟨ b , a ⟩
abstract
  swap-β : ∀ {X A B} {a : Term X A} {b : Term X B} →
           (⟨ snd , fst ⟩ ∘ ⟨ a , b ⟩) ⟶* ⟨ b , a ⟩
  swap-β = ⟶*-trans (step pair-comp done)
                    (⟨⟩-cong (step snd-pair done) (step fst-pair done))

-- ⟨ f ∘ snd , fst ⟩ ∘ ⟨ p , x ⟩ ⟶* ⟨ f ∘ x , p ⟩
abstract
  pair-snd-fst-β : ∀ {X P A B} {f : Term A B} {p : Term X P} {x : Term X A} →
                   (⟨ f ∘ snd , fst ⟩ ∘ ⟨ p , x ⟩) ⟶* ⟨ f ∘ x , p ⟩
  pair-snd-fst-β {f = f} = ⟶*-trans (step pair-comp done)
                            (⟨⟩-cong (⟶*-trans (step assoc-r done)
                                               (∘-cong-right' f (step snd-pair done)))
                                     (step fst-pair done))

-- curry-β-ext as multi-step (wraps primitive)
abstract
  curry-β-ext* : ∀ {X A B C} {f : Term (A * B) C} {h : Term X A} {g : Term X B} →
                (apply ∘ ⟨ curry f ∘ h , g ⟩) ⟶* (f ∘ ⟨ h , g ⟩)
  curry-β-ext* = step curry-β-ext done

------------------------------------------------------------------------
-- Distribution and caseWithCtx
------------------------------------------------------------------------

-- Distribution: P × (A + B) → (P × A) + (P × B)
distrib : ∀ {P A B : Ty} → Term (P * (A + B)) ((P * A) + (P * B))
distrib = apply ∘ ⟨ [ curry (inl ∘ ⟨ snd , fst ⟩) , curry (inr ∘ ⟨ snd , fst ⟩) ] ∘ snd , fst ⟩

-- Case with context: like case but threads context through
caseWithCtx : ∀ {P A B D : Ty} →
              Term (P * A) D → Term (P * B) D →
              Term (P * (A + B)) D
caseWithCtx l r = [ l , r ] ∘ distrib

-- Helper: the two curry terms in distrib
curry-inl-swap : ∀ {P A B} → Term A (P ⇒ (P * A) + (P * B))
curry-inl-swap {P} {A} {B} = curry (inl {P * A} {P * B} ∘ ⟨ snd {A} {P} , fst {A} {P} ⟩)

curry-inr-swap : ∀ {P A B} → Term B (P ⇒ (P * A) + (P * B))
curry-inr-swap {P} {A} {B} = curry (inr {P * A} {P * B} ∘ ⟨ snd {B} {P} , fst {B} {P} ⟩)

------------------------------------------------------------------------
-- Distrib reduction lemmas
------------------------------------------------------------------------

abstract
  distrib-inl : ∀ {X P A B} {p : Term X P} {a : Term X A} →
                (distrib {P} {A} {B} ∘ ⟨ p , inl ∘ a ⟩) ⟶* (inl ∘ ⟨ p , a ⟩)
  distrib-inl {X} {P} {A} {B} {p} {a} = runChain (
    let caseTerm = [ curry-inl-swap {P} {A} {B} , curry-inr-swap {P} {A} {B} ] in
    (distrib ∘ ⟨ p , inl ∘ a ⟩)
      ∵ ⟶1 assoc-r ⟶
    (apply ∘ (⟨ caseTerm ∘ snd , fst ⟩ ∘ ⟨ p , inl ∘ a ⟩))
      ∵ ∘-cong-right' apply pair-snd-fst-β ⟶
    (apply ∘ ⟨ caseTerm ∘ (inl ∘ a) , p ⟩)
      ∵ ∘-cong-right' apply (⟨⟩-cong case-step done) ⟶
    (apply ∘ ⟨ curry-inl-swap ∘ a , p ⟩)
      ∵ curry-β-ext* ⟶
    ((inl ∘ ⟨ snd , fst ⟩) ∘ ⟨ a , p ⟩)
      ∵ ⟶1 assoc-r ⟶
    (inl ∘ (⟨ snd , fst ⟩ ∘ ⟨ a , p ⟩))
      ∵ ∘-cong-right' inl swap-β ⟶
    (inl ∘ ⟨ p , a ⟩)
      ∎)
    where
      case-step : ([ curry-inl-swap {P} {A} {B} , curry-inr-swap {P} {A} {B} ] ∘ (inl ∘ a))
                  ⟶* (curry-inl-swap {P} {A} {B} ∘ a)
      case-step = ⟶1 assoc-l >> ∘-cong-left' a (⟶1 case-inl)

abstract
  distrib-inr : ∀ {X P A B} {p : Term X P} {b : Term X B} →
                (distrib {P} {A} {B} ∘ ⟨ p , inr ∘ b ⟩) ⟶* (inr ∘ ⟨ p , b ⟩)
  distrib-inr {X} {P} {A} {B} {p} {b} = runChain (
    let caseTerm = [ curry-inl-swap {P} {A} {B} , curry-inr-swap {P} {A} {B} ] in
    (distrib ∘ ⟨ p , inr ∘ b ⟩)
      ∵ ⟶1 assoc-r ⟶
    (apply ∘ (⟨ caseTerm ∘ snd , fst ⟩ ∘ ⟨ p , inr ∘ b ⟩))
      ∵ ∘-cong-right' apply pair-snd-fst-β ⟶
    (apply ∘ ⟨ caseTerm ∘ (inr ∘ b) , p ⟩)
      ∵ ∘-cong-right' apply (⟨⟩-cong case-step done) ⟶
    (apply ∘ ⟨ curry-inr-swap ∘ b , p ⟩)
      ∵ curry-β-ext* ⟶
    ((inr ∘ ⟨ snd , fst ⟩) ∘ ⟨ b , p ⟩)
      ∵ ⟶1 assoc-r ⟶
    (inr ∘ (⟨ snd , fst ⟩ ∘ ⟨ b , p ⟩))
      ∵ ∘-cong-right' inr swap-β ⟶
    (inr ∘ ⟨ p , b ⟩)
      ∎)
    where
      case-step : ([ curry-inl-swap {P} {A} {B} , curry-inr-swap {P} {A} {B} ] ∘ (inr ∘ b))
                  ⟶* (curry-inr-swap {P} {A} {B} ∘ b)
      case-step = ⟶1 assoc-l >> ∘-cong-left' b (⟶1 case-inr)

------------------------------------------------------------------------
-- caseWithCtx reduction lemmas
------------------------------------------------------------------------

abstract
  caseWithCtx-inl : ∀ {X P A B D} {l : Term (P * A) D} {r : Term (P * B) D}
                    {p : Term X P} {a : Term X A} →
                    (caseWithCtx l r ∘ ⟨ p , inl ∘ a ⟩) ⟶* (l ∘ ⟨ p , a ⟩)
  caseWithCtx-inl {l = l} {r = r} =
    ⟶1 assoc-r >>
    ∘-cong-right' [ l , r ] distrib-inl >>
    ⟶1 assoc-l >>
    ∘-cong-left' _ (⟶1 case-inl)

abstract
  caseWithCtx-inr : ∀ {X P A B D} {l : Term (P * A) D} {r : Term (P * B) D}
                    {p : Term X P} {b : Term X B} →
                    (caseWithCtx l r ∘ ⟨ p , inr ∘ b ⟩) ⟶* (r ∘ ⟨ p , b ⟩)
  caseWithCtx-inr {l = l} {r = r} =
    ⟶1 assoc-r >>
    ∘-cong-right' [ l , r ] distrib-inr >>
    ⟶1 assoc-l >>
    ∘-cong-left' _ (⟶1 case-inr)
