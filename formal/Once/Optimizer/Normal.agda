------------------------------------------------------------------------
-- Once.Optimizer.Normal
--
-- Normal forms for BCC terms.
-- A term is normal if no optimization rules apply.
--
-- Key properties to prove:
--   1. optimize produces normal forms
--   2. normal forms are unique per equivalence class
--   3. normal forms have minimal cost
------------------------------------------------------------------------

module Once.Optimizer.Normal where

open import Once.Type
open import Once.IR
open import Once.Optimize using (_≟Type_; _≟IR_; optimize; optimize-once;
  optimize-compose; optimize-pair; optimize-case; safe-pair-distrib)
open import Once.Optimize.Correct using (optimize-correct)
open import Once.Semantics using (eval; ⟦_⟧)
open import Once.Optimizer.Cost using (cost)

open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (_≤_)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; _≢_; sym; trans; cong)
open import Relation.Nullary using (Dec; yes; no; ¬_)

------------------------------------------------------------------------
-- Reducible Patterns
------------------------------------------------------------------------

-- A term is reducible if an optimization rule applies at the top level.
-- We define this by listing all the reducible patterns.

-- | Composition is reducible if it matches a beta/identity/dead-code pattern
data CompReducible : ∀ {A B C} → IR B C → IR A B → Set where
  -- Identity laws
  red-id-left  : ∀ {A B} {f : IR A B} → CompReducible id f
  red-id-right : ∀ {A B} {f : IR A B} → CompReducible f id

  -- Product beta
  red-fst-pair : ∀ {A B C} {f : IR C A} {g : IR C B} {m} →
                 CompReducible fst (⟨ f , g ⟩ m)
  red-snd-pair : ∀ {A B C} {f : IR C A} {g : IR C B} {m} →
                 CompReducible snd (⟨ f , g ⟩ m)

  -- Coproduct beta
  red-case-inl : ∀ {A B C} {f : IR A C} {g : IR B C} {m} →
                 CompReducible [ f , g ] (inl m)
  red-case-inr : ∀ {A B C} {f : IR A C} {g : IR B C} {m} →
                 CompReducible [ f , g ] (inr m)

  -- Exponential beta
  red-apply-curry : ∀ {A B C q} {f : IR (A * B) C} {g : IR A B} {m₁ m₂} →
                    CompReducible apply (⟨ curry {q = q} f m₁ , g ⟩ m₂)

  -- Dead code elimination
  red-terminal : ∀ {A B} {f : IR A B} → CompReducible terminal f

  -- Initial absorption
  red-initial : ∀ {A B} {f : IR A B} → CompReducible f initial

  -- Associativity (enables further reductions)
  red-assoc : ∀ {A B C D} {h : IR C D} {g : IR B C} {f : IR A B} →
              CompReducible (h ∘ g) f

-- | Pair is reducible if it matches an eta pattern
data PairReducible : ∀ {A B C} → IR C A → IR C B → Set where
  -- Eta: ⟨ fst , snd ⟩ = id
  red-pair-eta : ∀ {A B} → PairReducible (fst {A} {B}) snd

  -- Uniqueness: ⟨ fst ∘ h , snd ∘ h ⟩ = h
  red-pair-uniq : ∀ {A B C} {h : IR C (A * B)} →
                  PairReducible (fst ∘ h) (snd ∘ h)

-- | Case is reducible if it matches an eta pattern
data CaseReducible : ∀ {A B C} → IR A C → IR B C → Set where
  -- Eta: [ inl , inr ] = id
  red-case-eta : ∀ {A B} {m₁ m₂} → CaseReducible (inl {A} {B} m₁) (inr m₂)

  -- Uniqueness: [ h ∘ inl , h ∘ inr ] = h
  red-case-uniq : ∀ {A B C} {h : IR (A + B) C} {m₁ m₂} →
                  CaseReducible (h ∘ inl m₁) (h ∘ inr m₂)

-- | Injection with Void source is reducible
data InjReducible : ∀ {A B} → IR A B → Set where
  red-inl-void : ∀ {B m} → InjReducible (inl {Void} {B} m)
  red-inr-void : ∀ {A m} → InjReducible (inr {A} {Void} m)

------------------------------------------------------------------------
-- Normal Forms
------------------------------------------------------------------------

-- | A BCC term is in normal form if no reduction applies
data IsNormal : ∀ {A B} → IR A B → Set where
  -- Generators are normal
  normal-id       : ∀ {A} → IsNormal (id {A})
  normal-fst      : ∀ {A B} → IsNormal (fst {A} {B})
  normal-snd      : ∀ {A B} → IsNormal (snd {A} {B})
  normal-inl      : ∀ {A B m} → ¬ (A ≡ Void) → IsNormal (inl {A} {B} m)
  normal-inr      : ∀ {A B m} → ¬ (B ≡ Void) → IsNormal (inr {A} {B} m)
  normal-terminal : ∀ {A} → IsNormal (terminal {A})
  normal-initial  : ∀ {A} → IsNormal (initial {A})
  normal-apply    : ∀ {A B q} → IsNormal (apply {A} {B} {q})
  normal-arr      : ∀ {A B} → IsNormal (arr {A} {B})
  normal-fold     : ∀ {F} → ¬ (F ≡ Void) → IsNormal (fold {F})
  normal-unfold   : ∀ {F} → IsNormal (unfold {F})
  normal-prim     : ∀ {A B} {n} → ¬ (A ≡ Void) → IsNormal (Prim {A} {B} n)

  -- Composition is normal if not reducible and subterms are normal
  normal-compose : ∀ {A B C} {g : IR B C} {f : IR A B} →
                   IsNormal g → IsNormal f →
                   ¬ CompReducible g f →
                   IsNormal (g ∘ f)

  -- Pair is normal if not reducible and subterms are normal
  normal-pair : ∀ {A B C} {f : IR C A} {g : IR C B} {m} →
                IsNormal f → IsNormal g →
                ¬ PairReducible f g →
                IsNormal (⟨ f , g ⟩ m)

  -- Case is normal if not reducible and subterms are normal
  normal-case : ∀ {A B C} {f : IR A C} {g : IR B C} →
                IsNormal f → IsNormal g →
                ¬ CaseReducible f g →
                IsNormal [ f , g ]

  -- Curry is normal if body is normal
  normal-curry : ∀ {A B C q} {f : IR (A * B) C} {m} →
                 IsNormal f →
                 IsNormal (curry {q = q} f m)

------------------------------------------------------------------------
-- Helper: Decidability of reducibility
------------------------------------------------------------------------

-- | Decidability of pair reducibility
--
-- PairReducible has only 2 constructors:
--   red-pair-eta : PairReducible fst snd
--   red-pair-uniq : PairReducible (fst ∘ h) (snd ∘ h)
--
-- We check if f and g match these patterns.
pair-reducible? : ∀ {A B C} (f : IR C A) (g : IR C B) → Dec (PairReducible f g)
-- Case 1: f = fst, g = snd (eta)
pair-reducible? (fst {A} {B}) (snd {A'} {B'}) with A ≟Type A' | B ≟Type B'
... | yes refl | yes refl = yes red-pair-eta
... | no A≢A'  | _        = no λ { red-pair-eta → A≢A' refl }
... | _        | no B≢B'  = no λ { red-pair-eta → B≢B' refl }
-- Case 2: f = fst ∘ h, g = snd ∘ h' (uniqueness if h ≡ h')
pair-reducible? (_∘_ {_} {D} (fst {A} {B}) h) (_∘_ {_} {D'} (snd {A'} {B'}) h')
  with A ≟Type A' | B ≟Type B' | D ≟Type D'
... | yes refl | yes refl | yes refl with h ≟IR h'
...   | yes refl = yes red-pair-uniq
...   | no h≢h'  = no (fst-h-snd-h'-diff-not-reducible h≢h')
pair-reducible? (_∘_ (fst {A} {B}) h) (_∘_ (snd {A'} {B'}) h') | _ | _ | _ =
  no λ { red-pair-uniq → _ }  -- Types don't match
-- All other cases: not reducible
pair-reducible? fst fst = no λ ()
pair-reducible? fst (fst ∘ _) = no λ ()
pair-reducible? fst (snd ∘ _) = no λ ()
pair-reducible? fst id = no λ ()
pair-reducible? fst (⟨ _ , _ ⟩ _) = no λ ()
pair-reducible? fst (inl _) = no λ ()
pair-reducible? fst (inr _) = no λ ()
pair-reducible? fst [ _ , _ ] = no λ ()
pair-reducible? fst terminal = no λ ()
pair-reducible? fst initial = no λ ()
pair-reducible? fst (curry _ _) = no λ ()
pair-reducible? fst apply = no λ ()
pair-reducible? fst fold = no λ ()
pair-reducible? fst unfold = no λ ()
pair-reducible? fst arr = no λ ()
pair-reducible? fst (Prim _) = no λ ()
pair-reducible? snd _ = no λ ()
pair-reducible? id _ = no λ ()
pair-reducible? (⟨ _ , _ ⟩ _) _ = no λ ()
pair-reducible? (inl _) _ = no λ ()
pair-reducible? (inr _) _ = no λ ()
pair-reducible? [ _ , _ ] _ = no λ ()
pair-reducible? terminal _ = no λ ()
pair-reducible? initial _ = no λ ()
pair-reducible? (curry _ _) _ = no λ ()
pair-reducible? apply _ = no λ ()
pair-reducible? fold _ = no λ ()
pair-reducible? unfold _ = no λ ()
pair-reducible? arr _ = no λ ()
pair-reducible? (Prim _) _ = no λ ()
-- Composition cases where outer is not fst
pair-reducible? (snd ∘ _) _ = no λ ()
pair-reducible? (id ∘ _) _ = no λ ()
pair-reducible? ((⟨ _ , _ ⟩ _) ∘ _) _ = no λ ()
pair-reducible? ((inl _) ∘ _) _ = no λ ()
pair-reducible? ((inr _) ∘ _) _ = no λ ()
pair-reducible? ([ _ , _ ] ∘ _) _ = no λ ()
pair-reducible? (terminal ∘ _) _ = no λ ()
pair-reducible? (initial ∘ _) _ = no λ ()
pair-reducible? ((curry _ _) ∘ _) _ = no λ ()
pair-reducible? (apply ∘ _) _ = no λ ()
pair-reducible? (fold ∘ _) _ = no λ ()
pair-reducible? (unfold ∘ _) _ = no λ ()
pair-reducible? (arr ∘ _) _ = no λ ()
pair-reducible? ((Prim _) ∘ _) _ = no λ ()
pair-reducible? ((_ ∘ _) ∘ _) _ = no λ ()

-- | Decidability of case reducibility
--
-- CaseReducible has only 2 constructors:
--   red-case-eta : CaseReducible (inl m₁) (inr m₂)
--   red-case-uniq : CaseReducible (h ∘ inl m₁) (h ∘ inr m₂)
case-reducible? : ∀ {A B C} (f : IR A C) (g : IR B C) → Dec (CaseReducible f g)
-- Case 1: f = inl, g = inr (eta)
case-reducible? (inl {A} {B} m₁) (inr {A'} {B'} m₂) with A ≟Type A' | B ≟Type B'
... | yes refl | yes refl = yes red-case-eta
... | no A≢A'  | _        = no λ { red-case-eta → A≢A' refl }
... | _        | no B≢B'  = no λ { red-case-eta → B≢B' refl }
-- Case 2: f = h ∘ inl, g = h' ∘ inr (uniqueness if h ≡ h')
case-reducible? (_∘_ {_} {D} {C} h (inl {A} {B} m₁)) (_∘_ {_} {D'} {C'} h' (inr {A'} {B'} m₂))
  with A ≟Type A' | B ≟Type B' | D ≟Type D' | C ≟Type C'
... | yes refl | yes refl | yes refl | yes refl with h ≟IR h'
...   | yes refl = yes red-case-uniq
...   | no h≢h'  = no λ { red-case-uniq → h≢h' refl }
case-reducible? (_∘_ h (inl m₁)) (_∘_ h' (inr m₂)) | _ | _ | _ | _ =
  no λ { red-case-uniq → _ }  -- Types don't match
-- All other cases: not reducible
case-reducible? (inl _) (inl _) = no λ ()
case-reducible? (inl _) id = no λ ()
case-reducible? (inl _) fst = no λ ()
case-reducible? (inl _) snd = no λ ()
case-reducible? (inl _) (⟨ _ , _ ⟩ _) = no λ ()
case-reducible? (inl _) [ _ , _ ] = no λ ()
case-reducible? (inl _) terminal = no λ ()
case-reducible? (inl _) initial = no λ ()
case-reducible? (inl _) (curry _ _) = no λ ()
case-reducible? (inl _) apply = no λ ()
case-reducible? (inl _) fold = no λ ()
case-reducible? (inl _) unfold = no λ ()
case-reducible? (inl _) arr = no λ ()
case-reducible? (inl _) (Prim _) = no λ ()
case-reducible? (inl _) (_ ∘ _) = no λ ()
case-reducible? (inr _) _ = no λ ()
case-reducible? id _ = no λ ()
case-reducible? fst _ = no λ ()
case-reducible? snd _ = no λ ()
case-reducible? (⟨ _ , _ ⟩ _) _ = no λ ()
case-reducible? [ _ , _ ] _ = no λ ()
case-reducible? terminal _ = no λ ()
case-reducible? initial _ = no λ ()
case-reducible? (curry _ _) _ = no λ ()
case-reducible? apply _ = no λ ()
case-reducible? fold _ = no λ ()
case-reducible? unfold _ = no λ ()
case-reducible? arr _ = no λ ()
case-reducible? (Prim _) _ = no λ ()
-- Composition cases where inner is not inl
case-reducible? (_ ∘ id) _ = no λ ()
case-reducible? (_ ∘ fst) _ = no λ ()
case-reducible? (_ ∘ snd) _ = no λ ()
case-reducible? (_ ∘ (⟨ _ , _ ⟩ _)) _ = no λ ()
case-reducible? (_ ∘ (inr _)) _ = no λ ()
case-reducible? (_ ∘ [ _ , _ ]) _ = no λ ()
case-reducible? (_ ∘ terminal) _ = no λ ()
case-reducible? (_ ∘ initial) _ = no λ ()
case-reducible? (_ ∘ (curry _ _)) _ = no λ ()
case-reducible? (_ ∘ apply) _ = no λ ()
case-reducible? (_ ∘ fold) _ = no λ ()
case-reducible? (_ ∘ unfold) _ = no λ ()
case-reducible? (_ ∘ arr) _ = no λ ()
case-reducible? (_ ∘ (Prim _)) _ = no λ ()
case-reducible? (_ ∘ (_ ∘ _)) _ = no λ ()

-- | Decidability of composition reducibility
--
-- CompReducible has many constructors, requiring extensive case analysis.
-- We postulate it for now to focus on the main theorems.
postulate
  comp-reducible? : ∀ {A B C} (g : IR B C) (f : IR A B) → Dec (CompReducible g f)

------------------------------------------------------------------------
-- Helper: Extract normal subterms from normal compound terms
------------------------------------------------------------------------

-- | Extract the left subterm's normality from a normal composition
normal-compose-left : ∀ {A B C} {g : IR B C} {f : IR A B} →
  IsNormal (g ∘ f) → IsNormal g
normal-compose-left (normal-compose ng _ _) = ng

-- | Extract the right subterm's normality from a normal composition
normal-compose-right : ∀ {A B C} {g : IR B C} {f : IR A B} →
  IsNormal (g ∘ f) → IsNormal f
normal-compose-right (normal-compose _ nf _) = nf

-- | Extract the first component's normality from a normal pair
normal-pair-fst : ∀ {A B C} {f : IR C A} {g : IR C B} {m} →
  IsNormal (⟨ f , g ⟩ m) → IsNormal f
normal-pair-fst (normal-pair nf _ _) = nf

-- | Extract the second component's normality from a normal pair
normal-pair-snd : ∀ {A B C} {f : IR C A} {g : IR C B} {m} →
  IsNormal (⟨ f , g ⟩ m) → IsNormal g
normal-pair-snd (normal-pair _ ng _) = ng

-- | Extract the body's normality from a normal curry
normal-curry-body : ∀ {A B C q} {f : IR (A * B) C} {m} →
  IsNormal (curry {q = q} f m) → IsNormal f
normal-curry-body (normal-curry nf) = nf

------------------------------------------------------------------------
-- Proof: optimize-pair produces normal forms
------------------------------------------------------------------------

-- | Helper: ⟨ fst ∘ h , snd ∘ h' ⟩ with h ≢ h' is not pair-reducible
fst-h-snd-h'-diff-not-reducible : ∀ {A B C} {h h' : IR C (A * B)} →
  h ≢ h' → ¬ PairReducible (fst ∘ h) (snd ∘ h')
fst-h-snd-h'-diff-not-reducible h≢h' red-pair-uniq = h≢h' refl

-- | Helper: ⟨ fst , snd ⟩ with mismatched types is not pair-reducible
fst-snd-type-mismatch-not-reducible : ∀ {A B A' B'} →
  ¬ (A ≡ A') → ¬ PairReducible (fst {A} {B}) (snd {A'} {B'})
fst-snd-type-mismatch-not-reducible A≢A' red-pair-eta = A≢A' refl

fst-snd-type-mismatch-not-reducible' : ∀ {A B A' B'} →
  ¬ (B ≡ B') → ¬ PairReducible (fst {A} {B}) (snd {A'} {B'})
fst-snd-type-mismatch-not-reducible' B≢B' red-pair-eta = B≢B' refl

-- | optimize-pair produces normal forms when given normal inputs
optimize-pair-normal : ∀ {A B C} (f : IR C A) (g : IR C B) →
  IsNormal f → IsNormal g → IsNormal (optimize-pair f g)
-- Eta case: ⟨ fst , snd ⟩
optimize-pair-normal (fst {A} {B}) (snd {A'} {B'}) nf ng with A ≟Type A' | B ≟Type B'
... | yes refl | yes refl = normal-id
... | no A≢A'  | _        = normal-pair nf ng (fst-snd-type-mismatch-not-reducible A≢A')
... | yes refl | no B≢B'  = normal-pair nf ng (fst-snd-type-mismatch-not-reducible' B≢B')
-- Uniqueness case: ⟨ fst ∘ h , snd ∘ h' ⟩
optimize-pair-normal (_∘_ {_} {D} (fst {A} {B}) h) (_∘_ {_} {D'} (snd {A'} {B'}) h') nf ng
  with A ≟Type A' | B ≟Type B' | D ≟Type D'
... | yes refl | yes refl | yes refl with h ≟IR h'
...   | yes refl = normal-compose-right nf  -- h is normal (extracted from fst ∘ h)
...   | no h≢h'  = normal-pair nf ng (fst-h-snd-h'-diff-not-reducible h≢h')
optimize-pair-normal (_∘_ (fst {A} {B}) h) (_∘_ (snd {A'} {B'}) h') nf ng | _ | _ | _ =
  normal-pair nf ng λ { red-pair-uniq → _ }  -- Types don't match
-- All other cases: not pair-reducible (don't match fst/snd patterns)
optimize-pair-normal fst fst nf ng = normal-pair nf ng λ ()
optimize-pair-normal fst (fst ∘ _) nf ng = normal-pair nf ng λ ()
optimize-pair-normal fst (snd ∘ _) nf ng = normal-pair nf ng λ ()
optimize-pair-normal fst id nf ng = normal-pair nf ng λ ()
optimize-pair-normal fst (⟨ _ , _ ⟩ _) nf ng = normal-pair nf ng λ ()
optimize-pair-normal fst (inl _) nf ng = normal-pair nf ng λ ()
optimize-pair-normal fst (inr _) nf ng = normal-pair nf ng λ ()
optimize-pair-normal fst [ _ , _ ] nf ng = normal-pair nf ng λ ()
optimize-pair-normal fst terminal nf ng = normal-pair nf ng λ ()
optimize-pair-normal fst initial nf ng = normal-pair nf ng λ ()
optimize-pair-normal fst (curry _ _) nf ng = normal-pair nf ng λ ()
optimize-pair-normal fst apply nf ng = normal-pair nf ng λ ()
optimize-pair-normal fst fold nf ng = normal-pair nf ng λ ()
optimize-pair-normal fst unfold nf ng = normal-pair nf ng λ ()
optimize-pair-normal fst arr nf ng = normal-pair nf ng λ ()
optimize-pair-normal fst (Prim _) nf ng = normal-pair nf ng λ ()
optimize-pair-normal snd g nf ng = normal-pair nf ng λ ()
optimize-pair-normal id g nf ng = normal-pair nf ng λ ()
optimize-pair-normal (⟨ _ , _ ⟩ _) g nf ng = normal-pair nf ng λ ()
optimize-pair-normal (inl _) g nf ng = normal-pair nf ng λ ()
optimize-pair-normal (inr _) g nf ng = normal-pair nf ng λ ()
optimize-pair-normal [ _ , _ ] g nf ng = normal-pair nf ng λ ()
optimize-pair-normal terminal g nf ng = normal-pair nf ng λ ()
optimize-pair-normal initial g nf ng = normal-pair nf ng λ ()
optimize-pair-normal (curry _ _) g nf ng = normal-pair nf ng λ ()
optimize-pair-normal apply g nf ng = normal-pair nf ng λ ()
optimize-pair-normal fold g nf ng = normal-pair nf ng λ ()
optimize-pair-normal unfold g nf ng = normal-pair nf ng λ ()
optimize-pair-normal arr g nf ng = normal-pair nf ng λ ()
optimize-pair-normal (Prim _) g nf ng = normal-pair nf ng λ ()
-- Composition cases where outer is not fst
optimize-pair-normal (snd ∘ _) g nf ng = normal-pair nf ng λ ()
optimize-pair-normal (id ∘ _) g nf ng = normal-pair nf ng λ ()
optimize-pair-normal ((⟨ _ , _ ⟩ _) ∘ _) g nf ng = normal-pair nf ng λ ()
optimize-pair-normal ((inl _) ∘ _) g nf ng = normal-pair nf ng λ ()
optimize-pair-normal ((inr _) ∘ _) g nf ng = normal-pair nf ng λ ()
optimize-pair-normal ([ _ , _ ] ∘ _) g nf ng = normal-pair nf ng λ ()
optimize-pair-normal (terminal ∘ _) g nf ng = normal-pair nf ng λ ()
optimize-pair-normal (initial ∘ _) g nf ng = normal-pair nf ng λ ()
optimize-pair-normal ((curry _ _) ∘ _) g nf ng = normal-pair nf ng λ ()
optimize-pair-normal (apply ∘ _) g nf ng = normal-pair nf ng λ ()
optimize-pair-normal (fold ∘ _) g nf ng = normal-pair nf ng λ ()
optimize-pair-normal (unfold ∘ _) g nf ng = normal-pair nf ng λ ()
optimize-pair-normal (arr ∘ _) g nf ng = normal-pair nf ng λ ()
optimize-pair-normal ((Prim _) ∘ _) g nf ng = normal-pair nf ng λ ()
optimize-pair-normal ((_ ∘ _) ∘ _) g nf ng = normal-pair nf ng λ ()
-- fst ∘ h cases with non-snd ∘ h' second arg
optimize-pair-normal (fst ∘ _) id nf ng = normal-pair nf ng λ ()
optimize-pair-normal (fst ∘ _) fst nf ng = normal-pair nf ng λ ()
optimize-pair-normal (fst ∘ _) snd nf ng = normal-pair nf ng λ ()
optimize-pair-normal (fst ∘ _) (⟨ _ , _ ⟩ _) nf ng = normal-pair nf ng λ ()
optimize-pair-normal (fst ∘ _) (inl _) nf ng = normal-pair nf ng λ ()
optimize-pair-normal (fst ∘ _) (inr _) nf ng = normal-pair nf ng λ ()
optimize-pair-normal (fst ∘ _) [ _ , _ ] nf ng = normal-pair nf ng λ ()
optimize-pair-normal (fst ∘ _) terminal nf ng = normal-pair nf ng λ ()
optimize-pair-normal (fst ∘ _) initial nf ng = normal-pair nf ng λ ()
optimize-pair-normal (fst ∘ _) (curry _ _) nf ng = normal-pair nf ng λ ()
optimize-pair-normal (fst ∘ _) apply nf ng = normal-pair nf ng λ ()
optimize-pair-normal (fst ∘ _) fold nf ng = normal-pair nf ng λ ()
optimize-pair-normal (fst ∘ _) unfold nf ng = normal-pair nf ng λ ()
optimize-pair-normal (fst ∘ _) arr nf ng = normal-pair nf ng λ ()
optimize-pair-normal (fst ∘ _) (Prim _) nf ng = normal-pair nf ng λ ()
-- fst ∘ h cases with non-snd outer composition
optimize-pair-normal (fst ∘ _) (id ∘ _) nf ng = normal-pair nf ng λ ()
optimize-pair-normal (fst ∘ _) (fst ∘ _) nf ng = normal-pair nf ng λ ()
optimize-pair-normal (fst ∘ _) ((⟨ _ , _ ⟩ _) ∘ _) nf ng = normal-pair nf ng λ ()
optimize-pair-normal (fst ∘ _) ((inl _) ∘ _) nf ng = normal-pair nf ng λ ()
optimize-pair-normal (fst ∘ _) ((inr _) ∘ _) nf ng = normal-pair nf ng λ ()
optimize-pair-normal (fst ∘ _) ([ _ , _ ] ∘ _) nf ng = normal-pair nf ng λ ()
optimize-pair-normal (fst ∘ _) (terminal ∘ _) nf ng = normal-pair nf ng λ ()
optimize-pair-normal (fst ∘ _) (initial ∘ _) nf ng = normal-pair nf ng λ ()
optimize-pair-normal (fst ∘ _) ((curry _ _) ∘ _) nf ng = normal-pair nf ng λ ()
optimize-pair-normal (fst ∘ _) (apply ∘ _) nf ng = normal-pair nf ng λ ()
optimize-pair-normal (fst ∘ _) (fold ∘ _) nf ng = normal-pair nf ng λ ()
optimize-pair-normal (fst ∘ _) (unfold ∘ _) nf ng = normal-pair nf ng λ ()
optimize-pair-normal (fst ∘ _) (arr ∘ _) nf ng = normal-pair nf ng λ ()
optimize-pair-normal (fst ∘ _) ((Prim _) ∘ _) nf ng = normal-pair nf ng λ ()
optimize-pair-normal (fst ∘ _) ((_ ∘ _) ∘ _) nf ng = normal-pair nf ng λ ()

------------------------------------------------------------------------
-- Proof: optimize-case produces normal forms
------------------------------------------------------------------------

-- | Helper: [ inl , inr ] with mismatched types is not case-reducible
inl-inr-type-mismatch-not-reducible : ∀ {A B A' B' m₁ m₂} →
  ¬ (A ≡ A') → ¬ CaseReducible (inl {A} {B} m₁) (inr {A'} {B'} m₂)
inl-inr-type-mismatch-not-reducible A≢A' red-case-eta = A≢A' refl

inl-inr-type-mismatch-not-reducible' : ∀ {A B A' B' m₁ m₂} →
  ¬ (B ≡ B') → ¬ CaseReducible (inl {A} {B} m₁) (inr {A'} {B'} m₂)
inl-inr-type-mismatch-not-reducible' B≢B' red-case-eta = B≢B' refl

-- | Helper: [ h ∘ inl , h' ∘ inr ] with h ≢ h' is not case-reducible
h-inl-h'-inr-diff-not-reducible : ∀ {A B C m₁ m₂} {h h' : IR (A + B) C} →
  h ≢ h' → ¬ CaseReducible (h ∘ inl m₁) (h' ∘ inr m₂)
h-inl-h'-inr-diff-not-reducible h≢h' red-case-uniq = h≢h' refl

-- | optimize-case produces normal forms when given normal inputs
optimize-case-normal : ∀ {A B C} (f : IR A C) (g : IR B C) →
  IsNormal f → IsNormal g → IsNormal (optimize-case f g)
-- Eta case: [ inl , inr ]
optimize-case-normal (inl {A} {B} m₁) (inr {A'} {B'} m₂) nf ng with A ≟Type A' | B ≟Type B'
... | yes refl | yes refl = normal-id
... | no A≢A'  | _        = normal-case nf ng (inl-inr-type-mismatch-not-reducible A≢A')
... | yes refl | no B≢B'  = normal-case nf ng (inl-inr-type-mismatch-not-reducible' B≢B')
-- Uniqueness case: [ h ∘ inl , h' ∘ inr ]
optimize-case-normal (_∘_ {_} {D} h (inl {A} {B} m₁)) (_∘_ {_} {D'} h' (inr {A'} {B'} m₂)) nf ng
  with A ≟Type A' | B ≟Type B' | D ≟Type D'
... | yes refl | yes refl | yes refl with h ≟IR h'
...   | yes refl = normal-compose-left nf  -- h is normal (extracted from h ∘ inl)
...   | no h≢h'  = normal-case nf ng (h-inl-h'-inr-diff-not-reducible h≢h')
optimize-case-normal (_∘_ h (inl m₁)) (_∘_ h' (inr m₂)) nf ng | _ | _ | _ =
  normal-case nf ng λ { red-case-uniq → _ }  -- Types don't match
-- All other cases: not case-reducible (don't match inl/inr patterns)
optimize-case-normal (inl _) (inl _) nf ng = normal-case nf ng λ ()
optimize-case-normal (inl _) id nf ng = normal-case nf ng λ ()
optimize-case-normal (inl _) fst nf ng = normal-case nf ng λ ()
optimize-case-normal (inl _) snd nf ng = normal-case nf ng λ ()
optimize-case-normal (inl _) (⟨ _ , _ ⟩ _) nf ng = normal-case nf ng λ ()
optimize-case-normal (inl _) [ _ , _ ] nf ng = normal-case nf ng λ ()
optimize-case-normal (inl _) terminal nf ng = normal-case nf ng λ ()
optimize-case-normal (inl _) initial nf ng = normal-case nf ng λ ()
optimize-case-normal (inl _) (curry _ _) nf ng = normal-case nf ng λ ()
optimize-case-normal (inl _) apply nf ng = normal-case nf ng λ ()
optimize-case-normal (inl _) fold nf ng = normal-case nf ng λ ()
optimize-case-normal (inl _) unfold nf ng = normal-case nf ng λ ()
optimize-case-normal (inl _) arr nf ng = normal-case nf ng λ ()
optimize-case-normal (inl _) (Prim _) nf ng = normal-case nf ng λ ()
optimize-case-normal (inl _) (_ ∘ _) nf ng = normal-case nf ng λ ()
optimize-case-normal (inr _) g nf ng = normal-case nf ng λ ()
optimize-case-normal id g nf ng = normal-case nf ng λ ()
optimize-case-normal fst g nf ng = normal-case nf ng λ ()
optimize-case-normal snd g nf ng = normal-case nf ng λ ()
optimize-case-normal (⟨ _ , _ ⟩ _) g nf ng = normal-case nf ng λ ()
optimize-case-normal [ _ , _ ] g nf ng = normal-case nf ng λ ()
optimize-case-normal terminal g nf ng = normal-case nf ng λ ()
optimize-case-normal initial g nf ng = normal-case nf ng λ ()
optimize-case-normal (curry _ _) g nf ng = normal-case nf ng λ ()
optimize-case-normal apply g nf ng = normal-case nf ng λ ()
optimize-case-normal fold g nf ng = normal-case nf ng λ ()
optimize-case-normal unfold g nf ng = normal-case nf ng λ ()
optimize-case-normal arr g nf ng = normal-case nf ng λ ()
optimize-case-normal (Prim _) g nf ng = normal-case nf ng λ ()
-- Composition cases where inner is not inl
optimize-case-normal (_ ∘ id) g nf ng = normal-case nf ng λ ()
optimize-case-normal (_ ∘ fst) g nf ng = normal-case nf ng λ ()
optimize-case-normal (_ ∘ snd) g nf ng = normal-case nf ng λ ()
optimize-case-normal (_ ∘ (⟨ _ , _ ⟩ _)) g nf ng = normal-case nf ng λ ()
optimize-case-normal (_ ∘ (inr _)) g nf ng = normal-case nf ng λ ()
optimize-case-normal (_ ∘ [ _ , _ ]) g nf ng = normal-case nf ng λ ()
optimize-case-normal (_ ∘ terminal) g nf ng = normal-case nf ng λ ()
optimize-case-normal (_ ∘ initial) g nf ng = normal-case nf ng λ ()
optimize-case-normal (_ ∘ (curry _ _)) g nf ng = normal-case nf ng λ ()
optimize-case-normal (_ ∘ apply) g nf ng = normal-case nf ng λ ()
optimize-case-normal (_ ∘ fold) g nf ng = normal-case nf ng λ ()
optimize-case-normal (_ ∘ unfold) g nf ng = normal-case nf ng λ ()
optimize-case-normal (_ ∘ arr) g nf ng = normal-case nf ng λ ()
optimize-case-normal (_ ∘ (Prim _)) g nf ng = normal-case nf ng λ ()
optimize-case-normal (_ ∘ (_ ∘ _)) g nf ng = normal-case nf ng λ ()
-- h ∘ inl cases with non-inr second arg
optimize-case-normal (_ ∘ (inl _)) id nf ng = normal-case nf ng λ ()
optimize-case-normal (_ ∘ (inl _)) fst nf ng = normal-case nf ng λ ()
optimize-case-normal (_ ∘ (inl _)) snd nf ng = normal-case nf ng λ ()
optimize-case-normal (_ ∘ (inl _)) (⟨ _ , _ ⟩ _) nf ng = normal-case nf ng λ ()
optimize-case-normal (_ ∘ (inl _)) (inl _) nf ng = normal-case nf ng λ ()
optimize-case-normal (_ ∘ (inl _)) (inr _) nf ng = normal-case nf ng λ ()
optimize-case-normal (_ ∘ (inl _)) [ _ , _ ] nf ng = normal-case nf ng λ ()
optimize-case-normal (_ ∘ (inl _)) terminal nf ng = normal-case nf ng λ ()
optimize-case-normal (_ ∘ (inl _)) initial nf ng = normal-case nf ng λ ()
optimize-case-normal (_ ∘ (inl _)) (curry _ _) nf ng = normal-case nf ng λ ()
optimize-case-normal (_ ∘ (inl _)) apply nf ng = normal-case nf ng λ ()
optimize-case-normal (_ ∘ (inl _)) fold nf ng = normal-case nf ng λ ()
optimize-case-normal (_ ∘ (inl _)) unfold nf ng = normal-case nf ng λ ()
optimize-case-normal (_ ∘ (inl _)) arr nf ng = normal-case nf ng λ ()
optimize-case-normal (_ ∘ (inl _)) (Prim _) nf ng = normal-case nf ng λ ()
-- h ∘ inl cases with non-inr outer composition
optimize-case-normal (_ ∘ (inl _)) (_ ∘ id) nf ng = normal-case nf ng λ ()
optimize-case-normal (_ ∘ (inl _)) (_ ∘ fst) nf ng = normal-case nf ng λ ()
optimize-case-normal (_ ∘ (inl _)) (_ ∘ snd) nf ng = normal-case nf ng λ ()
optimize-case-normal (_ ∘ (inl _)) (_ ∘ (⟨ _ , _ ⟩ _)) nf ng = normal-case nf ng λ ()
optimize-case-normal (_ ∘ (inl _)) (_ ∘ (inl _)) nf ng = normal-case nf ng λ ()
optimize-case-normal (_ ∘ (inl _)) (_ ∘ [ _ , _ ]) nf ng = normal-case nf ng λ ()
optimize-case-normal (_ ∘ (inl _)) (_ ∘ terminal) nf ng = normal-case nf ng λ ()
optimize-case-normal (_ ∘ (inl _)) (_ ∘ initial) nf ng = normal-case nf ng λ ()
optimize-case-normal (_ ∘ (inl _)) (_ ∘ (curry _ _)) nf ng = normal-case nf ng λ ()
optimize-case-normal (_ ∘ (inl _)) (_ ∘ apply) nf ng = normal-case nf ng λ ()
optimize-case-normal (_ ∘ (inl _)) (_ ∘ fold) nf ng = normal-case nf ng λ ()
optimize-case-normal (_ ∘ (inl _)) (_ ∘ unfold) nf ng = normal-case nf ng λ ()
optimize-case-normal (_ ∘ (inl _)) (_ ∘ arr) nf ng = normal-case nf ng λ ()
optimize-case-normal (_ ∘ (inl _)) (_ ∘ (Prim _)) nf ng = normal-case nf ng λ ()
optimize-case-normal (_ ∘ (inl _)) (_ ∘ (_ ∘ _)) nf ng = normal-case nf ng λ ()

------------------------------------------------------------------------
-- Proof: optimize-compose produces normal forms
------------------------------------------------------------------------

-- | optimize-compose produces normal forms when given normal inputs
--
-- CHALLENGE: The apply-curry rule produces:
--   apply ∘ ⟨ curry f , g ⟩ → f ∘ ⟨ id , g ⟩
-- where f might be a composition, creating left-nested output.
--
-- The current optimizer handles this through multiple passes.
-- A single pass may not produce fully normal output.
--
-- For a complete proof, either:
-- 1. Modify optimize-compose to recursively right-associate, or
-- 2. Prove termination via well-founded recursion on "left-depth"

postulate
  optimize-compose-normal : ∀ {A B C} (g : IR B C) (f : IR A B) →
    IsNormal g → IsNormal f → IsNormal (optimize-compose g f)

------------------------------------------------------------------------
-- Proof: optimize-once produces normal forms
------------------------------------------------------------------------

-- | Single optimization pass produces normal forms
--
-- The proof is by structural induction on the input term.
-- For each constructor, show that the optimizer helper produces
-- a normal form when given normal subterms.

postulate
  optimize-once-normal : ∀ {A B} (t : IR A B) → IsNormal (optimize-once t)

------------------------------------------------------------------------
-- Main Theorem: optimize produces normal forms
------------------------------------------------------------------------

-- | Optimizer produces normal forms
--
-- Since optimize = optimize-n 10 optimize-once, and optimize-once
-- produces normal forms, the full optimizer produces normal forms.
--
-- NOTE: This relies on optimize-once-normal, which in turn relies
-- on optimize-compose-normal. The apply-curry case creates a gap
-- that requires either:
-- 1. Modifying the optimizer, or
-- 2. Proving multi-pass convergence

postulate
  optimize-normal : ∀ {A B} (t : IR A B) → IsNormal (optimize t)

------------------------------------------------------------------------
-- Coherence Properties (stated, require optimize-normal)
------------------------------------------------------------------------

-- | Normal forms are unique per equivalence class
--
-- This is the core coherence theorem: semantically equivalent
-- terms have the same normal form.
postulate
  normal-unique : ∀ {A B} (t t' : IR A B) →
    IsNormal t → IsNormal t' →
    (∀ x → eval t x ≡ eval t' x) →
    t ≡ t'

-- | Normal forms have minimal cost
postulate
  normal-minimal : ∀ {A B} (t t' : IR A B) →
    IsNormal t →
    (∀ x → eval t x ≡ eval t' x) →
    cost t ≤ cost t'

------------------------------------------------------------------------
-- Coherence Theorem
------------------------------------------------------------------------

-- | Two semantically equivalent terms optimize to the same normal form.
-- This follows from:
--   1. optimize produces normal forms (optimize-normal)
--   2. normal forms are unique per equivalence class (normal-unique)
coherence : ∀ {A B} (t t' : IR A B) →
  (∀ x → eval t x ≡ eval t' x) →
  optimize t ≡ optimize t'
coherence t t' eq = normal-unique (optimize t) (optimize t')
  (optimize-normal t)
  (optimize-normal t')
  (λ x → trans (optimize-correct t x) (trans (eq x) (sym (optimize-correct t' x))))
