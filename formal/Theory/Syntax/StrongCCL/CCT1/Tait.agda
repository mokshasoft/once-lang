------------------------------------------------------------------------
-- Theory.Syntax.CCT1.Tait
--
-- Scaffolding for Tait's reducibility candidates, the semantic path to
-- CCT1 strong normalization. Polynomial interpretations provably fail
-- here (curry-β's nonlinear RHS), so we use a type-indexed reducibility
-- predicate.
--
-- Red : (A B : Ty) → Term A B → Set, defined by recursion on the
-- target type B. At base types Red = SN; at product type Red lifts via
-- projections; at exponential type Red lifts under application to
-- reducible arguments.
--
-- Tait obligations:
--   (1) Red-SN     : Red t → SN t                            -- proved
--   (2) Red-⟶      : Red t → t ⟶βη u → Red u                -- proved
--   (3) Red-expand : neutral t ∧ (∀ u. t ⟶βη u → Red u) → Red t
--                    -- Unit, product, arrow cases all proved.
--                    -- Arrow case dispatches on Neutral t. The ne-fst
--                    -- sub-case (t = fst at arrow target) reduces to
--                    -- the narrow postulate Red-fst-at-arrow; all
--                    -- other Neutral shapes are fully discharged.
--   (4) red-all    : ∀ t. Red t
--                    -- Replaced with a structured dispatch on Term
--                    -- constructor. terminal and atomic-at-Unit cases
--                    -- discharged. Per-constructor narrow postulates
--                    -- remain for (id, fst, snd, apply) at non-Unit
--                    -- targets and for (_∘_, ⟨_,_⟩, curry) closures.
--
-- Then SN for every CCT1 term follows by (1) + (4).
------------------------------------------------------------------------

module Theory.Syntax.StrongCCL.CCT1.Tait where

open import Data.Product
  using (Σ; _,_; proj₁; proj₂) renaming (_×_ to _∧_)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_)

open import Theory.Syntax.StrongCCL.CCT1
open import Theory.Derived.Newman using (Acc; acc)

------------------------------------------------------------------------
-- Strong normalization: accessibility under _⟶βη_
------------------------------------------------------------------------

SN : ∀ {A B} → Term A B → Set
SN = Acc _⟶βη_

------------------------------------------------------------------------
-- Reducibility predicate, by recursion on the target type
------------------------------------------------------------------------

Red : (A B : Ty) → Term A B → Set
Red A Unit     t = SN t
Red A (B × C)  t = Red A B (fst ∘ t) ∧ Red A C (snd ∘ t)
Red A (B ⇒ C)  t = SN t
               ∧ (∀ (u : Term A B) → Red A B u →
                   Red A C (apply ∘ ⟨ t , u ⟩))
-- SN baked in at arrow type so Red-SN is immediate at all types
-- (standard Tait; avoids the "Red-SN-arrow requires red-all" circularity).
-- Source A is fixed per candidate. Reducibility-transfer across
-- sources (needed for compositional lemmas) will be a separate lemma
-- once the main Tait theorems are in place.

------------------------------------------------------------------------
-- SN is preserved by projection
------------------------------------------------------------------------

-- If fst ∘ t is SN, then t is SN: any infinite chain in t would lift
-- to an infinite chain in fst ∘ t via ∘-congʳ.
SN-under-fst : ∀ {A B C} (t : Term A (B × C)) →
               SN (fst ∘ t) → SN t
SN-under-fst t (acc ih) =
  acc (λ {t'} r → SN-under-fst t' (ih (βη-Closure.∘-congʳ r)))

SN-under-snd : ∀ {A B C} (t : Term A (B × C)) →
               SN (snd ∘ t) → SN t
SN-under-snd t (acc ih) =
  acc (λ {t'} r → SN-under-snd t' (ih (βη-Closure.∘-congʳ r)))

-- SN propagates from a composition to each subterm via congruence.
SN-under-∘ˡ : ∀ {A B C} (f : Term B C) (g : Term A B) →
              SN (f ∘ g) → SN f
SN-under-∘ˡ f g (acc ih) =
  acc (λ {f'} r → SN-under-∘ˡ f' g (ih (βη-Closure.∘-congˡ r)))

SN-under-∘ʳ : ∀ {A B C} (f : Term B C) (g : Term A B) →
              SN (f ∘ g) → SN g
SN-under-∘ʳ f g (acc ih) =
  acc (λ {g'} r → SN-under-∘ʳ f g' (ih (βη-Closure.∘-congʳ r)))

SN-under-⟨,⟩ˡ : ∀ {A B C} (f : Term C A) (g : Term C B) →
                SN ⟨ f , g ⟩ → SN f
SN-under-⟨,⟩ˡ f g (acc ih) =
  acc (λ {f'} r → SN-under-⟨,⟩ˡ f' g (ih (βη-Closure.⟨,⟩-congˡ r)))

SN-under-⟨,⟩ʳ : ∀ {A B C} (f : Term C A) (g : Term C B) →
                SN ⟨ f , g ⟩ → SN g
SN-under-⟨,⟩ʳ f g (acc ih) =
  acc (λ {g'} r → SN-under-⟨,⟩ʳ f g' (ih (βη-Closure.⟨,⟩-congʳ r)))

SN-under-curry : ∀ {A B C} (f : Term (A × B) C) →
                 SN (curry f) → SN f
SN-under-curry f (acc ih) =
  acc (λ {f'} r → SN-under-curry f' (ih (βη-Closure.curry-cong r)))

------------------------------------------------------------------------
-- Red-SN: Red implies SN (partial — Unit and product cases)
--
-- The arrow case requires constructing a "reducible variable" at type B
-- so that the reducibility hypothesis can be instantiated. That needs
-- either reducibility of neutrals (the red-expand theorem below) or
-- explicit construction; both are subsequent work.
------------------------------------------------------------------------

-- With SN baked into Red at arrow type, Red-SN is a direct projection.
Red-SN : ∀ {A} (B : Ty) (t : Term A B) → Red A B t → SN t
Red-SN Unit    t r                 = r
Red-SN (B × C) t (rfst , _)        = SN-under-fst t (Red-SN B (fst ∘ t) rfst)
Red-SN (B ⇒ C) t (snt , _)         = snt

------------------------------------------------------------------------
-- Red-⟶: reducibility is preserved under reduction
------------------------------------------------------------------------

Red-⟶ : ∀ {A} (B : Ty) {t u : Term A B} →
        Red A B t → t ⟶βη u → Red A B u
Red-⟶ Unit    (acc ih) r = ih r
Red-⟶ (B × C) (rfst , rsnd) r =
  Red-⟶ B rfst (βη-Closure.∘-congʳ r) ,
  Red-⟶ C rsnd (βη-Closure.∘-congʳ r)
Red-⟶ (B ⇒ C) (acc ih , fn) r =
  ih r ,
  (λ v rv → Red-⟶ C (fn v rv)
                    (βη-Closure.∘-congʳ (βη-Closure.⟨,⟩-congˡ r)))

Red-⟶* : ∀ {A} (B : Ty) {t u : Term A B} →
         Red A B t → t ⟶βη* u → Red A B u
Red-⟶* B red done       = red
Red-⟶* B red (r ∷ rs)   = Red-⟶* B (Red-⟶ B red r) rs

------------------------------------------------------------------------
-- Neutral: terms with no reduction at the root.
--
-- Only applications of base generators to neutrals themselves.
-- Compositions / pairs / currys where no β or η root-rule matches.
-- This corresponds to Tait's "neutral" (nf-ish) terms: the reducibility
-- candidate for them collapses to (all reducts reducible).
--
-- We encode Neutral inductively, listing the shapes that do NOT match
-- any CCT1 root rule.
------------------------------------------------------------------------

-- Neutral terms: no reduction rule fires at the root.
-- We list the shapes that are safe (no root redex possible).
data Neutral : ∀ {A B} → Term A B → Set where
  -- Atomic generators: they have no reductions at all.
  ne-fst      : ∀ {A B} → Neutral (fst {A} {B})
  ne-snd      : ∀ {A B} → Neutral (snd {A} {B})
  ne-apply    : ∀ {A B} → Neutral (apply {A} {B})
  ne-terminal : ∀ {A} → Neutral (terminal {A})
  -- Deliberately NOT ne-id, because fst ∘ id and similar WOULD fire
  -- id-right. `id` is handled via direct Red construction using
  -- β-expansion, not via the Neutral machinery.

  -- fst applied to a neutral non-pair: fst-pair doesn't fire because
  -- g isn't a pair; id-right doesn't fire because g isn't id (g is
  -- built from Neutral constructors, none of which produce id).
  ne-fst∘ : ∀ {A B C} {g : Term C (A × B)} →
            Neutral g → Neutral (fst ∘ g)
  ne-snd∘ : ∀ {A B C} {g : Term C (A × B)} →
            Neutral g → Neutral (snd ∘ g)
  -- apply applied to a neutral non-pair: curry-β doesn't fire (g
  -- isn't of form ⟨curry _, _⟩), id-right doesn't fire (g isn't id).
  ne-apply∘ : ∀ {A B C} {g : Term C ((A ⇒ B) × A)} →
              Neutral g → Neutral (apply ∘ g)
  -- apply applied to a pair whose first component is neutral: ensures
  -- curry-β can't fire (first isn't `curry _`) and the pair isn't id.
  -- Used by Red-expand at arrow type.
  ne-apply∘⟨,⟩ : ∀ {A B C} {t : Term C (A ⇒ B)} {u : Term C A} →
                 Neutral t → Neutral (apply ∘ ⟨ t , u ⟩)

------------------------------------------------------------------------
-- Atomic terms are SN: no rule fires at their root and they have no
-- subterms to propagate a reduction through. So the Acc function is
-- empty.
------------------------------------------------------------------------

sn-id : ∀ {A} → SN (id {A})
sn-id = acc λ
  { (βη-Closure.base (β-rule (from-CCTB ())))
  ; (βη-Closure.base (β-rule (from-CCT1 ())))
  ; (βη-Closure.base (η-rule ()))
  ; (βη-Closure.base (s-rule ()))
  }

sn-fst : ∀ {A B} → SN (fst {A} {B})
sn-fst = acc λ
  { (βη-Closure.base (β-rule (from-CCTB ())))
  ; (βη-Closure.base (β-rule (from-CCT1 ())))
  ; (βη-Closure.base (η-rule ()))
  ; (βη-Closure.base (s-rule ()))
  }

sn-snd : ∀ {A B} → SN (snd {A} {B})
sn-snd = acc λ
  { (βη-Closure.base (β-rule (from-CCTB ())))
  ; (βη-Closure.base (β-rule (from-CCT1 ())))
  ; (βη-Closure.base (η-rule ()))
  ; (βη-Closure.base (s-rule ()))
  }

sn-apply : ∀ {A B} → SN (apply {A} {B})
sn-apply = acc λ
  { (βη-Closure.base (β-rule (from-CCTB ())))
  ; (βη-Closure.base (β-rule (from-CCT1 ())))
  ; (βη-Closure.base (η-rule ()))
  ; (βη-Closure.base (s-rule ()))
  }

sn-terminal : ∀ {A} → SN (terminal {A})
sn-terminal = acc λ
  { (βη-Closure.base (β-rule (from-CCTB ())))
  ; (βη-Closure.base (β-rule (from-CCT1 ())))
  ; (βη-Closure.base (η-rule ()))
  ; (βη-Closure.base (s-rule ()))
  }

------------------------------------------------------------------------
-- Red-expand (CR3): if t is neutral and every single-step reduct of t
-- is reducible, then t itself is reducible.
--
-- The proof is by induction on the target type B:
--   * Unit        — SN because every reduct is SN.
--   * B × C       — fst ∘ t and snd ∘ t's reducts cover t's reducts;
--                   use IH to show Red on projections.
--   * B ⇒ C       — applied to any reducible u, apply ∘ ⟨t, u⟩'s reducts
--                   all come from reductions in t or u; handle by IH
--                   and closure under reduction.
------------------------------------------------------------------------

-- Red-expand at Unit: direct. Red A Unit t = SN t, and every reduct
-- is Red (= SN at Unit). So acc of hyp is the SN witness.
Red-expand-Unit : ∀ {A} (t : Term A Unit) →
                  Neutral t →
                  (∀ {u} → t ⟶βη u → Red A Unit u) →
                  Red A Unit t
Red-expand-Unit t ne hyp = acc hyp

------------------------------------------------------------------------
-- No-root-redex lemmas for fst/snd/apply composed with a Neutral term.
-- These are the key invariants that let Red-expand recurse via fst/snd
-- projections.
------------------------------------------------------------------------

-- Helper: fst ∘ t has no root redex for any Neutral t.
-- Drilled through to leaf rule constructors; each is absurd by
-- unification (the rule's LHS pattern doesn't match `fst ∘ t`).
no-fst∘-root-redex : ∀ {A B C} {t : Term C (A × B)} → Neutral t →
                     ∀ {u} → ¬ ((fst ∘ t) ⟶βη-rules u)
-- ne-fst (t = fst)
no-fst∘-root-redex ne-fst (β-rule (from-CCTB ()))
no-fst∘-root-redex ne-fst (β-rule (from-CCT1 ()))
no-fst∘-root-redex ne-fst (η-rule ())
no-fst∘-root-redex ne-fst (s-rule ())
-- ne-snd (t = snd)
no-fst∘-root-redex ne-snd (β-rule (from-CCTB ()))
no-fst∘-root-redex ne-snd (β-rule (from-CCT1 ()))
no-fst∘-root-redex ne-snd (η-rule ())
no-fst∘-root-redex ne-snd (s-rule ())
-- ne-apply (t = apply)
no-fst∘-root-redex ne-apply (β-rule (from-CCTB ()))
no-fst∘-root-redex ne-apply (β-rule (from-CCT1 ()))
no-fst∘-root-redex ne-apply (η-rule ())
no-fst∘-root-redex ne-apply (s-rule ())
-- ne-terminal: t = terminal has target Unit, can't be A × B. Absent.
-- ne-fst∘ (t = fst ∘ ...)
no-fst∘-root-redex (ne-fst∘ _) (β-rule (from-CCTB ()))
no-fst∘-root-redex (ne-fst∘ _) (β-rule (from-CCT1 ()))
no-fst∘-root-redex (ne-fst∘ _) (η-rule ())
no-fst∘-root-redex (ne-fst∘ _) (s-rule ())
-- ne-snd∘ (t = snd ∘ ...)
no-fst∘-root-redex (ne-snd∘ _) (β-rule (from-CCTB ()))
no-fst∘-root-redex (ne-snd∘ _) (β-rule (from-CCT1 ()))
no-fst∘-root-redex (ne-snd∘ _) (η-rule ())
no-fst∘-root-redex (ne-snd∘ _) (s-rule ())
-- ne-apply∘ (t = apply ∘ ...)
no-fst∘-root-redex (ne-apply∘ _) (β-rule (from-CCTB ()))
no-fst∘-root-redex (ne-apply∘ _) (β-rule (from-CCT1 ()))
no-fst∘-root-redex (ne-apply∘ _) (η-rule ())
no-fst∘-root-redex (ne-apply∘ _) (s-rule ())
-- ne-apply∘⟨,⟩ (t = apply ∘ ⟨_,_⟩)
no-fst∘-root-redex (ne-apply∘⟨,⟩ _) (β-rule (from-CCTB ()))
no-fst∘-root-redex (ne-apply∘⟨,⟩ _) (β-rule (from-CCT1 ()))
no-fst∘-root-redex (ne-apply∘⟨,⟩ _) (η-rule ())
no-fst∘-root-redex (ne-apply∘⟨,⟩ _) (s-rule ())

no-snd∘-root-redex : ∀ {A B C} {t : Term C (A × B)} → Neutral t →
                     ∀ {u} → ¬ ((snd ∘ t) ⟶βη-rules u)
no-snd∘-root-redex ne-fst (β-rule (from-CCTB ()))
no-snd∘-root-redex ne-fst (β-rule (from-CCT1 ()))
no-snd∘-root-redex ne-fst (η-rule ())
no-snd∘-root-redex ne-fst (s-rule ())
no-snd∘-root-redex ne-snd (β-rule (from-CCTB ()))
no-snd∘-root-redex ne-snd (β-rule (from-CCT1 ()))
no-snd∘-root-redex ne-snd (η-rule ())
no-snd∘-root-redex ne-snd (s-rule ())
no-snd∘-root-redex ne-apply (β-rule (from-CCTB ()))
no-snd∘-root-redex ne-apply (β-rule (from-CCT1 ()))
no-snd∘-root-redex ne-apply (η-rule ())
no-snd∘-root-redex ne-apply (s-rule ())
no-snd∘-root-redex (ne-fst∘ _) (β-rule (from-CCTB ()))
no-snd∘-root-redex (ne-fst∘ _) (β-rule (from-CCT1 ()))
no-snd∘-root-redex (ne-fst∘ _) (η-rule ())
no-snd∘-root-redex (ne-fst∘ _) (s-rule ())
no-snd∘-root-redex (ne-snd∘ _) (β-rule (from-CCTB ()))
no-snd∘-root-redex (ne-snd∘ _) (β-rule (from-CCT1 ()))
no-snd∘-root-redex (ne-snd∘ _) (η-rule ())
no-snd∘-root-redex (ne-snd∘ _) (s-rule ())
no-snd∘-root-redex (ne-apply∘ _) (β-rule (from-CCTB ()))
no-snd∘-root-redex (ne-apply∘ _) (β-rule (from-CCT1 ()))
no-snd∘-root-redex (ne-apply∘ _) (η-rule ())
no-snd∘-root-redex (ne-apply∘ _) (s-rule ())
no-snd∘-root-redex (ne-apply∘⟨,⟩ _) (β-rule (from-CCTB ()))
no-snd∘-root-redex (ne-apply∘⟨,⟩ _) (β-rule (from-CCT1 ()))
no-snd∘-root-redex (ne-apply∘⟨,⟩ _) (η-rule ())
no-snd∘-root-redex (ne-apply∘⟨,⟩ _) (s-rule ())

no-apply∘-root-redex : ∀ {A B C} {t : Term C ((A ⇒ B) × A)} → Neutral t →
                       ∀ {u} → ¬ ((apply ∘ t) ⟶βη-rules u)
no-apply∘-root-redex ne-fst (β-rule (from-CCTB ()))
no-apply∘-root-redex ne-fst (β-rule (from-CCT1 ()))
no-apply∘-root-redex ne-fst (η-rule ())
no-apply∘-root-redex ne-fst (s-rule ())
no-apply∘-root-redex ne-snd (β-rule (from-CCTB ()))
no-apply∘-root-redex ne-snd (β-rule (from-CCT1 ()))
no-apply∘-root-redex ne-snd (η-rule ())
no-apply∘-root-redex ne-snd (s-rule ())
no-apply∘-root-redex ne-apply (β-rule (from-CCTB ()))
no-apply∘-root-redex ne-apply (β-rule (from-CCT1 ()))
no-apply∘-root-redex ne-apply (η-rule ())
no-apply∘-root-redex ne-apply (s-rule ())
no-apply∘-root-redex (ne-fst∘ _) (β-rule (from-CCTB ()))
no-apply∘-root-redex (ne-fst∘ _) (β-rule (from-CCT1 ()))
no-apply∘-root-redex (ne-fst∘ _) (η-rule ())
no-apply∘-root-redex (ne-fst∘ _) (s-rule ())
no-apply∘-root-redex (ne-snd∘ _) (β-rule (from-CCTB ()))
no-apply∘-root-redex (ne-snd∘ _) (β-rule (from-CCT1 ()))
no-apply∘-root-redex (ne-snd∘ _) (η-rule ())
no-apply∘-root-redex (ne-snd∘ _) (s-rule ())
no-apply∘-root-redex (ne-apply∘ _) (β-rule (from-CCTB ()))
no-apply∘-root-redex (ne-apply∘ _) (β-rule (from-CCT1 ()))
no-apply∘-root-redex (ne-apply∘ _) (η-rule ())
no-apply∘-root-redex (ne-apply∘ _) (s-rule ())
no-apply∘-root-redex (ne-apply∘⟨,⟩ _) (β-rule (from-CCTB ()))
no-apply∘-root-redex (ne-apply∘⟨,⟩ _) (β-rule (from-CCT1 ()))
no-apply∘-root-redex (ne-apply∘⟨,⟩ _) (η-rule ())
no-apply∘-root-redex (ne-apply∘⟨,⟩ _) (s-rule ())

------------------------------------------------------------------------
-- Atomic terms have no reductions. Used as "absurd" patterns when
-- pattern-matching through ∘-congˡ on an atomic left side.
------------------------------------------------------------------------

no-fst-reduct : ∀ {A B} {u : Term (A × B) A} → ¬ (fst ⟶βη u)
no-fst-reduct (βη-Closure.base (β-rule (from-CCTB ())))
no-fst-reduct (βη-Closure.base (β-rule (from-CCT1 ())))
no-fst-reduct (βη-Closure.base (η-rule ()))
no-fst-reduct (βη-Closure.base (s-rule ()))

no-snd-reduct : ∀ {A B} {u : Term (A × B) B} → ¬ (snd ⟶βη u)
no-snd-reduct (βη-Closure.base (β-rule (from-CCTB ())))
no-snd-reduct (βη-Closure.base (β-rule (from-CCT1 ())))
no-snd-reduct (βη-Closure.base (η-rule ()))
no-snd-reduct (βη-Closure.base (s-rule ()))

no-apply-reduct : ∀ {A B} {u : Term ((A ⇒ B) × A) B} → ¬ (apply ⟶βη u)
no-apply-reduct (βη-Closure.base (β-rule (from-CCTB ())))
no-apply-reduct (βη-Closure.base (β-rule (from-CCT1 ())))
no-apply-reduct (βη-Closure.base (η-rule ()))
no-apply-reduct (βη-Closure.base (s-rule ()))

no-id-reduct : ∀ {A} {u : Term A A} → ¬ (id ⟶βη u)
no-id-reduct (βη-Closure.base (β-rule (from-CCTB ())))
no-id-reduct (βη-Closure.base (β-rule (from-CCT1 ())))
no-id-reduct (βη-Closure.base (η-rule ()))
no-id-reduct (βη-Closure.base (s-rule ()))

------------------------------------------------------------------------
-- SN (apply ∘ id) — the SN component of Red-fst-at-arrow's eta-pair sub-case.
--
-- apply ∘ id has exactly ONE reduct: apply (via id-right). All other
-- candidate root rules require shapes incompatible with apply or id:
--   - id-left (requires apply = id)         — impossible
--   - id-right (gives apply)                — fires; reduct apply is SN
--   - fst-pair / snd-pair / eta-pair        — require specific shapes
--   - curry-β (requires apply = curry _)    — impossible
--   - curry-η / curry-apply / curry-compose — curry root, mismatch
--   - assoc (requires apply = composition)  — impossible
--   - pair-dist (requires apply = pair)     — impossible
--   - term-unique (requires apply = terminal) — impossible
-- Congruences on apply or id give no reducts (both atomic).
------------------------------------------------------------------------

sn-apply∘id : ∀ {A B} → SN (apply {A = A} {B = B} ∘ id)
sn-apply∘id = acc go
  where
    go : ∀ {v} → (apply ∘ id) ⟶βη v → SN v
    go (βη-Closure.base (β-rule (from-CCTB id-right))) = sn-apply
    go (βη-Closure.base (β-rule (from-CCT1 ())))
    go (βη-Closure.base (η-rule ()))
    go (βη-Closure.base (s-rule ()))
    go (βη-Closure.∘-congˡ r) = ⊥-elim (no-apply-reduct r)
    go (βη-Closure.∘-congʳ r) = ⊥-elim (no-id-reduct r)

------------------------------------------------------------------------
-- Red-expand-Arrow helpers: rule out root reductions of (apply ∘ ⟨t, u⟩)
-- and pair-root reductions of ⟨t, u⟩ for non-fst-shaped Neutral t.
------------------------------------------------------------------------

no-curry-neutral : ∀ {A B C} {f : Term (A × B) C} → ¬ Neutral (curry f)
no-curry-neutral ()

-- Root reductions of (apply ∘ ⟨t, u⟩) when t is Neutral. The only
-- candidate β-rule is curry-β (LHS = apply ∘ ⟨curry _, _⟩), ruled out
-- because Neutral t excludes t = curry _. id-right would require
-- ⟨t, u⟩ ≡ id, impossible. All other rules have non-matching root.
no-apply∘⟨,⟩-root-redex :
  ∀ {A B C} {t : Term A (B ⇒ C)} {u : Term A B} →
  Neutral t →
  ∀ {v} → ¬ ((apply ∘ ⟨ t , u ⟩) ⟶βη-rules v)
no-apply∘⟨,⟩-root-redex ne (β-rule (from-CCTB ()))
no-apply∘⟨,⟩-root-redex ne (β-rule (from-CCT1 curry-β)) = no-curry-neutral ne
no-apply∘⟨,⟩-root-redex ne (η-rule ())
no-apply∘⟨,⟩-root-redex ne (s-rule ())

-- Pair-root reductions of ⟨t, u⟩ when t is shape-X (not fst-shaped).
-- Only eta-pair (β-rule, LHS ⟨fst, snd⟩) and eta-pair-gen (s-rule,
-- LHS ⟨fst ∘ h, snd ∘ h⟩) have ⟨,⟩ root. Both require t to be either
-- fst literally or fst ∘ h. For non-fst-shaped t, both are absurd.

no-pair-root-snd : ∀ {A B D} {u : Term (A × B) D} →
                   ∀ {v} → ¬ (⟨ snd {A} {B} , u ⟩ ⟶βη-rules v)
no-pair-root-snd (β-rule (from-CCTB ()))
no-pair-root-snd (β-rule (from-CCT1 ()))
no-pair-root-snd (η-rule ())
no-pair-root-snd (s-rule ())

no-pair-root-apply : ∀ {A B D} {u : Term ((A ⇒ B) × A) D} →
                     ∀ {v} → ¬ (⟨ apply {A} {B} , u ⟩ ⟶βη-rules v)
no-pair-root-apply (β-rule (from-CCTB ()))
no-pair-root-apply (β-rule (from-CCT1 ()))
no-pair-root-apply (η-rule ())
no-pair-root-apply (s-rule ())

no-pair-root-snd∘ : ∀ {A B C D} {g : Term C (A × B)} {u : Term C D} →
                    ∀ {v} → ¬ (⟨ snd ∘ g , u ⟩ ⟶βη-rules v)
no-pair-root-snd∘ (β-rule (from-CCTB ()))
no-pair-root-snd∘ (β-rule (from-CCT1 ()))
no-pair-root-snd∘ (η-rule ())
no-pair-root-snd∘ (s-rule ())

no-pair-root-apply∘ : ∀ {A B C D} {g : Term C ((A ⇒ B) × A)} {u : Term C D} →
                      ∀ {v} → ¬ (⟨ apply ∘ g , u ⟩ ⟶βη-rules v)
no-pair-root-apply∘ (β-rule (from-CCTB ()))
no-pair-root-apply∘ (β-rule (from-CCT1 ()))
no-pair-root-apply∘ (η-rule ())
no-pair-root-apply∘ (s-rule ())

no-pair-root-apply∘⟨,⟩ :
  ∀ {A B C D} {t' : Term C (A ⇒ B)} {u' : Term C A} {u : Term C D} →
  ∀ {v} → ¬ (⟨ apply ∘ ⟨ t' , u' ⟩ , u ⟩ ⟶βη-rules v)
no-pair-root-apply∘⟨,⟩ (β-rule (from-CCTB ()))
no-pair-root-apply∘⟨,⟩ (β-rule (from-CCT1 ()))
no-pair-root-apply∘⟨,⟩ (η-rule ())
no-pair-root-apply∘⟨,⟩ (s-rule ())

------------------------------------------------------------------------
-- Red-fst-at-arrow — Red of fst at arrow target.
--
-- When the eta-pair reduction ⟨fst, snd⟩ ⟶β id fires inside the
-- Red-expand-Arrow ne-fst case, we reach a sub-goal Red _ C (apply ∘ id).
-- apply ∘ id is not Neutral (id-right fires at root), so Red-expand
-- cannot be used directly.
--
-- We DISPATCH on the arrow's result type C:
--   * C = Unit:    fully proved (Red _ Unit = SN, sn-apply∘id covers it)
--   * C = X × Y:   postulate (would need red-id-right at sub-types)
--   * C = X ⇒ Y:   postulate (would need red-id-right at Y)
--
-- The remaining narrow postulates are precisely scoped: each represents
-- the Red of fst at a SPECIFIC arrow result-type shape, with a documented
-- discharge plan via the red-id-right family of lemmas.
------------------------------------------------------------------------

-- C = Unit: discharged.
Red-fst-at-arrow-Unit :
  ∀ {B B'} → Red ((B ⇒ Unit) × B') (B ⇒ Unit) (fst {A = B ⇒ Unit} {B = B'})
Red-fst-at-arrow-Unit {B} {B'} = sn-fst , go
  where
    go : ∀ (u : Term ((B ⇒ Unit) × B') B) →
         Red ((B ⇒ Unit) × B') B u →
         Red ((B ⇒ Unit) × B') Unit (apply ∘ ⟨ fst , u ⟩)
    go u ru = aux u ru (Red-SN B u ru)
      where
        aux : ∀ (u : Term ((B ⇒ Unit) × B') B) →
              Red ((B ⇒ Unit) × B') B u → SN u →
              SN (apply ∘ ⟨ fst , u ⟩)
        aux u ru (acc ihu) = acc handle
          where
            handle : ∀ {v} → (apply ∘ ⟨ fst , u ⟩) ⟶βη v → SN v
            handle-pair : ∀ {p'} → ⟨ fst , u ⟩ ⟶βη p' → SN (apply ∘ p')

            handle (βη-Closure.base r) = ⊥-elim (no-apply∘⟨,⟩-root-redex ne-fst r)
            handle (βη-Closure.∘-congˡ r) = ⊥-elim (no-apply-reduct r)
            handle (βη-Closure.∘-congʳ r-pair) = handle-pair r-pair

            handle-pair (βη-Closure.base (β-rule (from-CCTB eta-pair))) = sn-apply∘id
            handle-pair (βη-Closure.base (β-rule (from-CCT1 ())))
            handle-pair (βη-Closure.base (η-rule ()))
            handle-pair (βη-Closure.⟨,⟩-congˡ r-fst) = ⊥-elim (no-fst-reduct r-fst)
            handle-pair (βη-Closure.⟨,⟩-congʳ r-u) = aux _ (Red-⟶ B ru r-u) (ihu r-u)

-- C = X × Y and C = X ⇒ Y cases remain narrow postulates.
postulate
  Red-fst-at-arrow-Prod : ∀ {B X Y B'} →
                          Red ((B ⇒ (X × Y)) × B') (B ⇒ (X × Y))
                              (fst {A = B ⇒ (X × Y)} {B = B'})
  Red-fst-at-arrow-Arrow : ∀ {B X Y B'} →
                           Red ((B ⇒ (X ⇒ Y)) × B') (B ⇒ (X ⇒ Y))
                               (fst {A = B ⇒ (X ⇒ Y)} {B = B'})

Red-fst-at-arrow : ∀ {B C B'} →
                   Red ((B ⇒ C) × B') (B ⇒ C) (fst {A = B ⇒ C} {B = B'})
Red-fst-at-arrow {C = Unit}    = Red-fst-at-arrow-Unit
Red-fst-at-arrow {C = _ × _}   = Red-fst-at-arrow-Prod
Red-fst-at-arrow {C = _ ⇒ _}   = Red-fst-at-arrow-Arrow

------------------------------------------------------------------------
-- Forward declarations for the mutually-recursive Red-expand family.
------------------------------------------------------------------------

Red-expand : ∀ {A} (B : Ty) (t : Term A B) →
             Neutral t →
             (∀ {u} → t ⟶βη u → Red A B u) →
             Red A B t

Red-expand-Arrow : ∀ {A} (B C : Ty) (t : Term A (B ⇒ C)) →
                   Neutral t →
                   (∀ {u} → t ⟶βη u → Red A (B ⇒ C) u) →
                   Red A (B ⇒ C) t

Red-expand-Prod : ∀ {A} (B C : Ty) (t : Term A (B × C)) →
                  Neutral t →
                  (∀ {u} → t ⟶βη u → Red A (B × C) u) →
                  Red A (B × C) t

Red-expand Unit     t ne hyp = Red-expand-Unit  t ne hyp
Red-expand (B × C)  t ne hyp = Red-expand-Prod  B C t ne hyp
Red-expand (B ⇒ C)  t ne hyp = Red-expand-Arrow B C t ne hyp

------------------------------------------------------------------------
-- Red-expand-Arrow: discharged by case-splitting on Neutral t.
--
-- For ne-fst: defer to the narrow postulate Red-fst-at-arrow.
-- For ne-fst∘: handle the eta-pair-gen reduction via re-pairing —
--   we have hyp on t = fst ∘ h and Red on u = snd ∘ h; for each
--   reduct h ⟶ h', construct Red of (apply ∘ ⟨fst ∘ h', snd ∘ h'⟩)
--   from Red of fst ∘ h' (via hyp) and Red of snd ∘ h' (via Red-⟶
--   on u), then forward-step via eta-pair-gen + ∘-congʳ to get
--   Red of (apply ∘ h').
-- For all other Neutral shapes (ne-snd, ne-apply, ne-snd∘,
--   ne-apply∘, ne-apply∘⟨,⟩): the standard Tait pattern. Neither
--   eta-pair (requires t = fst) nor eta-pair-gen (requires t = fst ∘ h)
--   fires, so the pair-root reduction is vacuously absent.
-- ne-terminal is ruled out by typing (target Unit, not arrow).
------------------------------------------------------------------------

-- ne-fst: defer to narrow postulate.
Red-expand-Arrow B C ._ ne-fst _ = Red-fst-at-arrow

-- ne-snd, ne-apply, ne-snd∘, ne-apply∘, ne-apply∘⟨,⟩: standard.
-- Each share the same proof structure; we inline per case so Agda can
-- discharge the pair-root absurdity using the per-shape no-pair-root
-- lemmas above.

Red-expand-Arrow {A} B C ._ ne-snd hyp = sn-t , go
  where
    sn-t : SN snd
    sn-t = acc λ {t'} r → Red-SN (B ⇒ C) t' (hyp r)

    go : ∀ (u : Term A B) → Red A B u → Red A C (apply ∘ ⟨ snd , u ⟩)
    go u ru = aux u ru (Red-SN B u ru)
      where
        aux : ∀ (u : Term A B) → Red A B u → SN u → Red A C (apply ∘ ⟨ snd , u ⟩)
        aux u ru (acc ihu) =
          Red-expand C (apply ∘ ⟨ snd , u ⟩) (ne-apply∘⟨,⟩ ne-snd) handle
          where
            handle : ∀ {v} → (apply ∘ ⟨ snd , u ⟩) ⟶βη v → Red A C v
            handle-pair : ∀ {p'} → ⟨ snd , u ⟩ ⟶βη p' → Red A C (apply ∘ p')

            handle (βη-Closure.base r) = ⊥-elim (no-apply∘⟨,⟩-root-redex ne-snd r)
            handle (βη-Closure.∘-congˡ r) = ⊥-elim (no-apply-reduct r)
            handle (βη-Closure.∘-congʳ r-pair) = handle-pair r-pair

            handle-pair (βη-Closure.base r) = ⊥-elim (no-pair-root-snd r)
            handle-pair (βη-Closure.⟨,⟩-congˡ r-t) = proj₂ (hyp r-t) u ru
            handle-pair (βη-Closure.⟨,⟩-congʳ r-u) = aux _ (Red-⟶ B ru r-u) (ihu r-u)

Red-expand-Arrow {A} B C ._ ne-apply hyp = sn-t , go
  where
    sn-t : SN apply
    sn-t = acc λ {t'} r → Red-SN (B ⇒ C) t' (hyp r)

    go : ∀ (u : Term A B) → Red A B u → Red A C (apply ∘ ⟨ apply , u ⟩)
    go u ru = aux u ru (Red-SN B u ru)
      where
        aux : ∀ (u : Term A B) → Red A B u → SN u → Red A C (apply ∘ ⟨ apply , u ⟩)
        aux u ru (acc ihu) =
          Red-expand C (apply ∘ ⟨ apply , u ⟩) (ne-apply∘⟨,⟩ ne-apply) handle
          where
            handle : ∀ {v} → (apply ∘ ⟨ apply , u ⟩) ⟶βη v → Red A C v
            handle-pair : ∀ {p'} → ⟨ apply , u ⟩ ⟶βη p' → Red A C (apply ∘ p')

            handle (βη-Closure.base r) = ⊥-elim (no-apply∘⟨,⟩-root-redex ne-apply r)
            handle (βη-Closure.∘-congˡ r) = ⊥-elim (no-apply-reduct r)
            handle (βη-Closure.∘-congʳ r-pair) = handle-pair r-pair

            handle-pair (βη-Closure.base r) = ⊥-elim (no-pair-root-apply r)
            handle-pair (βη-Closure.⟨,⟩-congˡ r-t) = proj₂ (hyp r-t) u ru
            handle-pair (βη-Closure.⟨,⟩-congʳ r-u) = aux _ (Red-⟶ B ru r-u) (ihu r-u)

Red-expand-Arrow {A} B C ._ (ne-snd∘ {g = g} ne-g) hyp = sn-t , go
  where
    sn-t : SN (snd ∘ g)
    sn-t = acc λ {t'} r → Red-SN (B ⇒ C) t' (hyp r)

    go : ∀ (u : Term A B) → Red A B u → Red A C (apply ∘ ⟨ snd ∘ g , u ⟩)
    go u ru = aux u ru (Red-SN B u ru)
      where
        aux : ∀ (u : Term A B) → Red A B u → SN u → Red A C (apply ∘ ⟨ snd ∘ g , u ⟩)
        aux u ru (acc ihu) =
          Red-expand C (apply ∘ ⟨ snd ∘ g , u ⟩) (ne-apply∘⟨,⟩ (ne-snd∘ ne-g)) handle
          where
            handle : ∀ {v} → (apply ∘ ⟨ snd ∘ g , u ⟩) ⟶βη v → Red A C v
            handle-pair : ∀ {p'} → ⟨ snd ∘ g , u ⟩ ⟶βη p' → Red A C (apply ∘ p')

            handle (βη-Closure.base r) = ⊥-elim (no-apply∘⟨,⟩-root-redex (ne-snd∘ ne-g) r)
            handle (βη-Closure.∘-congˡ r) = ⊥-elim (no-apply-reduct r)
            handle (βη-Closure.∘-congʳ r-pair) = handle-pair r-pair

            handle-pair (βη-Closure.base r) = ⊥-elim (no-pair-root-snd∘ r)
            handle-pair (βη-Closure.⟨,⟩-congˡ r-t) = proj₂ (hyp r-t) u ru
            handle-pair (βη-Closure.⟨,⟩-congʳ r-u) = aux _ (Red-⟶ B ru r-u) (ihu r-u)

Red-expand-Arrow {A} B C ._ (ne-apply∘ {g = g} ne-g) hyp = sn-t , go
  where
    sn-t : SN (apply ∘ g)
    sn-t = acc λ {t'} r → Red-SN (B ⇒ C) t' (hyp r)

    go : ∀ (u : Term A B) → Red A B u → Red A C (apply ∘ ⟨ apply ∘ g , u ⟩)
    go u ru = aux u ru (Red-SN B u ru)
      where
        aux : ∀ (u : Term A B) → Red A B u → SN u → Red A C (apply ∘ ⟨ apply ∘ g , u ⟩)
        aux u ru (acc ihu) =
          Red-expand C (apply ∘ ⟨ apply ∘ g , u ⟩) (ne-apply∘⟨,⟩ (ne-apply∘ ne-g)) handle
          where
            handle : ∀ {v} → (apply ∘ ⟨ apply ∘ g , u ⟩) ⟶βη v → Red A C v
            handle-pair : ∀ {p'} → ⟨ apply ∘ g , u ⟩ ⟶βη p' → Red A C (apply ∘ p')

            handle (βη-Closure.base r) = ⊥-elim (no-apply∘⟨,⟩-root-redex (ne-apply∘ ne-g) r)
            handle (βη-Closure.∘-congˡ r) = ⊥-elim (no-apply-reduct r)
            handle (βη-Closure.∘-congʳ r-pair) = handle-pair r-pair

            handle-pair (βη-Closure.base r) = ⊥-elim (no-pair-root-apply∘ r)
            handle-pair (βη-Closure.⟨,⟩-congˡ r-t) = proj₂ (hyp r-t) u ru
            handle-pair (βη-Closure.⟨,⟩-congʳ r-u) = aux _ (Red-⟶ B ru r-u) (ihu r-u)

Red-expand-Arrow {A} B C ._ (ne-apply∘⟨,⟩ {t = t'} {u = u'} ne-t') hyp = sn-t , go
  where
    sn-t : SN (apply ∘ ⟨ t' , u' ⟩)
    sn-t = acc λ {t''} r → Red-SN (B ⇒ C) t'' (hyp r)

    go : ∀ (u : Term A B) → Red A B u →
         Red A C (apply ∘ ⟨ apply ∘ ⟨ t' , u' ⟩ , u ⟩)
    go u ru = aux u ru (Red-SN B u ru)
      where
        aux : ∀ (u : Term A B) → Red A B u → SN u →
              Red A C (apply ∘ ⟨ apply ∘ ⟨ t' , u' ⟩ , u ⟩)
        aux u ru (acc ihu) =
          Red-expand C (apply ∘ ⟨ apply ∘ ⟨ t' , u' ⟩ , u ⟩)
            (ne-apply∘⟨,⟩ (ne-apply∘⟨,⟩ ne-t')) handle
          where
            handle : ∀ {v} → (apply ∘ ⟨ apply ∘ ⟨ t' , u' ⟩ , u ⟩) ⟶βη v → Red A C v
            handle-pair : ∀ {p'} →
                          ⟨ apply ∘ ⟨ t' , u' ⟩ , u ⟩ ⟶βη p' →
                          Red A C (apply ∘ p')

            handle (βη-Closure.base r) =
              ⊥-elim (no-apply∘⟨,⟩-root-redex (ne-apply∘⟨,⟩ ne-t') r)
            handle (βη-Closure.∘-congˡ r) = ⊥-elim (no-apply-reduct r)
            handle (βη-Closure.∘-congʳ r-pair) = handle-pair r-pair

            handle-pair (βη-Closure.base r) = ⊥-elim (no-pair-root-apply∘⟨,⟩ r)
            handle-pair (βη-Closure.⟨,⟩-congˡ r-t) = proj₂ (hyp r-t) u ru
            handle-pair (βη-Closure.⟨,⟩-congʳ r-u) = aux _ (Red-⟶ B ru r-u) (ihu r-u)

-- ne-fst∘ case: t = fst ∘ h. eta-pair-gen DOES fire when u = snd ∘ h.
-- Use the re-pairing trick documented above.
Red-expand-Arrow {A} B C ._ (ne-fst∘ {g = h} ne-h) hyp = sn-t , go
  where
    sn-t : SN (fst ∘ h)
    sn-t = acc λ {t'} r → Red-SN (B ⇒ C) t' (hyp r)

    go : ∀ (u : Term A B) → Red A B u → Red A C (apply ∘ ⟨ fst ∘ h , u ⟩)
    go u ru = aux u ru (Red-SN B u ru)
      where
        aux : ∀ (u : Term A B) → Red A B u → SN u → Red A C (apply ∘ ⟨ fst ∘ h , u ⟩)
        aux u ru (acc ihu) =
          Red-expand C (apply ∘ ⟨ fst ∘ h , u ⟩) (ne-apply∘⟨,⟩ (ne-fst∘ ne-h)) handle
          where
            handle : ∀ {v} → (apply ∘ ⟨ fst ∘ h , u ⟩) ⟶βη v → Red A C v
            handle-pair : ∀ {p'} → ⟨ fst ∘ h , u ⟩ ⟶βη p' → Red A C (apply ∘ p')

            handle (βη-Closure.base r) = ⊥-elim (no-apply∘⟨,⟩-root-redex (ne-fst∘ ne-h) r)
            handle (βη-Closure.∘-congˡ r) = ⊥-elim (no-apply-reduct r)
            handle (βη-Closure.∘-congʳ r-pair) = handle-pair r-pair
            -- eta-pair would require fst ∘ h ≡ fst, impossible (different head).
            -- eta-pair-gen requires u ≡ snd ∘ h; when it fires, use re-pairing.
            handle-pair (βη-Closure.base (β-rule (from-CCTB ())))
            handle-pair (βη-Closure.base (β-rule (from-CCT1 ())))
            handle-pair (βη-Closure.base (η-rule ()))
            handle-pair (βη-Closure.base (s-rule eta-pair-gen)) = re-pairing
              where
                -- Reduct of eta-pair-gen on ⟨fst ∘ h, snd ∘ h⟩ is h.
                -- We need Red A C (apply ∘ h). Use Red-expand C with re-pairing.
                re-pairing : Red A C (apply ∘ h)
                re-pairing = Red-expand C (apply ∘ h) (ne-apply∘ ne-h) handle-h
                  where
                    handle-h : ∀ {v} → (apply ∘ h) ⟶βη v → Red A C v
                    handle-h (βη-Closure.base r) = ⊥-elim (no-apply∘-root-redex ne-h r)
                    handle-h (βη-Closure.∘-congˡ r) = ⊥-elim (no-apply-reduct r)
                    handle-h (βη-Closure.∘-congʳ r-h) =
                      -- Step apply ∘ ⟨fst ∘ h', snd ∘ h'⟩ ⟶s apply ∘ h' via
                      -- ∘-congʳ + eta-pair-gen, then Red-⟶ to get Red A C (apply ∘ h').
                      Red-⟶ C
                        (proj₂ (hyp (βη-Closure.∘-congʳ r-h))
                               _
                               (Red-⟶ B ru (βη-Closure.∘-congʳ r-h)))
                        (βη-Closure.∘-congʳ (βη-Closure.base (s-rule eta-pair-gen)))
            -- Other s-rules (assoc, pair-dist, term-unique) all have ∘-root LHS;
            -- their patterns don't unify with ⟨ fst ∘ h , u ⟩, so Agda's coverage
            -- check treats them as absurd without explicit clauses.
            handle-pair (βη-Closure.⟨,⟩-congˡ r-t) = proj₂ (hyp r-t) u ru
            handle-pair (βη-Closure.⟨,⟩-congʳ r-u) = aux _ (Red-⟶ B ru r-u) (ihu r-u)

Red-expand-Prod {A} B C t ne hyp =
  Red-expand B (fst ∘ t) (ne-fst∘ ne) fst-hyp ,
  Red-expand C (snd ∘ t) (ne-snd∘ ne) snd-hyp
  where
  fst-hyp : ∀ {u} → (fst ∘ t) ⟶βη u → Red A B u
  fst-hyp (βη-Closure.base r)    = ⊥-elim (no-fst∘-root-redex ne r)
  fst-hyp (βη-Closure.∘-congˡ r) = ⊥-elim (no-fst-reduct r)
  fst-hyp (βη-Closure.∘-congʳ r) = proj₁ (hyp r)

  snd-hyp : ∀ {u} → (snd ∘ t) ⟶βη u → Red A C u
  snd-hyp (βη-Closure.base r)    = ⊥-elim (no-snd∘-root-redex ne r)
  snd-hyp (βη-Closure.∘-congˡ r) = ⊥-elim (no-snd-reduct r)
  snd-hyp (βη-Closure.∘-congʳ r) = proj₂ (hyp r)

------------------------------------------------------------------------
-- red-all: every term is reducible.
--
-- Main case-bash. Each constructor (id, _∘_, fst, snd, ⟨_,_⟩, curry,
-- apply, terminal) must build a Red-term from Red-subterms. For the
-- β-redex shapes (apply ∘ ⟨curry f, g⟩, fst ∘ ⟨f, g⟩, …), the proof
-- invokes Red-⟶ to transport the reducibility witness across the β
-- step. For "structural" shapes that never fire a root redex, Red-expand
-- applies directly with the neutrality guarantee.
------------------------------------------------------------------------

-- Trivial Red cases at Unit target.
red-terminal : ∀ {A} → Red A Unit (terminal {A})
red-terminal = sn-terminal

red-id-unit : Red Unit Unit id
red-id-unit = sn-id

-- Red of atomic generators at Unit target type (when the type pinning
-- happens to make target = Unit). These instances are all just SN of
-- the atomic, lifted into Red's Unit-case.
red-fst-unit : ∀ {B} → Red (Unit × B) Unit fst
red-fst-unit = sn-fst

red-snd-unit : ∀ {A} → Red (A × Unit) Unit snd
red-snd-unit = sn-snd

red-apply-unit : ∀ {A} → Red ((A ⇒ Unit) × A) Unit apply
red-apply-unit = sn-apply

-- Generalisation: terminal ∘ f is SN whenever f is SN. Proof: any
-- reduct of terminal ∘ f is either terminal (via term-unique at root)
-- or terminal ∘ f' (via ∘-congʳ with f ⟶ f'), or an impossible case.
-- In the first we're done; in the second, IH on f's accessibility.
sn-terminal∘ : ∀ {A B} (f : Term A B) → SN f → SN (terminal ∘ f)
sn-terminal∘ f (acc ih) = acc go
  where
  go : ∀ {u} → (terminal ∘ f) ⟶βη u → SN u
  -- Root base-rules: only id-right (when f = id) and term-unique match.
  go (βη-Closure.base (β-rule (from-CCTB id-right))) = sn-terminal
  go (βη-Closure.base (s-rule term-unique))          = sn-terminal
  -- ∘-congˡ on terminal: terminal is atomic, no reducts.
  go (βη-Closure.∘-congˡ (βη-Closure.base (β-rule (from-CCTB ()))))
  go (βη-Closure.∘-congˡ (βη-Closure.base (β-rule (from-CCT1 ()))))
  go (βη-Closure.∘-congˡ (βη-Closure.base (η-rule ())))
  go (βη-Closure.∘-congˡ (βη-Closure.base (s-rule ())))
  -- ∘-congʳ on f: recurse via the IH of f's Acc.
  go (βη-Closure.∘-congʳ r) = sn-terminal∘ _ (ih r)

-- red-all at terminal-headed compositions — red-all is Red, which at
-- Unit target is SN. Combined with sn-terminal∘:
red-terminal∘ : ∀ {A B} (f : Term A B) → SN f → Red A Unit (terminal ∘ f)
red-terminal∘ f snf = sn-terminal∘ f snf

------------------------------------------------------------------------
-- red-all — every term is reducible.
--
-- Replaces the broad red-all postulate with a structured dispatch on
-- Term constructor. Each constructor delegates to a per-constructor
-- helper:
--   * Atomic constructors (id, fst, snd, apply): further dispatched
--     on the relevant type. Unit-target cases are fully discharged
--     (sn-id, sn-fst, sn-snd, sn-apply). The fst-at-arrow case uses
--     our earlier Red-fst-at-arrow lemma. Other type-shape cases
--     remain as narrow postulates.
--   * terminal: discharged trivially (sn-terminal).
--   * Constructive constructors (_∘_, ⟨_,_⟩, curry): postulated as
--     Red-closure lemmas (each takes Red of subterms and produces
--     Red of the constructed term). Discharging these requires the
--     full Tait substitution machinery.
--
-- The conversion narrows the audit surface from 1 broad obligation
-- into ~10 per-constructor / per-type-shape obligations. The
-- structurally-recursive call shape is maintained: red-all on a
-- composition / pair / curry calls red-all on its subterms.
------------------------------------------------------------------------

-- Atomic helpers — dispatch on the relevant type.

red-all-id : ∀ {A} → Red A A id
red-all-fst : ∀ {A B} → Red (A × B) A fst
red-all-snd : ∀ {A B} → Red (A × B) B snd
red-all-apply : ∀ {A B} → Red ((A ⇒ B) × A) B apply
red-all-terminal : ∀ {A} → Red A Unit terminal

-- Constructive helpers — postulated as Red-closure lemmas.
postulate
  red-all-id-Prod   : ∀ {X Y} → Red (X × Y) (X × Y) id
  red-all-id-Arrow  : ∀ {X Y} → Red (X ⇒ Y) (X ⇒ Y) id
  red-all-fst-Prod  : ∀ {X Y B} → Red ((X × Y) × B) (X × Y) fst
  red-all-snd-Prod  : ∀ {A X Y} → Red (A × (X × Y)) (X × Y) snd
  red-all-snd-Arrow : ∀ {A X Y} → Red (A × (X ⇒ Y)) (X ⇒ Y) snd
  red-all-apply-Prod  : ∀ {A X Y} → Red ((A ⇒ (X × Y)) × A) (X × Y) apply
  red-all-apply-Arrow : ∀ {A X Y} → Red ((A ⇒ (X ⇒ Y)) × A) (X ⇒ Y) apply
  red-all-comp  : ∀ {A B C} (f : Term B C) (g : Term A B) →
                  Red B C f → Red A B g → Red A C (f ∘ g)
  red-all-pair  : ∀ {C A B} (f : Term C A) (g : Term C B) →
                  Red C A f → Red C B g → Red C (A × B) ⟨ f , g ⟩
  red-all-curry : ∀ {A B C} (f : Term (A × B) C) →
                  Red (A × B) C f → Red A (B ⇒ C) (curry f)

-- Atomic helper definitions.
red-all-id {Unit}    = sn-id
red-all-id {_ × _}   = red-all-id-Prod
red-all-id {_ ⇒ _}   = red-all-id-Arrow

red-all-fst {A = Unit}    = sn-fst
red-all-fst {A = _ × _}   = red-all-fst-Prod
red-all-fst {A = _ ⇒ _}   = Red-fst-at-arrow

red-all-snd {B = Unit}    = sn-snd
red-all-snd {B = _ × _}   = red-all-snd-Prod
red-all-snd {B = _ ⇒ _}   = red-all-snd-Arrow

red-all-apply {B = Unit}    = sn-apply
red-all-apply {B = _ × _}   = red-all-apply-Prod
red-all-apply {B = _ ⇒ _}   = red-all-apply-Arrow

red-all-terminal = sn-terminal

-- Main red-all by structural recursion on Term.
red-all : ∀ {A B} (t : Term A B) → Red A B t
red-all id          = red-all-id
red-all terminal    = red-all-terminal
red-all fst         = red-all-fst
red-all snd         = red-all-snd
red-all apply       = red-all-apply
red-all (f ∘ g)     = red-all-comp f g (red-all f) (red-all g)
red-all ⟨ f , g ⟩   = red-all-pair f g (red-all f) (red-all g)
red-all (curry f)   = red-all-curry f (red-all f)

------------------------------------------------------------------------
-- Strong normalization for every CCT1 term — consequence of (1) + (4).
------------------------------------------------------------------------

sn : ∀ {A B} (t : Term A B) → SN t
sn {B = B} t = Red-SN B t (red-all t)

------------------------------------------------------------------------
-- Status summary:
--
--   Proved:     Red-⟶, Red-⟶*, SN-under-fst, SN-under-snd,
--               Red-SN at Unit and product types, Neutral (data),
--               Red-expand-Unit, Red-expand-Prod,
--               Red-expand-Arrow (by case-split on Neutral t,
--                 with the ne-fst sub-case deferred to the narrow
--                 postulate Red-fst-at-arrow),
--               sn (assuming red-all).
--
--   Postulated: Red-fst-at-arrow-Prod and Red-fst-at-arrow-Arrow
--                 (the t = fst arrow sub-cases of Red-expand-Arrow at
--                 result types X × Y and X ⇒ Y respectively — both
--                 need a red-id-right family of lemmas, structurally
--                 recursive on the result type; the C = Unit case is
--                 fully discharged via Red-fst-at-arrow-Unit, which
--                 reduces the eta-pair sub-goal to sn-apply∘id),
--               red-all-{id-Prod, id-Arrow, fst-Prod, snd-Prod,
--                        snd-Arrow, apply-Prod, apply-Arrow, comp,
--                        pair, curry} — the per-constructor Tait
--                        sub-obligations remaining after dispatching
--                        red-all on Term constructor. Atomic-at-Unit
--                        cases (id, fst, snd, apply at their respective
--                        Unit target shapes) and terminal are
--                        discharged. fst-at-Arrow uses Red-fst-at-arrow.
--
-- The Red-expand-Arrow discharge uses a re-pairing trick to handle
-- the eta-pair-gen sub-case (t = fst ∘ h, u = snd ∘ h): we have hyp
-- on t and Red on u, so for each reduct h ⟶ h' we construct
-- Red of (apply ∘ ⟨fst ∘ h', snd ∘ h'⟩) and forward-step via
-- eta-pair-gen + ∘-congʳ to get Red of (apply ∘ h').
------------------------------------------------------------------------
