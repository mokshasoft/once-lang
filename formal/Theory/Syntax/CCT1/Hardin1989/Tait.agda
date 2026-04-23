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
-- To prove in subsequent revisions:
--   (1) Red-SN     : Red t → SN t
--   (2) Red-⟶      : Red t → t ⟶βη u → Red u
--   (3) Red-expand : neutral t ∧ (∀ u. t ⟶βη u → Red u) → Red t
--   (4) red-all    : ∀ t. Red t
--
-- Then SN for every CCT1 term follows by (1) + (4).
------------------------------------------------------------------------

module Theory.Syntax.CCT1.Hardin1989.Tait where

open import Data.Product
  using (Σ; _,_; proj₁; proj₂) renaming (_×_ to _∧_)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_)

open import Theory.Syntax.CCT1.Hardin1989
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

-- Red-expand dispatcher: Unit and product cases proven; arrow case
-- needs machinery (lex induction on (SN t, SN u)) not yet in place,
-- so it remains postulated below.

postulate
  Red-expand-Arrow : ∀ {A} (B C : Ty) (t : Term A (B ⇒ C)) →
                     Neutral t →
                     (∀ {u} → t ⟶βη u → Red A (B ⇒ C) u) →
                     Red A (B ⇒ C) t

Red-expand : ∀ {A} (B : Ty) (t : Term A B) →
             Neutral t →
             (∀ {u} → t ⟶βη u → Red A B u) →
             Red A B t

Red-expand-Prod : ∀ {A} (B C : Ty) (t : Term A (B × C)) →
                  Neutral t →
                  (∀ {u} → t ⟶βη u → Red A (B × C) u) →
                  Red A (B × C) t

Red-expand Unit     t ne hyp = Red-expand-Unit  t ne hyp
Red-expand (B × C)  t ne hyp = Red-expand-Prod  B C t ne hyp
Red-expand (B ⇒ C)  t ne hyp = Red-expand-Arrow B C t ne hyp

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

-- Main case-bash: every term is reducible. To be proved by induction
-- on Term structure; for each constructor (id, _∘_, fst, snd, ⟨_,_⟩,
-- curry, apply, terminal), show Red at every target type. The hard
-- cases involve the β-redex shapes, where CR4 (β-expansion closure,
-- derivable from Red-expand + Red-⟶) is the key lemma.
postulate
  red-all : ∀ {A B} (t : Term A B) → Red A B t

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
--               sn (assuming red-all).
--
--   Postulated: Red-SN-arrow, Red-expand, red-all.
--
-- These three postulates correspond to the classical Tait proof
-- obligations. Discharging them is deferred to a subsequent session.
------------------------------------------------------------------------
