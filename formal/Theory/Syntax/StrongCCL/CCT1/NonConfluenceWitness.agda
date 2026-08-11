------------------------------------------------------------------------
-- Theory.Syntax.StrongCCL.CCT1.NonConfluenceWitness
--
-- A MECHANISED counter-witness: the full βη rewrite system at CCT1
-- (Theory.Syntax.StrongCCL.CCT1._⟶βη_) is NOT confluent.
--
-- The witness term
--
--   t = curry (apply ∘ ⟨ fst ∘ fst , snd ⟩) ∘ snd
--
-- reduces to TWO DISTINCT βη-normal forms:
--
--   Path 1 (∘-congˡ + curry-η):     t ⟶βη* fst ∘ snd
--   Path 2 (curry-compose + assoc…): t ⟶βη* curry (apply ∘ ⟨ fst ∘ (snd ∘ fst) , snd ⟩)
--
-- Both endpoints are βη-normal forms (proved here), and they are
-- distinct head constructors (∘ vs curry), so they cannot be joined.
-- The root cause: `assoc` is one-directional, while `curry-η` demands the
-- rigid shape `f ∘ fst`; Path 2 lands on `fst ∘ (snd ∘ fst)`, which
-- cannot be re-associated back into `(fst ∘ snd) ∘ fst` to re-expose the
-- curry-η redex. This is the typed-combinator surfacing of the
-- Klop / Curien-Hardin phenomenon.
--
-- Consequence: the global `cct1-confluence` postulate chain is not just
-- unproven but UNSOUND on the full rule set. Confluence holds only on
-- restricted subsystems (the Curien1985 β-fragment), which is what the
-- bootstrap actually relies on.
--
------------------------------------------------------------------------

module Theory.Syntax.StrongCCL.CCT1.NonConfluenceWitness where

open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (Σ; _,_) renaming (_×_ to _∧_)

open import Theory.Syntax.StrongCCL.CCT1

open βη-Closure
  using (base; ∘-congˡ; ∘-congʳ; ⟨,⟩-congˡ; ⟨,⟩-congʳ; curry-cong)

------------------------------------------------------------------------
-- Concrete types making the witness well-typed.
------------------------------------------------------------------------

U : Ty
U = Unit

E1 : Ty
E1 = U ⇒ U

A : Ty
A = E1 × U

D : Ty
D = U × A

------------------------------------------------------------------------
-- The terms.
------------------------------------------------------------------------

-- The curried body of the source term.
inner : Term (A × U) U
inner = apply ∘ ⟨ fst ∘ fst , snd ⟩

-- Source term.
t : Term D E1
t = curry inner ∘ snd

-- Path-1 normal form.
nf₁ : Term D E1
nf₁ = fst ∘ snd

-- Path-2 normal-form sub-pieces (named so the NF proofs and the
-- reduction chain stay definitionally aligned).
sf : Term (D × U) A          -- snd ∘ fst
sf = snd ∘ fst

fsf : Term (D × U) E1        -- fst ∘ (snd ∘ fst)
fsf = fst ∘ sf

pr2 : Term (D × U) (E1 × U)  -- ⟨ fst ∘ (snd ∘ fst) , snd ⟩
pr2 = ⟨ fsf , snd ⟩

in2 : Term (D × U) U         -- apply ∘ ⟨ … ⟩
in2 = apply ∘ pr2

-- Path-2 normal form.
nf₂ : Term D E1
nf₂ = curry in2

------------------------------------------------------------------------
-- Normal-form lemmas.  Each case-splits the congruence closure; the
-- `base` cases are refuted by constructor clash, the congruence cases
-- recurse into the corresponding sub-NF lemma.
------------------------------------------------------------------------

nf-fst : ∀ {X Y} → IsβηNormalForm (fst {X} {Y})
nf-fst (base (β-rule (from-CCTB ())))
nf-fst (base (β-rule (from-CCT1 ())))
nf-fst (base (η-rule ()))
nf-fst (base (s-rule ()))

nf-snd : ∀ {X Y} → IsβηNormalForm (snd {X} {Y})
nf-snd (base (β-rule (from-CCTB ())))
nf-snd (base (β-rule (from-CCT1 ())))
nf-snd (base (η-rule ()))
nf-snd (base (s-rule ()))

nf-apply : ∀ {X Y} → IsβηNormalForm (apply {X} {Y})
nf-apply (base (β-rule (from-CCTB ())))
nf-apply (base (β-rule (from-CCT1 ())))
nf-apply (base (η-rule ()))
nf-apply (base (s-rule ()))

nf-sf : IsβηNormalForm sf
nf-sf (base (β-rule (from-CCTB ())))
nf-sf (base (β-rule (from-CCT1 ())))
nf-sf (base (η-rule ()))
nf-sf (base (s-rule ()))
nf-sf (∘-congˡ r) = nf-snd r
nf-sf (∘-congʳ r) = nf-fst r

nf-fsf : IsβηNormalForm fsf
nf-fsf (base (β-rule (from-CCTB ())))
nf-fsf (base (β-rule (from-CCT1 ())))
nf-fsf (base (η-rule ()))
nf-fsf (base (s-rule ()))
nf-fsf (∘-congˡ r) = nf-fst r
nf-fsf (∘-congʳ r) = nf-sf r

nf-pr2 : IsβηNormalForm pr2
nf-pr2 (base (β-rule (from-CCTB ())))
nf-pr2 (base (β-rule (from-CCT1 ())))
nf-pr2 (base (η-rule ()))
nf-pr2 (base (s-rule ()))
nf-pr2 (⟨,⟩-congˡ r) = nf-fsf r
nf-pr2 (⟨,⟩-congʳ r) = nf-snd r

nf-in2 : IsβηNormalForm in2
nf-in2 (base (β-rule (from-CCTB ())))
nf-in2 (base (β-rule (from-CCT1 ())))
nf-in2 (base (η-rule ()))
nf-in2 (base (s-rule ()))
nf-in2 (∘-congˡ r) = nf-apply r
nf-in2 (∘-congʳ r) = nf-pr2 r

-- The crux: curry-η does NOT fire on `curry in2`, because in2's first
-- pair component is `fst ∘ (snd ∘ fst)`, not the required `f ∘ fst`.
nf-nf₂ : IsβηNormalForm nf₂
nf-nf₂ (base (β-rule (from-CCTB ())))
nf-nf₂ (base (β-rule (from-CCT1 ())))
nf-nf₂ (base (η-rule ()))
nf-nf₂ (base (s-rule ()))
nf-nf₂ (curry-cong r) = nf-in2 r

nf-nf₁ : IsβηNormalForm nf₁
nf-nf₁ (base (β-rule (from-CCTB ())))
nf-nf₁ (base (β-rule (from-CCT1 ())))
nf-nf₁ (base (η-rule ()))
nf-nf₁ (base (s-rule ()))
nf-nf₁ (∘-congˡ r) = nf-fst r
nf-nf₁ (∘-congʳ r) = nf-snd r

------------------------------------------------------------------------
-- The two reduction paths.
------------------------------------------------------------------------

-- Path 1: a single curry-η step under the left of the composition.
path₁ : t ⟶βη* nf₁
path₁ = ∘-congˡ (base (η-rule curry-η)) ∷ done

-- Path 2: curry-compose, then renormalise the curried body.
path₂ : t ⟶βη* nf₂
path₂ =
    base (η-rule curry-compose)
  ∷ (curry-cong (base (s-rule assoc))
  ∷ (curry-cong (∘-congʳ (base (s-rule pair-dist)))
  ∷ (curry-cong (∘-congʳ (⟨,⟩-congˡ (base (s-rule assoc))))
  ∷ (curry-cong (∘-congʳ (⟨,⟩-congˡ (∘-congʳ (base (β-rule (from-CCTB fst-pair))))))
  ∷ (curry-cong (∘-congʳ (⟨,⟩-congʳ (base (β-rule (from-CCTB snd-pair)))))
  ∷ done)))))

------------------------------------------------------------------------
-- Non-confluence.
------------------------------------------------------------------------

-- A normal form reduces only to itself.
nf-stops : ∀ {X Y} {a b : Term X Y} → IsβηNormalForm a → a ⟶βη* b → a ≡ b
nf-stops _  done      = refl
nf-stops nf (s ∷ _)   = ⊥-elim (nf s)

-- The two normal forms are syntactically distinct (∘ vs curry head).
nf₁≢nf₂ : ¬ (nf₁ ≡ nf₂)
nf₁≢nf₂ ()

-- Hence they have no common reduct.
not-joinable : ¬ (Σ (Term D E1) (λ w → (nf₁ ⟶βη* w) ∧ (nf₂ ⟶βη* w)))
not-joinable (w , p , q) =
  nf₁≢nf₂ (trans (nf-stops nf-nf₁ p) (sym (nf-stops nf-nf₂ q)))

-- Confluence of _⟶βη*_, stated locally.
Confluent-⟶βη : Set
Confluent-⟶βη =
  ∀ {X Y} {a b c : Term X Y} →
  a ⟶βη* b → a ⟶βη* c →
  Σ (Term X Y) (λ d → (b ⟶βη* d) ∧ (c ⟶βη* d))

-- The main result: the full βη system is not confluent.
¬confluent : ¬ Confluent-⟶βη
¬confluent conf = not-joinable (conf path₁ path₂)
