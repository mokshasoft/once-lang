------------------------------------------------------------------------
-- Theory.Syntax.StrongCCL.CCT1.DecidableEquality
--
-- Decidable propositional equality on Ty and Term at CCT1.
--
-- Reusable infrastructure. Primary consumer: the eta-pair-gen branch
-- of the complete development _* (Theory.Syntax.StrongCCL.CCT1.
-- Diamond), which fires when ⟨ fst ∘ h , snd ∘ h ⟩ has the SAME h
-- on both sides — a non-linear pattern that linear pattern matching
-- cannot decide without this lemma.
--
------------------------------------------------------------------------

module Theory.Syntax.StrongCCL.CCT1.DecidableEquality where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (Dec; yes; no; ¬_)

open import Theory.Syntax.StrongCCL.CCT1

------------------------------------------------------------------------
-- Decidable Ty equality.
------------------------------------------------------------------------

_≟Ty_ : (A B : Ty) → Dec (A ≡ B)

Unit ≟Ty Unit = yes refl
Unit ≟Ty (_ × _) = no λ ()
Unit ≟Ty (_ ⇒ _) = no λ ()

(_ × _) ≟Ty Unit = no λ ()
(A₁ × A₂) ≟Ty (B₁ × B₂) with A₁ ≟Ty B₁ | A₂ ≟Ty B₂
... | yes refl | yes refl = yes refl
... | no ¬eq   | _        = no λ { refl → ¬eq refl }
... | _        | no ¬eq   = no λ { refl → ¬eq refl }
(_ × _) ≟Ty (_ ⇒ _) = no λ ()

(_ ⇒ _) ≟Ty Unit = no λ ()
(_ ⇒ _) ≟Ty (_ × _) = no λ ()
(A₁ ⇒ A₂) ≟Ty (B₁ ⇒ B₂) with A₁ ≟Ty B₁ | A₂ ≟Ty B₂
... | yes refl | yes refl = yes refl
... | no ¬eq   | _        = no λ { refl → ¬eq refl }
... | _        | no ¬eq   = no λ { refl → ¬eq refl }

------------------------------------------------------------------------
-- Decidable Term equality (at the same Term A B type).
--
-- Diagonal cases (same constructor) recurse on subterms.
-- Off-diagonal cases (different constructors) are no — many are
-- absurd by type unification (Agda's coverage check sees them);
-- the remaining type-possible mismatches need an explicit `no λ ()`.
-- Compositions need Ty equality on the intermediate type.
------------------------------------------------------------------------

_≟_ : ∀ {A B} (t u : Term A B) → Dec (t ≡ u)

-- Diagonal cases.
id ≟ id = yes refl
terminal ≟ terminal = yes refl
fst ≟ fst = yes refl
snd ≟ snd = yes refl
apply ≟ apply = yes refl

(_∘_ {B = B₁} h₁ k₁) ≟ (_∘_ {B = B₂} h₂ k₂) with B₁ ≟Ty B₂
... | no ¬eq   = no λ { refl → ¬eq refl }
... | yes refl with h₁ ≟ h₂ | k₁ ≟ k₂
...   | yes refl | yes refl = yes refl
...   | no ¬eq   | _        = no λ { refl → ¬eq refl }
...   | _        | no ¬eq   = no λ { refl → ¬eq refl }

⟨ h₁ , k₁ ⟩ ≟ ⟨ h₂ , k₂ ⟩ with h₁ ≟ h₂ | k₁ ≟ k₂
... | yes refl | yes refl = yes refl
... | no ¬eq   | _        = no λ { refl → ¬eq refl }
... | _        | no ¬eq   = no λ { refl → ¬eq refl }

curry h₁ ≟ curry h₂ with h₁ ≟ h₂
... | yes refl = yes refl
... | no ¬eq   = no λ { refl → ¬eq refl }

-- Off-diagonals (different constructors at same Term A B type).
-- Each is `no λ ()` if type-possible; type-impossible pairs are
-- omitted (Agda's coverage check accepts via type unification).

id ≟ terminal     = no λ ()
id ≟ (_ ∘ _)      = no λ ()
id ≟ ⟨ _ , _ ⟩    = no λ ()
id ≟ curry _      = no λ ()

terminal ≟ id     = no λ ()
terminal ≟ fst    = no λ ()
terminal ≟ snd    = no λ ()
terminal ≟ apply  = no λ ()
terminal ≟ (_ ∘ _) = no λ ()

fst ≟ terminal    = no λ ()
fst ≟ snd         = no λ ()
-- fst ≟ apply: type-impossible (cycle B = X⇒Y where Y = B). Omitted.
fst ≟ (_ ∘ _)     = no λ ()
fst ≟ ⟨ _ , _ ⟩   = no λ ()
fst ≟ curry _     = no λ ()

snd ≟ terminal    = no λ ()
snd ≟ fst         = no λ ()
snd ≟ apply       = no λ ()
snd ≟ (_ ∘ _)     = no λ ()
snd ≟ ⟨ _ , _ ⟩   = no λ ()
snd ≟ curry _     = no λ ()

apply ≟ terminal  = no λ ()
-- apply ≟ fst: type-impossible (cycle, symmetric to fst ≟ apply).
apply ≟ snd       = no λ ()
apply ≟ (_ ∘ _)   = no λ ()
apply ≟ ⟨ _ , _ ⟩ = no λ ()
apply ≟ curry _   = no λ ()

(_ ∘ _) ≟ id      = no λ ()
(_ ∘ _) ≟ terminal = no λ ()
(_ ∘ _) ≟ fst     = no λ ()
(_ ∘ _) ≟ snd     = no λ ()
(_ ∘ _) ≟ apply   = no λ ()
(_ ∘ _) ≟ ⟨ _ , _ ⟩ = no λ ()
(_ ∘ _) ≟ curry _ = no λ ()

⟨ _ , _ ⟩ ≟ id    = no λ ()
⟨ _ , _ ⟩ ≟ fst   = no λ ()
⟨ _ , _ ⟩ ≟ snd   = no λ ()
⟨ _ , _ ⟩ ≟ apply = no λ ()
⟨ _ , _ ⟩ ≟ (_ ∘ _) = no λ ()

curry _ ≟ id      = no λ ()
curry _ ≟ fst     = no λ ()
curry _ ≟ snd     = no λ ()
curry _ ≟ apply   = no λ ()
curry _ ≟ (_ ∘ _) = no λ ()
