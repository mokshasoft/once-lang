-- Evidence for plan 0.119 §7 A″ (plans/0.119-A2.patch); checked against the Spec at ef91bbbd3
-- plus A″ items 1–2, not part of the build. Check: copy into formal/POC/, `make agda MODULE=POC/<file>`.
{-# OPTIONS --safe #-}
-- POC (not committed): `Spec.Metatheory.Coherence` is false when Σ declares
-- one operation twice. A reference typed by the first declaration and one
-- typed by the second mean calls of two different operations, and two
-- trees with different calls are never related.
module POC.CoherenceDup where

open import Data.Empty using (⊥)
open import Data.List using ([]; _∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (refl)
open import Relation.Nullary using (¬_)
open import Once.Spec.Name using (canonical)
open import Once.Spec.Grade using (mk-kind; Many; eff)
open import Once.Spec.Numerics using (TargetNum)
open import Once.Spec.Signature using (Signature; _∶_; arrow; unit; op; e-eff; call)
open import Once.Spec.Type using (∅ₖ; TySub; Respects)
open import Once.Spec.Context using (∅; [])
open import Once.Spec.Core.Syntax using (Defs; []; sigop)
import Once.Spec.Core.Typing as CoreTyping
import Once.Spec.Core.Meaning as Meaning
import Once.Spec.Observation as Observation
import Once.Spec.Equivalence as Equivalence
open import Once.Spec.Metatheory using (Coherence)

c = canonical ("c" ∷ [])
t = arrow unit (mk-kind Many eff) unit

dupΣ : Signature
dupΣ = (c ∶ t) ∷ (c ∶ t) ∷ []

open CoreTyping dupΣ []
open Observation dupΣ using (Interp)

ι : Interp
ι = record
  { value  = λ { (here refl) () ; (there (here refl)) () ; (there (there ())) _ }
  ; answer = λ { (op (here refl) e-eff) h a → tt ; (op (there (here refl)) e-eff) h a → tt
               ; (op (there (there ())) _) h a } }

d₁ d₂ : ∅ₖ ⊩ ∅ ⊢[ [] ] sigop c t ∷ _ ! _
d₁ = ⊢sigop (here refl)
d₂ = ⊢sigop (there (here refl))

coherence-false : ∀ (fmt : TargetNum) → ¬ Coherence dupΣ fmt []
coherence-false fmt C with Coherence.coherent C d₁ d₂ δ (λ ()) σ r r tt tt 2
  where
    δ : Meaning.DefSem dupΣ fmt []
    δ = record { defs = λ () ; interp = ι }
    σ : TySub 0 0
    σ ()
    r : Respects ∅ₖ ∅ₖ σ
    r ()
... | Equivalence.done≈ p with p tt tt (λ k → tt)
... | ()
