------------------------------------------------------------------------
-- OCP-0009 · DIRECTED rung 0 — Once's own transformations as Hom-structure
--
-- The directed-HoTT observation (design doc Option 4b/5, now with a POC):
-- Once's IR already OWNS a directed structure — its rewrite system `_⟶_`.
-- A reduction is a non-invertible transformation between programs; the
-- reflexive-transitive closure `_⟶*_` is a HOM-TYPE: `Hom t u` = "t
-- transforms into u". This module reasons about that structure the way the
-- rest of the tower reasons about equality — Once reasoning about Once
-- TRANSFORMATIONS, shallowly (in Agda), all `--safe`:
--
--   * CATEGORY: programs are objects, transformation chains are morphisms —
--     identity (`done`), composition (chain append), unit + associativity
--     laws proven. (The free category on the reduction graph.)
--   * DIRECTEDNESS, genuinely: `fst ∘ ⟨id,id⟩ ⟶* id` holds, and
--     `¬ (id ⟶* fst ∘ ⟨id,id⟩)` is PROVEN (`id` is no rule's redex) —
--     a proposition SYMMETRIC EQUALITY CANNOT EVEN STATE. The endpoints
--     are equal in the model (both denote the identity function); only the
--     Hom knows which way computation went. Equality forgets direction;
--     Hom keeps it.
--   * TRANSPORT along a Hom: properties of the source carry to the target
--     (pointwise, funext-free on the demo chain; the general theorem is
--     `Theory.Eval.EvalSound.eval-sound : t ⟶ u → ∀ x → eval t x ≡
--     eval u x` — one funext, for congruence under `curry`).
--
-- What this rung is NOT (the honest ceiling, as always): the research row
-- is `Hom` as an OBJECT-LANGUAGE type former with decidable directed
-- conversion (directed type theory with a kernel — exists nowhere yet).
-- This rung demonstrates the reasoning SHAPE on the reflected IR, exactly
-- as `Conv`/NbE first demonstrated equality-reasoning before the CwF rungs
-- internalized it.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPDir where

open import normalizer.Syntax.Types
  using ( Ty; Unit; _*_; _+_; ⊥; ¬_; _≡_; refl; cong )
open import normalizer.Syntax.CCC as C
  using ( Term; _⟶_; _⟶*_; done; step
        ; id-left; id-right; fst-pair )
open import normalizer.Testing.Evaluator
  using ( ⟦_⟧T; eval )

------------------------------------------------------------------------
-- Hom-structure: programs and their transformations form a category.
------------------------------------------------------------------------

Hom : ∀ {A B} → Term A B → Term A B → Set
Hom t u = t ⟶* u

idH : ∀ {A B} {t : Term A B} → Hom t t
idH = done

infixr 9 _∘H_
_∘H_ : ∀ {A B} {t u v : Term A B} → Hom u v → Hom t u → Hom t v
q ∘H done     = q
q ∘H step s p = step s (q ∘H p)

-- Category laws (on-the-nose, not up to homotopy — rung 0 is 1-categorical).
∘H-idˡ : ∀ {A B} {t u : Term A B} (p : Hom t u) → (idH ∘H p) ≡ p
∘H-idˡ done       = refl
∘H-idˡ (step s p) = cong (step s) (∘H-idˡ p)

∘H-idʳ : ∀ {A B} {t u : Term A B} (p : Hom t u) → (p ∘H idH) ≡ p
∘H-idʳ p = refl

∘H-assoc : ∀ {A B} {t u v w : Term A B}
           (r : Hom v w) (q : Hom u v) (p : Hom t u) →
           ((r ∘H q) ∘H p) ≡ (r ∘H (q ∘H p))
∘H-assoc r q done       = refl
∘H-assoc r q (step s p) = cong (step s) (∘H-assoc r q p)

------------------------------------------------------------------------
-- DIRECTEDNESS, proven. The demonstration pair lives at a concrete type.
------------------------------------------------------------------------

B₂ : Ty
B₂ = Unit + Unit

-- The optimization: project the first copy of a duplicated value.
src tgt : Term B₂ B₂
src = C.fst C.∘ C.⟨ C.id , C.id ⟩
tgt = C.id

-- Forward: one rewrite step.
opt : Hom src tgt
opt = step fst-pair done

-- `id` is fully reduced: it is no rule's redex — every `_⟶_` constructor's
-- source is headed by `∘`, `⟨_,_⟩`, `[_,_]`, `curry`, or `cata`.
id-stuck : ∀ {A} {v : Term A A} → C.id ⟶ v → ⊥
id-stuck ()

-- Backward: PROVABLY no transformation — the directed content.
no-way-back : ¬ Hom tgt src
no-way-back (step s _) = id-stuck s

-- ...while the ENDPOINTS ARE EQUAL in the model (pointwise, definitional):
-- symmetric equality sees no difference between `src` and `tgt` at all.
-- Direction is invisible to equality and native to Hom.
_ : ∀ (x : ⟦ B₂ ⟧T) → eval src x ≡ eval tgt x
_ = λ x → refl

------------------------------------------------------------------------
-- Transport along a Hom: what holds of the source holds of the target.
-- On this chain the denotations agree definitionally, so the transport is
-- funext-free; the general per-step theorem is `EvalSound.eval-sound`.
------------------------------------------------------------------------

transport-opt : (P : ⟦ B₂ ⟧T → Set) →
                (∀ x → P (eval src x)) → (∀ x → P (eval tgt x))
transport-opt P h x = h x

------------------------------------------------------------------------
-- The composite picture: a two-step optimization pipeline, as a morphism.
------------------------------------------------------------------------

src₂ : Term B₂ B₂
src₂ = C.id C.∘ (C.fst C.∘ C.⟨ C.id , C.id ⟩)

pipeline : Hom src₂ tgt
pipeline = opt ∘H step id-left done

-- Pipelines compose associatively and have identities — program
-- optimization is functorial data, not folklore: exactly the structure a
-- DIRECTED object-language `Hom` would internalize.
_ : (pipeline ∘H idH) ≡ pipeline
_ = refl
