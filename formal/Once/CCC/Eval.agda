------------------------------------------------------------------------
-- Once.CCC.Eval
--
-- Semantic evaluation of IR terms.
--
-- Provides:
--   - PrimSem: Record for primitive semantics provider
--   - eval: Evaluator for IR parameterized by PrimSem
------------------------------------------------------------------------

module Once.CCC.Eval where

open import Data.String using (String)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_,_)

open import Once.Type
open import Once.CCC.IR

-- Import semantic interpretation of types from Once.Sem
open import Once.Semantics.Machine
  using (⟦_⟧; sem-pair; sem-fst; sem-snd; sem-inl; sem-inr; sem-case; sem-fold; sem-unfold)

-- Re-export ⟦_⟧ for convenience
open import Once.Semantics.Machine public using (⟦_⟧)

------------------------------------------------------------------------
-- Primitive Semantics Provider
--
-- Any module that wants to evaluate IR must provide semantics for
-- primitive operations via this record.
------------------------------------------------------------------------

record PrimSem : Set₁ where
  field
    evalPrim : ∀ {A B} → String → ⟦ A ⟧ → ⟦ B ⟧

open PrimSem public

------------------------------------------------------------------------
-- Semantic Evaluation
--
-- Evaluates IR terms given a primitive semantics provider.
-- AllocMode is ignored in semantics (it's a compilation concern).
------------------------------------------------------------------------

eval : PrimSem → ∀ {A B} → IR A B → ⟦ A ⟧ → ⟦ B ⟧
eval ps id x = x
eval ps (g ∘ f) x = eval ps g (eval ps f x)
eval ps (⟨ f , g ⟩ _) x = sem-pair (eval ps f x) (eval ps g x)
eval ps fst x = sem-fst x
eval ps snd x = sem-snd x
eval ps (inl _) x = sem-inl x
eval ps (inr _) x = sem-inr x
eval ps (case f g) x = sem-case (eval ps f) (eval ps g) x
eval ps terminal x = tt
eval ps initial ()
eval ps (curry f _) x = λ y → eval ps f (sem-pair x y)
eval ps apply (closure , arg) = closure arg
eval ps arr f = f
eval ps (fold _) x = sem-fold x
eval ps unfold x = sem-unfold x
eval ps (free-heap _) x = x
eval ps (Prim name) x = evalPrim ps name x
