------------------------------------------------------------------------
-- normalizer.Theory.Eval.FixInduction
--
-- Structural INDUCTION PRINCIPLE for the NO_POSITIVITY_CHECK fixpoint
-- `Fix F` of a first-order functor code `F : Func` (Id / K / ⊕ / ⊗). This
-- is the proof-level mirror of CataTerminates' `cata`/`map-cata`: a mutual
-- structural descent that Agda's termination checker accepts WITHOUT any
-- pragma —
--
--   * `induct`     recurses `fix x ↦ x` (one layer down), and
--   * `induct-map` recurses on the FUNCTOR CODE `G` (Id/K/⊕/⊗) until it
--     reaches an `Id` position, where the value sitting there is a
--     strictly-smaller sub-`Fix` and `induct` is called on it.
--
-- So structural induction over `Fix TermF` is rigorous (no pragma, no
-- postulate) — the recursor every structural transparency / idempotence
-- theorem about `normalize = cata TermF normalize-step` is built on.
--
-- `All-rec F G P y` collects the induction hypotheses: it asserts the
-- predicate `P` at every RECURSIVE (`Id`) position of one functor layer
-- `y : ⟦ G ⟧FS (Fix F)`, and is trivially `⊤` at `K` (constant) positions.
-- These are exactly the hypotheses available when proving `P (fix x)`.
--
-- Build: bootstrap/check.sh normalizer/Theory/Eval/FixInduction.agda
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module normalizer.Theory.Eval.FixInduction where

open import normalizer.Syntax.Types
  using (Func; Id; One; Kc; _⊕_; _⊗_; ⊤; tt; _×_; _,_; inj₁; inj₂)
open import normalizer.Testing.Evaluator using (⟦_⟧FS; Fix; fix)

------------------------------------------------------------------------
-- Induction hypotheses collected over one functor layer.
------------------------------------------------------------------------

All-rec : ∀ F G → (Fix F → Set) → ⟦ G ⟧FS (Fix F) → Set
All-rec F Id      P y        = P y
All-rec F One     P _        = ⊤
All-rec F (Kc _)  P _        = ⊤
All-rec F (G ⊕ H) P (inj₁ y) = All-rec F G P y
All-rec F (G ⊕ H) P (inj₂ z) = All-rec F H P z
All-rec F (G ⊗ H) P (y , z)  = All-rec F G P y × All-rec F H P z

------------------------------------------------------------------------
-- The structural induction principle — NO {-# TERMINATING #-}.
--
-- Given a `method` proving `P (fix x)` from the hypotheses `All-rec F F P x`
-- at the recursive positions of the layer `x`, conclude `P c` for every
-- `c : Fix F`.
------------------------------------------------------------------------

mutual
  induct : ∀ F (P : Fix F → Set) →
           (∀ x → All-rec F F P x → P (fix x)) →
           ∀ c → P c
  induct F P method (fix x) = method x (induct-map F F P method x)

  induct-map : ∀ F G (P : Fix F → Set) →
               (∀ x → All-rec F F P x → P (fix x)) →
               (y : ⟦ G ⟧FS (Fix F)) → All-rec F G P y
  induct-map F Id      P method y        = induct F P method y
  induct-map F One     P method _        = tt
  induct-map F (Kc _)  P method _        = tt
  induct-map F (G ⊕ H) P method (inj₁ y) = induct-map F G P method y
  induct-map F (G ⊕ H) P method (inj₂ z) = induct-map F H P method z
  induct-map F (G ⊗ H) P method (y , z)  =
    induct-map F G P method y , induct-map F H P method z
