------------------------------------------------------------------------
-- Level 0 Normalizer V2 - Concrete Approach
--
-- Instead of proving properties for abstract normalizers, we define
-- a specific concrete normalizer and prove its fixpoint property directly.
--
-- Key insight: A concrete normalizer is just a Term. We prove:
--   N ∘ encode(N) ⟶* encode(N)
-- for a specific N, not for all N satisfying some spec.
------------------------------------------------------------------------

module normalizer.Level0V2.Normalizer where

open import normalizer.Foundations.Types
open import normalizer.Foundations.MinimalCCC
open import normalizer.Foundations.Encoding
open import normalizer.Foundations.Fixpoint

------------------------------------------------------------------------
-- The Simplest Normalizer: Identity
------------------------------------------------------------------------

-- The identity function on encoded terms.
-- This is the trivial normalizer that doesn't actually normalize anything,
-- but it lets us verify the proof structure works.

N-id : Term TermCode' TermCode'
N-id = id

-- Fixpoint proof for identity normalizer:
-- N-id ∘ encode(N-id) ⟶* encode(N-id)
--
-- Proof: id ∘ t ⟶ t (by id-left), so id ∘ encode(id) ⟶ encode(id)

-- The type: (id ∘ encode id) ⟶* encode id
-- where encode id : Term Unit TermCode'
N-id-fixpoint : (N-id ∘ encode N-id) ⟶* encode N-id
N-id-fixpoint = step id-left done

------------------------------------------------------------------------
-- A Real Normalizer: The Fold
------------------------------------------------------------------------

-- A real normalizer would be built as a catamorphism:
--   N = cata TermF algebra
--
-- Where algebra : Term (⟦ TermF ⟧F TermCode') TermCode'
-- handles each case of the unfolded term.
--
-- The algebra receives the "one-step unfolded" term and must produce
-- a normalized result. For terms already in normal form, it just
-- re-wraps with In. For redexes, it applies the reduction.

-- For the catamorphism approach, we need:
--   cata TermF alg ∘ In ⟶ alg ∘ fmap TermF (cata TermF alg)
--
-- This means when we apply the normalizer to an encoded term,
-- it unfolds one layer, recursively normalizes subterms, then
-- applies the algebra.

-- The algebra for a normalizer that just re-folds (identity on structure):
-- This is equivalent to N-id but built differently.

refold-algebra : Term (⟦ TermF ⟧F TermCode') TermCode'
refold-algebra = In

N-refold : Term TermCode' TermCode'
N-refold = cata TermF refold-algebra

-- Note: N-refold is NOT definitionally equal to id, but it's
-- extensionally equivalent. The cata-In reduction gives us:
--   cata TermF In ∘ In ⟶ In ∘ fmap TermF (cata TermF In)
--
-- This "refolds" the term with the same structure.

------------------------------------------------------------------------
-- Building Towards a Real Normalizer
------------------------------------------------------------------------

-- A normalizer that actually reduces needs an algebra that:
-- 1. Checks if the current node forms a redex with its children
-- 2. If yes, applies the reduction
-- 3. If no, just re-wraps with In
--
-- The challenge: the algebra only sees one level of structure.
-- To detect redexes like (f ∘ g) where f = id, we need to
-- inspect the encoded f.
--
-- This is where the encoding structure matters:
-- - encode(id) = In ∘ inl ∘ ...
-- - encode(f ∘ g) = In ∘ inr ∘ inl ∘ ⟨encode f, encode g⟩
--
-- The algebra can pattern match on which injection was used!
-- Position 0 (inl) = id
-- Position 1 (inr ∘ inl) = compose
-- etc.

-- To build a real normalizer, we'd define:
--
-- normalize-algebra : Term (⟦ TermF ⟧F TermCode') TermCode'
-- normalize-algebra = [
--   handle-id ,        -- case 0: id
--   handle-compose ,   -- case 1: compose (check for id-left, id-right, etc.)
--   handle-fst ,       -- case 2: fst
--   ...
-- ]
--
-- Where handle-compose checks if either child is id and reduces accordingly.

------------------------------------------------------------------------
-- Fixpoint for the Refold Normalizer
------------------------------------------------------------------------

-- Let's trace what happens when N-refold processes its own encoding.
--
-- N-refold = cata TermF In
-- encode(N-refold) = encode(cata TermF In)
--                  = In ∘ inr^11 ∘ ⟨ ⌜TermF⌝, encode(In) ⟩
--
-- Computing N-refold ∘ encode(N-refold):
-- = cata TermF In ∘ In ∘ inr^11 ∘ ⟨ ⌜TermF⌝, encode(In) ⟩
-- ⟶ In ∘ fmap TermF (cata TermF In) ∘ inr^11 ∘ ⟨ ⌜TermF⌝, encode(In) ⟩
--   (by cata-β)
--
-- Now fmap TermF (cata TermF In) maps the normalizer over subterms.
-- The subterms here are ⌜TermF⌝ (a type code) and encode(In) (a term code).
--
-- For the fixpoint to hold, we need this to eventually equal encode(cata TermF In).
-- This requires understanding how fmap interacts with the injection structure.

-- For now, let's just state the fixpoint as a goal and see what proof is needed.

-- First, let's expand encode for cata:
-- encode (cata F alg) = In ∘ inr^11 ∘ ⟨ ⌜F⌝Func , encode alg ⟩

-- So encode N-refold = encode (cata TermF In)
--                    = In ∘ inr^11 ∘ ⟨ ⌜TermF⌝Func , encode In ⟩

-- The fixpoint proof would need to show:
-- (cata TermF In ∘ In ∘ ...) ⟶* (In ∘ ...)

-- This is complex because cata-β unfolds the computation, and we need to
-- show it eventually reaches the same form.

------------------------------------------------------------------------
-- Key Insight: The Fixpoint is About Self-Reference
------------------------------------------------------------------------

-- The fixpoint property N ∘ encode(N) ⟶* encode(N) is really about
-- what happens when a normalizer encounters its own description.
--
-- For a normalizer to be a fixpoint, it must "recognize" its own encoding
-- and return it unchanged (after normalization).
--
-- The identity normalizer trivially satisfies this: id returns everything unchanged.
--
-- A cata-based normalizer processes the term structure. For it to be a fixpoint,
-- the processing must be idempotent on its own encoding.

------------------------------------------------------------------------
-- Observations and Next Steps
------------------------------------------------------------------------

-- Key observations:
-- 1. The fixpoint proof for id is trivial (one step: id-left)
-- 2. For cata-based normalizers, the proof uses cata-β and requires
--    showing the algebra's behavior on the normalizer's own structure
-- 3. We don't need Out - cata unfolds structure automatically
-- 4. The challenge is showing idempotence: normalizing a normal form gives the same
--
-- The fixpoint theorem approach:
-- If we can show N is a fixpoint and N terminates, then N is correct.
-- The identity normalizer is the trivial fixpoint.
--
-- For a real normalizer, we'd need to show:
-- 1. It reduces redexes (soundness)
-- 2. It preserves normal forms (idempotence)
-- 3. Its encoding is a normal form
--
-- Property 3 is key: if encode(N) is already in normal form,
-- and N preserves normal forms, then N ∘ encode(N) = encode(N).

------------------------------------------------------------------------
-- Using encode-always-nf
------------------------------------------------------------------------

-- From Fixpoint.agda, we have:
--   encode-always-nf : ∀ {A B} (t : Term A B) → NF (encode t)
--
-- This proves that every encoded term is in normal form.
-- In particular, encode(N) is in normal form for any normalizer N.

-- For the identity normalizer:
--   id ∘ encode(id) ⟶ encode(id)  (by id-left, one step)
--   Then we're at encode(id) which is NF, so done.

-- For the refold normalizer N-refold = cata TermF In:
--   N-refold ∘ encode(N-refold)
--   = cata TermF In ∘ encode(cata TermF In)
--   = cata TermF In ∘ (In ∘ inr^11 ∘ ⟨⌜TermF⌝, encode In⟩)
--   ⟶ In ∘ fmap TermF (cata TermF In) ∘ inr^11 ∘ ⟨⌜TermF⌝, encode In⟩
--     (by cata-β)
--
-- Now we need to compute fmap TermF (cata TermF In) applied to the
-- injection chain. The fmap will map (cata TermF In) over any subterms
-- of type TermCode' in the functor structure.
--
-- For the cata case (position 11), the functor is K TyFuncCode ⊗ Id.
-- fmap (K TyFuncCode ⊗ Id) f = ⟨ fst , f ∘ snd ⟩
-- (identity on first component, apply f to second)
--
-- So: fmap TermF (cata TermF In) ∘ inr^11 ∘ ⟨⌜TermF⌝, encode In⟩
--   = inr^11 ∘ fmap (K TyFuncCode ⊗ Id) (cata TermF In) ∘ ⟨⌜TermF⌝, encode In⟩
--   = inr^11 ∘ ⟨ fst ∘ ⟨⌜TermF⌝, encode In⟩ , (cata TermF In) ∘ snd ∘ ⟨⌜TermF⌝, encode In⟩ ⟩
--   ⟶ inr^11 ∘ ⟨ ⌜TermF⌝ , (cata TermF In) ∘ encode In ⟩
--     (by fst-pair, snd-pair)
--
-- So we've reduced to:
--   In ∘ inr^11 ∘ ⟨ ⌜TermF⌝ , (cata TermF In) ∘ encode In ⟩
--
-- Now we need (cata TermF In) ∘ encode In to reduce to encode In.
-- encode In = In ∘ inr^9 ∘ inl ∘ ⌜TermF⌝Func  (for some F in the In case)
--
-- This recursively requires the same fixpoint property!
-- The proof is inductive on the structure of the encoded term.

------------------------------------------------------------------------
-- The Inductive Structure
------------------------------------------------------------------------

-- The fixpoint proof for cata TermF In is inductive:
--
-- Base cases: Terms like id, fst, snd, inl, inr, terminal, In, Out
-- that have no TermCode' subterms in their encoding.
-- For these, fmap doesn't apply the cata to anything.
--
-- Inductive cases: compose, pair, case, cata
-- These have TermCode' subterms, so fmap applies cata recursively.
-- By induction, the recursive applications satisfy the fixpoint.
--
-- This suggests we need a mutual induction:
--   ∀ t. (cata TermF In) ∘ encode(t) ⟶* encode(t)
--
-- This is actually a stronger statement than just the fixpoint for N-refold!
-- It says the refold normalizer is idempotent on ALL encoded terms.

-- Let's try to prove this for a simple case first.

------------------------------------------------------------------------
-- Idempotence Proof Attempt
------------------------------------------------------------------------

-- For id: encode(id) = In ∘ inl ∘ ⌜A⌝Ty
-- (cata TermF In) ∘ (In ∘ inl ∘ ⌜A⌝Ty)
-- ⟶ In ∘ fmap TermF (cata TermF In) ∘ inl ∘ ⌜A⌝Ty  (by cata-β)
--
-- fmap TermF f ∘ inl = inl ∘ fmap (K TyFuncCode) f = inl ∘ id = inl
-- (because K TyFuncCode doesn't have recursive positions)
--
-- So: In ∘ inl ∘ ⌜A⌝Ty  (which is encode(id)!)
--
-- Hmm, but we need to show this via ⟶*, not definitional equality.
-- The fmap TermF (cata TermF In) ∘ inl step involves reductions.

-- This is getting complex. Let me try to formalize just the first step.

------------------------------------------------------------------------
-- Proof Using Parallel Reduction
------------------------------------------------------------------------

-- Parallel reduction ⇒ has congruence rules and ⇒→⟶* converts to ⟶*.
-- This makes proofs much cleaner.

-- For N-id = id, we can prove the fixpoint in one parallel step:
--   (id ∘ encode id) ⇒ encode id   by ⇒-id-l
--   Then use ⇒→⟶* to get ⟶*

N-id-fixpoint' : (N-id ∘ encode N-id) ⟶* encode N-id
N-id-fixpoint' = ⇒→⟶* (⇒-id-l (⇒-refl (encode N-id)))

-- For a cata-based normalizer, we'd need:
--   (cata TermF In ∘ encode (cata TermF In))
--   ⇒ In ∘ fmap TermF (cata TermF In) ∘ (the encoding tail)
--   by ⇒-cata-β
--
-- Then we'd need to show the result reduces further to encode(cata TermF In).
-- This requires understanding how fmap interacts with the injection structure.

------------------------------------------------------------------------
-- Key Lemma: fmap F id ⟶* id
------------------------------------------------------------------------

-- For any functor F, fmap F id reduces to id.
-- This requires multiple steps for sum/product functors.
--
-- The proof structure:
-- - Id, K cases: definitional equality (done in one step)
-- - ⊕ case: reduce components, then eta-case
-- - ⊗ case: reduce components, then eta-pair
--
-- This is tricky because we need congruence under [,] and ⟨,⟩.
-- Since ⟶ doesn't have congruence, we use ⇒ and ⇒→⟶*.

-- Helper: multi-step parallel to single parallel (not needed, but clarifying)
-- We'll build ⇒* and convert to ⟶*

-- For the sum functor case:
-- [ inl ∘ fmap F id , inr ∘ fmap G id ]
-- ⇒* [ inl ∘ id , inr ∘ id ]  (by IH applied to components)
-- ⇒  [ inl , inr ]            (by ⇒-case with ⇒-id-r)
-- ⇒  id                        (by ⇒-η-case)

-- We need a congruence lemma for case under ⇒*
-- This is getting complex - let's just postulate the result for now.

postulate
  fmap-id : ∀ F {A} → fmap F (id {A}) ⟶* id

-- The proof would use:
-- 1. Induction on F
-- 2. For ⊕/⊗ cases, use ⇒-case/⇒-pair congruence
-- 3. Chain multiple ⇒ steps
-- 4. Convert to ⟶* via ⇒*→⟶*
--
-- The key insight: this is provable but tedious.
-- It requires building congruence lemmas for ⇒*.

