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

module normalizer.Level0.Normalizer where

open import normalizer.Foundations.Types
open import normalizer.Foundations.MinimalCCC
open import normalizer.Foundations.Encoding
-- Fixpoint.agda not needed - removed

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

-- Parallel reduction ⟹has congruence rules and ⟹→⟶* converts to ⟶*.
-- This makes proofs much cleaner.

-- For N-id = id, we can prove the fixpoint in one parallel step:
--   (id ∘ encode id) ⟹encode id   by ⟹-id-l
--   Then use ⟹→⟶* to get ⟶*

N-id-fixpoint' : (N-id ∘ encode N-id) ⟶* encode N-id
N-id-fixpoint' = ⟹→⟶* (⟹-id-l (⟹-refl (encode N-id)))

-- For a cata-based normalizer, we'd need:
--   (cata TermF In ∘ encode (cata TermF In))
--   ⟹In ∘ fmap TermF (cata TermF In) ∘ (the encoding tail)
--   by ⟹-cata-β
--
-- Then we'd need to show the result reduces further to encode(cata TermF In).
-- This requires understanding how fmap interacts with the injection structure.

------------------------------------------------------------------------
-- Key Lemma: fmap F id ⟶* id
------------------------------------------------------------------------

-- For any functor F, fmap F id reduces to id.
-- This requires multiple steps for sum/product functors.
--
-- Proof structure:
-- - Id, K cases: definitional equality
-- - ⊕ case: [ inl ∘ fmap F id , inr ∘ fmap G id ] ⟶* [ inl , inr ] ⟶ id
-- - ⊗ case: ⟨ fmap F id ∘ fst , fmap G id ∘ snd ⟩ ⟶* ⟨ fst , snd ⟩ ⟶ id

------------------------------------------------------------------------
-- Infrastructure: Congruence lemmas for ⟹*
------------------------------------------------------------------------

-- Transitivity of ⟹*
⟹*-trans : ∀ {A B} {t u v : Term A B} → t ⟹* u → u ⟹* v → t ⟹* v
⟹*-trans done⟹ q = q
⟹*-trans (step⟹ p ps) q = step⟹ p (⟹*-trans ps q)

-- Single step to multi-step
⟹→⟹* : ∀ {A B} {t u : Term A B} → t ⟹ u → t ⟹* u
⟹→⟹* p = step⟹ p done⟹

-- Congruence: composition on the right
⟹*-∘-right : ∀ {A B C} {f : Term B C} {g g' : Term A B} →
             g ⟹* g' → (f ∘ g) ⟹* (f ∘ g')
⟹*-∘-right done⟹ = done⟹
⟹*-∘-right (step⟹ p ps) = step⟹ (⟹-∘ (⟹-refl _) p) (⟹*-∘-right ps)

-- Congruence: composition on the left
⟹*-∘-left : ∀ {A B C} {f f' : Term B C} {g : Term A B} →
            f ⟹* f' → (f ∘ g) ⟹* (f' ∘ g)
⟹*-∘-left done⟹ = done⟹
⟹*-∘-left (step⟹ p ps) = step⟹ (⟹-∘ p (⟹-refl _)) (⟹*-∘-left ps)

-- Congruence: case/coproduct
⟹*-case : ∀ {A B C} {f f' : Term A C} {g g' : Term B C} →
          f ⟹* f' → g ⟹* g' → [ f , g ] ⟹* [ f' , g' ]
⟹*-case done⟹ done⟹ = done⟹
⟹*-case done⟹ (step⟹ q qs) = step⟹ (⟹-case (⟹-refl _) q) (⟹*-case done⟹ qs)
⟹*-case (step⟹ p ps) qs = step⟹ (⟹-case p (⟹-refl _)) (⟹*-case ps qs)

-- Congruence: pair/product
⟹*-pair : ∀ {A B C} {f f' : Term C A} {g g' : Term C B} →
          f ⟹* f' → g ⟹* g' → ⟨ f , g ⟩ ⟹* ⟨ f' , g' ⟩
⟹*-pair done⟹ done⟹ = done⟹
⟹*-pair done⟹ (step⟹ q qs) = step⟹ (⟹-pair (⟹-refl _) q) (⟹*-pair done⟹ qs)
⟹*-pair (step⟹ p ps) qs = step⟹ (⟹-pair p (⟹-refl _)) (⟹*-pair ps qs)

------------------------------------------------------------------------
-- The fmap-id proof
------------------------------------------------------------------------

-- First in ⟹* form, then convert to ⟶*

fmap-id⟹* : ∀ F {A} → fmap F (id {A}) ⟹* id
fmap-id⟹* Id = done⟹  -- fmap Id id = id definitionally
fmap-id⟹* (K _) = done⟹  -- fmap (K _) _ = id definitionally
fmap-id⟹* (F ⊕ G) =
  -- fmap (F ⊕ G) id = [ inl ∘ fmap F id , inr ∘ fmap G id ]
  -- Goal: [ inl ∘ fmap F id , inr ∘ fmap G id ] ⟹* id
  --
  -- Step 1: By IH, fmap F id ⟹* id and fmap G id ⟹* id
  -- Step 2: inl ∘ fmap F id ⟹* inl ∘ id  (congruence)
  -- Step 3: inl ∘ id ⟹inl               (id-right)
  -- Step 4: Similarly for inr side
  -- Step 5: [ inl , inr ] ⟹id           (eta-case)
  let
    -- IH: fmap F id ⟹* id, fmap G id ⟹* id
    ih-F = fmap-id⟹* F
    ih-G = fmap-id⟹* G
    -- inl ∘ fmap F id ⟹* inl ∘ id ⟹* inl
    left-reduces : (inl ∘ fmap F id) ⟹* inl
    left-reduces = ⟹*-trans (⟹*-∘-right ih-F) (⟹→⟹* (⟹-id-r ⟹-inl))
    -- inr ∘ fmap G id ⟹* inr ∘ id ⟹* inr
    right-reduces : (inr ∘ fmap G id) ⟹* inr
    right-reduces = ⟹*-trans (⟹*-∘-right ih-G) (⟹→⟹* (⟹-id-r ⟹-inr))
    -- [ inl ∘ fmap F id , inr ∘ fmap G id ] ⟹* [ inl , inr ]
    case-reduces : [ inl ∘ fmap F id , inr ∘ fmap G id ] ⟹* [ inl , inr ]
    case-reduces = ⟹*-case left-reduces right-reduces
  in
    -- [ inl , inr ] ⟹id by eta-case
    ⟹*-trans case-reduces (⟹→⟹* ⟹-η-case)

fmap-id⟹* (F ⊗ G) =
  -- fmap (F ⊗ G) id = ⟨ fmap F id ∘ fst , fmap G id ∘ snd ⟩
  -- Goal: ⟨ fmap F id ∘ fst , fmap G id ∘ snd ⟩ ⟹* id
  --
  -- Step 1: By IH, fmap F id ⟹* id and fmap G id ⟹* id
  -- Step 2: fmap F id ∘ fst ⟹* id ∘ fst ⟹* fst  (congruence + id-left)
  -- Step 3: Similarly for snd side
  -- Step 4: ⟨ fst , snd ⟩ ⟹id                   (eta-pair)
  let
    ih-F = fmap-id⟹* F
    ih-G = fmap-id⟹* G
    -- fmap F id ∘ fst ⟹* id ∘ fst ⟹fst
    left-reduces : (fmap F id ∘ fst) ⟹* fst
    left-reduces = ⟹*-trans (⟹*-∘-left ih-F) (⟹→⟹* (⟹-id-l ⟹-fst))
    -- fmap G id ∘ snd ⟹* id ∘ snd ⟹snd
    right-reduces : (fmap G id ∘ snd) ⟹* snd
    right-reduces = ⟹*-trans (⟹*-∘-left ih-G) (⟹→⟹* (⟹-id-l ⟹-snd))
    -- ⟨ fmap F id ∘ fst , fmap G id ∘ snd ⟩ ⟹* ⟨ fst , snd ⟩
    pair-reduces : ⟨ fmap F id ∘ fst , fmap G id ∘ snd ⟩ ⟹* ⟨ fst , snd ⟩
    pair-reduces = ⟹*-pair left-reduces right-reduces
  in
    -- ⟨ fst , snd ⟩ ⟹id by eta-pair
    ⟹*-trans pair-reduces (⟹→⟹* ⟹-η-pair)

-- Convert to ⟶*
fmap-id : ∀ F {A} → fmap F (id {A}) ⟶* id
fmap-id F = ⟹*→⟶* (fmap-id⟹* F)

------------------------------------------------------------------------
-- Fixpoint for cata TermF In (the "refold" normalizer)
------------------------------------------------------------------------

-- Key property: the refold normalizer is idempotent on ALL encoded terms.
-- ∀ t. (cata TermF In) ∘ encode(t) ⟶* encode(t)
--
-- This is stronger than just the fixpoint for N-refold itself.
-- If we prove this, the N-refold fixpoint follows as a special case.

-- The proof strategy:
-- 1. encode(t) = In ∘ injection-chain ∘ payload
-- 2. (cata TermF In) ∘ In ⟶ In ∘ fmap TermF (cata TermF In) by cata-β
-- 3. fmap TermF (cata TermF In) applies normalizer to subterms of type TermCode'
-- 4. By induction, the subterm applications also reduce to identity
-- 5. The whole thing reconstructs encode(t)

-- First, we need a lemma about how fmap interacts with injection chains.
-- For a sum functor F ⊕ G:
--   fmap (F ⊕ G) f ∘ inl = [ inl ∘ fmap F f , inr ∘ fmap G f ] ∘ inl
--                        ⟶ inl ∘ fmap F f   (by case-inl)

-- This lemma shows fmap distributes through injection chains
fmap-inl : ∀ {A B} F G (f : Term A B) →
           (fmap (F ⊕ G) f ∘ inl) ⟶* (inl ∘ fmap F f)
fmap-inl F G f = step case-inl done

fmap-inr : ∀ {A B} F G (f : Term A B) →
           (fmap (F ⊕ G) f ∘ inr) ⟶* (inr ∘ fmap G f)
fmap-inr F G f = step case-inr done

-- For product functors, fmap distributes through pair:
--   fmap (F ⊗ G) f ∘ ⟨ a , b ⟩ = ⟨ fmap F f ∘ fst , fmap G f ∘ snd ⟩ ∘ ⟨ a , b ⟩
-- This requires fst-pair and snd-pair reductions

-- The main idempotence proof is by induction on the term t.
-- For each constructor, we show (cata TermF In) ∘ encode(t) ⟶* encode(t).

-- Let's trace through the id case as an example:
-- encode(id) = In ∘ inl ∘ ⌜A⌝Ty
-- (cata TermF In) ∘ In ∘ inl ∘ ⌜A⌝Ty
-- ⟶ In ∘ fmap TermF (cata TermF In) ∘ inl ∘ ⌜A⌝Ty  (cata-β)
-- ⟶ In ∘ inl ∘ fmap (K TyFuncCode) (cata TermF In) ∘ ⌜A⌝Ty  (case-inl via fmap)
-- = In ∘ inl ∘ id ∘ ⌜A⌝Ty  (fmap K _ = id)
-- ⟶ In ∘ inl ∘ ⌜A⌝Ty  (id-left)
-- = encode(id)  ✓

-- The full proof requires handling all 12 term constructors.
-- The simpler cases are done; the rest are proof obligations.

-- Note: ⟶*-trans is now provided by MinimalCCC

------------------------------------------------------------------------
-- Associativity
------------------------------------------------------------------------

-- In a CCC, composition is associative: (f ∘ g) ∘ h = f ∘ (g ∘ h)
-- Our Term type doesn't have this definitionally, so we add it as an axiom.
-- This is semantically justified: in any CCC model, these are equal.

-- We express this as a bi-directional reduction equivalence.
-- For proofs, we use ⟷ (convertibility) or add explicit associativity steps.

-- For our purposes, we need:
--   cata F alg ∘ (In ∘ t) ⟶* (alg ∘ fmap F (cata F alg)) ∘ t
--
-- This follows from cata-β if we could reassociate:
--   cata F alg ∘ (In ∘ t)
--   = (cata F alg ∘ In) ∘ t      (assoc)
--   ⟶ (alg ∘ fmap F (cata F alg)) ∘ t  (cata-β under context)

-- Derived cata reduction using assoc-l
-- cata F alg ∘ (In ∘ t)
-- ⟶ (cata F alg ∘ In) ∘ t    by assoc-l
-- ⟶ (alg ∘ fmap F (cata F alg)) ∘ t    by cata-β

-- Congruence helper: if x ⟶ y, then x ∘ t ⟶* y ∘ t
-- Uses parallel reduction which has congruence rules
∘-cong-left : ∀ {A B C} {x y : Term B C} (t : Term A B) →
              x ⟶ y → (x ∘ t) ⟶* (y ∘ t)
∘-cong-left t r = ⟹→⟶* (⟹-∘ (⟶→⟹ r) (⟹-refl t))

-- Derived cata reduction using assoc-l and congruence
-- cata F alg ∘ (In ∘ t)
-- ⟶ (cata F alg ∘ In) ∘ t    by assoc-l
-- ⟶* (alg ∘ fmap F (cata F alg)) ∘ t    by cata-β with congruence
cata-β-right : ∀ {F A B} {alg : Term (⟦ F ⟧F A) A} {t : Term B (⟦ F ⟧F (μ F))} →
               (cata F alg ∘ (In ∘ t)) ⟶* ((alg ∘ fmap F (cata F alg)) ∘ t)
cata-β-right {F} {A} {B} {alg} {t} =
  ⟶*-trans (step assoc-l done)
           (∘-cong-left t cata-β)

-- The idempotence theorem (full proof would be large)
-- We prove this by showing each encode case reduces back to itself

-- The remaining cases follow the same pattern:
-- 1. Use cata-β-right to unfold the cata
-- 2. Use assoc-l and case reductions to distribute fmap through injections
-- 3. Use fmap-id (for K functors) and eta rules to collapse to identity
-- 4. For recursive cases, apply IH and congruence
--
-- The proofs are tedious but mechanical. The id case is done fully
-- as a template; the rest are proof obligations.

------------------------------------------------------------------------
-- Additional congruence lemmas
------------------------------------------------------------------------

-- Congruence: if f ⟶* f', then f ∘ g ⟶* f' ∘ g
∘-cong-left' : ∀ {A B C} {f f' : Term B C} (g : Term A B) →
               f ⟶* f' → (f ∘ g) ⟶* (f' ∘ g)
∘-cong-left' g done = done
∘-cong-left' g (step r rs) = ⟶*-trans (⟶-cong-∘-left g r) (∘-cong-left' g rs)
  where
    -- Single step congruence via parallel reduction
    ⟶-cong-∘-left : ∀ {A B C} {f f' : Term B C} (g : Term A B) →
                    f ⟶ f' → (f ∘ g) ⟶* (f' ∘ g)
    ⟶-cong-∘-left g r = ⟹→⟶* (⟹-∘ (⟶→⟹ r) (⟹-refl g))

-- Congruence: if g ⟶* g', then f ∘ g ⟶* f ∘ g'
∘-cong-right' : ∀ {A B C} (f : Term B C) {g g' : Term A B} →
                g ⟶* g' → (f ∘ g) ⟶* (f ∘ g')
∘-cong-right' f done = done
∘-cong-right' f (step r rs) = ⟶*-trans (⟹→⟶* (⟹-∘ (⟹-refl f) (⟶→⟹ r))) (∘-cong-right' f rs)

------------------------------------------------------------------------
-- Proof of refold-idem-id
------------------------------------------------------------------------

-- The TermF functor is: (K TyFuncCode) ⊕ rest
-- For the id case (position 0), we inject via inl into the first component.

-- Step 1: fmap of first component of TermF is fmap (K TyFuncCode) = id
fmap-K-is-id : ∀ {X A B} (f : Term A B) → fmap (K X) f ≡ id
fmap-K-is-id f = refl

-- Step 2: Show that fmap TermF (cata TermF In) ∘ inl ⟶* inl
-- Since TermF = (K TyFuncCode) ⊕ rest, we have:
--   fmap TermF f = [ inl ∘ fmap (K TyFuncCode) f , inr ∘ fmap rest f ]
--                = [ inl ∘ id , inr ∘ fmap rest f ]
-- So fmap TermF f ∘ inl ⟶ inl ∘ id (by case-inl)
-- And inl ∘ id ⟶ inl (by id-right)

-- The rest of TermF after K TyFuncCode (positions 1-14)
TermF-rest : Func
TermF-rest = (Id ⊗ Id)                                   -- 1: f ∘ g
           ⊕ (K TyFuncCode ⊗ K TyFuncCode)              -- 2: fst A B
           ⊕ (K TyFuncCode ⊗ K TyFuncCode)              -- 3: snd A B
           ⊕ (Id ⊗ Id)                                   -- 4: ⟨f, g⟩
           ⊕ (K TyFuncCode ⊗ K TyFuncCode)              -- 5: inl A B
           ⊕ (K TyFuncCode ⊗ K TyFuncCode)              -- 6: inr A B
           ⊕ (Id ⊗ Id)                                   -- 7: [f, g]
           ⊕ (K TyFuncCode)                              -- 8: terminal A
           ⊕ (K TyFuncCode)                              -- 9: initial A
           ⊕ (K TyFuncCode)                              -- 10: In F
           ⊕ (K TyFuncCode)                              -- 11: Out F
           ⊕ (K TyFuncCode ⊗ Id)                        -- 12: cata F alg
           ⊕ ((K TyFuncCode ⊗ K TyFuncCode) ⊗ (K TyFuncCode ⊗ Id))  -- 13: curry
           ⊕ (K TyFuncCode ⊗ K TyFuncCode)              -- 14: apply

-- TermF = K TyFuncCode ⊕ TermF-rest
TermF-decomp : TermF ≡ (K TyFuncCode ⊕ TermF-rest)
TermF-decomp = refl

-- Key lemma: fmap TermF f ∘ inl ⟶* inl
fmap-TermF-inl : ∀ {A B} (f : Term A B) →
                 (fmap TermF f ∘ inl) ⟶* inl
fmap-TermF-inl f =
  -- fmap TermF f = fmap (K TyFuncCode ⊕ TermF-rest) f
  --              = [ inl ∘ fmap (K TyFuncCode) f , inr ∘ fmap TermF-rest f ]
  --              = [ inl ∘ id , inr ∘ fmap TermF-rest f ]
  -- So [ inl ∘ id , ... ] ∘ inl ⟶ inl ∘ id by case-inl
  -- And inl ∘ id ⟶ inl by id-right
  step case-inl (step id-right done)

-- The main proof for id case
--
-- Proof outline:
-- 1. encode (id {A}) = In ∘ inl ∘ ⌜A⌝Ty (by definition)
-- 2. cata TermF In ∘ (In ∘ (inl ∘ ⌜A⌝Ty))
--    ⟶* (In ∘ fmap TermF (cata TermF In)) ∘ (inl ∘ ⌜A⌝Ty)  (by cata-β-right)
-- 3. ⟶ ((In ∘ fmap TermF ...) ∘ inl) ∘ ⌜A⌝Ty  (by assoc-l)
-- 4. Now fmap TermF f ∘ inl = [inl ∘ id, ...] ∘ inl ⟶ inl ∘ id ⟶ inl
--    So ((In ∘ fmap ...) ∘ inl) ⟶* (In ∘ inl) using congruence
-- 5. (In ∘ inl) ∘ ⌜A⌝Ty = encode (id {A})

refold-idem-id : ∀ {A} → (cata TermF In ∘ encode (id {A})) ⟶* encode (id {A})
refold-idem-id {A} = ⟶*-trans step1 (⟶*-trans step2 step3)
  where
    -- Step 1: Apply cata-β-right
    step1 : (cata TermF In ∘ (In ∘ (inl ∘ ⌜ A ⌝Ty))) ⟶*
            ((In ∘ fmap TermF (cata TermF In)) ∘ (inl ∘ ⌜ A ⌝Ty))
    step1 = cata-β-right

    -- Step 2: Apply assoc-l to get inl next to fmap
    step2 : ((In ∘ fmap TermF (cata TermF In)) ∘ (inl ∘ ⌜ A ⌝Ty)) ⟶*
            (((In ∘ fmap TermF (cata TermF In)) ∘ inl) ∘ ⌜ A ⌝Ty)
    step2 = step assoc-l done

    -- Step 3: Reduce the inner part and reassociate
    -- We need: ((In ∘ fmap ...) ∘ inl) ∘ ⌜A⌝Ty ⟶* (In ∘ inl) ∘ ⌜A⌝Ty
    --        = In ∘ (inl ∘ ⌜A⌝Ty) = encode (id {A})
    --
    -- The inner reduction: (In ∘ fmap TermF (cata TermF In)) ∘ inl ⟶* In ∘ inl
    -- uses case-inl: fmap TermF f ∘ inl = [inl ∘ id, ...] ∘ inl ⟶ inl ∘ id
    -- and id-right: inl ∘ id ⟶ inl

    -- Direct proof using parallel reduction:
    -- (In ∘ [inl ∘ id, ...]) ∘ inl
    -- We observe that [inl ∘ id, ...] ∘ inl ⟶ inl ∘ id by case-inl
    -- So by congruence: (In ∘ ([inl ∘ id, ...] ∘ inl)) ⟶* (In ∘ (inl ∘ id))
    -- But we have left-associated form!
    --
    -- Key insight: use assoc-l to convert, then reduce, then assoc-l back
    -- In ∘ (fmap... ∘ inl) ⟶ (In ∘ fmap...) ∘ inl  [wrong direction for assoc-l]
    --
    -- Alternative: use parallel reduction which can do multiple things at once

    inner-step : ((In ∘ fmap TermF (cata TermF In)) ∘ inl) ⟶* (In ∘ inl)
    inner-step =
      -- We have: (In ∘ fmap TermF f) ∘ inl, which is left-associated
      -- Step 1: Use assoc-r to get In ∘ (fmap TermF f ∘ inl)
      -- Step 2: Reduce inner: fmap TermF f ∘ inl ⟶ inl ∘ id ⟶ inl
      -- Step 3: Result is In ∘ inl
      ⟶*-trans
        (step assoc-r done)  -- (In ∘ fmap...) ∘ inl ⟶ In ∘ (fmap... ∘ inl)
        (∘-cong-right' In (fmap-TermF-inl (cata TermF In)))  -- In ∘ (fmap ∘ inl) ⟶* In ∘ inl

    step3 : (((In ∘ fmap TermF (cata TermF In)) ∘ inl) ∘ ⌜ A ⌝Ty) ⟶*
            (In ∘ (inl ∘ ⌜ A ⌝Ty))
    step3 = ⟶*-trans
              (∘-cong-left' (⌜ A ⌝Ty) inner-step)  -- reduce inner part
              (step assoc-r done)                   -- reassociate: (In ∘ inl) ∘ ⌜A⌝Ty ⟶ In ∘ (inl ∘ ⌜A⌝Ty)

------------------------------------------------------------------------
-- Helper lemmas for injection chain reductions
------------------------------------------------------------------------

-- For each position N, we need: fmap TermF f ∘ (inr^N ∘ inl) ⟶* (inr^N ∘ inl) ∘ fmap_N f
-- where fmap_N is the fmap at position N.
--
-- For K-based positions: fmap (K X) f = id, so the whole thing reduces to inr^N ∘ inl
-- For Id-based positions: we get recursive applications

-- Nested functors for each depth level
TermF-1 : Func  -- After 1 inr (positions 1-14)
TermF-1 = (Id ⊗ Id)                                   -- 1: comp
        ⊕ (K TyFuncCode ⊗ K TyFuncCode)              -- 2: fst
        ⊕ (K TyFuncCode ⊗ K TyFuncCode)              -- 3: snd
        ⊕ (Id ⊗ Id)                                   -- 4: pair
        ⊕ (K TyFuncCode ⊗ K TyFuncCode)              -- 5: inl
        ⊕ (K TyFuncCode ⊗ K TyFuncCode)              -- 6: inr
        ⊕ (Id ⊗ Id)                                   -- 7: case
        ⊕ (K TyFuncCode)                              -- 8: terminal
        ⊕ (K TyFuncCode)                              -- 9: initial
        ⊕ (K TyFuncCode)                              -- 10: In
        ⊕ (K TyFuncCode)                              -- 11: Out
        ⊕ (K TyFuncCode ⊗ Id)                        -- 12: cata
        ⊕ ((K TyFuncCode ⊗ K TyFuncCode) ⊗ (K TyFuncCode ⊗ Id))  -- 13: curry
        ⊕ (K TyFuncCode ⊗ K TyFuncCode)              -- 14: apply

TermF-2 : Func  -- After 2 inrs (positions 2-14)
TermF-2 = (K TyFuncCode ⊗ K TyFuncCode)              -- 2: fst
        ⊕ (K TyFuncCode ⊗ K TyFuncCode)              -- 3: snd
        ⊕ (Id ⊗ Id)                                   -- 4: pair
        ⊕ (K TyFuncCode ⊗ K TyFuncCode)              -- 5: inl
        ⊕ (K TyFuncCode ⊗ K TyFuncCode)              -- 6: inr
        ⊕ (Id ⊗ Id)                                   -- 7: case
        ⊕ (K TyFuncCode)                              -- 8: terminal
        ⊕ (K TyFuncCode)                              -- 9: initial
        ⊕ (K TyFuncCode)                              -- 10: In
        ⊕ (K TyFuncCode)                              -- 11: Out
        ⊕ (K TyFuncCode ⊗ Id)                        -- 12: cata
        ⊕ ((K TyFuncCode ⊗ K TyFuncCode) ⊗ (K TyFuncCode ⊗ Id))  -- 13: curry
        ⊕ (K TyFuncCode ⊗ K TyFuncCode)              -- 14: apply

TermF-3 : Func  -- After 3 inrs (positions 3-14)
TermF-3 = (K TyFuncCode ⊗ K TyFuncCode)              -- 3: snd
        ⊕ (Id ⊗ Id)                                   -- 4: pair
        ⊕ (K TyFuncCode ⊗ K TyFuncCode)              -- 5: inl
        ⊕ (K TyFuncCode ⊗ K TyFuncCode)              -- 6: inr
        ⊕ (Id ⊗ Id)                                   -- 7: case
        ⊕ (K TyFuncCode)                              -- 8: terminal
        ⊕ (K TyFuncCode)                              -- 9: initial
        ⊕ (K TyFuncCode)                              -- 10: In
        ⊕ (K TyFuncCode)                              -- 11: Out
        ⊕ (K TyFuncCode ⊗ Id)                        -- 12: cata
        ⊕ ((K TyFuncCode ⊗ K TyFuncCode) ⊗ (K TyFuncCode ⊗ Id))  -- 13: curry
        ⊕ (K TyFuncCode ⊗ K TyFuncCode)              -- 14: apply

TermF-4 : Func  -- After 4 inrs (positions 4-14)
TermF-4 = (Id ⊗ Id)                                   -- 4: pair
        ⊕ (K TyFuncCode ⊗ K TyFuncCode)              -- 5: inl
        ⊕ (K TyFuncCode ⊗ K TyFuncCode)              -- 6: inr
        ⊕ (Id ⊗ Id)                                   -- 7: case
        ⊕ (K TyFuncCode)                              -- 8: terminal
        ⊕ (K TyFuncCode)                              -- 9: initial
        ⊕ (K TyFuncCode)                              -- 10: In
        ⊕ (K TyFuncCode)                              -- 11: Out
        ⊕ (K TyFuncCode ⊗ Id)                        -- 12: cata
        ⊕ ((K TyFuncCode ⊗ K TyFuncCode) ⊗ (K TyFuncCode ⊗ Id))  -- 13: curry
        ⊕ (K TyFuncCode ⊗ K TyFuncCode)              -- 14: apply

TermF-5 : Func  -- After 5 inrs (positions 5-14)
TermF-5 = (K TyFuncCode ⊗ K TyFuncCode)              -- 5: inl
        ⊕ (K TyFuncCode ⊗ K TyFuncCode)              -- 6: inr
        ⊕ (Id ⊗ Id)                                   -- 7: case
        ⊕ (K TyFuncCode)                              -- 8: terminal
        ⊕ (K TyFuncCode)                              -- 9: initial
        ⊕ (K TyFuncCode)                              -- 10: In
        ⊕ (K TyFuncCode)                              -- 11: Out
        ⊕ (K TyFuncCode ⊗ Id)                        -- 12: cata
        ⊕ ((K TyFuncCode ⊗ K TyFuncCode) ⊗ (K TyFuncCode ⊗ Id))  -- 13: curry
        ⊕ (K TyFuncCode ⊗ K TyFuncCode)              -- 14: apply

TermF-6 : Func  -- After 6 inrs (positions 6-14)
TermF-6 = (K TyFuncCode ⊗ K TyFuncCode)              -- 6: inr
        ⊕ (Id ⊗ Id)                                   -- 7: case
        ⊕ (K TyFuncCode)                              -- 8: terminal
        ⊕ (K TyFuncCode)                              -- 9: initial
        ⊕ (K TyFuncCode)                              -- 10: In
        ⊕ (K TyFuncCode)                              -- 11: Out
        ⊕ (K TyFuncCode ⊗ Id)                        -- 12: cata
        ⊕ ((K TyFuncCode ⊗ K TyFuncCode) ⊗ (K TyFuncCode ⊗ Id))  -- 13: curry
        ⊕ (K TyFuncCode ⊗ K TyFuncCode)              -- 14: apply

TermF-7 : Func  -- After 7 inrs (positions 7-14)
TermF-7 = (Id ⊗ Id)                                   -- 7: case
        ⊕ (K TyFuncCode)                              -- 8: terminal
        ⊕ (K TyFuncCode)                              -- 9: initial
        ⊕ (K TyFuncCode)                              -- 10: In
        ⊕ (K TyFuncCode)                              -- 11: Out
        ⊕ (K TyFuncCode ⊗ Id)                        -- 12: cata
        ⊕ ((K TyFuncCode ⊗ K TyFuncCode) ⊗ (K TyFuncCode ⊗ Id))  -- 13: curry
        ⊕ (K TyFuncCode ⊗ K TyFuncCode)              -- 14: apply

TermF-8 : Func  -- After 8 inrs (positions 8-14)
TermF-8 = (K TyFuncCode)                              -- 8: terminal
        ⊕ (K TyFuncCode)                              -- 9: initial
        ⊕ (K TyFuncCode)                              -- 10: In
        ⊕ (K TyFuncCode)                              -- 11: Out
        ⊕ (K TyFuncCode ⊗ Id)                        -- 12: cata
        ⊕ ((K TyFuncCode ⊗ K TyFuncCode) ⊗ (K TyFuncCode ⊗ Id))  -- 13: curry
        ⊕ (K TyFuncCode ⊗ K TyFuncCode)              -- 14: apply

TermF-9 : Func  -- After 9 inrs (positions 9-14)
TermF-9 = (K TyFuncCode)                              -- 9: initial
        ⊕ (K TyFuncCode)                              -- 10: In
        ⊕ (K TyFuncCode)                              -- 11: Out
        ⊕ (K TyFuncCode ⊗ Id)                        -- 12: cata
        ⊕ ((K TyFuncCode ⊗ K TyFuncCode) ⊗ (K TyFuncCode ⊗ Id))  -- 13: curry
        ⊕ (K TyFuncCode ⊗ K TyFuncCode)              -- 14: apply

TermF-10 : Func  -- After 10 inrs (positions 10-14)
TermF-10 = (K TyFuncCode)                             -- 10: In
         ⊕ (K TyFuncCode)                             -- 11: Out
         ⊕ (K TyFuncCode ⊗ Id)                       -- 12: cata
         ⊕ ((K TyFuncCode ⊗ K TyFuncCode) ⊗ (K TyFuncCode ⊗ Id))  -- 13: curry
         ⊕ (K TyFuncCode ⊗ K TyFuncCode)             -- 14: apply

TermF-11 : Func  -- After 11 inrs (positions 11-14)
TermF-11 = (K TyFuncCode)                             -- 11: Out
         ⊕ (K TyFuncCode ⊗ Id)                       -- 12: cata
         ⊕ ((K TyFuncCode ⊗ K TyFuncCode) ⊗ (K TyFuncCode ⊗ Id))  -- 13: curry
         ⊕ (K TyFuncCode ⊗ K TyFuncCode)             -- 14: apply

TermF-12 : Func  -- After 12 inrs (positions 12-14)
TermF-12 = (K TyFuncCode ⊗ Id)                       -- 12: cata
         ⊕ ((K TyFuncCode ⊗ K TyFuncCode) ⊗ (K TyFuncCode ⊗ Id))  -- 13: curry
         ⊕ (K TyFuncCode ⊗ K TyFuncCode)             -- 14: apply

TermF-13 : Func  -- After 13 inrs (positions 13-14)
TermF-13 = ((K TyFuncCode ⊗ K TyFuncCode) ⊗ (K TyFuncCode ⊗ Id))  -- 13: curry
         ⊕ (K TyFuncCode ⊗ K TyFuncCode)             -- 14: apply

TermF-14 : Func  -- After 14 inrs (position 14 only)
TermF-14 = (K TyFuncCode ⊗ K TyFuncCode)             -- 14: apply

-- fmap distributes through inr: fmap (F ⊕ G) f ∘ inr ⟶ inr ∘ fmap G f
fmap-through-inr : ∀ {A B} F G (f : Term A B) →
                   (fmap (F ⊕ G) f ∘ inr) ⟶* (inr ∘ fmap G f)
fmap-through-inr F G f = step case-inr done

-- K-pair reduces to identity via eta-pair
-- fmap (K X ⊗ K Y) f = ⟨ id ∘ fst , id ∘ snd ⟩ ⟶* id
fmap-KK-id : ∀ {A B} X Y (f : Term A B) → fmap (K X ⊗ K Y) f ⟶* id
fmap-KK-id X Y f =
  -- fmap (K X ⊗ K Y) f = ⟨ fmap (K X) f ∘ fst , fmap (K Y) f ∘ snd ⟩
  --                    = ⟨ id ∘ fst , id ∘ snd ⟩
  -- ⟶ ⟨ fst , snd ⟩ by id-left (twice)
  -- ⟶ id by eta-pair
  ⟶*-trans (⟹→⟶* (⟹-pair (⟹-id-l ⟹-fst) (⟹-id-l ⟹-snd))) (step eta-pair done)

-- Helper: chain multiple inr reductions
-- For each level, we reduce fmap F f ∘ inr to inr ∘ fmap G f
fmap-TermF-inr : ∀ {A B} (f : Term A B) →
                 (fmap TermF f ∘ inr) ⟶* (inr ∘ fmap TermF-1 f)
fmap-TermF-inr f = fmap-through-inr (K TyFuncCode) TermF-1 f

fmap-1-inr : ∀ {A B} (f : Term A B) →
             (fmap TermF-1 f ∘ inr) ⟶* (inr ∘ fmap TermF-2 f)
fmap-1-inr f = fmap-through-inr (Id ⊗ Id) TermF-2 f

fmap-2-inr : ∀ {A B} (f : Term A B) →
             (fmap TermF-2 f ∘ inr) ⟶* (inr ∘ fmap TermF-3 f)
fmap-2-inr f = fmap-through-inr (K TyFuncCode ⊗ K TyFuncCode) TermF-3 f

fmap-3-inr : ∀ {A B} (f : Term A B) →
             (fmap TermF-3 f ∘ inr) ⟶* (inr ∘ fmap TermF-4 f)
fmap-3-inr f = fmap-through-inr (K TyFuncCode ⊗ K TyFuncCode) TermF-4 f

fmap-4-inr : ∀ {A B} (f : Term A B) →
             (fmap TermF-4 f ∘ inr) ⟶* (inr ∘ fmap TermF-5 f)
fmap-4-inr f = fmap-through-inr (Id ⊗ Id) TermF-5 f

fmap-5-inr : ∀ {A B} (f : Term A B) →
             (fmap TermF-5 f ∘ inr) ⟶* (inr ∘ fmap TermF-6 f)
fmap-5-inr f = fmap-through-inr (K TyFuncCode ⊗ K TyFuncCode) TermF-6 f

fmap-6-inr : ∀ {A B} (f : Term A B) →
             (fmap TermF-6 f ∘ inr) ⟶* (inr ∘ fmap TermF-7 f)
fmap-6-inr f = fmap-through-inr (K TyFuncCode ⊗ K TyFuncCode) TermF-7 f

fmap-7-inr : ∀ {A B} (f : Term A B) →
             (fmap TermF-7 f ∘ inr) ⟶* (inr ∘ fmap TermF-8 f)
fmap-7-inr f = fmap-through-inr (Id ⊗ Id) TermF-8 f

fmap-8-inr : ∀ {A B} (f : Term A B) →
             (fmap TermF-8 f ∘ inr) ⟶* (inr ∘ fmap TermF-9 f)
fmap-8-inr f = fmap-through-inr (K TyFuncCode) TermF-9 f

fmap-9-inr : ∀ {A B} (f : Term A B) →
             (fmap TermF-9 f ∘ inr) ⟶* (inr ∘ fmap TermF-10 f)
fmap-9-inr f = fmap-through-inr (K TyFuncCode) TermF-10 f

fmap-10-inr : ∀ {A B} (f : Term A B) →
              (fmap TermF-10 f ∘ inr) ⟶* (inr ∘ fmap TermF-11 f)
fmap-10-inr f = fmap-through-inr (K TyFuncCode) TermF-11 f

fmap-11-inr : ∀ {A B} (f : Term A B) →
              (fmap TermF-11 f ∘ inr) ⟶* (inr ∘ fmap TermF-12 f)
fmap-11-inr f = fmap-through-inr (K TyFuncCode) TermF-12 f

fmap-12-inr : ∀ {A B} (f : Term A B) →
              (fmap TermF-12 f ∘ inr) ⟶* (inr ∘ fmap TermF-13 f)
fmap-12-inr f = fmap-through-inr (K TyFuncCode ⊗ Id) TermF-13 f

fmap-13-inr : ∀ {A B} (f : Term A B) →
              (fmap TermF-13 f ∘ inr) ⟶* (inr ∘ fmap TermF-14 f)
fmap-13-inr f = fmap-through-inr ((K TyFuncCode ⊗ K TyFuncCode) ⊗ (K TyFuncCode ⊗ Id)) TermF-14 f

-- fmap distributes through inl: fmap (F ⊕ G) f ∘ inl ⟶ inl ∘ fmap F f
fmap-sum-inl : ∀ {A B} F G (f : Term A B) →
               (fmap (F ⊕ G) f ∘ inl) ⟶* (inl ∘ fmap F f)
fmap-sum-inl F G f = step case-inl done

-- Specific inl lemmas for each position in TermF
-- Position 2 (fst): after 2 inrs, inl into K TyFuncCode ⊗ K TyFuncCode
fmap-2-inl : ∀ {A B} (f : Term A B) →
             (fmap TermF-2 f ∘ inl) ⟶* (inl ∘ fmap (K TyFuncCode ⊗ K TyFuncCode) f)
fmap-2-inl f = fmap-sum-inl (K TyFuncCode ⊗ K TyFuncCode) TermF-3 f

-- Position 3 (snd): after 3 inrs, inl into K TyFuncCode ⊗ K TyFuncCode
fmap-3-inl : ∀ {A B} (f : Term A B) →
             (fmap TermF-3 f ∘ inl) ⟶* (inl ∘ fmap (K TyFuncCode ⊗ K TyFuncCode) f)
fmap-3-inl f = fmap-sum-inl (K TyFuncCode ⊗ K TyFuncCode) TermF-4 f

-- Position 5 (inl): after 5 inrs, inl into K TyFuncCode ⊗ K TyFuncCode
fmap-5-inl : ∀ {A B} (f : Term A B) →
             (fmap TermF-5 f ∘ inl) ⟶* (inl ∘ fmap (K TyFuncCode ⊗ K TyFuncCode) f)
fmap-5-inl f = fmap-sum-inl (K TyFuncCode ⊗ K TyFuncCode) TermF-6 f

-- Position 6 (inr): after 6 inrs, inl into K TyFuncCode ⊗ K TyFuncCode
fmap-6-inl : ∀ {A B} (f : Term A B) →
             (fmap TermF-6 f ∘ inl) ⟶* (inl ∘ fmap (K TyFuncCode ⊗ K TyFuncCode) f)
fmap-6-inl f = fmap-sum-inl (K TyFuncCode ⊗ K TyFuncCode) TermF-7 f

-- Position 8 (terminal): after 8 inrs, inl into K TyFuncCode
fmap-8-inl : ∀ {A B} (f : Term A B) →
             (fmap TermF-8 f ∘ inl) ⟶* (inl ∘ fmap (K TyFuncCode) f)
fmap-8-inl f = fmap-sum-inl (K TyFuncCode) TermF-9 f

-- Position 9 (In): after 9 inrs, inl into K TyFuncCode
fmap-9-inl : ∀ {A B} (f : Term A B) →
             (fmap TermF-9 f ∘ inl) ⟶* (inl ∘ fmap (K TyFuncCode) f)
fmap-9-inl f = fmap-sum-inl (K TyFuncCode) TermF-10 f

-- Position 10 (Out): after 10 inrs, inl into K TyFuncCode
fmap-10-inl : ∀ {A B} (f : Term A B) →
              (fmap TermF-10 f ∘ inl) ⟶* (inl ∘ fmap (K TyFuncCode) f)
fmap-10-inl f = fmap-sum-inl (K TyFuncCode) TermF-11 f

-- Id⊗Id positions (for recursive cases):
-- Position 1 (comp): after 1 inr, inl into Id ⊗ Id
fmap-1-inl : ∀ {A B} (f : Term A B) →
             (fmap TermF-1 f ∘ inl) ⟶* (inl ∘ fmap (Id ⊗ Id) f)
fmap-1-inl f = fmap-sum-inl (Id ⊗ Id) TermF-2 f

-- Position 4 (pair): after 4 inrs, inl into Id ⊗ Id
fmap-4-inl : ∀ {A B} (f : Term A B) →
             (fmap TermF-4 f ∘ inl) ⟶* (inl ∘ fmap (Id ⊗ Id) f)
fmap-4-inl f = fmap-sum-inl (Id ⊗ Id) TermF-5 f

-- Position 7 (case): after 7 inrs, inl into Id ⊗ Id
fmap-7-inl : ∀ {A B} (f : Term A B) →
             (fmap TermF-7 f ∘ inl) ⟶* (inl ∘ fmap (Id ⊗ Id) f)
fmap-7-inl f = fmap-sum-inl (Id ⊗ Id) TermF-8 f

-- Position 11 (Out): after 11 inrs, inl into K TyFuncCode
fmap-11-inl : ∀ {A B} (f : Term A B) →
              (fmap TermF-11 f ∘ inl) ⟶* (inl ∘ fmap (K TyFuncCode) f)
fmap-11-inl f = fmap-sum-inl (K TyFuncCode) TermF-12 f

-- Position 12 (cata): after 12 inrs, inl into K TyFuncCode ⊗ Id
fmap-12-inl : ∀ {A B} (f : Term A B) →
              (fmap TermF-12 f ∘ inl) ⟶* (inl ∘ fmap (K TyFuncCode ⊗ Id) f)
fmap-12-inl f = fmap-sum-inl (K TyFuncCode ⊗ Id) TermF-13 f

-- Position 13 (curry): after 13 inrs, inl into curry's type
fmap-13-inl : ∀ {A B} (f : Term A B) →
              (fmap TermF-13 f ∘ inl) ⟶* (inl ∘ fmap ((K TyFuncCode ⊗ K TyFuncCode) ⊗ (K TyFuncCode ⊗ Id)) f)
fmap-13-inl f = fmap-sum-inl ((K TyFuncCode ⊗ K TyFuncCode) ⊗ (K TyFuncCode ⊗ Id)) TermF-14 f

-- Position 14 (apply): the terminal position - no inl needed

------------------------------------------------------------------------
-- Congruence for pair: if a ⟶* a' and b ⟶* b', then ⟨a,b⟩ ⟶* ⟨a',b'⟩
------------------------------------------------------------------------

⟨⟩-cong : ∀ {A B C} {f f' : Term C A} {g g' : Term C B} →
          f ⟶* f' → g ⟶* g' → ⟨ f , g ⟩ ⟶* ⟨ f' , g' ⟩
⟨⟩-cong done done = done
⟨⟩-cong done (step q qs) = ⟶*-trans (⟹→⟶* (⟹-pair (⟹-refl _) (⟶→⟹ q))) (⟨⟩-cong done qs)
⟨⟩-cong (step p ps) qs = ⟶*-trans (⟹→⟶* (⟹-pair (⟶→⟹ p) (⟹-refl _))) (⟨⟩-cong ps qs)

------------------------------------------------------------------------
-- The 11 refold-idem proofs
------------------------------------------------------------------------

-- The proofs follow the same pattern as refold-idem-id:
-- 1. Apply cata-β-right to unfold the cata
-- 2. Use assoc-r/assoc-l and congruence to push through injection chains
-- 3. For K-based positions: fmap reduces to id, payload passes through
-- 4. For Id-based positions: need mutual recursion with refold-idempotent
--
-- The refold-idem-id case is done above as a template.
-- The remaining 11 cases are proof obligations - they follow the same
-- mechanical pattern but with varying injection depths.

-- K-based positions (non-recursive):
-- - fst (pos 2): K ⊗ K
-- - snd (pos 3): K ⊗ K
-- - inl (pos 5): K ⊗ K
-- - inr (pos 6): K ⊗ K
-- - terminal (pos 8): K
-- - In (pos 9): K
-- - Out (pos 10): K
--
-- Id-based positions (recursive):
-- - comp (pos 1): Id ⊗ Id
-- - pair (pos 4): Id ⊗ Id
-- - case (pos 7): Id ⊗ Id
-- - cata (pos 11): K ⊗ Id

------------------------------------------------------------------------
-- K-based refold-idem proofs (non-recursive)
------------------------------------------------------------------------

-- General pattern for K-based proofs:
-- 1. cata-β-right to unfold
-- 2. Navigate through injection chain with assoc and case reductions
-- 3. K functor gives fmap K f = id, so inl ∘ id ⟶ inl
-- 4. Reassemble
--
-- The fst case (position 2) demonstrates this pattern:
-- encode fst = In ∘ inr ∘ inr ∘ inl ∘ ⟨ ⌜A⌝, ⌜B⌝ ⟩
--
-- After cata-β-right:
--   (In ∘ fmap TermF (cata TermF In)) ∘ (inr ∘ inr ∘ inl ∘ ⟨...⟩)
-- Using assoc-r:
--   In ∘ (fmap ∘ (inr ∘ inr ∘ inl ∘ ⟨...⟩))
-- Navigate through injection chain:
--   fmap TermF f ∘ inr ⟶ inr ∘ fmap TermF-1 f (by case-inr)
--   fmap TermF-1 f ∘ inr ⟶ inr ∘ fmap TermF-2 f (by case-inr)
--   fmap TermF-2 f ∘ inl ⟶ inl ∘ fmap (K⊗K) f (by case-inl)
--   fmap (K⊗K) f ⟶* id (by eta-pair since fmap K _ = id)
-- Final result:
--   In ∘ (inr ∘ (inr ∘ (inl ∘ ⟨...⟩))) = encode fst
--
-- All K-based cases follow this pattern with varying inr depths.

-- The remaining K-based cases:
-- 1. cata-β-right to unfold
-- 2. Navigate through injection chain with assoc and case reductions
-- 3. K functor gives fmap K f = id, so fmap reduces away
-- 4. Reassemble
--
-- Each case just has more inrs to navigate. The proofs are mechanical but long.
-- These are proof obligations - the fst case above demonstrates the pattern.

-- refold-idem-fst: position 2 (2 inrs before inl)
-- encode fst = In ∘ inr^2 ∘ inl ∘ ⟨ ⌜A⌝Ty, ⌜B⌝Ty ⟩
-- Payload functor: K TyFuncCode ⊗ K TyFuncCode
refold-idem-fst : ∀ {A B} → (cata TermF In ∘ encode (fst {A} {B})) ⟶* encode (fst {A} {B})
refold-idem-fst {A} {B} = ⟶*-trans step1 step2
  where
    payload : Term Unit (TyFuncCode * TyFuncCode)
    payload = ⟨ ⌜ A ⌝Ty , ⌜ B ⌝Ty ⟩

    f : Term TermCode' TermCode'
    f = cata TermF In

    step1 = cata-β-right

    r0 = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' _ (fmap-TermF-inr f)) (step assoc-r done))
    r1 = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' _ (fmap-1-inr f)) (step assoc-r done))

    -- Final step: fmap TermF-2 f ∘ (inl ∘ payload) ⟶* inl ∘ payload
    -- fmap TermF-2 f ∘ inl ⟶ inl ∘ fmap (K⊗K) f
    -- fmap (K⊗K) f ∘ payload ⟶* id ∘ payload ⟶ payload
    r2 : (fmap TermF-2 f ∘ (inl ∘ payload)) ⟶* (inl ∘ payload)
    r2 = ⟶*-trans (step assoc-l done)
           (⟶*-trans (∘-cong-left' payload (fmap-2-inl f))
             (⟶*-trans (step assoc-r done)
               (⟶*-trans (∘-cong-right' inl
                 (⟶*-trans (∘-cong-left' payload (fmap-KK-id TyFuncCode TyFuncCode f))
                   (step id-left done)))
                 done)))

    reduce-chain =
      ⟶*-trans r0 (∘-cong-right' inr
        (⟶*-trans r1 (∘-cong-right' inr r2)))

    step2 = ⟶*-trans (step assoc-r done) (∘-cong-right' In reduce-chain)

-- refold-idem-snd: position 3 (3 inrs before inl)
-- encode snd = In ∘ inr^3 ∘ inl ∘ ⟨ ⌜A⌝Ty, ⌜B⌝Ty ⟩
-- Payload functor: K TyFuncCode ⊗ K TyFuncCode
refold-idem-snd : ∀ {A B} → (cata TermF In ∘ encode (snd {A} {B})) ⟶* encode (snd {A} {B})
refold-idem-snd {A} {B} = ⟶*-trans step1 step2
  where
    payload : Term Unit (TyFuncCode * TyFuncCode)
    payload = ⟨ ⌜ A ⌝Ty , ⌜ B ⌝Ty ⟩

    f : Term TermCode' TermCode'
    f = cata TermF In

    step1 = cata-β-right

    r0 = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' _ (fmap-TermF-inr f)) (step assoc-r done))
    r1 = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' _ (fmap-1-inr f)) (step assoc-r done))
    r2 = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' _ (fmap-2-inr f)) (step assoc-r done))

    r3 : (fmap TermF-3 f ∘ (inl ∘ payload)) ⟶* (inl ∘ payload)
    r3 = ⟶*-trans (step assoc-l done)
           (⟶*-trans (∘-cong-left' payload (fmap-3-inl f))
             (⟶*-trans (step assoc-r done)
               (⟶*-trans (∘-cong-right' inl
                 (⟶*-trans (∘-cong-left' payload (fmap-KK-id TyFuncCode TyFuncCode f))
                   (step id-left done)))
                 done)))

    reduce-chain =
      ⟶*-trans r0 (∘-cong-right' inr
        (⟶*-trans r1 (∘-cong-right' inr
          (⟶*-trans r2 (∘-cong-right' inr r3)))))

    step2 = ⟶*-trans (step assoc-r done) (∘-cong-right' In reduce-chain)

-- refold-idem-inl: position 5 (5 inrs before inl)
-- encode inl = In ∘ inr^5 ∘ inl ∘ ⟨ ⌜A⌝Ty, ⌜B⌝Ty ⟩
-- Payload functor: K TyFuncCode ⊗ K TyFuncCode
refold-idem-inl : ∀ {A B} → (cata TermF In ∘ encode (inl {A} {B})) ⟶* encode (inl {A} {B})
refold-idem-inl {A} {B} = ⟶*-trans step1 step2
  where
    payload : Term Unit (TyFuncCode * TyFuncCode)
    payload = ⟨ ⌜ A ⌝Ty , ⌜ B ⌝Ty ⟩

    f : Term TermCode' TermCode'
    f = cata TermF In

    step1 = cata-β-right

    r0 = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' _ (fmap-TermF-inr f)) (step assoc-r done))
    r1 = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' _ (fmap-1-inr f)) (step assoc-r done))
    r2 = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' _ (fmap-2-inr f)) (step assoc-r done))
    r3 = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' _ (fmap-3-inr f)) (step assoc-r done))
    r4 = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' _ (fmap-4-inr f)) (step assoc-r done))

    r5 : (fmap TermF-5 f ∘ (inl ∘ payload)) ⟶* (inl ∘ payload)
    r5 = ⟶*-trans (step assoc-l done)
           (⟶*-trans (∘-cong-left' payload (fmap-5-inl f))
             (⟶*-trans (step assoc-r done)
               (⟶*-trans (∘-cong-right' inl
                 (⟶*-trans (∘-cong-left' payload (fmap-KK-id TyFuncCode TyFuncCode f))
                   (step id-left done)))
                 done)))

    reduce-chain =
      ⟶*-trans r0 (∘-cong-right' inr
        (⟶*-trans r1 (∘-cong-right' inr
          (⟶*-trans r2 (∘-cong-right' inr
            (⟶*-trans r3 (∘-cong-right' inr
              (⟶*-trans r4 (∘-cong-right' inr r5)))))))))

    step2 = ⟶*-trans (step assoc-r done) (∘-cong-right' In reduce-chain)

-- refold-idem-inr: position 6 (6 inrs before inl)
-- encode inr = In ∘ inr^6 ∘ inl ∘ ⟨ ⌜A⌝Ty, ⌜B⌝Ty ⟩
-- Payload functor: K TyFuncCode ⊗ K TyFuncCode
refold-idem-inr : ∀ {A B} → (cata TermF In ∘ encode (inr {A} {B})) ⟶* encode (inr {A} {B})
refold-idem-inr {A} {B} = ⟶*-trans step1 step2
  where
    payload : Term Unit (TyFuncCode * TyFuncCode)
    payload = ⟨ ⌜ A ⌝Ty , ⌜ B ⌝Ty ⟩

    f : Term TermCode' TermCode'
    f = cata TermF In

    step1 = cata-β-right

    r0 = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' _ (fmap-TermF-inr f)) (step assoc-r done))
    r1 = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' _ (fmap-1-inr f)) (step assoc-r done))
    r2 = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' _ (fmap-2-inr f)) (step assoc-r done))
    r3 = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' _ (fmap-3-inr f)) (step assoc-r done))
    r4 = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' _ (fmap-4-inr f)) (step assoc-r done))
    r5 = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' _ (fmap-5-inr f)) (step assoc-r done))

    r6 : (fmap TermF-6 f ∘ (inl ∘ payload)) ⟶* (inl ∘ payload)
    r6 = ⟶*-trans (step assoc-l done)
           (⟶*-trans (∘-cong-left' payload (fmap-6-inl f))
             (⟶*-trans (step assoc-r done)
               (⟶*-trans (∘-cong-right' inl
                 (⟶*-trans (∘-cong-left' payload (fmap-KK-id TyFuncCode TyFuncCode f))
                   (step id-left done)))
                 done)))

    reduce-chain =
      ⟶*-trans r0 (∘-cong-right' inr
        (⟶*-trans r1 (∘-cong-right' inr
          (⟶*-trans r2 (∘-cong-right' inr
            (⟶*-trans r3 (∘-cong-right' inr
              (⟶*-trans r4 (∘-cong-right' inr
                (⟶*-trans r5 (∘-cong-right' inr r6)))))))))))

    step2 = ⟶*-trans (step assoc-r done) (∘-cong-right' In reduce-chain)

-- refold-idem-terminal: position 8 (8 inrs before inl)
-- encode terminal = In ∘ inr^8 ∘ inl ∘ ⌜A⌝Ty
-- Payload functor: K TyFuncCode, so fmap (K _) f = id definitionally
refold-idem-terminal : ∀ {A} → (cata TermF In ∘ encode (terminal {A})) ⟶* encode (terminal {A})
refold-idem-terminal {A} = ⟶*-trans step1 step2
  where
    payload : Term Unit TyFuncCode
    payload = ⌜ A ⌝Ty

    f : Term TermCode' TermCode'
    f = cata TermF In

    -- Step 1: Unfold cata using cata-β-right
    step1 : (f ∘ (In ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inl ∘ payload))))))))))) ⟶*
            ((In ∘ fmap TermF f) ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inl ∘ payload))))))))))
    step1 = cata-β-right

    -- Navigation helper: (fmapN ∘ (inr ∘ rest)) ⟶* (inr ∘ (fmapN+1 ∘ rest))
    -- Pattern: assoc-l, reduce fmapN ∘ inr, assoc-r

    -- Chain through all 8 inrs, inlining the pattern
    r0 : (fmap TermF f ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inl ∘ payload)))))))))) ⟶*
         (inr ∘ (fmap TermF-1 f ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inl ∘ payload))))))))))
    r0 = ⟶*-trans (step assoc-l done)
           (⟶*-trans (∘-cong-left' _ (fmap-TermF-inr f))
             (step assoc-r done))

    r1 : (fmap TermF-1 f ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inl ∘ payload))))))))) ⟶*
         (inr ∘ (fmap TermF-2 f ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inl ∘ payload)))))))))
    r1 = ⟶*-trans (step assoc-l done)
           (⟶*-trans (∘-cong-left' _ (fmap-1-inr f))
             (step assoc-r done))

    r2 : (fmap TermF-2 f ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inl ∘ payload)))))))) ⟶*
         (inr ∘ (fmap TermF-3 f ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inl ∘ payload))))))))
    r2 = ⟶*-trans (step assoc-l done)
           (⟶*-trans (∘-cong-left' _ (fmap-2-inr f))
             (step assoc-r done))

    r3 : (fmap TermF-3 f ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inl ∘ payload))))))) ⟶*
         (inr ∘ (fmap TermF-4 f ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inl ∘ payload)))))))
    r3 = ⟶*-trans (step assoc-l done)
           (⟶*-trans (∘-cong-left' _ (fmap-3-inr f))
             (step assoc-r done))

    r4 : (fmap TermF-4 f ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inl ∘ payload)))))) ⟶*
         (inr ∘ (fmap TermF-5 f ∘ (inr ∘ (inr ∘ (inr ∘ (inl ∘ payload))))))
    r4 = ⟶*-trans (step assoc-l done)
           (⟶*-trans (∘-cong-left' _ (fmap-4-inr f))
             (step assoc-r done))

    r5 : (fmap TermF-5 f ∘ (inr ∘ (inr ∘ (inr ∘ (inl ∘ payload))))) ⟶*
         (inr ∘ (fmap TermF-6 f ∘ (inr ∘ (inr ∘ (inl ∘ payload)))))
    r5 = ⟶*-trans (step assoc-l done)
           (⟶*-trans (∘-cong-left' _ (fmap-5-inr f))
             (step assoc-r done))

    r6 : (fmap TermF-6 f ∘ (inr ∘ (inr ∘ (inl ∘ payload)))) ⟶*
         (inr ∘ (fmap TermF-7 f ∘ (inr ∘ (inl ∘ payload))))
    r6 = ⟶*-trans (step assoc-l done)
           (⟶*-trans (∘-cong-left' _ (fmap-6-inr f))
             (step assoc-r done))

    r7 : (fmap TermF-7 f ∘ (inr ∘ (inl ∘ payload))) ⟶*
         (inr ∘ (fmap TermF-8 f ∘ (inl ∘ payload)))
    r7 = ⟶*-trans (step assoc-l done)
           (⟶*-trans (∘-cong-left' _ (fmap-7-inr f))
             (step assoc-r done))

    -- Final step: fmap TermF-8 f ∘ inl ⟶* inl (since fmap (K _) f = id)
    r8 : (fmap TermF-8 f ∘ (inl ∘ payload)) ⟶* (inl ∘ payload)
    r8 = ⟶*-trans (step assoc-l done)
           (⟶*-trans (∘-cong-left' payload (fmap-8-inl f))
             (⟶*-trans (∘-cong-left' payload (step id-right done))
               done))

    -- Chain all together
    reduce-chain : (fmap TermF f ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inl ∘ payload)))))))))) ⟶*
                   (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inl ∘ payload)))))))))
    reduce-chain =
      ⟶*-trans r0 (∘-cong-right' inr
        (⟶*-trans r1 (∘-cong-right' inr
          (⟶*-trans r2 (∘-cong-right' inr
            (⟶*-trans r3 (∘-cong-right' inr
              (⟶*-trans r4 (∘-cong-right' inr
                (⟶*-trans r5 (∘-cong-right' inr
                  (⟶*-trans r6 (∘-cong-right' inr
                    (⟶*-trans r7 (∘-cong-right' inr r8)))))))))))))))

    step2 : ((In ∘ fmap TermF f) ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inl ∘ payload)))))))))) ⟶*
            (In ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inl ∘ payload))))))))))
    step2 = ⟶*-trans (step assoc-r done) (∘-cong-right' In reduce-chain)

-- refold-idem-initial: position 9 (9 inrs before inl)
-- encode initial = In ∘ inr^9 ∘ inl ∘ ⌜A⌝Ty
-- Payload functor: K TyFuncCode
refold-idem-initial : ∀ {A} → (cata TermF In ∘ encode (initial {A})) ⟶* encode (initial {A})
refold-idem-initial {A} = ⟶*-trans step1 step2
  where
    payload : Term Unit TyFuncCode
    payload = ⌜ A ⌝Ty

    f : Term TermCode' TermCode'
    f = cata TermF In

    step1 = cata-β-right

    r0 = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' _ (fmap-TermF-inr f)) (step assoc-r done))
    r1 = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' _ (fmap-1-inr f)) (step assoc-r done))
    r2 = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' _ (fmap-2-inr f)) (step assoc-r done))
    r3 = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' _ (fmap-3-inr f)) (step assoc-r done))
    r4 = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' _ (fmap-4-inr f)) (step assoc-r done))
    r5 = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' _ (fmap-5-inr f)) (step assoc-r done))
    r6 = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' _ (fmap-6-inr f)) (step assoc-r done))
    r7 = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' _ (fmap-7-inr f)) (step assoc-r done))
    r8 = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' _ (fmap-8-inr f)) (step assoc-r done))

    r9 : (fmap TermF-9 f ∘ (inl ∘ payload)) ⟶* (inl ∘ payload)
    r9 = ⟶*-trans (step assoc-l done)
           (⟶*-trans (∘-cong-left' payload (fmap-9-inl f))
             (⟶*-trans (∘-cong-left' payload (step id-right done))
               done))

    reduce-chain =
      ⟶*-trans r0 (∘-cong-right' inr
        (⟶*-trans r1 (∘-cong-right' inr
          (⟶*-trans r2 (∘-cong-right' inr
            (⟶*-trans r3 (∘-cong-right' inr
              (⟶*-trans r4 (∘-cong-right' inr
                (⟶*-trans r5 (∘-cong-right' inr
                  (⟶*-trans r6 (∘-cong-right' inr
                    (⟶*-trans r7 (∘-cong-right' inr
                      (⟶*-trans r8 (∘-cong-right' inr r9)))))))))))))))))

    step2 = ⟶*-trans (step assoc-r done) (∘-cong-right' In reduce-chain)

-- refold-idem-In: position 10 (10 inrs before inl)
-- encode In = In ∘ inr^10 ∘ inl ∘ ⌜F⌝Func
-- Payload functor: K TyFuncCode
refold-idem-In : ∀ {F} → (cata TermF In ∘ encode (In {F})) ⟶* encode (In {F})
refold-idem-In {F} = ⟶*-trans step1 step2
  where
    payload : Term Unit TyFuncCode
    payload = ⌜ F ⌝Func

    f : Term TermCode' TermCode'
    f = cata TermF In

    step1 = cata-β-right

    r0 = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' _ (fmap-TermF-inr f)) (step assoc-r done))
    r1 = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' _ (fmap-1-inr f)) (step assoc-r done))
    r2 = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' _ (fmap-2-inr f)) (step assoc-r done))
    r3 = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' _ (fmap-3-inr f)) (step assoc-r done))
    r4 = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' _ (fmap-4-inr f)) (step assoc-r done))
    r5 = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' _ (fmap-5-inr f)) (step assoc-r done))
    r6 = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' _ (fmap-6-inr f)) (step assoc-r done))
    r7 = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' _ (fmap-7-inr f)) (step assoc-r done))
    r8 = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' _ (fmap-8-inr f)) (step assoc-r done))
    r9 = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' _ (fmap-9-inr f)) (step assoc-r done))

    r10 : (fmap TermF-10 f ∘ (inl ∘ payload)) ⟶* (inl ∘ payload)
    r10 = ⟶*-trans (step assoc-l done)
           (⟶*-trans (∘-cong-left' payload (fmap-10-inl f))
             (⟶*-trans (∘-cong-left' payload (step id-right done))
               done))

    reduce-chain =
      ⟶*-trans r0 (∘-cong-right' inr
        (⟶*-trans r1 (∘-cong-right' inr
          (⟶*-trans r2 (∘-cong-right' inr
            (⟶*-trans r3 (∘-cong-right' inr
              (⟶*-trans r4 (∘-cong-right' inr
                (⟶*-trans r5 (∘-cong-right' inr
                  (⟶*-trans r6 (∘-cong-right' inr
                    (⟶*-trans r7 (∘-cong-right' inr
                      (⟶*-trans r8 (∘-cong-right' inr
                        (⟶*-trans r9 (∘-cong-right' inr r10)))))))))))))))))))

    step2 = ⟶*-trans (step assoc-r done) (∘-cong-right' In reduce-chain)

-- refold-idem-Out: position 11 (11 inrs before inl)
-- encode Out = In ∘ inr^11 ∘ inl ∘ ⌜F⌝Func
-- Payload functor: K TyFuncCode
refold-idem-Out : ∀ {F} → (cata TermF In ∘ encode (Out {F})) ⟶* encode (Out {F})
refold-idem-Out {F} = ⟶*-trans step1 step2
  where
    payload : Term Unit TyFuncCode
    payload = ⌜ F ⌝Func

    f : Term TermCode' TermCode'
    f = cata TermF In

    step1 = cata-β-right

    r0 = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' _ (fmap-TermF-inr f)) (step assoc-r done))
    r1 = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' _ (fmap-1-inr f)) (step assoc-r done))
    r2 = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' _ (fmap-2-inr f)) (step assoc-r done))
    r3 = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' _ (fmap-3-inr f)) (step assoc-r done))
    r4 = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' _ (fmap-4-inr f)) (step assoc-r done))
    r5 = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' _ (fmap-5-inr f)) (step assoc-r done))
    r6 = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' _ (fmap-6-inr f)) (step assoc-r done))
    r7 = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' _ (fmap-7-inr f)) (step assoc-r done))
    r8 = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' _ (fmap-8-inr f)) (step assoc-r done))
    r9 = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' _ (fmap-9-inr f)) (step assoc-r done))
    r10 = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' _ (fmap-10-inr f)) (step assoc-r done))

    r11 : (fmap TermF-11 f ∘ (inl ∘ payload)) ⟶* (inl ∘ payload)
    r11 = ⟶*-trans (step assoc-l done)
            (⟶*-trans (∘-cong-left' payload (fmap-11-inl f))
              (⟶*-trans (∘-cong-left' payload (step id-right done))
                done))

    reduce-chain =
      ⟶*-trans r0 (∘-cong-right' inr
        (⟶*-trans r1 (∘-cong-right' inr
          (⟶*-trans r2 (∘-cong-right' inr
            (⟶*-trans r3 (∘-cong-right' inr
              (⟶*-trans r4 (∘-cong-right' inr
                (⟶*-trans r5 (∘-cong-right' inr
                  (⟶*-trans r6 (∘-cong-right' inr
                    (⟶*-trans r7 (∘-cong-right' inr
                      (⟶*-trans r8 (∘-cong-right' inr
                        (⟶*-trans r9 (∘-cong-right' inr
                          (⟶*-trans r10 (∘-cong-right' inr r11)))))))))))))))))))))

    step2 = ⟶*-trans (step assoc-r done) (∘-cong-right' In reduce-chain)

------------------------------------------------------------------------
-- Id-based refold-idem proofs (recursive)
------------------------------------------------------------------------

-- These cases need mutual recursion with refold-idempotent.
-- The pattern is:
-- 1. cata-β-right to unfold
-- 2. Navigate through injection chain
-- 3. For Id ⊗ Id: use pair-comp to distribute, then fst-pair/snd-pair
-- 4. Apply IH recursively
-- 5. Reassemble

-- Mutual recursion block for Id-based cases
mutual
  refold-idempotent : ∀ {A B} (t : Term A B) →
                      (cata TermF In ∘ encode t) ⟶* encode t
  refold-idempotent id = refold-idem-id
  refold-idempotent (f ∘ g) = refold-idem-comp f g
  refold-idempotent fst = refold-idem-fst
  refold-idempotent snd = refold-idem-snd
  refold-idempotent ⟨ f , g ⟩ = refold-idem-pair f g
  refold-idempotent inl = refold-idem-inl
  refold-idempotent inr = refold-idem-inr
  refold-idempotent [ f , g ] = refold-idem-case f g
  refold-idempotent terminal = refold-idem-terminal
  refold-idempotent initial = refold-idem-initial
  refold-idempotent In = refold-idem-In
  refold-idempotent Out = refold-idem-Out
  refold-idempotent (cata F alg) = refold-idem-cata alg
  refold-idempotent (curry f) = refold-idem-curry f
  refold-idempotent apply = refold-idem-apply

  -- refold-idem-comp: position 1 (1 inr before inl)
  -- encode (f ∘ g) = In ∘ inr ∘ inl ∘ ⟨ encode f , encode g ⟩
  -- Payload functor: Id ⊗ Id
  refold-idem-comp : ∀ {A B C} (f : Term B C) (g : Term A B) →
                     (cata TermF In ∘ encode (f ∘ g)) ⟶* encode (f ∘ g)
  refold-idem-comp {A} {B} {C} f g = ⟶*-trans step1 step2
    where
      payload : Term Unit (TermCode' * TermCode')
      payload = ⟨ encode f , encode g ⟩

      c : Term TermCode' TermCode'
      c = cata TermF In

      step1 = cata-β-right

      -- Navigate 1 inr
      r0 : (fmap TermF c ∘ (inr ∘ (inl ∘ payload))) ⟶*
           (inr ∘ (fmap TermF-1 c ∘ (inl ∘ payload)))
      r0 = ⟶*-trans (step assoc-l done)
             (⟶*-trans (∘-cong-left' _ (fmap-TermF-inr c))
               (step assoc-r done))

      -- Handle inl with Id⊗Id payload
      -- fmap (Id ⊗ Id) c = ⟨ c ∘ fst , c ∘ snd ⟩
      -- ⟨ c ∘ fst , c ∘ snd ⟩ ∘ ⟨ encode f , encode g ⟩
      -- ⟶ ⟨ (c ∘ fst) ∘ payload , (c ∘ snd) ∘ payload ⟩ (by pair-comp)
      -- ⟶* ⟨ c ∘ encode f , c ∘ encode g ⟩ (by assoc + fst-pair/snd-pair)
      -- ⟶* ⟨ encode f , encode g ⟩ (by IH)

      r1 : (fmap TermF-1 c ∘ (inl ∘ payload)) ⟶* (inl ∘ payload)
      r1 = ⟶*-trans (step assoc-l done)
             (⟶*-trans (∘-cong-left' payload (fmap-1-inl c))
               (⟶*-trans (step assoc-r done)
                 (∘-cong-right' inl ih-step)))
        where
          -- fmap (Id ⊗ Id) c ∘ payload ⟶* payload
          ih-step : (fmap (Id ⊗ Id) c ∘ payload) ⟶* payload
          ih-step =
            -- fmap (Id ⊗ Id) c = ⟨ c ∘ fst , c ∘ snd ⟩
            -- ⟨ c ∘ fst , c ∘ snd ⟩ ∘ ⟨ encode f , encode g ⟩
            ⟶*-trans (step pair-comp done)  -- ⟶ ⟨ (c ∘ fst) ∘ payload , (c ∘ snd) ∘ payload ⟩
              (⟨⟩-cong
                (⟶*-trans (step assoc-r done)  -- (c ∘ fst) ∘ payload ⟶ c ∘ (fst ∘ payload)
                  (⟶*-trans (∘-cong-right' c (step fst-pair done))  -- ⟶* c ∘ encode f
                    (refold-idempotent f)))  -- IH: ⟶* encode f
                (⟶*-trans (step assoc-r done)  -- (c ∘ snd) ∘ payload ⟶ c ∘ (snd ∘ payload)
                  (⟶*-trans (∘-cong-right' c (step snd-pair done))  -- ⟶* c ∘ encode g
                    (refold-idempotent g))))  -- IH: ⟶* encode g

      reduce-chain : (fmap TermF c ∘ (inr ∘ (inl ∘ payload))) ⟶*
                     (inr ∘ (inl ∘ payload))
      reduce-chain = ⟶*-trans r0 (∘-cong-right' inr r1)

      step2 = ⟶*-trans (step assoc-r done) (∘-cong-right' In reduce-chain)

  -- refold-idem-pair: position 4 (4 inrs before inl)
  -- encode ⟨ f , g ⟩ = In ∘ inr^4 ∘ inl ∘ ⟨ encode f , encode g ⟩
  -- Payload functor: Id ⊗ Id
  refold-idem-pair : ∀ {A B C} (f : Term C A) (g : Term C B) →
                     (cata TermF In ∘ encode ⟨ f , g ⟩) ⟶* encode ⟨ f , g ⟩
  refold-idem-pair {A} {B} {C} f g = ⟶*-trans step1 step2
    where
      payload : Term Unit (TermCode' * TermCode')
      payload = ⟨ encode f , encode g ⟩

      c : Term TermCode' TermCode'
      c = cata TermF In

      step1 = cata-β-right

      r0 = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' _ (fmap-TermF-inr c)) (step assoc-r done))
      r1 = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' _ (fmap-1-inr c)) (step assoc-r done))
      r2 = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' _ (fmap-2-inr c)) (step assoc-r done))
      r3 = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' _ (fmap-3-inr c)) (step assoc-r done))

      r4 : (fmap TermF-4 c ∘ (inl ∘ payload)) ⟶* (inl ∘ payload)
      r4 = ⟶*-trans (step assoc-l done)
             (⟶*-trans (∘-cong-left' payload (fmap-4-inl c))
               (⟶*-trans (step assoc-r done)
                 (∘-cong-right' inl ih-step)))
        where
          ih-step : (fmap (Id ⊗ Id) c ∘ payload) ⟶* payload
          ih-step =
            ⟶*-trans (step pair-comp done)
              (⟨⟩-cong
                (⟶*-trans (step assoc-r done)
                  (⟶*-trans (∘-cong-right' c (step fst-pair done))
                    (refold-idempotent f)))
                (⟶*-trans (step assoc-r done)
                  (⟶*-trans (∘-cong-right' c (step snd-pair done))
                    (refold-idempotent g))))

      reduce-chain =
        ⟶*-trans r0 (∘-cong-right' inr
          (⟶*-trans r1 (∘-cong-right' inr
            (⟶*-trans r2 (∘-cong-right' inr
              (⟶*-trans r3 (∘-cong-right' inr r4)))))))

      step2 = ⟶*-trans (step assoc-r done) (∘-cong-right' In reduce-chain)

  -- refold-idem-case: position 7 (7 inrs before inl)
  -- encode [ f , g ] = In ∘ inr^7 ∘ inl ∘ ⟨ encode f , encode g ⟩
  -- Payload functor: Id ⊗ Id
  refold-idem-case : ∀ {A B C} (f : Term A C) (g : Term B C) →
                     (cata TermF In ∘ encode [ f , g ]) ⟶* encode [ f , g ]
  refold-idem-case {A} {B} {C} f g = ⟶*-trans step1 step2
    where
      payload : Term Unit (TermCode' * TermCode')
      payload = ⟨ encode f , encode g ⟩

      c : Term TermCode' TermCode'
      c = cata TermF In

      step1 = cata-β-right

      r0 = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' _ (fmap-TermF-inr c)) (step assoc-r done))
      r1 = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' _ (fmap-1-inr c)) (step assoc-r done))
      r2 = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' _ (fmap-2-inr c)) (step assoc-r done))
      r3 = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' _ (fmap-3-inr c)) (step assoc-r done))
      r4 = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' _ (fmap-4-inr c)) (step assoc-r done))
      r5 = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' _ (fmap-5-inr c)) (step assoc-r done))
      r6 = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' _ (fmap-6-inr c)) (step assoc-r done))

      r7 : (fmap TermF-7 c ∘ (inl ∘ payload)) ⟶* (inl ∘ payload)
      r7 = ⟶*-trans (step assoc-l done)
             (⟶*-trans (∘-cong-left' payload (fmap-7-inl c))
               (⟶*-trans (step assoc-r done)
                 (∘-cong-right' inl ih-step)))
        where
          ih-step : (fmap (Id ⊗ Id) c ∘ payload) ⟶* payload
          ih-step =
            ⟶*-trans (step pair-comp done)
              (⟨⟩-cong
                (⟶*-trans (step assoc-r done)
                  (⟶*-trans (∘-cong-right' c (step fst-pair done))
                    (refold-idempotent f)))
                (⟶*-trans (step assoc-r done)
                  (⟶*-trans (∘-cong-right' c (step snd-pair done))
                    (refold-idempotent g))))

      reduce-chain =
        ⟶*-trans r0 (∘-cong-right' inr
          (⟶*-trans r1 (∘-cong-right' inr
            (⟶*-trans r2 (∘-cong-right' inr
              (⟶*-trans r3 (∘-cong-right' inr
                (⟶*-trans r4 (∘-cong-right' inr
                  (⟶*-trans r5 (∘-cong-right' inr
                    (⟶*-trans r6 (∘-cong-right' inr r7)))))))))))))

      step2 = ⟶*-trans (step assoc-r done) (∘-cong-right' In reduce-chain)

  -- refold-idem-cata: position 12 (12 inrs then inl)
  -- encode (cata F alg) = In ∘ inr^12 ∘ inl ∘ ⟨ ⌜F⌝Func , encode alg ⟩
  -- Payload functor: K TyFuncCode ⊗ Id
  refold-idem-cata : ∀ {F A} (alg : Term (⟦ F ⟧F A) A) →
                     (cata TermF In ∘ encode (cata F alg)) ⟶* encode (cata F alg)
  refold-idem-cata {F} {A} alg = ⟶*-trans step1 step2
    where
      payload : Term Unit (TyFuncCode * TermCode')
      payload = ⟨ ⌜ F ⌝Func , encode alg ⟩

      c : Term TermCode' TermCode'
      c = cata TermF In

      step1 = cata-β-right

      r0 = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' _ (fmap-TermF-inr c)) (step assoc-r done))
      r1 = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' _ (fmap-1-inr c)) (step assoc-r done))
      r2 = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' _ (fmap-2-inr c)) (step assoc-r done))
      r3 = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' _ (fmap-3-inr c)) (step assoc-r done))
      r4 = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' _ (fmap-4-inr c)) (step assoc-r done))
      r5 = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' _ (fmap-5-inr c)) (step assoc-r done))
      r6 = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' _ (fmap-6-inr c)) (step assoc-r done))
      r7 = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' _ (fmap-7-inr c)) (step assoc-r done))
      r8 = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' _ (fmap-8-inr c)) (step assoc-r done))
      r9 = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' _ (fmap-9-inr c)) (step assoc-r done))
      r10 = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' _ (fmap-10-inr c)) (step assoc-r done))
      r11 = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' _ (fmap-11-inr c)) (step assoc-r done))

      -- Navigate through inl with TermF-12 = (K TyFuncCode ⊗ Id) ⊕ curry ⊕ apply
      -- fmap TermF-12 c ∘ inl ⟶* inl ∘ fmap (K TyFuncCode ⊗ Id) c
      r12-inl : (fmap TermF-12 c ∘ inl) ⟶* (inl ∘ fmap (K TyFuncCode ⊗ Id) c)
      r12-inl = fmap-sum-inl (K TyFuncCode ⊗ Id) TermF-13 c

      -- Final step: fmap (K ⊗ Id) c ∘ payload
      -- fmap (K TyFuncCode ⊗ Id) c = ⟨ id ∘ fst , c ∘ snd ⟩ = ⟨ fst , c ∘ snd ⟩ after id-left
      r12-payload : (fmap (K TyFuncCode ⊗ Id) c ∘ payload) ⟶* payload
      r12-payload =
        ⟶*-trans (step pair-comp done)  -- ⟶ ⟨ (id ∘ fst) ∘ payload , (c ∘ snd) ∘ payload ⟩
          (⟨⟩-cong
            (⟶*-trans (step assoc-r done)  -- (id ∘ fst) ∘ payload ⟶ id ∘ (fst ∘ payload)
              (⟶*-trans (step id-left done)  -- ⟶ fst ∘ payload
                (step fst-pair done)))  -- ⟶ ⌜F⌝Func
            (⟶*-trans (step assoc-r done)  -- (c ∘ snd) ∘ payload ⟶ c ∘ (snd ∘ payload)
              (⟶*-trans (∘-cong-right' c (step snd-pair done))  -- ⟶ c ∘ encode alg
                (refold-idempotent alg))))  -- IH: ⟶* encode alg

      -- Chain: (fmap TermF-12 c ∘ (inl ∘ payload)) ⟶* (inl ∘ payload)
      r12 : (fmap TermF-12 c ∘ (inl ∘ payload)) ⟶* (inl ∘ payload)
      r12 = ⟶*-trans (step assoc-l done)
              (⟶*-trans (∘-cong-left' _ r12-inl)
                (⟶*-trans (step assoc-r done)
                  (∘-cong-right' inl r12-payload)))

      reduce-chain =
        ⟶*-trans r0 (∘-cong-right' inr
          (⟶*-trans r1 (∘-cong-right' inr
            (⟶*-trans r2 (∘-cong-right' inr
              (⟶*-trans r3 (∘-cong-right' inr
                (⟶*-trans r4 (∘-cong-right' inr
                  (⟶*-trans r5 (∘-cong-right' inr
                    (⟶*-trans r6 (∘-cong-right' inr
                      (⟶*-trans r7 (∘-cong-right' inr
                        (⟶*-trans r8 (∘-cong-right' inr
                          (⟶*-trans r9 (∘-cong-right' inr
                            (⟶*-trans r10 (∘-cong-right' inr
                              (⟶*-trans r11 (∘-cong-right' inr r12)))))))))))))))))))))))

      step2 = ⟶*-trans (step assoc-r done) (∘-cong-right' In reduce-chain)

  -- refold-idem-curry: position 13 (13 inrs then inl)
  -- encode (curry f) = In ∘ inr^13 ∘ inl ∘ ⟨ ⟨ ⌜A⌝, ⌜B⌝ ⟩ , ⟨ ⌜C⌝, encode f ⟩ ⟩
  -- Payload functor: (K TyFuncCode ⊗ K TyFuncCode) ⊗ (K TyFuncCode ⊗ Id)
  refold-idem-curry : ∀ {A B C} (f : Term (A * B) C) →
                      (cata TermF In ∘ encode (curry f)) ⟶* encode (curry f)
  refold-idem-curry {A} {B} {C} f = ⟶*-trans step1 step2
    where
      payload : Term Unit ((TyFuncCode * TyFuncCode) * (TyFuncCode * TermCode'))
      payload = ⟨ ⟨ ⌜ A ⌝Ty , ⌜ B ⌝Ty ⟩ , ⟨ ⌜ C ⌝Ty , encode f ⟩ ⟩

      c : Term TermCode' TermCode'
      c = cata TermF In

      step1 = cata-β-right

      r0 = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' _ (fmap-TermF-inr c)) (step assoc-r done))
      r1 = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' _ (fmap-1-inr c)) (step assoc-r done))
      r2 = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' _ (fmap-2-inr c)) (step assoc-r done))
      r3 = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' _ (fmap-3-inr c)) (step assoc-r done))
      r4 = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' _ (fmap-4-inr c)) (step assoc-r done))
      r5 = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' _ (fmap-5-inr c)) (step assoc-r done))
      r6 = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' _ (fmap-6-inr c)) (step assoc-r done))
      r7 = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' _ (fmap-7-inr c)) (step assoc-r done))
      r8 = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' _ (fmap-8-inr c)) (step assoc-r done))
      r9 = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' _ (fmap-9-inr c)) (step assoc-r done))
      r10 = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' _ (fmap-10-inr c)) (step assoc-r done))
      r11 = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' _ (fmap-11-inr c)) (step assoc-r done))
      r12 = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' _ (fmap-12-inr c)) (step assoc-r done))

      -- Navigate through inl with TermF-13 = CurryF ⊕ ApplyF
      CurryF = (K TyFuncCode ⊗ K TyFuncCode) ⊗ (K TyFuncCode ⊗ Id)
      r13-inl : (fmap TermF-13 c ∘ inl) ⟶* (inl ∘ fmap CurryF c)
      r13-inl = fmap-sum-inl CurryF TermF-14 c

      -- fmap CurryF c ∘ payload
      -- CurryF = (K ⊗ K) ⊗ (K ⊗ Id)
      -- fmap CurryF c = ⟨ fmap (K ⊗ K) c ∘ fst , fmap (K ⊗ Id) c ∘ snd ⟩
      --              = ⟨ id ∘ fst , ⟨ id ∘ fst , c ∘ snd ⟩ ∘ snd ⟩
      r13-payload : (fmap CurryF c ∘ payload) ⟶* payload
      r13-payload =
        ⟶*-trans (step pair-comp done)
          (⟨⟩-cong
            -- First component: fmap (K ⊗ K) c ∘ fst ∘ payload ⟶* ⟨ ⌜A⌝, ⌜B⌝ ⟩
            (⟶*-trans (step assoc-r done)
              (⟶*-trans (∘-cong-right' (fmap (K TyFuncCode ⊗ K TyFuncCode) c) (step fst-pair done))
                (⟶*-trans (∘-cong-left' _ (fmap-KK-id TyFuncCode TyFuncCode c))
                  (step id-left done))))
            -- Second component: fmap (K ⊗ Id) c ∘ snd ∘ payload ⟶* ⟨ ⌜C⌝, encode f ⟩
            (⟶*-trans (step assoc-r done)
              (⟶*-trans (∘-cong-right' (fmap (K TyFuncCode ⊗ Id) c) (step snd-pair done))
                (⟶*-trans (step pair-comp done)
                  (⟨⟩-cong
                    (⟶*-trans (step assoc-r done)
                      (⟶*-trans (step id-left done)
                        (step fst-pair done)))
                    (⟶*-trans (step assoc-r done)
                      (⟶*-trans (∘-cong-right' c (step snd-pair done))
                        (refold-idempotent f))))))))

      r13 : (fmap TermF-13 c ∘ (inl ∘ payload)) ⟶* (inl ∘ payload)
      r13 = ⟶*-trans (step assoc-l done)
              (⟶*-trans (∘-cong-left' _ r13-inl)
                (⟶*-trans (step assoc-r done)
                  (∘-cong-right' inl r13-payload)))

      reduce-chain =
        ⟶*-trans r0 (∘-cong-right' inr
          (⟶*-trans r1 (∘-cong-right' inr
            (⟶*-trans r2 (∘-cong-right' inr
              (⟶*-trans r3 (∘-cong-right' inr
                (⟶*-trans r4 (∘-cong-right' inr
                  (⟶*-trans r5 (∘-cong-right' inr
                    (⟶*-trans r6 (∘-cong-right' inr
                      (⟶*-trans r7 (∘-cong-right' inr
                        (⟶*-trans r8 (∘-cong-right' inr
                          (⟶*-trans r9 (∘-cong-right' inr
                            (⟶*-trans r10 (∘-cong-right' inr
                              (⟶*-trans r11 (∘-cong-right' inr
                                (⟶*-trans r12 (∘-cong-right' inr r13)))))))))))))))))))))))))

      step2 = ⟶*-trans (step assoc-r done) (∘-cong-right' In reduce-chain)

  -- refold-idem-apply: position 14 (14 inrs, no inl - terminal position)
  -- encode apply = In ∘ inr^14 ∘ ⟨ ⌜A⌝, ⌜B⌝ ⟩
  -- Payload functor: K TyFuncCode ⊗ K TyFuncCode
  refold-idem-apply : ∀ {A B} →
                      (cata TermF In ∘ encode (apply {A} {B})) ⟶* encode (apply {A} {B})
  refold-idem-apply {A} {B} = ⟶*-trans step1 step2
    where
      payload : Term Unit (TyFuncCode * TyFuncCode)
      payload = ⟨ ⌜ A ⌝Ty , ⌜ B ⌝Ty ⟩

      c : Term TermCode' TermCode'
      c = cata TermF In

      step1 = cata-β-right

      r0 = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' _ (fmap-TermF-inr c)) (step assoc-r done))
      r1 = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' _ (fmap-1-inr c)) (step assoc-r done))
      r2 = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' _ (fmap-2-inr c)) (step assoc-r done))
      r3 = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' _ (fmap-3-inr c)) (step assoc-r done))
      r4 = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' _ (fmap-4-inr c)) (step assoc-r done))
      r5 = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' _ (fmap-5-inr c)) (step assoc-r done))
      r6 = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' _ (fmap-6-inr c)) (step assoc-r done))
      r7 = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' _ (fmap-7-inr c)) (step assoc-r done))
      r8 = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' _ (fmap-8-inr c)) (step assoc-r done))
      r9 = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' _ (fmap-9-inr c)) (step assoc-r done))
      r10 = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' _ (fmap-10-inr c)) (step assoc-r done))
      r11 = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' _ (fmap-11-inr c)) (step assoc-r done))
      r12 = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' _ (fmap-12-inr c)) (step assoc-r done))
      r13 = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' _ (fmap-13-inr c)) (step assoc-r done))

      -- Final step: fmap TermF-14 c ∘ payload
      -- TermF-14 = K TyFuncCode ⊗ K TyFuncCode
      -- fmap TermF-14 c = ⟨ id ∘ fst , id ∘ snd ⟩ ⟶* id (by fmap-KK-id)
      r14 : (fmap TermF-14 c ∘ payload) ⟶* payload
      r14 = ⟶*-trans (∘-cong-left' payload (fmap-KK-id TyFuncCode TyFuncCode c)) (step id-left done)

      reduce-chain =
        ⟶*-trans r0 (∘-cong-right' inr
          (⟶*-trans r1 (∘-cong-right' inr
            (⟶*-trans r2 (∘-cong-right' inr
              (⟶*-trans r3 (∘-cong-right' inr
                (⟶*-trans r4 (∘-cong-right' inr
                  (⟶*-trans r5 (∘-cong-right' inr
                    (⟶*-trans r6 (∘-cong-right' inr
                      (⟶*-trans r7 (∘-cong-right' inr
                        (⟶*-trans r8 (∘-cong-right' inr
                          (⟶*-trans r9 (∘-cong-right' inr
                            (⟶*-trans r10 (∘-cong-right' inr
                              (⟶*-trans r11 (∘-cong-right' inr
                                (⟶*-trans r12 (∘-cong-right' inr
                                  (⟶*-trans r13 (∘-cong-right' inr r14)))))))))))))))))))))))))))

      step2 = ⟶*-trans (step assoc-r done) (∘-cong-right' In reduce-chain)

-- The N-refold fixpoint follows from refold-idempotent
N-refold-fixpoint : (N-refold ∘ encode N-refold) ⟶* encode N-refold
N-refold-fixpoint = refold-idempotent N-refold

