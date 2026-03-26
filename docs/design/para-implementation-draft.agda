------------------------------------------------------------------------
-- Draft: Paramorphism Implementation
--
-- This file shows the code changes needed to add Para to Once.
-- NOT meant to be compiled - just a design document.
------------------------------------------------------------------------

-- ======================================================================
-- PART 1: Add to Once.Functor.Base (after Catamorphism section, ~line 142)
-- ======================================================================

------------------------------------------------------------------------
-- Paramorphism (Primitive Recursion)
--
-- Paramorphism gives access to both the original substructure AND
-- the recursive result. This is the key to bounded hylomorphisms.
--
-- Derived from cataS by making the carrier type (μS F × A).
------------------------------------------------------------------------

-- | Paramorphism (primitive recursion)
--
-- The algebra receives F (μS F × A) where each recursive position has:
--   - μS F: the original substructure
--   - A: the recursive result
--
-- Termination follows from cataS termination (structural recursion on μS).
-- No TERMINATING pragma needed!
--
paraS : ∀ {F} {A : Set} → (⟦ F ⟧SF (μS F × A) → A) → μS F → A
paraS {F} {A} alg x = proj₂ (cataS {F} alg' x)
  where
    -- Carrier type: μS F × A (both reconstruction and result)
    alg' : ⟦ F ⟧SF (μS F × A) → (μS F × A)
    alg' fx = (⟨ sfmap F proj₁ fx ⟩ , alg fx)

-- | Paramorphism computation law
--
-- para alg ⟨ x ⟩ = alg (fmap (λ y → (y , para alg y)) x)
--
-- This shows the algebra sees both original substructures and recursive results.
--
paraS-computation : ∀ (F : SFunctor) {A : Set} (alg : ⟦ F ⟧SF (μS F × A) → A)
                    (x : ⟦ F ⟧SF (μS F))
                  → paraS {F} alg ⟨ x ⟩ ≡ alg (sfmap F (λ y → (y , paraS alg y)) x)
-- Proof would follow from cataS-computation

-- ======================================================================
-- PART 2: Add to Once.CCC.IR (after Cata, ~line 106)
-- ======================================================================

  -- Para: paramorphism (fold with access to original substructure)
  --
  -- The algebra IR (⟦ F ⟧T (μ-type F * A)) A receives at each position:
  --   - The original substructure (μ-type F)
  --   - The recursive result (A)
  --
  -- Total by Lambek's Lemma (derived from Cata).
  --
  Para : ∀ {F} → WellFormedF F → ∀ {A}
       → IR (⟦ F ⟧T (μ-type F * A)) A
       → IR (μ-type F) A

-- ======================================================================
-- PART 3: Add to Once.Semantics.Core (after sem-cata)
-- ======================================================================

-- | Paramorphism: fold with access to original substructure
--
-- Derived from sem-cata, no TERMINATING needed.
--
sem-para : ∀ {F : Functor} → WellFormedF F → {A : Set}
         → (⟦ F ⟧F (⟦μ⟧ F × A) → A) → ⟦μ⟧ F → A
sem-para {F} wf {A} alg x = proj₂ (sem-cata wf alg' x)
  where
    alg' : ⟦ F ⟧F (⟦μ⟧ F × A) → (⟦μ⟧ F × A)
    alg' fx = (sem-In F (sem-fmap F proj₁ fx) , alg fx)

-- ======================================================================
-- PART 4: Add to Once.Semantics.IR (eval case)
-- ======================================================================

-- Para evaluation:
eval ps (Para {F} wf alg) x =
  sem-para wf (λ fx → eval ps alg (coerce-functor⁻¹ F _ fx)) x

-- ======================================================================
-- PART 5: Rewrite obs using Para (in Once.Derived.Observation)
-- ======================================================================

-- Current obs implementation uses Hylo with TERMINATING pragma in semantics.
-- New implementation uses Para - terminating by construction!

-- | obs : Nat → Stream A → List A
--
-- Observe exactly n steps of a stream, producing a list.
--
-- Implementation: Para on NatF with carrier type (Stream A → List A).
-- The algebra pattern-matches on the NatF structure:
--   - Zero: ignore stream, produce Nil
--   - Suc (n, k): produce Cons (head stream, k (tail stream))
--
-- Termination: Para is derived from Cata, which is structurally recursive.
--
obsViaPara : ∀ {A}
    → WellFormedF (StreamF A)
    → WellFormedF (ListF A)
    → IR (Nat * Stream A) (List A)
obsViaPara {A} wfStream wfList =
  -- Para returns: Nat → (Stream A → List A)
  -- We apply: (Nat * Stream A) → List A
  apply ∘ ⟨ paraBody ∘ fst , snd ⟩ Stack
  where
    -- Para algebra type: ⟦ NatF ⟧T (Nat * (Stream A ⇒ List A)) → (Stream A ⇒ List A)
    -- = (Unit + (Nat * (Stream A ⇒ List A))) → (Stream A ⇒ List A)

    -- Type of Para result: Nat → (Stream A ⇒ List A)
    paraBody : IR Nat (Stream A ⇒[ Many ] List A)
    paraBody = Para wf-NatF paraAlg

    -- The algebra: receives NatF (Nat × (Stream A → List A))
    -- In the point-free IR, this is complex to express...
    --
    -- Conceptually:
    --   paraAlg (inl tt) = λ _ → Nil
    --   paraAlg (inr (n, k)) = λ stream → Cons (head stream, k (tail stream))
    --
    paraAlg : IR (⟦ NatF ⟧T (Nat * (Stream A ⇒[ Many ] List A))) (Stream A ⇒[ Many ] List A)
    paraAlg = case zeroCase sucCase
      where
        -- Zero case: Unit → (Stream A → List A)
        -- Result: constant empty list (ignores stream)
        zeroCase : IR Unit (Stream A ⇒[ Many ] List A)
        zeroCase = curry (In wfList Stack ∘ inl Stack ∘ terminal) Stack

        -- Suc case: (Nat * (Stream A ⇒ List A)) → (Stream A ⇒ List A)
        -- We have: predecessor n and continuation k
        -- We want: λ stream → Cons (head stream, k (tail stream))
        sucCase : IR (Nat * (Stream A ⇒[ Many ] List A)) (Stream A ⇒[ Many ] List A)
        sucCase = curry body Stack
          where
            -- body : (Nat * (Stream A ⇒ List A)) * Stream A → List A
            -- Let's call the input ((n, k), stream)
            -- Result: Cons (head stream, k (tail stream))
            body : IR ((Nat * (Stream A ⇒[ Many ] List A)) * Stream A) (List A)
            body = In wfList Stack ∘ inr Stack ∘
                   ⟨ fst ∘ Out wfStream ∘ snd   -- head of stream
                   , apply ∘ ⟨ snd ∘ fst        -- continuation k
                             , snd ∘ Out wfStream ∘ snd  -- tail of stream
                             ⟩ Stack
                   ⟩ Stack

-- ======================================================================
-- Summary
-- ======================================================================

-- Key changes:
-- 1. paraS in Base.agda: derived from cataS, terminating by construction
-- 2. Para in IR.agda: new constructor for paramorphism
-- 3. sem-para in Core.agda: evaluation via sem-cata, no TERMINATING
-- 4. eval case in IR.agda: evaluate Para via sem-para
-- 5. obsViaPara: demonstrates rewriting obs without Hylo
--
-- Benefits:
-- - obs terminates provably (no trust pragma)
-- - Full fusion still possible (Para composes with other schemes)
-- - Clean separation: Para for bounded recursion, Ana for corecursion
--
-- The general Hylo remains with TERMINATING for cases where:
-- - F ≠ G (different functor shapes)
-- - User must provide external termination argument
-- - Escape hatch for complex recursion patterns
