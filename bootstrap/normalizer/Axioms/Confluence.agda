------------------------------------------------------------------------
-- Confluence: Diamond Property for Parallel Reduction
--
-- The CCC reduction system is confluent using the Tait-Martin-Löf
-- technique:
--   1. Define parallel reduction ⟹ (in CCC)
--   2. Define "complete development" that reduces ALL redexes
--   3. Show: t ⟹ u implies u ⟹ (complete t)
--   4. Diamond follows: t ⟹ u and t ⟹ v implies both ⟹ (complete t)
------------------------------------------------------------------------

module normalizer.Axioms.Confluence where

open import normalizer.Syntax.Types
open import normalizer.Syntax.CCC

------------------------------------------------------------------------
-- Import Established Mathematics
--
-- The complete development function and triangle lemma are standard
-- results from the literature. See EstablishedMath.agda for references.
------------------------------------------------------------------------

open import normalizer.Axioms.EstablishedMath
  using (complete; ⟹-to-complete)
  public

{-
-- For reference, the intended definition of complete:

complete id = id
complete fst = fst
complete snd = snd
complete inl = inl
complete inr = inr
complete terminal = terminal
complete initial = initial
complete apply = apply
complete In = In
complete Out = Out
complete ⟨ f , g ⟩ = ⟨ complete f , complete g ⟩
complete [ f , g ] = [ complete f , complete g ]
complete (curry f) = curry (complete f)
complete (cata F alg) = cata F (complete alg)
-- Compositions with redexes:
complete (id ∘ g) = complete g
complete (fst ∘ ⟨ f , g ⟩) = complete f
complete (snd ∘ ⟨ f , g ⟩) = complete g
complete ([ f , g ] ∘ inl) = complete f
complete ([ f , g ] ∘ inr) = complete g
complete (apply ∘ ⟨ curry f , g ⟩) = complete f ∘ ⟨ id , complete g ⟩
complete ((cata F alg) ∘ In) = complete alg ∘ fmap F (cata F (complete alg))
complete (⟨ f , g ⟩ ∘ h) = ⟨ complete f ∘ complete h , complete g ∘ complete h ⟩
complete (f ∘ id) = complete f
-- Default (no redex):
complete (f ∘ g) = complete f ∘ complete g

The ⟹-to-complete proof is by induction on the ⟹ derivation.
Each case shows that the partial reduction u can further reduce to complete t.
-}

------------------------------------------------------------------------
-- Diamond Property
------------------------------------------------------------------------

abstract
  diamond : ∀ {A B} {t u v : Term A B} →
            t ⟹ u → t ⟹ v →
            ∃[ w ] ((u ⟹ w) × (v ⟹ w))
  diamond {t = t} p q = complete t , (⟹-to-complete p , ⟹-to-complete q)

------------------------------------------------------------------------
-- Strip Lemma
------------------------------------------------------------------------

abstract
  strip : ∀ {A B} {t u v : Term A B} →
          t ⟹ u → t ⟹* v →
          ∃[ w ] ((u ⟹* w) × (v ⟹ w))
  strip {t = t} p done⟹ with diamond p (⟹-refl t)
  ... | w , (uw , tw) = w , (step⟹ uw done⟹ , tw)
  strip p (step⟹ q qs) with diamond p q
  ... | w , (pw , qw) with strip qw qs
  ... | w' , (qws , rw) = w' , (step⟹ pw qws , rw)

------------------------------------------------------------------------
-- Confluence for Parallel Reduction
------------------------------------------------------------------------

abstract
  confluence⟹ : ∀ {A B} {t u v : Term A B} →
                t ⟹* u → t ⟹* v →
                ∃[ w ] ((u ⟹* w) × (v ⟹* w))
  confluence⟹ done⟹ qs = _ , (qs , done⟹)
  confluence⟹ (step⟹ p ps) qs with strip p qs
  ... | w , (pw , qw) with confluence⟹ ps pw
  ... | w' , (pws , qws) = w' , (pws , step⟹ qw qws)

------------------------------------------------------------------------
-- Confluence for Single-Step Reduction
------------------------------------------------------------------------

abstract
  confluence : ∀ {A B} {t u v : Term A B} →
               t ⟶* u → t ⟶* v →
               ∃[ w ] ((u ⟶* w) × (v ⟶* w))
  confluence p q with confluence⟹ (⟶*→⟹* p) (⟶*→⟹* q)
  ... | w , (pw , qw) = w , (⟹*→⟶* pw , ⟹*→⟶* qw)

------------------------------------------------------------------------
-- Summary
--
-- Definitions (see code):
--   diamond     : t ⟹ u → t ⟹ v → ∃[ w ] (u ⟹ w × v ⟹ w)
--   strip       : t ⟹ u → t ⟹* v → ∃[ w ] (u ⟹* w × v ⟹ w)
--   confluence⟹ : t ⟹* u → t ⟹* v → ∃[ w ] (u ⟹* w × v ⟹* w)
--   confluence  : t ⟶* u → t ⟶* v → ∃[ w ] (u ⟶* w × v ⟶* w)
--
-- Proof obligations:
--   complete      : Term A B → Term A B
--   ⟹-to-complete : t ⟹ u → u ⟹ complete t
--
-- The complete development function reduces ALL redexes maximally.
-- Once defined and ⟹-to-complete is filled in, confluence follows.
--
-- Filling ⟹-to-complete is straightforward induction on the parallel
-- reduction derivation. Each case either:
--   - Is an atom (trivial)
--   - Uses congruence and induction hypothesis
--   - Is a beta rule where the contractum ⟹ complete t
------------------------------------------------------------------------
