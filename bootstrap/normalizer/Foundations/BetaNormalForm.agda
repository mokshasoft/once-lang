------------------------------------------------------------------------
-- BetaNormalForm: Computational normal forms (no beta-redexes)
--
-- A term is in beta-normal form if no computation rules apply.
-- This ignores structural rewrites like associativity.
------------------------------------------------------------------------

module normalizer.Foundations.BetaNormalForm where

open import normalizer.Foundations.Types
open import normalizer.Foundations.CCC
open import normalizer.Foundations.Encoding
  using (encode; ⌜_⌝Ty; ⌜_⌝Func; TyFuncCode; TyFuncF; TermCode'; TermF)

------------------------------------------------------------------------
-- Beta-Redex Patterns
------------------------------------------------------------------------

data _⟶β_ : ∀ {A B} → Term A B → Term A B → Set where
  β-id-left   : ∀ {A B} {f : Term A B} → (id ∘ f) ⟶β f
  β-id-right  : ∀ {A B} {f : Term A B} → (f ∘ id) ⟶β f
  β-fst-pair  : ∀ {A B C} {f : Term C A} {g : Term C B} → (fst ∘ ⟨ f , g ⟩) ⟶β f
  β-snd-pair  : ∀ {A B C} {f : Term C A} {g : Term C B} → (snd ∘ ⟨ f , g ⟩) ⟶β g
  β-eta-pair  : ∀ {A B} → ⟨ fst , snd ⟩ ⟶β id {A * B}
  β-case-inl  : ∀ {A B C} {f : Term A C} {g : Term B C} → ([ f , g ] ∘ inl) ⟶β f
  β-case-inr  : ∀ {A B C} {f : Term A C} {g : Term B C} → ([ f , g ] ∘ inr) ⟶β g
  β-eta-case  : ∀ {A B} → [ inl , inr ] ⟶β id {A + B}
  β-curry-β   : ∀ {A B C} {f : Term (A * B) C} {g : Term A B} →
                (apply ∘ ⟨ curry f , g ⟩) ⟶β (f ∘ ⟨ id , g ⟩)
  β-cata      : ∀ {F A} {alg : Term (⟦ F ⟧F A) A} →
                (cata F alg ∘ In) ⟶β (alg ∘ fmap F (cata F alg))
  β-out-in    : ∀ F → (Out {F} ∘ In {F}) ⟶β id {⟦ F ⟧F (μ F)}
  β-in-out    : ∀ F → (In {F} ∘ Out {F}) ⟶β id {μ F}
  β-∘-l    : ∀ {A B C} {f f' : Term B C} {g : Term A B} →
              f ⟶β f' → (f ∘ g) ⟶β (f' ∘ g)
  β-∘-r    : ∀ {A B C} {f : Term B C} {g g' : Term A B} →
              g ⟶β g' → (f ∘ g) ⟶β (f ∘ g')
  β-pair-l : ∀ {A B C} {f f' : Term C A} {g : Term C B} →
              f ⟶β f' → ⟨ f , g ⟩ ⟶β ⟨ f' , g ⟩
  β-pair-r : ∀ {A B C} {f : Term C A} {g g' : Term C B} →
              g ⟶β g' → ⟨ f , g ⟩ ⟶β ⟨ f , g' ⟩
  β-case-l : ∀ {A B C} {f f' : Term A C} {g : Term B C} →
              f ⟶β f' → [ f , g ] ⟶β [ f' , g ]
  β-case-r : ∀ {A B C} {f : Term A C} {g g' : Term B C} →
              g ⟶β g' → [ f , g ] ⟶β [ f , g' ]
  β-cata-alg : ∀ {F A} {alg alg' : Term (⟦ F ⟧F A) A} →
              alg ⟶β alg' → cata F alg ⟶β cata F alg'
  β-curry-cong : ∀ {A B C} {f f' : Term (A * B) C} →
                 f ⟶β f' → curry f ⟶β curry f'

------------------------------------------------------------------------
-- Beta-Normal Form
------------------------------------------------------------------------

IsBetaNormalForm : ∀ {A B} → Term A B → Set
IsBetaNormalForm t = ∀ {u} → ¬ (t ⟶β u)

------------------------------------------------------------------------
-- Proof that encoded terms are in beta-normal form
--
-- Key insight: All encodings have the form In ∘ inr^n ∘ [inl ∘] payload
-- where payload is terminal, ⟨encoded, encoded⟩, or recursive encoding.
--
-- The critical observation: ALL encoding bodies have target type that
-- is NOT Unit. This means id : Term Unit Unit can never appear as a body,
-- ruling out β-id-right. Similarly, Out : Term (μ F) _ can never appear
-- since our sources are all Unit, ruling out β-in-out.
------------------------------------------------------------------------

private
  -- Unit is not equal to any complex type (both directions for convenience)
  Unit≢TyFuncCode : Unit ≡ TyFuncCode → ⊥
  Unit≢TyFuncCode ()

  TyFuncCode≢Unit : TyFuncCode ≡ Unit → ⊥
  TyFuncCode≢Unit ()

  Unit≢TermCode : Unit ≡ TermCode' → ⊥
  Unit≢TermCode ()

  TermCode≢Unit : TermCode' ≡ Unit → ⊥
  TermCode≢Unit ()

  Unit≢Sum : ∀ {A B} → Unit ≡ (A + B) → ⊥
  Unit≢Sum ()

  Sum≢Unit : ∀ {A B} → (A + B) ≡ Unit → ⊥
  Sum≢Unit ()

  Unit≢Prod : ∀ {A B} → Unit ≡ (A * B) → ⊥
  Unit≢Prod ()

  Prod≢Unit : ∀ {A B} → (A * B) ≡ Unit → ⊥
  Prod≢Unit ()

  abstract
    terminal-nf : ∀ {A} → IsBetaNormalForm (terminal {A})
    terminal-nf ()

    -- Pair of encodings from Unit is β-nf
    -- β-eta-pair needs ⟨fst, snd⟩ but fst : Term (A * B) A has non-Unit source
    pair-nf : ∀ {A B} {f : Term Unit A} {g : Term Unit B} →
              IsBetaNormalForm f → IsBetaNormalForm g →
              IsBetaNormalForm ⟨ f , g ⟩
    pair-nf f-nf g-nf (β-pair-l r) = f-nf r
    pair-nf f-nf g-nf (β-pair-r r) = g-nf r

    -- inl ∘ body where body : Term Unit A and A ≢ Unit.
    -- β-id-right requires body = id : Term Unit Unit, but if A ≢ Unit then id can't type-check.
    inl-comp-nf : ∀ {A B} {body : Term Unit A} →
                  (A ≡ Unit → ⊥) →
                  IsBetaNormalForm body →
                  IsBetaNormalForm (inl {A} {B} ∘ body)
    inl-comp-nf _ body-nf (β-∘-l ())
    inl-comp-nf A≢Unit _ β-id-right = A≢Unit refl
    inl-comp-nf _ body-nf (β-∘-r r) = body-nf r

    -- inr ∘ body where body : Term Unit B and B ≢ Unit.
    inr-comp-nf : ∀ {A B} {body : Term Unit B} →
                  (B ≡ Unit → ⊥) →
                  IsBetaNormalForm body →
                  IsBetaNormalForm (inr {A} {B} ∘ body)
    inr-comp-nf _ body-nf (β-∘-l ())
    inr-comp-nf B≢Unit _ β-id-right = B≢Unit refl
    inr-comp-nf _ body-nf (β-∘-r r) = body-nf r

    -- In ∘ body where body : Term Unit (⟦ F ⟧F (μ F)) is β-nf
    -- Note: For K Unit, ⟦ K Unit ⟧F X = Unit, so body = id would type-check!
    -- But in that case, (In ∘ id) ⟶β In via β-id-right is a valid reduction.
    -- Our encodings never use In {K Unit} though - they use In {TyFuncF} or In {TermF}.
    -- So we need to take the functor F as explicit and require F ≠ K Unit.
    -- Actually, simpler: just require ⟦ F ⟧F (μ F) ≠ Unit.

    -- For In ∘ body, β-id-right requires body = id : Term A A (source = target).
    -- Since body : Term Unit B and id : Term A A requires A = Unit ∧ A = B,
    -- we need B = Unit. But we require B ≢ Unit, so this case is impossible.
    --
    -- Strategy: For functors where ⟦ F ⟧F (μ F) is definitionally ≠ Unit,
    -- Agda can see β-id-right is impossible. We inline the proof for our specific functors.
    In-comp-nf-TyFuncF : ∀ {body : Term Unit (⟦ TyFuncF ⟧F (μ TyFuncF))} →
                          IsBetaNormalForm body →
                          IsBetaNormalForm (In {TyFuncF} ∘ body)
    In-comp-nf-TyFuncF body-nf (β-∘-l ())
    In-comp-nf-TyFuncF body-nf (β-∘-r r) = body-nf r
    -- β-id-right is impossible: would need id : Term Unit (⟦ TyFuncF ⟧F (μ TyFuncF))
    -- but ⟦ TyFuncF ⟧F (μ TyFuncF) = (Unit + ...) ≠ Unit

    In-comp-nf-TermF : ∀ {body : Term Unit (⟦ TermF ⟧F (μ TermF))} →
                        IsBetaNormalForm body →
                        IsBetaNormalForm (In {TermF} ∘ body)
    In-comp-nf-TermF body-nf (β-∘-l ())
    In-comp-nf-TermF body-nf (β-∘-r r) = body-nf r
    -- β-id-right is impossible: ⟦ TermF ⟧F (μ TermF) = (TyFuncCode + ...) ≠ Unit

------------------------------------------------------------------------
-- Main Theorem: Encoded terms are in beta-normal form
--
-- PROOF OBLIGATION: The key insight is that all encoded terms have
-- the form `In ∘ inr^n ∘ [inl ∘] payload` where payload is built from
-- terminal, pairs, and recursive encodings. None of these match the
-- beta-redex patterns because:
--   1. In ∘ Out is impossible (sources don't match: Unit vs μ F)
--   2. id ∘ _ is impossible (head is In, not id)
--   3. All subterms are recursively beta-normal
--
-- The proof requires careful handling of type inference for deeply
-- nested sum types. This is marked as a postulate pending a complete
-- implementation that properly handles the type unification issues.
------------------------------------------------------------------------

postulate
  ⌜⌝Ty-betanf : ∀ A → IsBetaNormalForm (⌜ A ⌝Ty)
  ⌜⌝Func-betanf : ∀ F → IsBetaNormalForm (⌜ F ⌝Func)
  encode-is-betanf : ∀ {A B} (t : Term A B) → IsBetaNormalForm (encode t)
