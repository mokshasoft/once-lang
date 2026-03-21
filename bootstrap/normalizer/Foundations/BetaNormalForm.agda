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

    -- Helper: inl has no direct β-reductions
    inl-no-β : ∀ {A B} {u : Term A (A + B)} → inl {A} {B} ⟶β u → ⊥
    inl-no-β ()

    -- Helper: inr has no direct β-reductions
    inr-no-β : ∀ {A B} {u : Term B (A + B)} → inr {A} {B} ⟶β u → ⊥
    inr-no-β ()

  abstract
    -- inl ∘ terminal is β-nf: inl ≠ id, terminal ≠ id
    -- Cases: β-id-left needs head=id (but inl≠id), β-id-right needs tail=id (but terminal≠id)
    --        β-∘-l needs inl to reduce (impossible), β-∘-r needs terminal to reduce (impossible)
    inl-terminal-nf : ∀ {B} → IsBetaNormalForm (inl {Unit} {B} ∘ terminal {Unit})
    inl-terminal-nf (β-∘-l r) = inl-no-β r
    inl-terminal-nf (β-∘-r r) = terminal-nf r
    -- β-id-left, β-id-right ruled out by constructor mismatch (inl≠id, terminal≠id)

    -- inr ∘ terminal is β-nf: inr ≠ id, terminal ≠ id
    inr-terminal-nf : ∀ {A} → IsBetaNormalForm (inr {A} {Unit} ∘ terminal {Unit})
    inr-terminal-nf (β-∘-l r) = inr-no-β r
    inr-terminal-nf (β-∘-r r) = terminal-nf r
    -- β-id-left, β-id-right ruled out by constructor mismatch (inr≠id, terminal≠id)

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
-- Key insight: All encoded terms have the form
--   In ∘ inr^n ∘ [inl ∘] payload
-- where payload is terminal, pairs, or recursive encodings.
--
-- None match beta-redex patterns because:
--   1. In ∘ Out is impossible (Out not in encoding bodies)
--   2. id ∘ _ is impossible (head is In/inl/inr, not id)
--   3. All subterms are recursively beta-normal
------------------------------------------------------------------------

-- Proving type/func encoding cases with mutual recursion
mutual
  abstract
    -- ⌜ Void ⌝Ty = In ∘ inl ∘ terminal
    ⌜Void⌝-betanf : IsBetaNormalForm (⌜ Void ⌝Ty)
    ⌜Void⌝-betanf = In-comp-nf-TyFuncF inl-terminal-nf

    -- ⌜ Unit ⌝Ty = In ∘ inr ∘ inl ∘ terminal
    ⌜Unit⌝-betanf : IsBetaNormalForm (⌜ Unit ⌝Ty)
    ⌜Unit⌝-betanf = In-comp-nf-TyFuncF (inr-comp-nf Sum≢Unit inl-terminal-nf)

    -- ⌜ A * B ⌝Ty = In ∘ inr ∘ inr ∘ inl ∘ ⟨ ⌜ A ⌝Ty , ⌜ B ⌝Ty ⟩
    ⌜*⌝-betanf : ∀ A B → IsBetaNormalForm (⌜ A * B ⌝Ty)
    ⌜*⌝-betanf A B = In-comp-nf-TyFuncF
      (inr-comp-nf Sum≢Unit
        (inr-comp-nf Sum≢Unit
          (inl-comp-nf Prod≢Unit
            (pair-nf (⌜⌝Ty-betanf A) (⌜⌝Ty-betanf B)))))

    -- ⌜ A + B ⌝Ty = In ∘ inr ∘ inr ∘ inr ∘ inl ∘ ⟨ ⌜ A ⌝Ty , ⌜ B ⌝Ty ⟩
    ⌜+⌝-betanf : ∀ A B → IsBetaNormalForm (⌜ A + B ⌝Ty)
    ⌜+⌝-betanf A B = In-comp-nf-TyFuncF
      (inr-comp-nf Sum≢Unit
        (inr-comp-nf Sum≢Unit
          (inr-comp-nf Sum≢Unit
            (inl-comp-nf Prod≢Unit
              (pair-nf (⌜⌝Ty-betanf A) (⌜⌝Ty-betanf B))))))

    -- ⌜ A ⇒ B ⌝Ty = In ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ ⟨ ⌜ A ⌝Ty , ⌜ B ⌝Ty ⟩
    ⌜⇒⌝-betanf : ∀ A B → IsBetaNormalForm (⌜ A ⇒ B ⌝Ty)
    ⌜⇒⌝-betanf A B = In-comp-nf-TyFuncF
      (inr-comp-nf Sum≢Unit
        (inr-comp-nf Sum≢Unit
          (inr-comp-nf Sum≢Unit
            (inr-comp-nf Sum≢Unit
              (inl-comp-nf Prod≢Unit
                (pair-nf (⌜⌝Ty-betanf A) (⌜⌝Ty-betanf B)))))))

    -- ⌜ μ F ⌝Ty = In ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ ⌜ F ⌝Func
    ⌜μ⌝-betanf : ∀ F → IsBetaNormalForm (⌜ μ F ⌝Ty)
    ⌜μ⌝-betanf F = In-comp-nf-TyFuncF
      (inr-comp-nf Sum≢Unit
        (inr-comp-nf Sum≢Unit
          (inr-comp-nf Sum≢Unit
            (inr-comp-nf Sum≢Unit
              (inr-comp-nf Sum≢Unit
                (inl-comp-nf TyFuncCode≢Unit (⌜⌝Func-betanf F)))))))

    -- Main type encoding theorem
    ⌜⌝Ty-betanf : ∀ A → IsBetaNormalForm (⌜ A ⌝Ty)
    ⌜⌝Ty-betanf Void = ⌜Void⌝-betanf
    ⌜⌝Ty-betanf Unit = ⌜Unit⌝-betanf
    ⌜⌝Ty-betanf (A * B) = ⌜*⌝-betanf A B
    ⌜⌝Ty-betanf (A + B) = ⌜+⌝-betanf A B
    ⌜⌝Ty-betanf (A ⇒ B) = ⌜⇒⌝-betanf A B
    ⌜⌝Ty-betanf (μ F) = ⌜μ⌝-betanf F

    -- ⌜ Id ⌝Func = In ∘ inr^6 ∘ inl ∘ terminal
    ⌜Id⌝-betanf : IsBetaNormalForm (⌜ Id ⌝Func)
    ⌜Id⌝-betanf = In-comp-nf-TyFuncF
      (inr-comp-nf Sum≢Unit
        (inr-comp-nf Sum≢Unit
          (inr-comp-nf Sum≢Unit
            (inr-comp-nf Sum≢Unit
              (inr-comp-nf Sum≢Unit
                (inr-comp-nf Sum≢Unit
                  inl-terminal-nf))))))

    -- ⌜ K A ⌝Func = In ∘ inr^7 ∘ inl ∘ ⌜ A ⌝Ty
    ⌜K⌝-betanf : ∀ A → IsBetaNormalForm (⌜ K A ⌝Func)
    ⌜K⌝-betanf A = In-comp-nf-TyFuncF
      (inr-comp-nf Sum≢Unit
        (inr-comp-nf Sum≢Unit
          (inr-comp-nf Sum≢Unit
            (inr-comp-nf Sum≢Unit
              (inr-comp-nf Sum≢Unit
                (inr-comp-nf Sum≢Unit
                  (inr-comp-nf Sum≢Unit
                    (inl-comp-nf TyFuncCode≢Unit (⌜⌝Ty-betanf A)))))))))

    -- ⌜ F ⊕ G ⌝Func = In ∘ inr^8 ∘ inl ∘ ⟨ ⌜ F ⌝Func , ⌜ G ⌝Func ⟩
    ⌜⊕⌝-betanf : ∀ F G → IsBetaNormalForm (⌜ F ⊕ G ⌝Func)
    ⌜⊕⌝-betanf F G = In-comp-nf-TyFuncF
      (inr-comp-nf Sum≢Unit
        (inr-comp-nf Sum≢Unit
          (inr-comp-nf Sum≢Unit
            (inr-comp-nf Sum≢Unit
              (inr-comp-nf Sum≢Unit
                (inr-comp-nf Sum≢Unit
                  (inr-comp-nf Sum≢Unit
                    (inr-comp-nf Sum≢Unit
                      (inl-comp-nf Prod≢Unit
                        (pair-nf (⌜⌝Func-betanf F) (⌜⌝Func-betanf G)))))))))))

    -- ⌜ F ⊗ G ⌝Func = In ∘ inr^9 ∘ ⟨ ⌜ F ⌝Func , ⌜ G ⌝Func ⟩ (no inl - last alternative)
    ⌜⊗⌝-betanf : ∀ F G → IsBetaNormalForm (⌜ F ⊗ G ⌝Func)
    ⌜⊗⌝-betanf F G = In-comp-nf-TyFuncF
      (inr-comp-nf Sum≢Unit
        (inr-comp-nf Sum≢Unit
          (inr-comp-nf Sum≢Unit
            (inr-comp-nf Sum≢Unit
              (inr-comp-nf Sum≢Unit
                (inr-comp-nf Sum≢Unit
                  (inr-comp-nf Sum≢Unit
                    (inr-comp-nf Sum≢Unit
                      (inr-comp-nf Prod≢Unit
                        (pair-nf (⌜⌝Func-betanf F) (⌜⌝Func-betanf G)))))))))))

    -- Main functor encoding theorem
    ⌜⌝Func-betanf : ∀ F → IsBetaNormalForm (⌜ F ⌝Func)
    ⌜⌝Func-betanf Id = ⌜Id⌝-betanf
    ⌜⌝Func-betanf (K A) = ⌜K⌝-betanf A
    ⌜⌝Func-betanf (F ⊕ G) = ⌜⊕⌝-betanf F G
    ⌜⌝Func-betanf (F ⊗ G) = ⌜⊗⌝-betanf F G

-- Term encoding proofs (mutual recursion for recursive cases)
-- encode produces: In ∘ inr^n ∘ [inl ∘] payload
-- where payload is ⌜_⌝Ty, ⟨encode, encode⟩, etc.
mutual
 abstract
  -- Main theorem: All encoded terms are beta-normal (forward declaration for mutual)
  encode-is-betanf : ∀ {A B} (t : Term A B) → IsBetaNormalForm (encode t)

  -- Helper for chains in term encoding
  -- 0: encode id = In ∘ inl ∘ ⌜ A ⌝Ty
  encode-id-nf : ∀ A → IsBetaNormalForm (encode (id {A}))
  encode-id-nf A = In-comp-nf-TermF (inl-comp-nf TyFuncCode≢Unit (⌜⌝Ty-betanf A))

  -- 1: encode (f ∘ g) = In ∘ inr ∘ inl ∘ ⟨ encode f , encode g ⟩
  encode-comp-nf : ∀ {A B C} (f : Term B C) (g : Term A B) →
                   IsBetaNormalForm (encode (f ∘ g))
  encode-comp-nf f g = In-comp-nf-TermF
    (inr-comp-nf Sum≢Unit
      (inl-comp-nf Prod≢Unit
        (pair-nf (encode-is-betanf f) (encode-is-betanf g))))

  -- 2: encode fst = In ∘ inr^2 ∘ inl ∘ ⟨ ⌜ A ⌝Ty , ⌜ B ⌝Ty ⟩
  encode-fst-nf : ∀ A B → IsBetaNormalForm (encode (fst {A} {B}))
  encode-fst-nf A B = In-comp-nf-TermF
    (inr-comp-nf Sum≢Unit
      (inr-comp-nf Sum≢Unit
        (inl-comp-nf Prod≢Unit
          (pair-nf (⌜⌝Ty-betanf A) (⌜⌝Ty-betanf B)))))

  -- 3: encode snd = In ∘ inr^3 ∘ inl ∘ ⟨ ⌜ A ⌝Ty , ⌜ B ⌝Ty ⟩
  encode-snd-nf : ∀ A B → IsBetaNormalForm (encode (snd {A} {B}))
  encode-snd-nf A B = In-comp-nf-TermF
    (inr-comp-nf Sum≢Unit
      (inr-comp-nf Sum≢Unit
        (inr-comp-nf Sum≢Unit
          (inl-comp-nf Prod≢Unit
            (pair-nf (⌜⌝Ty-betanf A) (⌜⌝Ty-betanf B))))))

  -- 4: encode ⟨ f , g ⟩ = In ∘ inr^4 ∘ inl ∘ ⟨ encode f , encode g ⟩
  encode-pair-nf : ∀ {A B C} (f : Term C A) (g : Term C B) →
                   IsBetaNormalForm (encode ⟨ f , g ⟩)
  encode-pair-nf f g = In-comp-nf-TermF
    (inr-comp-nf Sum≢Unit
      (inr-comp-nf Sum≢Unit
        (inr-comp-nf Sum≢Unit
          (inr-comp-nf Sum≢Unit
            (inl-comp-nf Prod≢Unit
              (pair-nf (encode-is-betanf f) (encode-is-betanf g)))))))

  -- 5: encode inl = In ∘ inr^5 ∘ inl ∘ ⟨ ⌜ A ⌝Ty , ⌜ B ⌝Ty ⟩
  encode-inl-nf : ∀ A B → IsBetaNormalForm (encode (inl {A} {B}))
  encode-inl-nf A B = In-comp-nf-TermF
    (inr-comp-nf Sum≢Unit
      (inr-comp-nf Sum≢Unit
        (inr-comp-nf Sum≢Unit
          (inr-comp-nf Sum≢Unit
            (inr-comp-nf Sum≢Unit
              (inl-comp-nf Prod≢Unit
                (pair-nf (⌜⌝Ty-betanf A) (⌜⌝Ty-betanf B))))))))

  -- 6: encode inr = In ∘ inr^6 ∘ inl ∘ ⟨ ⌜ A ⌝Ty , ⌜ B ⌝Ty ⟩
  encode-inr-nf : ∀ A B → IsBetaNormalForm (encode (inr {A} {B}))
  encode-inr-nf A B = In-comp-nf-TermF
    (inr-comp-nf Sum≢Unit
      (inr-comp-nf Sum≢Unit
        (inr-comp-nf Sum≢Unit
          (inr-comp-nf Sum≢Unit
            (inr-comp-nf Sum≢Unit
              (inr-comp-nf Sum≢Unit
                (inl-comp-nf Prod≢Unit
                  (pair-nf (⌜⌝Ty-betanf A) (⌜⌝Ty-betanf B)))))))))

  -- 7: encode [ f , g ] = In ∘ inr^7 ∘ inl ∘ ⟨ encode f , encode g ⟩
  encode-case-nf : ∀ {A B C} (f : Term A C) (g : Term B C) →
                   IsBetaNormalForm (encode [ f , g ])
  encode-case-nf f g = In-comp-nf-TermF
    (inr-comp-nf Sum≢Unit
      (inr-comp-nf Sum≢Unit
        (inr-comp-nf Sum≢Unit
          (inr-comp-nf Sum≢Unit
            (inr-comp-nf Sum≢Unit
              (inr-comp-nf Sum≢Unit
                (inr-comp-nf Sum≢Unit
                  (inl-comp-nf Prod≢Unit
                    (pair-nf (encode-is-betanf f) (encode-is-betanf g))))))))))

  -- 8: encode terminal = In ∘ inr^8 ∘ inl ∘ ⌜ A ⌝Ty
  encode-terminal-nf : ∀ A → IsBetaNormalForm (encode (terminal {A}))
  encode-terminal-nf A = In-comp-nf-TermF
    (inr-comp-nf Sum≢Unit
      (inr-comp-nf Sum≢Unit
        (inr-comp-nf Sum≢Unit
          (inr-comp-nf Sum≢Unit
            (inr-comp-nf Sum≢Unit
              (inr-comp-nf Sum≢Unit
                (inr-comp-nf Sum≢Unit
                  (inr-comp-nf Sum≢Unit
                    (inl-comp-nf TyFuncCode≢Unit (⌜⌝Ty-betanf A))))))))))

  -- 9: encode initial = In ∘ inr^9 ∘ inl ∘ ⌜ A ⌝Ty
  encode-initial-nf : ∀ A → IsBetaNormalForm (encode (initial {A}))
  encode-initial-nf A = In-comp-nf-TermF
    (inr-comp-nf Sum≢Unit
      (inr-comp-nf Sum≢Unit
        (inr-comp-nf Sum≢Unit
          (inr-comp-nf Sum≢Unit
            (inr-comp-nf Sum≢Unit
              (inr-comp-nf Sum≢Unit
                (inr-comp-nf Sum≢Unit
                  (inr-comp-nf Sum≢Unit
                    (inr-comp-nf Sum≢Unit
                      (inl-comp-nf TyFuncCode≢Unit (⌜⌝Ty-betanf A)))))))))))

  -- 10: encode In = In ∘ inr^10 ∘ inl ∘ ⌜ F ⌝Func
  encode-In-nf : ∀ F → IsBetaNormalForm (encode (In {F}))
  encode-In-nf F = In-comp-nf-TermF
    (inr-comp-nf Sum≢Unit
      (inr-comp-nf Sum≢Unit
        (inr-comp-nf Sum≢Unit
          (inr-comp-nf Sum≢Unit
            (inr-comp-nf Sum≢Unit
              (inr-comp-nf Sum≢Unit
                (inr-comp-nf Sum≢Unit
                  (inr-comp-nf Sum≢Unit
                    (inr-comp-nf Sum≢Unit
                      (inr-comp-nf Sum≢Unit
                        (inl-comp-nf TyFuncCode≢Unit (⌜⌝Func-betanf F))))))))))))

  -- 11: encode Out = In ∘ inr^11 ∘ inl ∘ ⌜ F ⌝Func
  encode-Out-nf : ∀ F → IsBetaNormalForm (encode (Out {F}))
  encode-Out-nf F = In-comp-nf-TermF
    (inr-comp-nf Sum≢Unit
      (inr-comp-nf Sum≢Unit
        (inr-comp-nf Sum≢Unit
          (inr-comp-nf Sum≢Unit
            (inr-comp-nf Sum≢Unit
              (inr-comp-nf Sum≢Unit
                (inr-comp-nf Sum≢Unit
                  (inr-comp-nf Sum≢Unit
                    (inr-comp-nf Sum≢Unit
                      (inr-comp-nf Sum≢Unit
                        (inr-comp-nf Sum≢Unit
                          (inl-comp-nf TyFuncCode≢Unit (⌜⌝Func-betanf F)))))))))))))

  -- 12: encode (cata F alg) = In ∘ inr^12 ∘ inl ∘ ⟨ ⌜ F ⌝Func , encode alg ⟩
  encode-cata-nf : ∀ F {A} (alg : Term (⟦ F ⟧F A) A) →
                   IsBetaNormalForm (encode (cata F alg))
  encode-cata-nf F alg = In-comp-nf-TermF
    (inr-comp-nf Sum≢Unit
      (inr-comp-nf Sum≢Unit
        (inr-comp-nf Sum≢Unit
          (inr-comp-nf Sum≢Unit
            (inr-comp-nf Sum≢Unit
              (inr-comp-nf Sum≢Unit
                (inr-comp-nf Sum≢Unit
                  (inr-comp-nf Sum≢Unit
                    (inr-comp-nf Sum≢Unit
                      (inr-comp-nf Sum≢Unit
                        (inr-comp-nf Sum≢Unit
                          (inr-comp-nf Sum≢Unit
                            (inl-comp-nf Prod≢Unit
                              (pair-nf (⌜⌝Func-betanf F) (encode-is-betanf alg)))))))))))))))

  -- 13: encode (curry f) = In ∘ inr^13 ∘ inl ∘ ⟨ ⟨ ⌜A⌝, ⌜B⌝ ⟩ , ⟨ ⌜C⌝, encode f ⟩ ⟩
  encode-curry-nf : ∀ A B C (f : Term (A * B) C) →
                    IsBetaNormalForm (encode (curry f))
  encode-curry-nf A B C f = In-comp-nf-TermF
    (inr-comp-nf Sum≢Unit
      (inr-comp-nf Sum≢Unit
        (inr-comp-nf Sum≢Unit
          (inr-comp-nf Sum≢Unit
            (inr-comp-nf Sum≢Unit
              (inr-comp-nf Sum≢Unit
                (inr-comp-nf Sum≢Unit
                  (inr-comp-nf Sum≢Unit
                    (inr-comp-nf Sum≢Unit
                      (inr-comp-nf Sum≢Unit
                        (inr-comp-nf Sum≢Unit
                          (inr-comp-nf Sum≢Unit
                            (inr-comp-nf Sum≢Unit
                              (inl-comp-nf Prod≢Unit
                                (pair-nf
                                  (pair-nf (⌜⌝Ty-betanf A) (⌜⌝Ty-betanf B))
                                  (pair-nf (⌜⌝Ty-betanf C) (encode-is-betanf f)))))))))))))))))

  -- 14: encode apply = In ∘ inr^14 ∘ ⟨ ⌜ A ⌝Ty , ⌜ B ⌝Ty ⟩ (no inl - last alternative)
  encode-apply-nf : ∀ A B → IsBetaNormalForm (encode (apply {A} {B}))
  encode-apply-nf A B = In-comp-nf-TermF
    (inr-comp-nf Sum≢Unit
      (inr-comp-nf Sum≢Unit
        (inr-comp-nf Sum≢Unit
          (inr-comp-nf Sum≢Unit
            (inr-comp-nf Sum≢Unit
              (inr-comp-nf Sum≢Unit
                (inr-comp-nf Sum≢Unit
                  (inr-comp-nf Sum≢Unit
                    (inr-comp-nf Sum≢Unit
                      (inr-comp-nf Sum≢Unit
                        (inr-comp-nf Sum≢Unit
                          (inr-comp-nf Sum≢Unit
                            (inr-comp-nf Sum≢Unit
                              (inr-comp-nf Prod≢Unit
                                (pair-nf (⌜⌝Ty-betanf A) (⌜⌝Ty-betanf B))))))))))))))))

  -- Main theorem implementation (type declared above)
  encode-is-betanf (id {A}) = encode-id-nf A
  encode-is-betanf (f ∘ g) = encode-comp-nf f g
  encode-is-betanf (fst {A} {B}) = encode-fst-nf A B
  encode-is-betanf (snd {A} {B}) = encode-snd-nf A B
  encode-is-betanf ⟨ f , g ⟩ = encode-pair-nf f g
  encode-is-betanf (inl {A} {B}) = encode-inl-nf A B
  encode-is-betanf (inr {A} {B}) = encode-inr-nf A B
  encode-is-betanf [ f , g ] = encode-case-nf f g
  encode-is-betanf (terminal {A}) = encode-terminal-nf A
  encode-is-betanf (initial {A}) = encode-initial-nf A
  encode-is-betanf (In {F}) = encode-In-nf F
  encode-is-betanf (Out {F}) = encode-Out-nf F
  encode-is-betanf (cata F alg) = encode-cata-nf F alg
  encode-is-betanf (curry {A} {B} {C} f) = encode-curry-nf A B C f
  encode-is-betanf (apply {A} {B}) = encode-apply-nf A B
