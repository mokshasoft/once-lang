------------------------------------------------------------------------
-- RefoldIdempotent: The identity algebra case
--
-- This module proves that cata TermF In (the "refold" operation)
-- is idempotent on all encoded terms:
--
--   ∀ t. (cata TermF In) ∘ encode(t) ⟶* encode(t)
--
-- This is the fundamental fixpoint property for the identity algebra,
-- which is reusable for any CCC encoding scheme.
--
-- The proof is by structural induction on terms:
-- - K-based positions (non-recursive): fmap gives id, trivial
-- - Id-based positions (recursive): mutual recursion with refold-idempotent
------------------------------------------------------------------------

module normalizer.TCB0.RefoldIdempotent where

open import normalizer.Encoding.TermFunctor public
open import normalizer.Encoding.Encoding public
open import normalizer.Combinators.DispatchCombinators
  using (assoc-sandwich; pair-ih-step; _>>inr_; assoc-r-In; _>>_)

------------------------------------------------------------------------
-- The identity algebra
------------------------------------------------------------------------

refold-algebra : Term (⟦ TermF ⟧F TermCode') TermCode'
refold-algebra = In

N-refold : Term TermCode' TermCode'
N-refold = cata TermF refold-algebra

------------------------------------------------------------------------
-- Proof of refold-idem-id (position 0)
------------------------------------------------------------------------

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
    inner-step : ((In ∘ fmap TermF (cata TermF In)) ∘ inl) ⟶* (In ∘ inl)
    inner-step =
      ⟶*-trans
        (step assoc-r done)  -- (In ∘ fmap...) ∘ inl ⟶ In ∘ (fmap... ∘ inl)
        (∘-cong-right' In (fmap-TermF-inl (cata TermF In)))  -- In ∘ (fmap ∘ inl) ⟶* In ∘ inl

    step3 : (((In ∘ fmap TermF (cata TermF In)) ∘ inl) ∘ ⌜ A ⌝Ty) ⟶*
            (In ∘ (inl ∘ ⌜ A ⌝Ty))
    step3 = ⟶*-trans
              (∘-cong-left' (⌜ A ⌝Ty) inner-step)  -- reduce inner part
              (step assoc-r done)                   -- reassociate

------------------------------------------------------------------------
-- K-based refold-idem proofs (non-recursive)
------------------------------------------------------------------------

-- refold-idem-fst: position 2 (2 inrs before inl)
refold-idem-fst : ∀ {A B} → (cata TermF In ∘ encode (fst {A} {B})) ⟶* encode (fst {A} {B})
refold-idem-fst {A} {B} = ⟶*-trans step1 step2
  where
    payload : Term Unit (TyFuncCode * TyFuncCode)
    payload = ⟨ ⌜ A ⌝Ty , ⌜ B ⌝Ty ⟩

    f : Term TermCode' TermCode'
    f = cata TermF In

    step1 = cata-β-right

    r0 = assoc-sandwich _ (fmap-TermF-inr f)
    r1 = assoc-sandwich _ (fmap-1-inr f)

    r2 : (fmap TermF-2 f ∘ (inl ∘ payload)) ⟶* (inl ∘ payload)
    r2 = ⟶*-trans (step assoc-l done)
           (⟶*-trans (∘-cong-left' payload (fmap-2-inl f))
             (⟶*-trans (step assoc-r done)
               (⟶*-trans (∘-cong-right' inl
                 (⟶*-trans (∘-cong-left' payload (fmap-KK-id TyFuncCode TyFuncCode f))
                   (step id-left done)))
                 done)))

    reduce-chain = r0 >>inr r1 >>inr r2

    step2 = assoc-r-In reduce-chain

-- refold-idem-snd: position 3
refold-idem-snd : ∀ {A B} → (cata TermF In ∘ encode (snd {A} {B})) ⟶* encode (snd {A} {B})
refold-idem-snd {A} {B} = ⟶*-trans step1 step2
  where
    payload : Term Unit (TyFuncCode * TyFuncCode)
    payload = ⟨ ⌜ A ⌝Ty , ⌜ B ⌝Ty ⟩

    f : Term TermCode' TermCode'
    f = cata TermF In

    step1 = cata-β-right

    r0 = assoc-sandwich _ (fmap-TermF-inr f)
    r1 = assoc-sandwich _ (fmap-1-inr f)
    r2 = assoc-sandwich _ (fmap-2-inr f)

    r3 : (fmap TermF-3 f ∘ (inl ∘ payload)) ⟶* (inl ∘ payload)
    r3 = ⟶*-trans (step assoc-l done)
           (⟶*-trans (∘-cong-left' payload (fmap-3-inl f))
             (⟶*-trans (step assoc-r done)
               (⟶*-trans (∘-cong-right' inl
                 (⟶*-trans (∘-cong-left' payload (fmap-KK-id TyFuncCode TyFuncCode f))
                   (step id-left done)))
                 done)))

    reduce-chain = r0 >>inr r1 >>inr r2 >>inr r3

    step2 = assoc-r-In reduce-chain

-- refold-idem-inl: position 5
refold-idem-inl : ∀ {A B} → (cata TermF In ∘ encode (inl {A} {B})) ⟶* encode (inl {A} {B})
refold-idem-inl {A} {B} = ⟶*-trans step1 step2
  where
    payload : Term Unit (TyFuncCode * TyFuncCode)
    payload = ⟨ ⌜ A ⌝Ty , ⌜ B ⌝Ty ⟩

    f : Term TermCode' TermCode'
    f = cata TermF In

    step1 = cata-β-right

    r0 = assoc-sandwich _ (fmap-TermF-inr f)
    r1 = assoc-sandwich _ (fmap-1-inr f)
    r2 = assoc-sandwich _ (fmap-2-inr f)
    r3 = assoc-sandwich _ (fmap-3-inr f)
    r4 = assoc-sandwich _ (fmap-4-inr f)
    r5 : (fmap TermF-5 f ∘ (inl ∘ payload)) ⟶* (inl ∘ payload)
    r5 = ⟶*-trans (step assoc-l done)
           (⟶*-trans (∘-cong-left' payload (fmap-5-inl f))
             (⟶*-trans (step assoc-r done)
               (⟶*-trans (∘-cong-right' inl
                 (⟶*-trans (∘-cong-left' payload (fmap-KK-id TyFuncCode TyFuncCode f))
                   (step id-left done)))
                 done)))

    reduce-chain = r0 >>inr r1 >>inr r2 >>inr r3 >>inr r4 >>inr r5

    step2 = assoc-r-In reduce-chain

-- refold-idem-inr: position 6
refold-idem-inr : ∀ {A B} → (cata TermF In ∘ encode (inr {A} {B})) ⟶* encode (inr {A} {B})
refold-idem-inr {A} {B} = ⟶*-trans step1 step2
  where
    payload : Term Unit (TyFuncCode * TyFuncCode)
    payload = ⟨ ⌜ A ⌝Ty , ⌜ B ⌝Ty ⟩

    f : Term TermCode' TermCode'
    f = cata TermF In

    step1 = cata-β-right

    r0 = assoc-sandwich _ (fmap-TermF-inr f)
    r1 = assoc-sandwich _ (fmap-1-inr f)
    r2 = assoc-sandwich _ (fmap-2-inr f)
    r3 = assoc-sandwich _ (fmap-3-inr f)
    r4 = assoc-sandwich _ (fmap-4-inr f)
    r5 = assoc-sandwich _ (fmap-5-inr f)
    r6 : (fmap TermF-6 f ∘ (inl ∘ payload)) ⟶* (inl ∘ payload)
    r6 = ⟶*-trans (step assoc-l done)
           (⟶*-trans (∘-cong-left' payload (fmap-6-inl f))
             (⟶*-trans (step assoc-r done)
               (⟶*-trans (∘-cong-right' inl
                 (⟶*-trans (∘-cong-left' payload (fmap-KK-id TyFuncCode TyFuncCode f))
                   (step id-left done)))
                 done)))

    reduce-chain = r0 >>inr r1 >>inr r2 >>inr r3 >>inr r4 >>inr r5 >>inr r6

    step2 = assoc-r-In reduce-chain

-- refold-idem-terminal: position 8
refold-idem-terminal : ∀ {A} → (cata TermF In ∘ encode (terminal {A})) ⟶* encode (terminal {A})
refold-idem-terminal {A} = ⟶*-trans step1 step2
  where
    payload : Term Unit TyFuncCode
    payload = ⌜ A ⌝Ty

    f : Term TermCode' TermCode'
    f = cata TermF In

    step1 = cata-β-right

    r0 = assoc-sandwich _ (fmap-TermF-inr f)
    r1 = assoc-sandwich _ (fmap-1-inr f)
    r2 = assoc-sandwich _ (fmap-2-inr f)
    r3 = assoc-sandwich _ (fmap-3-inr f)
    r4 = assoc-sandwich _ (fmap-4-inr f)
    r5 = assoc-sandwich _ (fmap-5-inr f)
    r6 = assoc-sandwich _ (fmap-6-inr f)
    r7 = assoc-sandwich _ (fmap-7-inr f)
    r8 = step assoc-l done >>
         ∘-cong-left' payload (fmap-8-inl f) >>
         ∘-cong-left' payload (step id-right done)

    reduce-chain = r0 >>inr r1 >>inr r2 >>inr r3 >>inr r4 >>inr r5 >>inr r6 >>inr r7 >>inr r8

    step2 = assoc-r-In reduce-chain

-- refold-idem-initial: position 9
refold-idem-initial : ∀ {A} → (cata TermF In ∘ encode (initial {A})) ⟶* encode (initial {A})
refold-idem-initial {A} = ⟶*-trans step1 step2
  where
    payload : Term Unit TyFuncCode
    payload = ⌜ A ⌝Ty

    f : Term TermCode' TermCode'
    f = cata TermF In

    step1 = cata-β-right

    r0 = assoc-sandwich _ (fmap-TermF-inr f)
    r1 = assoc-sandwich _ (fmap-1-inr f)
    r2 = assoc-sandwich _ (fmap-2-inr f)
    r3 = assoc-sandwich _ (fmap-3-inr f)
    r4 = assoc-sandwich _ (fmap-4-inr f)
    r5 = assoc-sandwich _ (fmap-5-inr f)
    r6 = assoc-sandwich _ (fmap-6-inr f)
    r7 = assoc-sandwich _ (fmap-7-inr f)
    r8 = assoc-sandwich _ (fmap-8-inr f)
    r9 = step assoc-l done >>
         ∘-cong-left' payload (fmap-9-inl f) >>
         ∘-cong-left' payload (step id-right done)

    reduce-chain = r0 >>inr r1 >>inr r2 >>inr r3 >>inr r4 >>inr r5 >>inr r6 >>inr r7 >>inr r8 >>inr r9

    step2 = assoc-r-In reduce-chain

-- refold-idem-In: position 10
refold-idem-In : ∀ {F} → (cata TermF In ∘ encode (In {F})) ⟶* encode (In {F})
refold-idem-In {F} = ⟶*-trans step1 step2
  where
    payload : Term Unit TyFuncCode
    payload = ⌜ F ⌝Func

    f : Term TermCode' TermCode'
    f = cata TermF In

    step1 = cata-β-right

    r0 = assoc-sandwich _ (fmap-TermF-inr f)
    r1 = assoc-sandwich _ (fmap-1-inr f)
    r2 = assoc-sandwich _ (fmap-2-inr f)
    r3 = assoc-sandwich _ (fmap-3-inr f)
    r4 = assoc-sandwich _ (fmap-4-inr f)
    r5 = assoc-sandwich _ (fmap-5-inr f)
    r6 = assoc-sandwich _ (fmap-6-inr f)
    r7 = assoc-sandwich _ (fmap-7-inr f)
    r8 = assoc-sandwich _ (fmap-8-inr f)
    r9 = assoc-sandwich _ (fmap-9-inr f)
    r10 = step assoc-l done >>
          ∘-cong-left' payload (fmap-10-inl f) >>
          ∘-cong-left' payload (step id-right done)

    reduce-chain = r0 >>inr r1 >>inr r2 >>inr r3 >>inr r4 >>inr r5 >>inr r6 >>inr r7 >>inr r8 >>inr r9 >>inr r10

    step2 = assoc-r-In reduce-chain

-- refold-idem-Out: position 11
refold-idem-Out : ∀ {F} → (cata TermF In ∘ encode (Out {F})) ⟶* encode (Out {F})
refold-idem-Out {F} = ⟶*-trans step1 step2
  where
    payload : Term Unit TyFuncCode
    payload = ⌜ F ⌝Func

    f : Term TermCode' TermCode'
    f = cata TermF In

    step1 = cata-β-right

    r0 = assoc-sandwich _ (fmap-TermF-inr f)
    r1 = assoc-sandwich _ (fmap-1-inr f)
    r2 = assoc-sandwich _ (fmap-2-inr f)
    r3 = assoc-sandwich _ (fmap-3-inr f)
    r4 = assoc-sandwich _ (fmap-4-inr f)
    r5 = assoc-sandwich _ (fmap-5-inr f)
    r6 = assoc-sandwich _ (fmap-6-inr f)
    r7 = assoc-sandwich _ (fmap-7-inr f)
    r8 = assoc-sandwich _ (fmap-8-inr f)
    r9 = assoc-sandwich _ (fmap-9-inr f)
    r10 = assoc-sandwich _ (fmap-10-inr f)
    r11 = step assoc-l done >>
          ∘-cong-left' payload (fmap-11-inl f) >>
          ∘-cong-left' payload (step id-right done)

    reduce-chain = r0 >>inr r1 >>inr r2 >>inr r3 >>inr r4 >>inr r5 >>inr r6 >>inr r7 >>inr r8 >>inr r9 >>inr r10 >>inr r11

    step2 = assoc-r-In reduce-chain

-- refold-idem-apply: position 14
refold-idem-apply : ∀ {A B} → (cata TermF In ∘ encode (apply {A} {B})) ⟶* encode (apply {A} {B})
refold-idem-apply {A} {B} = ⟶*-trans step1 step2
  where
    payload : Term Unit (TyFuncCode * TyFuncCode)
    payload = ⟨ ⌜ A ⌝Ty , ⌜ B ⌝Ty ⟩

    c : Term TermCode' TermCode'
    c = cata TermF In

    step1 = cata-β-right

    r0 = assoc-sandwich _ (fmap-TermF-inr c)
    r1 = assoc-sandwich _ (fmap-1-inr c)
    r2 = assoc-sandwich _ (fmap-2-inr c)
    r3 = assoc-sandwich _ (fmap-3-inr c)
    r4 = assoc-sandwich _ (fmap-4-inr c)
    r5 = assoc-sandwich _ (fmap-5-inr c)
    r6 = assoc-sandwich _ (fmap-6-inr c)
    r7 = assoc-sandwich _ (fmap-7-inr c)
    r8 = assoc-sandwich _ (fmap-8-inr c)
    r9 = assoc-sandwich _ (fmap-9-inr c)
    r10 = assoc-sandwich _ (fmap-10-inr c)
    r11 = assoc-sandwich _ (fmap-11-inr c)
    r12 = assoc-sandwich _ (fmap-12-inr c)
    r13 = assoc-sandwich _ (fmap-13-inr c)

    r14 : (fmap TermF-14 c ∘ payload) ⟶* payload
    r14 = ⟶*-trans (∘-cong-left' payload (fmap-KK-id TyFuncCode TyFuncCode c)) (step id-left done)

    reduce-chain = r0 >>inr r1 >>inr r2 >>inr r3 >>inr r4 >>inr r5 >>inr r6 >>inr r7 >>inr r8 >>inr r9 >>inr r10 >>inr r11 >>inr r12 >>inr r13 >>inr r14

    step2 = assoc-r-In reduce-chain

------------------------------------------------------------------------
-- Id-based refold-idem proofs (recursive)
--
-- These cases need mutual recursion with refold-idempotent.
------------------------------------------------------------------------

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
  refold-idem-comp : ∀ {A B C} (f : Term B C) (g : Term A B) →
                     (cata TermF In ∘ encode (f ∘ g)) ⟶* encode (f ∘ g)
  refold-idem-comp {A} {B} {C} f g = ⟶*-trans step1 step2
    where
      payload : Term Unit (TermCode' * TermCode')
      payload = ⟨ encode f , encode g ⟩

      c : Term TermCode' TermCode'
      c = cata TermF In

      step1 = cata-β-right

      r0 : (fmap TermF c ∘ (inr ∘ (inl ∘ payload))) ⟶*
           (inr ∘ (fmap TermF-1 c ∘ (inl ∘ payload)))
      r0 = assoc-sandwich _ (fmap-TermF-inr c)

      ih-step : (fmap (Id ⊗ Id) c ∘ payload) ⟶* payload
      ih-step = pair-ih-step (refold-idempotent f) (refold-idempotent g)

      r1 : (fmap TermF-1 c ∘ (inl ∘ payload)) ⟶* (inl ∘ payload)
      r1 = ⟶*-trans (step assoc-l done)
             (⟶*-trans (∘-cong-left' payload (fmap-1-inl c))
               (⟶*-trans (step assoc-r done)
                 (∘-cong-right' inl ih-step)))

      reduce-chain : (fmap TermF c ∘ (inr ∘ (inl ∘ payload))) ⟶*
                     (inr ∘ (inl ∘ payload))
      reduce-chain = r0 >>inr r1

      step2 = assoc-r-In reduce-chain

  -- refold-idem-pair: position 4
  refold-idem-pair : ∀ {A B C} (f : Term C A) (g : Term C B) →
                     (cata TermF In ∘ encode ⟨ f , g ⟩) ⟶* encode ⟨ f , g ⟩
  refold-idem-pair {A} {B} {C} f g = ⟶*-trans step1 step2
    where
      payload : Term Unit (TermCode' * TermCode')
      payload = ⟨ encode f , encode g ⟩

      c : Term TermCode' TermCode'
      c = cata TermF In

      step1 = cata-β-right

      r0 = assoc-sandwich _ (fmap-TermF-inr c)
      r1 = assoc-sandwich _ (fmap-1-inr c)
      r2 = assoc-sandwich _ (fmap-2-inr c)
      r3 = assoc-sandwich _ (fmap-3-inr c)

      ih-step : (fmap (Id ⊗ Id) c ∘ payload) ⟶* payload
      ih-step = pair-ih-step (refold-idempotent f) (refold-idempotent g)

      r4 : (fmap TermF-4 c ∘ (inl ∘ payload)) ⟶* (inl ∘ payload)
      r4 = ⟶*-trans (step assoc-l done)
             (⟶*-trans (∘-cong-left' payload (fmap-4-inl c))
               (⟶*-trans (step assoc-r done)
                 (∘-cong-right' inl ih-step)))

      reduce-chain = r0 >>inr r1 >>inr r2 >>inr r3 >>inr r4

      step2 = assoc-r-In reduce-chain

  -- refold-idem-case: position 7
  refold-idem-case : ∀ {A B C} (f : Term A C) (g : Term B C) →
                     (cata TermF In ∘ encode [ f , g ]) ⟶* encode [ f , g ]
  refold-idem-case {A} {B} {C} f g = ⟶*-trans step1 step2
    where
      payload : Term Unit (TermCode' * TermCode')
      payload = ⟨ encode f , encode g ⟩

      c : Term TermCode' TermCode'
      c = cata TermF In

      step1 = cata-β-right

      r0 = assoc-sandwich _ (fmap-TermF-inr c)
      r1 = assoc-sandwich _ (fmap-1-inr c)
      r2 = assoc-sandwich _ (fmap-2-inr c)
      r3 = assoc-sandwich _ (fmap-3-inr c)
      r4 = assoc-sandwich _ (fmap-4-inr c)
      r5 = assoc-sandwich _ (fmap-5-inr c)
      r6 = assoc-sandwich _ (fmap-6-inr c)

      ih-step : (fmap (Id ⊗ Id) c ∘ payload) ⟶* payload
      ih-step = pair-ih-step (refold-idempotent f) (refold-idempotent g)

      r7 : (fmap TermF-7 c ∘ (inl ∘ payload)) ⟶* (inl ∘ payload)
      r7 = ⟶*-trans (step assoc-l done)
             (⟶*-trans (∘-cong-left' payload (fmap-7-inl c))
               (⟶*-trans (step assoc-r done)
                 (∘-cong-right' inl ih-step)))

      reduce-chain = r0 >>inr r1 >>inr r2 >>inr r3 >>inr r4 >>inr r5 >>inr r6 >>inr r7

      step2 = assoc-r-In reduce-chain

  -- refold-idem-cata: position 12
  refold-idem-cata : ∀ {F A} (alg : Term (⟦ F ⟧F A) A) →
                     (cata TermF In ∘ encode (cata F alg)) ⟶* encode (cata F alg)
  refold-idem-cata {F} {A} alg = ⟶*-trans step1 step2
    where
      payload : Term Unit (TyFuncCode * TermCode')
      payload = ⟨ ⌜ F ⌝Func , encode alg ⟩

      c : Term TermCode' TermCode'
      c = cata TermF In

      step1 = cata-β-right

      r0 = assoc-sandwich _ (fmap-TermF-inr c)
      r1 = assoc-sandwich _ (fmap-1-inr c)
      r2 = assoc-sandwich _ (fmap-2-inr c)
      r3 = assoc-sandwich _ (fmap-3-inr c)
      r4 = assoc-sandwich _ (fmap-4-inr c)
      r5 = assoc-sandwich _ (fmap-5-inr c)
      r6 = assoc-sandwich _ (fmap-6-inr c)
      r7 = assoc-sandwich _ (fmap-7-inr c)
      r8 = assoc-sandwich _ (fmap-8-inr c)
      r9 = assoc-sandwich _ (fmap-9-inr c)
      r10 = assoc-sandwich _ (fmap-10-inr c)
      r11 = assoc-sandwich _ (fmap-11-inr c)

      r12-inl : (fmap TermF-12 c ∘ inl) ⟶* (inl ∘ fmap (K TyFuncCode ⊗ Id) c)
      r12-inl = fmap-sum-inl (K TyFuncCode ⊗ Id) TermF-13 c

      r12-payload : (fmap (K TyFuncCode ⊗ Id) c ∘ payload) ⟶* payload
      r12-payload =
        ⟶*-trans (step pair-comp done)
          (⟨⟩-cong
            (⟶*-trans (step assoc-r done)
              (⟶*-trans (step id-left done)
                (step fst-pair done)))
            (⟶*-trans (step assoc-r done)
              (⟶*-trans (∘-cong-right' c (step snd-pair done))
                (refold-idempotent alg))))

      r12 : (fmap TermF-12 c ∘ (inl ∘ payload)) ⟶* (inl ∘ payload)
      r12 = ⟶*-trans (step assoc-l done)
              (⟶*-trans (∘-cong-left' _ r12-inl)
                (⟶*-trans (step assoc-r done)
                  (∘-cong-right' inl r12-payload)))

      reduce-chain = r0 >>inr r1 >>inr r2 >>inr r3 >>inr r4 >>inr r5 >>inr r6 >>inr r7 >>inr r8 >>inr r9 >>inr r10 >>inr r11 >>inr r12

      step2 = assoc-r-In reduce-chain

  -- refold-idem-curry: position 13
  refold-idem-curry : ∀ {A B C} (f : Term (A * B) C) →
                      (cata TermF In ∘ encode (curry f)) ⟶* encode (curry f)
  refold-idem-curry {A} {B} {C} f = ⟶*-trans step1 step2
    where
      payload : Term Unit ((TyFuncCode * TyFuncCode) * (TyFuncCode * TermCode'))
      payload = ⟨ ⟨ ⌜ A ⌝Ty , ⌜ B ⌝Ty ⟩ , ⟨ ⌜ C ⌝Ty , encode f ⟩ ⟩

      c : Term TermCode' TermCode'
      c = cata TermF In

      step1 = cata-β-right

      r0 = assoc-sandwich _ (fmap-TermF-inr c)
      r1 = assoc-sandwich _ (fmap-1-inr c)
      r2 = assoc-sandwich _ (fmap-2-inr c)
      r3 = assoc-sandwich _ (fmap-3-inr c)
      r4 = assoc-sandwich _ (fmap-4-inr c)
      r5 = assoc-sandwich _ (fmap-5-inr c)
      r6 = assoc-sandwich _ (fmap-6-inr c)
      r7 = assoc-sandwich _ (fmap-7-inr c)
      r8 = assoc-sandwich _ (fmap-8-inr c)
      r9 = assoc-sandwich _ (fmap-9-inr c)
      r10 = assoc-sandwich _ (fmap-10-inr c)
      r11 = assoc-sandwich _ (fmap-11-inr c)
      r12 = assoc-sandwich _ (fmap-12-inr c)

      CurryF = (K TyFuncCode ⊗ K TyFuncCode) ⊗ (K TyFuncCode ⊗ Id)
      r13-inl : (fmap TermF-13 c ∘ inl) ⟶* (inl ∘ fmap CurryF c)
      r13-inl = fmap-sum-inl CurryF TermF-14 c

      r13-payload : (fmap CurryF c ∘ payload) ⟶* payload
      r13-payload =
        ⟶*-trans (step pair-comp done)
          (⟨⟩-cong
            (⟶*-trans (step assoc-r done)
              (⟶*-trans (∘-cong-right' (fmap (K TyFuncCode ⊗ K TyFuncCode) c) (step fst-pair done))
                (⟶*-trans (∘-cong-left' _ (fmap-KK-id TyFuncCode TyFuncCode c))
                  (step id-left done))))
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

      reduce-chain = r0 >>inr r1 >>inr r2 >>inr r3 >>inr r4 >>inr r5 >>inr r6 >>inr r7 >>inr r8 >>inr r9 >>inr r10 >>inr r11 >>inr r12 >>inr r13

      step2 = assoc-r-In reduce-chain

------------------------------------------------------------------------
-- The N-refold fixpoint theorem
------------------------------------------------------------------------

N-refold-fixpoint : (N-refold ∘ encode N-refold) ⟶* encode N-refold
N-refold-fixpoint = refold-idempotent N-refold
