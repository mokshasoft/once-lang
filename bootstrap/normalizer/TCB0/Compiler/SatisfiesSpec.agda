------------------------------------------------------------------------
-- SatisfiesSpec: Proof that normalize-step satisfies AlgebraSpec
--
-- This module proves that our concrete normalize-step algebra satisfies
-- the AlgebraSpec specification. This consists of:
--
--   For each position N: alg ∘ inj-N ⟶* In ∘ inj-N
--
-- Most handlers (14 out of 15) are trivial because they're just
-- rebuild-N = In ∘ inj-N. Only handle-comp needs a real proof,
-- which uses the is-id-noredex lemma.
--
-- Combined with SpecDerivedFixpoint, this gives us noredex-fixpoint.
------------------------------------------------------------------------

module normalizer.TCB0.Compiler.SatisfiesSpec where

open import normalizer.Syntax.Types
open import normalizer.Syntax.CCC
open import normalizer.Encoding.Encoding
open import normalizer.Syntax.NoRedex
open import normalizer.Combinators.ReductionCombinators
open import normalizer.Theory.Spec.AlgebraSpec

-- Import the handlers and normalize-step
open import normalizer.TCB0.Normalizer.Handlers
  using (normalize-step; normalize; handle-comp;
         handle-id; handle-fst; handle-snd; handle-pair;
         handle-inl; handle-inr; handle-case; handle-terminal;
         handle-initial; handle-In; handle-Out; handle-cata;
         handle-curry; handle-apply)

-- Import rebuild definitions (needed for definitional equality)
open import normalizer.TCB0.Normalizer.Rebuild
  using (rebuild-0; rebuild-1; rebuild-2; rebuild-3; rebuild-4;
         rebuild-5; rebuild-6; rebuild-7; rebuild-8; rebuild-9;
         rebuild-10; rebuild-11; rebuild-12; rebuild-13; rebuild-14)

-- Import the dispatch lemmas
open import normalizer.TCB0.Normalizer.Proofs.DispatchLemmas
  using (handle-comp-rebuild; nstep-at-1'; nstep-at-2'; nstep-at-3';
         nstep-at-4'; nstep-at-5'; nstep-at-6'; nstep-at-7'; nstep-at-8';
         nstep-at-9'; nstep-at-10'; nstep-at-11'; nstep-at-12'; nstep-at-13';
         nstep-at-14'; nstep-inl;
         ∘-cong-left'; ∘-cong-right')

------------------------------------------------------------------------
-- Helper: convert associativity for injection chains
------------------------------------------------------------------------

-- Right-associate a composition chain with payload
assoc-chain : ∀ {A B C D} {f : Term C D} {g : Term B C} {h : Term A B} →
              ((f ∘ g) ∘ h) ⟶* (f ∘ (g ∘ h))
assoc-chain = ⟶1 assoc-r

------------------------------------------------------------------------
-- Position 0 (id): normalize-step ∘ inl ⟶* In ∘ inl
------------------------------------------------------------------------

alg-at-id-proof : ∀ {A} →
  (normalize-step ∘ (inl ∘ ⌜ A ⌝Ty)) ⟶* (In {TermF} ∘ (inl ∘ ⌜ A ⌝Ty))
alg-at-id-proof {A} =
  -- normalize-step ∘ (inl ∘ ⌜ A ⌝Ty)
  -- ⟶ (normalize-step ∘ inl) ∘ ⌜ A ⌝Ty   [assoc-l]
  -- ⟶ handle-id ∘ ⌜ A ⌝Ty               [nstep-inl]
  -- = rebuild-0 ∘ ⌜ A ⌝Ty               [def of handle-id]
  -- = (In ∘ inl) ∘ ⌜ A ⌝Ty              [def of rebuild-0]
  -- ⟶ In ∘ (inl ∘ ⌜ A ⌝Ty)              [assoc-r]
  ⟶1 assoc-l >> ∘-cong-left' ⌜ A ⌝Ty (⟶1 nstep-inl) >> ⟶1 assoc-r

------------------------------------------------------------------------
-- Position 1 (comp): The non-trivial case - uses handle-comp-rebuild
------------------------------------------------------------------------

alg-at-comp-proof : ∀ {A B C} {f : Term B C} {g : Term A B} →
                    NoRedex f → NoRedex g →
                    NotIdStruct f → NotIdStruct g →
                    (normalize-step ∘ (inr ∘ inl ∘ ⟨ encode f , encode g ⟩)) ⟶*
                    (In {TermF} ∘ (inr ∘ inl ∘ ⟨ encode f , encode g ⟩))
alg-at-comp-proof {f = f} {g = g} nrf nrg nisf nisg =
  -- normalize-step ∘ inr ∘ inl ∘ payload
  -- ⟶* handle-comp ∘ payload   (by case dispatch)
  -- ⟶* (In ∘ inr ∘ inl) ∘ payload   (by handle-comp-rebuild)
  -- ⟶* In ∘ inr ∘ inl ∘ payload   (by associativity)
  step1 >> step2 >> step3
  where
    payload : Term Unit (TermCode' * TermCode')
    payload = ⟨ encode f , encode g ⟩

    -- Step 1: normalize-step ∘ inr ∘ inl ⟶ handle-comp
    step1 : (normalize-step ∘ inr ∘ inl ∘ payload) ⟶* (handle-comp ∘ payload)
    step1 = ⟶1 assoc-l >> ⟶1 assoc-l >> ∘-cong-left' payload nstep-at-1'

    -- Step 2: handle-comp ∘ payload ⟶* (In ∘ inr ∘ inl) ∘ payload
    step2 : (handle-comp ∘ payload) ⟶* ((In ∘ inr ∘ inl) ∘ payload)
    step2 = handle-comp-rebuild nrf nrg nisf nisg

    -- Step 3: (In ∘ inr ∘ inl) ∘ payload ⟶* In ∘ inr ∘ inl ∘ payload
    step3 : ((In ∘ inr ∘ inl) ∘ payload) ⟶* (In ∘ inr ∘ inl ∘ payload)
    step3 = ⟶1 assoc-r >> ∘-cong-right' In (⟶1 assoc-r)

------------------------------------------------------------------------
-- Position 2 (fst): normalize-step ∘ inr ∘ inr ∘ inl ⟶* In ∘ inr ∘ inr ∘ inl
------------------------------------------------------------------------

alg-at-fst-proof : ∀ {A B} →
  (normalize-step ∘ (inr ∘ inr ∘ inl ∘ ⟨ ⌜ A ⌝Ty , ⌜ B ⌝Ty ⟩)) ⟶*
  (In {TermF} ∘ (inr ∘ inr ∘ inl ∘ ⟨ ⌜ A ⌝Ty , ⌜ B ⌝Ty ⟩))
alg-at-fst-proof {A} {B} =
  let payload = ⟨ ⌜ A ⌝Ty , ⌜ B ⌝Ty ⟩ in
  -- dispatch to handle-fst = rebuild-2 = In ∘ inr ∘ inr ∘ inl
  ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >>
  ∘-cong-left' payload nstep-at-2' >>
  -- handle-fst = rebuild-2 = In ∘ inr ∘ inr ∘ inl, reassociate
  ⟶1 assoc-r >> ∘-cong-right' In (⟶1 assoc-r >> ∘-cong-right' inr (⟶1 assoc-r))

------------------------------------------------------------------------
-- Position 3 (snd)
------------------------------------------------------------------------

alg-at-snd-proof : ∀ {A B} →
  (normalize-step ∘ (inr ∘ inr ∘ inr ∘ inl ∘ ⟨ ⌜ A ⌝Ty , ⌜ B ⌝Ty ⟩)) ⟶*
  (In {TermF} ∘ (inr ∘ inr ∘ inr ∘ inl ∘ ⟨ ⌜ A ⌝Ty , ⌜ B ⌝Ty ⟩))
alg-at-snd-proof {A} {B} =
  let payload = ⟨ ⌜ A ⌝Ty , ⌜ B ⌝Ty ⟩ in
  ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >>
  ∘-cong-left' payload nstep-at-3' >>
  ⟶1 assoc-r >> ∘-cong-right' In (⟶1 assoc-r >> ∘-cong-right' inr (⟶1 assoc-r >> ∘-cong-right' inr (⟶1 assoc-r)))

------------------------------------------------------------------------
-- Position 4 (pair)
------------------------------------------------------------------------

alg-at-pair-proof : ∀ {C A B} {f : Term C A} {g : Term C B} →
  (normalize-step ∘ (inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ ⟨ encode f , encode g ⟩)) ⟶*
  (In {TermF} ∘ (inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ ⟨ encode f , encode g ⟩))
alg-at-pair-proof {f = f} {g = g} =
  let payload = ⟨ encode f , encode g ⟩ in
  ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >>
  ∘-cong-left' payload nstep-at-4' >>
  ⟶1 assoc-r >> ∘-cong-right' In (⟶1 assoc-r >> ∘-cong-right' inr (⟶1 assoc-r >> ∘-cong-right' inr (⟶1 assoc-r >> ∘-cong-right' inr (⟶1 assoc-r))))

------------------------------------------------------------------------
-- Position 5 (inl)
------------------------------------------------------------------------

alg-at-inl-proof : ∀ {A B} →
  (normalize-step ∘ (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ ⟨ ⌜ A ⌝Ty , ⌜ B ⌝Ty ⟩)) ⟶*
  (In {TermF} ∘ (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ ⟨ ⌜ A ⌝Ty , ⌜ B ⌝Ty ⟩))
alg-at-inl-proof {A} {B} =
  let payload = ⟨ ⌜ A ⌝Ty , ⌜ B ⌝Ty ⟩ in
  ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >>
  ∘-cong-left' payload nstep-at-5' >>
  ⟶1 assoc-r >> ∘-cong-right' In (⟶1 assoc-r >> ∘-cong-right' inr (⟶1 assoc-r >> ∘-cong-right' inr (⟶1 assoc-r >> ∘-cong-right' inr (⟶1 assoc-r >> ∘-cong-right' inr (⟶1 assoc-r)))))

------------------------------------------------------------------------
-- Position 6 (inr)
------------------------------------------------------------------------

alg-at-inr-proof : ∀ {A B} →
  (normalize-step ∘ (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ ⟨ ⌜ A ⌝Ty , ⌜ B ⌝Ty ⟩)) ⟶*
  (In {TermF} ∘ (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ ⟨ ⌜ A ⌝Ty , ⌜ B ⌝Ty ⟩))
alg-at-inr-proof {A} {B} =
  let payload = ⟨ ⌜ A ⌝Ty , ⌜ B ⌝Ty ⟩ in
  ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >>
  ∘-cong-left' payload nstep-at-6' >>
  ⟶1 assoc-r >> ∘-cong-right' In (⟶1 assoc-r >> ∘-cong-right' inr (⟶1 assoc-r >> ∘-cong-right' inr (⟶1 assoc-r >> ∘-cong-right' inr (⟶1 assoc-r >> ∘-cong-right' inr (⟶1 assoc-r >> ∘-cong-right' inr (⟶1 assoc-r))))))

------------------------------------------------------------------------
-- Position 7 (case)
------------------------------------------------------------------------

alg-at-case-proof : ∀ {A B C} {f : Term A C} {g : Term B C} →
  (normalize-step ∘ (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ ⟨ encode f , encode g ⟩)) ⟶*
  (In {TermF} ∘ (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ ⟨ encode f , encode g ⟩))
alg-at-case-proof {f = f} {g = g} =
  let payload = ⟨ encode f , encode g ⟩ in
  ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >>
  ∘-cong-left' payload nstep-at-7' >>
  ⟶1 assoc-r >> ∘-cong-right' In (⟶1 assoc-r >> ∘-cong-right' inr (⟶1 assoc-r >> ∘-cong-right' inr (⟶1 assoc-r >> ∘-cong-right' inr (⟶1 assoc-r >> ∘-cong-right' inr (⟶1 assoc-r >> ∘-cong-right' inr (⟶1 assoc-r >> ∘-cong-right' inr (⟶1 assoc-r)))))))

------------------------------------------------------------------------
-- Position 8 (terminal)
------------------------------------------------------------------------

alg-at-terminal-proof : ∀ {A} →
  (normalize-step ∘ (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ ⌜ A ⌝Ty)) ⟶*
  (In {TermF} ∘ (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ ⌜ A ⌝Ty))
alg-at-terminal-proof {A} =
  let payload = ⌜ A ⌝Ty in
  ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >>
  ∘-cong-left' payload nstep-at-8' >>
  ⟶1 assoc-r >> ∘-cong-right' In (⟶1 assoc-r >> ∘-cong-right' inr (⟶1 assoc-r >> ∘-cong-right' inr (⟶1 assoc-r >> ∘-cong-right' inr (⟶1 assoc-r >> ∘-cong-right' inr (⟶1 assoc-r >> ∘-cong-right' inr (⟶1 assoc-r >> ∘-cong-right' inr (⟶1 assoc-r >> ∘-cong-right' inr (⟶1 assoc-r))))))))

------------------------------------------------------------------------
-- Position 9 (initial)
------------------------------------------------------------------------

alg-at-initial-proof : ∀ {A} →
  (normalize-step ∘ (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ ⌜ A ⌝Ty)) ⟶*
  (In {TermF} ∘ (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ ⌜ A ⌝Ty))
alg-at-initial-proof {A} =
  let payload = ⌜ A ⌝Ty in
  ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >>
  ∘-cong-left' payload nstep-at-9' >>
  ⟶1 assoc-r >> ∘-cong-right' In (⟶1 assoc-r >> ∘-cong-right' inr (⟶1 assoc-r >> ∘-cong-right' inr (⟶1 assoc-r >> ∘-cong-right' inr (⟶1 assoc-r >> ∘-cong-right' inr (⟶1 assoc-r >> ∘-cong-right' inr (⟶1 assoc-r >> ∘-cong-right' inr (⟶1 assoc-r >> ∘-cong-right' inr (⟶1 assoc-r >> ∘-cong-right' inr (⟶1 assoc-r)))))))))

------------------------------------------------------------------------
-- Position 10 (In)
------------------------------------------------------------------------

alg-at-In-proof : ∀ {F} →
  (normalize-step ∘ (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ ⌜ F ⌝Func)) ⟶*
  (In {TermF} ∘ (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ ⌜ F ⌝Func))
alg-at-In-proof {F} =
  let payload = ⌜ F ⌝Func in
  ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >>
  ∘-cong-left' payload nstep-at-10' >>
  ⟶1 assoc-r >> ∘-cong-right' In (⟶1 assoc-r >> ∘-cong-right' inr (⟶1 assoc-r >> ∘-cong-right' inr (⟶1 assoc-r >> ∘-cong-right' inr (⟶1 assoc-r >> ∘-cong-right' inr (⟶1 assoc-r >> ∘-cong-right' inr (⟶1 assoc-r >> ∘-cong-right' inr (⟶1 assoc-r >> ∘-cong-right' inr (⟶1 assoc-r >> ∘-cong-right' inr (⟶1 assoc-r >> ∘-cong-right' inr (⟶1 assoc-r))))))))))

------------------------------------------------------------------------
-- Position 11 (Out)
------------------------------------------------------------------------

alg-at-Out-proof : ∀ {F} →
  (normalize-step ∘ (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ ⌜ F ⌝Func)) ⟶*
  (In {TermF} ∘ (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ ⌜ F ⌝Func))
alg-at-Out-proof {F} =
  let payload = ⌜ F ⌝Func in
  ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >>
  ∘-cong-left' payload nstep-at-11' >>
  ⟶1 assoc-r >> ∘-cong-right' In (⟶1 assoc-r >> ∘-cong-right' inr (⟶1 assoc-r >> ∘-cong-right' inr (⟶1 assoc-r >> ∘-cong-right' inr (⟶1 assoc-r >> ∘-cong-right' inr (⟶1 assoc-r >> ∘-cong-right' inr (⟶1 assoc-r >> ∘-cong-right' inr (⟶1 assoc-r >> ∘-cong-right' inr (⟶1 assoc-r >> ∘-cong-right' inr (⟶1 assoc-r >> ∘-cong-right' inr (⟶1 assoc-r >> ∘-cong-right' inr (⟶1 assoc-r)))))))))))

------------------------------------------------------------------------
-- Position 12 (cata)
------------------------------------------------------------------------

alg-at-cata-proof : ∀ {F A} {a : Term (⟦ F ⟧F A) A} →
  (normalize-step ∘ (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ ⟨ ⌜ F ⌝Func , encode a ⟩)) ⟶*
  (In {TermF} ∘ (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ ⟨ ⌜ F ⌝Func , encode a ⟩))
alg-at-cata-proof {F} {A} {a} =
  let payload = ⟨ ⌜ F ⌝Func , encode a ⟩ in
  ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >>
  ∘-cong-left' payload nstep-at-12' >>
  ⟶1 assoc-r >> ∘-cong-right' In (⟶1 assoc-r >> ∘-cong-right' inr (⟶1 assoc-r >> ∘-cong-right' inr (⟶1 assoc-r >> ∘-cong-right' inr (⟶1 assoc-r >> ∘-cong-right' inr (⟶1 assoc-r >> ∘-cong-right' inr (⟶1 assoc-r >> ∘-cong-right' inr (⟶1 assoc-r >> ∘-cong-right' inr (⟶1 assoc-r >> ∘-cong-right' inr (⟶1 assoc-r >> ∘-cong-right' inr (⟶1 assoc-r >> ∘-cong-right' inr (⟶1 assoc-r >> ∘-cong-right' inr (⟶1 assoc-r))))))))))))

------------------------------------------------------------------------
-- Position 13 (curry)
------------------------------------------------------------------------

alg-at-curry-proof : ∀ {A B C} {f : Term (A * B) C} →
  (normalize-step ∘ (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘
          ⟨ ⟨ ⌜ A ⌝Ty , ⌜ B ⌝Ty ⟩ , ⟨ ⌜ C ⌝Ty , encode f ⟩ ⟩)) ⟶*
  (In {TermF} ∘ (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘
          ⟨ ⟨ ⌜ A ⌝Ty , ⌜ B ⌝Ty ⟩ , ⟨ ⌜ C ⌝Ty , encode f ⟩ ⟩))
alg-at-curry-proof {A} {B} {C} {f} =
  let payload = ⟨ ⟨ ⌜ A ⌝Ty , ⌜ B ⌝Ty ⟩ , ⟨ ⌜ C ⌝Ty , encode f ⟩ ⟩ in
  ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >>
  ∘-cong-left' payload nstep-at-13' >>
  ⟶1 assoc-r >> ∘-cong-right' In (⟶1 assoc-r >> ∘-cong-right' inr (⟶1 assoc-r >> ∘-cong-right' inr (⟶1 assoc-r >> ∘-cong-right' inr (⟶1 assoc-r >> ∘-cong-right' inr (⟶1 assoc-r >> ∘-cong-right' inr (⟶1 assoc-r >> ∘-cong-right' inr (⟶1 assoc-r >> ∘-cong-right' inr (⟶1 assoc-r >> ∘-cong-right' inr (⟶1 assoc-r >> ∘-cong-right' inr (⟶1 assoc-r >> ∘-cong-right' inr (⟶1 assoc-r >> ∘-cong-right' inr (⟶1 assoc-r >> ∘-cong-right' inr (⟶1 assoc-r)))))))))))))

------------------------------------------------------------------------
-- Position 14 (apply)
------------------------------------------------------------------------

alg-at-apply-proof : ∀ {A B} →
  (normalize-step ∘ (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ ⟨ ⌜ A ⌝Ty , ⌜ B ⌝Ty ⟩)) ⟶*
  (In {TermF} ∘ (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ ⟨ ⌜ A ⌝Ty , ⌜ B ⌝Ty ⟩))
alg-at-apply-proof {A} {B} =
  let payload = ⟨ ⌜ A ⌝Ty , ⌜ B ⌝Ty ⟩ in
  ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >>
  ∘-cong-left' payload nstep-at-14' >>
  ⟶1 assoc-r >> ∘-cong-right' In (⟶1 assoc-r >> ∘-cong-right' inr (⟶1 assoc-r >> ∘-cong-right' inr (⟶1 assoc-r >> ∘-cong-right' inr (⟶1 assoc-r >> ∘-cong-right' inr (⟶1 assoc-r >> ∘-cong-right' inr (⟶1 assoc-r >> ∘-cong-right' inr (⟶1 assoc-r >> ∘-cong-right' inr (⟶1 assoc-r >> ∘-cong-right' inr (⟶1 assoc-r >> ∘-cong-right' inr (⟶1 assoc-r >> ∘-cong-right' inr (⟶1 assoc-r >> ∘-cong-right' inr (⟶1 assoc-r >> ∘-cong-right' inr (⟶1 assoc-r)))))))))))))

------------------------------------------------------------------------
-- The AlgebraSpec instance for normalize-step
------------------------------------------------------------------------

normalize-algebra-spec : AlgebraSpec normalize-step
normalize-algebra-spec = record
  { alg-at-id       = alg-at-id-proof
  ; alg-at-comp     = alg-at-comp-proof
  ; alg-at-fst      = alg-at-fst-proof
  ; alg-at-snd      = alg-at-snd-proof
  ; alg-at-pair     = alg-at-pair-proof
  ; alg-at-inl      = alg-at-inl-proof
  ; alg-at-inr      = alg-at-inr-proof
  ; alg-at-case     = alg-at-case-proof
  ; alg-at-terminal = alg-at-terminal-proof
  ; alg-at-initial  = alg-at-initial-proof
  ; alg-at-In       = alg-at-In-proof
  ; alg-at-Out      = alg-at-Out-proof
  ; alg-at-cata     = alg-at-cata-proof
  ; alg-at-curry    = alg-at-curry-proof
  ; alg-at-apply    = alg-at-apply-proof
  }

------------------------------------------------------------------------
-- Re-export the existing fixpoint proof
--
-- For now, we still use the direct proof from Fixpoint/MainTheorem.
-- Once SpecDerivedFixpoint is complete, fixpoint will be derived
-- from normalize-algebra-spec.
------------------------------------------------------------------------

open import normalizer.TCB0.Normalizer.SelfFixpoint
  using (noredex-fixpoint)
  public

-- Alias: spec-implies-fixpoint is the same as noredex-fixpoint
spec-implies-fixpoint : ∀ {A B} (t : Term A B) → NoRedex t →
                        (normalize ∘ encode t) ⟶* encode t
spec-implies-fixpoint = noredex-fixpoint

------------------------------------------------------------------------
-- NormalizerSpecSimple instance
------------------------------------------------------------------------

open import normalizer.Theory.Spec.NormalizerSpec

normalize-spec : NormalizerSpecSimple normalize-step
normalize-spec = record
  { alg-comp-noredex = alg-at-comp-proof
  }

------------------------------------------------------------------------
-- Summary of what we export:
--
--   normalize-algebra-spec : AlgebraSpec normalize-step
--   normalize-spec : NormalizerSpecSimple normalize-step
--   noredex-fixpoint : ∀ t → NoRedex t → (normalize ∘ encode t) ⟶* encode t
--   spec-implies-fixpoint : alias for noredex-fixpoint
--
-- The architecture is:
--   1. AlgebraSpec defines per-position conditions for fixpoint
--   2. This module proves normalize-step satisfies AlgebraSpec
--   3. (TODO) SpecDerivedFixpoint derives fixpoint from AlgebraSpec
------------------------------------------------------------------------
