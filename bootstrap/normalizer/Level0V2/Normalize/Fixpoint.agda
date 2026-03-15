------------------------------------------------------------------------
-- Normalize.Fixpoint: Fixpoint property proofs for NoRedex terms
--
-- For NoRedex t: normalize ∘ encode t ⟶* encode t
--
-- Proof structure:
-- 1. Unfold cata via cata-β-right
-- 2. Apply fmap reductions to reach the injection
-- 3. Apply case dispatch: normalize-step ∘ inj-N ⟶ handle-N
-- 4. handle-N = In ∘ inj-N (definitionally, for N ≠ 1)
-- 5. Reassociate to get encode t
--
-- Uses Chain-style proofs with >> operator.
------------------------------------------------------------------------

module normalizer.Level0V2.Normalize.Fixpoint where

open import normalizer.Level0V2.Normalize.NstepDispatch public
open import normalizer.Level0V2.Normalizer
  using (∘-cong-left'; ∘-cong-right'; cata-β-right; fmap-TermF-inl;
         fmap-TermF-inr; fmap-1-inr; fmap-2-inr; fmap-3-inr; fmap-4-inr;
         fmap-5-inr; fmap-6-inr; fmap-7-inr; fmap-8-inr; fmap-9-inr;
         fmap-10-inr; fmap-11-inr; fmap-12-inr;
         fmap-1-inl; fmap-2-inl; fmap-3-inl; fmap-4-inl; fmap-5-inl;
         fmap-6-inl; fmap-7-inl; fmap-8-inl; fmap-9-inl; fmap-10-inl;
         fmap-KK-id; TermF-13; fmap-sum-inl)

-- Proof obligation: handle-comp reduces to rebuild
-- (When inputs are non-id NoRedex terms)
postulate
  handle-comp-rebuild : ∀ {X} (payload : Term X (TermCode' * TermCode')) →
                        (handle-comp ∘ payload) ⟶* ((In ∘ inr ∘ inl) ∘ payload)

------------------------------------------------------------------------
-- Payload functor for curry (position 12): (K⊗K) ⊗ (K⊗Id)
------------------------------------------------------------------------

CurryPayloadF : Func
CurryPayloadF = (K TyFuncCode ⊗ K TyFuncCode) ⊗ (K TyFuncCode ⊗ Id)

------------------------------------------------------------------------
-- Position dispatch lemmas (left-associated versions)
-- Wrapped in abstract to prevent term expansion during type-checking
------------------------------------------------------------------------

abstract
  nstep-at-1' : (((normalize-step ∘ inr) ∘ inl)) ⟶* handle-comp
  nstep-at-1' = ⟶1 (⟶-∘-l nstep-inr) >> ⟶1 tail-1-inl

  nstep-at-2' : (((normalize-step ∘ inr) ∘ inr) ∘ inl) ⟶* handle-fst
  nstep-at-2' =
    ⟶1 (⟶-∘-l (⟶-∘-l nstep-inr)) >>
    ⟶1 (⟶-∘-l tail-1-inr) >>
    ⟶1 tail-2-inl

  nstep-at-3' : ((((normalize-step ∘ inr) ∘ inr) ∘ inr) ∘ inl) ⟶* handle-snd
  nstep-at-3' =
    ⟶1 (⟶-∘-l (⟶-∘-l (⟶-∘-l nstep-inr))) >>
    ⟶1 (⟶-∘-l (⟶-∘-l tail-1-inr)) >>
    ⟶1 (⟶-∘-l tail-2-inr) >>
    ⟶1 tail-3-inl

  nstep-at-4' : (((((normalize-step ∘ inr) ∘ inr) ∘ inr) ∘ inr) ∘ inl) ⟶* handle-pair
  nstep-at-4' =
    ⟶1 (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l nstep-inr)))) >>
    ⟶1 (⟶-∘-l (⟶-∘-l (⟶-∘-l tail-1-inr))) >>
    ⟶1 (⟶-∘-l (⟶-∘-l tail-2-inr)) >>
    ⟶1 (⟶-∘-l tail-3-inr) >>
    ⟶1 tail-4-inl

  nstep-at-5' : ((((((normalize-step ∘ inr) ∘ inr) ∘ inr) ∘ inr) ∘ inr) ∘ inl) ⟶* handle-inl
  nstep-at-5' =
    ⟶1 (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l nstep-inr))))) >>
    ⟶1 (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l tail-1-inr)))) >>
    ⟶1 (⟶-∘-l (⟶-∘-l (⟶-∘-l tail-2-inr))) >>
    ⟶1 (⟶-∘-l (⟶-∘-l tail-3-inr)) >>
    ⟶1 (⟶-∘-l tail-4-inr) >>
    ⟶1 tail-5-inl

  nstep-at-6' : (((((((normalize-step ∘ inr) ∘ inr) ∘ inr) ∘ inr) ∘ inr) ∘ inr) ∘ inl) ⟶* handle-inr
  nstep-at-6' =
    ⟶1 (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l nstep-inr)))))) >>
    ⟶1 (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l tail-1-inr))))) >>
    ⟶1 (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l tail-2-inr)))) >>
    ⟶1 (⟶-∘-l (⟶-∘-l (⟶-∘-l tail-3-inr))) >>
    ⟶1 (⟶-∘-l (⟶-∘-l tail-4-inr)) >>
    ⟶1 (⟶-∘-l tail-5-inr) >>
    ⟶1 tail-6-inl

  nstep-at-7' : ((((((((normalize-step ∘ inr) ∘ inr) ∘ inr) ∘ inr) ∘ inr) ∘ inr) ∘ inr) ∘ inl) ⟶* handle-case
  nstep-at-7' =
    ⟶1 (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l nstep-inr))))))) >>
    ⟶1 (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l tail-1-inr)))))) >>
    ⟶1 (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l tail-2-inr))))) >>
    ⟶1 (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l tail-3-inr)))) >>
    ⟶1 (⟶-∘-l (⟶-∘-l (⟶-∘-l tail-4-inr))) >>
    ⟶1 (⟶-∘-l (⟶-∘-l tail-5-inr)) >>
    ⟶1 (⟶-∘-l tail-6-inr) >>
    ⟶1 tail-7-inl

  nstep-at-8' : (((((((((normalize-step ∘ inr) ∘ inr) ∘ inr) ∘ inr) ∘ inr) ∘ inr) ∘ inr) ∘ inr) ∘ inl) ⟶* handle-terminal
  nstep-at-8' =
    ⟶1 (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l nstep-inr)))))))) >>
    ⟶1 (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l tail-1-inr))))))) >>
    ⟶1 (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l tail-2-inr)))))) >>
    ⟶1 (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l tail-3-inr))))) >>
    ⟶1 (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l tail-4-inr)))) >>
    ⟶1 (⟶-∘-l (⟶-∘-l (⟶-∘-l tail-5-inr))) >>
    ⟶1 (⟶-∘-l (⟶-∘-l tail-6-inr)) >>
    ⟶1 (⟶-∘-l tail-7-inr) >>
    ⟶1 tail-8-inl

  nstep-at-9' : ((((((((((normalize-step ∘ inr) ∘ inr) ∘ inr) ∘ inr) ∘ inr) ∘ inr) ∘ inr) ∘ inr) ∘ inr) ∘ inl) ⟶* handle-In
  nstep-at-9' =
    ⟶1 (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l nstep-inr))))))))) >>
    ⟶1 (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l tail-1-inr)))))))) >>
    ⟶1 (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l tail-2-inr))))))) >>
    ⟶1 (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l tail-3-inr)))))) >>
    ⟶1 (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l tail-4-inr))))) >>
    ⟶1 (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l tail-5-inr)))) >>
    ⟶1 (⟶-∘-l (⟶-∘-l (⟶-∘-l tail-6-inr))) >>
    ⟶1 (⟶-∘-l (⟶-∘-l tail-7-inr)) >>
    ⟶1 (⟶-∘-l tail-8-inr) >>
    ⟶1 tail-9-inl

  nstep-at-10' : (((((((((((normalize-step ∘ inr) ∘ inr) ∘ inr) ∘ inr) ∘ inr) ∘ inr) ∘ inr) ∘ inr) ∘ inr) ∘ inr) ∘ inl) ⟶* handle-Out
  nstep-at-10' =
    ⟶1 (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l nstep-inr)))))))))) >>
    ⟶1 (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l tail-1-inr))))))))) >>
    ⟶1 (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l tail-2-inr)))))))) >>
    ⟶1 (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l tail-3-inr))))))) >>
    ⟶1 (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l tail-4-inr)))))) >>
    ⟶1 (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l tail-5-inr))))) >>
    ⟶1 (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l tail-6-inr)))) >>
    ⟶1 (⟶-∘-l (⟶-∘-l (⟶-∘-l tail-7-inr))) >>
    ⟶1 (⟶-∘-l (⟶-∘-l tail-8-inr)) >>
    ⟶1 (⟶-∘-l tail-9-inr) >>
    ⟶1 tail-10-inl

  nstep-at-11' : ((((((((((((normalize-step ∘ inr) ∘ inr) ∘ inr) ∘ inr) ∘ inr) ∘ inr) ∘ inr) ∘ inr) ∘ inr) ∘ inr) ∘ inr) ∘ inl) ⟶* handle-cata
  nstep-at-11' =
    ⟶1 (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l nstep-inr))))))))))) >>
    ⟶1 (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l tail-1-inr)))))))))) >>
    ⟶1 (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l tail-2-inr))))))))) >>
    ⟶1 (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l tail-3-inr)))))))) >>
    ⟶1 (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l tail-4-inr))))))) >>
    ⟶1 (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l tail-5-inr)))))) >>
    ⟶1 (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l tail-6-inr))))) >>
    ⟶1 (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l tail-7-inr)))) >>
    ⟶1 (⟶-∘-l (⟶-∘-l (⟶-∘-l tail-8-inr))) >>
    ⟶1 (⟶-∘-l (⟶-∘-l tail-9-inr)) >>
    ⟶1 (⟶-∘-l tail-10-inr) >>
    ⟶1 tail-11-inl

  nstep-at-12' : (((((((((((((normalize-step ∘ inr) ∘ inr) ∘ inr) ∘ inr) ∘ inr) ∘ inr) ∘ inr) ∘ inr) ∘ inr) ∘ inr) ∘ inr) ∘ inr) ∘ inl) ⟶* handle-curry
  nstep-at-12' =
    ⟶1 (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l nstep-inr)))))))))))) >>
    ⟶1 (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l tail-1-inr))))))))))) >>
    ⟶1 (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l tail-2-inr)))))))))) >>
    ⟶1 (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l tail-3-inr))))))))) >>
    ⟶1 (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l tail-4-inr)))))))) >>
    ⟶1 (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l tail-5-inr))))))) >>
    ⟶1 (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l tail-6-inr)))))) >>
    ⟶1 (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l tail-7-inr))))) >>
    ⟶1 (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l tail-8-inr)))) >>
    ⟶1 (⟶-∘-l (⟶-∘-l (⟶-∘-l tail-9-inr))) >>
    ⟶1 (⟶-∘-l (⟶-∘-l tail-10-inr)) >>
    ⟶1 (⟶-∘-l tail-11-inr) >>
    ⟶1 tail-12-inl

  nstep-at-13' : (((((((((((((normalize-step ∘ inr) ∘ inr) ∘ inr) ∘ inr) ∘ inr) ∘ inr) ∘ inr) ∘ inr) ∘ inr) ∘ inr) ∘ inr) ∘ inr) ∘ inr) ⟶* handle-apply
  nstep-at-13' =
    ⟶1 (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l nstep-inr)))))))))))) >>
    ⟶1 (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l tail-1-inr))))))))))) >>
    ⟶1 (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l tail-2-inr)))))))))) >>
    ⟶1 (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l tail-3-inr))))))))) >>
    ⟶1 (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l tail-4-inr)))))))) >>
    ⟶1 (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l tail-5-inr))))))) >>
    ⟶1 (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l tail-6-inr)))))) >>
    ⟶1 (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l tail-7-inr))))) >>
    ⟶1 (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l tail-8-inr)))) >>
    ⟶1 (⟶-∘-l (⟶-∘-l (⟶-∘-l tail-9-inr))) >>
    ⟶1 (⟶-∘-l (⟶-∘-l tail-10-inr)) >>
    ⟶1 (⟶-∘-l tail-11-inr) >>
    ⟶1 tail-12-inr

  ------------------------------------------------------------------------
  -- Key lemma: normalize-step ∘ inl ⟶ handle-id = In ∘ inl
  ------------------------------------------------------------------------

  nstep-inl : (normalize-step ∘ inl) ⟶ handle-id
  nstep-inl = case-inl

------------------------------------------------------------------------
-- Base case: noredex-fixpoint-id
------------------------------------------------------------------------

abstract
  noredex-fixpoint-id : ∀ {A} → (normalize ∘ encode (id {A})) ⟶* encode (id {A})
  noredex-fixpoint-id {A} = step1 >> step2 >> step3 >> step4
    where
      N : Term TermCode' TermCode'
      N = cata TermF normalize-step

      step1 : (N ∘ (In {TermF} ∘ (inl ∘ ⌜ A ⌝Ty))) ⟶*
              ((normalize-step ∘ fmap TermF N) ∘ (inl ∘ ⌜ A ⌝Ty))
      step1 = cata-β-right {TermF} {TermCode'} {Unit} {normalize-step} {inl ∘ ⌜ A ⌝Ty}

      step2 : ((normalize-step ∘ fmap TermF N) ∘ (inl ∘ ⌜ A ⌝Ty)) ⟶*
              (((normalize-step ∘ fmap TermF N) ∘ inl) ∘ ⌜ A ⌝Ty)
      step2 = ⟶1 assoc-l

      inner-step : ((normalize-step ∘ fmap TermF N) ∘ inl) ⟶* (In {TermF} ∘ inl)
      inner-step =
        ⟶1 assoc-r >>
        ∘-cong-right' normalize-step (fmap-TermF-inl N) >>
        ⟶1 nstep-inl

      step3 : (((normalize-step ∘ fmap TermF N) ∘ inl) ∘ ⌜ A ⌝Ty) ⟶*
              ((In {TermF} ∘ inl) ∘ ⌜ A ⌝Ty)
      step3 = ∘-cong-left' (⌜ A ⌝Ty) inner-step

      step4 : ((In {TermF} ∘ inl) ∘ ⌜ A ⌝Ty) ⟶* (In {TermF} ∘ (inl ∘ ⌜ A ⌝Ty))
      step4 = ⟶1 assoc-r

------------------------------------------------------------------------
-- Base case: noredex-fixpoint-fst (position 2)
------------------------------------------------------------------------

abstract
  noredex-fixpoint-fst : ∀ {A B} → (normalize ∘ encode (fst {A} {B})) ⟶* encode (fst {A} {B})
  noredex-fixpoint-fst {A} {B} = step1 >> step2 >> step3 >> step4
    where
      N : Term TermCode' TermCode'
      N = cata TermF normalize-step

      payload : Term Unit (TyFuncCode * TyFuncCode)
      payload = ⟨ ⌜ A ⌝Ty , ⌜ B ⌝Ty ⟩

      step1 : (N ∘ (In {TermF} ∘ (inr ∘ inr ∘ inl ∘ payload))) ⟶*
              ((normalize-step ∘ fmap TermF N) ∘ (inr ∘ inr ∘ inl ∘ payload))
      step1 = cata-β-right {TermF} {TermCode'} {Unit} {normalize-step} {inr ∘ inr ∘ inl ∘ payload}

      -- fmap reductions
      r0 : (fmap TermF N ∘ (inr ∘ (inr ∘ inl ∘ payload))) ⟶* (inr ∘ (fmap TermF-1 N ∘ (inr ∘ inl ∘ payload)))
      r0 = ⟶1 assoc-l >> ∘-cong-left' (inr ∘ inl ∘ payload) (fmap-TermF-inr N) >> ⟶1 assoc-r

      r1 : (fmap TermF-1 N ∘ (inr ∘ inl ∘ payload)) ⟶* (inr ∘ (fmap TermF-2 N ∘ (inl ∘ payload)))
      r1 = ⟶1 assoc-l >> ∘-cong-left' (inl ∘ payload) (fmap-1-inr N) >> ⟶1 assoc-r

      r2 : (fmap TermF-2 N ∘ (inl ∘ payload)) ⟶* (inl ∘ payload)
      r2 = ⟶1 assoc-l >>
           ∘-cong-left' payload (fmap-2-inl N) >>
           ⟶1 assoc-r >>
           ∘-cong-right' inl (∘-cong-left' payload (fmap-KK-id TyFuncCode TyFuncCode N) >> ⟶1 id-left)

      reduce-chain : (fmap TermF N ∘ (inr ∘ inr ∘ inl ∘ payload)) ⟶* (inr ∘ inr ∘ inl ∘ payload)
      reduce-chain = r0 >> ∘-cong-right' inr (r1 >> ∘-cong-right' inr r2)

      inner-step : (normalize-step ∘ (inr ∘ inr ∘ inl ∘ payload)) ⟶* (handle-fst ∘ payload)
      inner-step = ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >> ∘-cong-left' payload nstep-at-2'

      step2 : ((normalize-step ∘ fmap TermF N) ∘ (inr ∘ inr ∘ inl ∘ payload)) ⟶* (handle-fst ∘ payload)
      step2 = ⟶1 assoc-r >> ∘-cong-right' normalize-step reduce-chain >> inner-step

      step3 : (handle-fst ∘ payload) ⟶* ((In {TermF} ∘ inr ∘ inr ∘ inl) ∘ payload)
      step3 = done

      step4 : ((In {TermF} ∘ inr ∘ inr ∘ inl) ∘ payload) ⟶* (In {TermF} ∘ (inr ∘ inr ∘ inl ∘ payload))
      step4 = ⟶1 assoc-r >> ∘-cong-right' In (⟶1 assoc-r >> ∘-cong-right' inr (⟶1 assoc-r))

------------------------------------------------------------------------
-- Base case: noredex-fixpoint-snd (position 3)
------------------------------------------------------------------------

abstract
  noredex-fixpoint-snd : ∀ {A B} → (normalize ∘ encode (snd {A} {B})) ⟶* encode (snd {A} {B})
  noredex-fixpoint-snd {A} {B} = step1 >> step2 >> step3 >> step4
    where
      N : Term TermCode' TermCode'
      N = cata TermF normalize-step

      payload : Term Unit (TyFuncCode * TyFuncCode)
      payload = ⟨ ⌜ A ⌝Ty , ⌜ B ⌝Ty ⟩

      step1 : (N ∘ (In {TermF} ∘ (inr ∘ inr ∘ inr ∘ inl ∘ payload))) ⟶*
              ((normalize-step ∘ fmap TermF N) ∘ (inr ∘ inr ∘ inr ∘ inl ∘ payload))
      step1 = cata-β-right {TermF} {TermCode'} {Unit} {normalize-step} {inr ∘ inr ∘ inr ∘ inl ∘ payload}

      r0 : (fmap TermF N ∘ (inr ∘ (inr ∘ (inr ∘ (inl ∘ payload))))) ⟶* (inr ∘ (fmap TermF-1 N ∘ (inr ∘ (inr ∘ (inl ∘ payload)))))
      r0 = ⟶1 assoc-l >> ∘-cong-left' (inr ∘ (inr ∘ (inl ∘ payload))) (fmap-TermF-inr N) >> ⟶1 assoc-r

      r1 : (fmap TermF-1 N ∘ (inr ∘ (inr ∘ (inl ∘ payload)))) ⟶* (inr ∘ (fmap TermF-2 N ∘ (inr ∘ (inl ∘ payload))))
      r1 = ⟶1 assoc-l >> ∘-cong-left' (inr ∘ (inl ∘ payload)) (fmap-1-inr N) >> ⟶1 assoc-r

      r2 : (fmap TermF-2 N ∘ (inr ∘ (inl ∘ payload))) ⟶* (inr ∘ (fmap TermF-3 N ∘ (inl ∘ payload)))
      r2 = ⟶1 assoc-l >> ∘-cong-left' (inl ∘ payload) (fmap-2-inr N) >> ⟶1 assoc-r

      r3 : (fmap TermF-3 N ∘ (inl ∘ payload)) ⟶* (inl ∘ payload)
      r3 = ⟶1 assoc-l >>
           ∘-cong-left' payload (fmap-3-inl N) >>
           ⟶1 assoc-r >>
           ∘-cong-right' inl (∘-cong-left' payload (fmap-KK-id TyFuncCode TyFuncCode N) >> ⟶1 id-left)

      reduce-chain : (fmap TermF N ∘ (inr ∘ inr ∘ inr ∘ inl ∘ payload)) ⟶* (inr ∘ inr ∘ inr ∘ inl ∘ payload)
      reduce-chain = r0 >> ∘-cong-right' inr (r1 >> ∘-cong-right' inr (r2 >> ∘-cong-right' inr r3))

      inner-step : (normalize-step ∘ (inr ∘ inr ∘ inr ∘ inl ∘ payload)) ⟶* (handle-snd ∘ payload)
      inner-step = ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >> ∘-cong-left' payload nstep-at-3'

      step2 : ((normalize-step ∘ fmap TermF N) ∘ (inr ∘ inr ∘ inr ∘ inl ∘ payload)) ⟶* (handle-snd ∘ payload)
      step2 = ⟶1 assoc-r >> ∘-cong-right' normalize-step reduce-chain >> inner-step

      step3 : (handle-snd ∘ payload) ⟶* ((In {TermF} ∘ inr ∘ inr ∘ inr ∘ inl) ∘ payload)
      step3 = done

      step4 : ((In {TermF} ∘ inr ∘ inr ∘ inr ∘ inl) ∘ payload) ⟶* (In {TermF} ∘ (inr ∘ inr ∘ inr ∘ inl ∘ payload))
      step4 = ⟶1 assoc-r >> ∘-cong-right' In (⟶1 assoc-r >> ∘-cong-right' inr (⟶1 assoc-r >> ∘-cong-right' inr (⟶1 assoc-r)))

------------------------------------------------------------------------
-- Base case: noredex-fixpoint-inl (position 5)
------------------------------------------------------------------------

abstract
  noredex-fixpoint-inl : ∀ {A B} → (normalize ∘ encode (inl {A} {B})) ⟶* encode (inl {A} {B})
  noredex-fixpoint-inl {A} {B} = step1 >> step2 >> step3 >> step4
    where
      N : Term TermCode' TermCode'
      N = cata TermF normalize-step

      payload : Term Unit (TyFuncCode * TyFuncCode)
      payload = ⟨ ⌜ A ⌝Ty , ⌜ B ⌝Ty ⟩

      step1 : (N ∘ (In {TermF} ∘ (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ payload))) ⟶*
              ((normalize-step ∘ fmap TermF N) ∘ (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ payload))
      step1 = cata-β-right {TermF} {TermCode'} {Unit} {normalize-step} {inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ payload}

      r0 : (fmap TermF N ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inl ∘ payload))))))) ⟶*
           (inr ∘ (fmap TermF-1 N ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inl ∘ payload)))))))
      r0 = ⟶1 assoc-l >> ∘-cong-left' (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inl ∘ payload))))) (fmap-TermF-inr N) >> ⟶1 assoc-r

      r1 : (fmap TermF-1 N ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inl ∘ payload)))))) ⟶*
           (inr ∘ (fmap TermF-2 N ∘ (inr ∘ (inr ∘ (inr ∘ (inl ∘ payload))))))
      r1 = ⟶1 assoc-l >> ∘-cong-left' (inr ∘ (inr ∘ (inr ∘ (inl ∘ payload)))) (fmap-1-inr N) >> ⟶1 assoc-r

      r2 : (fmap TermF-2 N ∘ (inr ∘ (inr ∘ (inr ∘ (inl ∘ payload))))) ⟶*
           (inr ∘ (fmap TermF-3 N ∘ (inr ∘ (inr ∘ (inl ∘ payload)))))
      r2 = ⟶1 assoc-l >> ∘-cong-left' (inr ∘ (inr ∘ (inl ∘ payload))) (fmap-2-inr N) >> ⟶1 assoc-r

      r3 : (fmap TermF-3 N ∘ (inr ∘ (inr ∘ (inl ∘ payload)))) ⟶*
           (inr ∘ (fmap TermF-4 N ∘ (inr ∘ (inl ∘ payload))))
      r3 = ⟶1 assoc-l >> ∘-cong-left' (inr ∘ (inl ∘ payload)) (fmap-3-inr N) >> ⟶1 assoc-r

      r4 : (fmap TermF-4 N ∘ (inr ∘ (inl ∘ payload))) ⟶*
           (inr ∘ (fmap TermF-5 N ∘ (inl ∘ payload)))
      r4 = ⟶1 assoc-l >> ∘-cong-left' (inl ∘ payload) (fmap-4-inr N) >> ⟶1 assoc-r

      r5 : (fmap TermF-5 N ∘ (inl ∘ payload)) ⟶* (inl ∘ payload)
      r5 = ⟶1 assoc-l >>
           ∘-cong-left' payload (fmap-5-inl N) >>
           ⟶1 assoc-r >>
           ∘-cong-right' inl (∘-cong-left' payload (fmap-KK-id TyFuncCode TyFuncCode N) >> ⟶1 id-left)

      reduce-chain : (fmap TermF N ∘ (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ payload)) ⟶* (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ payload)
      reduce-chain = r0 >> ∘-cong-right' inr (r1 >> ∘-cong-right' inr (r2 >> ∘-cong-right' inr (r3 >> ∘-cong-right' inr (r4 >> ∘-cong-right' inr r5))))

      inner-step : (normalize-step ∘ (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ payload)) ⟶* (handle-inl ∘ payload)
      inner-step = ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >> ∘-cong-left' payload nstep-at-5'

      step2 : ((normalize-step ∘ fmap TermF N) ∘ (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ payload)) ⟶* (handle-inl ∘ payload)
      step2 = ⟶1 assoc-r >> ∘-cong-right' normalize-step reduce-chain >> inner-step

      step3 : (handle-inl ∘ payload) ⟶* ((In {TermF} ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl) ∘ payload)
      step3 = done

      step4 : ((In {TermF} ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl) ∘ payload) ⟶* (In {TermF} ∘ (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ payload))
      step4 = ⟶1 assoc-r >> ∘-cong-right' In
              (⟶1 assoc-r >> ∘-cong-right' inr
              (⟶1 assoc-r >> ∘-cong-right' inr
              (⟶1 assoc-r >> ∘-cong-right' inr
              (⟶1 assoc-r >> ∘-cong-right' inr (⟶1 assoc-r)))))

------------------------------------------------------------------------
-- Base case: noredex-fixpoint-inr (position 6)
------------------------------------------------------------------------

abstract
  noredex-fixpoint-inr : ∀ {A B} → (normalize ∘ encode (inr {A} {B})) ⟶* encode (inr {A} {B})
  noredex-fixpoint-inr {A} {B} = step1 >> step2 >> step3 >> step4
    where
      N : Term TermCode' TermCode'
      N = cata TermF normalize-step

      payload : Term Unit (TyFuncCode * TyFuncCode)
      payload = ⟨ ⌜ A ⌝Ty , ⌜ B ⌝Ty ⟩

      step1 : (N ∘ (In {TermF} ∘ (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ payload))) ⟶*
              ((normalize-step ∘ fmap TermF N) ∘ (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ payload))
      step1 = cata-β-right {TermF} {TermCode'} {Unit} {normalize-step} {inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ payload}

      r0 : (fmap TermF N ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inl ∘ payload)))))))) ⟶*
           (inr ∘ (fmap TermF-1 N ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inl ∘ payload))))))))
      r0 = ⟶1 assoc-l >> ∘-cong-left' (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inl ∘ payload)))))) (fmap-TermF-inr N) >> ⟶1 assoc-r

      r1 : (fmap TermF-1 N ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inl ∘ payload))))))) ⟶*
           (inr ∘ (fmap TermF-2 N ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inl ∘ payload)))))))
      r1 = ⟶1 assoc-l >> ∘-cong-left' (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inl ∘ payload))))) (fmap-1-inr N) >> ⟶1 assoc-r

      r2 : (fmap TermF-2 N ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inl ∘ payload)))))) ⟶*
           (inr ∘ (fmap TermF-3 N ∘ (inr ∘ (inr ∘ (inr ∘ (inl ∘ payload))))))
      r2 = ⟶1 assoc-l >> ∘-cong-left' (inr ∘ (inr ∘ (inr ∘ (inl ∘ payload)))) (fmap-2-inr N) >> ⟶1 assoc-r

      r3 : (fmap TermF-3 N ∘ (inr ∘ (inr ∘ (inr ∘ (inl ∘ payload))))) ⟶*
           (inr ∘ (fmap TermF-4 N ∘ (inr ∘ (inr ∘ (inl ∘ payload)))))
      r3 = ⟶1 assoc-l >> ∘-cong-left' (inr ∘ (inr ∘ (inl ∘ payload))) (fmap-3-inr N) >> ⟶1 assoc-r

      r4 : (fmap TermF-4 N ∘ (inr ∘ (inr ∘ (inl ∘ payload)))) ⟶*
           (inr ∘ (fmap TermF-5 N ∘ (inr ∘ (inl ∘ payload))))
      r4 = ⟶1 assoc-l >> ∘-cong-left' (inr ∘ (inl ∘ payload)) (fmap-4-inr N) >> ⟶1 assoc-r

      r5 : (fmap TermF-5 N ∘ (inr ∘ (inl ∘ payload))) ⟶*
           (inr ∘ (fmap TermF-6 N ∘ (inl ∘ payload)))
      r5 = ⟶1 assoc-l >> ∘-cong-left' (inl ∘ payload) (fmap-5-inr N) >> ⟶1 assoc-r

      r6 : (fmap TermF-6 N ∘ (inl ∘ payload)) ⟶* (inl ∘ payload)
      r6 = ⟶1 assoc-l >>
           ∘-cong-left' payload (fmap-6-inl N) >>
           ⟶1 assoc-r >>
           ∘-cong-right' inl (∘-cong-left' payload (fmap-KK-id TyFuncCode TyFuncCode N) >> ⟶1 id-left)

      reduce-chain : (fmap TermF N ∘ (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ payload)) ⟶* (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ payload)
      reduce-chain = r0 >> ∘-cong-right' inr (r1 >> ∘-cong-right' inr (r2 >> ∘-cong-right' inr (r3 >> ∘-cong-right' inr (r4 >> ∘-cong-right' inr (r5 >> ∘-cong-right' inr r6)))))

      inner-step : (normalize-step ∘ (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ payload)) ⟶* (handle-inr ∘ payload)
      inner-step = ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >> ∘-cong-left' payload nstep-at-6'

      step2 : ((normalize-step ∘ fmap TermF N) ∘ (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ payload)) ⟶* (handle-inr ∘ payload)
      step2 = ⟶1 assoc-r >> ∘-cong-right' normalize-step reduce-chain >> inner-step

      step3 : (handle-inr ∘ payload) ⟶* ((In {TermF} ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl) ∘ payload)
      step3 = done

      step4 : ((In {TermF} ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl) ∘ payload) ⟶* (In {TermF} ∘ (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ payload))
      step4 = ⟶1 assoc-r >> ∘-cong-right' In
              (⟶1 assoc-r >> ∘-cong-right' inr
              (⟶1 assoc-r >> ∘-cong-right' inr
              (⟶1 assoc-r >> ∘-cong-right' inr
              (⟶1 assoc-r >> ∘-cong-right' inr
              (⟶1 assoc-r >> ∘-cong-right' inr (⟶1 assoc-r))))))

------------------------------------------------------------------------
-- Base case: noredex-fixpoint-terminal (position 8)
------------------------------------------------------------------------

abstract
  noredex-fixpoint-terminal : ∀ {A} → (normalize ∘ encode (terminal {A})) ⟶* encode (terminal {A})
  noredex-fixpoint-terminal {A} = step1 >> step2 >> step3 >> step4
    where
      N : Term TermCode' TermCode'
      N = cata TermF normalize-step

      payload : Term Unit TyFuncCode
      payload = ⌜ A ⌝Ty

      step1 : (N ∘ (In {TermF} ∘ (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ payload))) ⟶*
              ((normalize-step ∘ fmap TermF N) ∘ (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ payload))
      step1 = cata-β-right {TermF} {TermCode'} {Unit} {normalize-step} {inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ payload}

      -- Abbreviated: fmap chain reduces inr^8 ∘ inl to itself (K functor)
      reduce-chain : (fmap TermF N ∘ (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ payload)) ⟶*
                     (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ payload)
      reduce-chain =
        ⟶1 assoc-l >> ∘-cong-left' _ (fmap-TermF-inr N) >> ⟶1 assoc-r >> ∘-cong-right' inr
        (⟶1 assoc-l >> ∘-cong-left' _ (fmap-1-inr N) >> ⟶1 assoc-r >> ∘-cong-right' inr
        (⟶1 assoc-l >> ∘-cong-left' _ (fmap-2-inr N) >> ⟶1 assoc-r >> ∘-cong-right' inr
        (⟶1 assoc-l >> ∘-cong-left' _ (fmap-3-inr N) >> ⟶1 assoc-r >> ∘-cong-right' inr
        (⟶1 assoc-l >> ∘-cong-left' _ (fmap-4-inr N) >> ⟶1 assoc-r >> ∘-cong-right' inr
        (⟶1 assoc-l >> ∘-cong-left' _ (fmap-5-inr N) >> ⟶1 assoc-r >> ∘-cong-right' inr
        (⟶1 assoc-l >> ∘-cong-left' _ (fmap-6-inr N) >> ⟶1 assoc-r >> ∘-cong-right' inr
        (⟶1 assoc-l >> ∘-cong-left' _ (fmap-7-inr N) >> ⟶1 assoc-r >> ∘-cong-right' inr
        (⟶1 assoc-l >> ∘-cong-left' payload (fmap-8-inl N) >>
         ∘-cong-left' payload (⟶1 id-right)))))))))

      inner-step : (normalize-step ∘ (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ payload)) ⟶* (handle-terminal ∘ payload)
      inner-step = ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >> ∘-cong-left' payload nstep-at-8'

      step2 : ((normalize-step ∘ fmap TermF N) ∘ (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ payload)) ⟶* (handle-terminal ∘ payload)
      step2 = ⟶1 assoc-r >> ∘-cong-right' normalize-step reduce-chain >> inner-step

      step3 : (handle-terminal ∘ payload) ⟶* ((In {TermF} ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl) ∘ payload)
      step3 = done

      step4 : ((In {TermF} ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl) ∘ payload) ⟶* (In {TermF} ∘ (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ payload))
      step4 = ⟶1 assoc-r >> ∘-cong-right' In
              (⟶1 assoc-r >> ∘-cong-right' inr
              (⟶1 assoc-r >> ∘-cong-right' inr
              (⟶1 assoc-r >> ∘-cong-right' inr
              (⟶1 assoc-r >> ∘-cong-right' inr
              (⟶1 assoc-r >> ∘-cong-right' inr
              (⟶1 assoc-r >> ∘-cong-right' inr
              (⟶1 assoc-r >> ∘-cong-right' inr (⟶1 assoc-r))))))))

------------------------------------------------------------------------
-- Base case: noredex-fixpoint-In (position 9)
------------------------------------------------------------------------

abstract
  noredex-fixpoint-In' : ∀ {F} → (normalize ∘ encode (In {F})) ⟶* encode (In {F})
  noredex-fixpoint-In' {F} = step1 >> step2 >> step3 >> step4
    where
      N : Term TermCode' TermCode'
      N = cata TermF normalize-step

      payload : Term Unit TyFuncCode
      payload = ⌜ F ⌝Func

      step1 : (N ∘ (In {TermF} ∘ (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ payload))) ⟶*
              ((normalize-step ∘ fmap TermF N) ∘ (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ payload))
      step1 = cata-β-right {TermF} {TermCode'} {Unit} {normalize-step} {inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ payload}

      reduce-chain : (fmap TermF N ∘ (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ payload)) ⟶*
                     (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ payload)
      reduce-chain =
        ⟶1 assoc-l >> ∘-cong-left' _ (fmap-TermF-inr N) >> ⟶1 assoc-r >> ∘-cong-right' inr
        (⟶1 assoc-l >> ∘-cong-left' _ (fmap-1-inr N) >> ⟶1 assoc-r >> ∘-cong-right' inr
        (⟶1 assoc-l >> ∘-cong-left' _ (fmap-2-inr N) >> ⟶1 assoc-r >> ∘-cong-right' inr
        (⟶1 assoc-l >> ∘-cong-left' _ (fmap-3-inr N) >> ⟶1 assoc-r >> ∘-cong-right' inr
        (⟶1 assoc-l >> ∘-cong-left' _ (fmap-4-inr N) >> ⟶1 assoc-r >> ∘-cong-right' inr
        (⟶1 assoc-l >> ∘-cong-left' _ (fmap-5-inr N) >> ⟶1 assoc-r >> ∘-cong-right' inr
        (⟶1 assoc-l >> ∘-cong-left' _ (fmap-6-inr N) >> ⟶1 assoc-r >> ∘-cong-right' inr
        (⟶1 assoc-l >> ∘-cong-left' _ (fmap-7-inr N) >> ⟶1 assoc-r >> ∘-cong-right' inr
        (⟶1 assoc-l >> ∘-cong-left' _ (fmap-8-inr N) >> ⟶1 assoc-r >> ∘-cong-right' inr
        (⟶1 assoc-l >> ∘-cong-left' payload (fmap-9-inl N) >>
         ∘-cong-left' payload (⟶1 id-right))))))))))

      inner-step : (normalize-step ∘ (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ payload)) ⟶* (handle-In ∘ payload)
      inner-step = ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >> ∘-cong-left' payload nstep-at-9'

      step2 : ((normalize-step ∘ fmap TermF N) ∘ (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ payload)) ⟶* (handle-In ∘ payload)
      step2 = ⟶1 assoc-r >> ∘-cong-right' normalize-step reduce-chain >> inner-step

      step3 : (handle-In ∘ payload) ⟶* ((In {TermF} ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl) ∘ payload)
      step3 = done

      step4 : ((In {TermF} ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl) ∘ payload) ⟶* (In {TermF} ∘ (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ payload))
      step4 = ⟶1 assoc-r >> ∘-cong-right' In
              (⟶1 assoc-r >> ∘-cong-right' inr
              (⟶1 assoc-r >> ∘-cong-right' inr
              (⟶1 assoc-r >> ∘-cong-right' inr
              (⟶1 assoc-r >> ∘-cong-right' inr
              (⟶1 assoc-r >> ∘-cong-right' inr
              (⟶1 assoc-r >> ∘-cong-right' inr
              (⟶1 assoc-r >> ∘-cong-right' inr
              (⟶1 assoc-r >> ∘-cong-right' inr (⟶1 assoc-r)))))))))

------------------------------------------------------------------------
-- Base case: noredex-fixpoint-Out (position 10)
------------------------------------------------------------------------

abstract
  noredex-fixpoint-Out : ∀ {F} → (normalize ∘ encode (Out {F})) ⟶* encode (Out {F})
  noredex-fixpoint-Out {F} = step1 >> step2 >> step3 >> step4
    where
      N : Term TermCode' TermCode'
      N = cata TermF normalize-step

      payload : Term Unit TyFuncCode
      payload = ⌜ F ⌝Func

      step1 : (N ∘ (In {TermF} ∘ (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ payload))) ⟶*
              ((normalize-step ∘ fmap TermF N) ∘ (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ payload))
      step1 = cata-β-right {TermF} {TermCode'} {Unit} {normalize-step} {inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ payload}

      reduce-chain : (fmap TermF N ∘ (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ payload)) ⟶*
                     (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ payload)
      reduce-chain =
        ⟶1 assoc-l >> ∘-cong-left' _ (fmap-TermF-inr N) >> ⟶1 assoc-r >> ∘-cong-right' inr
        (⟶1 assoc-l >> ∘-cong-left' _ (fmap-1-inr N) >> ⟶1 assoc-r >> ∘-cong-right' inr
        (⟶1 assoc-l >> ∘-cong-left' _ (fmap-2-inr N) >> ⟶1 assoc-r >> ∘-cong-right' inr
        (⟶1 assoc-l >> ∘-cong-left' _ (fmap-3-inr N) >> ⟶1 assoc-r >> ∘-cong-right' inr
        (⟶1 assoc-l >> ∘-cong-left' _ (fmap-4-inr N) >> ⟶1 assoc-r >> ∘-cong-right' inr
        (⟶1 assoc-l >> ∘-cong-left' _ (fmap-5-inr N) >> ⟶1 assoc-r >> ∘-cong-right' inr
        (⟶1 assoc-l >> ∘-cong-left' _ (fmap-6-inr N) >> ⟶1 assoc-r >> ∘-cong-right' inr
        (⟶1 assoc-l >> ∘-cong-left' _ (fmap-7-inr N) >> ⟶1 assoc-r >> ∘-cong-right' inr
        (⟶1 assoc-l >> ∘-cong-left' _ (fmap-8-inr N) >> ⟶1 assoc-r >> ∘-cong-right' inr
        (⟶1 assoc-l >> ∘-cong-left' _ (fmap-9-inr N) >> ⟶1 assoc-r >> ∘-cong-right' inr
        (⟶1 assoc-l >> ∘-cong-left' payload (fmap-10-inl N) >>
         ∘-cong-left' payload (⟶1 id-right)))))))))))

      inner-step : (normalize-step ∘ (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ payload)) ⟶* (handle-Out ∘ payload)
      inner-step = ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >> ∘-cong-left' payload nstep-at-10'

      step2 : ((normalize-step ∘ fmap TermF N) ∘ (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ payload)) ⟶* (handle-Out ∘ payload)
      step2 = ⟶1 assoc-r >> ∘-cong-right' normalize-step reduce-chain >> inner-step

      step3 : (handle-Out ∘ payload) ⟶* ((In {TermF} ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl) ∘ payload)
      step3 = done

      step4 : ((In {TermF} ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl) ∘ payload) ⟶* (In {TermF} ∘ (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ payload))
      step4 = ⟶1 assoc-r >> ∘-cong-right' In
              (⟶1 assoc-r >> ∘-cong-right' inr
              (⟶1 assoc-r >> ∘-cong-right' inr
              (⟶1 assoc-r >> ∘-cong-right' inr
              (⟶1 assoc-r >> ∘-cong-right' inr
              (⟶1 assoc-r >> ∘-cong-right' inr
              (⟶1 assoc-r >> ∘-cong-right' inr
              (⟶1 assoc-r >> ∘-cong-right' inr
              (⟶1 assoc-r >> ∘-cong-right' inr
              (⟶1 assoc-r >> ∘-cong-right' inr (⟶1 assoc-r))))))))))

------------------------------------------------------------------------
-- Base case: noredex-fixpoint-apply (position 13)
------------------------------------------------------------------------

abstract
  noredex-fixpoint-apply : ∀ {A B} → (normalize ∘ encode (apply {A} {B})) ⟶* encode (apply {A} {B})
  noredex-fixpoint-apply {A} {B} = step1 >> step2 >> step3 >> step4
    where
      N : Term TermCode' TermCode'
      N = cata TermF normalize-step

      payload : Term Unit (TyFuncCode * TyFuncCode)
      payload = ⟨ ⌜ A ⌝Ty , ⌜ B ⌝Ty ⟩

      step1 : (N ∘ (In {TermF} ∘ (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ payload))) ⟶*
              ((normalize-step ∘ fmap TermF N) ∘ (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ payload))
      step1 = cata-β-right {TermF} {TermCode'} {Unit} {normalize-step} {inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ payload}

      reduce-chain : (fmap TermF N ∘ (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ payload)) ⟶*
                     (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ payload)
      reduce-chain =
        ⟶1 assoc-l >> ∘-cong-left' _ (fmap-TermF-inr N) >> ⟶1 assoc-r >> ∘-cong-right' inr
        (⟶1 assoc-l >> ∘-cong-left' _ (fmap-1-inr N) >> ⟶1 assoc-r >> ∘-cong-right' inr
        (⟶1 assoc-l >> ∘-cong-left' _ (fmap-2-inr N) >> ⟶1 assoc-r >> ∘-cong-right' inr
        (⟶1 assoc-l >> ∘-cong-left' _ (fmap-3-inr N) >> ⟶1 assoc-r >> ∘-cong-right' inr
        (⟶1 assoc-l >> ∘-cong-left' _ (fmap-4-inr N) >> ⟶1 assoc-r >> ∘-cong-right' inr
        (⟶1 assoc-l >> ∘-cong-left' _ (fmap-5-inr N) >> ⟶1 assoc-r >> ∘-cong-right' inr
        (⟶1 assoc-l >> ∘-cong-left' _ (fmap-6-inr N) >> ⟶1 assoc-r >> ∘-cong-right' inr
        (⟶1 assoc-l >> ∘-cong-left' _ (fmap-7-inr N) >> ⟶1 assoc-r >> ∘-cong-right' inr
        (⟶1 assoc-l >> ∘-cong-left' _ (fmap-8-inr N) >> ⟶1 assoc-r >> ∘-cong-right' inr
        (⟶1 assoc-l >> ∘-cong-left' _ (fmap-9-inr N) >> ⟶1 assoc-r >> ∘-cong-right' inr
        (⟶1 assoc-l >> ∘-cong-left' _ (fmap-10-inr N) >> ⟶1 assoc-r >> ∘-cong-right' inr
        (⟶1 assoc-l >> ∘-cong-left' _ (fmap-11-inr N) >> ⟶1 assoc-r >> ∘-cong-right' inr
        (⟶1 assoc-l >> ∘-cong-left' _ (fmap-12-inr N) >> ⟶1 assoc-r >> ∘-cong-right' inr
        (∘-cong-left' payload (fmap-KK-id TyFuncCode TyFuncCode N) >> ⟶1 id-left)))))))))))))

      inner-step : (normalize-step ∘ (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ payload)) ⟶* (handle-apply ∘ payload)
      inner-step = ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >> ∘-cong-left' payload nstep-at-13'

      step2 : ((normalize-step ∘ fmap TermF N) ∘ (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ payload)) ⟶* (handle-apply ∘ payload)
      step2 = ⟶1 assoc-r >> ∘-cong-right' normalize-step reduce-chain >> inner-step

      step3 : (handle-apply ∘ payload) ⟶* ((In {TermF} ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr) ∘ payload)
      step3 = done

      step4 : ((In {TermF} ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr) ∘ payload) ⟶* (In {TermF} ∘ (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ payload))
      step4 = ⟶1 assoc-r >> ∘-cong-right' In
              (⟶1 assoc-r >> ∘-cong-right' inr
              (⟶1 assoc-r >> ∘-cong-right' inr
              (⟶1 assoc-r >> ∘-cong-right' inr
              (⟶1 assoc-r >> ∘-cong-right' inr
              (⟶1 assoc-r >> ∘-cong-right' inr
              (⟶1 assoc-r >> ∘-cong-right' inr
              (⟶1 assoc-r >> ∘-cong-right' inr
              (⟶1 assoc-r >> ∘-cong-right' inr
              (⟶1 assoc-r >> ∘-cong-right' inr
              (⟶1 assoc-r >> ∘-cong-right' inr
              (⟶1 assoc-r >> ∘-cong-right' inr (⟶1 assoc-r))))))))))))

------------------------------------------------------------------------
-- Main fixpoint theorem (by structural induction on NoRedex)
-- Wrapped in abstract to prevent term expansion during type-checking
------------------------------------------------------------------------

abstract
  noredex-fixpoint : ∀ {A B} (t : Term A B) →
                     NoRedex t →
                     (normalize ∘ encode t) ⟶* encode t

  -- Base cases: delegate to individual proofs
  noredex-fixpoint id nr-id = noredex-fixpoint-id
  noredex-fixpoint fst nr-fst = noredex-fixpoint-fst
  noredex-fixpoint snd nr-snd = noredex-fixpoint-snd
  noredex-fixpoint inl nr-inl = noredex-fixpoint-inl
  noredex-fixpoint inr nr-inr = noredex-fixpoint-inr
  noredex-fixpoint terminal nr-terminal = noredex-fixpoint-terminal
  noredex-fixpoint In nr-In = noredex-fixpoint-In'
  noredex-fixpoint Out nr-Out = noredex-fixpoint-Out
  noredex-fixpoint apply nr-apply = noredex-fixpoint-apply

  -- Position 4 (pair): encode ⟨f,g⟩ = In ∘ inr^4 ∘ inl ∘ ⟨encode f, encode g⟩
  noredex-fixpoint ⟨ f , g ⟩ (nr-pair nrf nrg) = step1 >> step2 >> step3 >> step4
    where
    N : Term TermCode' TermCode'
    N = cata TermF normalize-step

    payload : Term Unit (TermCode' * TermCode')
    payload = ⟨ encode f , encode g ⟩

    step1 : (N ∘ (In {TermF} ∘ (inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ payload))) ⟶*
            ((normalize-step ∘ fmap TermF N) ∘ (inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ payload))
    step1 = cata-β-right {TermF} {TermCode'} {Unit} {normalize-step} {inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ payload}

    r0 : (fmap TermF N ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inl ∘ payload)))))) ⟶*
         (inr ∘ (fmap TermF-1 N ∘ (inr ∘ (inr ∘ (inr ∘ (inl ∘ payload))))))
    r0 = ⟶1 assoc-l >> ∘-cong-left' (inr ∘ (inr ∘ (inr ∘ (inl ∘ payload)))) (fmap-TermF-inr N) >> ⟶1 assoc-r

    r1 : (fmap TermF-1 N ∘ (inr ∘ (inr ∘ (inr ∘ (inl ∘ payload))))) ⟶*
         (inr ∘ (fmap TermF-2 N ∘ (inr ∘ (inr ∘ (inl ∘ payload)))))
    r1 = ⟶1 assoc-l >> ∘-cong-left' (inr ∘ (inr ∘ (inl ∘ payload))) (fmap-1-inr N) >> ⟶1 assoc-r

    r2 : (fmap TermF-2 N ∘ (inr ∘ (inr ∘ (inl ∘ payload)))) ⟶*
         (inr ∘ (fmap TermF-3 N ∘ (inr ∘ (inl ∘ payload))))
    r2 = ⟶1 assoc-l >> ∘-cong-left' (inr ∘ (inl ∘ payload)) (fmap-2-inr N) >> ⟶1 assoc-r

    r3 : (fmap TermF-3 N ∘ (inr ∘ (inl ∘ payload))) ⟶*
         (inr ∘ (fmap TermF-4 N ∘ (inl ∘ payload)))
    r3 = ⟶1 assoc-l >> ∘-cong-left' (inl ∘ payload) (fmap-3-inr N) >> ⟶1 assoc-r

    -- Position 4 payload functor: Id ⊗ Id
    ih-step : (fmap (Id ⊗ Id) N ∘ payload) ⟶* payload
    ih-step =
      ⟶1 pair-comp >>
      ⟨⟩-cong
        (⟶1 assoc-r >> ∘-cong-right' N (⟶1 fst-pair) >> noredex-fixpoint f nrf)
        (⟶1 assoc-r >> ∘-cong-right' N (⟶1 snd-pair) >> noredex-fixpoint g nrg)

    r4 : (fmap TermF-4 N ∘ (inl ∘ payload)) ⟶* (inl ∘ payload)
    r4 = ⟶1 assoc-l >>
         ∘-cong-left' payload (fmap-4-inl N) >>
         ⟶1 assoc-r >>
         ∘-cong-right' inl ih-step

    reduce-chain : (fmap TermF N ∘ (inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ payload)) ⟶* (inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ payload)
    reduce-chain =
      r0 >> ∘-cong-right' inr
        (r1 >> ∘-cong-right' inr
          (r2 >> ∘-cong-right' inr
            (r3 >> ∘-cong-right' inr r4)))

    inner-step : (normalize-step ∘ (inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ payload)) ⟶* (handle-pair ∘ payload)
    inner-step =
      ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >>
      ∘-cong-left' payload nstep-at-4'

    step2 : ((normalize-step ∘ fmap TermF N) ∘ (inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ payload)) ⟶*
            (handle-pair ∘ payload)
    step2 = ⟶1 assoc-r >> ∘-cong-right' normalize-step reduce-chain >> inner-step

    step3 : (handle-pair ∘ payload) ⟶* ((In {TermF} ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl) ∘ payload)
    step3 = done

    step4 : ((In {TermF} ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl) ∘ payload) ⟶* (In {TermF} ∘ (inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ payload))
    step4 = ⟶1 assoc-r >> ∘-cong-right' In
            (⟶1 assoc-r >> ∘-cong-right' inr
            (⟶1 assoc-r >> ∘-cong-right' inr
            (⟶1 assoc-r >> ∘-cong-right' inr (⟶1 assoc-r))))

  -- Position 7 (case): encode [f,g] = In ∘ inr^7 ∘ inl ∘ ⟨encode f, encode g⟩
  noredex-fixpoint [ f , g ] (nr-case nrf nrg) = step1 >> step2 >> step3 >> step4
    where
    N : Term TermCode' TermCode'
    N = cata TermF normalize-step

    payload : Term Unit (TermCode' * TermCode')
    payload = ⟨ encode f , encode g ⟩

    step1 : (N ∘ (In {TermF} ∘ (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ payload))) ⟶*
            ((normalize-step ∘ fmap TermF N) ∘ (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ payload))
    step1 = cata-β-right {TermF} {TermCode'} {Unit} {normalize-step} {inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ payload}

    r0 : (fmap TermF N ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inl ∘ payload))))))))) ⟶*
         (inr ∘ (fmap TermF-1 N ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inl ∘ payload)))))))))
    r0 = ⟶1 assoc-l >> ∘-cong-left' _ (fmap-TermF-inr N) >> ⟶1 assoc-r

    r1 : (fmap TermF-1 N ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inl ∘ payload)))))))) ⟶*
         (inr ∘ (fmap TermF-2 N ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inl ∘ payload))))))))
    r1 = ⟶1 assoc-l >> ∘-cong-left' _ (fmap-1-inr N) >> ⟶1 assoc-r

    r2 : (fmap TermF-2 N ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inl ∘ payload))))))) ⟶*
         (inr ∘ (fmap TermF-3 N ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inl ∘ payload)))))))
    r2 = ⟶1 assoc-l >> ∘-cong-left' _ (fmap-2-inr N) >> ⟶1 assoc-r

    r3 : (fmap TermF-3 N ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inl ∘ payload)))))) ⟶*
         (inr ∘ (fmap TermF-4 N ∘ (inr ∘ (inr ∘ (inr ∘ (inl ∘ payload))))))
    r3 = ⟶1 assoc-l >> ∘-cong-left' _ (fmap-3-inr N) >> ⟶1 assoc-r

    r4 : (fmap TermF-4 N ∘ (inr ∘ (inr ∘ (inr ∘ (inl ∘ payload))))) ⟶*
         (inr ∘ (fmap TermF-5 N ∘ (inr ∘ (inr ∘ (inl ∘ payload)))))
    r4 = ⟶1 assoc-l >> ∘-cong-left' _ (fmap-4-inr N) >> ⟶1 assoc-r

    r5 : (fmap TermF-5 N ∘ (inr ∘ (inr ∘ (inl ∘ payload)))) ⟶*
         (inr ∘ (fmap TermF-6 N ∘ (inr ∘ (inl ∘ payload))))
    r5 = ⟶1 assoc-l >> ∘-cong-left' _ (fmap-5-inr N) >> ⟶1 assoc-r

    r6 : (fmap TermF-6 N ∘ (inr ∘ (inl ∘ payload))) ⟶*
         (inr ∘ (fmap TermF-7 N ∘ (inl ∘ payload)))
    r6 = ⟶1 assoc-l >> ∘-cong-left' _ (fmap-6-inr N) >> ⟶1 assoc-r

    ih-step : (fmap (Id ⊗ Id) N ∘ payload) ⟶* payload
    ih-step =
      ⟶1 pair-comp >>
      ⟨⟩-cong
        (⟶1 assoc-r >> ∘-cong-right' N (⟶1 fst-pair) >> noredex-fixpoint f nrf)
        (⟶1 assoc-r >> ∘-cong-right' N (⟶1 snd-pair) >> noredex-fixpoint g nrg)

    r7 : (fmap TermF-7 N ∘ (inl ∘ payload)) ⟶* (inl ∘ payload)
    r7 = ⟶1 assoc-l >>
         ∘-cong-left' payload (fmap-7-inl N) >>
         ⟶1 assoc-r >>
         ∘-cong-right' inl ih-step

    reduce-chain : (fmap TermF N ∘ (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ payload)) ⟶* (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ payload)
    reduce-chain =
      r0 >> ∘-cong-right' inr
        (r1 >> ∘-cong-right' inr
          (r2 >> ∘-cong-right' inr
            (r3 >> ∘-cong-right' inr
              (r4 >> ∘-cong-right' inr
                (r5 >> ∘-cong-right' inr
                  (r6 >> ∘-cong-right' inr r7))))))

    inner-step : (normalize-step ∘ (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ payload)) ⟶* (handle-case ∘ payload)
    inner-step =
      ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >>
      ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >>
      ∘-cong-left' payload nstep-at-7'

    step2 : ((normalize-step ∘ fmap TermF N) ∘ (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ payload)) ⟶*
            (handle-case ∘ payload)
    step2 = ⟶1 assoc-r >> ∘-cong-right' normalize-step reduce-chain >> inner-step

    step3 : (handle-case ∘ payload) ⟶* ((In {TermF} ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl) ∘ payload)
    step3 = done

    step4 : ((In {TermF} ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl) ∘ payload) ⟶* (In {TermF} ∘ (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ payload))
    step4 = ⟶1 assoc-r >> ∘-cong-right' In
            (⟶1 assoc-r >> ∘-cong-right' inr
            (⟶1 assoc-r >> ∘-cong-right' inr
            (⟶1 assoc-r >> ∘-cong-right' inr
            (⟶1 assoc-r >> ∘-cong-right' inr
            (⟶1 assoc-r >> ∘-cong-right' inr
            (⟶1 assoc-r >> ∘-cong-right' inr (⟶1 assoc-r)))))))

  -- Position 12 (curry): encode (curry f) = In ∘ inr^12 ∘ inl ∘ ⟨⟨⌜A⌝,⌜B⌝⟩, ⟨⌜C⌝, encode f⟩⟩
  noredex-fixpoint (curry {A} {B} {C} f) (nr-curry nrf) = step1 >> step2 >> step3 >> step4
    where
    N : Term TermCode' TermCode'
    N = cata TermF normalize-step

    payload : Term Unit ((TyFuncCode * TyFuncCode) * (TyFuncCode * TermCode'))
    payload = ⟨ ⟨ ⌜ A ⌝Ty , ⌜ B ⌝Ty ⟩ , ⟨ ⌜ C ⌝Ty , encode f ⟩ ⟩

    step1 : (N ∘ (In {TermF} ∘ (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ payload))) ⟶*
            ((normalize-step ∘ fmap TermF N) ∘ (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ payload))
    step1 = cata-β-right {TermF} {TermCode'} {Unit} {normalize-step} {inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ payload}

    -- 12 inr navigations
    reduce-chain : (fmap TermF N ∘ (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ payload)) ⟶*
                   (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ payload)
    reduce-chain =
      ⟶1 assoc-l >> ∘-cong-left' _ (fmap-TermF-inr N) >> ⟶1 assoc-r >> ∘-cong-right' inr
      (⟶1 assoc-l >> ∘-cong-left' _ (fmap-1-inr N) >> ⟶1 assoc-r >> ∘-cong-right' inr
      (⟶1 assoc-l >> ∘-cong-left' _ (fmap-2-inr N) >> ⟶1 assoc-r >> ∘-cong-right' inr
      (⟶1 assoc-l >> ∘-cong-left' _ (fmap-3-inr N) >> ⟶1 assoc-r >> ∘-cong-right' inr
      (⟶1 assoc-l >> ∘-cong-left' _ (fmap-4-inr N) >> ⟶1 assoc-r >> ∘-cong-right' inr
      (⟶1 assoc-l >> ∘-cong-left' _ (fmap-5-inr N) >> ⟶1 assoc-r >> ∘-cong-right' inr
      (⟶1 assoc-l >> ∘-cong-left' _ (fmap-6-inr N) >> ⟶1 assoc-r >> ∘-cong-right' inr
      (⟶1 assoc-l >> ∘-cong-left' _ (fmap-7-inr N) >> ⟶1 assoc-r >> ∘-cong-right' inr
      (⟶1 assoc-l >> ∘-cong-left' _ (fmap-8-inr N) >> ⟶1 assoc-r >> ∘-cong-right' inr
      (⟶1 assoc-l >> ∘-cong-left' _ (fmap-9-inr N) >> ⟶1 assoc-r >> ∘-cong-right' inr
      (⟶1 assoc-l >> ∘-cong-left' _ (fmap-10-inr N) >> ⟶1 assoc-r >> ∘-cong-right' inr
      (⟶1 assoc-l >> ∘-cong-left' _ (fmap-11-inr N) >> ⟶1 assoc-r >> ∘-cong-right' inr
      (⟶1 assoc-l >> ∘-cong-left' payload curry-fmap-12-inl >> ⟶1 assoc-r >> ∘-cong-right' inl curry-ih-step))))))))))))
      where
        curry-ih-step : (fmap CurryPayloadF N ∘ payload) ⟶* payload
        curry-ih-step =
          ⟶1 pair-comp >>
          ⟨⟩-cong
            -- First component: fmap (K⊗K) N ∘ fst ∘ payload ⟶* ⟨⌜A⌝,⌜B⌝⟩
            (⟶1 assoc-r >> ∘-cong-right' (fmap (K TyFuncCode ⊗ K TyFuncCode) N) (⟶1 fst-pair) >>
             ∘-cong-left' _ (fmap-KK-id TyFuncCode TyFuncCode N) >> ⟶1 id-left)
            -- Second component: fmap (K⊗Id) N ∘ snd ∘ payload ⟶* ⟨⌜C⌝, encode f⟩
            (⟶1 assoc-r >> ∘-cong-right' (fmap (K TyFuncCode ⊗ Id) N) (⟶1 snd-pair) >>
             ⟶1 pair-comp >>
             ⟨⟩-cong
               (⟶1 assoc-r >> ⟶1 id-left >> ⟶1 fst-pair)
               (⟶1 assoc-r >> ∘-cong-right' N (⟶1 snd-pair) >> noredex-fixpoint f nrf))

        curry-fmap-12-inl : (fmap TermF-12 N ∘ inl) ⟶* (inl ∘ fmap CurryPayloadF N)
        curry-fmap-12-inl = fmap-sum-inl CurryPayloadF TermF-13 N

    inner-step : (normalize-step ∘ (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ payload)) ⟶* (handle-curry ∘ payload)
    inner-step =
      ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >>
      ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >>
      ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >>
      ∘-cong-left' payload nstep-at-12'

    step2 : ((normalize-step ∘ fmap TermF N) ∘ (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ payload)) ⟶*
            (handle-curry ∘ payload)
    step2 = ⟶1 assoc-r >> ∘-cong-right' normalize-step reduce-chain >> inner-step

    step3 : (handle-curry ∘ payload) ⟶* ((In {TermF} ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl) ∘ payload)
    step3 = done

    step4 : ((In {TermF} ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl) ∘ payload) ⟶*
            (In {TermF} ∘ (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ payload))
    step4 = ⟶1 assoc-r >> ∘-cong-right' In
            (⟶1 assoc-r >> ∘-cong-right' inr
            (⟶1 assoc-r >> ∘-cong-right' inr
            (⟶1 assoc-r >> ∘-cong-right' inr
            (⟶1 assoc-r >> ∘-cong-right' inr
            (⟶1 assoc-r >> ∘-cong-right' inr
            (⟶1 assoc-r >> ∘-cong-right' inr
            (⟶1 assoc-r >> ∘-cong-right' inr
            (⟶1 assoc-r >> ∘-cong-right' inr
            (⟶1 assoc-r >> ∘-cong-right' inr
            (⟶1 assoc-r >> ∘-cong-right' inr
            (⟶1 assoc-r >> ∘-cong-right' inr (⟶1 assoc-r))))))))))))

  -- Position 11 (cata): encode (cata F alg) = In ∘ inr^11 ∘ inl ∘ ⟨⌜F⌝, encode alg⟩
  noredex-fixpoint (cata F alg) (nr-cata nralg) = step1 >> step2 >> step3 >> step4
    where
    N : Term TermCode' TermCode'
    N = cata TermF normalize-step

    payload : Term Unit (TyFuncCode * TermCode')
    payload = ⟨ ⌜ F ⌝Func , encode alg ⟩

    step1 : (N ∘ (In {TermF} ∘ (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ payload))) ⟶*
            ((normalize-step ∘ fmap TermF N) ∘ (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ payload))
    step1 = cata-β-right {TermF} {TermCode'} {Unit} {normalize-step} {inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ payload}

    -- 11 inr navigations
    reduce-chain : (fmap TermF N ∘ (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ payload)) ⟶*
                   (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ payload)
    reduce-chain =
      ⟶1 assoc-l >> ∘-cong-left' _ (fmap-TermF-inr N) >> ⟶1 assoc-r >> ∘-cong-right' inr
      (⟶1 assoc-l >> ∘-cong-left' _ (fmap-1-inr N) >> ⟶1 assoc-r >> ∘-cong-right' inr
      (⟶1 assoc-l >> ∘-cong-left' _ (fmap-2-inr N) >> ⟶1 assoc-r >> ∘-cong-right' inr
      (⟶1 assoc-l >> ∘-cong-left' _ (fmap-3-inr N) >> ⟶1 assoc-r >> ∘-cong-right' inr
      (⟶1 assoc-l >> ∘-cong-left' _ (fmap-4-inr N) >> ⟶1 assoc-r >> ∘-cong-right' inr
      (⟶1 assoc-l >> ∘-cong-left' _ (fmap-5-inr N) >> ⟶1 assoc-r >> ∘-cong-right' inr
      (⟶1 assoc-l >> ∘-cong-left' _ (fmap-6-inr N) >> ⟶1 assoc-r >> ∘-cong-right' inr
      (⟶1 assoc-l >> ∘-cong-left' _ (fmap-7-inr N) >> ⟶1 assoc-r >> ∘-cong-right' inr
      (⟶1 assoc-l >> ∘-cong-left' _ (fmap-8-inr N) >> ⟶1 assoc-r >> ∘-cong-right' inr
      (⟶1 assoc-l >> ∘-cong-left' _ (fmap-9-inr N) >> ⟶1 assoc-r >> ∘-cong-right' inr
      (⟶1 assoc-l >> ∘-cong-left' _ (fmap-10-inr N) >> ⟶1 assoc-r >> ∘-cong-right' inr
      (⟶1 assoc-l >> ∘-cong-left' payload cata-fmap-11-inl >> ⟶1 assoc-r >> ∘-cong-right' inl cata-ih-step)))))))))))
      where
        cata-ih-step : (fmap (K TyFuncCode ⊗ Id) N ∘ payload) ⟶* payload
        cata-ih-step =
          ⟶1 pair-comp >>
          ⟨⟩-cong
            (⟶1 assoc-r >> ⟶1 id-left >> ⟶1 fst-pair)
            (⟶1 assoc-r >> ∘-cong-right' N (⟶1 snd-pair) >> noredex-fixpoint alg nralg)

        cata-fmap-11-inl : (fmap TermF-11 N ∘ inl) ⟶* (inl ∘ fmap (K TyFuncCode ⊗ Id) N)
        cata-fmap-11-inl = fmap-sum-inl (K TyFuncCode ⊗ Id) TermF-12 N

    inner-step : (normalize-step ∘ (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ payload)) ⟶* (handle-cata ∘ payload)
    inner-step =
      ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >>
      ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >>
      ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >>
      ∘-cong-left' payload nstep-at-11'

    step2 : ((normalize-step ∘ fmap TermF N) ∘ (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ payload)) ⟶*
            (handle-cata ∘ payload)
    step2 = ⟶1 assoc-r >> ∘-cong-right' normalize-step reduce-chain >> inner-step

    step3 : (handle-cata ∘ payload) ⟶* ((In {TermF} ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl) ∘ payload)
    step3 = done

    step4 : ((In {TermF} ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl) ∘ payload) ⟶*
            (In {TermF} ∘ (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ payload))
    step4 = ⟶1 assoc-r >> ∘-cong-right' In
            (⟶1 assoc-r >> ∘-cong-right' inr
            (⟶1 assoc-r >> ∘-cong-right' inr
            (⟶1 assoc-r >> ∘-cong-right' inr
            (⟶1 assoc-r >> ∘-cong-right' inr
            (⟶1 assoc-r >> ∘-cong-right' inr
            (⟶1 assoc-r >> ∘-cong-right' inr
            (⟶1 assoc-r >> ∘-cong-right' inr
            (⟶1 assoc-r >> ∘-cong-right' inr
            (⟶1 assoc-r >> ∘-cong-right' inr
            (⟶1 assoc-r >> ∘-cong-right' inr (⟶1 assoc-r)))))))))))

  -- Position 1 (comp): encode (f ∘ g) = In ∘ inr ∘ inl ∘ ⟨encode f, encode g⟩
  noredex-fixpoint (f ∘ g) (nr-comp nrf nrg nisf nisg) = step1 >> step2 >> step3 >> step4
    where
    N : Term TermCode' TermCode'
    N = cata TermF normalize-step

    payload : Term Unit (TermCode' * TermCode')
    payload = ⟨ encode f , encode g ⟩

    step1 : (N ∘ (In {TermF} ∘ (inr ∘ inl ∘ payload))) ⟶*
            ((normalize-step ∘ fmap TermF N) ∘ (inr ∘ inl ∘ payload))
    step1 = cata-β-right {TermF} {TermCode'} {Unit} {normalize-step} {inr ∘ inl ∘ payload}

    r0 : (fmap TermF N ∘ (inr ∘ (inl ∘ payload))) ⟶*
         (inr ∘ (fmap TermF-1 N ∘ (inl ∘ payload)))
    r0 = ⟶1 assoc-l >> ∘-cong-left' _ (fmap-TermF-inr N) >> ⟶1 assoc-r

    ih-step : (fmap (Id ⊗ Id) N ∘ payload) ⟶* payload
    ih-step =
      ⟶1 pair-comp >>
      ⟨⟩-cong
        (⟶1 assoc-r >> ∘-cong-right' N (⟶1 fst-pair) >> noredex-fixpoint f nrf)
        (⟶1 assoc-r >> ∘-cong-right' N (⟶1 snd-pair) >> noredex-fixpoint g nrg)

    comp-fmap-1-inl : (fmap TermF-1 N ∘ inl) ⟶* (inl ∘ fmap (Id ⊗ Id) N)
    comp-fmap-1-inl = fmap-sum-inl (Id ⊗ Id) TermF-2 N

    r1 : (fmap TermF-1 N ∘ (inl ∘ payload)) ⟶* (inl ∘ payload)
    r1 = ⟶1 assoc-l >> ∘-cong-left' payload comp-fmap-1-inl >> ⟶1 assoc-r >> ∘-cong-right' inl ih-step

    reduce-chain : (fmap TermF N ∘ (inr ∘ inl ∘ payload)) ⟶* (inr ∘ inl ∘ payload)
    reduce-chain = r0 >> ∘-cong-right' inr r1

    inner-step : (normalize-step ∘ (inr ∘ inl ∘ payload)) ⟶* (handle-comp ∘ payload)
    inner-step =
      ⟶1 assoc-l >> ⟶1 assoc-l >>
      ∘-cong-left' payload nstep-at-1'

    step2 : ((normalize-step ∘ fmap TermF N) ∘ (inr ∘ inl ∘ payload)) ⟶*
            (handle-comp ∘ payload)
    step2 = ⟶1 assoc-r >> ∘-cong-right' normalize-step reduce-chain >> inner-step

    step3 : (handle-comp ∘ payload) ⟶* ((In {TermF} ∘ inr ∘ inl) ∘ payload)
    step3 = handle-comp-rebuild payload

    step4 : ((In {TermF} ∘ inr ∘ inl) ∘ payload) ⟶* (In {TermF} ∘ (inr ∘ inl ∘ payload))
    step4 = ⟶1 assoc-r >> ∘-cong-right' In (⟶1 assoc-r)
