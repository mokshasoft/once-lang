------------------------------------------------------------------------
-- Fixpoint.BaseRecursive: Base case proofs for recursive type operations
--
-- For In, Out, and apply (positions 10, 11, 14)
------------------------------------------------------------------------

module normalizer.Implementation.Normalize.Fixpoint.BaseRecursive where

open import normalizer.Implementation.Normalize.Fixpoint.DispatchLemmas public

------------------------------------------------------------------------
-- Base case: noredex-fixpoint-In (position 10)
------------------------------------------------------------------------

abstract
  noredex-fixpoint-In' : ∀ {F} → (normalize ∘ encode (In {F})) ⟶* encode (In {F})
  noredex-fixpoint-In' {F} = step1 >> step2 >> step3 >> step4
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

      inner-step : (normalize-step ∘ (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ payload)) ⟶* (handle-In ∘ payload)
      inner-step = ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >> ∘-cong-left' payload nstep-at-10'

      step2 : ((normalize-step ∘ fmap TermF N) ∘ (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ payload)) ⟶* (handle-In ∘ payload)
      step2 = ⟶1 assoc-r >> ∘-cong-right' normalize-step reduce-chain >> inner-step

      step3 : (handle-In ∘ payload) ⟶* ((In {TermF} ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl) ∘ payload)
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
-- Base case: noredex-fixpoint-Out (position 11)
------------------------------------------------------------------------

abstract
  noredex-fixpoint-Out : ∀ {F} → (normalize ∘ encode (Out {F})) ⟶* encode (Out {F})
  noredex-fixpoint-Out {F} = step1 >> step2 >> step3 >> step4
    where
      N : Term TermCode' TermCode'
      N = cata TermF normalize-step

      payload : Term Unit TyFuncCode
      payload = ⌜ F ⌝Func

      step1 : (N ∘ (In {TermF} ∘ (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ payload))) ⟶*
              ((normalize-step ∘ fmap TermF N) ∘ (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ payload))
      step1 = cata-β-right {TermF} {TermCode'} {Unit} {normalize-step} {inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ payload}

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
        (⟶1 assoc-l >> ∘-cong-left' payload (fmap-11-inl N) >>
         ∘-cong-left' payload (⟶1 id-right))))))))))))

      inner-step : (normalize-step ∘ (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ payload)) ⟶* (handle-Out ∘ payload)
      inner-step = ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >> ∘-cong-left' payload nstep-at-11'

      step2 : ((normalize-step ∘ fmap TermF N) ∘ (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ payload)) ⟶* (handle-Out ∘ payload)
      step2 = ⟶1 assoc-r >> ∘-cong-right' normalize-step reduce-chain >> inner-step

      step3 : (handle-Out ∘ payload) ⟶* ((In {TermF} ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl) ∘ payload)
      step3 = done

      step4 : ((In {TermF} ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl) ∘ payload) ⟶* (In {TermF} ∘ (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ payload))
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

------------------------------------------------------------------------
-- Base case: noredex-fixpoint-apply (position 14)
------------------------------------------------------------------------

abstract
  noredex-fixpoint-apply : ∀ {A B} → (normalize ∘ encode (apply {A} {B})) ⟶* encode (apply {A} {B})
  noredex-fixpoint-apply {A} {B} = step1 >> step2 >> step3 >> step4
    where
      N : Term TermCode' TermCode'
      N = cata TermF normalize-step

      payload : Term Unit (TyFuncCode * TyFuncCode)
      payload = ⟨ ⌜ A ⌝Ty , ⌜ B ⌝Ty ⟩

      step1 : (N ∘ (In {TermF} ∘ (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ payload))) ⟶*
              ((normalize-step ∘ fmap TermF N) ∘ (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ payload))
      step1 = cata-β-right {TermF} {TermCode'} {Unit} {normalize-step} {inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ payload}

      reduce-chain : (fmap TermF N ∘ (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ payload)) ⟶*
                     (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ payload)
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
        (⟶1 assoc-l >> ∘-cong-left' _ (fmap-13-inr N) >> ⟶1 assoc-r >> ∘-cong-right' inr
        (∘-cong-left' payload (fmap-KK-id TyFuncCode TyFuncCode N) >> ⟶1 id-left))))))))))))))

      inner-step : (normalize-step ∘ (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ payload)) ⟶* (handle-apply ∘ payload)
      inner-step = ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >> ∘-cong-left' payload nstep-at-14'

      step2 : ((normalize-step ∘ fmap TermF N) ∘ (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ payload)) ⟶* (handle-apply ∘ payload)
      step2 = ⟶1 assoc-r >> ∘-cong-right' normalize-step reduce-chain >> inner-step

      step3 : (handle-apply ∘ payload) ⟶* ((In {TermF} ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr) ∘ payload)
      step3 = done

      step4 : ((In {TermF} ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr) ∘ payload) ⟶* (In {TermF} ∘ (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ payload))
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
              (⟶1 assoc-r >> ∘-cong-right' inr
              (⟶1 assoc-r >> ∘-cong-right' inr (⟶1 assoc-r)))))))))))))
