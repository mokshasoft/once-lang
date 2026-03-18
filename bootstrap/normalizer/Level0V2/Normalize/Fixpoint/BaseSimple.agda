------------------------------------------------------------------------
-- Fixpoint.BaseSimple: Simple base case fixpoint proofs
--
-- For NoRedex primitives (id, fst, snd, inl, inr, terminal, initial)
-- that have no subterms.
------------------------------------------------------------------------

module normalizer.Level0V2.Normalize.Fixpoint.BaseSimple where

open import normalizer.Level0V2.Normalize.Fixpoint.DispatchLemmas public

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
-- Base case: noredex-fixpoint-initial (position 9)
------------------------------------------------------------------------

abstract
  noredex-fixpoint-initial : ∀ {A} → (normalize ∘ encode (initial {A})) ⟶* encode (initial {A})
  noredex-fixpoint-initial {A} = step1 >> step2 >> step3 >> step4
    where
      N : Term TermCode' TermCode'
      N = cata TermF normalize-step

      payload : Term Unit TyFuncCode
      payload = ⌜ A ⌝Ty

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

      inner-step : (normalize-step ∘ (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ payload)) ⟶* (handle-initial ∘ payload)
      inner-step = ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >> ∘-cong-left' payload nstep-at-9'

      step2 : ((normalize-step ∘ fmap TermF N) ∘ (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ payload)) ⟶* (handle-initial ∘ payload)
      step2 = ⟶1 assoc-r >> ∘-cong-right' normalize-step reduce-chain >> inner-step

      step3 : (handle-initial ∘ payload) ⟶* ((In {TermF} ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl) ∘ payload)
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
