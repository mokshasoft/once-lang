------------------------------------------------------------------------
-- Fixpoint.MainTheorem: Main fixpoint theorem by structural induction
--
-- For NoRedex t: normalize ∘ encode t ⟶* encode t
------------------------------------------------------------------------

module normalizer.Implementation.Normalize.Fixpoint.MainTheorem where

open import normalizer.Implementation.Normalize.Fixpoint.BaseSimple public
open import normalizer.Implementation.Normalize.Fixpoint.BaseRecursive public

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
  noredex-fixpoint initial nr-initial = noredex-fixpoint-initial
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

  -- Position 13 (curry): encode (curry f) = In ∘ inr^13 ∘ inl ∘ ⟨⟨⌜A⌝,⌜B⌝⟩, ⟨⌜C⌝, encode f⟩⟩
  noredex-fixpoint (curry {A} {B} {C} f) (nr-curry nrf) = step1 >> step2 >> step3 >> step4
    where
    N : Term TermCode' TermCode'
    N = cata TermF normalize-step

    payload : Term Unit ((TyFuncCode * TyFuncCode) * (TyFuncCode * TermCode'))
    payload = ⟨ ⟨ ⌜ A ⌝Ty , ⌜ B ⌝Ty ⟩ , ⟨ ⌜ C ⌝Ty , encode f ⟩ ⟩

    step1 : (N ∘ (In {TermF} ∘ (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ payload))) ⟶*
            ((normalize-step ∘ fmap TermF N) ∘ (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ payload))
    step1 = cata-β-right {TermF} {TermCode'} {Unit} {normalize-step} {inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ payload}

    -- 13 inr navigations
    reduce-chain : (fmap TermF N ∘ (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ payload)) ⟶*
                   (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ payload)
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
      (⟶1 assoc-l >> ∘-cong-left' payload curry-fmap-13-inl >> ⟶1 assoc-r >> ∘-cong-right' inl curry-ih-step)))))))))))))
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

        curry-fmap-13-inl : (fmap TermF-13 N ∘ inl) ⟶* (inl ∘ fmap CurryPayloadF N)
        curry-fmap-13-inl = fmap-sum-inl CurryPayloadF TermF-14 N

    inner-step : (normalize-step ∘ (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ payload)) ⟶* (handle-curry ∘ payload)
    inner-step =
      ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >>
      ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >>
      ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >>
      ∘-cong-left' payload nstep-at-13'

    step2 : ((normalize-step ∘ fmap TermF N) ∘ (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ payload)) ⟶*
            (handle-curry ∘ payload)
    step2 = ⟶1 assoc-r >> ∘-cong-right' normalize-step reduce-chain >> inner-step

    step3 : (handle-curry ∘ payload) ⟶* ((In {TermF} ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl) ∘ payload)
    step3 = done

    step4 : ((In {TermF} ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl) ∘ payload) ⟶*
            (In {TermF} ∘ (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ payload))
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

  -- Position 12 (cata): encode (cata F alg) = In ∘ inr^12 ∘ inl ∘ ⟨⌜F⌝, encode alg⟩
  noredex-fixpoint (cata F alg) (nr-cata nralg) = step1 >> step2 >> step3 >> step4
    where
    N : Term TermCode' TermCode'
    N = cata TermF normalize-step

    payload : Term Unit (TyFuncCode * TermCode')
    payload = ⟨ ⌜ F ⌝Func , encode alg ⟩

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
      (⟶1 assoc-l >> ∘-cong-left' payload cata-fmap-12-inl >> ⟶1 assoc-r >> ∘-cong-right' inl cata-ih-step))))))))))))
      where
        cata-ih-step : (fmap (K TyFuncCode ⊗ Id) N ∘ payload) ⟶* payload
        cata-ih-step =
          ⟶1 pair-comp >>
          ⟨⟩-cong
            (⟶1 assoc-r >> ⟶1 id-left >> ⟶1 fst-pair)
            (⟶1 assoc-r >> ∘-cong-right' N (⟶1 snd-pair) >> noredex-fixpoint alg nralg)

        cata-fmap-12-inl : (fmap TermF-12 N ∘ inl) ⟶* (inl ∘ fmap (K TyFuncCode ⊗ Id) N)
        cata-fmap-12-inl = fmap-sum-inl (K TyFuncCode ⊗ Id) TermF-13 N

    inner-step : (normalize-step ∘ (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ payload)) ⟶* (handle-cata ∘ payload)
    inner-step =
      ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >>
      ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >>
      ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >> ⟶1 assoc-l >>
      ∘-cong-left' payload nstep-at-12'

    step2 : ((normalize-step ∘ fmap TermF N) ∘ (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ payload)) ⟶*
            (handle-cata ∘ payload)
    step2 = ⟶1 assoc-r >> ∘-cong-right' normalize-step reduce-chain >> inner-step

    step3 : (handle-cata ∘ payload) ⟶* ((In {TermF} ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl) ∘ payload)
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

  -- Position 1 (comp): encode (f ∘ g) = In ∘ inr ∘ inl ∘ ⟨encode f, encode g⟩
  noredex-fixpoint (f ∘ g) (nr-comp nrf nrg sc) = step1 >> step2 >> step3 >> step4
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
    step3 = handle-comp-rebuild nrf nrg (safecomp-notid-f sc) (safecomp-notid-g sc)

    step4 : ((In {TermF} ∘ inr ∘ inl) ∘ payload) ⟶* (In {TermF} ∘ (inr ∘ inl ∘ payload))
    step4 = ⟶1 assoc-r >> ∘-cong-right' In (⟶1 assoc-r)
