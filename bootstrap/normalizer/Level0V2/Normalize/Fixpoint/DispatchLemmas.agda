------------------------------------------------------------------------
-- Fixpoint.DispatchLemmas: Position dispatch lemmas for normalize-step
--
-- Left-associated versions of nstep-at-N lemmas.
-- Wrapped in abstract to prevent term expansion.
------------------------------------------------------------------------

module normalizer.Level0V2.Normalize.Fixpoint.DispatchLemmas where

open import normalizer.Level0V2.Normalize.NstepDispatch public
open import normalizer.Level0V2.Normalizer public
  using (∘-cong-left'; ∘-cong-right'; cata-β-right; fmap-TermF-inl;
         fmap-TermF-inr; fmap-1-inr; fmap-2-inr; fmap-3-inr; fmap-4-inr;
         fmap-5-inr; fmap-6-inr; fmap-7-inr; fmap-8-inr; fmap-9-inr;
         fmap-10-inr; fmap-11-inr; fmap-12-inr; fmap-13-inr;
         fmap-1-inl; fmap-2-inl; fmap-3-inl; fmap-4-inl; fmap-5-inl;
         fmap-6-inl; fmap-7-inl; fmap-8-inl; fmap-9-inl; fmap-10-inl;
         fmap-11-inl; fmap-12-inl; fmap-13-inl;
         fmap-KK-id; TermF-13; TermF-14; fmap-sum-inl)

-- Proof obligation: handle-comp reduces to rebuild
-- (When inputs are non-id NoRedex terms)
postulate
  handle-comp-rebuild : ∀ {X} (payload : Term X (TermCode' * TermCode')) →
                        (handle-comp ∘ payload) ⟶* ((In ∘ inr ∘ inl) ∘ payload)

------------------------------------------------------------------------
-- Payload functor for curry (position 13): (K⊗K) ⊗ (K⊗Id)
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

  nstep-at-9' : ((((((((((normalize-step ∘ inr) ∘ inr) ∘ inr) ∘ inr) ∘ inr) ∘ inr) ∘ inr) ∘ inr) ∘ inr) ∘ inl) ⟶* handle-initial
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

  nstep-at-10' : (((((((((((normalize-step ∘ inr) ∘ inr) ∘ inr) ∘ inr) ∘ inr) ∘ inr) ∘ inr) ∘ inr) ∘ inr) ∘ inr) ∘ inl) ⟶* handle-In
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

  nstep-at-11' : ((((((((((((normalize-step ∘ inr) ∘ inr) ∘ inr) ∘ inr) ∘ inr) ∘ inr) ∘ inr) ∘ inr) ∘ inr) ∘ inr) ∘ inr) ∘ inl) ⟶* handle-Out
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

  nstep-at-12' : (((((((((((((normalize-step ∘ inr) ∘ inr) ∘ inr) ∘ inr) ∘ inr) ∘ inr) ∘ inr) ∘ inr) ∘ inr) ∘ inr) ∘ inr) ∘ inr) ∘ inl) ⟶* handle-cata
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

  nstep-at-13' : ((((((((((((((normalize-step ∘ inr) ∘ inr) ∘ inr) ∘ inr) ∘ inr) ∘ inr) ∘ inr) ∘ inr) ∘ inr) ∘ inr) ∘ inr) ∘ inr) ∘ inr) ∘ inl) ⟶* handle-curry
  nstep-at-13' =
    ⟶1 (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l nstep-inr))))))))))))) >>
    ⟶1 (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l tail-1-inr)))))))))))) >>
    ⟶1 (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l tail-2-inr))))))))))) >>
    ⟶1 (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l tail-3-inr)))))))))) >>
    ⟶1 (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l tail-4-inr))))))))) >>
    ⟶1 (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l tail-5-inr)))))))) >>
    ⟶1 (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l tail-6-inr))))))) >>
    ⟶1 (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l tail-7-inr)))))) >>
    ⟶1 (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l tail-8-inr))))) >>
    ⟶1 (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l tail-9-inr)))) >>
    ⟶1 (⟶-∘-l (⟶-∘-l (⟶-∘-l tail-10-inr))) >>
    ⟶1 (⟶-∘-l (⟶-∘-l tail-11-inr)) >>
    ⟶1 (⟶-∘-l tail-12-inr) >>
    ⟶1 tail-13-inl

  nstep-at-14' : ((((((((((((((normalize-step ∘ inr) ∘ inr) ∘ inr) ∘ inr) ∘ inr) ∘ inr) ∘ inr) ∘ inr) ∘ inr) ∘ inr) ∘ inr) ∘ inr) ∘ inr) ∘ inr) ⟶* handle-apply
  nstep-at-14' =
    ⟶1 (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l nstep-inr))))))))))))) >>
    ⟶1 (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l tail-1-inr)))))))))))) >>
    ⟶1 (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l tail-2-inr))))))))))) >>
    ⟶1 (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l tail-3-inr)))))))))) >>
    ⟶1 (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l tail-4-inr))))))))) >>
    ⟶1 (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l tail-5-inr)))))))) >>
    ⟶1 (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l tail-6-inr))))))) >>
    ⟶1 (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l tail-7-inr)))))) >>
    ⟶1 (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l tail-8-inr))))) >>
    ⟶1 (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l tail-9-inr)))) >>
    ⟶1 (⟶-∘-l (⟶-∘-l (⟶-∘-l tail-10-inr))) >>
    ⟶1 (⟶-∘-l (⟶-∘-l tail-11-inr)) >>
    ⟶1 (⟶-∘-l tail-12-inr) >>
    ⟶1 tail-13-inr

  ------------------------------------------------------------------------
  -- Key lemma: normalize-step ∘ inl ⟶ handle-id = In ∘ inl
  ------------------------------------------------------------------------

  nstep-inl : (normalize-step ∘ inl) ⟶ handle-id
  nstep-inl = case-inl
