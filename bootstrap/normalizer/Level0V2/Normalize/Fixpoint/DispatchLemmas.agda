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

------------------------------------------------------------------------
-- is-id behavior on non-id encoded terms
--
-- Key lemma: For non-id terms, is-id returns inr ∘ encode t.
-- This is because:
--   1. encode t at position N has form: In ∘ inj-N ∘ payload
--   2. Out ∘ In ∘ ... ⟶* ... (via out-in)
--   3. is-id-dispatch at position N returns ret-no-N
--   4. ret-no-N = inr ∘ rebuild-N exactly reconstructs the encoding
------------------------------------------------------------------------

-- Tails of is-id-dispatch for navigating the nested case structure
is-id-tail-1 : Term (⟦ TermF-1 ⟧F TermCode') (Unit + TermCode')
is-id-tail-1 =
  [ ret-no-1
  , [ ret-no-2
    , [ ret-no-3
      , [ ret-no-4
        , [ ret-no-5
          , [ ret-no-6
            , [ ret-no-7
              , [ ret-no-8
                , [ ret-no-9
                  , [ ret-no-10
                    , [ ret-no-11
                      , [ ret-no-12
                        , [ ret-no-13
                          , ret-no-14
                          ]
                        ]
                      ]
                    ]
                  ]
                ]
              ]
            ]
          ]
        ]
      ]
    ]
  ]

-- Reduction: is-id-dispatch ∘ inr ⟶ is-id-tail-1
abstract
  is-id-dispatch-inr : (is-id-dispatch ∘ inr) ⟶ is-id-tail-1
  is-id-dispatch-inr = case-inr

-- Reduction for position 1 (composition): is-id-tail-1 ∘ inl ⟶ ret-no-1
abstract
  is-id-tail-1-inl : (is-id-tail-1 ∘ inl) ⟶ ret-no-1
  is-id-tail-1-inl = case-inl

-- Key lemma: For composition (f ∘ g), is-id returns inr ∘ encode (f ∘ g)
-- encode (f ∘ g) = In ∘ inr ∘ inl ∘ ⟨encode f, encode g⟩
-- So: is-id ∘ encode (f ∘ g)
--   = is-id-dispatch ∘ Out ∘ In ∘ inr ∘ inl ∘ payload
--   ⟶* is-id-dispatch ∘ inr ∘ inl ∘ payload  (via out-in)
--   ⟶* is-id-tail-1 ∘ inl ∘ payload          (via case-inr)
--   ⟶* ret-no-1 ∘ payload                     (via case-inl)
--   = inr ∘ rebuild-1 ∘ payload
--   = inr ∘ (In ∘ inr ∘ inl) ∘ payload
--   = inr ∘ encode (f ∘ g)

------------------------------------------------------------------------
-- handle-comp-rebuild: The main theorem for composition handling
--
-- For NoRedex compositions where neither operand is id, handle-comp
-- reduces to rebuild-1 (which just reconstructs the composition encoding).
------------------------------------------------------------------------

-- Helper: is-id returns inr for NoRedex non-id terms
-- Postulated due to Agda associativity handling issues in chain proofs.
-- The proof outline is documented below.
--
-- For each non-id position N (1-14), the reduction is:
--   is-id ∘ encode t
--   = (is-id-dispatch ∘ Out) ∘ (In ∘ inr ∘ inj-N ∘ payload)
--   ⟶* is-id-dispatch ∘ (inr ∘ inj-N ∘ payload)     [via Out ∘ In ⟶ id]
--   ⟶* is-id-tail-1 ∘ (inj-N ∘ payload)             [via case-inr: not position 0]
--   ⟶* ret-no-N ∘ payload                           [via N-1 case-inr's then case-inl]
--   = (inr ∘ rebuild-N) ∘ payload
--   ⟶ inr ∘ (rebuild-N ∘ payload)                   [via assoc-r]
--   = inr ∘ encode t                                 [by definition: rebuild-N ∘ payload = encode t]
postulate
  is-id-noredex : ∀ {A B} (t : Term A B) → NotIdStruct t →
                  (is-id ∘ encode t) ⟶* (inr ∘ encode t)

abstract
  handle-comp-rebuild-noredex : ∀ {A B C D} {f : Term A B} {g : Term C D} →
                                NoRedex f → NoRedex g → NotIdStruct f → NotIdStruct g →
                                (handle-comp ∘ ⟨ encode f , encode g ⟩) ⟶*
                                ((In ∘ inr ∘ inl) ∘ ⟨ encode f , encode g ⟩)
  handle-comp-rebuild-noredex {f = f} {g = g} nrf nrg nisf nisg = runChain (
    let payload = ⟨ encode f , encode g ⟩ in
    -- handle-comp = caseWithCtx comp-f-is-id check-g-handler ∘ prep-check-f-id
    -- prep-check-f-id = ⟨ snd , is-id ∘ fst ⟩
    (handle-comp ∘ payload)
      ∵ done ⟶
    ((caseWithCtx comp-f-is-id check-g-handler ∘ prep-check-f-id) ∘ payload)
      ∵ ⟶1 assoc-r ⟶
    (caseWithCtx comp-f-is-id check-g-handler ∘ (prep-check-f-id ∘ payload))
      ∵ ∘-cong-right' (caseWithCtx comp-f-is-id check-g-handler) prep-step ⟶
    (caseWithCtx comp-f-is-id check-g-handler ∘ ⟨ encode g , inr ∘ encode f ⟩)
      ∵ caseWithCtx-inr ⟶  -- Because is-id returned inr, take the check-g branch
    (check-g-handler ∘ ⟨ encode g , encode f ⟩)
      ∵ check-g-step ⟶
    (comp-fallback ∘ ⟨ encode f , encode g ⟩)
      ∵ done ⟶  -- comp-fallback = rebuild-1 = In ∘ inr ∘ inl
    ((In ∘ inr ∘ inl) ∘ ⟨ encode f , encode g ⟩)
      ∎)
    where
      -- Step 1: prep-check-f-id ∘ payload ⟶* ⟨encode g, inr ∘ encode f⟩
      prep-step : (prep-check-f-id ∘ ⟨ encode f , encode g ⟩) ⟶*
                  ⟨ encode g , inr ∘ encode f ⟩
      prep-step =
        ⟶1 pair-comp >>
        ⟨⟩-cong
          (⟶1 snd-pair)
          (⟶1 assoc-r >> ∘-cong-right' is-id (⟶1 fst-pair) >> is-id-noredex f nisf)

      -- Step 2: check-g-handler ∘ ⟨encode g, encode f⟩ ⟶* comp-fallback ∘ ⟨encode f, encode g⟩
      -- check-g-handler = caseWithCtx comp-g-is-id comp-fallback ∘ prep-check-g-id
      check-g-step : (check-g-handler ∘ ⟨ encode g , encode f ⟩) ⟶*
                     (comp-fallback ∘ ⟨ encode f , encode g ⟩)
      check-g-step =
        -- check-g-handler = caseWithCtx comp-g-is-id comp-fallback ∘ prep-check-g-id
        ⟶1 assoc-r >>
        ∘-cong-right' (caseWithCtx comp-g-is-id comp-fallback) prep-g-step >>
        caseWithCtx-inr  -- Because is-id returned inr, take fallback branch
        where
          prep-g-step : (prep-check-g-id ∘ ⟨ encode g , encode f ⟩) ⟶*
                        ⟨ encode f , inr ∘ encode g ⟩
          prep-g-step =
            ⟶1 pair-comp >>
            ⟨⟩-cong
              (⟶1 snd-pair)
              (⟶1 assoc-r >> ∘-cong-right' is-id (⟶1 fst-pair) >> is-id-noredex g nisg)

-- Wrapper: handle-comp-rebuild with the old signature for compatibility
-- This delegates to handle-comp-rebuild-noredex
abstract
  handle-comp-rebuild : ∀ {A B C D} {f : Term A B} {g : Term C D} →
                        NoRedex f → NoRedex g → NotIdStruct f → NotIdStruct g →
                        (handle-comp ∘ ⟨ encode f , encode g ⟩) ⟶*
                        ((In ∘ inr ∘ inl) ∘ ⟨ encode f , encode g ⟩)
  handle-comp-rebuild = handle-comp-rebuild-noredex

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
