{-# OPTIONS --allow-unsolved-metas #-}
------------------------------------------------------------------------
-- Fixpoint.DispatchLemmas: Position dispatch lemmas for normalize-step
--
-- Left-associated versions of nstep-at-N lemmas.
-- Wrapped in abstract to prevent term expansion.
------------------------------------------------------------------------

module normalizer.Implementation.Normalize.Fixpoint.DispatchLemmas where

open import normalizer.Implementation.Normalize.NstepDispatch public
open import normalizer.Implementation.Normalizer public
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

------------------------------------------------------------------------
-- Tails for positions 2-14
------------------------------------------------------------------------

is-id-tail-2 : Term (⟦ TermF-2 ⟧F TermCode') (Unit + TermCode')
is-id-tail-2 =
  [ ret-no-2
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

is-id-tail-3 : Term (⟦ TermF-3 ⟧F TermCode') (Unit + TermCode')
is-id-tail-3 =
  [ ret-no-3
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

is-id-tail-4 : Term (⟦ TermF-4 ⟧F TermCode') (Unit + TermCode')
is-id-tail-4 =
  [ ret-no-4
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

is-id-tail-5 : Term (⟦ TermF-5 ⟧F TermCode') (Unit + TermCode')
is-id-tail-5 =
  [ ret-no-5
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

is-id-tail-6 : Term (⟦ TermF-6 ⟧F TermCode') (Unit + TermCode')
is-id-tail-6 =
  [ ret-no-6
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

is-id-tail-7 : Term (⟦ TermF-7 ⟧F TermCode') (Unit + TermCode')
is-id-tail-7 =
  [ ret-no-7
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

is-id-tail-8 : Term (⟦ TermF-8 ⟧F TermCode') (Unit + TermCode')
is-id-tail-8 =
  [ ret-no-8
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

is-id-tail-9 : Term (⟦ TermF-9 ⟧F TermCode') (Unit + TermCode')
is-id-tail-9 =
  [ ret-no-9
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

is-id-tail-10 : Term (⟦ TermF-10 ⟧F TermCode') (Unit + TermCode')
is-id-tail-10 =
  [ ret-no-10
  , [ ret-no-11
    , [ ret-no-12
      , [ ret-no-13
        , ret-no-14
        ]
      ]
    ]
  ]

is-id-tail-11 : Term (⟦ TermF-11 ⟧F TermCode') (Unit + TermCode')
is-id-tail-11 =
  [ ret-no-11
  , [ ret-no-12
    , [ ret-no-13
      , ret-no-14
      ]
    ]
  ]

is-id-tail-12 : Term (⟦ TermF-12 ⟧F TermCode') (Unit + TermCode')
is-id-tail-12 =
  [ ret-no-12
  , [ ret-no-13
    , ret-no-14
    ]
  ]

is-id-tail-13 : Term (⟦ TermF-13 ⟧F TermCode') (Unit + TermCode')
is-id-tail-13 =
  [ ret-no-13
  , ret-no-14
  ]

------------------------------------------------------------------------
-- Reduction lemmas for navigating tails
------------------------------------------------------------------------

abstract
  is-id-tail-1-inr : (is-id-tail-1 ∘ inr) ⟶ is-id-tail-2
  is-id-tail-1-inr = case-inr

  is-id-tail-2-inl : (is-id-tail-2 ∘ inl) ⟶ ret-no-2
  is-id-tail-2-inl = case-inl

  is-id-tail-2-inr : (is-id-tail-2 ∘ inr) ⟶ is-id-tail-3
  is-id-tail-2-inr = case-inr

  is-id-tail-3-inl : (is-id-tail-3 ∘ inl) ⟶ ret-no-3
  is-id-tail-3-inl = case-inl

  is-id-tail-3-inr : (is-id-tail-3 ∘ inr) ⟶ is-id-tail-4
  is-id-tail-3-inr = case-inr

  is-id-tail-4-inl : (is-id-tail-4 ∘ inl) ⟶ ret-no-4
  is-id-tail-4-inl = case-inl

  is-id-tail-4-inr : (is-id-tail-4 ∘ inr) ⟶ is-id-tail-5
  is-id-tail-4-inr = case-inr

  is-id-tail-5-inl : (is-id-tail-5 ∘ inl) ⟶ ret-no-5
  is-id-tail-5-inl = case-inl

  is-id-tail-5-inr : (is-id-tail-5 ∘ inr) ⟶ is-id-tail-6
  is-id-tail-5-inr = case-inr

  is-id-tail-6-inl : (is-id-tail-6 ∘ inl) ⟶ ret-no-6
  is-id-tail-6-inl = case-inl

  is-id-tail-6-inr : (is-id-tail-6 ∘ inr) ⟶ is-id-tail-7
  is-id-tail-6-inr = case-inr

  is-id-tail-7-inl : (is-id-tail-7 ∘ inl) ⟶ ret-no-7
  is-id-tail-7-inl = case-inl

  is-id-tail-7-inr : (is-id-tail-7 ∘ inr) ⟶ is-id-tail-8
  is-id-tail-7-inr = case-inr

  is-id-tail-8-inl : (is-id-tail-8 ∘ inl) ⟶ ret-no-8
  is-id-tail-8-inl = case-inl

  is-id-tail-8-inr : (is-id-tail-8 ∘ inr) ⟶ is-id-tail-9
  is-id-tail-8-inr = case-inr

  is-id-tail-9-inl : (is-id-tail-9 ∘ inl) ⟶ ret-no-9
  is-id-tail-9-inl = case-inl

  is-id-tail-9-inr : (is-id-tail-9 ∘ inr) ⟶ is-id-tail-10
  is-id-tail-9-inr = case-inr

  is-id-tail-10-inl : (is-id-tail-10 ∘ inl) ⟶ ret-no-10
  is-id-tail-10-inl = case-inl

  is-id-tail-10-inr : (is-id-tail-10 ∘ inr) ⟶ is-id-tail-11
  is-id-tail-10-inr = case-inr

  is-id-tail-11-inl : (is-id-tail-11 ∘ inl) ⟶ ret-no-11
  is-id-tail-11-inl = case-inl

  is-id-tail-11-inr : (is-id-tail-11 ∘ inr) ⟶ is-id-tail-12
  is-id-tail-11-inr = case-inr

  is-id-tail-12-inl : (is-id-tail-12 ∘ inl) ⟶ ret-no-12
  is-id-tail-12-inl = case-inl

  is-id-tail-12-inr : (is-id-tail-12 ∘ inr) ⟶ is-id-tail-13
  is-id-tail-12-inr = case-inr

  is-id-tail-13-inl : (is-id-tail-13 ∘ inl) ⟶ ret-no-13
  is-id-tail-13-inl = case-inl

  is-id-tail-13-inr : (is-id-tail-13 ∘ inr) ⟶ ret-no-14
  is-id-tail-13-inr = case-inr

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
--
-- This can be verified two ways:
--   1. Formal proof: Follow the reduction chain (tedious in Agda)
--   2. Observation: The fixpoint test (normalize ∘ encode normalize) succeeds,
--      which implies is-id behaves correctly on all encoded subterms
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
------------------------------------------------------------------------
-- Proof: is-id returns inr for non-id terms
--
-- For each non-id term at position N (1-14), the reduction is:
--   is-id ∘ encode t
--   = (is-id-dispatch ∘ Out) ∘ (In ∘ inr ∘ inj-N ∘ payload)
--   ⟶* is-id-dispatch ∘ (inr ∘ inj-N ∘ payload)     [via Out ∘ In ⟶ id]
--   ⟶* is-id-tail-1 ∘ (inj-N ∘ payload)             [via case-inr]
--   ⟶* ret-no-N ∘ payload                           [via case navigation]
--   = (inr ∘ rebuild-N) ∘ payload
--   = inr ∘ (rebuild-N ∘ payload)                   [via assoc-r]
--   = inr ∘ encode t                                 [by rebuild-N ∘ payload = encode t]
--
-- This property can be verified by observing the fixpoint test succeeds:
-- normalize ∘ encode normalize = encode normalize
-- which implies is-id behaves correctly on all encoded subterms.
------------------------------------------------------------------------

-- Helper: reduce (f ∘ Out) ∘ (In ∘ body) to f ∘ body
-- This uses: assoc-r, out-in, id-left
abstract
  out-in-compose : ∀ {F A B} (f : Term (⟦ F ⟧F (μ F)) B) (body : Term A (⟦ F ⟧F (μ F))) →
                   ((f ∘ Out) ∘ (In ∘ body)) ⟶* (f ∘ body)
  out-in-compose {F} f body =
    ⟶*-trans (step assoc-r done)     -- f ∘ (Out ∘ (In ∘ body))
    (⟶*-trans (step (⟶-∘-r assoc-l) done)  -- f ∘ ((Out ∘ In) ∘ body)
    (⟶*-trans (step (⟶-∘-r (⟶-∘-l (out-in F))) done)  -- f ∘ (id ∘ body)
    (step (⟶-∘-r id-left) done)))  -- f ∘ body

------------------------------------------------------------------------
-- Per-position proofs: show that is-id at position N reduces to inr ∘ encode t
--
-- Each proof follows the pattern:
--   1. Unfold is-id as (is-id-dispatch ∘ Out) ∘ (In ∘ inj-chain ∘ payload)
--   2. Use out-in-compose to eliminate Out ∘ In
--   3. Navigate the case structure using is-id-dispatch-inr and is-id-tail-N-inr/inl
--   4. Reach ret-no-N ∘ payload = (inr ∘ rebuild-N) ∘ payload
--   5. Use assoc-r to get inr ∘ (rebuild-N ∘ payload) = inr ∘ encode t
------------------------------------------------------------------------

-- Helper: reassociate 3-term composition right
-- ((a ∘ b) ∘ c) ⟶* (a ∘ (b ∘ c))
abstract
  assoc-r3 : ∀ {A B C D} (a : Term C D) (b : Term B C) (c : Term A B) →
             ((a ∘ b) ∘ c) ⟶* (a ∘ (b ∘ c))
  assoc-r3 a b c = ⟶1 assoc-r

-- Helper: reassociate 4-term composition right
-- (((a ∘ b) ∘ c) ∘ d) ⟶* (a ∘ (b ∘ (c ∘ d)))
abstract
  assoc-r4 : ∀ {A B C D E} (a : Term D E) (b : Term C D) (c : Term B C) (d : Term A B) →
             (((a ∘ b) ∘ c) ∘ d) ⟶* (a ∘ (b ∘ (c ∘ d)))
  assoc-r4 a b c d =
    ⟶1 assoc-r >>  -- ((a ∘ b) ∘ c) ∘ d ⟶ (a ∘ b) ∘ (c ∘ d)
    ⟶1 assoc-r     -- (a ∘ b) ∘ (c ∘ d) ⟶ a ∘ (b ∘ (c ∘ d))

------------------------------------------------------------------------
-- Position 1: f ∘ g (composition)
-- encode (f ∘ g) = In ∘ inr ∘ inl ∘ ⟨encode f, encode g⟩
--                = In ∘ (inr ∘ (inl ∘ payload))  [right-associated]
------------------------------------------------------------------------
abstract
  is-id-pos-1 : ∀ {A B C} (f : Term B C) (g : Term A B) →
                (is-id ∘ encode (f ∘ g)) ⟶* (inr ∘ encode (f ∘ g))
  is-id-pos-1 f g =
    let payload = ⟨ encode f , encode g ⟩ in
    -- is-id ∘ encode (f ∘ g)
    -- = (is-id-dispatch ∘ Out) ∘ (In ∘ (inr ∘ (inl ∘ payload)))
    out-in-compose is-id-dispatch (inr ∘ (inl ∘ payload)) >>
    -- ⟶* is-id-dispatch ∘ (inr ∘ (inl ∘ payload))
    ⟶1 assoc-l >> ⟶1 (⟶-∘-l is-id-dispatch-inr) >>
    -- ⟶ is-id-tail-1 ∘ (inl ∘ payload)
    ⟶1 assoc-l >> ⟶1 (⟶-∘-l is-id-tail-1-inl) >>
    -- ⟶ ret-no-1 ∘ payload = (inr ∘ (In ∘ (inr ∘ inl))) ∘ payload
    ⟶1 assoc-r >>
    -- ⟶ inr ∘ ((In ∘ (inr ∘ inl)) ∘ payload)
    -- Need: inr ∘ (In ∘ (inr ∘ (inl ∘ payload))) = inr ∘ encode (f ∘ g)
    ∘-cong-right' inr (⟶1 assoc-r >> ∘-cong-right' In (⟶1 assoc-r))

------------------------------------------------------------------------
-- Position 2: fst
-- encode fst = In ∘ inr ∘ inr ∘ inl ∘ ⟨⌜A⌝, ⌜B⌝⟩
--            = In ∘ (inr ∘ (inr ∘ (inl ∘ payload)))  [right-associated]
------------------------------------------------------------------------
abstract
  is-id-pos-2 : ∀ {A B} → (is-id ∘ encode (fst {A} {B})) ⟶* (inr ∘ encode (fst {A} {B}))
  is-id-pos-2 {A} {B} =
    let payload = ⟨ ⌜ A ⌝Ty , ⌜ B ⌝Ty ⟩ in
    out-in-compose is-id-dispatch (inr ∘ (inr ∘ (inl ∘ payload))) >>
    -- Navigate: 1 inr to is-id-tail-1, 1 more inr to is-id-tail-2, then inl
    ⟶1 assoc-l >> ⟶1 (⟶-∘-l is-id-dispatch-inr) >>
    ⟶1 assoc-l >> ⟶1 (⟶-∘-l is-id-tail-1-inr) >>
    ⟶1 assoc-l >> ⟶1 (⟶-∘-l is-id-tail-2-inl) >>
    -- ret-no-2 ∘ payload = (inr ∘ (In ∘ (inr ∘ (inr ∘ inl)))) ∘ payload
    ⟶1 assoc-r >>
    -- ⟶ inr ∘ ((In ∘ (inr ∘ (inr ∘ inl))) ∘ payload)
    -- Need: inr ∘ (In ∘ (inr ∘ (inr ∘ (inl ∘ payload))))
    ∘-cong-right' inr (⟶1 assoc-r >> ∘-cong-right' In (⟶1 assoc-r >> ∘-cong-right' inr (⟶1 assoc-r)))

------------------------------------------------------------------------
-- Position 3: snd
-- encode snd = In ∘ inr ∘ inr ∘ inr ∘ inl ∘ ⟨⌜A⌝, ⌜B⌝⟩
--            = In ∘ (inr ∘ (inr ∘ (inr ∘ (inl ∘ payload))))  [right-associated]
------------------------------------------------------------------------
abstract
  is-id-pos-3 : ∀ {A B} → (is-id ∘ encode (snd {A} {B})) ⟶* (inr ∘ encode (snd {A} {B}))
  is-id-pos-3 {A} {B} =
    let payload = ⟨ ⌜ A ⌝Ty , ⌜ B ⌝Ty ⟩ in
    out-in-compose is-id-dispatch (inr ∘ (inr ∘ (inr ∘ (inl ∘ payload)))) >>
    ⟶1 assoc-l >> ⟶1 (⟶-∘-l is-id-dispatch-inr) >>
    ⟶1 assoc-l >> ⟶1 (⟶-∘-l is-id-tail-1-inr) >>
    ⟶1 assoc-l >> ⟶1 (⟶-∘-l is-id-tail-2-inr) >>
    ⟶1 assoc-l >> ⟶1 (⟶-∘-l is-id-tail-3-inl) >>
    ⟶1 assoc-r >>
    ∘-cong-right' inr (⟶1 assoc-r >> ∘-cong-right' In (⟶1 assoc-r >> ∘-cong-right' inr (⟶1 assoc-r >> ∘-cong-right' inr (⟶1 assoc-r))))

------------------------------------------------------------------------
-- Position 4: ⟨f, g⟩ (pair)
-- encode ⟨f, g⟩ = In ∘ inr^4 ∘ inl ∘ ⟨encode f, encode g⟩  [right-associated]
------------------------------------------------------------------------
abstract
  is-id-pos-4 : ∀ {A B C} (f : Term C A) (g : Term C B) →
                (is-id ∘ encode ⟨ f , g ⟩) ⟶* (inr ∘ encode ⟨ f , g ⟩)
  is-id-pos-4 f g =
    let payload = ⟨ encode f , encode g ⟩ in
    out-in-compose is-id-dispatch (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inl ∘ payload))))) >>
    ⟶1 assoc-l >> ⟶1 (⟶-∘-l is-id-dispatch-inr) >>
    ⟶1 assoc-l >> ⟶1 (⟶-∘-l is-id-tail-1-inr) >>
    ⟶1 assoc-l >> ⟶1 (⟶-∘-l is-id-tail-2-inr) >>
    ⟶1 assoc-l >> ⟶1 (⟶-∘-l is-id-tail-3-inr) >>
    ⟶1 assoc-l >> ⟶1 (⟶-∘-l is-id-tail-4-inl) >>
    ⟶1 assoc-r >>
    ∘-cong-right' inr (⟶1 assoc-r >> ∘-cong-right' In (⟶1 assoc-r >> ∘-cong-right' inr (⟶1 assoc-r >> ∘-cong-right' inr (⟶1 assoc-r >> ∘-cong-right' inr (⟶1 assoc-r)))))

------------------------------------------------------------------------
-- Position 5: inl
-- encode inl = In ∘ inr^5 ∘ inl ∘ ⟨⌜A⌝, ⌜B⌝⟩  [right-associated]
------------------------------------------------------------------------
abstract
  is-id-pos-5 : ∀ {A B} → (is-id ∘ encode (inl {A} {B})) ⟶* (inr ∘ encode (inl {A} {B}))
  is-id-pos-5 {A} {B} =
    let payload = ⟨ ⌜ A ⌝Ty , ⌜ B ⌝Ty ⟩ in
    out-in-compose is-id-dispatch (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inl ∘ payload)))))) >>
    ⟶1 assoc-l >> ⟶1 (⟶-∘-l is-id-dispatch-inr) >>
    ⟶1 assoc-l >> ⟶1 (⟶-∘-l is-id-tail-1-inr) >>
    ⟶1 assoc-l >> ⟶1 (⟶-∘-l is-id-tail-2-inr) >>
    ⟶1 assoc-l >> ⟶1 (⟶-∘-l is-id-tail-3-inr) >>
    ⟶1 assoc-l >> ⟶1 (⟶-∘-l is-id-tail-4-inr) >>
    ⟶1 assoc-l >> ⟶1 (⟶-∘-l is-id-tail-5-inl) >>
    ⟶1 assoc-r >>
    ∘-cong-right' inr (⟶1 assoc-r >> ∘-cong-right' In (⟶1 assoc-r >> ∘-cong-right' inr (⟶1 assoc-r >> ∘-cong-right' inr (⟶1 assoc-r >> ∘-cong-right' inr (⟶1 assoc-r >> ∘-cong-right' inr (⟶1 assoc-r))))))

------------------------------------------------------------------------
-- Position 6: inr
-- encode inr = In ∘ inr^6 ∘ inl ∘ ⟨⌜A⌝, ⌜B⌝⟩  [right-associated]
------------------------------------------------------------------------
abstract
  is-id-pos-6 : ∀ {A B} → (is-id ∘ encode (inr {A} {B})) ⟶* (inr ∘ encode (inr {A} {B}))
  is-id-pos-6 {A} {B} =
    let payload = ⟨ ⌜ A ⌝Ty , ⌜ B ⌝Ty ⟩ in
    out-in-compose is-id-dispatch (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inl ∘ payload))))))) >>
    ⟶1 assoc-l >> ⟶1 (⟶-∘-l is-id-dispatch-inr) >>
    ⟶1 assoc-l >> ⟶1 (⟶-∘-l is-id-tail-1-inr) >>
    ⟶1 assoc-l >> ⟶1 (⟶-∘-l is-id-tail-2-inr) >>
    ⟶1 assoc-l >> ⟶1 (⟶-∘-l is-id-tail-3-inr) >>
    ⟶1 assoc-l >> ⟶1 (⟶-∘-l is-id-tail-4-inr) >>
    ⟶1 assoc-l >> ⟶1 (⟶-∘-l is-id-tail-5-inr) >>
    ⟶1 assoc-l >> ⟶1 (⟶-∘-l is-id-tail-6-inl) >>
    ⟶1 assoc-r >>
    ∘-cong-right' inr (⟶1 assoc-r >> ∘-cong-right' In (⟶1 assoc-r >> ∘-cong-right' inr (⟶1 assoc-r >> ∘-cong-right' inr (⟶1 assoc-r >> ∘-cong-right' inr (⟶1 assoc-r >> ∘-cong-right' inr (⟶1 assoc-r >> ∘-cong-right' inr (⟶1 assoc-r)))))))

------------------------------------------------------------------------
-- Position 7: [f, g] (case)
-- encode [f, g] = In ∘ inr^7 ∘ inl ∘ ⟨encode f, encode g⟩  [right-associated]
------------------------------------------------------------------------
abstract
  is-id-pos-7 : ∀ {A B C} (f : Term A C) (g : Term B C) →
                (is-id ∘ encode [ f , g ]) ⟶* (inr ∘ encode [ f , g ])
  is-id-pos-7 f g =
    let payload = ⟨ encode f , encode g ⟩ in
    out-in-compose is-id-dispatch (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inl ∘ payload)))))))) >>
    ⟶1 assoc-l >> ⟶1 (⟶-∘-l is-id-dispatch-inr) >>
    ⟶1 assoc-l >> ⟶1 (⟶-∘-l is-id-tail-1-inr) >>
    ⟶1 assoc-l >> ⟶1 (⟶-∘-l is-id-tail-2-inr) >>
    ⟶1 assoc-l >> ⟶1 (⟶-∘-l is-id-tail-3-inr) >>
    ⟶1 assoc-l >> ⟶1 (⟶-∘-l is-id-tail-4-inr) >>
    ⟶1 assoc-l >> ⟶1 (⟶-∘-l is-id-tail-5-inr) >>
    ⟶1 assoc-l >> ⟶1 (⟶-∘-l is-id-tail-6-inr) >>
    ⟶1 assoc-l >> ⟶1 (⟶-∘-l is-id-tail-7-inl) >>
    ⟶1 assoc-r >>
    ∘-cong-right' inr (⟶1 assoc-r >> ∘-cong-right' In (⟶1 assoc-r >> ∘-cong-right' inr (⟶1 assoc-r >> ∘-cong-right' inr (⟶1 assoc-r >> ∘-cong-right' inr (⟶1 assoc-r >> ∘-cong-right' inr (⟶1 assoc-r >> ∘-cong-right' inr (⟶1 assoc-r >> ∘-cong-right' inr (⟶1 assoc-r))))))))

------------------------------------------------------------------------
-- Position 8: terminal
-- encode terminal = In ∘ inr^8 ∘ inl ∘ ⌜A⌝  [right-associated]
------------------------------------------------------------------------
abstract
  is-id-pos-8 : ∀ {A} → (is-id ∘ encode (terminal {A})) ⟶* (inr ∘ encode (terminal {A}))
  is-id-pos-8 {A} =
    let payload = ⌜ A ⌝Ty in
    out-in-compose is-id-dispatch (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inl ∘ payload))))))))) >>
    ⟶1 assoc-l >> ⟶1 (⟶-∘-l is-id-dispatch-inr) >>
    ⟶1 assoc-l >> ⟶1 (⟶-∘-l is-id-tail-1-inr) >>
    ⟶1 assoc-l >> ⟶1 (⟶-∘-l is-id-tail-2-inr) >>
    ⟶1 assoc-l >> ⟶1 (⟶-∘-l is-id-tail-3-inr) >>
    ⟶1 assoc-l >> ⟶1 (⟶-∘-l is-id-tail-4-inr) >>
    ⟶1 assoc-l >> ⟶1 (⟶-∘-l is-id-tail-5-inr) >>
    ⟶1 assoc-l >> ⟶1 (⟶-∘-l is-id-tail-6-inr) >>
    ⟶1 assoc-l >> ⟶1 (⟶-∘-l is-id-tail-7-inr) >>
    ⟶1 assoc-l >> ⟶1 (⟶-∘-l is-id-tail-8-inl) >>
    ⟶1 assoc-r >>
    ∘-cong-right' inr (⟶1 assoc-r >> ∘-cong-right' In (⟶1 assoc-r >> ∘-cong-right' inr (⟶1 assoc-r >> ∘-cong-right' inr (⟶1 assoc-r >> ∘-cong-right' inr (⟶1 assoc-r >> ∘-cong-right' inr (⟶1 assoc-r >> ∘-cong-right' inr (⟶1 assoc-r >> ∘-cong-right' inr (⟶1 assoc-r >> ∘-cong-right' inr (⟶1 assoc-r)))))))))

------------------------------------------------------------------------
-- Position 10: In
-- encode In = In ∘ inr^10 ∘ inl ∘ ⌜F⌝  [right-associated]
------------------------------------------------------------------------
abstract
  is-id-pos-10 : ∀ {F} → (is-id ∘ encode (In {F})) ⟶* (inr ∘ encode (In {F}))
  is-id-pos-10 {F} =
    let payload = ⌜ F ⌝Func in
    out-in-compose is-id-dispatch (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inl ∘ payload))))))))))) >>
    ⟶1 assoc-l >> ⟶1 (⟶-∘-l is-id-dispatch-inr) >>
    ⟶1 assoc-l >> ⟶1 (⟶-∘-l is-id-tail-1-inr) >>
    ⟶1 assoc-l >> ⟶1 (⟶-∘-l is-id-tail-2-inr) >>
    ⟶1 assoc-l >> ⟶1 (⟶-∘-l is-id-tail-3-inr) >>
    ⟶1 assoc-l >> ⟶1 (⟶-∘-l is-id-tail-4-inr) >>
    ⟶1 assoc-l >> ⟶1 (⟶-∘-l is-id-tail-5-inr) >>
    ⟶1 assoc-l >> ⟶1 (⟶-∘-l is-id-tail-6-inr) >>
    ⟶1 assoc-l >> ⟶1 (⟶-∘-l is-id-tail-7-inr) >>
    ⟶1 assoc-l >> ⟶1 (⟶-∘-l is-id-tail-8-inr) >>
    ⟶1 assoc-l >> ⟶1 (⟶-∘-l is-id-tail-9-inr) >>
    ⟶1 assoc-l >> ⟶1 (⟶-∘-l is-id-tail-10-inl) >>
    ⟶1 assoc-r >>
    ∘-cong-right' inr (⟶1 assoc-r >> ∘-cong-right' In (⟶1 assoc-r >> ∘-cong-right' inr (⟶1 assoc-r >> ∘-cong-right' inr (⟶1 assoc-r >> ∘-cong-right' inr (⟶1 assoc-r >> ∘-cong-right' inr (⟶1 assoc-r >> ∘-cong-right' inr (⟶1 assoc-r >> ∘-cong-right' inr (⟶1 assoc-r >> ∘-cong-right' inr (⟶1 assoc-r >> ∘-cong-right' inr (⟶1 assoc-r >> ∘-cong-right' inr (⟶1 assoc-r)))))))))))

------------------------------------------------------------------------
-- Position 11: Out
-- encode Out = In ∘ inr^11 ∘ inl ∘ ⌜F⌝  [right-associated]
------------------------------------------------------------------------
abstract
  is-id-pos-11 : ∀ {F} → (is-id ∘ encode (Out {F})) ⟶* (inr ∘ encode (Out {F}))
  is-id-pos-11 {F} =
    let payload = ⌜ F ⌝Func in
    out-in-compose is-id-dispatch (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inl ∘ payload)))))))))))) >>
    ⟶1 assoc-l >> ⟶1 (⟶-∘-l is-id-dispatch-inr) >>
    ⟶1 assoc-l >> ⟶1 (⟶-∘-l is-id-tail-1-inr) >>
    ⟶1 assoc-l >> ⟶1 (⟶-∘-l is-id-tail-2-inr) >>
    ⟶1 assoc-l >> ⟶1 (⟶-∘-l is-id-tail-3-inr) >>
    ⟶1 assoc-l >> ⟶1 (⟶-∘-l is-id-tail-4-inr) >>
    ⟶1 assoc-l >> ⟶1 (⟶-∘-l is-id-tail-5-inr) >>
    ⟶1 assoc-l >> ⟶1 (⟶-∘-l is-id-tail-6-inr) >>
    ⟶1 assoc-l >> ⟶1 (⟶-∘-l is-id-tail-7-inr) >>
    ⟶1 assoc-l >> ⟶1 (⟶-∘-l is-id-tail-8-inr) >>
    ⟶1 assoc-l >> ⟶1 (⟶-∘-l is-id-tail-9-inr) >>
    ⟶1 assoc-l >> ⟶1 (⟶-∘-l is-id-tail-10-inr) >>
    ⟶1 assoc-l >> ⟶1 (⟶-∘-l is-id-tail-11-inl) >>
    ⟶1 assoc-r >>
    ∘-cong-right' inr (⟶1 assoc-r >> ∘-cong-right' In (⟶1 assoc-r >> ∘-cong-right' inr (⟶1 assoc-r >> ∘-cong-right' inr (⟶1 assoc-r >> ∘-cong-right' inr (⟶1 assoc-r >> ∘-cong-right' inr (⟶1 assoc-r >> ∘-cong-right' inr (⟶1 assoc-r >> ∘-cong-right' inr (⟶1 assoc-r >> ∘-cong-right' inr (⟶1 assoc-r >> ∘-cong-right' inr (⟶1 assoc-r >> ∘-cong-right' inr (⟶1 assoc-r >> ∘-cong-right' inr (⟶1 assoc-r))))))))))))

------------------------------------------------------------------------
-- Position 12: cata F alg
-- encode (cata F alg) = In ∘ inr^12 ∘ inl ∘ ⟨⌜F⌝, encode alg⟩  [right-associated]
------------------------------------------------------------------------
abstract
  is-id-pos-12 : ∀ {F A} (alg : Term (⟦ F ⟧F A) A) →
                 (is-id ∘ encode (cata F alg)) ⟶* (inr ∘ encode (cata F alg))
  is-id-pos-12 {F} alg =
    let payload = ⟨ ⌜ F ⌝Func , encode alg ⟩ in
    out-in-compose is-id-dispatch (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inl ∘ payload))))))))))))) >>
    ⟶1 assoc-l >> ⟶1 (⟶-∘-l is-id-dispatch-inr) >>
    ⟶1 assoc-l >> ⟶1 (⟶-∘-l is-id-tail-1-inr) >>
    ⟶1 assoc-l >> ⟶1 (⟶-∘-l is-id-tail-2-inr) >>
    ⟶1 assoc-l >> ⟶1 (⟶-∘-l is-id-tail-3-inr) >>
    ⟶1 assoc-l >> ⟶1 (⟶-∘-l is-id-tail-4-inr) >>
    ⟶1 assoc-l >> ⟶1 (⟶-∘-l is-id-tail-5-inr) >>
    ⟶1 assoc-l >> ⟶1 (⟶-∘-l is-id-tail-6-inr) >>
    ⟶1 assoc-l >> ⟶1 (⟶-∘-l is-id-tail-7-inr) >>
    ⟶1 assoc-l >> ⟶1 (⟶-∘-l is-id-tail-8-inr) >>
    ⟶1 assoc-l >> ⟶1 (⟶-∘-l is-id-tail-9-inr) >>
    ⟶1 assoc-l >> ⟶1 (⟶-∘-l is-id-tail-10-inr) >>
    ⟶1 assoc-l >> ⟶1 (⟶-∘-l is-id-tail-11-inr) >>
    ⟶1 assoc-l >> ⟶1 (⟶-∘-l is-id-tail-12-inl) >>
    ⟶1 assoc-r >>
    ∘-cong-right' inr (⟶1 assoc-r >> ∘-cong-right' In (⟶1 assoc-r >> ∘-cong-right' inr (⟶1 assoc-r >> ∘-cong-right' inr (⟶1 assoc-r >> ∘-cong-right' inr (⟶1 assoc-r >> ∘-cong-right' inr (⟶1 assoc-r >> ∘-cong-right' inr (⟶1 assoc-r >> ∘-cong-right' inr (⟶1 assoc-r >> ∘-cong-right' inr (⟶1 assoc-r >> ∘-cong-right' inr (⟶1 assoc-r >> ∘-cong-right' inr (⟶1 assoc-r >> ∘-cong-right' inr (⟶1 assoc-r >> ∘-cong-right' inr (⟶1 assoc-r)))))))))))))

------------------------------------------------------------------------
-- Position 13: curry f
-- encode (curry f) = In ∘ inr^13 ∘ inl ∘ ⟨⟨⌜A⌝, ⌜B⌝⟩, ⟨⌜C⌝, encode f⟩⟩  [right-associated]
------------------------------------------------------------------------
abstract
  is-id-pos-13 : ∀ {A B C} (f : Term (A * B) C) →
                 (is-id ∘ encode (curry f)) ⟶* (inr ∘ encode (curry f))
  is-id-pos-13 {A} {B} {C} f =
    let payload = ⟨ ⟨ ⌜ A ⌝Ty , ⌜ B ⌝Ty ⟩ , ⟨ ⌜ C ⌝Ty , encode f ⟩ ⟩ in
    out-in-compose is-id-dispatch (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inl ∘ payload)))))))))))))) >>
    ⟶1 assoc-l >> ⟶1 (⟶-∘-l is-id-dispatch-inr) >>
    ⟶1 assoc-l >> ⟶1 (⟶-∘-l is-id-tail-1-inr) >>
    ⟶1 assoc-l >> ⟶1 (⟶-∘-l is-id-tail-2-inr) >>
    ⟶1 assoc-l >> ⟶1 (⟶-∘-l is-id-tail-3-inr) >>
    ⟶1 assoc-l >> ⟶1 (⟶-∘-l is-id-tail-4-inr) >>
    ⟶1 assoc-l >> ⟶1 (⟶-∘-l is-id-tail-5-inr) >>
    ⟶1 assoc-l >> ⟶1 (⟶-∘-l is-id-tail-6-inr) >>
    ⟶1 assoc-l >> ⟶1 (⟶-∘-l is-id-tail-7-inr) >>
    ⟶1 assoc-l >> ⟶1 (⟶-∘-l is-id-tail-8-inr) >>
    ⟶1 assoc-l >> ⟶1 (⟶-∘-l is-id-tail-9-inr) >>
    ⟶1 assoc-l >> ⟶1 (⟶-∘-l is-id-tail-10-inr) >>
    ⟶1 assoc-l >> ⟶1 (⟶-∘-l is-id-tail-11-inr) >>
    ⟶1 assoc-l >> ⟶1 (⟶-∘-l is-id-tail-12-inr) >>
    ⟶1 assoc-l >> ⟶1 (⟶-∘-l is-id-tail-13-inl) >>
    ⟶1 assoc-r >>
    ∘-cong-right' inr (⟶1 assoc-r >> ∘-cong-right' In (⟶1 assoc-r >> ∘-cong-right' inr (⟶1 assoc-r >> ∘-cong-right' inr (⟶1 assoc-r >> ∘-cong-right' inr (⟶1 assoc-r >> ∘-cong-right' inr (⟶1 assoc-r >> ∘-cong-right' inr (⟶1 assoc-r >> ∘-cong-right' inr (⟶1 assoc-r >> ∘-cong-right' inr (⟶1 assoc-r >> ∘-cong-right' inr (⟶1 assoc-r >> ∘-cong-right' inr (⟶1 assoc-r >> ∘-cong-right' inr (⟶1 assoc-r >> ∘-cong-right' inr (⟶1 assoc-r >> ∘-cong-right' inr (⟶1 assoc-r))))))))))))))

------------------------------------------------------------------------
-- Position 14: apply (last position, no inl)
-- encode apply = In ∘ inr^14 ∘ ⟨⌜A⌝, ⌜B⌝⟩  [right-associated]
-- Note: Position 14 has no trailing inl since it's the last alternative
------------------------------------------------------------------------
abstract
  is-id-pos-14 : ∀ {A B} → (is-id ∘ encode (apply {A} {B})) ⟶* (inr ∘ encode (apply {A} {B}))
  is-id-pos-14 {A} {B} =
    let payload = ⟨ ⌜ A ⌝Ty , ⌜ B ⌝Ty ⟩ in
    out-in-compose is-id-dispatch (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ payload)))))))))))))) >>
    ⟶1 assoc-l >> ⟶1 (⟶-∘-l is-id-dispatch-inr) >>
    ⟶1 assoc-l >> ⟶1 (⟶-∘-l is-id-tail-1-inr) >>
    ⟶1 assoc-l >> ⟶1 (⟶-∘-l is-id-tail-2-inr) >>
    ⟶1 assoc-l >> ⟶1 (⟶-∘-l is-id-tail-3-inr) >>
    ⟶1 assoc-l >> ⟶1 (⟶-∘-l is-id-tail-4-inr) >>
    ⟶1 assoc-l >> ⟶1 (⟶-∘-l is-id-tail-5-inr) >>
    ⟶1 assoc-l >> ⟶1 (⟶-∘-l is-id-tail-6-inr) >>
    ⟶1 assoc-l >> ⟶1 (⟶-∘-l is-id-tail-7-inr) >>
    ⟶1 assoc-l >> ⟶1 (⟶-∘-l is-id-tail-8-inr) >>
    ⟶1 assoc-l >> ⟶1 (⟶-∘-l is-id-tail-9-inr) >>
    ⟶1 assoc-l >> ⟶1 (⟶-∘-l is-id-tail-10-inr) >>
    ⟶1 assoc-l >> ⟶1 (⟶-∘-l is-id-tail-11-inr) >>
    ⟶1 assoc-l >> ⟶1 (⟶-∘-l is-id-tail-12-inr) >>
    ⟶1 assoc-l >> ⟶1 (⟶-∘-l is-id-tail-13-inr) >>
    -- is-id-tail-13 ∘ inr ⟶ ret-no-14 = inr ∘ (In ∘ inr^14)
    ⟶1 assoc-r >>
    ∘-cong-right' inr (⟶1 assoc-r >> ∘-cong-right' In (⟶1 assoc-r >> ∘-cong-right' inr (⟶1 assoc-r >> ∘-cong-right' inr (⟶1 assoc-r >> ∘-cong-right' inr (⟶1 assoc-r >> ∘-cong-right' inr (⟶1 assoc-r >> ∘-cong-right' inr (⟶1 assoc-r >> ∘-cong-right' inr (⟶1 assoc-r >> ∘-cong-right' inr (⟶1 assoc-r >> ∘-cong-right' inr (⟶1 assoc-r >> ∘-cong-right' inr (⟶1 assoc-r >> ∘-cong-right' inr (⟶1 assoc-r >> ∘-cong-right' inr (⟶1 assoc-r >> ∘-cong-right' inr (⟶1 assoc-r))))))))))))))

------------------------------------------------------------------------
-- Main theorem: is-id-noredex by case analysis on NotIdStruct
------------------------------------------------------------------------

is-id-noredex : ∀ {A B} (t : Term A B) → NotIdStruct t →
                (is-id ∘ encode t) ⟶* (inr ∘ encode t)
is-id-noredex (f ∘ g) nis-comp = is-id-pos-1 f g
is-id-noredex fst nis-fst = is-id-pos-2
is-id-noredex snd nis-snd = is-id-pos-3
is-id-noredex ⟨ f , g ⟩ nis-pair = is-id-pos-4 f g
is-id-noredex inl nis-inl = is-id-pos-5
is-id-noredex inr nis-inr = is-id-pos-6
is-id-noredex [ f , g ] nis-case = is-id-pos-7 f g
is-id-noredex terminal nis-terminal = is-id-pos-8
is-id-noredex In nis-In = is-id-pos-10
is-id-noredex Out nis-Out = is-id-pos-11
is-id-noredex (cata F alg) nis-cata = is-id-pos-12 alg
is-id-noredex (curry f) nis-curry = is-id-pos-13 f
is-id-noredex apply nis-apply = is-id-pos-14

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
