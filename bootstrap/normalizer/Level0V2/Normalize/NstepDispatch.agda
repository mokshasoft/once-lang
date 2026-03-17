------------------------------------------------------------------------
-- Normalize.NstepDispatch: Case dispatch infrastructure
--
-- Contains:
-- - nstep-tail-N: tails of the nested case structure
-- - tail-N-inr: dispatch lemmas for inr (skip to next position)
-- - tail-N-inl: dispatch lemmas for inl (select handler at position)
-- - nr-normalize-step: NoRedex proof for normalize-step
------------------------------------------------------------------------

module normalizer.Level0V2.Normalize.NstepDispatch where

open import normalizer.Level0V2.Normalize.NoRedexHandlers public
open import normalizer.Level0V2.Normalizer
  using (TermF-1; TermF-2; TermF-3; TermF-4; TermF-5; TermF-6;
         TermF-7; TermF-8; TermF-9; TermF-10; TermF-11; TermF-12; TermF-13) public

------------------------------------------------------------------------
-- Tails of normalize-step (nested cases without outer handlers)
------------------------------------------------------------------------

nstep-tail-1 : Term (⟦ TermF-1 ⟧F TermCode') TermCode'
nstep-tail-1 =
    [ handle-comp
    , [ handle-fst
      , [ handle-snd
        , [ handle-pair
          , [ handle-inl
            , [ handle-inr
              , [ handle-case
                , [ handle-terminal
                  , [ handle-initial
                    , [ handle-In
                      , [ handle-Out
                        , [ handle-cata
                          , [ handle-curry
                            , handle-apply
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

nstep-tail-2 : Term (⟦ TermF-2 ⟧F TermCode') TermCode'
nstep-tail-2 =
    [ handle-fst
    , [ handle-snd
      , [ handle-pair
        , [ handle-inl
          , [ handle-inr
            , [ handle-case
              , [ handle-terminal
                , [ handle-initial
                  , [ handle-In
                    , [ handle-Out
                      , [ handle-cata
                        , [ handle-curry
                          , handle-apply
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

nstep-tail-3 : Term (⟦ TermF-3 ⟧F TermCode') TermCode'
nstep-tail-3 =
    [ handle-snd
    , [ handle-pair
      , [ handle-inl
        , [ handle-inr
          , [ handle-case
            , [ handle-terminal
              , [ handle-initial
                , [ handle-In
                  , [ handle-Out
                    , [ handle-cata
                      , [ handle-curry
                        , handle-apply
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

nstep-tail-4 : Term (⟦ TermF-4 ⟧F TermCode') TermCode'
nstep-tail-4 =
    [ handle-pair
    , [ handle-inl
      , [ handle-inr
        , [ handle-case
          , [ handle-terminal
            , [ handle-initial
              , [ handle-In
                , [ handle-Out
                  , [ handle-cata
                    , [ handle-curry
                      , handle-apply
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

nstep-tail-5 : Term (⟦ TermF-5 ⟧F TermCode') TermCode'
nstep-tail-5 =
    [ handle-inl
    , [ handle-inr
      , [ handle-case
        , [ handle-terminal
          , [ handle-initial
            , [ handle-In
              , [ handle-Out
                , [ handle-cata
                  , [ handle-curry
                    , handle-apply
                    ]
                  ]
                ]
              ]
            ]
          ]
        ]
      ]
    ]

nstep-tail-6 : Term (⟦ TermF-6 ⟧F TermCode') TermCode'
nstep-tail-6 =
    [ handle-inr
    , [ handle-case
      , [ handle-terminal
        , [ handle-initial
          , [ handle-In
            , [ handle-Out
              , [ handle-cata
                , [ handle-curry
                  , handle-apply
                  ]
                ]
              ]
            ]
          ]
        ]
      ]
    ]

nstep-tail-7 : Term (⟦ TermF-7 ⟧F TermCode') TermCode'
nstep-tail-7 =
    [ handle-case
    , [ handle-terminal
      , [ handle-initial
        , [ handle-In
          , [ handle-Out
            , [ handle-cata
              , [ handle-curry
                , handle-apply
                ]
              ]
            ]
          ]
        ]
      ]
    ]

nstep-tail-8 : Term (⟦ TermF-8 ⟧F TermCode') TermCode'
nstep-tail-8 =
    [ handle-terminal
    , [ handle-initial
      , [ handle-In
        , [ handle-Out
          , [ handle-cata
            , [ handle-curry
              , handle-apply
              ]
            ]
          ]
        ]
      ]
    ]

nstep-tail-9 : Term (⟦ TermF-9 ⟧F TermCode') TermCode'
nstep-tail-9 =
    [ handle-initial
    , [ handle-In
      , [ handle-Out
        , [ handle-cata
          , [ handle-curry
            , handle-apply
            ]
          ]
        ]
      ]
    ]

nstep-tail-10 : Term (⟦ TermF-10 ⟧F TermCode') TermCode'
nstep-tail-10 =
    [ handle-In
    , [ handle-Out
      , [ handle-cata
        , [ handle-curry
          , handle-apply
          ]
        ]
      ]
    ]

nstep-tail-11 : Term (⟦ TermF-11 ⟧F TermCode') TermCode'
nstep-tail-11 =
    [ handle-Out
    , [ handle-cata
      , [ handle-curry
        , handle-apply
        ]
      ]
    ]

nstep-tail-12 : Term (⟦ TermF-12 ⟧F TermCode') TermCode'
nstep-tail-12 =
    [ handle-cata
    , [ handle-curry
      , handle-apply
      ]
    ]

nstep-tail-13 : Term (⟦ TermF-13 ⟧F TermCode') TermCode'
nstep-tail-13 =
    [ handle-curry
    , handle-apply
    ]

------------------------------------------------------------------------
-- Dispatch lemmas: normalize-step ∘ inr ⟶ nstep-tail-1, etc.
------------------------------------------------------------------------

nstep-inr : (normalize-step ∘ inr) ⟶ nstep-tail-1
nstep-inr = case-inr

------------------------------------------------------------------------
-- Tail dispatch lemmas (inr skips to next position)
------------------------------------------------------------------------

tail-1-inr : (nstep-tail-1 ∘ inr) ⟶ nstep-tail-2
tail-1-inr = case-inr

tail-2-inr : (nstep-tail-2 ∘ inr) ⟶ nstep-tail-3
tail-2-inr = case-inr

tail-3-inr : (nstep-tail-3 ∘ inr) ⟶ nstep-tail-4
tail-3-inr = case-inr

tail-4-inr : (nstep-tail-4 ∘ inr) ⟶ nstep-tail-5
tail-4-inr = case-inr

tail-5-inr : (nstep-tail-5 ∘ inr) ⟶ nstep-tail-6
tail-5-inr = case-inr

tail-6-inr : (nstep-tail-6 ∘ inr) ⟶ nstep-tail-7
tail-6-inr = case-inr

tail-7-inr : (nstep-tail-7 ∘ inr) ⟶ nstep-tail-8
tail-7-inr = case-inr

tail-8-inr : (nstep-tail-8 ∘ inr) ⟶ nstep-tail-9
tail-8-inr = case-inr

tail-9-inr : (nstep-tail-9 ∘ inr) ⟶ nstep-tail-10
tail-9-inr = case-inr

tail-10-inr : (nstep-tail-10 ∘ inr) ⟶ nstep-tail-11
tail-10-inr = case-inr

tail-11-inr : (nstep-tail-11 ∘ inr) ⟶ nstep-tail-12
tail-11-inr = case-inr

tail-12-inr : (nstep-tail-12 ∘ inr) ⟶ nstep-tail-13
tail-12-inr = case-inr

------------------------------------------------------------------------
-- Dispatch lemmas for inl at each position
------------------------------------------------------------------------

tail-1-inl : (nstep-tail-1 ∘ inl) ⟶ handle-comp
tail-1-inl = case-inl

tail-2-inl : (nstep-tail-2 ∘ inl) ⟶ handle-fst
tail-2-inl = case-inl

tail-3-inl : (nstep-tail-3 ∘ inl) ⟶ handle-snd
tail-3-inl = case-inl

tail-4-inl : (nstep-tail-4 ∘ inl) ⟶ handle-pair
tail-4-inl = case-inl

tail-5-inl : (nstep-tail-5 ∘ inl) ⟶ handle-inl
tail-5-inl = case-inl

tail-6-inl : (nstep-tail-6 ∘ inl) ⟶ handle-inr
tail-6-inl = case-inl

tail-7-inl : (nstep-tail-7 ∘ inl) ⟶ handle-case
tail-7-inl = case-inl

tail-8-inl : (nstep-tail-8 ∘ inl) ⟶ handle-terminal
tail-8-inl = case-inl

tail-9-inl : (nstep-tail-9 ∘ inl) ⟶ handle-initial
tail-9-inl = case-inl

tail-10-inl : (nstep-tail-10 ∘ inl) ⟶ handle-In
tail-10-inl = case-inl

tail-11-inl : (nstep-tail-11 ∘ inl) ⟶ handle-Out
tail-11-inl = case-inl

tail-12-inl : (nstep-tail-12 ∘ inl) ⟶ handle-cata
tail-12-inl = case-inl

tail-13-inl : (nstep-tail-13 ∘ inl) ⟶ handle-curry
tail-13-inl = case-inl

tail-13-inr : (nstep-tail-13 ∘ inr) ⟶ handle-apply
tail-13-inr = case-inr

------------------------------------------------------------------------
-- The complete NoRedex proof for normalize-step
------------------------------------------------------------------------

nr-normalize-step : NoRedex normalize-step
nr-normalize-step =
  nr-case nr-handle-id
    (nr-case nr-handle-comp
      (nr-case nr-handle-fst
        (nr-case nr-handle-snd
          (nr-case nr-handle-pair
            (nr-case nr-handle-inl
              (nr-case nr-handle-inr
                (nr-case nr-handle-case
                  (nr-case nr-handle-terminal
                    (nr-case nr-handle-initial
                      (nr-case nr-handle-In
                        (nr-case nr-handle-Out
                          (nr-case nr-handle-cata
                            (nr-case nr-handle-curry nr-handle-apply)))))))))))))
