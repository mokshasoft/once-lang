------------------------------------------------------------------------
-- Normalize.Dispatch: Tag dispatchers for pattern matching
--
-- Each is-X function inspects an encoded term to determine if it has
-- a specific top-level constructor. Used to detect redex patterns.
--
-- Pattern:
--   is-X = dispatch-X ∘ Out
--
-- where dispatch-X is a 15-way nested case returning:
--   - inl (yes/match) at position X
--   - inr ∘ rebuild-N (no/rebuild) at other positions
--
-- Positions (15 constructors):
--   0: id, 1: compose, 2: fst, 3: snd, 4: pair, 5: inl, 6: inr,
--   7: case, 8: terminal, 9: initial, 10: In, 11: Out, 12: cata,
--   13: curry, 14: apply
------------------------------------------------------------------------

module normalizer.Implementation.Normalize.Dispatch where

open import normalizer.Implementation.Normalize.Rebuild public

------------------------------------------------------------------------
-- is-id: Position 0 returns yes
------------------------------------------------------------------------

is-id-dispatch : Term (⟦ TermF ⟧F TermCode') (Unit + TermCode')
is-id-dispatch =
  [ ret-yes
  , [ ret-no-1
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
  ]

is-id : Term TermCode' (Unit + TermCode')
is-id = is-id-dispatch ∘ Out

------------------------------------------------------------------------
-- is-fst: Position 2 returns yes
------------------------------------------------------------------------

is-fst-dispatch : Term (⟦ TermF ⟧F TermCode') (Unit + TermCode')
is-fst-dispatch =
  [ ret-no-0
  , [ ret-no-1
    , [ ret-yes
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
  ]

is-fst : Term TermCode' (Unit + TermCode')
is-fst = is-fst-dispatch ∘ Out

------------------------------------------------------------------------
-- is-snd: Position 3 returns yes
------------------------------------------------------------------------

is-snd-dispatch : Term (⟦ TermF ⟧F TermCode') (Unit + TermCode')
is-snd-dispatch =
  [ ret-no-0
  , [ ret-no-1
    , [ ret-no-2
      , [ ret-yes
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
  ]

is-snd : Term TermCode' (Unit + TermCode')
is-snd = is-snd-dispatch ∘ Out

------------------------------------------------------------------------
-- is-pair: Position 4 returns inl (with pair data), others return inr
-- Return type: (TermCode' * TermCode') + TermCode'
------------------------------------------------------------------------

is-pair-dispatch : Term (⟦ TermF ⟧F TermCode') ((TermCode' * TermCode') + TermCode')
is-pair-dispatch =
  [ ret-no-pair-0
  , [ ret-no-pair-1
    , [ ret-no-pair-2
      , [ ret-no-pair-3
        , [ inl  -- 4: pair → yes, return the pair data
          , [ ret-no-pair-5
            , [ ret-no-pair-6
              , [ ret-no-pair-7
                , [ ret-no-pair-8
                  , [ ret-no-pair-9
                    , [ ret-no-pair-10
                      , [ ret-no-pair-11
                        , [ ret-no-pair-12
                          , [ ret-no-pair-13
                            , ret-no-pair-14
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
  ]

is-pair : Term TermCode' ((TermCode' * TermCode') + TermCode')
is-pair = is-pair-dispatch ∘ Out

------------------------------------------------------------------------
-- is-inl: Position 5 returns yes
------------------------------------------------------------------------

is-inl-dispatch : Term (⟦ TermF ⟧F TermCode') (Unit + TermCode')
is-inl-dispatch =
  [ ret-no-0
  , [ ret-no-1
    , [ ret-no-2
      , [ ret-no-3
        , [ ret-no-4
          , [ ret-yes  -- 5: inl → yes
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
  ]

is-inl : Term TermCode' (Unit + TermCode')
is-inl = is-inl-dispatch ∘ Out

------------------------------------------------------------------------
-- is-inr: Position 6 returns yes
------------------------------------------------------------------------

is-inr-dispatch : Term (⟦ TermF ⟧F TermCode') (Unit + TermCode')
is-inr-dispatch =
  [ ret-no-0
  , [ ret-no-1
    , [ ret-no-2
      , [ ret-no-3
        , [ ret-no-4
          , [ ret-no-5
            , [ ret-yes  -- 6: inr → yes
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
  ]

is-inr : Term TermCode' (Unit + TermCode')
is-inr = is-inr-dispatch ∘ Out

------------------------------------------------------------------------
-- is-case: Position 7 returns inl (with case branches), others return inr
-- Return type: (TermCode' * TermCode') + TermCode'
------------------------------------------------------------------------

is-case-dispatch : Term (⟦ TermF ⟧F TermCode') ((TermCode' * TermCode') + TermCode')
is-case-dispatch =
  [ ret-no-pair-0
  , [ ret-no-pair-1
    , [ ret-no-pair-2
      , [ ret-no-pair-3
        , [ ret-no-pair-4
          , [ ret-no-pair-5
            , [ ret-no-pair-6
              , [ inl  -- 7: case → yes, return the branches
                , [ ret-no-pair-8
                  , [ ret-no-pair-9
                    , [ ret-no-pair-10
                      , [ ret-no-pair-11
                        , [ ret-no-pair-12
                          , [ ret-no-pair-13
                            , ret-no-pair-14
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
  ]

is-case : Term TermCode' ((TermCode' * TermCode') + TermCode')
is-case = is-case-dispatch ∘ Out

------------------------------------------------------------------------
-- is-In: Position 10 returns yes
------------------------------------------------------------------------

is-In-dispatch : Term (⟦ TermF ⟧F TermCode') (Unit + TermCode')
is-In-dispatch =
  [ ret-no-0
  , [ ret-no-1
    , [ ret-no-2
      , [ ret-no-3
        , [ ret-no-4
          , [ ret-no-5
            , [ ret-no-6
              , [ ret-no-7
                , [ ret-no-8
                  , [ ret-no-9
                    , [ ret-yes  -- 10: In → yes
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
  ]

is-In : Term TermCode' (Unit + TermCode')
is-In = is-In-dispatch ∘ Out

------------------------------------------------------------------------
-- is-Out: Position 11 returns yes
------------------------------------------------------------------------

is-Out-dispatch : Term (⟦ TermF ⟧F TermCode') (Unit + TermCode')
is-Out-dispatch =
  [ ret-no-0
  , [ ret-no-1
    , [ ret-no-2
      , [ ret-no-3
        , [ ret-no-4
          , [ ret-no-5
            , [ ret-no-6
              , [ ret-no-7
                , [ ret-no-8
                  , [ ret-no-9
                    , [ ret-no-10
                      , [ ret-yes  -- 11: Out → yes
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
  ]

is-Out : Term TermCode' (Unit + TermCode')
is-Out = is-Out-dispatch ∘ Out

------------------------------------------------------------------------
-- is-cata: Position 12 returns inl (with functor and algebra), others return inr
-- Return type: (TyFuncCode * TermCode') + TermCode'
------------------------------------------------------------------------

is-cata-dispatch : Term (⟦ TermF ⟧F TermCode') ((TyFuncCode * TermCode') + TermCode')
is-cata-dispatch =
  [ ret-no-cata-0
  , [ ret-no-cata-1
    , [ ret-no-cata-2
      , [ ret-no-cata-3
        , [ ret-no-cata-4
          , [ ret-no-cata-5
            , [ ret-no-cata-6
              , [ ret-no-cata-7
                , [ ret-no-cata-8
                  , [ ret-no-cata-9
                    , [ ret-no-cata-10
                      , [ ret-no-cata-11
                        , [ inl  -- 12: cata → yes, return functor and algebra
                          , [ ret-no-cata-13
                            , ret-no-cata-14
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
  ]

is-cata : Term TermCode' ((TyFuncCode * TermCode') + TermCode')
is-cata = is-cata-dispatch ∘ Out
