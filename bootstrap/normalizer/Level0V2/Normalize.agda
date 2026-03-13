------------------------------------------------------------------------
-- Normalize: The Actual Normalizer
--
-- This module defines a normalizer that applies CCC reduction rules
-- to encoded terms. Unlike `cata TermF In` (which is just identity),
-- this actually reduces redexes.
--
-- Structure:
--   normalize = cata TermF normalize-step
--   normalize-step checks for redexes and applies reductions
------------------------------------------------------------------------

module normalizer.Level0V2.Normalize where

open import normalizer.Foundations.Types
open import normalizer.Foundations.MinimalCCC
open import normalizer.Foundations.Encoding

------------------------------------------------------------------------
-- Strategy
--
-- The normalizer is: normalize = cata TermF normalize-step
--
-- When processing a term, cata gives us the subterms already normalized.
-- normalize-step must:
--   1. Check if the current node + normalized subterms form a redex
--   2. If yes, apply the reduction
--   3. If no, rebuild with In
--
-- For composition (f ∘ g), we need to inspect f and g to detect:
--   - id ∘ g → g
--   - f ∘ id → f
--   - fst ∘ ⟨f,g⟩ → f
--   - snd ∘ ⟨f,g⟩ → g
--   - [f,g] ∘ inl → f
--   - [f,g] ∘ inr → g
--   - Out ∘ In → id
--   - cata F alg ∘ In → alg ∘ fmap F (cata F alg)
--
-- For pairs ⟨f,g⟩, check for eta: ⟨fst,snd⟩ → id
-- For case [f,g], check for eta: [inl,inr] → id
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Helper: Inspect the head constructor of an encoded term
------------------------------------------------------------------------

-- The unfolded structure of TermF
-- Position 0: id, 1: comp, 2: fst, 3: snd, 4: pair,
-- 5: inl, 6: inr, 7: case, 8: terminal, 9: In, 10: Out, 11: cata

-- We need to pattern match on the structure to detect redexes.
-- This is done using Out to unfold, then case analysis.

-- Tag type for term constructors
data TermTag : Set where
  tag-id tag-comp tag-fst tag-snd tag-pair : TermTag
  tag-inl tag-inr tag-case tag-terminal : TermTag
  tag-In tag-Out tag-cata : TermTag

------------------------------------------------------------------------
-- The Normalizer Step Function
--
-- This is the algebra for cata that applies reductions.
-- Input: unfolded term with subterms already normalized
-- Output: normalized result
------------------------------------------------------------------------

-- The normalizer step function is defined below, after the helper infrastructure.
-- Properties of normalize-step:
-- 1. For non-redex: normalize-step ∘ inj-X = In ∘ inj-X (rebuild)
-- 2. For redex: applies the reduction rule
--
-- normalize-step is defined at the end of this file, after all helpers.
-- normalize = cata TermF normalize-step (also at end)

------------------------------------------------------------------------
-- Reduction Detection Helpers
--
-- To build normalize-step, we need helpers that detect redex patterns.
-- These check if two encoded terms form a redex when composed.
------------------------------------------------------------------------

-- Check if a term is `id` (position 0 in TermF)
-- Returns inl tt if it's id, inr self otherwise
--
-- Implementation: Out to unfold, then 12-way case analysis
-- Position 0 → inl ∘ terminal (it's id!)
-- Positions 1-11 → inr ∘ In ∘ (rebuild at that position)

------------------------------------------------------------------------
-- Rebuild helpers: reconstruct a TermCode' from position data
--
-- rebuild-N takes data at position N and produces TermCode' via In ∘ inj-N
------------------------------------------------------------------------

rebuild-0 : Term TyFuncCode TermCode'
rebuild-0 = In ∘ inl  -- position 0: id

rebuild-1 : Term (TermCode' * TermCode') TermCode'
rebuild-1 = In ∘ inr ∘ inl  -- position 1: comp

rebuild-2 : Term (TyFuncCode * TyFuncCode) TermCode'
rebuild-2 = In ∘ inr ∘ inr ∘ inl  -- position 2: fst

rebuild-3 : Term (TyFuncCode * TyFuncCode) TermCode'
rebuild-3 = In ∘ inr ∘ inr ∘ inr ∘ inl  -- position 3: snd

rebuild-4 : Term (TermCode' * TermCode') TermCode'
rebuild-4 = In ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl  -- position 4: pair

rebuild-5 : Term (TyFuncCode * TyFuncCode) TermCode'
rebuild-5 = In ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl  -- position 5: inl

rebuild-6 : Term (TyFuncCode * TyFuncCode) TermCode'
rebuild-6 = In ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl  -- position 6: inr

rebuild-7 : Term (TermCode' * TermCode') TermCode'
rebuild-7 = In ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl  -- position 7: case

rebuild-8 : Term TyFuncCode TermCode'
rebuild-8 = In ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl  -- position 8: terminal

rebuild-9 : Term TyFuncCode TermCode'
rebuild-9 = In ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl  -- position 9: In

rebuild-10 : Term TyFuncCode TermCode'
rebuild-10 = In ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl  -- position 10: Out

rebuild-11 : Term (TyFuncCode * TermCode') TermCode'
rebuild-11 = In ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl  -- position 11: cata

rebuild-12 : Term ((TyFuncCode * TyFuncCode) * (TyFuncCode * TermCode')) TermCode'
rebuild-12 = In ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl  -- position 12: curry

rebuild-13 : Term (TyFuncCode * TyFuncCode) TermCode'
rebuild-13 = In ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr  -- position 13: apply

------------------------------------------------------------------------
-- "Return yes" helper: signals match with inl ∘ terminal
------------------------------------------------------------------------

ret-yes : ∀ {A} → Term A (Unit + TermCode')
ret-yes = inl ∘ terminal

------------------------------------------------------------------------
-- "Return no" helpers: rebuild and return inr
--
-- These use the rebuild-N helpers composed with inr
------------------------------------------------------------------------

ret-no-0 : Term TyFuncCode (Unit + TermCode')
ret-no-0 = inr ∘ rebuild-0

ret-no-1 : Term (TermCode' * TermCode') (Unit + TermCode')
ret-no-1 = inr ∘ rebuild-1

ret-no-2 : Term (TyFuncCode * TyFuncCode) (Unit + TermCode')
ret-no-2 = inr ∘ rebuild-2

ret-no-3 : Term (TyFuncCode * TyFuncCode) (Unit + TermCode')
ret-no-3 = inr ∘ rebuild-3

ret-no-4 : Term (TermCode' * TermCode') (Unit + TermCode')
ret-no-4 = inr ∘ rebuild-4

ret-no-5 : Term (TyFuncCode * TyFuncCode) (Unit + TermCode')
ret-no-5 = inr ∘ rebuild-5

ret-no-6 : Term (TyFuncCode * TyFuncCode) (Unit + TermCode')
ret-no-6 = inr ∘ rebuild-6

ret-no-7 : Term (TermCode' * TermCode') (Unit + TermCode')
ret-no-7 = inr ∘ rebuild-7

ret-no-8 : Term TyFuncCode (Unit + TermCode')
ret-no-8 = inr ∘ rebuild-8

ret-no-9 : Term TyFuncCode (Unit + TermCode')
ret-no-9 = inr ∘ rebuild-9

ret-no-10 : Term TyFuncCode (Unit + TermCode')
ret-no-10 = inr ∘ rebuild-10

ret-no-11 : Term (TyFuncCode * TermCode') (Unit + TermCode')
ret-no-11 = inr ∘ rebuild-11

ret-no-12 : Term ((TyFuncCode * TyFuncCode) * (TyFuncCode * TermCode')) (Unit + TermCode')
ret-no-12 = inr ∘ rebuild-12

ret-no-13 : Term (TyFuncCode * TyFuncCode) (Unit + TermCode')
ret-no-13 = inr ∘ rebuild-13

------------------------------------------------------------------------
-- Dispatcher Pattern
--
-- Each is-X function:
--   is-X = dispatch-X ∘ Out
--
-- where dispatch-X is a 14-way nested case:
--   [ h0, [ h1, [ h2, ... [ h12, h13 ]...]]]
--
-- Position X returns "yes" (inl), other positions return "no" (inr ∘ rebuild)
------------------------------------------------------------------------

-- is-id: Position 0 returns yes
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
                          , ret-no-13
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

-- is-fst: Position 2 returns yes
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
                          , ret-no-13
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

-- is-snd: Position 3 returns yes
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
                          , ret-no-13
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

-- is-pair: Position 4 returns inl (with pair data), others return inr
-- Return type: (TermCode' * TermCode') + TermCode'
ret-no-pair-0 : Term TyFuncCode ((TermCode' * TermCode') + TermCode')
ret-no-pair-0 = inr ∘ rebuild-0

ret-no-pair-1 : Term (TermCode' * TermCode') ((TermCode' * TermCode') + TermCode')
ret-no-pair-1 = inr ∘ rebuild-1

ret-no-pair-2 : Term (TyFuncCode * TyFuncCode) ((TermCode' * TermCode') + TermCode')
ret-no-pair-2 = inr ∘ rebuild-2

ret-no-pair-3 : Term (TyFuncCode * TyFuncCode) ((TermCode' * TermCode') + TermCode')
ret-no-pair-3 = inr ∘ rebuild-3

-- Note: ret-no-pair-4 is needed for is-case-dispatch (position 4 is "no" when checking for case)
ret-no-pair-4 : Term (TermCode' * TermCode') ((TermCode' * TermCode') + TermCode')
ret-no-pair-4 = inr ∘ rebuild-4

ret-no-pair-5 : Term (TyFuncCode * TyFuncCode) ((TermCode' * TermCode') + TermCode')
ret-no-pair-5 = inr ∘ rebuild-5

ret-no-pair-6 : Term (TyFuncCode * TyFuncCode) ((TermCode' * TermCode') + TermCode')
ret-no-pair-6 = inr ∘ rebuild-6

ret-no-pair-7 : Term (TermCode' * TermCode') ((TermCode' * TermCode') + TermCode')
ret-no-pair-7 = inr ∘ rebuild-7

ret-no-pair-8 : Term TyFuncCode ((TermCode' * TermCode') + TermCode')
ret-no-pair-8 = inr ∘ rebuild-8

ret-no-pair-9 : Term TyFuncCode ((TermCode' * TermCode') + TermCode')
ret-no-pair-9 = inr ∘ rebuild-9

ret-no-pair-10 : Term TyFuncCode ((TermCode' * TermCode') + TermCode')
ret-no-pair-10 = inr ∘ rebuild-10

ret-no-pair-11 : Term (TyFuncCode * TermCode') ((TermCode' * TermCode') + TermCode')
ret-no-pair-11 = inr ∘ rebuild-11

ret-no-pair-12 : Term ((TyFuncCode * TyFuncCode) * (TyFuncCode * TermCode')) ((TermCode' * TermCode') + TermCode')
ret-no-pair-12 = inr ∘ rebuild-12

ret-no-pair-13 : Term (TyFuncCode * TyFuncCode) ((TermCode' * TermCode') + TermCode')
ret-no-pair-13 = inr ∘ rebuild-13

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
                          , ret-no-pair-13
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

-- is-inl: Position 5 returns yes
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
                          , ret-no-13
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

-- is-inr: Position 6 returns yes
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
                          , ret-no-13
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

-- is-case: Position 7 returns inl (with case branches), others return inr
-- Return type: (TermCode' * TermCode') + TermCode'
is-case-dispatch : Term (⟦ TermF ⟧F TermCode') ((TermCode' * TermCode') + TermCode')
is-case-dispatch =
  [ ret-no-pair-0
  , [ ret-no-pair-1
    , [ ret-no-pair-2
      , [ ret-no-pair-3
        , [ ret-no-pair-4  -- 4: pair → no (rebuild at position 4)
          , [ ret-no-pair-5
            , [ ret-no-pair-6
              , [ inl  -- 7: case → yes, return the branches
                , [ ret-no-pair-8
                  , [ ret-no-pair-9
                    , [ ret-no-pair-10
                      , [ ret-no-pair-11
                        , [ ret-no-pair-12
                          , ret-no-pair-13
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

-- is-In: Position 9 returns yes
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
                  , [ ret-yes  -- 9: In → yes
                    , [ ret-no-10
                      , [ ret-no-11
                        , [ ret-no-12
                          , ret-no-13
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

-- is-Out: Position 10 returns yes
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
                    , [ ret-yes  -- 10: Out → yes
                      , [ ret-no-11
                        , [ ret-no-12
                          , ret-no-13
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

-- is-cata: Position 11 returns inl (with functor and algebra), others return inr
-- Return type: (TyFuncCode * TermCode') + TermCode'
ret-no-cata-0 : Term TyFuncCode ((TyFuncCode * TermCode') + TermCode')
ret-no-cata-0 = inr ∘ rebuild-0

ret-no-cata-1 : Term (TermCode' * TermCode') ((TyFuncCode * TermCode') + TermCode')
ret-no-cata-1 = inr ∘ rebuild-1

ret-no-cata-2 : Term (TyFuncCode * TyFuncCode) ((TyFuncCode * TermCode') + TermCode')
ret-no-cata-2 = inr ∘ rebuild-2

ret-no-cata-3 : Term (TyFuncCode * TyFuncCode) ((TyFuncCode * TermCode') + TermCode')
ret-no-cata-3 = inr ∘ rebuild-3

ret-no-cata-4 : Term (TermCode' * TermCode') ((TyFuncCode * TermCode') + TermCode')
ret-no-cata-4 = inr ∘ rebuild-4

ret-no-cata-5 : Term (TyFuncCode * TyFuncCode) ((TyFuncCode * TermCode') + TermCode')
ret-no-cata-5 = inr ∘ rebuild-5

ret-no-cata-6 : Term (TyFuncCode * TyFuncCode) ((TyFuncCode * TermCode') + TermCode')
ret-no-cata-6 = inr ∘ rebuild-6

ret-no-cata-7 : Term (TermCode' * TermCode') ((TyFuncCode * TermCode') + TermCode')
ret-no-cata-7 = inr ∘ rebuild-7

ret-no-cata-8 : Term TyFuncCode ((TyFuncCode * TermCode') + TermCode')
ret-no-cata-8 = inr ∘ rebuild-8

ret-no-cata-9 : Term TyFuncCode ((TyFuncCode * TermCode') + TermCode')
ret-no-cata-9 = inr ∘ rebuild-9

ret-no-cata-10 : Term TyFuncCode ((TyFuncCode * TermCode') + TermCode')
ret-no-cata-10 = inr ∘ rebuild-10

ret-no-cata-12 : Term ((TyFuncCode * TyFuncCode) * (TyFuncCode * TermCode')) ((TyFuncCode * TermCode') + TermCode')
ret-no-cata-12 = inr ∘ rebuild-12

ret-no-cata-13 : Term (TyFuncCode * TyFuncCode) ((TyFuncCode * TermCode') + TermCode')
ret-no-cata-13 = inr ∘ rebuild-13

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
                      , [ inl  -- 11: cata → yes, return functor and algebra
                        , [ ret-no-cata-12
                          , ret-no-cata-13
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

------------------------------------------------------------------------
-- Case-With-Context Combinator
--
-- In a CCC without exponentials, we cannot directly build:
--   caseWithCtx : (P * A → D) → (P * B → D) → (P * (A + B)) → D
--
-- using just the basic combinators, because [_,_] ∘ snd loses fst.
--
-- However, this IS definable in a distributive category (which ours is).
-- With exponentials (curry/apply), we can define this constructively!
------------------------------------------------------------------------

-- Distributivity: P * (A + B) → (P * A) + (P * B)
-- This is the key that enables caseWithCtx.
--
-- The construction uses curry to "remember" the context P while
-- case analyzing on (A + B), then uses apply to evaluate.
--
-- distrib = apply ∘ ⟨ [ curry (inl ∘ swap) , curry (inr ∘ swap) ] ∘ snd , fst ⟩
-- where swap : X * P → P * X reverses the pair

distrib : ∀ {P A B : Ty} → Term (P * (A + B)) ((P * A) + (P * B))
distrib = apply ∘ ⟨ [ curry (inl ∘ ⟨ snd , fst ⟩) , curry (inr ∘ ⟨ snd , fst ⟩) ] ∘ snd , fst ⟩

-- For case analysis that preserves context:
-- caseWithCtx takes:
--   - handler for "left" case: receives (context, left-value)
--   - handler for "right" case: receives (context, right-value)
--   - input: (context, left-or-right)
-- and dispatches appropriately
--
-- Now PROVEN using exponentials!
caseWithCtx : ∀ {P A B D : Ty} →
              Term (P * A) D →
              Term (P * B) D →
              Term (P * (A + B)) D
caseWithCtx l r = [ l , r ] ∘ distrib

-- Reduction rules follow from curry-β and case-inl/case-inr:
-- caseWithCtx l r ∘ ⟨ p , inl ∘ a ⟩
--   = [ l , r ] ∘ distrib ∘ ⟨ p , inl ∘ a ⟩
--   ⟶* [ l , r ] ∘ (inl ∘ ⟨ p , a ⟩)    (by distrib reduction)
--   ⟶ l ∘ ⟨ p , a ⟩                      (by case-inl)
-- Similarly for the inr case.

------------------------------------------------------------------------
-- Simple Handlers (just rebuild)
------------------------------------------------------------------------

-- Most positions just rebuild with In
handle-id : Term TyFuncCode TermCode'
handle-id = rebuild-0

handle-fst : Term (TyFuncCode * TyFuncCode) TermCode'
handle-fst = rebuild-2

handle-snd : Term (TyFuncCode * TyFuncCode) TermCode'
handle-snd = rebuild-3

handle-inl : Term (TyFuncCode * TyFuncCode) TermCode'
handle-inl = rebuild-5

handle-inr : Term (TyFuncCode * TyFuncCode) TermCode'
handle-inr = rebuild-6

handle-terminal : Term TyFuncCode TermCode'
handle-terminal = rebuild-8

handle-In : Term TyFuncCode TermCode'
handle-In = rebuild-9

handle-Out : Term TyFuncCode TermCode'
handle-Out = rebuild-10

handle-cata : Term (TyFuncCode * TermCode') TermCode'
handle-cata = rebuild-11

handle-curry : Term ((TyFuncCode * TyFuncCode) * (TyFuncCode * TermCode')) TermCode'
handle-curry = rebuild-12

handle-apply : Term (TyFuncCode * TyFuncCode) TermCode'
handle-apply = rebuild-13

------------------------------------------------------------------------
-- Composition Handler (position 1)
--
-- Input: (f, g) : TermCode' * TermCode' (already normalized)
--
-- Reduction rules to apply:
--   id ∘ g  → g
--   f ∘ id  → f
--   fst ∘ ⟨f,g⟩ → f
--   snd ∘ ⟨f,g⟩ → g
--   [f,g] ∘ inl → f
--   [f,g] ∘ inr → g
--
-- For now, we implement just id ∘ g → g and f ∘ id → f.
-- Other reductions can be added incrementally.
------------------------------------------------------------------------

-- Helper: prepare for is-id check on first component
-- ⟨ snd , is-id ∘ fst ⟩ : (f, g) → (g, Unit + f')
prep-check-f-id : Term (TermCode' * TermCode') (TermCode' * (Unit + TermCode'))
prep-check-f-id = ⟨ snd , is-id ∘ fst ⟩

-- When f = id: return g (which is fst after prep)
-- When f ≠ id: continue checking
comp-f-is-id : Term (TermCode' * Unit) TermCode'
comp-f-is-id = fst  -- g is in fst position after prep

-- Helper: prepare for is-id check on second component
-- Starting from (g, f') after f≠id, we want to check g
-- Restructure to (f', is-id(g))
prep-check-g-id : Term (TermCode' * TermCode') (TermCode' * (Unit + TermCode'))
prep-check-g-id = ⟨ fst , is-id ∘ snd ⟩

-- When g = id: return f' (which is fst)
comp-g-is-id : Term (TermCode' * Unit) TermCode'
comp-g-is-id = fst

-- When g ≠ id: rebuild as composition
-- Input: (f', g') where both are non-id normalized terms
comp-fallback : Term (TermCode' * TermCode') TermCode'
comp-fallback = rebuild-1  -- In ∘ inr ∘ inl = rebuild as comp

-- Full composition handler:
-- 1. Check if f = id, if so return g
-- 2. Else check if g = id, if so return f
-- 3. Else rebuild as comp(f, g)
--
-- Type trace:
--   prep-check-f-id : (f,g) → (g, Unit+f')
--   outer caseWithCtx left : (g, tt) → g
--   outer caseWithCtx right: (g, f') → check g next
--     prep-check-g-id : (g, f') → (f', Unit+g')
--     inner caseWithCtx left : (f', tt) → f'
--     inner caseWithCtx right: (f', g') → rebuild comp(f',g')

private
  -- Inner handler: check if g = id, broken out to help Agda type-check
  check-g-handler : Term (TermCode' * TermCode') TermCode'
  check-g-handler = caseWithCtx comp-g-is-id comp-fallback ∘ prep-check-g-id

handle-comp : Term (TermCode' * TermCode') TermCode'
handle-comp = caseWithCtx comp-f-is-id check-g-handler ∘ prep-check-f-id

------------------------------------------------------------------------
-- Pair Handler (position 4) - eta reduction
--
-- ⟨fst, snd⟩ → id
--
-- Check if first component is fst and second is snd.
-- If both: return encoded id
-- Otherwise: rebuild as pair
------------------------------------------------------------------------

-- Encoded id term (for eta reductions)
-- id is at position 0, with Unit type annotation
encoded-id : Term Unit TermCode'
encoded-id = In ∘ inl ∘ ⌜ Unit ⌝Ty

-- Check first component for fst
prep-check-fst : Term (TermCode' * TermCode') (TermCode' * (Unit + TermCode'))
prep-check-fst = ⟨ snd , is-fst ∘ fst ⟩

-- Check second component for snd
prep-check-snd : Term (TermCode' * TermCode') (TermCode' * (Unit + TermCode'))
prep-check-snd = ⟨ fst , is-snd ∘ snd ⟩

-- When both fst and snd: return id
pair-eta : Term (TermCode' * Unit) TermCode'
pair-eta = encoded-id ∘ terminal

-- When first is fst but second not snd: rebuild
pair-fst-but-not-snd : Term (TermCode' * TermCode') TermCode'
pair-fst-but-not-snd = rebuild-4 ∘ ⟨ rebuild-2 ∘ ⟨ ⌜ Unit ⌝Ty ∘ terminal , ⌜ Unit ⌝Ty ∘ terminal ⟩ , fst ⟩
-- Note: This is a simplified version; proper implementation would preserve original types

-- Pair handler: check for eta
-- Type trace:
--   prep-check-fst : (f,g) → (g, Unit+f') where f' is f if f≠fst
--   outer left: (g, tt) → f was fst, now check g for snd
--     prep-check-snd : (g, f') = (g, ??) → need restructure
--   outer right: (g, f') → f was not fst, just rebuild
--
-- Actually, after prep-check-fst with left branch (f=fst):
--   Input to left handler: (g, tt)
--   We need to check if g = snd
--   prep-check-snd expects (f,g) but we have (g, tt)
--   Need different approach for nested check
--
-- Simplified: just rebuild for now (eta optimization deferred)
handle-pair : Term (TermCode' * TermCode') TermCode'
handle-pair = rebuild-4

------------------------------------------------------------------------
-- Case Handler (position 7) - eta reduction
--
-- [inl, inr] → id
--
-- Check if first branch is inl and second is inr.
------------------------------------------------------------------------

-- Check first component for inl
prep-check-inl : Term (TermCode' * TermCode') (TermCode' * (Unit + TermCode'))
prep-check-inl = ⟨ snd , is-inl ∘ fst ⟩

-- Check second component for inr
prep-check-inr : Term (TermCode' * TermCode') (TermCode' * (Unit + TermCode'))
prep-check-inr = ⟨ fst , is-inr ∘ snd ⟩

-- When both inl and inr: return id
case-eta : Term (TermCode' * Unit) TermCode'
case-eta = encoded-id ∘ terminal

-- Case handler: check for eta
-- Simplified: just rebuild for now (eta optimization deferred)
handle-case : Term (TermCode' * TermCode') TermCode'
handle-case = rebuild-7

------------------------------------------------------------------------
-- The Normalizer Step Function
------------------------------------------------------------------------

normalize-step : Term (⟦ TermF ⟧F TermCode') TermCode'
normalize-step =
  [ handle-id
  , [ handle-comp
    , [ handle-fst
      , [ handle-snd
        , [ handle-pair
          , [ handle-inl
            , [ handle-inr
              , [ handle-case
                , [ handle-terminal
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

------------------------------------------------------------------------
-- The Normalizer
------------------------------------------------------------------------

-- The normalizer: applies normalize-step via catamorphism
-- Abstract prevents unfolding during MainTheorem type-checking
abstract
  normalize : Term TermCode' TermCode'
  normalize = cata TermF normalize-step

------------------------------------------------------------------------
-- The Encoding of the Normalizer
------------------------------------------------------------------------

-- The normalizer encoded as data
-- Abstract prevents Agda from unfolding during MainTheorem type-checking
abstract
  normalize-encoded : Term Unit TermCode'
  normalize-encoded = encode normalize

------------------------------------------------------------------------
-- Summary
--
-- We have defined:
--   normalize : Term TermCode' TermCode'
--   normalize = cata TermF normalize-step
--
-- The key postulate is normalize-step, which requires:
--   1. Pattern matching on 12-way sum (tedious but mechanical)
--   2. Detecting redex patterns using is-* helpers
--   3. Applying the appropriate reduction or rebuilding
--
-- Once normalize-step is built, we can:
--   1. Prove normalize achieves fixpoint on its encoding
--   2. Prove normalize produces normal forms
--   3. Complete the main theorem
------------------------------------------------------------------------
