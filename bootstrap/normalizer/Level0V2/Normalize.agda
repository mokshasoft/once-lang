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
open import normalizer.Level0V2.NoRedex hiding (is-id)
open import normalizer.Level0V2.Normalizer
  using (TermF-1; TermF-2; TermF-3; TermF-4; TermF-5; TermF-6;
         TermF-7; TermF-8; TermF-9; TermF-10; TermF-11; TermF-12)

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
-- NoRedex Proofs for Handlers
--
-- Each handler is a composition of NoRedex components.
-- These proofs enable proving normalize-noredex.
------------------------------------------------------------------------

-- rebuild-N is NoRedex (In ∘ chain of inr/inl)
-- Each chain is built incrementally

private
  -- Helper: inr chain compositions are NoRedex
  nr-inr-chain-1 : ∀ {A B C} → NoRedex (inr {C} ∘ inl {A} {B})
  nr-inr-chain-1 = nr-comp nr-inr nr-inl nis-inr nis-inl

  nr-inr-chain-2 : ∀ {A B C D} → NoRedex (inr {D} ∘ inr {C} ∘ inl {A} {B})
  nr-inr-chain-2 = nr-comp nr-inr nr-inr-chain-1 nis-inr nis-comp

  nr-inr-chain-3 : ∀ {A B C D E} → NoRedex (inr {E} ∘ inr {D} ∘ inr {C} ∘ inl {A} {B})
  nr-inr-chain-3 = nr-comp nr-inr nr-inr-chain-2 nis-inr nis-comp

  nr-inr-chain-4 : ∀ {A B C D E F} → NoRedex (inr {F} ∘ inr {E} ∘ inr {D} ∘ inr {C} ∘ inl {A} {B})
  nr-inr-chain-4 = nr-comp nr-inr nr-inr-chain-3 nis-inr nis-comp

  nr-inr-chain-5 : ∀ {A B C D E F G} → NoRedex (inr {G} ∘ inr {F} ∘ inr {E} ∘ inr {D} ∘ inr {C} ∘ inl {A} {B})
  nr-inr-chain-5 = nr-comp nr-inr nr-inr-chain-4 nis-inr nis-comp

  nr-inr-chain-6 : ∀ {A B C D E F G H} → NoRedex (inr {H} ∘ inr {G} ∘ inr {F} ∘ inr {E} ∘ inr {D} ∘ inr {C} ∘ inl {A} {B})
  nr-inr-chain-6 = nr-comp nr-inr nr-inr-chain-5 nis-inr nis-comp

  nr-inr-chain-7 : ∀ {A B C D E F G H I} → NoRedex (inr {I} ∘ inr {H} ∘ inr {G} ∘ inr {F} ∘ inr {E} ∘ inr {D} ∘ inr {C} ∘ inl {A} {B})
  nr-inr-chain-7 = nr-comp nr-inr nr-inr-chain-6 nis-inr nis-comp

  nr-inr-chain-8 : ∀ {A B C D E F G H I J} → NoRedex (inr {J} ∘ inr {I} ∘ inr {H} ∘ inr {G} ∘ inr {F} ∘ inr {E} ∘ inr {D} ∘ inr {C} ∘ inl {A} {B})
  nr-inr-chain-8 = nr-comp nr-inr nr-inr-chain-7 nis-inr nis-comp

  nr-inr-chain-9 : ∀ {A B C D E F G H I J K} → NoRedex (inr {K} ∘ inr {J} ∘ inr {I} ∘ inr {H} ∘ inr {G} ∘ inr {F} ∘ inr {E} ∘ inr {D} ∘ inr {C} ∘ inl {A} {B})
  nr-inr-chain-9 = nr-comp nr-inr nr-inr-chain-8 nis-inr nis-comp

  nr-inr-chain-10 : ∀ {A B C D E F G H I J K L} → NoRedex (inr {L} ∘ inr {K} ∘ inr {J} ∘ inr {I} ∘ inr {H} ∘ inr {G} ∘ inr {F} ∘ inr {E} ∘ inr {D} ∘ inr {C} ∘ inl {A} {B})
  nr-inr-chain-10 = nr-comp nr-inr nr-inr-chain-9 nis-inr nis-comp

  nr-inr-chain-11 : ∀ {A B C D E F G H I J K L M} → NoRedex (inr {M} ∘ inr {L} ∘ inr {K} ∘ inr {J} ∘ inr {I} ∘ inr {H} ∘ inr {G} ∘ inr {F} ∘ inr {E} ∘ inr {D} ∘ inr {C} ∘ inl {A} {B})
  nr-inr-chain-11 = nr-comp nr-inr nr-inr-chain-10 nis-inr nis-comp

  nr-inr-chain-12 : ∀ {A B C D E F G H I J K L M N} → NoRedex (inr {N} ∘ inr {M} ∘ inr {L} ∘ inr {K} ∘ inr {J} ∘ inr {I} ∘ inr {H} ∘ inr {G} ∘ inr {F} ∘ inr {E} ∘ inr {D} ∘ inr {C} ∘ inl {A} {B})
  nr-inr-chain-12 = nr-comp nr-inr nr-inr-chain-11 nis-inr nis-comp

  -- Rightmost chain (no inl at end)
  nr-inr-end-1 : ∀ {A B} → NoRedex (inr {A} {B})
  nr-inr-end-1 = nr-inr

  nr-inr-end-2 : ∀ {A B C} → NoRedex (inr {A} ∘ inr {B} {C})
  nr-inr-end-2 = nr-comp nr-inr nr-inr-end-1 nis-inr nis-inr

  nr-inr-end-3 : ∀ {A B C D} → NoRedex (inr {A} ∘ inr {B} ∘ inr {C} {D})
  nr-inr-end-3 = nr-comp nr-inr nr-inr-end-2 nis-inr nis-comp

  nr-inr-end-4 : ∀ {A B C D E} → NoRedex (inr {A} ∘ inr {B} ∘ inr {C} ∘ inr {D} {E})
  nr-inr-end-4 = nr-comp nr-inr nr-inr-end-3 nis-inr nis-comp

  nr-inr-end-5 : ∀ {A B C D E F} → NoRedex (inr {A} ∘ inr {B} ∘ inr {C} ∘ inr {D} ∘ inr {E} {F})
  nr-inr-end-5 = nr-comp nr-inr nr-inr-end-4 nis-inr nis-comp

  nr-inr-end-6 : ∀ {A B C D E F G} → NoRedex (inr {A} ∘ inr {B} ∘ inr {C} ∘ inr {D} ∘ inr {E} ∘ inr {F} {G})
  nr-inr-end-6 = nr-comp nr-inr nr-inr-end-5 nis-inr nis-comp

  nr-inr-end-7 : ∀ {A B C D E F G H} → NoRedex (inr {A} ∘ inr {B} ∘ inr {C} ∘ inr {D} ∘ inr {E} ∘ inr {F} ∘ inr {G} {H})
  nr-inr-end-7 = nr-comp nr-inr nr-inr-end-6 nis-inr nis-comp

  nr-inr-end-8 : ∀ {A B C D E F G H I} → NoRedex (inr {A} ∘ inr {B} ∘ inr {C} ∘ inr {D} ∘ inr {E} ∘ inr {F} ∘ inr {G} ∘ inr {H} {I})
  nr-inr-end-8 = nr-comp nr-inr nr-inr-end-7 nis-inr nis-comp

  nr-inr-end-9 : ∀ {A B C D E F G H I J} → NoRedex (inr {A} ∘ inr {B} ∘ inr {C} ∘ inr {D} ∘ inr {E} ∘ inr {F} ∘ inr {G} ∘ inr {H} ∘ inr {I} {J})
  nr-inr-end-9 = nr-comp nr-inr nr-inr-end-8 nis-inr nis-comp

  nr-inr-end-10 : ∀ {A B C D E F G H I J K} → NoRedex (inr {A} ∘ inr {B} ∘ inr {C} ∘ inr {D} ∘ inr {E} ∘ inr {F} ∘ inr {G} ∘ inr {H} ∘ inr {I} ∘ inr {J} {K})
  nr-inr-end-10 = nr-comp nr-inr nr-inr-end-9 nis-inr nis-comp

  nr-inr-end-11 : ∀ {A B C D E F G H I J K L} → NoRedex (inr {A} ∘ inr {B} ∘ inr {C} ∘ inr {D} ∘ inr {E} ∘ inr {F} ∘ inr {G} ∘ inr {H} ∘ inr {I} ∘ inr {J} ∘ inr {K} {L})
  nr-inr-end-11 = nr-comp nr-inr nr-inr-end-10 nis-inr nis-comp

  nr-inr-end-12 : ∀ {A B C D E F G H I J K L M} → NoRedex (inr {A} ∘ inr {B} ∘ inr {C} ∘ inr {D} ∘ inr {E} ∘ inr {F} ∘ inr {G} ∘ inr {H} ∘ inr {I} ∘ inr {J} ∘ inr {K} ∘ inr {L} {M})
  nr-inr-end-12 = nr-comp nr-inr nr-inr-end-11 nis-inr nis-comp

  nr-inr-end-13 : ∀ {A B C D E F G H I J K L M N} → NoRedex (inr {A} ∘ inr {B} ∘ inr {C} ∘ inr {D} ∘ inr {E} ∘ inr {F} ∘ inr {G} ∘ inr {H} ∘ inr {I} ∘ inr {J} ∘ inr {K} ∘ inr {L} ∘ inr {M} {N})
  nr-inr-end-13 = nr-comp nr-inr nr-inr-end-12 nis-inr nis-comp

-- NoRedex proofs for rebuild functions
nr-rebuild-0 : NoRedex rebuild-0
nr-rebuild-0 = nr-comp nr-In nr-inl nis-In nis-inl

nr-rebuild-1 : NoRedex rebuild-1
nr-rebuild-1 = nr-comp nr-In nr-inr-chain-1 nis-In nis-comp

nr-rebuild-2 : NoRedex rebuild-2
nr-rebuild-2 = nr-comp nr-In nr-inr-chain-2 nis-In nis-comp

nr-rebuild-3 : NoRedex rebuild-3
nr-rebuild-3 = nr-comp nr-In nr-inr-chain-3 nis-In nis-comp

nr-rebuild-4 : NoRedex rebuild-4
nr-rebuild-4 = nr-comp nr-In nr-inr-chain-4 nis-In nis-comp

nr-rebuild-5 : NoRedex rebuild-5
nr-rebuild-5 = nr-comp nr-In nr-inr-chain-5 nis-In nis-comp

nr-rebuild-6 : NoRedex rebuild-6
nr-rebuild-6 = nr-comp nr-In nr-inr-chain-6 nis-In nis-comp

nr-rebuild-7 : NoRedex rebuild-7
nr-rebuild-7 = nr-comp nr-In nr-inr-chain-7 nis-In nis-comp

nr-rebuild-8 : NoRedex rebuild-8
nr-rebuild-8 = nr-comp nr-In nr-inr-chain-8 nis-In nis-comp

nr-rebuild-9 : NoRedex rebuild-9
nr-rebuild-9 = nr-comp nr-In nr-inr-chain-9 nis-In nis-comp

nr-rebuild-10 : NoRedex rebuild-10
nr-rebuild-10 = nr-comp nr-In nr-inr-chain-10 nis-In nis-comp

nr-rebuild-11 : NoRedex rebuild-11
nr-rebuild-11 = nr-comp nr-In nr-inr-chain-11 nis-In nis-comp

nr-rebuild-12 : NoRedex rebuild-12
nr-rebuild-12 = nr-comp nr-In nr-inr-chain-12 nis-In nis-comp

nr-rebuild-13 : NoRedex rebuild-13
nr-rebuild-13 = nr-comp nr-In nr-inr-end-13 nis-In nis-comp

-- NoRedex proofs for simple handlers (just rebuilds)
nr-handle-id : NoRedex handle-id
nr-handle-id = nr-rebuild-0

nr-handle-fst : NoRedex handle-fst
nr-handle-fst = nr-rebuild-2

nr-handle-snd : NoRedex handle-snd
nr-handle-snd = nr-rebuild-3

nr-handle-pair : NoRedex handle-pair
nr-handle-pair = nr-rebuild-4

nr-handle-inl : NoRedex handle-inl
nr-handle-inl = nr-rebuild-5

nr-handle-inr : NoRedex handle-inr
nr-handle-inr = nr-rebuild-6

nr-handle-case : NoRedex handle-case
nr-handle-case = nr-rebuild-7

nr-handle-terminal : NoRedex handle-terminal
nr-handle-terminal = nr-rebuild-8

nr-handle-In : NoRedex handle-In
nr-handle-In = nr-rebuild-9

nr-handle-Out : NoRedex handle-Out
nr-handle-Out = nr-rebuild-10

nr-handle-cata : NoRedex handle-cata
nr-handle-cata = nr-rebuild-11

nr-handle-curry : NoRedex handle-curry
nr-handle-curry = nr-rebuild-12

nr-handle-apply : NoRedex handle-apply
nr-handle-apply = nr-rebuild-13

-- NoRedex proof for handle-comp (complex but mechanical)
-- handle-comp = caseWithCtx comp-f-is-id check-g-handler ∘ prep-check-f-id
-- This requires proving NoRedex for caseWithCtx, distrib, detect helpers, etc.
-- For now, we use the fact that all components are compositions of NoRedex terms.

private
  -- Helper: swap = ⟨ snd, fst ⟩ is NoRedex
  nr-swap : ∀ {A B} → NoRedex (⟨ snd {A} {B} , fst ⟩)
  nr-swap = nr-pair nr-snd nr-fst

  -- inl/inr ∘ swap
  nr-inl-swap : ∀ {A B C} → NoRedex (inl {A * B} {C} ∘ ⟨ snd , fst ⟩)
  nr-inl-swap = nr-comp nr-inl nr-swap nis-inl nis-pair

  nr-inr-swap : ∀ {A B C} → NoRedex (inr {C} {A * B} ∘ ⟨ snd , fst ⟩)
  nr-inr-swap = nr-comp nr-inr nr-swap nis-inr nis-pair

  -- curry of the above
  nr-curry-inl-swap : ∀ {A B C} → NoRedex (curry (inl {A * B} {C} ∘ ⟨ snd , fst ⟩))
  nr-curry-inl-swap = nr-curry nr-inl-swap

  nr-curry-inr-swap : ∀ {A B C} → NoRedex (curry (inr {C} {A * B} ∘ ⟨ snd , fst ⟩))
  nr-curry-inr-swap = nr-curry nr-inr-swap

  -- The case in distrib
  nr-distrib-case : ∀ {P A B} → NoRedex ([ curry (inl {P * A} {P * B} ∘ ⟨ snd , fst ⟩) , curry (inr ∘ ⟨ snd , fst ⟩) ])
  nr-distrib-case = nr-case nr-curry-inl-swap nr-curry-inr-swap

  -- case ∘ snd
  nr-distrib-case-snd : ∀ {P A B} → NoRedex ([ curry (inl {P * A} {P * B} ∘ ⟨ snd , fst ⟩) , curry (inr ∘ ⟨ snd , fst ⟩) ] ∘ snd {P} {A + B})
  nr-distrib-case-snd = nr-comp nr-distrib-case nr-snd nis-case nis-snd

  -- The pair in distrib: ⟨ case ∘ snd, fst ⟩
  nr-distrib-pair : ∀ {P A B} → NoRedex (⟨ [ curry (inl {P * A} {P * B} ∘ ⟨ snd , fst ⟩) , curry (inr ∘ ⟨ snd , fst ⟩) ] ∘ snd , fst ⟩)
  nr-distrib-pair = nr-pair nr-distrib-case-snd nr-fst

  -- distrib = apply ∘ pair
  nr-distrib : ∀ {P A B} → NoRedex (distrib {P} {A} {B})
  nr-distrib = nr-comp nr-apply nr-distrib-pair nis-apply nis-pair

  -- caseWithCtx l r = [ l, r ] ∘ distrib
  nr-caseWithCtx : ∀ {P A B D} {l : Term (P * A) D} {r : Term (P * B) D} →
                   NoRedex l → NoRedex r → NoRedex (caseWithCtx l r)
  nr-caseWithCtx nrl nrr = nr-comp (nr-case nrl nrr) nr-distrib nis-case nis-comp

  -- is-id-dispatch is NoRedex (14-way nested case of NoRedex handlers)
  -- Each branch is either ret-yes (inl ∘ terminal) or ret-no-N (inr ∘ rebuild-N)
  nr-ret-yes : ∀ {A} → NoRedex (ret-yes {A})
  nr-ret-yes = nr-comp nr-inl nr-terminal nis-inl nis-terminal

  nr-ret-no-0 : NoRedex ret-no-0
  nr-ret-no-0 = nr-comp nr-inr nr-rebuild-0 nis-inr nis-comp

  nr-ret-no-1 : NoRedex ret-no-1
  nr-ret-no-1 = nr-comp nr-inr nr-rebuild-1 nis-inr nis-comp

  nr-ret-no-2 : NoRedex ret-no-2
  nr-ret-no-2 = nr-comp nr-inr nr-rebuild-2 nis-inr nis-comp

  nr-ret-no-3 : NoRedex ret-no-3
  nr-ret-no-3 = nr-comp nr-inr nr-rebuild-3 nis-inr nis-comp

  nr-ret-no-4 : NoRedex ret-no-4
  nr-ret-no-4 = nr-comp nr-inr nr-rebuild-4 nis-inr nis-comp

  nr-ret-no-5 : NoRedex ret-no-5
  nr-ret-no-5 = nr-comp nr-inr nr-rebuild-5 nis-inr nis-comp

  nr-ret-no-6 : NoRedex ret-no-6
  nr-ret-no-6 = nr-comp nr-inr nr-rebuild-6 nis-inr nis-comp

  nr-ret-no-7 : NoRedex ret-no-7
  nr-ret-no-7 = nr-comp nr-inr nr-rebuild-7 nis-inr nis-comp

  nr-ret-no-8 : NoRedex ret-no-8
  nr-ret-no-8 = nr-comp nr-inr nr-rebuild-8 nis-inr nis-comp

  nr-ret-no-9 : NoRedex ret-no-9
  nr-ret-no-9 = nr-comp nr-inr nr-rebuild-9 nis-inr nis-comp

  nr-ret-no-10 : NoRedex ret-no-10
  nr-ret-no-10 = nr-comp nr-inr nr-rebuild-10 nis-inr nis-comp

  nr-ret-no-11 : NoRedex ret-no-11
  nr-ret-no-11 = nr-comp nr-inr nr-rebuild-11 nis-inr nis-comp

  nr-ret-no-12 : NoRedex ret-no-12
  nr-ret-no-12 = nr-comp nr-inr nr-rebuild-12 nis-inr nis-comp

  nr-ret-no-13 : NoRedex ret-no-13
  nr-ret-no-13 = nr-comp nr-inr nr-rebuild-13 nis-inr nis-comp

  -- is-id-dispatch is a 14-way nested case
  nr-is-id-dispatch : NoRedex is-id-dispatch
  nr-is-id-dispatch =
    nr-case nr-ret-yes
      (nr-case nr-ret-no-1
        (nr-case nr-ret-no-2
          (nr-case nr-ret-no-3
            (nr-case nr-ret-no-4
              (nr-case nr-ret-no-5
                (nr-case nr-ret-no-6
                  (nr-case nr-ret-no-7
                    (nr-case nr-ret-no-8
                      (nr-case nr-ret-no-9
                        (nr-case nr-ret-no-10
                          (nr-case nr-ret-no-11
                            (nr-case nr-ret-no-12 nr-ret-no-13))))))))))))

  -- is-id = is-id-dispatch ∘ Out
  nr-is-id' : NoRedex is-id
  nr-is-id' = nr-comp nr-is-id-dispatch nr-Out nis-case nis-Out

  -- prep-check-f-id = ⟨ snd, is-id ∘ fst ⟩
  nr-is-id-fst : NoRedex (is-id ∘ fst {TermCode'} {TermCode'})
  nr-is-id-fst = nr-comp nr-is-id' nr-fst nis-comp nis-fst

  nr-prep-check-f-id : NoRedex prep-check-f-id
  nr-prep-check-f-id = nr-pair nr-snd nr-is-id-fst

  -- comp-f-is-id = fst
  nr-comp-f-is-id : NoRedex comp-f-is-id
  nr-comp-f-is-id = nr-fst

  -- prep-check-g-id = ⟨ fst, is-id ∘ snd ⟩
  nr-is-id-snd : NoRedex (is-id ∘ snd {TermCode'} {TermCode'})
  nr-is-id-snd = nr-comp nr-is-id' nr-snd nis-comp nis-snd

  nr-prep-check-g-id : NoRedex prep-check-g-id
  nr-prep-check-g-id = nr-pair nr-fst nr-is-id-snd

  -- comp-g-is-id = fst
  nr-comp-g-is-id : NoRedex comp-g-is-id
  nr-comp-g-is-id = nr-fst

  -- comp-fallback = rebuild-1
  nr-comp-fallback : NoRedex comp-fallback
  nr-comp-fallback = nr-rebuild-1

  -- check-g-handler = caseWithCtx comp-g-is-id comp-fallback ∘ prep-check-g-id
  nr-check-g-handler : NoRedex check-g-handler
  nr-check-g-handler = nr-comp (nr-caseWithCtx nr-comp-g-is-id nr-comp-fallback) nr-prep-check-g-id nis-comp nis-pair

-- handle-comp = caseWithCtx comp-f-is-id check-g-handler ∘ prep-check-f-id
nr-handle-comp : NoRedex handle-comp
nr-handle-comp = nr-comp (nr-caseWithCtx nr-comp-f-is-id nr-check-g-handler) nr-prep-check-f-id nis-comp nis-pair

------------------------------------------------------------------------
-- Case Dispatch Infrastructure
--
-- To prove that normalize-step at position N reduces to handle-N,
-- we define the tails of the nested case and prove dispatch lemmas.
------------------------------------------------------------------------

-- Tails of normalize-step (nested cases without outer handlers)
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

nstep-tail-2 : Term (⟦ TermF-2 ⟧F TermCode') TermCode'
nstep-tail-2 =
    [ handle-fst
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

nstep-tail-3 : Term (⟦ TermF-3 ⟧F TermCode') TermCode'
nstep-tail-3 =
    [ handle-snd
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

nstep-tail-4 : Term (⟦ TermF-4 ⟧F TermCode') TermCode'
nstep-tail-4 =
    [ handle-pair
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

nstep-tail-5 : Term (⟦ TermF-5 ⟧F TermCode') TermCode'
nstep-tail-5 =
    [ handle-inl
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

nstep-tail-6 : Term (⟦ TermF-6 ⟧F TermCode') TermCode'
nstep-tail-6 =
    [ handle-inr
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

nstep-tail-7 : Term (⟦ TermF-7 ⟧F TermCode') TermCode'
nstep-tail-7 =
    [ handle-case
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

nstep-tail-8 : Term (⟦ TermF-8 ⟧F TermCode') TermCode'
nstep-tail-8 =
    [ handle-terminal
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

nstep-tail-9 : Term (⟦ TermF-9 ⟧F TermCode') TermCode'
nstep-tail-9 =
    [ handle-In
    , [ handle-Out
      , [ handle-cata
        , [ handle-curry
          , handle-apply
          ]
        ]
      ]
    ]

nstep-tail-10 : Term (⟦ TermF-10 ⟧F TermCode') TermCode'
nstep-tail-10 =
    [ handle-Out
    , [ handle-cata
      , [ handle-curry
        , handle-apply
        ]
      ]
    ]

nstep-tail-11 : Term (⟦ TermF-11 ⟧F TermCode') TermCode'
nstep-tail-11 =
    [ handle-cata
    , [ handle-curry
      , handle-apply
      ]
    ]

nstep-tail-12 : Term (⟦ TermF-12 ⟧F TermCode') TermCode'
nstep-tail-12 =
    [ handle-curry
    , handle-apply
    ]

-- Dispatch lemmas: normalize-step ∘ inr ⟶ nstep-tail-1, etc.
nstep-inr : (normalize-step ∘ inr) ⟶ nstep-tail-1
nstep-inr = case-inr

-- Tail dispatch lemmas
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

-- Dispatch lemmas for inl at each position
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

tail-9-inl : (nstep-tail-9 ∘ inl) ⟶ handle-In
tail-9-inl = case-inl

tail-10-inl : (nstep-tail-10 ∘ inl) ⟶ handle-Out
tail-10-inl = case-inl

tail-11-inl : (nstep-tail-11 ∘ inl) ⟶ handle-cata
tail-11-inl = case-inl

tail-12-inl : (nstep-tail-12 ∘ inl) ⟶ handle-curry
tail-12-inl = case-inl

tail-12-inr : (nstep-tail-12 ∘ inr) ⟶ handle-apply
tail-12-inr = case-inr

-- The complete NoRedex proof for normalize-step
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
                    (nr-case nr-handle-In
                      (nr-case nr-handle-Out
                        (nr-case nr-handle-cata
                          (nr-case nr-handle-curry nr-handle-apply))))))))))))

------------------------------------------------------------------------
-- The Normalizer
------------------------------------------------------------------------

-- The normalizer: applies normalize-step via catamorphism
-- Abstract prevents unfolding during MainTheorem type-checking
-- Import congruence helpers for the proof
open import normalizer.Level0V2.Normalizer
  using (∘-cong-left'; ∘-cong-right'; cata-β-right; fmap-TermF-inl;
         fmap-TermF-inr; fmap-1-inr; fmap-2-inr; fmap-3-inr; fmap-4-inr;
         fmap-5-inr; fmap-6-inr; fmap-7-inr; fmap-8-inr; fmap-9-inr;
         fmap-10-inr; fmap-11-inr; fmap-12-inr;
         fmap-1-inl; fmap-2-inl; fmap-3-inl; fmap-4-inl; fmap-5-inl;
         fmap-6-inl; fmap-7-inl; fmap-8-inl; fmap-9-inl; fmap-10-inl;
         fmap-KK-id; fmap-K-is-id; ⟨⟩-cong;
         fmap-sum-inl; TermF-11; TermF-12; TermF-13)

-- Payload functor for curry (position 12): (K⊗K) ⊗ (K⊗Id)
-- Defined outside abstract block so ⟦ CurryPayloadF ⟧F reduces properly
CurryPayloadF : Func
CurryPayloadF = (K TyFuncCode ⊗ K TyFuncCode) ⊗ (K TyFuncCode ⊗ Id)

abstract
  normalize : Term TermCode' TermCode'
  normalize = cata TermF normalize-step

  -- NoRedex proof for normalize
  normalize-noredex : NoRedex normalize
  normalize-noredex = nr-cata nr-normalize-step

  ------------------------------------------------------------------------
  -- Fixpoint Property for NoRedex Terms
  --
  -- For NoRedex t: normalize ∘ encode t ⟶* encode t
  --
  -- Proof structure (same as refold-idempotent):
  -- 1. Unfold cata via cata-β-right
  -- 2. Apply fmap reductions to reach the injection
  -- 3. Apply case dispatch: normalize-step ∘ inj-N ⟶ handle-N
  -- 4. handle-N = In ∘ inj-N (definitionally, for N ≠ 1)
  -- 5. Reassociate to get encode t
  ------------------------------------------------------------------------

  -- Key lemma: normalize-step ∘ inl ⟶ handle-id = In ∘ inl
  nstep-inl : (normalize-step ∘ inl) ⟶ handle-id
  nstep-inl = case-inl

  -- Proof for id case
  noredex-fixpoint-id : ∀ {A} → (normalize ∘ encode (id {A})) ⟶* encode (id {A})
  noredex-fixpoint-id {A} = ⟶*-trans step1 (⟶*-trans step2 (⟶*-trans step3 step4))
    where
      -- Explicit type aliases for clarity
      N : Term TermCode' TermCode'
      N = cata TermF normalize-step

      -- Step 1: Unfold cata via cata-β-right
      step1 : (N ∘ (In {TermF} ∘ (inl {⟦ K TyFuncCode ⟧F TermCode'} ∘ ⌜ A ⌝Ty))) ⟶*
              ((normalize-step ∘ fmap TermF N) ∘ (inl ∘ ⌜ A ⌝Ty))
      step1 = cata-β-right {TermF} {TermCode'} {Unit} {normalize-step} {inl ∘ ⌜ A ⌝Ty}

      -- Step 2: Rearrange with assoc-l
      step2 : ((normalize-step ∘ fmap TermF N) ∘ (inl ∘ ⌜ A ⌝Ty)) ⟶*
              (((normalize-step ∘ fmap TermF N) ∘ inl) ∘ ⌜ A ⌝Ty)
      step2 = step assoc-l done

      -- Step 3: Reduce inner part
      -- (nstep ∘ fmap) ∘ inl ⟶* nstep ∘ inl ⟶ In ∘ inl
      inner-step : ((normalize-step ∘ fmap TermF N) ∘ inl) ⟶* (In {TermF} ∘ inl)
      inner-step =
        ⟶*-trans (step assoc-r done)                                 -- ⟶ nstep ∘ (fmap ∘ inl)
          (⟶*-trans (∘-cong-right' normalize-step (fmap-TermF-inl N)) -- ⟶* nstep ∘ inl
            (step nstep-inl done))                                    -- ⟶ In ∘ inl

      step3 : (((normalize-step ∘ fmap TermF N) ∘ inl) ∘ ⌜ A ⌝Ty) ⟶*
              ((In {TermF} ∘ inl) ∘ ⌜ A ⌝Ty)
      step3 = ∘-cong-left' (⌜ A ⌝Ty) inner-step

      -- Step 4: Reassociate
      step4 : ((In {TermF} ∘ inl) ∘ ⌜ A ⌝Ty) ⟶* (In {TermF} ∘ (inl ∘ ⌜ A ⌝Ty))
      step4 = step assoc-r done

  ------------------------------------------------------------------------
  -- Case Dispatch Lemmas for normalize-step at each position
  --
  -- These show that normalize-step ∘ inj-N ⟶* handle-N = In ∘ inj-N
  ------------------------------------------------------------------------

  -- Position 1 (comp): left-associated version for inner-step use
  nstep-at-1' : (((normalize-step ∘ inr) ∘ inl)) ⟶* handle-comp
  nstep-at-1' =
    ⟶*-trans (step (⟶-∘-l nstep-inr) done)
      (step tail-1-inl done)

  -- Position 2 (fst): ((normalize-step ∘ inr) ∘ inr) ∘ inl ⟶* handle-fst
  -- Note: left-associated type to match the result of assoc-l steps
  nstep-at-2 : (((normalize-step ∘ inr) ∘ inr) ∘ inl) ⟶* handle-fst
  nstep-at-2 =
    -- (((nstep ∘ inr) ∘ inr) ∘ inl) ⟶ ((tail-1 ∘ inr) ∘ inl) by ⟶-∘-l (⟶-∘-l nstep-inr)
    ⟶*-trans (step (⟶-∘-l (⟶-∘-l nstep-inr)) done)
      -- ((tail-1 ∘ inr) ∘ inl) ⟶ (tail-2 ∘ inl) by ⟶-∘-l tail-1-inr
      (⟶*-trans (step (⟶-∘-l tail-1-inr) done)
        -- (tail-2 ∘ inl) ⟶ handle-fst by tail-2-inl
        (step tail-2-inl done))

  -- Position 3 (snd): normalize-step ∘ inr ∘ inr ∘ inr ∘ inl ⟶* handle-snd
  -- Right-associated version (kept for reference)
  nstep-at-3 : (normalize-step ∘ inr ∘ inr ∘ inr ∘ inl) ⟶* handle-snd
  nstep-at-3 =
    ⟶*-trans (step assoc-l done)
      (⟶*-trans (∘-cong-left' (inr ∘ inr ∘ inl) (step nstep-inr done))
        (⟶*-trans (step assoc-l done)
          (⟶*-trans (∘-cong-left' (inr ∘ inl) (step tail-1-inr done))
            (⟶*-trans (step assoc-l done)
              (⟶*-trans (∘-cong-left' inl (step tail-2-inr done))
                (step tail-3-inl done))))))

  -- Position 3 (snd): left-associated version for inner-step use
  nstep-at-3' : ((((normalize-step ∘ inr) ∘ inr) ∘ inr) ∘ inl) ⟶* handle-snd
  nstep-at-3' =
    ⟶*-trans (step (⟶-∘-l (⟶-∘-l (⟶-∘-l nstep-inr))) done)
      (⟶*-trans (step (⟶-∘-l (⟶-∘-l tail-1-inr)) done)
        (⟶*-trans (step (⟶-∘-l tail-2-inr) done)
          (step tail-3-inl done)))

  -- Position 5 (inl): normalize-step ∘ inr^5 ∘ inl ⟶* handle-inl
  nstep-at-5 : (normalize-step ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl) ⟶* handle-inl
  nstep-at-5 =
    ⟶*-trans (step assoc-l done)
      (⟶*-trans (∘-cong-left' (inr ∘ inr ∘ inr ∘ inr ∘ inl) (step nstep-inr done))
        (⟶*-trans (step assoc-l done)
          (⟶*-trans (∘-cong-left' (inr ∘ inr ∘ inr ∘ inl) (step tail-1-inr done))
            (⟶*-trans (step assoc-l done)
              (⟶*-trans (∘-cong-left' (inr ∘ inr ∘ inl) (step tail-2-inr done))
                (⟶*-trans (step assoc-l done)
                  (⟶*-trans (∘-cong-left' (inr ∘ inl) (step tail-3-inr done))
                    (⟶*-trans (step assoc-l done)
                      (⟶*-trans (∘-cong-left' inl (step tail-4-inr done))
                        (step tail-5-inl done))))))))))

  -- Position 5 (inl): left-associated version for inner-step use
  nstep-at-5' : ((((((normalize-step ∘ inr) ∘ inr) ∘ inr) ∘ inr) ∘ inr) ∘ inl) ⟶* handle-inl
  nstep-at-5' =
    ⟶*-trans (step (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l nstep-inr))))) done)
      (⟶*-trans (step (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l tail-1-inr)))) done)
        (⟶*-trans (step (⟶-∘-l (⟶-∘-l (⟶-∘-l tail-2-inr))) done)
          (⟶*-trans (step (⟶-∘-l (⟶-∘-l tail-3-inr)) done)
            (⟶*-trans (step (⟶-∘-l tail-4-inr) done)
              (step tail-5-inl done)))))

  -- Position 6 (inr): normalize-step ∘ inr^6 ∘ inl ⟶* handle-inr
  nstep-at-6 : (normalize-step ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl) ⟶* handle-inr
  nstep-at-6 =
    ⟶*-trans (step assoc-l done)
      (⟶*-trans (∘-cong-left' (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl) (step nstep-inr done))
        (⟶*-trans (step assoc-l done)
          (⟶*-trans (∘-cong-left' (inr ∘ inr ∘ inr ∘ inr ∘ inl) (step tail-1-inr done))
            (⟶*-trans (step assoc-l done)
              (⟶*-trans (∘-cong-left' (inr ∘ inr ∘ inr ∘ inl) (step tail-2-inr done))
                (⟶*-trans (step assoc-l done)
                  (⟶*-trans (∘-cong-left' (inr ∘ inr ∘ inl) (step tail-3-inr done))
                    (⟶*-trans (step assoc-l done)
                      (⟶*-trans (∘-cong-left' (inr ∘ inl) (step tail-4-inr done))
                        (⟶*-trans (step assoc-l done)
                          (⟶*-trans (∘-cong-left' inl (step tail-5-inr done))
                            (step tail-6-inl done))))))))))))

  -- Position 4 (pair): left-associated version for inner-step use
  nstep-at-4' : (((((normalize-step ∘ inr) ∘ inr) ∘ inr) ∘ inr) ∘ inl) ⟶* handle-pair
  nstep-at-4' =
    ⟶*-trans (step (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l nstep-inr)))) done)
      (⟶*-trans (step (⟶-∘-l (⟶-∘-l (⟶-∘-l tail-1-inr))) done)
        (⟶*-trans (step (⟶-∘-l (⟶-∘-l tail-2-inr)) done)
          (⟶*-trans (step (⟶-∘-l tail-3-inr) done)
            (step tail-4-inl done))))

  -- Position 6 (inr): left-associated version for inner-step use
  nstep-at-6' : (((((((normalize-step ∘ inr) ∘ inr) ∘ inr) ∘ inr) ∘ inr) ∘ inr) ∘ inl) ⟶* handle-inr
  nstep-at-6' =
    ⟶*-trans (step (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l nstep-inr)))))) done)
      (⟶*-trans (step (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l tail-1-inr))))) done)
        (⟶*-trans (step (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l tail-2-inr)))) done)
          (⟶*-trans (step (⟶-∘-l (⟶-∘-l (⟶-∘-l tail-3-inr))) done)
            (⟶*-trans (step (⟶-∘-l (⟶-∘-l tail-4-inr)) done)
              (⟶*-trans (step (⟶-∘-l tail-5-inr) done)
                (step tail-6-inl done))))))

  -- Position 7 (case): left-associated version for inner-step use
  nstep-at-7' : ((((((((normalize-step ∘ inr) ∘ inr) ∘ inr) ∘ inr) ∘ inr) ∘ inr) ∘ inr) ∘ inl) ⟶* handle-case
  nstep-at-7' =
    ⟶*-trans (step (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l nstep-inr))))))) done)
      (⟶*-trans (step (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l tail-1-inr)))))) done)
        (⟶*-trans (step (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l tail-2-inr))))) done)
          (⟶*-trans (step (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l tail-3-inr)))) done)
            (⟶*-trans (step (⟶-∘-l (⟶-∘-l (⟶-∘-l tail-4-inr))) done)
              (⟶*-trans (step (⟶-∘-l (⟶-∘-l tail-5-inr)) done)
                (⟶*-trans (step (⟶-∘-l tail-6-inr) done)
                  (step tail-7-inl done)))))))

  -- Position 8 (terminal): normalize-step ∘ inr^8 ∘ inl ⟶* handle-terminal
  nstep-at-8 : (normalize-step ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl) ⟶* handle-terminal
  nstep-at-8 =
    ⟶*-trans (step assoc-l done)
      (⟶*-trans (∘-cong-left' (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl) (step nstep-inr done))
        (⟶*-trans (step assoc-l done)
          (⟶*-trans (∘-cong-left' (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl) (step tail-1-inr done))
            (⟶*-trans (step assoc-l done)
              (⟶*-trans (∘-cong-left' (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl) (step tail-2-inr done))
                (⟶*-trans (step assoc-l done)
                  (⟶*-trans (∘-cong-left' (inr ∘ inr ∘ inr ∘ inr ∘ inl) (step tail-3-inr done))
                    (⟶*-trans (step assoc-l done)
                      (⟶*-trans (∘-cong-left' (inr ∘ inr ∘ inr ∘ inl) (step tail-4-inr done))
                        (⟶*-trans (step assoc-l done)
                          (⟶*-trans (∘-cong-left' (inr ∘ inr ∘ inl) (step tail-5-inr done))
                            (⟶*-trans (step assoc-l done)
                              (⟶*-trans (∘-cong-left' (inr ∘ inl) (step tail-6-inr done))
                                (⟶*-trans (step assoc-l done)
                                  (⟶*-trans (∘-cong-left' inl (step tail-7-inr done))
                                    (step tail-8-inl done))))))))))))))))

  -- Position 8 (terminal): left-associated version for inner-step use
  nstep-at-8' : (((((((((normalize-step ∘ inr) ∘ inr) ∘ inr) ∘ inr) ∘ inr) ∘ inr) ∘ inr) ∘ inr) ∘ inl) ⟶* handle-terminal
  nstep-at-8' =
    ⟶*-trans (step (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l nstep-inr)))))))) done)
      (⟶*-trans (step (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l tail-1-inr))))))) done)
        (⟶*-trans (step (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l tail-2-inr)))))) done)
          (⟶*-trans (step (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l tail-3-inr))))) done)
            (⟶*-trans (step (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l tail-4-inr)))) done)
              (⟶*-trans (step (⟶-∘-l (⟶-∘-l (⟶-∘-l tail-5-inr))) done)
                (⟶*-trans (step (⟶-∘-l (⟶-∘-l tail-6-inr)) done)
                  (⟶*-trans (step (⟶-∘-l tail-7-inr) done)
                    (step tail-8-inl done))))))))

  -- Position 9 (In): normalize-step ∘ inr^9 ∘ inl ⟶* handle-In
  nstep-at-9 : (normalize-step ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl) ⟶* handle-In
  nstep-at-9 =
    ⟶*-trans (step assoc-l done)
      (⟶*-trans (∘-cong-left' (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl) (step nstep-inr done))
        (⟶*-trans (step assoc-l done)
          (⟶*-trans (∘-cong-left' (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl) (step tail-1-inr done))
            (⟶*-trans (step assoc-l done)
              (⟶*-trans (∘-cong-left' (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl) (step tail-2-inr done))
                (⟶*-trans (step assoc-l done)
                  (⟶*-trans (∘-cong-left' (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl) (step tail-3-inr done))
                    (⟶*-trans (step assoc-l done)
                      (⟶*-trans (∘-cong-left' (inr ∘ inr ∘ inr ∘ inr ∘ inl) (step tail-4-inr done))
                        (⟶*-trans (step assoc-l done)
                          (⟶*-trans (∘-cong-left' (inr ∘ inr ∘ inr ∘ inl) (step tail-5-inr done))
                            (⟶*-trans (step assoc-l done)
                              (⟶*-trans (∘-cong-left' (inr ∘ inr ∘ inl) (step tail-6-inr done))
                                (⟶*-trans (step assoc-l done)
                                  (⟶*-trans (∘-cong-left' (inr ∘ inl) (step tail-7-inr done))
                                    (⟶*-trans (step assoc-l done)
                                      (⟶*-trans (∘-cong-left' inl (step tail-8-inr done))
                                        (step tail-9-inl done))))))))))))))))))

  -- Position 9 (In): left-associated version for inner-step use
  nstep-at-9' : ((((((((((normalize-step ∘ inr) ∘ inr) ∘ inr) ∘ inr) ∘ inr) ∘ inr) ∘ inr) ∘ inr) ∘ inr) ∘ inl) ⟶* handle-In
  nstep-at-9' =
    ⟶*-trans (step (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l nstep-inr))))))))) done)
      (⟶*-trans (step (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l tail-1-inr)))))))) done)
        (⟶*-trans (step (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l tail-2-inr))))))) done)
          (⟶*-trans (step (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l tail-3-inr)))))) done)
            (⟶*-trans (step (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l tail-4-inr))))) done)
              (⟶*-trans (step (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l tail-5-inr)))) done)
                (⟶*-trans (step (⟶-∘-l (⟶-∘-l (⟶-∘-l tail-6-inr))) done)
                  (⟶*-trans (step (⟶-∘-l (⟶-∘-l tail-7-inr)) done)
                    (⟶*-trans (step (⟶-∘-l tail-8-inr) done)
                      (step tail-9-inl done)))))))))

  -- Position 10 (Out): normalize-step ∘ inr^10 ∘ inl ⟶* handle-Out
  nstep-at-10 : (normalize-step ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl) ⟶* handle-Out
  nstep-at-10 =
    ⟶*-trans (step assoc-l done)
      (⟶*-trans (∘-cong-left' (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl) (step nstep-inr done))
        (⟶*-trans (step assoc-l done)
          (⟶*-trans (∘-cong-left' (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl) (step tail-1-inr done))
            (⟶*-trans (step assoc-l done)
              (⟶*-trans (∘-cong-left' (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl) (step tail-2-inr done))
                (⟶*-trans (step assoc-l done)
                  (⟶*-trans (∘-cong-left' (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl) (step tail-3-inr done))
                    (⟶*-trans (step assoc-l done)
                      (⟶*-trans (∘-cong-left' (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl) (step tail-4-inr done))
                        (⟶*-trans (step assoc-l done)
                          (⟶*-trans (∘-cong-left' (inr ∘ inr ∘ inr ∘ inr ∘ inl) (step tail-5-inr done))
                            (⟶*-trans (step assoc-l done)
                              (⟶*-trans (∘-cong-left' (inr ∘ inr ∘ inr ∘ inl) (step tail-6-inr done))
                                (⟶*-trans (step assoc-l done)
                                  (⟶*-trans (∘-cong-left' (inr ∘ inr ∘ inl) (step tail-7-inr done))
                                    (⟶*-trans (step assoc-l done)
                                      (⟶*-trans (∘-cong-left' (inr ∘ inl) (step tail-8-inr done))
                                        (⟶*-trans (step assoc-l done)
                                          (⟶*-trans (∘-cong-left' inl (step tail-9-inr done))
                                            (step tail-10-inl done))))))))))))))))))))

  -- Position 10 (Out): left-associated version for inner-step use
  nstep-at-10' : (((((((((((normalize-step ∘ inr) ∘ inr) ∘ inr) ∘ inr) ∘ inr) ∘ inr) ∘ inr) ∘ inr) ∘ inr) ∘ inr) ∘ inl) ⟶* handle-Out
  nstep-at-10' =
    ⟶*-trans (step (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l nstep-inr)))))))))) done)
      (⟶*-trans (step (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l tail-1-inr))))))))) done)
        (⟶*-trans (step (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l tail-2-inr)))))))) done)
          (⟶*-trans (step (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l tail-3-inr))))))) done)
            (⟶*-trans (step (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l tail-4-inr)))))) done)
              (⟶*-trans (step (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l tail-5-inr))))) done)
                (⟶*-trans (step (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l tail-6-inr)))) done)
                  (⟶*-trans (step (⟶-∘-l (⟶-∘-l (⟶-∘-l tail-7-inr))) done)
                    (⟶*-trans (step (⟶-∘-l (⟶-∘-l tail-8-inr)) done)
                      (⟶*-trans (step (⟶-∘-l tail-9-inr) done)
                        (step tail-10-inl done))))))))))

  -- Position 11 (cata): left-associated version for inner-step use
  nstep-at-11' : ((((((((((((normalize-step ∘ inr) ∘ inr) ∘ inr) ∘ inr) ∘ inr) ∘ inr) ∘ inr) ∘ inr) ∘ inr) ∘ inr) ∘ inr) ∘ inl) ⟶* handle-cata
  nstep-at-11' =
    ⟶*-trans (step (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l nstep-inr))))))))))) done)
      (⟶*-trans (step (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l tail-1-inr)))))))))) done)
        (⟶*-trans (step (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l tail-2-inr))))))))) done)
          (⟶*-trans (step (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l tail-3-inr)))))))) done)
            (⟶*-trans (step (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l tail-4-inr))))))) done)
              (⟶*-trans (step (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l tail-5-inr)))))) done)
                (⟶*-trans (step (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l tail-6-inr))))) done)
                  (⟶*-trans (step (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l tail-7-inr)))) done)
                    (⟶*-trans (step (⟶-∘-l (⟶-∘-l (⟶-∘-l tail-8-inr))) done)
                      (⟶*-trans (step (⟶-∘-l (⟶-∘-l tail-9-inr)) done)
                        (⟶*-trans (step (⟶-∘-l tail-10-inr) done)
                          (step tail-11-inl done)))))))))))

  -- Position 12 (curry): left-associated version for inner-step use
  nstep-at-12' : (((((((((((((normalize-step ∘ inr) ∘ inr) ∘ inr) ∘ inr) ∘ inr) ∘ inr) ∘ inr) ∘ inr) ∘ inr) ∘ inr) ∘ inr) ∘ inr) ∘ inl) ⟶* handle-curry
  nstep-at-12' =
    ⟶*-trans (step (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l nstep-inr)))))))))))) done)
      (⟶*-trans (step (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l tail-1-inr))))))))))) done)
        (⟶*-trans (step (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l tail-2-inr)))))))))) done)
          (⟶*-trans (step (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l tail-3-inr))))))))) done)
            (⟶*-trans (step (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l tail-4-inr)))))))) done)
              (⟶*-trans (step (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l tail-5-inr))))))) done)
                (⟶*-trans (step (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l tail-6-inr)))))) done)
                  (⟶*-trans (step (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l tail-7-inr))))) done)
                    (⟶*-trans (step (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l tail-8-inr)))) done)
                      (⟶*-trans (step (⟶-∘-l (⟶-∘-l (⟶-∘-l tail-9-inr))) done)
                        (⟶*-trans (step (⟶-∘-l (⟶-∘-l tail-10-inr)) done)
                          (⟶*-trans (step (⟶-∘-l tail-11-inr) done)
                            (step tail-12-inl done))))))))))))

  -- Position 13 (apply): normalize-step ∘ inr^13 ⟶* handle-apply
  nstep-at-13 : (normalize-step ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr) ⟶* handle-apply
  nstep-at-13 =
    ⟶*-trans (step assoc-l done)
      (⟶*-trans (∘-cong-left' (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr) (step nstep-inr done))
        (⟶*-trans (step assoc-l done)
          (⟶*-trans (∘-cong-left' (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr) (step tail-1-inr done))
            (⟶*-trans (step assoc-l done)
              (⟶*-trans (∘-cong-left' (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr) (step tail-2-inr done))
                (⟶*-trans (step assoc-l done)
                  (⟶*-trans (∘-cong-left' (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr) (step tail-3-inr done))
                    (⟶*-trans (step assoc-l done)
                      (⟶*-trans (∘-cong-left' (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr) (step tail-4-inr done))
                        (⟶*-trans (step assoc-l done)
                          (⟶*-trans (∘-cong-left' (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr) (step tail-5-inr done))
                            (⟶*-trans (step assoc-l done)
                              (⟶*-trans (∘-cong-left' (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr) (step tail-6-inr done))
                                (⟶*-trans (step assoc-l done)
                                  (⟶*-trans (∘-cong-left' (inr ∘ inr ∘ inr ∘ inr ∘ inr) (step tail-7-inr done))
                                    (⟶*-trans (step assoc-l done)
                                      (⟶*-trans (∘-cong-left' (inr ∘ inr ∘ inr ∘ inr) (step tail-8-inr done))
                                        (⟶*-trans (step assoc-l done)
                                          (⟶*-trans (∘-cong-left' (inr ∘ inr ∘ inr) (step tail-9-inr done))
                                            (⟶*-trans (step assoc-l done)
                                              (⟶*-trans (∘-cong-left' (inr ∘ inr) (step tail-10-inr done))
                                                (⟶*-trans (step assoc-l done)
                                                  (⟶*-trans (∘-cong-left' inr (step tail-11-inr done))
                                                    (step tail-12-inr done))))))))))))))))))))))))

  -- Position 13 (apply): left-associated version for inner-step use (no inl at end)
  nstep-at-13' : ((((((((((((((normalize-step ∘ inr) ∘ inr) ∘ inr) ∘ inr) ∘ inr) ∘ inr) ∘ inr) ∘ inr) ∘ inr) ∘ inr) ∘ inr) ∘ inr) ∘ inr)) ⟶* handle-apply
  nstep-at-13' =
    ⟶*-trans (step (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l nstep-inr)))))))))))) done)
      (⟶*-trans (step (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l tail-1-inr))))))))))) done)
        (⟶*-trans (step (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l tail-2-inr)))))))))) done)
          (⟶*-trans (step (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l tail-3-inr))))))))) done)
            (⟶*-trans (step (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l tail-4-inr)))))))) done)
              (⟶*-trans (step (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l tail-5-inr))))))) done)
                (⟶*-trans (step (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l tail-6-inr)))))) done)
                  (⟶*-trans (step (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l tail-7-inr))))) done)
                    (⟶*-trans (step (⟶-∘-l (⟶-∘-l (⟶-∘-l (⟶-∘-l tail-8-inr)))) done)
                      (⟶*-trans (step (⟶-∘-l (⟶-∘-l (⟶-∘-l tail-9-inr))) done)
                        (⟶*-trans (step (⟶-∘-l (⟶-∘-l tail-10-inr)) done)
                          (⟶*-trans (step (⟶-∘-l tail-11-inr) done)
                            (step tail-12-inr done))))))))))))

  ------------------------------------------------------------------------
  -- Fixpoint proofs for atoms
  ------------------------------------------------------------------------

  -- Position 2 (fst): encode fst = In ∘ inr ∘ inr ∘ inl ∘ ⟨ ⌜A⌝, ⌜B⌝ ⟩
  noredex-fixpoint-fst : ∀ {A B} → (normalize ∘ encode (fst {A} {B})) ⟶* encode (fst {A} {B})
  noredex-fixpoint-fst {A} {B} = ⟶*-trans step1 (⟶*-trans step2 (⟶*-trans step3 step4))
    where
      N : Term TermCode' TermCode'
      N = cata TermF normalize-step

      payload : Term Unit (TyFuncCode * TyFuncCode)
      payload = ⟨ ⌜ A ⌝Ty , ⌜ B ⌝Ty ⟩

      -- Step 1: Unfold cata
      step1 : (N ∘ (In {TermF} ∘ (inr ∘ inr ∘ inl ∘ payload))) ⟶*
              ((normalize-step ∘ fmap TermF N) ∘ (inr ∘ inr ∘ inl ∘ payload))
      step1 = cata-β-right {TermF} {TermCode'} {Unit} {normalize-step} {inr ∘ inr ∘ inl ∘ payload}

      -- Step 2: Reduce fmap chain and apply case dispatch
      -- After cata-β-right: (nstep ∘ fmap) ∘ (inr ∘ inr ∘ inl ∘ payload)
      -- Need to reduce to: handle-fst ∘ payload = In ∘ inr ∘ inr ∘ inl ∘ payload

      -- fmap reductions (same as refold-idem-fst)
      r0 : (fmap TermF N ∘ (inr ∘ (inr ∘ inl ∘ payload))) ⟶* (inr ∘ (fmap TermF-1 N ∘ (inr ∘ inl ∘ payload)))
      r0 = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' (inr ∘ inl ∘ payload) (fmap-TermF-inr N)) (step assoc-r done))

      r1 : (fmap TermF-1 N ∘ (inr ∘ inl ∘ payload)) ⟶* (inr ∘ (fmap TermF-2 N ∘ (inl ∘ payload)))
      r1 = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' (inl ∘ payload) (fmap-1-inr N)) (step assoc-r done))

      -- Final position: fmap TermF-2 N ∘ (inl ∘ payload) ⟶* inl ∘ payload
      r2 : (fmap TermF-2 N ∘ (inl ∘ payload)) ⟶* (inl ∘ payload)
      r2 = ⟶*-trans (step assoc-l done)
             (⟶*-trans (∘-cong-left' payload (fmap-2-inl N))
               (⟶*-trans (step assoc-r done)
                 (⟶*-trans (∘-cong-right' inl
                   (⟶*-trans (∘-cong-left' payload (fmap-KK-id TyFuncCode TyFuncCode N))
                     (step id-left done)))
                   done)))

      -- Combine fmap reductions
      reduce-chain : (fmap TermF N ∘ (inr ∘ inr ∘ inl ∘ payload)) ⟶* (inr ∘ inr ∘ inl ∘ payload)
      reduce-chain =
        ⟶*-trans r0 (∘-cong-right' inr
          (⟶*-trans r1 (∘-cong-right' inr r2)))

      -- inner-step: nstep ∘ (inr ∘ inr ∘ inl ∘ payload) ⟶* handle-fst ∘ payload
      -- Structure: reassociate with assoc-l, then apply nstep-at-2 with congruence
      inner-step : (normalize-step ∘ (inr ∘ inr ∘ inl ∘ payload)) ⟶* (handle-fst ∘ payload)
      inner-step =
        -- nstep ∘ (inr ∘ (inr ∘ (inl ∘ payload))) ⟶ (nstep ∘ inr) ∘ (inr ∘ (inl ∘ payload))
        ⟶*-trans (step assoc-l done)
          -- (nstep ∘ inr) ∘ (inr ∘ (inl ∘ payload)) ⟶ ((nstep ∘ inr) ∘ inr) ∘ (inl ∘ payload)
          (⟶*-trans (step assoc-l done)
            -- ((nstep ∘ inr) ∘ inr) ∘ (inl ∘ payload) ⟶ (((nstep ∘ inr) ∘ inr) ∘ inl) ∘ payload
            (⟶*-trans (step assoc-l done)
              -- Apply nstep-at-2 with congruence on payload
              (∘-cong-left' payload nstep-at-2)))

      step2 : ((normalize-step ∘ fmap TermF N) ∘ (inr ∘ inr ∘ inl ∘ payload)) ⟶*
              (handle-fst ∘ payload)
      step2 = ⟶*-trans (step assoc-r done)
                (⟶*-trans (∘-cong-right' normalize-step reduce-chain)
                  inner-step)

      -- Step 3: handle-fst ∘ payload = (In ∘ inr ∘ inr ∘ inl) ∘ payload
      -- This is definitionally equal, so just done
      step3 : (handle-fst ∘ payload) ⟶* ((In {TermF} ∘ inr ∘ inr ∘ inl) ∘ payload)
      step3 = done  -- definitional equality

      -- Step 4: Reassociate
      -- (In ∘ (inr ∘ (inr ∘ inl))) ∘ payload ⟶* In ∘ (inr ∘ (inr ∘ (inl ∘ payload)))
      step4 : ((In {TermF} ∘ inr ∘ inr ∘ inl) ∘ payload) ⟶* (In {TermF} ∘ (inr ∘ inr ∘ inl ∘ payload))
      step4 = ⟶*-trans (step assoc-r done)
                -- In ∘ ((inr ∘ (inr ∘ inl)) ∘ payload) ⟶* In ∘ (inr ∘ (inr ∘ (inl ∘ payload)))
                (∘-cong-right' In
                  (⟶*-trans (step assoc-r done)
                    -- inr ∘ ((inr ∘ inl) ∘ payload) ⟶* inr ∘ (inr ∘ (inl ∘ payload))
                    (∘-cong-right' inr (step assoc-r done))))

  -- Position 3 (snd): encode snd = In ∘ inr ∘ inr ∘ inr ∘ inl ∘ ⟨ ⌜A⌝, ⌜B⌝ ⟩
  noredex-fixpoint-snd : ∀ {A B} → (normalize ∘ encode (snd {A} {B})) ⟶* encode (snd {A} {B})
  noredex-fixpoint-snd {A} {B} = ⟶*-trans step1 (⟶*-trans step2 (⟶*-trans step3 step4))
    where
      N : Term TermCode' TermCode'
      N = cata TermF normalize-step

      payload : Term Unit (TyFuncCode * TyFuncCode)
      payload = ⟨ ⌜ A ⌝Ty , ⌜ B ⌝Ty ⟩

      step1 : (N ∘ (In {TermF} ∘ (inr ∘ inr ∘ inr ∘ inl ∘ payload))) ⟶*
              ((normalize-step ∘ fmap TermF N) ∘ (inr ∘ inr ∘ inr ∘ inl ∘ payload))
      step1 = cata-β-right {TermF} {TermCode'} {Unit} {normalize-step} {inr ∘ inr ∘ inr ∘ inl ∘ payload}

      -- fmap reductions
      r0 : (fmap TermF N ∘ (inr ∘ (inr ∘ (inr ∘ (inl ∘ payload))))) ⟶* (inr ∘ (fmap TermF-1 N ∘ (inr ∘ (inr ∘ (inl ∘ payload)))))
      r0 = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' (inr ∘ (inr ∘ (inl ∘ payload))) (fmap-TermF-inr N)) (step assoc-r done))

      r1 : (fmap TermF-1 N ∘ (inr ∘ (inr ∘ (inl ∘ payload)))) ⟶* (inr ∘ (fmap TermF-2 N ∘ (inr ∘ (inl ∘ payload))))
      r1 = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' (inr ∘ (inl ∘ payload)) (fmap-1-inr N)) (step assoc-r done))

      r2 : (fmap TermF-2 N ∘ (inr ∘ (inl ∘ payload))) ⟶* (inr ∘ (fmap TermF-3 N ∘ (inl ∘ payload)))
      r2 = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' (inl ∘ payload) (fmap-2-inr N)) (step assoc-r done))

      r3 : (fmap TermF-3 N ∘ (inl ∘ payload)) ⟶* (inl ∘ payload)
      r3 = ⟶*-trans (step assoc-l done)
             (⟶*-trans (∘-cong-left' payload (fmap-3-inl N))
               (⟶*-trans (step assoc-r done)
                 (⟶*-trans (∘-cong-right' inl
                   (⟶*-trans (∘-cong-left' payload (fmap-KK-id TyFuncCode TyFuncCode N))
                     (step id-left done)))
                   done)))

      reduce-chain : (fmap TermF N ∘ (inr ∘ inr ∘ inr ∘ inl ∘ payload)) ⟶* (inr ∘ inr ∘ inr ∘ inl ∘ payload)
      reduce-chain =
        ⟶*-trans r0 (∘-cong-right' inr
          (⟶*-trans r1 (∘-cong-right' inr
            (⟶*-trans r2 (∘-cong-right' inr r3)))))

      inner-step : (normalize-step ∘ (inr ∘ inr ∘ inr ∘ inl ∘ payload)) ⟶* (handle-snd ∘ payload)
      inner-step =
        ⟶*-trans (step assoc-l done)
          (⟶*-trans (step assoc-l done)
            (⟶*-trans (step assoc-l done)
              (⟶*-trans (step assoc-l done)
                (∘-cong-left' payload nstep-at-3'))))

      step2 : ((normalize-step ∘ fmap TermF N) ∘ (inr ∘ inr ∘ inr ∘ inl ∘ payload)) ⟶*
              (handle-snd ∘ payload)
      step2 = ⟶*-trans (step assoc-r done)
                (⟶*-trans (∘-cong-right' normalize-step reduce-chain)
                  inner-step)

      step3 : (handle-snd ∘ payload) ⟶* ((In {TermF} ∘ inr ∘ inr ∘ inr ∘ inl) ∘ payload)
      step3 = done

      step4 : ((In {TermF} ∘ inr ∘ inr ∘ inr ∘ inl) ∘ payload) ⟶* (In {TermF} ∘ (inr ∘ inr ∘ inr ∘ inl ∘ payload))
      step4 = ⟶*-trans (step assoc-r done)
                (∘-cong-right' In
                  (⟶*-trans (step assoc-r done)
                    (∘-cong-right' inr
                      (⟶*-trans (step assoc-r done)
                        (∘-cong-right' inr (step assoc-r done))))))

  -- Position 5 (inl term constructor): encode inl = In ∘ inr^5 ∘ inl ∘ ⟨ ⌜A⌝, ⌜B⌝ ⟩
  noredex-fixpoint-inl : ∀ {A B} → (normalize ∘ encode (inl {A} {B})) ⟶* encode (inl {A} {B})
  noredex-fixpoint-inl {A} {B} = ⟶*-trans step1 (⟶*-trans step2 (⟶*-trans step3 step4))
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
      r0 = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inl ∘ payload))))) (fmap-TermF-inr N)) (step assoc-r done))

      r1 : (fmap TermF-1 N ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inl ∘ payload)))))) ⟶*
           (inr ∘ (fmap TermF-2 N ∘ (inr ∘ (inr ∘ (inr ∘ (inl ∘ payload))))))
      r1 = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' (inr ∘ (inr ∘ (inr ∘ (inl ∘ payload)))) (fmap-1-inr N)) (step assoc-r done))

      r2 : (fmap TermF-2 N ∘ (inr ∘ (inr ∘ (inr ∘ (inl ∘ payload))))) ⟶*
           (inr ∘ (fmap TermF-3 N ∘ (inr ∘ (inr ∘ (inl ∘ payload)))))
      r2 = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' (inr ∘ (inr ∘ (inl ∘ payload))) (fmap-2-inr N)) (step assoc-r done))

      r3 : (fmap TermF-3 N ∘ (inr ∘ (inr ∘ (inl ∘ payload)))) ⟶*
           (inr ∘ (fmap TermF-4 N ∘ (inr ∘ (inl ∘ payload))))
      r3 = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' (inr ∘ (inl ∘ payload)) (fmap-3-inr N)) (step assoc-r done))

      r4 : (fmap TermF-4 N ∘ (inr ∘ (inl ∘ payload))) ⟶*
           (inr ∘ (fmap TermF-5 N ∘ (inl ∘ payload)))
      r4 = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' (inl ∘ payload) (fmap-4-inr N)) (step assoc-r done))

      r5 : (fmap TermF-5 N ∘ (inl ∘ payload)) ⟶* (inl ∘ payload)
      r5 = ⟶*-trans (step assoc-l done)
             (⟶*-trans (∘-cong-left' payload (fmap-5-inl N))
               (⟶*-trans (step assoc-r done)
                 (⟶*-trans (∘-cong-right' inl
                   (⟶*-trans (∘-cong-left' payload (fmap-KK-id TyFuncCode TyFuncCode N))
                     (step id-left done)))
                   done)))

      reduce-chain : (fmap TermF N ∘ (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ payload)) ⟶* (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ payload)
      reduce-chain =
        ⟶*-trans r0 (∘-cong-right' inr
          (⟶*-trans r1 (∘-cong-right' inr
            (⟶*-trans r2 (∘-cong-right' inr
              (⟶*-trans r3 (∘-cong-right' inr
                (⟶*-trans r4 (∘-cong-right' inr r5)))))))))

      inner-step : (normalize-step ∘ (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ payload)) ⟶* (handle-inl ∘ payload)
      inner-step =
        ⟶*-trans (step assoc-l done)
          (⟶*-trans (step assoc-l done)
            (⟶*-trans (step assoc-l done)
              (⟶*-trans (step assoc-l done)
                (⟶*-trans (step assoc-l done)
                  (⟶*-trans (step assoc-l done)
                    (∘-cong-left' payload nstep-at-5'))))))

      step2 : ((normalize-step ∘ fmap TermF N) ∘ (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ payload)) ⟶*
              (handle-inl ∘ payload)
      step2 = ⟶*-trans (step assoc-r done)
                (⟶*-trans (∘-cong-right' normalize-step reduce-chain)
                  inner-step)

      step3 : (handle-inl ∘ payload) ⟶* ((In {TermF} ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl) ∘ payload)
      step3 = done

      step4 : ((In {TermF} ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl) ∘ payload) ⟶* (In {TermF} ∘ (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ payload))
      step4 = ⟶*-trans (step assoc-r done)
                (∘-cong-right' In
                  (⟶*-trans (step assoc-r done)
                    (∘-cong-right' inr
                      (⟶*-trans (step assoc-r done)
                        (∘-cong-right' inr
                          (⟶*-trans (step assoc-r done)
                            (∘-cong-right' inr
                              (⟶*-trans (step assoc-r done)
                                (∘-cong-right' inr (step assoc-r done))))))))))

  -- Position 6 (inr term constructor): encode inr = In ∘ inr^6 ∘ inl ∘ ⟨ ⌜A⌝, ⌜B⌝ ⟩
  noredex-fixpoint-inr : ∀ {A B} → (normalize ∘ encode (inr {A} {B})) ⟶* encode (inr {A} {B})
  noredex-fixpoint-inr {A} {B} = ⟶*-trans step1 (⟶*-trans step2 (⟶*-trans step3 step4))
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
      r0 = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inl ∘ payload)))))) (fmap-TermF-inr N)) (step assoc-r done))

      r1 : (fmap TermF-1 N ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inl ∘ payload))))))) ⟶*
           (inr ∘ (fmap TermF-2 N ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inl ∘ payload)))))))
      r1 = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inl ∘ payload))))) (fmap-1-inr N)) (step assoc-r done))

      r2 : (fmap TermF-2 N ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inl ∘ payload)))))) ⟶*
           (inr ∘ (fmap TermF-3 N ∘ (inr ∘ (inr ∘ (inr ∘ (inl ∘ payload))))))
      r2 = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' (inr ∘ (inr ∘ (inr ∘ (inl ∘ payload)))) (fmap-2-inr N)) (step assoc-r done))

      r3 : (fmap TermF-3 N ∘ (inr ∘ (inr ∘ (inr ∘ (inl ∘ payload))))) ⟶*
           (inr ∘ (fmap TermF-4 N ∘ (inr ∘ (inr ∘ (inl ∘ payload)))))
      r3 = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' (inr ∘ (inr ∘ (inl ∘ payload))) (fmap-3-inr N)) (step assoc-r done))

      r4 : (fmap TermF-4 N ∘ (inr ∘ (inr ∘ (inl ∘ payload)))) ⟶*
           (inr ∘ (fmap TermF-5 N ∘ (inr ∘ (inl ∘ payload))))
      r4 = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' (inr ∘ (inl ∘ payload)) (fmap-4-inr N)) (step assoc-r done))

      r5 : (fmap TermF-5 N ∘ (inr ∘ (inl ∘ payload))) ⟶*
           (inr ∘ (fmap TermF-6 N ∘ (inl ∘ payload)))
      r5 = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' (inl ∘ payload) (fmap-5-inr N)) (step assoc-r done))

      r6 : (fmap TermF-6 N ∘ (inl ∘ payload)) ⟶* (inl ∘ payload)
      r6 = ⟶*-trans (step assoc-l done)
             (⟶*-trans (∘-cong-left' payload (fmap-6-inl N))
               (⟶*-trans (step assoc-r done)
                 (⟶*-trans (∘-cong-right' inl
                   (⟶*-trans (∘-cong-left' payload (fmap-KK-id TyFuncCode TyFuncCode N))
                     (step id-left done)))
                   done)))

      reduce-chain : (fmap TermF N ∘ (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ payload)) ⟶* (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ payload)
      reduce-chain =
        ⟶*-trans r0 (∘-cong-right' inr
          (⟶*-trans r1 (∘-cong-right' inr
            (⟶*-trans r2 (∘-cong-right' inr
              (⟶*-trans r3 (∘-cong-right' inr
                (⟶*-trans r4 (∘-cong-right' inr
                  (⟶*-trans r5 (∘-cong-right' inr r6)))))))))))

      inner-step : (normalize-step ∘ (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ payload)) ⟶* (handle-inr ∘ payload)
      inner-step =
        ⟶*-trans (step assoc-l done)
          (⟶*-trans (step assoc-l done)
            (⟶*-trans (step assoc-l done)
              (⟶*-trans (step assoc-l done)
                (⟶*-trans (step assoc-l done)
                  (⟶*-trans (step assoc-l done)
                    (⟶*-trans (step assoc-l done)
                      (∘-cong-left' payload nstep-at-6')))))))

      step2 : ((normalize-step ∘ fmap TermF N) ∘ (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ payload)) ⟶*
              (handle-inr ∘ payload)
      step2 = ⟶*-trans (step assoc-r done)
                (⟶*-trans (∘-cong-right' normalize-step reduce-chain)
                  inner-step)

      step3 : (handle-inr ∘ payload) ⟶* ((In {TermF} ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl) ∘ payload)
      step3 = done

      step4 : ((In {TermF} ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl) ∘ payload) ⟶* (In {TermF} ∘ (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ payload))
      step4 = ⟶*-trans (step assoc-r done)
                (∘-cong-right' In
                  (⟶*-trans (step assoc-r done)
                    (∘-cong-right' inr
                      (⟶*-trans (step assoc-r done)
                        (∘-cong-right' inr
                          (⟶*-trans (step assoc-r done)
                            (∘-cong-right' inr
                              (⟶*-trans (step assoc-r done)
                                (∘-cong-right' inr
                                  (⟶*-trans (step assoc-r done)
                                    (∘-cong-right' inr (step assoc-r done))))))))))))

  -- Position 8 (terminal): encode terminal = In ∘ inr^8 ∘ inl ∘ ⌜A⌝
  noredex-fixpoint-terminal : ∀ {A} → (normalize ∘ encode (terminal {A})) ⟶* encode (terminal {A})
  noredex-fixpoint-terminal {A} = ⟶*-trans step1 (⟶*-trans step2 (⟶*-trans step3 step4))
    where
      N : Term TermCode' TermCode'
      N = cata TermF normalize-step

      payload : Term Unit TyFuncCode
      payload = ⌜ A ⌝Ty

      step1 : (N ∘ (In {TermF} ∘ (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ payload))) ⟶*
              ((normalize-step ∘ fmap TermF N) ∘ (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ payload))
      step1 = cata-β-right {TermF} {TermCode'} {Unit} {normalize-step} {inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ payload}

      r0 : (fmap TermF N ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inl ∘ payload)))))))))) ⟶*
           (inr ∘ (fmap TermF-1 N ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inl ∘ payload))))))))))
      r0 = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inl ∘ payload)))))))) (fmap-TermF-inr N)) (step assoc-r done))

      r1 : (fmap TermF-1 N ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inl ∘ payload))))))))) ⟶*
           (inr ∘ (fmap TermF-2 N ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inl ∘ payload)))))))))
      r1 = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inl ∘ payload))))))) (fmap-1-inr N)) (step assoc-r done))

      r2 : (fmap TermF-2 N ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inl ∘ payload)))))))) ⟶*
           (inr ∘ (fmap TermF-3 N ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inl ∘ payload))))))))
      r2 = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inl ∘ payload)))))) (fmap-2-inr N)) (step assoc-r done))

      r3 : (fmap TermF-3 N ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inl ∘ payload))))))) ⟶*
           (inr ∘ (fmap TermF-4 N ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inl ∘ payload)))))))
      r3 = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inl ∘ payload))))) (fmap-3-inr N)) (step assoc-r done))

      r4 : (fmap TermF-4 N ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inl ∘ payload)))))) ⟶*
           (inr ∘ (fmap TermF-5 N ∘ (inr ∘ (inr ∘ (inr ∘ (inl ∘ payload))))))
      r4 = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' (inr ∘ (inr ∘ (inr ∘ (inl ∘ payload)))) (fmap-4-inr N)) (step assoc-r done))

      r5 : (fmap TermF-5 N ∘ (inr ∘ (inr ∘ (inr ∘ (inl ∘ payload))))) ⟶*
           (inr ∘ (fmap TermF-6 N ∘ (inr ∘ (inr ∘ (inl ∘ payload)))))
      r5 = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' (inr ∘ (inr ∘ (inl ∘ payload))) (fmap-5-inr N)) (step assoc-r done))

      r6 : (fmap TermF-6 N ∘ (inr ∘ (inr ∘ (inl ∘ payload)))) ⟶*
           (inr ∘ (fmap TermF-7 N ∘ (inr ∘ (inl ∘ payload))))
      r6 = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' (inr ∘ (inl ∘ payload)) (fmap-6-inr N)) (step assoc-r done))

      r7 : (fmap TermF-7 N ∘ (inr ∘ (inl ∘ payload))) ⟶*
           (inr ∘ (fmap TermF-8 N ∘ (inl ∘ payload)))
      r7 = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' (inl ∘ payload) (fmap-7-inr N)) (step assoc-r done))

      r8 : (fmap TermF-8 N ∘ (inl ∘ payload)) ⟶* (inl ∘ payload)
      r8 = ⟶*-trans (step assoc-l done)
             (⟶*-trans (∘-cong-left' payload (fmap-8-inl N))
               (⟶*-trans (∘-cong-left' payload (step id-right done))
                 done))

      reduce-chain : (fmap TermF N ∘ (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ payload)) ⟶* (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ payload)
      reduce-chain =
        ⟶*-trans r0 (∘-cong-right' inr
          (⟶*-trans r1 (∘-cong-right' inr
            (⟶*-trans r2 (∘-cong-right' inr
              (⟶*-trans r3 (∘-cong-right' inr
                (⟶*-trans r4 (∘-cong-right' inr
                  (⟶*-trans r5 (∘-cong-right' inr
                    (⟶*-trans r6 (∘-cong-right' inr
                      (⟶*-trans r7 (∘-cong-right' inr r8)))))))))))))))

      inner-step : (normalize-step ∘ (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ payload)) ⟶* (handle-terminal ∘ payload)
      inner-step =
        ⟶*-trans (step assoc-l done)
          (⟶*-trans (step assoc-l done)
            (⟶*-trans (step assoc-l done)
              (⟶*-trans (step assoc-l done)
                (⟶*-trans (step assoc-l done)
                  (⟶*-trans (step assoc-l done)
                    (⟶*-trans (step assoc-l done)
                      (⟶*-trans (step assoc-l done)
                        (⟶*-trans (step assoc-l done)
                          (∘-cong-left' payload nstep-at-8')))))))))

      step2 : ((normalize-step ∘ fmap TermF N) ∘ (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ payload)) ⟶*
              (handle-terminal ∘ payload)
      step2 = ⟶*-trans (step assoc-r done)
                (⟶*-trans (∘-cong-right' normalize-step reduce-chain)
                  inner-step)

      step3 : (handle-terminal ∘ payload) ⟶* ((In {TermF} ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl) ∘ payload)
      step3 = done

      step4 : ((In {TermF} ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl) ∘ payload) ⟶* (In {TermF} ∘ (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ payload))
      step4 = ⟶*-trans (step assoc-r done)
                (∘-cong-right' In
                  (⟶*-trans (step assoc-r done)
                    (∘-cong-right' inr
                      (⟶*-trans (step assoc-r done)
                        (∘-cong-right' inr
                          (⟶*-trans (step assoc-r done)
                            (∘-cong-right' inr
                              (⟶*-trans (step assoc-r done)
                                (∘-cong-right' inr
                                  (⟶*-trans (step assoc-r done)
                                    (∘-cong-right' inr
                                      (⟶*-trans (step assoc-r done)
                                        (∘-cong-right' inr
                                          (⟶*-trans (step assoc-r done)
                                            (∘-cong-right' inr (step assoc-r done))))))))))))))))

  -- Position 9 (In): encode In = In ∘ inr^9 ∘ inl ∘ ⌜F⌝
  noredex-fixpoint-In' : ∀ {F} → (normalize ∘ encode (In {F})) ⟶* encode (In {F})
  noredex-fixpoint-In' {F} = ⟶*-trans step1 (⟶*-trans step2 (⟶*-trans step3 step4))
    where
      N : Term TermCode' TermCode'
      N = cata TermF normalize-step

      payload : Term Unit TyFuncCode
      payload = ⌜ F ⌝Func

      step1 : (N ∘ (In {TermF} ∘ (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ payload))) ⟶*
              ((normalize-step ∘ fmap TermF N) ∘ (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ payload))
      step1 = cata-β-right {TermF} {TermCode'} {Unit} {normalize-step} {inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ payload}

      r0 : (fmap TermF N ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inl ∘ payload))))))))))) ⟶*
           (inr ∘ (fmap TermF-1 N ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inl ∘ payload)))))))))))
      r0 = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inl ∘ payload))))))))) (fmap-TermF-inr N)) (step assoc-r done))

      r1 : (fmap TermF-1 N ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inl ∘ payload)))))))))) ⟶*
           (inr ∘ (fmap TermF-2 N ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inl ∘ payload))))))))))
      r1 = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inl ∘ payload)))))))) (fmap-1-inr N)) (step assoc-r done))

      r2 : (fmap TermF-2 N ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inl ∘ payload))))))))) ⟶*
           (inr ∘ (fmap TermF-3 N ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inl ∘ payload)))))))))
      r2 = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inl ∘ payload))))))) (fmap-2-inr N)) (step assoc-r done))

      r3 : (fmap TermF-3 N ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inl ∘ payload)))))))) ⟶*
           (inr ∘ (fmap TermF-4 N ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inl ∘ payload))))))))
      r3 = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inl ∘ payload)))))) (fmap-3-inr N)) (step assoc-r done))

      r4 : (fmap TermF-4 N ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inl ∘ payload))))))) ⟶*
           (inr ∘ (fmap TermF-5 N ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inl ∘ payload)))))))
      r4 = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inl ∘ payload))))) (fmap-4-inr N)) (step assoc-r done))

      r5 : (fmap TermF-5 N ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inl ∘ payload)))))) ⟶*
           (inr ∘ (fmap TermF-6 N ∘ (inr ∘ (inr ∘ (inr ∘ (inl ∘ payload))))))
      r5 = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' (inr ∘ (inr ∘ (inr ∘ (inl ∘ payload)))) (fmap-5-inr N)) (step assoc-r done))

      r6 : (fmap TermF-6 N ∘ (inr ∘ (inr ∘ (inr ∘ (inl ∘ payload))))) ⟶*
           (inr ∘ (fmap TermF-7 N ∘ (inr ∘ (inr ∘ (inl ∘ payload)))))
      r6 = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' (inr ∘ (inr ∘ (inl ∘ payload))) (fmap-6-inr N)) (step assoc-r done))

      r7 : (fmap TermF-7 N ∘ (inr ∘ (inr ∘ (inl ∘ payload)))) ⟶*
           (inr ∘ (fmap TermF-8 N ∘ (inr ∘ (inl ∘ payload))))
      r7 = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' (inr ∘ (inl ∘ payload)) (fmap-7-inr N)) (step assoc-r done))

      r8 : (fmap TermF-8 N ∘ (inr ∘ (inl ∘ payload))) ⟶*
           (inr ∘ (fmap TermF-9 N ∘ (inl ∘ payload)))
      r8 = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' (inl ∘ payload) (fmap-8-inr N)) (step assoc-r done))

      r9 : (fmap TermF-9 N ∘ (inl ∘ payload)) ⟶* (inl ∘ payload)
      r9 = ⟶*-trans (step assoc-l done)
             (⟶*-trans (∘-cong-left' payload (fmap-9-inl N))
               (⟶*-trans (∘-cong-left' payload (step id-right done))
                 done))

      reduce-chain : (fmap TermF N ∘ (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ payload)) ⟶* (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ payload)
      reduce-chain =
        ⟶*-trans r0 (∘-cong-right' inr
          (⟶*-trans r1 (∘-cong-right' inr
            (⟶*-trans r2 (∘-cong-right' inr
              (⟶*-trans r3 (∘-cong-right' inr
                (⟶*-trans r4 (∘-cong-right' inr
                  (⟶*-trans r5 (∘-cong-right' inr
                    (⟶*-trans r6 (∘-cong-right' inr
                      (⟶*-trans r7 (∘-cong-right' inr
                        (⟶*-trans r8 (∘-cong-right' inr r9)))))))))))))))))

      inner-step : (normalize-step ∘ (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ payload)) ⟶* (handle-In ∘ payload)
      inner-step =
        ⟶*-trans (step assoc-l done)
          (⟶*-trans (step assoc-l done)
            (⟶*-trans (step assoc-l done)
              (⟶*-trans (step assoc-l done)
                (⟶*-trans (step assoc-l done)
                  (⟶*-trans (step assoc-l done)
                    (⟶*-trans (step assoc-l done)
                      (⟶*-trans (step assoc-l done)
                        (⟶*-trans (step assoc-l done)
                          (⟶*-trans (step assoc-l done)
                            (∘-cong-left' payload nstep-at-9'))))))))))

      step2 : ((normalize-step ∘ fmap TermF N) ∘ (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ payload)) ⟶*
              (handle-In ∘ payload)
      step2 = ⟶*-trans (step assoc-r done)
                (⟶*-trans (∘-cong-right' normalize-step reduce-chain)
                  inner-step)

      step3 : (handle-In ∘ payload) ⟶* ((In {TermF} ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl) ∘ payload)
      step3 = done

      step4 : ((In {TermF} ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl) ∘ payload) ⟶* (In {TermF} ∘ (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ payload))
      step4 = ⟶*-trans (step assoc-r done)
                (∘-cong-right' In
                  (⟶*-trans (step assoc-r done)
                    (∘-cong-right' inr
                      (⟶*-trans (step assoc-r done)
                        (∘-cong-right' inr
                          (⟶*-trans (step assoc-r done)
                            (∘-cong-right' inr
                              (⟶*-trans (step assoc-r done)
                                (∘-cong-right' inr
                                  (⟶*-trans (step assoc-r done)
                                    (∘-cong-right' inr
                                      (⟶*-trans (step assoc-r done)
                                        (∘-cong-right' inr
                                          (⟶*-trans (step assoc-r done)
                                            (∘-cong-right' inr
                                              (⟶*-trans (step assoc-r done)
                                                (∘-cong-right' inr (step assoc-r done))))))))))))))))))

  -- Position 10 (Out): encode Out = In ∘ inr^10 ∘ inl ∘ ⌜F⌝
  noredex-fixpoint-Out : ∀ {F} → (normalize ∘ encode (Out {F})) ⟶* encode (Out {F})
  noredex-fixpoint-Out {F} = ⟶*-trans step1 (⟶*-trans step2 (⟶*-trans step3 step4))
    where
      N : Term TermCode' TermCode'
      N = cata TermF normalize-step

      payload : Term Unit TyFuncCode
      payload = ⌜ F ⌝Func

      step1 : (N ∘ (In {TermF} ∘ (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ payload))) ⟶*
              ((normalize-step ∘ fmap TermF N) ∘ (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ payload))
      step1 = cata-β-right {TermF} {TermCode'} {Unit} {normalize-step} {inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ payload}

      r0 : (fmap TermF N ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inl ∘ payload)))))))))))) ⟶*
           (inr ∘ (fmap TermF-1 N ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inl ∘ payload))))))))))))
      r0 = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inl ∘ payload)))))))))) (fmap-TermF-inr N)) (step assoc-r done))

      r1 : (fmap TermF-1 N ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inl ∘ payload))))))))))) ⟶*
           (inr ∘ (fmap TermF-2 N ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inl ∘ payload)))))))))))
      r1 = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inl ∘ payload))))))))) (fmap-1-inr N)) (step assoc-r done))

      r2 : (fmap TermF-2 N ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inl ∘ payload)))))))))) ⟶*
           (inr ∘ (fmap TermF-3 N ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inl ∘ payload))))))))))
      r2 = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inl ∘ payload)))))))) (fmap-2-inr N)) (step assoc-r done))

      r3 : (fmap TermF-3 N ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inl ∘ payload))))))))) ⟶*
           (inr ∘ (fmap TermF-4 N ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inl ∘ payload)))))))))
      r3 = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inl ∘ payload))))))) (fmap-3-inr N)) (step assoc-r done))

      r4 : (fmap TermF-4 N ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inl ∘ payload)))))))) ⟶*
           (inr ∘ (fmap TermF-5 N ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inl ∘ payload))))))))
      r4 = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inl ∘ payload)))))) (fmap-4-inr N)) (step assoc-r done))

      r5 : (fmap TermF-5 N ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inl ∘ payload))))))) ⟶*
           (inr ∘ (fmap TermF-6 N ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inl ∘ payload)))))))
      r5 = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inl ∘ payload))))) (fmap-5-inr N)) (step assoc-r done))

      r6 : (fmap TermF-6 N ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inl ∘ payload)))))) ⟶*
           (inr ∘ (fmap TermF-7 N ∘ (inr ∘ (inr ∘ (inr ∘ (inl ∘ payload))))))
      r6 = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' (inr ∘ (inr ∘ (inr ∘ (inl ∘ payload)))) (fmap-6-inr N)) (step assoc-r done))

      r7 : (fmap TermF-7 N ∘ (inr ∘ (inr ∘ (inr ∘ (inl ∘ payload))))) ⟶*
           (inr ∘ (fmap TermF-8 N ∘ (inr ∘ (inr ∘ (inl ∘ payload)))))
      r7 = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' (inr ∘ (inr ∘ (inl ∘ payload))) (fmap-7-inr N)) (step assoc-r done))

      r8 : (fmap TermF-8 N ∘ (inr ∘ (inr ∘ (inl ∘ payload)))) ⟶*
           (inr ∘ (fmap TermF-9 N ∘ (inr ∘ (inl ∘ payload))))
      r8 = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' (inr ∘ (inl ∘ payload)) (fmap-8-inr N)) (step assoc-r done))

      r9 : (fmap TermF-9 N ∘ (inr ∘ (inl ∘ payload))) ⟶*
           (inr ∘ (fmap TermF-10 N ∘ (inl ∘ payload)))
      r9 = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' (inl ∘ payload) (fmap-9-inr N)) (step assoc-r done))

      r10 : (fmap TermF-10 N ∘ (inl ∘ payload)) ⟶* (inl ∘ payload)
      r10 = ⟶*-trans (step assoc-l done)
              (⟶*-trans (∘-cong-left' payload (fmap-10-inl N))
                (⟶*-trans (∘-cong-left' payload (step id-right done))
                  done))

      reduce-chain : (fmap TermF N ∘ (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ payload)) ⟶* (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ payload)
      reduce-chain =
        ⟶*-trans r0 (∘-cong-right' inr
          (⟶*-trans r1 (∘-cong-right' inr
            (⟶*-trans r2 (∘-cong-right' inr
              (⟶*-trans r3 (∘-cong-right' inr
                (⟶*-trans r4 (∘-cong-right' inr
                  (⟶*-trans r5 (∘-cong-right' inr
                    (⟶*-trans r6 (∘-cong-right' inr
                      (⟶*-trans r7 (∘-cong-right' inr
                        (⟶*-trans r8 (∘-cong-right' inr
                          (⟶*-trans r9 (∘-cong-right' inr r10)))))))))))))))))))

      inner-step : (normalize-step ∘ (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ payload)) ⟶* (handle-Out ∘ payload)
      inner-step =
        ⟶*-trans (step assoc-l done)
          (⟶*-trans (step assoc-l done)
            (⟶*-trans (step assoc-l done)
              (⟶*-trans (step assoc-l done)
                (⟶*-trans (step assoc-l done)
                  (⟶*-trans (step assoc-l done)
                    (⟶*-trans (step assoc-l done)
                      (⟶*-trans (step assoc-l done)
                        (⟶*-trans (step assoc-l done)
                          (⟶*-trans (step assoc-l done)
                            (⟶*-trans (step assoc-l done)
                              (∘-cong-left' payload nstep-at-10')))))))))))

      step2 : ((normalize-step ∘ fmap TermF N) ∘ (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ payload)) ⟶*
              (handle-Out ∘ payload)
      step2 = ⟶*-trans (step assoc-r done)
                (⟶*-trans (∘-cong-right' normalize-step reduce-chain)
                  inner-step)

      step3 : (handle-Out ∘ payload) ⟶* ((In {TermF} ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl) ∘ payload)
      step3 = done

      step4 : ((In {TermF} ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl) ∘ payload) ⟶* (In {TermF} ∘ (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ payload))
      step4 = ⟶*-trans (step assoc-r done)
                (∘-cong-right' In
                  (⟶*-trans (step assoc-r done)
                    (∘-cong-right' inr
                      (⟶*-trans (step assoc-r done)
                        (∘-cong-right' inr
                          (⟶*-trans (step assoc-r done)
                            (∘-cong-right' inr
                              (⟶*-trans (step assoc-r done)
                                (∘-cong-right' inr
                                  (⟶*-trans (step assoc-r done)
                                    (∘-cong-right' inr
                                      (⟶*-trans (step assoc-r done)
                                        (∘-cong-right' inr
                                          (⟶*-trans (step assoc-r done)
                                            (∘-cong-right' inr
                                              (⟶*-trans (step assoc-r done)
                                                (∘-cong-right' inr
                                                  (⟶*-trans (step assoc-r done)
                                                    (∘-cong-right' inr (step assoc-r done))))))))))))))))))))

  -- Position 13 (apply): encode apply = In ∘ inr^13 ∘ ⟨⌜A⌝, ⌜B⌝⟩  (no inl!)
  noredex-fixpoint-apply : ∀ {A B} → (normalize ∘ encode (apply {A} {B})) ⟶* encode (apply {A} {B})
  noredex-fixpoint-apply {A} {B} = ⟶*-trans step1 (⟶*-trans step2 (⟶*-trans step3 step4))
    where
      N : Term TermCode' TermCode'
      N = cata TermF normalize-step

      payload : Term Unit (TyFuncCode * TyFuncCode)
      payload = ⟨ ⌜ A ⌝Ty , ⌜ B ⌝Ty ⟩

      step1 : (N ∘ (In {TermF} ∘ (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ payload))) ⟶*
              ((normalize-step ∘ fmap TermF N) ∘ (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ payload))
      step1 = cata-β-right {TermF} {TermCode'} {Unit} {normalize-step} {inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ payload}

      r0 : (fmap TermF N ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ payload)))))))))))))) ⟶*
           (inr ∘ (fmap TermF-1 N ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ payload))))))))))))))
      r0 = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ payload)))))))))))) (fmap-TermF-inr N)) (step assoc-r done))

      r1 : (fmap TermF-1 N ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ payload))))))))))))) ⟶*
           (inr ∘ (fmap TermF-2 N ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ payload)))))))))))))
      r1 = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ payload))))))))))) (fmap-1-inr N)) (step assoc-r done))

      r2 : (fmap TermF-2 N ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ payload)))))))))))) ⟶*
           (inr ∘ (fmap TermF-3 N ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ payload))))))))))))
      r2 = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ payload)))))))))) (fmap-2-inr N)) (step assoc-r done))

      r3 : (fmap TermF-3 N ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ payload))))))))))) ⟶*
           (inr ∘ (fmap TermF-4 N ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ payload)))))))))))
      r3 = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ payload))))))))) (fmap-3-inr N)) (step assoc-r done))

      r4 : (fmap TermF-4 N ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ payload)))))))))) ⟶*
           (inr ∘ (fmap TermF-5 N ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ payload))))))))))
      r4 = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ payload)))))))) (fmap-4-inr N)) (step assoc-r done))

      r5 : (fmap TermF-5 N ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ payload))))))))) ⟶*
           (inr ∘ (fmap TermF-6 N ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ payload)))))))))
      r5 = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ payload))))))) (fmap-5-inr N)) (step assoc-r done))

      r6 : (fmap TermF-6 N ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ payload)))))))) ⟶*
           (inr ∘ (fmap TermF-7 N ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ payload))))))))
      r6 = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ payload)))))) (fmap-6-inr N)) (step assoc-r done))

      r7 : (fmap TermF-7 N ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ payload))))))) ⟶*
           (inr ∘ (fmap TermF-8 N ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ payload)))))))
      r7 = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ payload))))) (fmap-7-inr N)) (step assoc-r done))

      r8 : (fmap TermF-8 N ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ payload)))))) ⟶*
           (inr ∘ (fmap TermF-9 N ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ payload))))))
      r8 = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' (inr ∘ (inr ∘ (inr ∘ (inr ∘ payload)))) (fmap-8-inr N)) (step assoc-r done))

      r9 : (fmap TermF-9 N ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ payload))))) ⟶*
           (inr ∘ (fmap TermF-10 N ∘ (inr ∘ (inr ∘ (inr ∘ payload)))))
      r9 = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' (inr ∘ (inr ∘ (inr ∘ payload))) (fmap-9-inr N)) (step assoc-r done))

      r10 : (fmap TermF-10 N ∘ (inr ∘ (inr ∘ (inr ∘ payload)))) ⟶*
            (inr ∘ (fmap TermF-11 N ∘ (inr ∘ (inr ∘ payload))))
      r10 = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' (inr ∘ (inr ∘ payload)) (fmap-10-inr N)) (step assoc-r done))

      r11 : (fmap TermF-11 N ∘ (inr ∘ (inr ∘ payload))) ⟶*
            (inr ∘ (fmap TermF-12 N ∘ (inr ∘ payload)))
      r11 = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' (inr ∘ payload) (fmap-11-inr N)) (step assoc-r done))

      r12 : (fmap TermF-12 N ∘ (inr ∘ payload)) ⟶*
            (inr ∘ (fmap (K TyFuncCode ⊗ K TyFuncCode) N ∘ payload))
      r12 = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' payload (fmap-12-inr N)) (step assoc-r done))

      r13 : (fmap (K TyFuncCode ⊗ K TyFuncCode) N ∘ payload) ⟶* payload
      r13 = ⟶*-trans (∘-cong-left' payload (fmap-KK-id TyFuncCode TyFuncCode N)) (step id-left done)

      reduce-chain : (fmap TermF N ∘ (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ payload)) ⟶* (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ payload)
      reduce-chain =
        ⟶*-trans r0 (∘-cong-right' inr
          (⟶*-trans r1 (∘-cong-right' inr
            (⟶*-trans r2 (∘-cong-right' inr
              (⟶*-trans r3 (∘-cong-right' inr
                (⟶*-trans r4 (∘-cong-right' inr
                  (⟶*-trans r5 (∘-cong-right' inr
                    (⟶*-trans r6 (∘-cong-right' inr
                      (⟶*-trans r7 (∘-cong-right' inr
                        (⟶*-trans r8 (∘-cong-right' inr
                          (⟶*-trans r9 (∘-cong-right' inr
                            (⟶*-trans r10 (∘-cong-right' inr
                              (⟶*-trans r11 (∘-cong-right' inr
                                (⟶*-trans r12 (∘-cong-right' inr r13)))))))))))))))))))))))))

      inner-step : (normalize-step ∘ (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ payload)) ⟶* (handle-apply ∘ payload)
      inner-step =
        ⟶*-trans (step assoc-l done)
          (⟶*-trans (step assoc-l done)
            (⟶*-trans (step assoc-l done)
              (⟶*-trans (step assoc-l done)
                (⟶*-trans (step assoc-l done)
                  (⟶*-trans (step assoc-l done)
                    (⟶*-trans (step assoc-l done)
                      (⟶*-trans (step assoc-l done)
                        (⟶*-trans (step assoc-l done)
                          (⟶*-trans (step assoc-l done)
                            (⟶*-trans (step assoc-l done)
                              (⟶*-trans (step assoc-l done)
                                (⟶*-trans (step assoc-l done)
                                  (∘-cong-left' payload nstep-at-13')))))))))))))

      step2 : ((normalize-step ∘ fmap TermF N) ∘ (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ payload)) ⟶*
              (handle-apply ∘ payload)
      step2 = ⟶*-trans (step assoc-r done)
                (⟶*-trans (∘-cong-right' normalize-step reduce-chain)
                  inner-step)

      step3 : (handle-apply ∘ payload) ⟶* ((In {TermF} ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr) ∘ payload)
      step3 = done

      step4 : ((In {TermF} ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr) ∘ payload) ⟶* (In {TermF} ∘ (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ payload))
      step4 = ⟶*-trans (step assoc-r done)
                (∘-cong-right' In
                  (⟶*-trans (step assoc-r done)
                    (∘-cong-right' inr
                      (⟶*-trans (step assoc-r done)
                        (∘-cong-right' inr
                          (⟶*-trans (step assoc-r done)
                            (∘-cong-right' inr
                              (⟶*-trans (step assoc-r done)
                                (∘-cong-right' inr
                                  (⟶*-trans (step assoc-r done)
                                    (∘-cong-right' inr
                                      (⟶*-trans (step assoc-r done)
                                        (∘-cong-right' inr
                                          (⟶*-trans (step assoc-r done)
                                            (∘-cong-right' inr
                                              (⟶*-trans (step assoc-r done)
                                                (∘-cong-right' inr
                                                  (⟶*-trans (step assoc-r done)
                                                    (∘-cong-right' inr
                                                      (⟶*-trans (step assoc-r done)
                                                        (∘-cong-right' inr
                                                          (⟶*-trans (step assoc-r done)
                                                            (∘-cong-right' inr (step assoc-r done))))))))))))))))))))))))

  -- Main fixpoint theorem (by structural induction on NoRedex)
  noredex-fixpoint : ∀ {A B} (t : Term A B) →
                     NoRedex t →
                     (normalize ∘ encode t) ⟶* encode t
  noredex-fixpoint id nr-id = noredex-fixpoint-id
  noredex-fixpoint fst nr-fst = noredex-fixpoint-fst
  noredex-fixpoint snd nr-snd = noredex-fixpoint-snd
  noredex-fixpoint inl nr-inl = noredex-fixpoint-inl
  noredex-fixpoint inr nr-inr = noredex-fixpoint-inr
  noredex-fixpoint terminal nr-terminal = noredex-fixpoint-terminal
  noredex-fixpoint In nr-In = noredex-fixpoint-In'
  noredex-fixpoint Out nr-Out = noredex-fixpoint-Out
  noredex-fixpoint apply nr-apply = noredex-fixpoint-apply
  -- Compound terms with Id⊗Id payload (pair, case) - simple rebuilds

  -- Position 4 (pair): encode ⟨f,g⟩ = In ∘ inr^4 ∘ inl ∘ ⟨encode f, encode g⟩
  noredex-fixpoint ⟨ f , g ⟩ (nr-pair nrf nrg) = ⟶*-trans step1 (⟶*-trans step2 (⟶*-trans step3 step4))
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
      r0 = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' (inr ∘ (inr ∘ (inr ∘ (inl ∘ payload)))) (fmap-TermF-inr N)) (step assoc-r done))

      r1 : (fmap TermF-1 N ∘ (inr ∘ (inr ∘ (inr ∘ (inl ∘ payload))))) ⟶*
           (inr ∘ (fmap TermF-2 N ∘ (inr ∘ (inr ∘ (inl ∘ payload)))))
      r1 = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' (inr ∘ (inr ∘ (inl ∘ payload))) (fmap-1-inr N)) (step assoc-r done))

      r2 : (fmap TermF-2 N ∘ (inr ∘ (inr ∘ (inl ∘ payload)))) ⟶*
           (inr ∘ (fmap TermF-3 N ∘ (inr ∘ (inl ∘ payload))))
      r2 = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' (inr ∘ (inl ∘ payload)) (fmap-2-inr N)) (step assoc-r done))

      r3 : (fmap TermF-3 N ∘ (inr ∘ (inl ∘ payload))) ⟶*
           (inr ∘ (fmap TermF-4 N ∘ (inl ∘ payload)))
      r3 = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' (inl ∘ payload) (fmap-3-inr N)) (step assoc-r done))

      -- Position 4 payload functor: Id ⊗ Id
      -- fmap (Id ⊗ Id) N ∘ payload ⟶* payload via IH
      ih-step : (fmap (Id ⊗ Id) N ∘ payload) ⟶* payload
      ih-step =
        ⟶*-trans (step pair-comp done)
          (⟨⟩-cong
            (⟶*-trans (step assoc-r done)
              (⟶*-trans (∘-cong-right' N (step fst-pair done))
                (noredex-fixpoint f nrf)))
            (⟶*-trans (step assoc-r done)
              (⟶*-trans (∘-cong-right' N (step snd-pair done))
                (noredex-fixpoint g nrg))))

      r4 : (fmap TermF-4 N ∘ (inl ∘ payload)) ⟶* (inl ∘ payload)
      r4 = ⟶*-trans (step assoc-l done)
             (⟶*-trans (∘-cong-left' payload (fmap-4-inl N))
               (⟶*-trans (step assoc-r done)
                 (∘-cong-right' inl ih-step)))

      reduce-chain : (fmap TermF N ∘ (inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ payload)) ⟶* (inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ payload)
      reduce-chain =
        ⟶*-trans r0 (∘-cong-right' inr
          (⟶*-trans r1 (∘-cong-right' inr
            (⟶*-trans r2 (∘-cong-right' inr
              (⟶*-trans r3 (∘-cong-right' inr r4)))))))

      inner-step : (normalize-step ∘ (inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ payload)) ⟶* (handle-pair ∘ payload)
      inner-step =
        ⟶*-trans (step assoc-l done)
          (⟶*-trans (step assoc-l done)
            (⟶*-trans (step assoc-l done)
              (⟶*-trans (step assoc-l done)
                (⟶*-trans (step assoc-l done)
                  (∘-cong-left' payload nstep-at-4')))))

      step2 : ((normalize-step ∘ fmap TermF N) ∘ (inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ payload)) ⟶*
              (handle-pair ∘ payload)
      step2 = ⟶*-trans (step assoc-r done)
                (⟶*-trans (∘-cong-right' normalize-step reduce-chain)
                  inner-step)

      -- handle-pair = rebuild-4 = In ∘ inr^4 ∘ inl (definitional equality)
      step3 : (handle-pair ∘ payload) ⟶* ((In {TermF} ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl) ∘ payload)
      step3 = done

      step4 : ((In {TermF} ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl) ∘ payload) ⟶* (In {TermF} ∘ (inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ payload))
      step4 = ⟶*-trans (step assoc-r done)
                (∘-cong-right' In
                  (⟶*-trans (step assoc-r done)
                    (∘-cong-right' inr
                      (⟶*-trans (step assoc-r done)
                        (∘-cong-right' inr
                          (⟶*-trans (step assoc-r done)
                            (∘-cong-right' inr (step assoc-r done))))))))

  -- Position 7 (case): encode [f,g] = In ∘ inr^7 ∘ inl ∘ ⟨encode f, encode g⟩
  noredex-fixpoint [ f , g ] (nr-case nrf nrg) = ⟶*-trans step1 (⟶*-trans step2 (⟶*-trans step3 step4))
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
      r0 = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inl ∘ payload))))))) (fmap-TermF-inr N)) (step assoc-r done))

      r1 : (fmap TermF-1 N ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inl ∘ payload)))))))) ⟶*
           (inr ∘ (fmap TermF-2 N ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inl ∘ payload))))))))
      r1 = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inl ∘ payload)))))) (fmap-1-inr N)) (step assoc-r done))

      r2 : (fmap TermF-2 N ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inl ∘ payload))))))) ⟶*
           (inr ∘ (fmap TermF-3 N ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inl ∘ payload)))))))
      r2 = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inl ∘ payload))))) (fmap-2-inr N)) (step assoc-r done))

      r3 : (fmap TermF-3 N ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inl ∘ payload)))))) ⟶*
           (inr ∘ (fmap TermF-4 N ∘ (inr ∘ (inr ∘ (inr ∘ (inl ∘ payload))))))
      r3 = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' (inr ∘ (inr ∘ (inr ∘ (inl ∘ payload)))) (fmap-3-inr N)) (step assoc-r done))

      r4 : (fmap TermF-4 N ∘ (inr ∘ (inr ∘ (inr ∘ (inl ∘ payload))))) ⟶*
           (inr ∘ (fmap TermF-5 N ∘ (inr ∘ (inr ∘ (inl ∘ payload)))))
      r4 = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' (inr ∘ (inr ∘ (inl ∘ payload))) (fmap-4-inr N)) (step assoc-r done))

      r5 : (fmap TermF-5 N ∘ (inr ∘ (inr ∘ (inl ∘ payload)))) ⟶*
           (inr ∘ (fmap TermF-6 N ∘ (inr ∘ (inl ∘ payload))))
      r5 = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' (inr ∘ (inl ∘ payload)) (fmap-5-inr N)) (step assoc-r done))

      r6 : (fmap TermF-6 N ∘ (inr ∘ (inl ∘ payload))) ⟶*
           (inr ∘ (fmap TermF-7 N ∘ (inl ∘ payload)))
      r6 = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' (inl ∘ payload) (fmap-6-inr N)) (step assoc-r done))

      -- Position 7 payload functor: Id ⊗ Id
      ih-step : (fmap (Id ⊗ Id) N ∘ payload) ⟶* payload
      ih-step =
        ⟶*-trans (step pair-comp done)
          (⟨⟩-cong
            (⟶*-trans (step assoc-r done)
              (⟶*-trans (∘-cong-right' N (step fst-pair done))
                (noredex-fixpoint f nrf)))
            (⟶*-trans (step assoc-r done)
              (⟶*-trans (∘-cong-right' N (step snd-pair done))
                (noredex-fixpoint g nrg))))

      r7 : (fmap TermF-7 N ∘ (inl ∘ payload)) ⟶* (inl ∘ payload)
      r7 = ⟶*-trans (step assoc-l done)
             (⟶*-trans (∘-cong-left' payload (fmap-7-inl N))
               (⟶*-trans (step assoc-r done)
                 (∘-cong-right' inl ih-step)))

      reduce-chain : (fmap TermF N ∘ (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ payload)) ⟶* (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ payload)
      reduce-chain =
        ⟶*-trans r0 (∘-cong-right' inr
          (⟶*-trans r1 (∘-cong-right' inr
            (⟶*-trans r2 (∘-cong-right' inr
              (⟶*-trans r3 (∘-cong-right' inr
                (⟶*-trans r4 (∘-cong-right' inr
                  (⟶*-trans r5 (∘-cong-right' inr
                    (⟶*-trans r6 (∘-cong-right' inr r7)))))))))))))

      inner-step : (normalize-step ∘ (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ payload)) ⟶* (handle-case ∘ payload)
      inner-step =
        ⟶*-trans (step assoc-l done)
          (⟶*-trans (step assoc-l done)
            (⟶*-trans (step assoc-l done)
              (⟶*-trans (step assoc-l done)
                (⟶*-trans (step assoc-l done)
                  (⟶*-trans (step assoc-l done)
                    (⟶*-trans (step assoc-l done)
                      (⟶*-trans (step assoc-l done)
                        (∘-cong-left' payload nstep-at-7'))))))))

      step2 : ((normalize-step ∘ fmap TermF N) ∘ (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ payload)) ⟶*
              (handle-case ∘ payload)
      step2 = ⟶*-trans (step assoc-r done)
                (⟶*-trans (∘-cong-right' normalize-step reduce-chain)
                  inner-step)

      step3 : (handle-case ∘ payload) ⟶* ((In {TermF} ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl) ∘ payload)
      step3 = done

      step4 : ((In {TermF} ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl) ∘ payload) ⟶* (In {TermF} ∘ (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ payload))
      step4 = ⟶*-trans (step assoc-r done)
                (∘-cong-right' In
                  (⟶*-trans (step assoc-r done)
                    (∘-cong-right' inr
                      (⟶*-trans (step assoc-r done)
                        (∘-cong-right' inr
                          (⟶*-trans (step assoc-r done)
                            (∘-cong-right' inr
                              (⟶*-trans (step assoc-r done)
                                (∘-cong-right' inr
                                  (⟶*-trans (step assoc-r done)
                                    (∘-cong-right' inr
                                      (⟶*-trans (step assoc-r done)
                                        (∘-cong-right' inr (step assoc-r done))))))))))))))

  -- Position 12 (curry): encode (curry f) = In ∘ inr^12 ∘ inl ∘ ⟨⟨⌜A⌝,⌜B⌝⟩, ⟨⌜C⌝, encode f⟩⟩
  -- Payload functor: CurryF = (K⊗K) ⊗ (K⊗Id)
  noredex-fixpoint (curry {A} {B} {C} f) (nr-curry nrf) = ⟶*-trans step1 (⟶*-trans step2 (⟶*-trans step3 step4))
    where
      N : Term TermCode' TermCode'
      N = cata TermF normalize-step

      payload : Term Unit ((TyFuncCode * TyFuncCode) * (TyFuncCode * TermCode'))
      payload = ⟨ ⟨ ⌜ A ⌝Ty , ⌜ B ⌝Ty ⟩ , ⟨ ⌜ C ⌝Ty , encode f ⟩ ⟩

      step1 : (N ∘ (In {TermF} ∘ (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ payload))) ⟶*
              ((normalize-step ∘ fmap TermF N) ∘ (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ payload))
      step1 = cata-β-right {TermF} {TermCode'} {Unit} {normalize-step} {inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ payload}

      -- 12 inr navigations then inl
      r0 : (fmap TermF N ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inl ∘ payload)))))))))))))) ⟶*
           (inr ∘ (fmap TermF-1 N ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inl ∘ payload))))))))))))))
      r0 = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' _ (fmap-TermF-inr N)) (step assoc-r done))

      r1 : (fmap TermF-1 N ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inl ∘ payload))))))))))))) ⟶*
           (inr ∘ (fmap TermF-2 N ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inl ∘ payload)))))))))))))
      r1 = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' _ (fmap-1-inr N)) (step assoc-r done))

      r2 : (fmap TermF-2 N ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inl ∘ payload)))))))))))) ⟶*
           (inr ∘ (fmap TermF-3 N ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inl ∘ payload))))))))))))
      r2 = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' _ (fmap-2-inr N)) (step assoc-r done))

      r3 : (fmap TermF-3 N ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inl ∘ payload))))))))))) ⟶*
           (inr ∘ (fmap TermF-4 N ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inl ∘ payload)))))))))))
      r3 = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' _ (fmap-3-inr N)) (step assoc-r done))

      r4 : (fmap TermF-4 N ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inl ∘ payload)))))))))) ⟶*
           (inr ∘ (fmap TermF-5 N ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inl ∘ payload))))))))))
      r4 = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' _ (fmap-4-inr N)) (step assoc-r done))

      r5 : (fmap TermF-5 N ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inl ∘ payload))))))))) ⟶*
           (inr ∘ (fmap TermF-6 N ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inl ∘ payload)))))))))
      r5 = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' _ (fmap-5-inr N)) (step assoc-r done))

      r6 : (fmap TermF-6 N ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inl ∘ payload)))))))) ⟶*
           (inr ∘ (fmap TermF-7 N ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inl ∘ payload))))))))
      r6 = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' _ (fmap-6-inr N)) (step assoc-r done))

      r7 : (fmap TermF-7 N ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inl ∘ payload))))))) ⟶*
           (inr ∘ (fmap TermF-8 N ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inl ∘ payload)))))))
      r7 = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' _ (fmap-7-inr N)) (step assoc-r done))

      r8 : (fmap TermF-8 N ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inl ∘ payload)))))) ⟶*
           (inr ∘ (fmap TermF-9 N ∘ (inr ∘ (inr ∘ (inr ∘ (inl ∘ payload))))))
      r8 = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' _ (fmap-8-inr N)) (step assoc-r done))

      r9 : (fmap TermF-9 N ∘ (inr ∘ (inr ∘ (inr ∘ (inl ∘ payload))))) ⟶*
           (inr ∘ (fmap TermF-10 N ∘ (inr ∘ (inr ∘ (inl ∘ payload)))))
      r9 = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' _ (fmap-9-inr N)) (step assoc-r done))

      r10 : (fmap TermF-10 N ∘ (inr ∘ (inr ∘ (inl ∘ payload)))) ⟶*
            (inr ∘ (fmap TermF-11 N ∘ (inr ∘ (inl ∘ payload))))
      r10 = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' _ (fmap-10-inr N)) (step assoc-r done))

      r11 : (fmap TermF-11 N ∘ (inr ∘ (inl ∘ payload))) ⟶*
            (inr ∘ (fmap TermF-12 N ∘ (inl ∘ payload)))
      r11 = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' _ (fmap-11-inr N)) (step assoc-r done))

      -- Position 12 payload functor: CurryPayloadF = (K ⊗ K) ⊗ (K ⊗ Id)
      ih-step : (fmap CurryPayloadF N ∘ payload) ⟶* payload
      ih-step =
        ⟶*-trans (step pair-comp done)
          (⟨⟩-cong
            -- First component: fmap (K⊗K) N ∘ fst ∘ payload ⟶* ⟨⌜A⌝,⌜B⌝⟩
            (⟶*-trans (step assoc-r done)
              (⟶*-trans (∘-cong-right' (fmap (K TyFuncCode ⊗ K TyFuncCode) N) (step fst-pair done))
                (⟶*-trans (∘-cong-left' _ (fmap-KK-id TyFuncCode TyFuncCode N))
                  (step id-left done))))
            -- Second component: fmap (K⊗Id) N ∘ snd ∘ payload ⟶* ⟨⌜C⌝, encode f⟩
            (⟶*-trans (step assoc-r done)
              (⟶*-trans (∘-cong-right' (fmap (K TyFuncCode ⊗ Id) N) (step snd-pair done))
                (⟶*-trans (step pair-comp done)
                  (⟨⟩-cong
                    (⟶*-trans (step assoc-r done)
                      (⟶*-trans (step id-left done)
                        (step fst-pair done)))
                    (⟶*-trans (step assoc-r done)
                      (⟶*-trans (∘-cong-right' N (step snd-pair done))
                        (noredex-fixpoint f nrf))))))))

      -- Navigate through inl: fmap TermF-12 N ∘ inl ⟶* inl ∘ fmap CurryPayloadF N
      fmap-12-inl : (fmap TermF-12 N ∘ inl) ⟶* (inl ∘ fmap CurryPayloadF N)
      fmap-12-inl = fmap-sum-inl CurryPayloadF TermF-13 N

      r12 : (fmap TermF-12 N ∘ (inl ∘ payload)) ⟶* (inl ∘ payload)
      r12 = ⟶*-trans (step assoc-l done)
              (⟶*-trans (∘-cong-left' payload fmap-12-inl)
                (⟶*-trans (step assoc-r done)
                  (∘-cong-right' inl ih-step)))

      reduce-chain : (fmap TermF N ∘ (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ payload)) ⟶*
                     (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ payload)
      reduce-chain =
        ⟶*-trans r0 (∘-cong-right' inr
          (⟶*-trans r1 (∘-cong-right' inr
            (⟶*-trans r2 (∘-cong-right' inr
              (⟶*-trans r3 (∘-cong-right' inr
                (⟶*-trans r4 (∘-cong-right' inr
                  (⟶*-trans r5 (∘-cong-right' inr
                    (⟶*-trans r6 (∘-cong-right' inr
                      (⟶*-trans r7 (∘-cong-right' inr
                        (⟶*-trans r8 (∘-cong-right' inr
                          (⟶*-trans r9 (∘-cong-right' inr
                            (⟶*-trans r10 (∘-cong-right' inr
                              (⟶*-trans r11 (∘-cong-right' inr r12)))))))))))))))))))))))

      inner-step : (normalize-step ∘ (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ payload)) ⟶* (handle-curry ∘ payload)
      inner-step =
        ⟶*-trans (step assoc-l done)
          (⟶*-trans (step assoc-l done)
            (⟶*-trans (step assoc-l done)
              (⟶*-trans (step assoc-l done)
                (⟶*-trans (step assoc-l done)
                  (⟶*-trans (step assoc-l done)
                    (⟶*-trans (step assoc-l done)
                      (⟶*-trans (step assoc-l done)
                        (⟶*-trans (step assoc-l done)
                          (⟶*-trans (step assoc-l done)
                            (⟶*-trans (step assoc-l done)
                              (⟶*-trans (step assoc-l done)
                                (⟶*-trans (step assoc-l done)
                                  (∘-cong-left' payload nstep-at-12')))))))))))))

      step2 : ((normalize-step ∘ fmap TermF N) ∘ (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ payload)) ⟶*
              (handle-curry ∘ payload)
      step2 = ⟶*-trans (step assoc-r done)
                (⟶*-trans (∘-cong-right' normalize-step reduce-chain)
                  inner-step)

      step3 : (handle-curry ∘ payload) ⟶* ((In {TermF} ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl) ∘ payload)
      step3 = done

      step4 : ((In {TermF} ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl) ∘ payload) ⟶*
              (In {TermF} ∘ (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ payload))
      step4 = ⟶*-trans (step assoc-r done)
                (∘-cong-right' In
                  (⟶*-trans (step assoc-r done)
                    (∘-cong-right' inr
                      (⟶*-trans (step assoc-r done)
                        (∘-cong-right' inr
                          (⟶*-trans (step assoc-r done)
                            (∘-cong-right' inr
                              (⟶*-trans (step assoc-r done)
                                (∘-cong-right' inr
                                  (⟶*-trans (step assoc-r done)
                                    (∘-cong-right' inr
                                      (⟶*-trans (step assoc-r done)
                                        (∘-cong-right' inr
                                          (⟶*-trans (step assoc-r done)
                                            (∘-cong-right' inr
                                              (⟶*-trans (step assoc-r done)
                                                (∘-cong-right' inr
                                                  (⟶*-trans (step assoc-r done)
                                                    (∘-cong-right' inr
                                                      (⟶*-trans (step assoc-r done)
                                                        (∘-cong-right' inr
                                                          (⟶*-trans (step assoc-r done)
                                                            (∘-cong-right' inr (step assoc-r done))))))))))))))))))))))))

  -- Position 11 (cata): encode (cata F alg) = In ∘ inr^11 ∘ inl ∘ ⟨⌜F⌝, encode alg⟩
  -- Payload functor: K TyFuncCode ⊗ Id
  noredex-fixpoint (cata F alg) (nr-cata nralg) = ⟶*-trans step1 (⟶*-trans step2 (⟶*-trans step3 step4))
    where
      N : Term TermCode' TermCode'
      N = cata TermF normalize-step

      payload : Term Unit (TyFuncCode * TermCode')
      payload = ⟨ ⌜ F ⌝Func , encode alg ⟩

      step1 : (N ∘ (In {TermF} ∘ (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ payload))) ⟶*
              ((normalize-step ∘ fmap TermF N) ∘ (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ payload))
      step1 = cata-β-right {TermF} {TermCode'} {Unit} {normalize-step} {inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ payload}

      -- 11 inr navigations
      r0 : (fmap TermF N ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inl ∘ payload))))))))))))) ⟶*
           (inr ∘ (fmap TermF-1 N ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inl ∘ payload)))))))))))))
      r0 = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' _ (fmap-TermF-inr N)) (step assoc-r done))

      r1 : (fmap TermF-1 N ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inl ∘ payload)))))))))))) ⟶*
           (inr ∘ (fmap TermF-2 N ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inl ∘ payload))))))))))))
      r1 = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' _ (fmap-1-inr N)) (step assoc-r done))

      r2 : (fmap TermF-2 N ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inl ∘ payload))))))))))) ⟶*
           (inr ∘ (fmap TermF-3 N ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inl ∘ payload)))))))))))
      r2 = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' _ (fmap-2-inr N)) (step assoc-r done))

      r3 : (fmap TermF-3 N ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inl ∘ payload)))))))))) ⟶*
           (inr ∘ (fmap TermF-4 N ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inl ∘ payload))))))))))
      r3 = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' _ (fmap-3-inr N)) (step assoc-r done))

      r4 : (fmap TermF-4 N ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inl ∘ payload))))))))) ⟶*
           (inr ∘ (fmap TermF-5 N ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inl ∘ payload)))))))))
      r4 = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' _ (fmap-4-inr N)) (step assoc-r done))

      r5 : (fmap TermF-5 N ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inl ∘ payload)))))))) ⟶*
           (inr ∘ (fmap TermF-6 N ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inl ∘ payload))))))))
      r5 = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' _ (fmap-5-inr N)) (step assoc-r done))

      r6 : (fmap TermF-6 N ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inl ∘ payload))))))) ⟶*
           (inr ∘ (fmap TermF-7 N ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inl ∘ payload)))))))
      r6 = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' _ (fmap-6-inr N)) (step assoc-r done))

      r7 : (fmap TermF-7 N ∘ (inr ∘ (inr ∘ (inr ∘ (inr ∘ (inl ∘ payload)))))) ⟶*
           (inr ∘ (fmap TermF-8 N ∘ (inr ∘ (inr ∘ (inr ∘ (inl ∘ payload))))))
      r7 = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' _ (fmap-7-inr N)) (step assoc-r done))

      r8 : (fmap TermF-8 N ∘ (inr ∘ (inr ∘ (inr ∘ (inl ∘ payload))))) ⟶*
           (inr ∘ (fmap TermF-9 N ∘ (inr ∘ (inr ∘ (inl ∘ payload)))))
      r8 = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' _ (fmap-8-inr N)) (step assoc-r done))

      r9 : (fmap TermF-9 N ∘ (inr ∘ (inr ∘ (inl ∘ payload)))) ⟶*
           (inr ∘ (fmap TermF-10 N ∘ (inr ∘ (inl ∘ payload))))
      r9 = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' _ (fmap-9-inr N)) (step assoc-r done))

      r10 : (fmap TermF-10 N ∘ (inr ∘ (inl ∘ payload))) ⟶*
            (inr ∘ (fmap TermF-11 N ∘ (inl ∘ payload)))
      r10 = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' _ (fmap-10-inr N)) (step assoc-r done))

      -- Position 11 payload functor: K TyFuncCode ⊗ Id
      ih-step : (fmap (K TyFuncCode ⊗ Id) N ∘ payload) ⟶* payload
      ih-step =
        ⟶*-trans (step pair-comp done)
          (⟨⟩-cong
            (⟶*-trans (step assoc-r done)
              (⟶*-trans (step id-left done)
                (step fst-pair done)))
            (⟶*-trans (step assoc-r done)
              (⟶*-trans (∘-cong-right' N (step snd-pair done))
                (noredex-fixpoint alg nralg))))

      -- Navigate through inl: fmap TermF-11 N ∘ inl ⟶* inl ∘ fmap (K TyFuncCode ⊗ Id) N
      fmap-11-inl : (fmap TermF-11 N ∘ inl) ⟶* (inl ∘ fmap (K TyFuncCode ⊗ Id) N)
      fmap-11-inl = fmap-sum-inl (K TyFuncCode ⊗ Id) TermF-12 N

      r11 : (fmap TermF-11 N ∘ (inl ∘ payload)) ⟶* (inl ∘ payload)
      r11 = ⟶*-trans (step assoc-l done)
              (⟶*-trans (∘-cong-left' payload fmap-11-inl)
                (⟶*-trans (step assoc-r done)
                  (∘-cong-right' inl ih-step)))

      reduce-chain : (fmap TermF N ∘ (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ payload)) ⟶*
                     (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ payload)
      reduce-chain =
        ⟶*-trans r0 (∘-cong-right' inr
          (⟶*-trans r1 (∘-cong-right' inr
            (⟶*-trans r2 (∘-cong-right' inr
              (⟶*-trans r3 (∘-cong-right' inr
                (⟶*-trans r4 (∘-cong-right' inr
                  (⟶*-trans r5 (∘-cong-right' inr
                    (⟶*-trans r6 (∘-cong-right' inr
                      (⟶*-trans r7 (∘-cong-right' inr
                        (⟶*-trans r8 (∘-cong-right' inr
                          (⟶*-trans r9 (∘-cong-right' inr
                            (⟶*-trans r10 (∘-cong-right' inr r11)))))))))))))))))))))

      inner-step : (normalize-step ∘ (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ payload)) ⟶* (handle-cata ∘ payload)
      inner-step =
        ⟶*-trans (step assoc-l done)
          (⟶*-trans (step assoc-l done)
            (⟶*-trans (step assoc-l done)
              (⟶*-trans (step assoc-l done)
                (⟶*-trans (step assoc-l done)
                  (⟶*-trans (step assoc-l done)
                    (⟶*-trans (step assoc-l done)
                      (⟶*-trans (step assoc-l done)
                        (⟶*-trans (step assoc-l done)
                          (⟶*-trans (step assoc-l done)
                            (⟶*-trans (step assoc-l done)
                              (⟶*-trans (step assoc-l done)
                                (∘-cong-left' payload nstep-at-11'))))))))))))

      step2 : ((normalize-step ∘ fmap TermF N) ∘ (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ payload)) ⟶*
              (handle-cata ∘ payload)
      step2 = ⟶*-trans (step assoc-r done)
                (⟶*-trans (∘-cong-right' normalize-step reduce-chain)
                  inner-step)

      step3 : (handle-cata ∘ payload) ⟶* ((In {TermF} ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl) ∘ payload)
      step3 = done

      step4 : ((In {TermF} ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl) ∘ payload) ⟶*
              (In {TermF} ∘ (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ payload))
      step4 = ⟶*-trans (step assoc-r done)
                (∘-cong-right' In
                  (⟶*-trans (step assoc-r done)
                    (∘-cong-right' inr
                      (⟶*-trans (step assoc-r done)
                        (∘-cong-right' inr
                          (⟶*-trans (step assoc-r done)
                            (∘-cong-right' inr
                              (⟶*-trans (step assoc-r done)
                                (∘-cong-right' inr
                                  (⟶*-trans (step assoc-r done)
                                    (∘-cong-right' inr
                                      (⟶*-trans (step assoc-r done)
                                        (∘-cong-right' inr
                                          (⟶*-trans (step assoc-r done)
                                            (∘-cong-right' inr
                                              (⟶*-trans (step assoc-r done)
                                                (∘-cong-right' inr
                                                  (⟶*-trans (step assoc-r done)
                                                    (∘-cong-right' inr
                                                      (⟶*-trans (step assoc-r done)
                                                        (∘-cong-right' inr (step assoc-r done))))))))))))))))))))))

  -- Position 1 (comp): This is the most complex case because handle-comp does runtime checks
  -- For NoRedex inputs, handle-comp should behave like rebuild-1
  -- Postulate: handle-comp ∘ ⟨encode f, encode g⟩ ⟶* rebuild-1 ∘ ⟨encode f, encode g⟩
  -- when f,g are NoRedex and not identities
  noredex-fixpoint (f ∘ g) (nr-comp nrf nrg nisf nisg) = ⟶*-trans step1 (⟶*-trans step2 (⟶*-trans step3 step4))
    where
      N : Term TermCode' TermCode'
      N = cata TermF normalize-step

      payload : Term Unit (TermCode' * TermCode')
      payload = ⟨ encode f , encode g ⟩

      step1 : (N ∘ (In {TermF} ∘ (inr ∘ inl ∘ payload))) ⟶*
              ((normalize-step ∘ fmap TermF N) ∘ (inr ∘ inl ∘ payload))
      step1 = cata-β-right {TermF} {TermCode'} {Unit} {normalize-step} {inr ∘ inl ∘ payload}

      -- 1 inr navigation then inl
      r0 : (fmap TermF N ∘ (inr ∘ (inl ∘ payload))) ⟶*
           (inr ∘ (fmap TermF-1 N ∘ (inl ∘ payload)))
      r0 = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' _ (fmap-TermF-inr N)) (step assoc-r done))

      -- Position 1 payload functor: Id ⊗ Id
      ih-step : (fmap (Id ⊗ Id) N ∘ payload) ⟶* payload
      ih-step =
        ⟶*-trans (step pair-comp done)
          (⟨⟩-cong
            (⟶*-trans (step assoc-r done)
              (⟶*-trans (∘-cong-right' N (step fst-pair done))
                (noredex-fixpoint f nrf)))
            (⟶*-trans (step assoc-r done)
              (⟶*-trans (∘-cong-right' N (step snd-pair done))
                (noredex-fixpoint g nrg))))

      comp-fmap-1-inl : (fmap TermF-1 N ∘ inl) ⟶* (inl ∘ fmap (Id ⊗ Id) N)
      comp-fmap-1-inl = fmap-sum-inl (Id ⊗ Id) TermF-2 N

      r1 : (fmap TermF-1 N ∘ (inl ∘ payload)) ⟶* (inl ∘ payload)
      r1 = ⟶*-trans (step assoc-l done)
             (⟶*-trans (∘-cong-left' payload comp-fmap-1-inl)
               (⟶*-trans (step assoc-r done)
                 (∘-cong-right' inl ih-step)))

      reduce-chain : (fmap TermF N ∘ (inr ∘ inl ∘ payload)) ⟶* (inr ∘ inl ∘ payload)
      reduce-chain = ⟶*-trans r0 (∘-cong-right' inr r1)

      inner-step : (normalize-step ∘ (inr ∘ inl ∘ payload)) ⟶* (handle-comp ∘ payload)
      inner-step =
        ⟶*-trans (step assoc-l done)
          (⟶*-trans (step assoc-l done)
            (∘-cong-left' payload nstep-at-1'))

      step2 : ((normalize-step ∘ fmap TermF N) ∘ (inr ∘ inl ∘ payload)) ⟶*
              (handle-comp ∘ payload)
      step2 = ⟶*-trans (step assoc-r done)
                (⟶*-trans (∘-cong-right' normalize-step reduce-chain)
                  inner-step)

      -- Key step: handle-comp reduces to rebuild-1 for non-identity NoRedex inputs
      -- TODO: Prove that is-id ∘ encode f returns inr for non-identity NoRedex terms
      step3 : (handle-comp ∘ payload) ⟶* ((In {TermF} ∘ inr ∘ inl) ∘ payload)
      step3 = {!!}

      step4 : ((In {TermF} ∘ inr ∘ inl) ∘ payload) ⟶* (In {TermF} ∘ (inr ∘ inl ∘ payload))
      step4 = ⟶*-trans (step assoc-r done)
                (∘-cong-right' In (step assoc-r done))

------------------------------------------------------------------------
-- The Encoding of the Normalizer
------------------------------------------------------------------------

-- The normalizer encoded as data
-- Abstract prevents Agda from unfolding during MainTheorem type-checking
abstract
  normalize-encoded : Term Unit TermCode'
  normalize-encoded = encode normalize

  -- Definitional equality (for export)
  normalize-encoded-def : normalize-encoded ≡ encode normalize
  normalize-encoded-def = refl

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
