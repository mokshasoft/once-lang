------------------------------------------------------------------------
-- Normalize.Handlers: Handler functions for normalize-step
--
-- Each handler processes a specific term constructor position:
-- - Simple handlers just rebuild with In
-- - handle-comp detects id composition and reduces
-- - handle-pair and handle-case check for eta reduction
------------------------------------------------------------------------

module normalizer.Implementation.Normalize.Handlers where

open import normalizer.Foundations.Chain public
open import normalizer.Implementation.Normalize.Dispatch public

------------------------------------------------------------------------
-- Simple Handlers (just rebuild)
------------------------------------------------------------------------

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

handle-initial : Term TyFuncCode TermCode'
handle-initial = rebuild-9

handle-In : Term TyFuncCode TermCode'
handle-In = rebuild-10

handle-Out : Term TyFuncCode TermCode'
handle-Out = rebuild-11

handle-cata : Term (TyFuncCode * TermCode') TermCode'
handle-cata = rebuild-12

handle-curry : Term ((TyFuncCode * TyFuncCode) * (TyFuncCode * TermCode')) TermCode'
handle-curry = rebuild-13

handle-apply : Term (TyFuncCode * TyFuncCode) TermCode'
handle-apply = rebuild-14

------------------------------------------------------------------------
-- Composition Handler (position 1)
--
-- Input: (f, g) : TermCode' * TermCode' (already normalized)
--
-- Reduction rules to apply:
--   id ∘ g  → g
--   f ∘ id  → f
--   fst ∘ ⟨f,g⟩ → f  (TODO)
--   snd ∘ ⟨f,g⟩ → g  (TODO)
--   [f,g] ∘ inl → f  (TODO)
--   [f,g] ∘ inr → g  (TODO)
------------------------------------------------------------------------

-- Helper: prepare for is-id check on first component
-- ⟨ snd , is-id ∘ fst ⟩ : (f, g) → (g, Unit + f')
prep-check-f-id : Term (TermCode' * TermCode') (TermCode' * (Unit + TermCode'))
prep-check-f-id = ⟨ snd , is-id ∘ fst ⟩

-- When f = id: return g (which is fst after prep)
comp-f-is-id : Term (TermCode' * Unit) TermCode'
comp-f-is-id = fst

-- Helper: prepare for is-id check on second component
-- Starting from (g, f') after f≠id, restructure to (f', is-id(g))
prep-check-g-id : Term (TermCode' * TermCode') (TermCode' * (Unit + TermCode'))
prep-check-g-id = ⟨ snd , is-id ∘ fst ⟩

-- When g = id: return f' (which is fst)
comp-g-is-id : Term (TermCode' * Unit) TermCode'
comp-g-is-id = fst

-- When g ≠ id: rebuild as composition
comp-fallback : Term (TermCode' * TermCode') TermCode'
comp-fallback = rebuild-1

-- Inner handler: check if g = id (exported for NoRedex proofs)
check-g-handler : Term (TermCode' * TermCode') TermCode'
check-g-handler = caseWithCtx comp-g-is-id comp-fallback ∘ prep-check-g-id

-- Full composition handler:
-- 1. Check if f = id, if so return g
-- 2. Else check if g = id, if so return f
-- 3. Else rebuild as comp(f, g)
handle-comp : Term (TermCode' * TermCode') TermCode'
handle-comp = caseWithCtx comp-f-is-id check-g-handler ∘ prep-check-f-id

------------------------------------------------------------------------
-- Pair Handler (position 4) - eta reduction
--
-- ⟨fst, snd⟩ → id
--
-- Simplified: just rebuild for now (eta optimization deferred)
------------------------------------------------------------------------

-- Check first component for fst
prep-check-fst : Term (TermCode' * TermCode') (TermCode' * (Unit + TermCode'))
prep-check-fst = ⟨ snd , is-fst ∘ fst ⟩

-- Check second component for snd
prep-check-snd : Term (TermCode' * TermCode') (TermCode' * (Unit + TermCode'))
prep-check-snd = ⟨ fst , is-snd ∘ snd ⟩

-- When both fst and snd: return id
pair-eta : Term (TermCode' * Unit) TermCode'
pair-eta = encoded-id ∘ terminal

-- Pair handler: just rebuild for now (eta optimization deferred)
handle-pair : Term (TermCode' * TermCode') TermCode'
handle-pair = rebuild-4

------------------------------------------------------------------------
-- Case Handler (position 7) - eta reduction
--
-- [inl, inr] → id
--
-- Simplified: just rebuild for now (eta optimization deferred)
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

-- Case handler: just rebuild for now (eta optimization deferred)
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
  ]

------------------------------------------------------------------------
-- The Normalizer (cata TermF normalize-step)
------------------------------------------------------------------------

normalize : Term TermCode' TermCode'
normalize = cata TermF normalize-step
