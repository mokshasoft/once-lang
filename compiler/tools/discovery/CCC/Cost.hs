{-# LANGUAGE LambdaCase #-}
-- | Cost model for CCC optimization discovery
--
-- The cost model determines which terms are "simpler" or "cheaper".
-- We primarily count allocations, as the goal of deforestation is
-- to eliminate intermediate data structures.
module CCC.Cost
  ( Cost(..)
  , cost
  , totalCost
  , cheaper
  ) where

import Once.IR (IR(..))

-- | Cost of an IR term
--
-- We track:
-- - allocations: Number of heap allocations (Pair, Inl, Inr, Curry)
-- - depth: Structural depth of the term (tie-breaker)
data Cost = Cost
  { allocations :: !Int
  , depth :: !Int
  } deriving (Eq, Show)

-- | Combine costs (for subterms)
addCost :: Cost -> Cost -> Cost
addCost c1 c2 = Cost
  { allocations = allocations c1 + allocations c2
  , depth = max (depth c1) (depth c2) + 1
  }

-- | Calculate the cost of an IR term
--
-- The key insight: we want to minimize allocations.
-- - Pair allocates a pair on the heap
-- - Inl/Inr allocate a tagged sum
-- - Curry allocates a closure
-- - Everything else is "free" (projections, composition, etc.)
cost :: IR -> Cost
cost = \case
  -- Category structure: free
  Id _ -> Cost 0 1
  Compose g f -> addCost (cost g) (cost f)

  -- Products: projections free, pairing allocates
  Fst _ _ -> Cost 0 1
  Snd _ _ -> Cost 0 1
  Pair f g -> Cost 1 1 `addCost` cost f `addCost` cost g  -- 1 allocation

  -- Terminal/Initial: free
  Terminal _ -> Cost 0 1
  Initial _ -> Cost 0 1

  -- Coproducts: case free, injections allocate
  Inl _ _ -> Cost 1 1  -- 1 allocation (tag)
  Inr _ _ -> Cost 1 1  -- 1 allocation (tag)
  Case f g -> maxCost (cost f) (cost g)

  -- Exponentials: apply free, curry allocates closure
  Curry _ f -> Cost 1 1 `addCost` cost f  -- 1 allocation (closure)
  Apply _ _ -> Cost 0 1

  -- Fixed points: fold allocates, unfold free
  Fold _ -> Cost 1 1  -- 1 allocation
  Unfold _ -> Cost 0 1

  -- Variables and primitives: opaque, assume free
  Var _ -> Cost 0 1
  LocalVar _ -> Cost 0 1
  FunRef _ -> Cost 0 1
  Prim _ _ _ -> Cost 0 1
  StringLit _ -> Cost 0 1
  Let _ e1 e2 -> addCost (cost e1) (cost e2)
  Arith _ _ -> Cost 0 1

-- | Maximum of two costs (for case branches)
maxCost :: Cost -> Cost -> Cost
maxCost c1 c2 = Cost
  { allocations = max (allocations c1) (allocations c2)
  , depth = max (depth c1) (depth c2)
  }

-- | Total cost as a single comparable number
--
-- Allocations are weighted heavily, depth is a tie-breaker.
totalCost :: Cost -> Int
totalCost c = 100 * allocations c + depth c

-- | Check if one term is strictly cheaper than another
cheaper :: IR -> IR -> Bool
cheaper t1 t2 = totalCost (cost t1) < totalCost (cost t2)
