-- | Tail-call optimization via Loop transformation (D047)
--
-- This module detects tail-recursive functions and transforms them
-- to use the Loop IR construct, enabling stack-free iteration.
--
-- Handles both direct self-recursion and mutual recursion via
-- defunctionalization.
module Once.TailCall
  ( -- * Main API
    optimizeTailCalls
  , optimizeTailCallsSingle
    -- * Analysis
  , TailCallGroup(..)
  , analyzeTailCalls
  , findTailCalls
  , isInTailPosition
    -- * Transformation
  , transformSingleRecursive
  , transformMutualRecursive
  ) where

import Data.Graph (SCC(..), stronglyConnComp)
import Data.List (nub)
import qualified Data.Map.Strict as Map
import Data.Maybe (mapMaybe)
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Text (Text)

import Once.IR (IR(..))
import Once.Type (Name, Type(..))

-- | A group of functions that are mutually tail-recursive
data TailCallGroup
  = SingleRecursive Name IR        -- ^ Direct self-recursion: f calls f
  | MutualRecursive [(Name, IR)]   -- ^ Mutually recursive: f calls g calls f
  deriving (Show, Eq)

-- | Optimize tail calls for a list of function definitions
-- Returns transformed definitions
optimizeTailCalls :: [(Name, IR)] -> [(Name, IR)]
optimizeTailCalls funcs =
  let groups = analyzeTailCalls funcs
  in concatMap transformGroup groups

-- | Optimize a single function (for use in pipeline)
-- If it's self-recursive in tail position, transform to Loop
--
-- TODO: Currently disabled because OnceSum.value is intptr_t which
-- can't hold struct types (OncePair, OnceBuffer). Need to fix the
-- C representation of sum types first.
optimizeTailCallsSingle :: Name -> IR -> IR
optimizeTailCallsSingle _name ir = ir  -- Disabled for now
-- optimizeTailCallsSingle name ir =
--   let tailCalls = findTailCalls name ir
--   in if name `Set.member` tailCalls
--      then transformSingleRecursive name ir
--      else ir

-- | Analyze functions to find tail-recursive groups
analyzeTailCalls :: [(Name, IR)] -> [TailCallGroup]
analyzeTailCalls funcs =
  let -- Build call graph: (node, key, [keys it depends on])
      -- For stronglyConnComp: (node, key, [keys]) where node is our data
      graph = [((n, ir), n, Set.toList (findTailCalls n ir)) | (n, ir) <- funcs]
      sccs = stronglyConnComp graph
  in mapMaybe sccToGroup sccs
  where
    sccToGroup :: SCC (Name, IR) -> Maybe TailCallGroup
    sccToGroup (AcyclicSCC _) = Nothing  -- Not recursive
    sccToGroup (CyclicSCC [(name, body)]) = Just (SingleRecursive name body)
    sccToGroup (CyclicSCC items) = Just (MutualRecursive items)

-- | Find all function names that are called in tail position
findTailCalls :: Name -> IR -> Set Name
findTailCalls context = go True
  where
    -- go isTail ir: find tail calls, isTail indicates if current position is tail
    go :: Bool -> IR -> Set Name
    go isTail ir = case ir of
      -- Variable reference: tail call if in tail position
      Var n | isTail -> Set.singleton n
            | otherwise -> Set.empty

      -- Composition: only the outer (g) is in tail position
      -- compose g f : the result of f is passed to g, so g is tail
      Compose g f -> Set.union (go isTail g) (go False f)

      -- Case: both branches inherit tail position
      Case l r -> Set.union (go isTail l) (go isTail r)

      -- Curry: the body is in tail position (result of lambda)
      Curry _ body -> go isTail body

      -- Let: the body (e2) is in tail position, e1 is not
      Let _ e1 e2 -> Set.union (go False e1) (go isTail e2)

      -- Pair: neither component is in tail position (constructing a value)
      Pair f g -> Set.union (go False f) (go False g)

      -- Loop body: the body produces Either, not in simple tail position
      Loop _ body -> go False body

      -- Leaves: no calls
      Id _ -> Set.empty
      Fst _ _ -> Set.empty
      Snd _ _ -> Set.empty
      Terminal _ -> Set.empty
      Inl _ _ -> Set.empty
      Inr _ _ -> Set.empty
      Initial _ -> Set.empty
      Apply _ _ -> Set.empty
      LocalVar _ -> Set.empty
      FunRef _ -> Set.empty
      Prim _ _ _ -> Set.empty
      StringLit _ -> Set.empty
      Fold _ -> Set.empty
      Unfold _ -> Set.empty

-- | Check if a specific call is in tail position
isInTailPosition :: Name -> IR -> Bool
isInTailPosition name ir = name `Set.member` findTailCalls name ir

-- | Transform a group to use Loop
transformGroup :: TailCallGroup -> [(Name, IR)]
transformGroup (SingleRecursive name body) =
  [(name, transformSingleRecursive name body)]
transformGroup (MutualRecursive funcs) =
  transformMutualRecursive funcs

-- | Transform a self-recursive function to use Loop
--
-- Before: f = \x -> ... case ... { Left -> f(y); Right -> result }
-- After:  f = \x -> Loop x (... case ... { Left -> Right(y); Right -> Left(result) })
--
-- The transformation:
-- 1. Wrap body in Loop
-- 2. Replace recursive calls (Var name) with Inr (continue)
-- 3. Replace non-recursive returns with Inl (exit)
transformSingleRecursive :: Name -> IR -> IR
transformSingleRecursive name body = case body of
  -- Lambda at top level: transform the body
  Curry varName innerBody ->
    Curry varName (Loop varName (transformBody name innerBody))
  -- No lambda: wrap in Loop directly
  _ -> Loop "_state" (transformBody name body)

-- | Transform the body of a recursive function
-- Replace tail calls with Inr, other returns with Inl
--
-- The key insight: we need to find the "return points" and wrap them:
-- - Recursive calls (Var name or Compose (Var name) f) -> Inr (continue)
-- - Non-recursive final values -> Inl (exit)
transformBody :: Name -> IR -> IR
transformBody name = go
  where
    go :: IR -> IR
    go ir = case ir of
      -- Direct recursive call: replace with Inr id (continue with same input)
      Var n | n == name -> Inr TUnit TUnit

      -- Composition with recursive call as outer: f computes next state
      -- Compose (Var name) f means: compute f, then call name with result
      -- Replace with: compute f, wrap in Inr (Right = continue)
      Compose (Var n) f | n == name -> Compose (Inr TUnit TUnit) (go f)

      -- General composition: only transform if outer isn't the recursive call
      Compose g f -> Compose (go g) (go f)

      -- Case: transform both branches
      Case l r -> Case (go l) (go r)

      -- Curry: transform inner body, then wrap result in Inl if non-recursive
      Curry varName innerBody ->
        let transformed = go innerBody
        in if containsInr transformed
           then Curry varName transformed  -- Has Inr, don't add Inl
           else Curry varName (Compose (Inl TUnit TUnit) transformed)  -- Wrap exit in Inl

      -- Let: transform both parts
      Let x e1 e2 -> Let x (go e1) (go e2)

      -- Pair: transform components
      Pair f g -> Pair (go f) (go g)

      -- Leaves that don't contain recursive calls: these are intermediate values
      -- They'll get wrapped by enclosing Curry if they're the final result
      _ -> ir

-- | Check if IR contains Inr (meaning it has a continue path)
containsInr :: IR -> Bool
containsInr = go
  where
    go ir = case ir of
      Inr _ _ -> True
      Compose g f -> go g || go f
      Case l r -> go l || go r
      Curry _ body -> go body
      Let _ e1 e2 -> go e1 || go e2
      Pair f g -> go f || go g
      Loop _ body -> go body
      _ -> False

-- | Check if IR contains a call to the given name
containsCall :: Name -> IR -> Bool
containsCall name = go
  where
    go ir = case ir of
      Var n -> n == name
      Compose g f -> go g || go f
      Case l r -> go l || go r
      Curry _ body -> go body
      Let _ e1 e2 -> go e1 || go e2
      Pair f g -> go f || go g
      Loop _ body -> go body
      _ -> False

-- | Transform mutually recursive functions using defunctionalization
--
-- For f : A -> C and g : B -> C that call each other:
-- 1. Create combined function fg : Either A B -> C
-- 2. Replace f with: compose fg inl
-- 3. Replace g with: compose fg inr
-- 4. Transform fg to use Loop
transformMutualRecursive :: [(Name, IR)] -> [(Name, IR)]
transformMutualRecursive funcs = case funcs of
  [] -> []
  [(name, body)] -> [(name, transformSingleRecursive name body)]
  _ ->
    let names = map fst funcs
        -- Create the combined function name
        combinedName = mconcat names <> "_combined"
        -- Transform each function to produce Either result C (Either entry)
        -- where entry is the sum type of all function inputs
        transformedBodies = map (transformForCombined names) funcs
        -- Combine into single Case expression
        combinedBody = buildCombinedBody transformedBodies
        -- Wrap in Loop
        loopBody = Loop "_state" combinedBody
        -- Create wrapper functions
        wrappers = zipWith (makeWrapper combinedName) [0..] funcs
    in (combinedName, loopBody) : wrappers

-- | Transform a function body for the combined function
-- Replace calls to any of the mutual functions with appropriate Inr
transformForCombined :: [Name] -> (Name, IR) -> (Name, IR)
transformForCombined names (name, body) =
  (name, transformBodyForCombined names body)

transformBodyForCombined :: [Name] -> IR -> IR
transformBodyForCombined names = go True
  where
    go isTail ir = case ir of
      -- Call to one of our mutual functions: replace with Inr
      Var n | n `elem` names && isTail ->
        -- Need to tag which function we're calling
        let idx = findIndex n names
        in Compose (Inr TUnit TUnit) (tagForIndex idx (length names))

      Compose (Var n) f | n `elem` names && isTail ->
        let idx = findIndex n names
        in Compose (Inr TUnit TUnit) (Compose (tagForIndex idx (length names)) (go False f))

      Compose g f -> Compose (go isTail g) (go False f)
      Case l r -> Case (go isTail l) (go isTail r)
      Curry varName innerBody -> Curry varName (go isTail innerBody)
      Let x e1 e2 -> Let x (go False e1) (go isTail e2)
      Pair f g -> Pair (go False f) (go False g)

      -- Non-recursive return
      _ | isTail && not (any (\n -> containsCall n ir) names) ->
        Compose (Inl TUnit TUnit) ir

      _ -> ir

    findIndex :: Name -> [Name] -> Int
    findIndex n ns = case lookup n (zip ns [0..]) of
      Just i -> i
      Nothing -> error $ "Name not found: " ++ show n

-- | Build nested Inl/Inr to tag entry point
-- For 2 functions: 0 -> Inl, 1 -> Inr
-- For 3 functions: 0 -> Inl, 1 -> Inr.Inl, 2 -> Inr.Inr
tagForIndex :: Int -> Int -> IR
tagForIndex 0 _ = Inl TUnit TUnit
tagForIndex n total
  | n == total - 1 = Inr TUnit TUnit
  | otherwise = Compose (Inr TUnit TUnit) (tagForIndex (n - 1) (total - 1))

-- | Build combined body from transformed functions
buildCombinedBody :: [(Name, IR)] -> IR
buildCombinedBody [] = error "Empty function list"
buildCombinedBody [(_, body)] = body
buildCombinedBody ((_, body):rest) =
  Case (Curry "_l" body) (Curry "_r" (buildCombinedBody rest))

-- | Make wrapper function: f = compose combined (tagForIndex i)
makeWrapper :: Name -> Int -> (Name, IR) -> (Name, IR)
makeWrapper combinedName idx (name, _) =
  let tag = tagForIndex idx 2  -- Simplified for 2 functions
  in (name, Compose (Var combinedName) tag)
