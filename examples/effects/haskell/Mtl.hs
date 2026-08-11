-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson
--
-- mtl version of the State + Teletype program (cf. Once examples 03-05).
-- Illustrative: shows the *shape* of mtl-style effect composition.
--
-- Pain points to notice, vs the Once version:
--   * an effect = a typeclass; each new carrier must instantiate EVERY effect
--     class it wants (the O(n^2) instance problem);
--   * effect ORDER is fixed in the carrier's transformer-stack type;
--   * reinterpreting for a test means a WHOLE NEW carrier + its instances.

{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleInstances #-}

module Mtl where

import Control.Monad.State
import Control.Monad.Writer

-- An effect is a typeclass.
class Monad m => MonadTeletype m where
  readTTY  :: m String
  writeTTY :: String -> m ()

-- The program is constraint-polymorphic over the carrier. To MIX two effects
-- you must name BOTH constraints here, and every concrete carrier below must
-- satisfy both.
session :: (MonadState Int m, MonadTeletype m) => m ()
session = greet >> bump >> greet
  where
    greet = do { name <- readTTY; writeTTY ("Hello, " ++ name) }
    bump  = modify (+ 1)

-- Production carrier: StateT over IO. The effect order is pinned in THIS type.
newtype App a = App { runApp :: StateT Int IO a }
  deriving (Functor, Applicative, Monad, MonadState Int, MonadIO)

instance MonadTeletype App where
  readTTY  = liftIO getLine
  writeTTY = liftIO . putStrLn

main :: IO ()
main = evalStateT (runApp (session :: App ())) 0

-- Reinterpretation for tests: a SECOND carrier. Note we must re-provide every
-- instance again (here Teletype via Writer). This duplication is exactly what
-- the Once `pureConsole` handler avoids — same `session`, new handler, done.
newtype Test a = Test { runTest :: StateT Int (Writer [String]) a }
  deriving (Functor, Applicative, Monad, MonadState Int, MonadWriter [String])

instance MonadTeletype Test where
  readTTY    = pure "<canned>"
  writeTTY s = tell [s]

runPure :: Int -> ((), [String])
runPure s0 = runWriter (evalStateT (runTest (session :: Test ())) s0)
