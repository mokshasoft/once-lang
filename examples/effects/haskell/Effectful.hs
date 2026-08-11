-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson
--
-- effectful version of the State + Teletype program (cf. Once examples 03-05).
-- Illustrative: shows the fast, ReaderT-IO-backed algebraic-effects style.
--
-- Like polysemy, effects are an unordered ROW (`:>` constraints) discharged by
-- handlers. Unlike polysemy, there is no free-monad tree: `Eff es` is
-- essentially `ReaderT (Env es) IO`, so it is fast. This is the closest
-- *runtime* analogue to OCP-0007's "grade erases" — except Once erases the row
-- entirely at compile time rather than carrying an environment at run time.

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module Effectful where

import Effectful
import Effectful.Dispatch.Dynamic
import Effectful.State.Static.Local

data Teletype :: Effect where
  ReadTTY  :: Teletype m String
  WriteTTY :: String -> Teletype m ()

type instance DispatchOf Teletype = Dynamic

makeEffect ''Teletype

-- Effect set as a row of `:>` constraints.
session :: (State Int :> es, Teletype :> es) => Eff es ()
session = greet >> bump >> greet
  where
    greet = do { name <- readTTY; writeTTY ("Hello, " ++ name) }
    bump  = modify (+ 1)

-- Production handler: interpret Teletype via IO.
runTeletypeIO :: IOE :> es => Eff (Teletype : es) a -> Eff es a
runTeletypeIO = interpret $ \_ -> \case
  ReadTTY    -> liftIO getLine
  WriteTTY s -> liftIO (putStrLn s)

main :: IO ()
main = runEff . runTeletypeIO . evalState (0 :: Int) $ session

-- Reinterpretation for tests: a pure handler, no IOE required. Same `session`.
runTeletypePure :: [String] -> Eff (Teletype : es) a -> Eff es (a, [String])
runTeletypePure _input = reinterpret (runState []) $ \_ -> \case
  ReadTTY    -> pure "<canned>"
  WriteTTY s -> modify (++ [s])
