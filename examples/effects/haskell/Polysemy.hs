-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson
--
-- polysemy version of the State + Teletype program (cf. Once examples 03-05).
-- Illustrative: shows algebraic effects with a type-level row.
--
-- Closest in spirit to OCP-0007: effects are an unordered ROW (here via
-- `Member` constraints), handlers DISCHARGE rows, and order is handler order.
-- The key difference from Once: `Sem r` builds a free-monad tree that is
-- INTERPRETED at runtime, and you thread `Member`/`Sem` plumbing explicitly.

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeOperators #-}

module Polysemy where

import Polysemy
import Polysemy.State

-- Declare the Teletype effect as a GADT, then generate the smart constructors.
data Teletype m a where
  ReadTTY  :: Teletype m String
  WriteTTY :: String -> Teletype m ()

makeSem ''Teletype

-- The effect set is a ROW in the type: `Members '[State Int, Teletype] r`.
session :: Members '[State Int, Teletype] r => Sem r ()
session = greet >> bump >> greet
  where
    greet = do { name <- readTTY; writeTTY ("Hello, " ++ name) }
    bump  = modify (+ 1)

-- Production handler: discharge Teletype onto IO.
teletypeToIO :: Member (Embed IO) r => Sem (Teletype ': r) a -> Sem r a
teletypeToIO = interpret $ \case
  ReadTTY    -> embed getLine
  WriteTTY s -> embed (putStrLn s)

-- Run: peel handlers (handler ORDER decides semantics).
main :: IO ()
main = runM . teletypeToIO . fmap snd . runState (0 :: Int) $ session

-- Reinterpretation for tests: swap ONE handler — collect output, no IO.
-- The SAME `session` is reused (this is the modularity polysemy/Once share).
teletypePure :: Sem (Teletype ': r) a -> Sem r (a, [String])
teletypePure = fmap (\(o, a) -> (a, o)) . runOutputAsList
  where runOutputAsList = undefined  -- sketch: accumulate WriteTTY, canned ReadTTY
