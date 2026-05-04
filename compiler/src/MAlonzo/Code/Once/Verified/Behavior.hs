{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-# OPTIONS_GHC -Wno-overlapping-patterns #-}

module MAlonzo.Code.Once.Verified.Behavior where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text

-- Once.Verified.Behavior.Behavior
d_Behavior_6 :: ()
d_Behavior_6 = erased
-- Once.Verified.Behavior.Source
d_Source_8 :: ()
d_Source_8 = erased
-- Once.Verified.Behavior.⟦_⟧
d_'10214'_'10215'_10
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Verified.Behavior.\10214_\10215"
