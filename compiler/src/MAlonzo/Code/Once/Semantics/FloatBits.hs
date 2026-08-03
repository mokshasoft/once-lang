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

module MAlonzo.Code.Once.Semantics.FloatBits where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Float
import qualified MAlonzo.Code.Data.Float.Base
import qualified MAlonzo.Code.Data.Maybe.Base

-- Once.Semantics.FloatBits.float-bits
d_float'45'bits_6 ::
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 -> Integer
d_float'45'bits_6 v0
  = coe
      MAlonzo.Code.Data.Maybe.Base.du_maybe'8242'_44 word64ToNat
      (0 :: Integer) (coe MAlonzo.Code.Data.Float.Base.d_toWord_14 v0)
