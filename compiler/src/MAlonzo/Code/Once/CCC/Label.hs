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

module MAlonzo.Code.Once.CCC.Label where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.Bool.Base
import qualified MAlonzo.Code.Data.String.Properties

-- Once.CCC.Label.Label
d_Label_6 = ()
data T_Label_6
  = C_once_8 Integer |
    C_sigop_10 MAlonzo.Code.Agda.Builtin.String.T_String_6 Integer |
    C_thunk_12 Integer
-- Once.CCC.Label._≡ᵇᴸ_
d__'8801''7495''7480'__14 :: T_Label_6 -> T_Label_6 -> Bool
d__'8801''7495''7480'__14 v0 v1
  = let v2 = coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
    coe
      (case coe v0 of
         C_once_8 v3
           -> case coe v1 of
                C_once_8 v4 -> coe eqInt (coe v3) (coe v4)
                _ -> coe v2
         C_sigop_10 v3 v4
           -> case coe v1 of
                C_sigop_10 v5 v6
                  -> coe
                       MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                       (coe
                          MAlonzo.Code.Data.String.Properties.d__'61''61'__86 (coe v3)
                          (coe v5))
                       (coe eqInt (coe v4) (coe v6))
                _ -> coe v2
         C_thunk_12 v3
           -> case coe v1 of
                C_thunk_12 v4 -> coe eqInt (coe v3) (coe v4)
                _ -> coe v2
         _ -> MAlonzo.RTE.mazUnreachableError)
