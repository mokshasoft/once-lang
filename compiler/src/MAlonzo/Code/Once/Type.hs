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

module MAlonzo.Code.Once.Type where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.String

-- Once.Type.Type
d_Type_4 = ()
data T_Type_4
  = C_Unit_6 | C_Void_8 | C__'42'__10 T_Type_4 T_Type_4 |
    C__'43'__12 T_Type_4 T_Type_4 | C__'8658'__14 T_Type_4 T_Type_4 |
    C_Eff_16 T_Type_4 T_Type_4 | C_Fix_18 T_Type_4 | C_Int_20 |
    C_Float_22 | C_Str_24 | C_Buffer_26 |
    C_TVar_28 MAlonzo.Code.Agda.Builtin.String.T_String_6
-- Once.Type.IO
d_IO_30 :: T_Type_4 -> T_Type_4
d_IO_30 v0 = coe C_Eff_16 (coe C_Unit_6) (coe v0)
