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

module MAlonzo.Code.Once.Spec.Type.Sub where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Once.Spec.Type
import qualified MAlonzo.Code.Once.Spec.Type.Grade

-- Once.Spec.Type.Sub._⊑π_
d__'8849'π__8 a0 a1 = ()
data T__'8849'π__8
  = C_'8849''45'pure_10 | C_'8849''45'eff_12 | C_'8849''45'pe_14
-- Once.Spec.Type.Sub.pure⊑
d_pure'8849'_18 ::
  MAlonzo.Code.Once.Spec.Type.Grade.T_Purity_28 -> T__'8849'π__8
d_pure'8849'_18 v0
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Type.Grade.C_pure_30
        -> coe C_'8849''45'pure_10
      MAlonzo.Code.Once.Spec.Type.Grade.C_eff_32 -> coe C_'8849''45'pe_14
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Type.Sub._<:_
d__'60''58'__20 a0 a1 = ()
data T__'60''58'__20
  = C_sub'45'void_24 | C_sub'45'unit_26 | C_sub'45'int_28 |
    C_sub'45'float_30 |
    C_sub'45'arr_46 T__'60''58'__20 T__'60''58'__20 T__'8849'π__8 |
    C_sub'45'prod_56 T__'60''58'__20 T__'60''58'__20 |
    C_sub'45'sum_66 T__'60''58'__20 T__'60''58'__20 | C_sub'45'μ_70 |
    C_sub'45'ν_78 T__'8849'π__8 | C_sub'45'rigid_84
