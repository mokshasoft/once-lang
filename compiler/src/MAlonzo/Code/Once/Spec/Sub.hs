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

module MAlonzo.Code.Once.Spec.Sub where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Once.Spec.Grade
import qualified MAlonzo.Code.Once.Spec.Type

-- Once.Spec.Sub._<:_
d__'60''58'__8 a0 a1 a2 = ()
data T__'60''58'__8
  = C_sub'45'void_14 | C_sub'45'var_18 | C_sub'45'unit_20 |
    C_sub'45'int_22 | C_sub'45'float_24 |
    C_sub'45'arr_40 T__'60''58'__8 T__'60''58'__8
                    MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 |
    C_sub'45''42'_50 T__'60''58'__8 T__'60''58'__8 |
    C_sub'45''43'_60 T__'60''58'__8 T__'60''58'__8 | C_sub'45'μ_64 |
    C_sub'45'ν_72 MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50
-- Once.Spec.Sub._<:ᶜ_
d__'60''58''7580'__76 a0 a1 a2 = ()
data T__'60''58''7580'__76
  = C_sub'7580''45'void_82 | C_sub'7580''45'var_86 |
    C_sub'7580''45'unit_88 | C_sub'7580''45'int_90 |
    C_sub'7580''45'float_92 |
    C_sub'7580''45'arr_106 T__'60''58''7580'__76
                           MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 |
    C_sub'7580''45''42'_116 T__'60''58''7580'__76
                            T__'60''58''7580'__76 |
    C_sub'7580''45''43'_126 T__'60''58''7580'__76
                            T__'60''58''7580'__76 |
    C_sub'7580''45'μ_130 |
    C_sub'7580''45'ν_138 MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50
-- Once.Spec.Sub._⊔_≔_
d__'8852'_'8788'__148 a0 a1 a2 a3 = ()
data T__'8852'_'8788'__148
  = C_constructor_174 T__'60''58''7580'__76 T__'60''58''7580'__76
                      (MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
                       T__'60''58''7580'__76 ->
                       T__'60''58''7580'__76 -> T__'60''58''7580'__76)
-- Once.Spec.Sub._⊔_≔_.left
d_left_166 :: T__'8852'_'8788'__148 -> T__'60''58''7580'__76
d_left_166 v0
  = case coe v0 of
      C_constructor_174 v1 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Sub._⊔_≔_.right
d_right_168 :: T__'8852'_'8788'__148 -> T__'60''58''7580'__76
d_right_168 v0
  = case coe v0 of
      C_constructor_174 v1 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Sub._⊔_≔_.least
d_least_172 ::
  T__'8852'_'8788'__148 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  T__'60''58''7580'__76 ->
  T__'60''58''7580'__76 -> T__'60''58''7580'__76
d_least_172 v0
  = case coe v0 of
      C_constructor_174 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
