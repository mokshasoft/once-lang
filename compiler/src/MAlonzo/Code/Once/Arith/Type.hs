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

module MAlonzo.Code.Once.Arith.Type where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.Equality

-- Once.Arith.Type.NumType
d_NumType_6 = ()
data T_NumType_6
  = C_I8_8 | C_I16_10 | C_I32_12 | C_I64_14 | C_F32_16 | C_F64_18
-- Once.Arith.Type.bitwidth
d_bitwidth_20 :: T_NumType_6 -> Integer
d_bitwidth_20 v0
  = case coe v0 of
      C_I8_8 -> coe (8 :: Integer)
      C_I16_10 -> coe (16 :: Integer)
      C_I32_12 -> coe (32 :: Integer)
      C_I64_14 -> coe (64 :: Integer)
      C_F32_16 -> coe (32 :: Integer)
      C_F64_18 -> coe (64 :: Integer)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Type.isFloat
d_isFloat_22 :: T_NumType_6 -> Bool
d_isFloat_22 v0
  = case coe v0 of
      C_I8_8 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      C_I16_10 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      C_I32_12 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      C_I64_14 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      C_F32_16 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      C_F64_18 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Type.isInteger
d_isInteger_24 :: T_NumType_6 -> Bool
d_isInteger_24 v0
  = case coe v0 of
      C_I8_8 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      C_I16_10 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      C_I32_12 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      C_I64_14 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      C_F32_16 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      C_F64_18 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Type.RegClass
d_RegClass_26 = ()
data T_RegClass_26 = C_GPR_28 | C_XMM_30
-- Once.Arith.Type.regClass
d_regClass_32 :: T_NumType_6 -> T_RegClass_26
d_regClass_32 v0
  = case coe v0 of
      C_I8_8 -> coe C_GPR_28
      C_I16_10 -> coe C_GPR_28
      C_I32_12 -> coe C_GPR_28
      C_I64_14 -> coe C_GPR_28
      C_F32_16 -> coe C_XMM_30
      C_F64_18 -> coe C_XMM_30
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Type.⟦_⟧N
d_'10214'_'10215'N_34 :: T_NumType_6 -> ()
d_'10214'_'10215'N_34 = erased
-- Once.Arith.Type._≟N_
d__'8799'N__36 a0 a1 = ()
data T__'8799'N__36
  = C_refl'45'I8_38 | C_refl'45'I16_40 | C_refl'45'I32_42 |
    C_refl'45'I64_44 | C_refl'45'F32_46 | C_refl'45'F64_48
-- Once.Arith.Type.≟N-to-≡
d_'8799'N'45'to'45''8801'_54 ::
  T_NumType_6 ->
  T_NumType_6 ->
  T__'8799'N__36 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8799'N'45'to'45''8801'_54 = erased
