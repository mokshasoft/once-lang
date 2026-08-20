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
data T_NumType_6 = C_NInt_8 | C_NFloat_10
-- Once.Arith.Type.isFloat
d_isFloat_12 :: T_NumType_6 -> Bool
d_isFloat_12 v0
  = case coe v0 of
      C_NInt_8 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      C_NFloat_10 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Type.isInteger
d_isInteger_14 :: T_NumType_6 -> Bool
d_isInteger_14 v0
  = case coe v0 of
      C_NInt_8 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      C_NFloat_10 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Type.RegClass
d_RegClass_16 = ()
data T_RegClass_16 = C_GPR_18 | C_XMM_20
-- Once.Arith.Type.regClass
d_regClass_22 :: T_NumType_6 -> T_RegClass_16
d_regClass_22 v0
  = case coe v0 of
      C_NInt_8 -> coe C_GPR_18
      C_NFloat_10 -> coe C_XMM_20
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Type.⟦_⟧N
d_'10214'_'10215'N_24 :: T_NumType_6 -> ()
d_'10214'_'10215'N_24 = erased
-- Once.Arith.Type._≟N_
d__'8799'N__26 a0 a1 = ()
data T__'8799'N__26 = C_refl'45'NInt_28 | C_refl'45'NFloat_30
-- Once.Arith.Type.≟N-to-≡
d_'8799'N'45'to'45''8801'_36 ::
  T_NumType_6 ->
  T_NumType_6 ->
  T__'8799'N__26 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8799'N'45'to'45''8801'_36 = erased
