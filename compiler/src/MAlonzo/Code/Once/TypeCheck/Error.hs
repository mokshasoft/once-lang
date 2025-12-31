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

module MAlonzo.Code.Once.TypeCheck.Error where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.String.Base
import qualified MAlonzo.Code.Once.Type

-- Once.TypeCheck.Error.TypeError
d_TypeError_6 = ()
data T_TypeError_6
  = C_UnboundVariable_8 MAlonzo.Code.Agda.Builtin.String.T_String_6 |
    C_TypeMismatch_10 MAlonzo.Code.Once.Type.T_Type_32
                      MAlonzo.Code.Once.Type.T_Type_32 |
    C_NotAFunction_12 MAlonzo.Code.Once.Type.T_Type_32 |
    C_NotAProduct_14 MAlonzo.Code.Once.Type.T_Type_32 |
    C_NotASum_16 MAlonzo.Code.Once.Type.T_Type_32 |
    C_OccursCheck_18 MAlonzo.Code.Agda.Builtin.String.T_String_6
                     MAlonzo.Code.Once.Type.T_Type_32 |
    C_UnificationError_20 MAlonzo.Code.Once.Type.T_Type_32
                          MAlonzo.Code.Once.Type.T_Type_32 |
    C_ArityMismatch_22 MAlonzo.Code.Agda.Builtin.String.T_String_6
                       Integer Integer |
    C_SignatureMismatch_24 MAlonzo.Code.Once.Type.T_Type_32
                           MAlonzo.Code.Once.Type.T_Type_32 |
    C_LinearUsedMultiple_26 MAlonzo.Code.Agda.Builtin.String.T_String_6
                            Integer |
    C_LinearUnused_28 MAlonzo.Code.Agda.Builtin.String.T_String_6 |
    C_ErasedUsedAtRuntime_30 MAlonzo.Code.Agda.Builtin.String.T_String_6 |
    C_QuantityMismatch_32 MAlonzo.Code.Agda.Builtin.String.T_String_6
                          MAlonzo.Code.Once.Type.T_Quantity_4
                          MAlonzo.Code.Once.Type.T_Quantity_4 |
    C_ArithNonInteger_34 MAlonzo.Code.Once.Type.T_Type_32 |
    C_CompareNonInteger_36 MAlonzo.Code.Once.Type.T_Type_32
-- Once.TypeCheck.Error.errorMessage
d_errorMessage_38 ::
  T_TypeError_6 -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_errorMessage_38 v0
  = case coe v0 of
      C_UnboundVariable_8 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("Unbound variable: " :: Data.Text.Text) v1
      C_TypeMismatch_10 v1 v2 -> coe ("Type mismatch" :: Data.Text.Text)
      C_NotAFunction_12 v1 -> coe ("Not a function" :: Data.Text.Text)
      C_NotAProduct_14 v1 -> coe ("Not a product" :: Data.Text.Text)
      C_NotASum_16 v1 -> coe ("Not a sum" :: Data.Text.Text)
      C_OccursCheck_18 v1 v2
        -> coe ("Infinite type (occurs check)" :: Data.Text.Text)
      C_UnificationError_20 v1 v2
        -> coe ("Cannot unify types" :: Data.Text.Text)
      C_ArityMismatch_22 v1 v2 v3
        -> coe ("Wrong number of arguments" :: Data.Text.Text)
      C_SignatureMismatch_24 v1 v2
        -> coe ("Signature doesn't match inferred type" :: Data.Text.Text)
      C_LinearUsedMultiple_26 v1 v2
        -> coe ("Linear variable used multiple times" :: Data.Text.Text)
      C_LinearUnused_28 v1
        -> coe ("Linear variable not used" :: Data.Text.Text)
      C_ErasedUsedAtRuntime_30 v1
        -> coe ("Erased variable used at runtime" :: Data.Text.Text)
      C_QuantityMismatch_32 v1 v2 v3
        -> coe ("Quantity mismatch" :: Data.Text.Text)
      C_ArithNonInteger_34 v1
        -> coe
             ("Arithmetic operator requires integer operands" :: Data.Text.Text)
      C_CompareNonInteger_36 v1
        -> coe
             ("Comparison operator requires integer operands" :: Data.Text.Text)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Error.Result
d_Result_48 a0 = ()
data T_Result_48 = C_ok_52 AgdaAny | C_fail_54 T_TypeError_6
-- Once.TypeCheck.Error.mapResult
d_mapResult_60 ::
  () -> () -> (AgdaAny -> AgdaAny) -> T_Result_48 -> T_Result_48
d_mapResult_60 ~v0 ~v1 v2 v3 = du_mapResult_60 v2 v3
du_mapResult_60 ::
  (AgdaAny -> AgdaAny) -> T_Result_48 -> T_Result_48
du_mapResult_60 v0 v1
  = case coe v1 of
      C_ok_52 v2 -> coe C_ok_52 (coe v0 v2)
      C_fail_54 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Error.bindResult
d_bindResult_74 ::
  () -> () -> T_Result_48 -> (AgdaAny -> T_Result_48) -> T_Result_48
d_bindResult_74 ~v0 ~v1 v2 v3 = du_bindResult_74 v2 v3
du_bindResult_74 ::
  T_Result_48 -> (AgdaAny -> T_Result_48) -> T_Result_48
du_bindResult_74 v0 v1
  = case coe v0 of
      C_ok_52 v2 -> coe v1 v2
      C_fail_54 v2 -> coe v0
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Error._>>=_
d__'62''62''61'__88 ::
  () -> () -> T_Result_48 -> (AgdaAny -> T_Result_48) -> T_Result_48
d__'62''62''61'__88 ~v0 ~v1 = du__'62''62''61'__88
du__'62''62''61'__88 ::
  T_Result_48 -> (AgdaAny -> T_Result_48) -> T_Result_48
du__'62''62''61'__88 = coe du_bindResult_74
-- Once.TypeCheck.Error.return
d_return_92 :: () -> AgdaAny -> T_Result_48
d_return_92 ~v0 = du_return_92
du_return_92 :: AgdaAny -> T_Result_48
du_return_92 = coe C_ok_52
