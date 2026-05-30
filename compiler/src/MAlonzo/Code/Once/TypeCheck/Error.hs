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
    C_UnboundQualified_14 MAlonzo.Code.Agda.Builtin.String.T_String_6
                          MAlonzo.Code.Agda.Builtin.String.T_String_6 |
    C_LambdaInInferMode_16 | C_LambdaRequiresFunctionType_18 |
    C_InlInInferMode_20 | C_InrInInferMode_22 |
    C_InitialInInferMode_24 | C_InlNeedsSumType_26 |
    C_InrNeedsSumType_28 | C_FstNeedsPair_30 | C_SndNeedsPair_32 |
    C_ArrNeedsFunction_34 | C_NegationNotInt_36 |
    C_CaseScrutineeNotSum_38 | C_CaseBranchMismatch_40 |
    C_ApplicationTypeMismatch_46 MAlonzo.Code.Once.Type.T_Type_108
                                 MAlonzo.Code.Once.Type.T_Type_108 |
    C_TypeMismatch_52 MAlonzo.Code.Once.Type.T_Type_108
                      MAlonzo.Code.Once.Type.T_Type_108 |
    C_NotFunction_56 MAlonzo.Code.Once.Type.T_Type_108 |
    C_UsageViolation_64 MAlonzo.Code.Agda.Builtin.String.T_String_6
                        MAlonzo.Code.Once.Type.T_Quantity_4
                        MAlonzo.Code.Once.Type.T_Quantity_4 |
    C_BuiltinTypeMismatch_68 MAlonzo.Code.Agda.Builtin.String.T_String_6 |
    C_BinOpLeftError_70 T_TypeError_6 |
    C_BinOpRightError_72 T_TypeError_6 |
    C_UnclassifiedError_74 MAlonzo.Code.Agda.Builtin.String.T_String_6
-- Once.TypeCheck.Error.renderError
d_renderError_76 ::
  T_TypeError_6 -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_renderError_76 v0
  = case coe v0 of
      C_UnboundVariable_8 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("Unbound or unspecialized variable: " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20 v1
                (" (polymorphic builtins must appear applied or in check mode)"
                 ::
                 Data.Text.Text))
      C_UnboundQualified_14 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("Unbound qualified variable: " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20 v1
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   ("@" :: Data.Text.Text) v2))
      C_LambdaInInferMode_16
        -> coe
             ("Lambda without type annotation not supported in inference mode."
              ::
              Data.Text.Text)
      C_LambdaRequiresFunctionType_18
        -> coe ("Lambda requires function type" :: Data.Text.Text)
      C_InlInInferMode_20
        -> coe
             ("inl requires check mode (needs target sum type)"
              ::
              Data.Text.Text)
      C_InrInInferMode_22
        -> coe
             ("inr requires check mode (needs target sum type)"
              ::
              Data.Text.Text)
      C_InitialInInferMode_24
        -> coe
             ("initial requires check mode (needs target type)"
              ::
              Data.Text.Text)
      C_InlNeedsSumType_26
        -> coe ("inl expects a sum type in check mode" :: Data.Text.Text)
      C_InrNeedsSumType_28
        -> coe ("inr expects a sum type in check mode" :: Data.Text.Text)
      C_FstNeedsPair_30
        -> coe ("fst requires a pair argument" :: Data.Text.Text)
      C_SndNeedsPair_32
        -> coe ("snd requires a pair argument" :: Data.Text.Text)
      C_ArrNeedsFunction_34
        -> coe
             ("arr requires a function argument (A \8594 B)" :: Data.Text.Text)
      C_NegationNotInt_36
        -> coe ("Negation requires Int operand" :: Data.Text.Text)
      C_CaseScrutineeNotSum_38
        -> coe ("Case requires a sum-typed scrutinee" :: Data.Text.Text)
      C_CaseBranchMismatch_40
        -> coe ("Case branches have different types" :: Data.Text.Text)
      C_ApplicationTypeMismatch_46 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("Application: argument type " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (MAlonzo.Code.Once.Type.d_showType_198 (coe v2))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (" does not match function domain " :: Data.Text.Text)
                   (MAlonzo.Code.Once.Type.d_showType_198 (coe v1))))
      C_TypeMismatch_52 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("Type mismatch: expected " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (MAlonzo.Code.Once.Type.d_showType_198 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (" but got " :: Data.Text.Text)
                   (MAlonzo.Code.Once.Type.d_showType_198 (coe v2))))
      C_NotFunction_56 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("expected function type, got " :: Data.Text.Text)
             (MAlonzo.Code.Once.Type.d_showType_198 (coe v1))
      C_UsageViolation_64 v1 v2 v3
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("Parameter '" :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20 v1
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   ("' used with quantity " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (MAlonzo.Code.Once.Type.d_showQuantity_30 (coe v3))
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         (" but declared with quantity " :: Data.Text.Text)
                         (MAlonzo.Code.Once.Type.d_showQuantity_30 (coe v2))))))
      C_BuiltinTypeMismatch_68 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20 v1
             (": expected type mismatch" :: Data.Text.Text)
      C_BinOpLeftError_70 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("binop left: " :: Data.Text.Text) (d_renderError_76 (coe v1))
      C_BinOpRightError_72 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("binop right: " :: Data.Text.Text) (d_renderError_76 (coe v1))
      C_UnclassifiedError_74 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
