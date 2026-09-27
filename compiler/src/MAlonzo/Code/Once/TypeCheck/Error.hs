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
    C_NonConcreteSigOpType_20 MAlonzo.Code.Agda.Builtin.String.T_String_6
                              MAlonzo.Code.Once.Type.T_Type_108 |
    C_DishonestSigOpType_26 MAlonzo.Code.Agda.Builtin.String.T_String_6
                            MAlonzo.Code.Once.Type.T_Type_108 |
    C_FloatLiteralUnsupported_28 | C_LambdaInInferMode_30 |
    C_LambdaRequiresFunctionType_32 | C_InlInInferMode_34 |
    C_InrInInferMode_36 | C_InitialInInferMode_38 |
    C_InlNeedsSumType_40 | C_InrNeedsSumType_42 | C_FstNeedsPair_44 |
    C_SndNeedsPair_46 | C_ArrNeedsFunction_48 | C_NegationNotInt_50 |
    C_CaseScrutineeNotSum_52 | C_CaseBranchMismatch_54 |
    C_ApplicationTypeMismatch_60 MAlonzo.Code.Once.Type.T_Type_108
                                 MAlonzo.Code.Once.Type.T_Type_108 |
    C_TypeMismatch_66 MAlonzo.Code.Once.Type.T_Type_108
                      MAlonzo.Code.Once.Type.T_Type_108 |
    C_NotFunction_70 MAlonzo.Code.Once.Type.T_Type_108 |
    C_UsageViolation_78 MAlonzo.Code.Agda.Builtin.String.T_String_6
                        MAlonzo.Code.Once.Type.T_Quantity_4
                        MAlonzo.Code.Once.Type.T_Quantity_4 |
    C_BuiltinTypeMismatch_82 MAlonzo.Code.Agda.Builtin.String.T_String_6 |
    C_ComposeMiddleUndetermined_84 |
    C_BinOpLeftError_86 T_TypeError_6 |
    C_BinOpRightError_88 T_TypeError_6 |
    C_UnclassifiedError_90 MAlonzo.Code.Agda.Builtin.String.T_String_6
-- Once.TypeCheck.Error.renderError
d_renderError_92 ::
  T_TypeError_6 -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_renderError_92 v0
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
      C_NonConcreteSigOpType_20 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("Reference '" :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20 v1
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   ("' has non-concrete type " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (MAlonzo.Code.Once.Type.d_showType_206 (coe v2))
                      (" (FFI/SigOp references must be base types or first-order function pointers)"
                       ::
                       Data.Text.Text))))
      C_DishonestSigOpType_26 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("Reference '" :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20 v1
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   ("' has type " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (MAlonzo.Code.Once.Type.d_showType_206 (coe v2))
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         (", which hides an effect: a SigOp returning Unit emits and one returning Void halts,"
                          ::
                          Data.Text.Text)
                         (" so its arrow must be Eff (and a bare Unit/Void constant is written Eff Unit Unit)"
                          ::
                          Data.Text.Text)))))
      C_FloatLiteralUnsupported_28
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("Float literals are not supported yet (the lexer and parser accept them; the"
              ::
              Data.Text.Text)
             (" elaborator's rule lands with plan 0.71 F3b)" :: Data.Text.Text)
      C_LambdaInInferMode_30
        -> coe
             ("Lambda without type annotation not supported in inference mode."
              ::
              Data.Text.Text)
      C_LambdaRequiresFunctionType_32
        -> coe ("Lambda requires function type" :: Data.Text.Text)
      C_InlInInferMode_34
        -> coe
             ("inl requires check mode (needs target sum type)"
              ::
              Data.Text.Text)
      C_InrInInferMode_36
        -> coe
             ("inr requires check mode (needs target sum type)"
              ::
              Data.Text.Text)
      C_InitialInInferMode_38
        -> coe
             ("initial requires check mode (needs target type)"
              ::
              Data.Text.Text)
      C_InlNeedsSumType_40
        -> coe ("inl expects a sum type in check mode" :: Data.Text.Text)
      C_InrNeedsSumType_42
        -> coe ("inr expects a sum type in check mode" :: Data.Text.Text)
      C_FstNeedsPair_44
        -> coe ("fst requires a pair argument" :: Data.Text.Text)
      C_SndNeedsPair_46
        -> coe ("snd requires a pair argument" :: Data.Text.Text)
      C_ArrNeedsFunction_48
        -> coe
             ("arr requires a function argument (A \8594 B)" :: Data.Text.Text)
      C_NegationNotInt_50
        -> coe ("Negation requires Int operand" :: Data.Text.Text)
      C_CaseScrutineeNotSum_52
        -> coe ("Case requires a sum-typed scrutinee" :: Data.Text.Text)
      C_CaseBranchMismatch_54
        -> coe ("Case branches have different types" :: Data.Text.Text)
      C_ApplicationTypeMismatch_60 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("Application: argument type " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (MAlonzo.Code.Once.Type.d_showType_206 (coe v2))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (" does not match function domain " :: Data.Text.Text)
                   (MAlonzo.Code.Once.Type.d_showType_206 (coe v1))))
      C_TypeMismatch_66 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("Type mismatch: expected " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (MAlonzo.Code.Once.Type.d_showType_206 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (" but got " :: Data.Text.Text)
                   (MAlonzo.Code.Once.Type.d_showType_206 (coe v2))))
      C_NotFunction_70 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("expected function type, got " :: Data.Text.Text)
             (MAlonzo.Code.Once.Type.d_showType_206 (coe v1))
      C_UsageViolation_78 v1 v2 v3
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
      C_BuiltinTypeMismatch_82 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20 v1
             (": expected type mismatch" :: Data.Text.Text)
      C_ComposeMiddleUndetermined_84
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("compose: cannot determine the middle type \8212 neither the second argument's "
              ::
              Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                ("output (given its input) nor the first argument's input is known; "
                 ::
                 Data.Text.Text)
                ("annotate one of them" :: Data.Text.Text))
      C_BinOpLeftError_86 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("binop left: " :: Data.Text.Text) (d_renderError_92 (coe v1))
      C_BinOpRightError_88 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("binop right: " :: Data.Text.Text) (d_renderError_92 (coe v1))
      C_UnclassifiedError_90 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
