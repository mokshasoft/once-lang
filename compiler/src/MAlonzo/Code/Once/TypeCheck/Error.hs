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
import qualified MAlonzo.Code.Once.Spec.Grade
import qualified MAlonzo.Code.Once.Spec.Surface.Syntax
import qualified MAlonzo.Code.Once.Spec.Type
import qualified MAlonzo.Code.Once.Type

-- Once.TypeCheck.Error.TypeError
d_TypeError_6 = ()
data T_TypeError_6
  = C_UnboundVariable_8 MAlonzo.Code.Agda.Builtin.String.T_String_6 |
    C_UnboundQualified_14 MAlonzo.Code.Agda.Builtin.String.T_String_6
                          MAlonzo.Code.Agda.Builtin.String.T_String_6 |
    C_NonConcreteSigOpType_20 MAlonzo.Code.Agda.Builtin.String.T_String_6
                              MAlonzo.Code.Once.Spec.Type.T_Ty_8 |
    C_LambdaInInferMode_22 | C_LambdaRequiresFunctionType_24 |
    C_InlInInferMode_26 | C_InrInInferMode_28 |
    C_InitialInInferMode_30 |
    C_GeneratorInInferMode_34 MAlonzo.Code.Agda.Builtin.String.T_String_6 |
    C_InlNeedsSumType_36 | C_InrNeedsSumType_38 | C_FstNeedsPair_40 |
    C_SndNeedsPair_42 | C_CaseScrutineeNotSum_44 |
    C_CaseBranchMismatch_46 |
    C_TypeMismatch_54 Integer MAlonzo.Code.Once.Spec.Type.T_Ty_8
                      MAlonzo.Code.Once.Spec.Type.T_Ty_8 |
    C_NotFunction_60 Integer MAlonzo.Code.Once.Spec.Type.T_Ty_8 |
    C_UsageViolation_68 MAlonzo.Code.Agda.Builtin.String.T_String_6
                        MAlonzo.Code.Once.Spec.Grade.T_Quantity_6
                        MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 |
    C_BuiltinTypeMismatch_72 MAlonzo.Code.Agda.Builtin.String.T_String_6 |
    C_NoInstance_82 Integer MAlonzo.Code.Agda.Builtin.String.T_String_6
                    MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10
                    MAlonzo.Code.Once.Spec.Type.T_Ty_8 |
    C_ComposeMiddleUndetermined_84 |
    C_BinOpLeftError_86 T_TypeError_6 |
    C_BinOpRightError_88 T_TypeError_6
-- Once.TypeCheck.Error.renderError
d_renderError_90 ::
  T_TypeError_6 -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_renderError_90 v0
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
                      (MAlonzo.Code.Once.Type.d_showType_36
                         (coe (0 :: Integer)) (coe v2))
                      (" (FFI/SigOp references must be base types or first-order function pointers)"
                       ::
                       Data.Text.Text))))
      C_LambdaInInferMode_22
        -> coe
             ("Lambda without type annotation not supported in inference mode."
              ::
              Data.Text.Text)
      C_LambdaRequiresFunctionType_24
        -> coe ("Lambda requires function type" :: Data.Text.Text)
      C_InlInInferMode_26
        -> coe
             ("inl requires check mode (needs target sum type)"
              ::
              Data.Text.Text)
      C_InrInInferMode_28
        -> coe
             ("inr requires check mode (needs target sum type)"
              ::
              Data.Text.Text)
      C_InitialInInferMode_30
        -> coe
             ("initial requires check mode (needs target type)"
              ::
              Data.Text.Text)
      C_GeneratorInInferMode_34 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20 v1
             (" requires check mode (needs target type)" :: Data.Text.Text)
      C_InlNeedsSumType_36
        -> coe ("inl expects a sum type in check mode" :: Data.Text.Text)
      C_InrNeedsSumType_38
        -> coe ("inr expects a sum type in check mode" :: Data.Text.Text)
      C_FstNeedsPair_40
        -> coe ("fst requires a pair argument" :: Data.Text.Text)
      C_SndNeedsPair_42
        -> coe ("snd requires a pair argument" :: Data.Text.Text)
      C_CaseScrutineeNotSum_44
        -> coe ("Case requires a sum-typed scrutinee" :: Data.Text.Text)
      C_CaseBranchMismatch_46
        -> coe ("Case branches have different types" :: Data.Text.Text)
      C_TypeMismatch_54 v1 v2 v3
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("Type mismatch: expected " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (MAlonzo.Code.Once.Type.d_showType_36 (coe v1) (coe v2))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (" but got " :: Data.Text.Text)
                   (MAlonzo.Code.Once.Type.d_showType_36 (coe v1) (coe v3))))
      C_NotFunction_60 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("expected function type, got " :: Data.Text.Text)
             (MAlonzo.Code.Once.Type.d_showType_36 (coe v1) (coe v2))
      C_UsageViolation_68 v1 v2 v3
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
                      (MAlonzo.Code.Once.Type.d_showQuantity_4 (coe v3))
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         (" but declared with quantity " :: Data.Text.Text)
                         (MAlonzo.Code.Once.Type.d_showQuantity_4 (coe v2))))))
      C_BuiltinTypeMismatch_72 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20 v1
             (": expected type mismatch" :: Data.Text.Text)
      C_NoInstance_82 v1 v2 v3 v4
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20 v2
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (": " :: Data.Text.Text)
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (MAlonzo.Code.Once.Type.d_showType_36 (coe v1) (coe v4))
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (" is not an instance of " :: Data.Text.Text)
                      (MAlonzo.Code.Once.Type.d_showPolyType_134 (coe v3)))))
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
             ("binop left: " :: Data.Text.Text) (d_renderError_90 (coe v1))
      C_BinOpRightError_88 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("binop right: " :: Data.Text.Text) (d_renderError_90 (coe v1))
      _ -> MAlonzo.RTE.mazUnreachableError
