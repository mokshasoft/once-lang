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
import qualified MAlonzo.Code.Once.Spec.Surface.Operator
import qualified MAlonzo.Code.Once.Spec.Surface.Syntax
import qualified MAlonzo.Code.Once.Spec.Theory
import qualified MAlonzo.Code.Once.Spec.Type
import qualified MAlonzo.Code.Once.Type

-- Once.TypeCheck.Error.dottableText
d_dottableText_6 ::
  MAlonzo.Code.Once.Spec.Surface.Operator.T_Dottable_8 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_dottableText_6 v0
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Surface.Operator.C_o'43'_10
        -> coe ("+" :: Data.Text.Text)
      MAlonzo.Code.Once.Spec.Surface.Operator.C_o'45'_12
        -> coe ("-" :: Data.Text.Text)
      MAlonzo.Code.Once.Spec.Surface.Operator.C_o'42'_14
        -> coe ("*" :: Data.Text.Text)
      MAlonzo.Code.Once.Spec.Surface.Operator.C_o'47'_16
        -> coe ("/" :: Data.Text.Text)
      MAlonzo.Code.Once.Spec.Surface.Operator.C_o'60'_18
        -> coe ("<" :: Data.Text.Text)
      MAlonzo.Code.Once.Spec.Surface.Operator.C_o'60''61'_20
        -> coe ("<=" :: Data.Text.Text)
      MAlonzo.Code.Once.Spec.Surface.Operator.C_o'62'_22
        -> coe (">" :: Data.Text.Text)
      MAlonzo.Code.Once.Spec.Surface.Operator.C_o'62''61'_24
        -> coe (">=" :: Data.Text.Text)
      MAlonzo.Code.Once.Spec.Surface.Operator.C_o'61''61'_26
        -> coe ("==" :: Data.Text.Text)
      MAlonzo.Code.Once.Spec.Surface.Operator.C_o'33''61'_28
        -> coe ("!=" :: Data.Text.Text)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Error.opText
d_opText_8 ::
  MAlonzo.Code.Once.Spec.Surface.Operator.T_BinOp_36 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_opText_8 v0
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Surface.Operator.C_plain_38 v1
        -> case coe v1 of
             MAlonzo.Code.Once.Spec.Surface.Operator.C_'8249'_'8250'_32 v2
               -> coe d_dottableText_6 (coe v2)
             MAlonzo.Code.Once.Spec.Surface.Operator.C_o'37'_34
               -> coe ("%" :: Data.Text.Text)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Surface.Operator.C_dotted_40 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             (d_dottableText_6 (coe v1)) ("." :: Data.Text.Text)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Error.numTyText
d_numTyText_14 ::
  MAlonzo.Code.Once.Spec.Theory.T_NumTy_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_numTyText_14 v0
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Theory.C_int_8
        -> coe ("Int" :: Data.Text.Text)
      MAlonzo.Code.Once.Spec.Theory.C_float_10
        -> coe ("Float" :: Data.Text.Text)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Error.undefinedHint
d_undefinedHint_16 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Theory.T_NumTy_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_undefinedHint_16 v0 v1
  = let v2 = "" :: Data.Text.Text in
    coe
      (case coe v0 of
         l | (==) l ("!=." :: Data.Text.Text) ->
             case coe v1 of
               MAlonzo.Code.Once.Spec.Theory.C_int_8
                 -> coe (": use `!=`" :: Data.Text.Text)
               _ -> coe v2
         l | (==) l ("%" :: Data.Text.Text) ->
             case coe v1 of
               MAlonzo.Code.Once.Spec.Theory.C_float_10
                 -> coe (", which has no remainder" :: Data.Text.Text)
               _ -> coe v2
         l | (==) l ("*" :: Data.Text.Text) ->
             case coe v1 of
               MAlonzo.Code.Once.Spec.Theory.C_float_10
                 -> coe
                      (", whose multiplication rounds: use `*.`" :: Data.Text.Text)
               _ -> coe v2
         l | (==) l ("*." :: Data.Text.Text) ->
             case coe v1 of
               MAlonzo.Code.Once.Spec.Theory.C_int_8
                 -> coe
                      (", whose multiplication is exact: use `*`" :: Data.Text.Text)
               _ -> coe v2
         l | (==) l ("+" :: Data.Text.Text) ->
             case coe v1 of
               MAlonzo.Code.Once.Spec.Theory.C_float_10
                 -> coe (", whose addition rounds: use `+.`" :: Data.Text.Text)
               _ -> coe v2
         l | (==) l ("+." :: Data.Text.Text) ->
             case coe v1 of
               MAlonzo.Code.Once.Spec.Theory.C_int_8
                 -> coe (", whose addition is exact: use `+`" :: Data.Text.Text)
               _ -> coe v2
         l | (==) l ("-" :: Data.Text.Text) ->
             case coe v1 of
               MAlonzo.Code.Once.Spec.Theory.C_float_10
                 -> coe (", whose subtraction rounds: use `-.`" :: Data.Text.Text)
               _ -> coe v2
         l | (==) l ("-." :: Data.Text.Text) ->
             case coe v1 of
               MAlonzo.Code.Once.Spec.Theory.C_int_8
                 -> coe (", whose subtraction is exact: use `-`" :: Data.Text.Text)
               _ -> coe v2
         l | (==) l ("/" :: Data.Text.Text) ->
             case coe v1 of
               MAlonzo.Code.Once.Spec.Theory.C_float_10
                 -> coe (", whose division rounds: use `/.`" :: Data.Text.Text)
               _ -> coe v2
         l | (==) l ("/." :: Data.Text.Text) ->
             case coe v1 of
               MAlonzo.Code.Once.Spec.Theory.C_int_8
                 -> coe
                      (", whose division is on integers: use `/`" :: Data.Text.Text)
               _ -> coe v2
         l | (==) l ("<." :: Data.Text.Text) ->
             case coe v1 of
               MAlonzo.Code.Once.Spec.Theory.C_int_8
                 -> coe (": use `<`" :: Data.Text.Text)
               _ -> coe v2
         l | (==) l ("<=." :: Data.Text.Text) ->
             case coe v1 of
               MAlonzo.Code.Once.Spec.Theory.C_int_8
                 -> coe (": use `<=`" :: Data.Text.Text)
               _ -> coe v2
         l | (==) l ("==." :: Data.Text.Text) ->
             case coe v1 of
               MAlonzo.Code.Once.Spec.Theory.C_int_8
                 -> coe (": use `==`" :: Data.Text.Text)
               _ -> coe v2
         l | (==) l (">." :: Data.Text.Text) ->
             case coe v1 of
               MAlonzo.Code.Once.Spec.Theory.C_int_8
                 -> coe (": use `>`" :: Data.Text.Text)
               _ -> coe v2
         l | (==) l (">=." :: Data.Text.Text) ->
             case coe v1 of
               MAlonzo.Code.Once.Spec.Theory.C_int_8
                 -> coe (": use `>=`" :: Data.Text.Text)
               _ -> coe v2
         _ -> coe v2)
-- Once.TypeCheck.Error.TypeError
d_TypeError_18 = ()
data T_TypeError_18
  = C_UnboundVariable_20 MAlonzo.Code.Agda.Builtin.String.T_String_6 |
    C_UnboundQualified_26 MAlonzo.Code.Agda.Builtin.String.T_String_6
                          MAlonzo.Code.Agda.Builtin.String.T_String_6 |
    C_NonConcreteSigOpType_32 MAlonzo.Code.Agda.Builtin.String.T_String_6
                              MAlonzo.Code.Once.Spec.Type.T_Ty_8 |
    C_LambdaInInferMode_34 | C_LambdaRequiresFunctionType_36 |
    C_InlInInferMode_38 | C_InrInInferMode_40 |
    C_InitialInInferMode_42 |
    C_GeneratorInInferMode_46 MAlonzo.Code.Agda.Builtin.String.T_String_6 |
    C_InlNeedsSumType_48 | C_InrNeedsSumType_50 | C_FstNeedsPair_52 |
    C_SndNeedsPair_54 | C_CaseScrutineeNotSum_56 |
    C_CaseBranchMismatch_58 |
    C_TypeMismatch_66 Integer MAlonzo.Code.Once.Spec.Type.T_Ty_8
                      MAlonzo.Code.Once.Spec.Type.T_Ty_8 |
    C_NotFunction_72 Integer MAlonzo.Code.Once.Spec.Type.T_Ty_8 |
    C_UsageViolation_80 MAlonzo.Code.Agda.Builtin.String.T_String_6
                        MAlonzo.Code.Once.Spec.Grade.T_Quantity_6
                        MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 |
    C_BuiltinTypeMismatch_84 MAlonzo.Code.Agda.Builtin.String.T_String_6 |
    C_NoInstance_94 Integer MAlonzo.Code.Agda.Builtin.String.T_String_6
                    MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10
                    MAlonzo.Code.Once.Spec.Type.T_Ty_8 |
    C_ComposeMiddleUndetermined_96 |
    C_OperatorUndefined_102 MAlonzo.Code.Agda.Builtin.String.T_String_6
                            MAlonzo.Code.Once.Spec.Theory.T_NumTy_6 |
    C_MixedOperands_106 MAlonzo.Code.Agda.Builtin.String.T_String_6 |
    C_NegativeZeroLiteral_108 | C_BinOpLeftError_110 T_TypeError_18 |
    C_BinOpRightError_112 T_TypeError_18
-- Once.TypeCheck.Error.renderError
d_renderError_114 ::
  T_TypeError_18 -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_renderError_114 v0
  = case coe v0 of
      C_UnboundVariable_20 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("Unbound or unspecialized variable: " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20 v1
                (" (polymorphic builtins must appear applied or in check mode)"
                 ::
                 Data.Text.Text))
      C_UnboundQualified_26 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("Unbound qualified variable: " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20 v1
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   ("@" :: Data.Text.Text) v2))
      C_NonConcreteSigOpType_32 v1 v2
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
      C_LambdaInInferMode_34
        -> coe
             ("Lambda without type annotation not supported in inference mode."
              ::
              Data.Text.Text)
      C_LambdaRequiresFunctionType_36
        -> coe ("Lambda requires function type" :: Data.Text.Text)
      C_InlInInferMode_38
        -> coe
             ("inl requires check mode (needs target sum type)"
              ::
              Data.Text.Text)
      C_InrInInferMode_40
        -> coe
             ("inr requires check mode (needs target sum type)"
              ::
              Data.Text.Text)
      C_InitialInInferMode_42
        -> coe
             ("initial requires check mode (needs target type)"
              ::
              Data.Text.Text)
      C_GeneratorInInferMode_46 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20 v1
             (" requires check mode (needs target type)" :: Data.Text.Text)
      C_InlNeedsSumType_48
        -> coe ("inl expects a sum type in check mode" :: Data.Text.Text)
      C_InrNeedsSumType_50
        -> coe ("inr expects a sum type in check mode" :: Data.Text.Text)
      C_FstNeedsPair_52
        -> coe ("fst requires a pair argument" :: Data.Text.Text)
      C_SndNeedsPair_54
        -> coe ("snd requires a pair argument" :: Data.Text.Text)
      C_CaseScrutineeNotSum_56
        -> coe ("Case requires a sum-typed scrutinee" :: Data.Text.Text)
      C_CaseBranchMismatch_58
        -> coe ("Case branches have different types" :: Data.Text.Text)
      C_TypeMismatch_66 v1 v2 v3
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
      C_NotFunction_72 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("expected function type, got " :: Data.Text.Text)
             (MAlonzo.Code.Once.Type.d_showType_36 (coe v1) (coe v2))
      C_UsageViolation_80 v1 v2 v3
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
      C_BuiltinTypeMismatch_84 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20 v1
             (": expected type mismatch" :: Data.Text.Text)
      C_NoInstance_94 v1 v2 v3 v4
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
      C_ComposeMiddleUndetermined_96
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
      C_OperatorUndefined_102 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("`" :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20 v1
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   ("` is not defined at " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_numTyText_14 (coe v2)) (d_undefinedHint_16 (coe v1) (coe v2)))))
      C_MixedOperands_106 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("`" :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20 v1
                ("` needs operands of one type: convert the Int with toFloat"
                 ::
                 Data.Text.Text))
      C_NegativeZeroLiteral_108
        -> coe
             ("the literal -0.0 is not allowed: write -(0.0) for negative zero"
              ::
              Data.Text.Text)
      C_BinOpLeftError_110 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("binop left: " :: Data.Text.Text) (d_renderError_114 (coe v1))
      C_BinOpRightError_112 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("binop right: " :: Data.Text.Text) (d_renderError_114 (coe v1))
      _ -> MAlonzo.RTE.mazUnreachableError
