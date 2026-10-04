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

module MAlonzo.Code.Once.TypeCheck.Raw where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Once.CanonicalName
import qualified MAlonzo.Code.Once.Type

-- Once.TypeCheck.Raw.BinOp
d_BinOp_6 = ()
data T_BinOp_6
  = C_OpAdd_8 | C_OpSub_10 | C_OpMul_12 | C_OpDiv_14 | C_OpMod_16 |
    C_OpLt_18 | C_OpLe_20 | C_OpGt_22 | C_OpGe_24 | C_OpEq_26 |
    C_OpNe_28
-- Once.TypeCheck.Raw.UnaryOp
d_UnaryOp_30 = ()
data T_UnaryOp_30 = C_OpNeg_32
-- Once.TypeCheck.Raw.RawExpr
d_RawExpr_34 = ()
data T_RawExpr_34
  = C_RVar_36 MAlonzo.Code.Agda.Builtin.String.T_String_6 |
    C_RQualified_38 MAlonzo.Code.Agda.Builtin.String.T_String_6
                    MAlonzo.Code.Agda.Builtin.String.T_String_6 |
    C_RResolved_40 MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 |
    C_RApp_42 T_RawExpr_34 T_RawExpr_34 |
    C_RLam_44 MAlonzo.Code.Agda.Builtin.String.T_String_6
              T_RawExpr_34 |
    C_RLet_46 MAlonzo.Code.Agda.Builtin.String.T_String_6 T_RawExpr_34
              T_RawExpr_34 |
    C_RPair_48 T_RawExpr_34 T_RawExpr_34 |
    C_RDestruct_50 T_RawExpr_34
                   MAlonzo.Code.Agda.Builtin.String.T_String_6 T_RawExpr_34
                   MAlonzo.Code.Agda.Builtin.String.T_String_6 T_RawExpr_34 |
    C_RUnit_52 | C_RInt_54 Integer |
    C_RFloat_56 Integer Integer Integer Integer |
    C_RStringLit_58 MAlonzo.Code.Agda.Builtin.String.T_String_6 |
    C_RAnnot_60 T_RawExpr_34 MAlonzo.Code.Once.Type.T_Type_108 |
    C_RBinOp_62 T_BinOp_6 T_RawExpr_34 T_RawExpr_34 |
    C_RUnaryOp_64 T_RawExpr_34 |
    C_RAna_66 MAlonzo.Code.Once.Type.T_Functor_106 T_RawExpr_34
-- Once.TypeCheck.Raw.RawType
d_RawType_68 = ()
data T_RawType_68
  = C_RTVar_70 MAlonzo.Code.Agda.Builtin.String.T_String_6 |
    C_RTUnit_72 | C_RTVoid_74 | C_RTInt_76 | C_RTFloat_78 |
    C_RTStr_80 | C_RTProduct_82 T_RawType_68 T_RawType_68 |
    C_RTSum_84 T_RawType_68 T_RawType_68 |
    C_RTArrow_86 T_RawType_68 T_RawType_68 |
    C_RTEff_88 T_RawType_68 T_RawType_68 | C_RTFix_90 T_RawType_68
-- Once.TypeCheck.Raw.isComparisonOp
d_isComparisonOp_92 :: T_BinOp_6 -> Bool
d_isComparisonOp_92 v0
  = case coe v0 of
      C_OpAdd_8 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      C_OpSub_10 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      C_OpMul_12 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      C_OpDiv_14 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      C_OpMod_16 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      C_OpLt_18 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      C_OpLe_20 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      C_OpGt_22 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      C_OpGe_24 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      C_OpEq_26 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      C_OpNe_28 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Raw.isFloatArithmeticOp
d_isFloatArithmeticOp_94 :: T_BinOp_6 -> Bool
d_isFloatArithmeticOp_94 v0
  = case coe v0 of
      C_OpAdd_8 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      C_OpSub_10 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      C_OpMul_12 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      C_OpDiv_14 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      C_OpMod_16 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      C_OpLt_18 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      C_OpLe_20 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      C_OpGt_22 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      C_OpGe_24 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      C_OpEq_26 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      C_OpNe_28 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Raw.isArithmeticOp
d_isArithmeticOp_96 :: T_BinOp_6 -> Bool
d_isArithmeticOp_96 v0
  = case coe v0 of
      C_OpAdd_8 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      C_OpSub_10 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      C_OpMul_12 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      C_OpDiv_14 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      C_OpMod_16 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      C_OpLt_18 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      C_OpLe_20 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      C_OpGt_22 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      C_OpGe_24 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      C_OpEq_26 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      C_OpNe_28 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Raw.ClosedLiftShape
d_ClosedLiftShape_98 a0 = ()
data T_ClosedLiftShape_98
  = C_cls'45'var_102 | C_cls'45'qual_108 | C_cls'45'res_112 |
    C_cls'45'let_120 | C_cls'45'destr_132 | C_cls'45'unit_134 |
    C_cls'45'str_138 | C_cls'45'annot_144 | C_cls'45'binop_152
-- Once.TypeCheck.Raw.closedLiftShape?
d_closedLiftShape'63'_156 ::
  T_RawExpr_34 -> Maybe T_ClosedLiftShape_98
d_closedLiftShape'63'_156 v0
  = case coe v0 of
      C_RVar_36 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe C_cls'45'var_102)
      C_RQualified_38 v1 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe C_cls'45'qual_108)
      C_RResolved_40 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe C_cls'45'res_112)
      C_RApp_42 v1 v2 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      C_RLam_44 v1 v2 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      C_RLet_46 v1 v2 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe C_cls'45'let_120)
      C_RPair_48 v1 v2
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      C_RDestruct_50 v1 v2 v3 v4 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe C_cls'45'destr_132)
      C_RUnit_52
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe C_cls'45'unit_134)
      C_RInt_54 v1 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      C_RFloat_56 v1 v2 v3 v4
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      C_RStringLit_58 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe C_cls'45'str_138)
      C_RAnnot_60 v1 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe C_cls'45'annot_144)
      C_RBinOp_62 v1 v2 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe C_cls'45'binop_152)
      C_RUnaryOp_64 v2
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      C_RAna_66 v1 v2 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Raw.closedLiftShape?-just
d_closedLiftShape'63''45'just_162 ::
  T_RawExpr_34 ->
  T_ClosedLiftShape_98 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_closedLiftShape'63''45'just_162 = erased
