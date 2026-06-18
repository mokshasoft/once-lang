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
import qualified MAlonzo.Code.Agda.Builtin.String
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
    C_RApp_40 T_RawExpr_34 T_RawExpr_34 |
    C_RLam_42 MAlonzo.Code.Agda.Builtin.String.T_String_6
              T_RawExpr_34 |
    C_RLet_44 MAlonzo.Code.Agda.Builtin.String.T_String_6 T_RawExpr_34
              T_RawExpr_34 |
    C_RPair_46 T_RawExpr_34 T_RawExpr_34 |
    C_RDestruct_48 T_RawExpr_34
                   MAlonzo.Code.Agda.Builtin.String.T_String_6 T_RawExpr_34
                   MAlonzo.Code.Agda.Builtin.String.T_String_6 T_RawExpr_34 |
    C_RUnit_50 | C_RInt_52 Integer |
    C_RStringLit_54 MAlonzo.Code.Agda.Builtin.String.T_String_6 |
    C_RAnnot_56 T_RawExpr_34 MAlonzo.Code.Once.Type.T_Type_112 |
    C_RBinOp_58 T_BinOp_6 T_RawExpr_34 T_RawExpr_34 |
    C_RUnaryOp_60 T_RawExpr_34 |
    C_RAna_62 MAlonzo.Code.Once.Type.T_Functor_110 T_RawExpr_34
-- Once.TypeCheck.Raw.RawType
d_RawType_64 = ()
data T_RawType_64
  = C_RTVar_66 MAlonzo.Code.Agda.Builtin.String.T_String_6 |
    C_RTUnit_68 | C_RTVoid_70 | C_RTInt_72 | C_RTFloat_74 |
    C_RTBuffer_76 | C_RTStr_78 |
    C_RTProduct_80 T_RawType_64 T_RawType_64 |
    C_RTSum_82 T_RawType_64 T_RawType_64 |
    C_RTArrow_84 T_RawType_64 T_RawType_64 |
    C_RTEff_86 T_RawType_64 T_RawType_64 | C_RTFix_88 T_RawType_64
-- Once.TypeCheck.Raw.isComparisonOp
d_isComparisonOp_90 :: T_BinOp_6 -> Bool
d_isComparisonOp_90 v0
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
-- Once.TypeCheck.Raw.isArithmeticOp
d_isArithmeticOp_92 :: T_BinOp_6 -> Bool
d_isArithmeticOp_92 v0
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
