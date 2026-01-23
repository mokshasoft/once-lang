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
    C_RApp_38 T_RawExpr_34 T_RawExpr_34 |
    C_RLam_40 MAlonzo.Code.Agda.Builtin.String.T_String_6
              T_RawExpr_34 |
    C_RLet_42 MAlonzo.Code.Agda.Builtin.String.T_String_6 T_RawExpr_34
              T_RawExpr_34 |
    C_RPair_44 T_RawExpr_34 T_RawExpr_34 |
    C_RDestruct_46 T_RawExpr_34
                   MAlonzo.Code.Agda.Builtin.String.T_String_6 T_RawExpr_34
                   MAlonzo.Code.Agda.Builtin.String.T_String_6 T_RawExpr_34 |
    C_RUnit_48 | C_RInt_50 Integer |
    C_RStringLit_52 MAlonzo.Code.Agda.Builtin.String.T_String_6 |
    C_RAnnot_54 T_RawExpr_34 MAlonzo.Code.Once.Type.T_Type_32 |
    C_RBinOp_56 T_BinOp_6 T_RawExpr_34 T_RawExpr_34 |
    C_RUnaryOp_58 T_RawExpr_34
-- Once.TypeCheck.Raw.RawType
d_RawType_60 = ()
data T_RawType_60
  = C_RTVar_62 MAlonzo.Code.Agda.Builtin.String.T_String_6 |
    C_RTUnit_64 | C_RTVoid_66 | C_RTInt_68 | C_RTFloat_70 |
    C_RTBuffer_72 | C_RTStr_74 |
    C_RTProduct_76 T_RawType_60 T_RawType_60 |
    C_RTSum_78 T_RawType_60 T_RawType_60 |
    C_RTArrow_80 T_RawType_60 T_RawType_60 |
    C_RTEff_82 T_RawType_60 T_RawType_60 | C_RTFix_84 T_RawType_60
-- Once.TypeCheck.Raw.isComparisonOp
d_isComparisonOp_86 :: T_BinOp_6 -> Bool
d_isComparisonOp_86 v0
  = let v1 = coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
    coe
      (case coe v0 of
         C_OpLt_18 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
         C_OpLe_20 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
         C_OpGt_22 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
         C_OpGe_24 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
         C_OpEq_26 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
         C_OpNe_28 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
         _ -> coe v1)
-- Once.TypeCheck.Raw.isArithmeticOp
d_isArithmeticOp_88 :: T_BinOp_6 -> Bool
d_isArithmeticOp_88 v0
  = let v1 = coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
    coe
      (case coe v0 of
         C_OpAdd_8 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
         C_OpSub_10 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
         C_OpMul_12 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
         C_OpDiv_14 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
         C_OpMod_16 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
         _ -> coe v1)
