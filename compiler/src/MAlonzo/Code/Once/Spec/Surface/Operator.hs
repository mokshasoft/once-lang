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

module MAlonzo.Code.Once.Spec.Surface.Operator where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Once.Spec.Theory

-- Once.Spec.Surface.Operator.Dottable
d_Dottable_8 = ()
data T_Dottable_8
  = C_o'43'_10 | C_o'45'_12 | C_o'42'_14 | C_o'47'_16 | C_o'60'_18 |
    C_o'60''61'_20 | C_o'62'_22 | C_o'62''61'_24 | C_o'61''61'_26 |
    C_o'33''61'_28
-- Once.Spec.Surface.Operator.Op
d_Op_30 = ()
data T_Op_30 = C_'8249'_'8250'_32 T_Dottable_8 | C_o'37'_34
-- Once.Spec.Surface.Operator.BinOp
d_BinOp_36 = ()
data T_BinOp_36 = C_plain_38 T_Op_30 | C_dotted_40 T_Dottable_8
-- Once.Spec.Surface.Operator.Level
d_Level_42 = ()
data T_Level_42
  = C_comparison_44 | C_additive_46 | C_multiplicative_48
-- Once.Spec.Surface.Operator.level
d_level_50 :: T_Op_30 -> T_Level_42
d_level_50 v0
  = case coe v0 of
      C_'8249'_'8250'_32 v1
        -> case coe v1 of
             C_o'43'_10 -> coe C_additive_46
             C_o'45'_12 -> coe C_additive_46
             C_o'42'_14 -> coe C_multiplicative_48
             C_o'47'_16 -> coe C_multiplicative_48
             C_o'60'_18 -> coe C_comparison_44
             C_o'60''61'_20 -> coe C_comparison_44
             C_o'62'_22 -> coe C_comparison_44
             C_o'62''61'_24 -> coe C_comparison_44
             C_o'61''61'_26 -> coe C_comparison_44
             C_o'33''61'_28 -> coe C_comparison_44
             _ -> MAlonzo.RTE.mazUnreachableError
      C_o'37'_34 -> coe C_multiplicative_48
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Surface.Operator.BinSym
d_BinSym_52 = ()
data T_BinSym_52
  = C__'8758'_'8758'__66 MAlonzo.Code.Once.Spec.Theory.T_Theory_16
                         MAlonzo.Code.Once.Spec.Theory.T_Shape_30
                         MAlonzo.Code.Once.Spec.Theory.T_Sym_38
-- Once.Spec.Surface.Operator.BinSym.theory
d_theory_60 ::
  T_BinSym_52 -> MAlonzo.Code.Once.Spec.Theory.T_Theory_16
d_theory_60 v0
  = case coe v0 of
      C__'8758'_'8758'__66 v1 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Surface.Operator.BinSym.shape
d_shape_62 ::
  T_BinSym_52 -> MAlonzo.Code.Once.Spec.Theory.T_Shape_30
d_shape_62 v0
  = case coe v0 of
      C__'8758'_'8758'__66 v1 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Surface.Operator.BinSym.symbol
d_symbol_64 ::
  T_BinSym_52 -> MAlonzo.Code.Once.Spec.Theory.T_Sym_38
d_symbol_64 v0
  = case coe v0 of
      C__'8758'_'8758'__66 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Surface.Operator.binSym
d_binSym_68 :: T_BinOp_36 -> T_BinSym_52
d_binSym_68 v0
  = case coe v0 of
      C_plain_38 v1
        -> case coe v1 of
             C_'8249'_'8250'_32 v2
               -> case coe v2 of
                    C_o'43'_10
                      -> coe
                           C__'8758'_'8758'__66 (coe MAlonzo.Code.Once.Spec.Theory.C_Ring_20)
                           (coe MAlonzo.Code.Once.Spec.Theory.C_binary_34)
                           (coe MAlonzo.Code.Once.Spec.Theory.C_'8245''43'_42)
                    C_o'45'_12
                      -> coe
                           C__'8758'_'8758'__66 (coe MAlonzo.Code.Once.Spec.Theory.C_Ring_20)
                           (coe MAlonzo.Code.Once.Spec.Theory.C_binary_34)
                           (coe MAlonzo.Code.Once.Spec.Theory.C_'8245''45'_44)
                    C_o'42'_14
                      -> coe
                           C__'8758'_'8758'__66 (coe MAlonzo.Code.Once.Spec.Theory.C_Ring_20)
                           (coe MAlonzo.Code.Once.Spec.Theory.C_binary_34)
                           (coe MAlonzo.Code.Once.Spec.Theory.C_'8245''42'_46)
                    C_o'47'_16
                      -> coe
                           C__'8758'_'8758'__66
                           (coe MAlonzo.Code.Once.Spec.Theory.C_Division_22)
                           (coe MAlonzo.Code.Once.Spec.Theory.C_binary_34)
                           (coe MAlonzo.Code.Once.Spec.Theory.C_'8245''47'_48)
                    C_o'60'_18
                      -> coe
                           C__'8758'_'8758'__66 (coe MAlonzo.Code.Once.Spec.Theory.C_Order_24)
                           (coe MAlonzo.Code.Once.Spec.Theory.C_compare_36)
                           (coe MAlonzo.Code.Once.Spec.Theory.C_'8245''60'_52)
                    C_o'60''61'_20
                      -> coe
                           C__'8758'_'8758'__66 (coe MAlonzo.Code.Once.Spec.Theory.C_Order_24)
                           (coe MAlonzo.Code.Once.Spec.Theory.C_compare_36)
                           (coe MAlonzo.Code.Once.Spec.Theory.C_'8245''60''61'_54)
                    C_o'62'_22
                      -> coe
                           C__'8758'_'8758'__66 (coe MAlonzo.Code.Once.Spec.Theory.C_Order_24)
                           (coe MAlonzo.Code.Once.Spec.Theory.C_compare_36)
                           (coe MAlonzo.Code.Once.Spec.Theory.C_'8245''62'_56)
                    C_o'62''61'_24
                      -> coe
                           C__'8758'_'8758'__66 (coe MAlonzo.Code.Once.Spec.Theory.C_Order_24)
                           (coe MAlonzo.Code.Once.Spec.Theory.C_compare_36)
                           (coe MAlonzo.Code.Once.Spec.Theory.C_'8245''62''61'_58)
                    C_o'61''61'_26
                      -> coe
                           C__'8758'_'8758'__66
                           (coe MAlonzo.Code.Once.Spec.Theory.C_Equality_26)
                           (coe MAlonzo.Code.Once.Spec.Theory.C_compare_36)
                           (coe MAlonzo.Code.Once.Spec.Theory.C_'8245''61''61'_60)
                    C_o'33''61'_28
                      -> coe
                           C__'8758'_'8758'__66
                           (coe MAlonzo.Code.Once.Spec.Theory.C_Equality_26)
                           (coe MAlonzo.Code.Once.Spec.Theory.C_compare_36)
                           (coe MAlonzo.Code.Once.Spec.Theory.C_'8245''33''61'_62)
                    _ -> MAlonzo.RTE.mazUnreachableError
             C_o'37'_34
               -> coe
                    C__'8758'_'8758'__66
                    (coe MAlonzo.Code.Once.Spec.Theory.C_Division_22)
                    (coe MAlonzo.Code.Once.Spec.Theory.C_binary_34)
                    (coe MAlonzo.Code.Once.Spec.Theory.C_'8245''37'_50)
             _ -> MAlonzo.RTE.mazUnreachableError
      C_dotted_40 v1
        -> case coe v1 of
             C_o'43'_10
               -> coe
                    C__'8758'_'8758'__66
                    (coe MAlonzo.Code.Once.Spec.Theory.C_Rounded_28)
                    (coe MAlonzo.Code.Once.Spec.Theory.C_binary_34)
                    (coe MAlonzo.Code.Once.Spec.Theory.C_'8245''43''7496'_64)
             C_o'45'_12
               -> coe
                    C__'8758'_'8758'__66
                    (coe MAlonzo.Code.Once.Spec.Theory.C_Rounded_28)
                    (coe MAlonzo.Code.Once.Spec.Theory.C_binary_34)
                    (coe MAlonzo.Code.Once.Spec.Theory.C_'8245''45''7496'_66)
             C_o'42'_14
               -> coe
                    C__'8758'_'8758'__66
                    (coe MAlonzo.Code.Once.Spec.Theory.C_Rounded_28)
                    (coe MAlonzo.Code.Once.Spec.Theory.C_binary_34)
                    (coe MAlonzo.Code.Once.Spec.Theory.C_'8245''42''7496'_68)
             C_o'47'_16
               -> coe
                    C__'8758'_'8758'__66
                    (coe MAlonzo.Code.Once.Spec.Theory.C_Rounded_28)
                    (coe MAlonzo.Code.Once.Spec.Theory.C_binary_34)
                    (coe MAlonzo.Code.Once.Spec.Theory.C_'8245''47''7496'_70)
             C_o'60'_18
               -> coe
                    C__'8758'_'8758'__66
                    (coe MAlonzo.Code.Once.Spec.Theory.C_Rounded_28)
                    (coe MAlonzo.Code.Once.Spec.Theory.C_compare_36)
                    (coe MAlonzo.Code.Once.Spec.Theory.C_'8245''60''7496'_76)
             C_o'60''61'_20
               -> coe
                    C__'8758'_'8758'__66
                    (coe MAlonzo.Code.Once.Spec.Theory.C_Rounded_28)
                    (coe MAlonzo.Code.Once.Spec.Theory.C_compare_36)
                    (coe MAlonzo.Code.Once.Spec.Theory.C_'8245''60''61''7496'_78)
             C_o'62'_22
               -> coe
                    C__'8758'_'8758'__66
                    (coe MAlonzo.Code.Once.Spec.Theory.C_Rounded_28)
                    (coe MAlonzo.Code.Once.Spec.Theory.C_compare_36)
                    (coe MAlonzo.Code.Once.Spec.Theory.C_'8245''62''7496'_80)
             C_o'62''61'_24
               -> coe
                    C__'8758'_'8758'__66
                    (coe MAlonzo.Code.Once.Spec.Theory.C_Rounded_28)
                    (coe MAlonzo.Code.Once.Spec.Theory.C_compare_36)
                    (coe MAlonzo.Code.Once.Spec.Theory.C_'8245''62''61''7496'_82)
             C_o'61''61'_26
               -> coe
                    C__'8758'_'8758'__66
                    (coe MAlonzo.Code.Once.Spec.Theory.C_Rounded_28)
                    (coe MAlonzo.Code.Once.Spec.Theory.C_compare_36)
                    (coe MAlonzo.Code.Once.Spec.Theory.C_'8245''61''61''7496'_72)
             C_o'33''61'_28
               -> coe
                    C__'8758'_'8758'__66
                    (coe MAlonzo.Code.Once.Spec.Theory.C_Rounded_28)
                    (coe MAlonzo.Code.Once.Spec.Theory.C_compare_36)
                    (coe MAlonzo.Code.Once.Spec.Theory.C_'8245''33''61''7496'_74)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
