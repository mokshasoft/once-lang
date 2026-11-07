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

module MAlonzo.Code.Once.Arith.Machine.IR where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Once.Arith.CmpOp
import qualified MAlonzo.Code.Once.Arith.Machine.Shape
import qualified MAlonzo.Code.Once.Arith.Type
import qualified MAlonzo.Code.Once.Spec.Float.Decimal
import qualified MAlonzo.Code.Once.Spec.Type

-- Once.Arith.Machine.IR.MArithIR
d_MArithIR_10 a0 a1 = ()
data T_MArithIR_10
  = C_alit_14 Integer |
    C_aflit_16 MAlonzo.Code.Once.Spec.Float.Decimal.T_Decimal_8 |
    C_ainput_20 MAlonzo.Code.Once.Arith.Machine.Shape.T_Path_68 |
    C_aadd_24 T_MArithIR_10 T_MArithIR_10 |
    C_asub_28 T_MArithIR_10 T_MArithIR_10 |
    C_amul_32 T_MArithIR_10 T_MArithIR_10 |
    C_adiv_36 T_MArithIR_10 T_MArithIR_10 |
    C_amod_38 T_MArithIR_10 T_MArithIR_10 | C_aneg_42 T_MArithIR_10 |
    C_ai2f_44 T_MArithIR_10 |
    C_acmp_46 MAlonzo.Code.Once.Arith.CmpOp.T_CmpOp_6 T_MArithIR_10
              T_MArithIR_10
-- Once.Arith.Machine.IR.shape-as-type
d_shape'45'as'45'type_48 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8
d_shape'45'as'45'type_48 v0
  = case coe v0 of
      MAlonzo.Code.Once.Arith.Machine.Shape.C_shape'45'unit_10
        -> coe MAlonzo.Code.Once.Spec.Type.C_Unit_18
      MAlonzo.Code.Once.Arith.Machine.Shape.C_shape'45'int_12
        -> coe MAlonzo.Code.Once.Spec.Type.C_Int_32
      MAlonzo.Code.Once.Arith.Machine.Shape.C_shape'45'float_14
        -> coe MAlonzo.Code.Once.Spec.Type.C_Float_34
      MAlonzo.Code.Once.Arith.Machine.Shape.C_shape'45'pair_16 v1 v2
        -> coe
             MAlonzo.Code.Once.Spec.Type.C__'42'__22
             (coe d_shape'45'as'45'type_48 (coe v1))
             (coe d_shape'45'as'45'type_48 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Machine.IR.numtype-as-type
d_numtype'45'as'45'type_54 ::
  MAlonzo.Code.Once.Arith.Type.T_NumType_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8
d_numtype'45'as'45'type_54 v0
  = case coe v0 of
      MAlonzo.Code.Once.Arith.Type.C_NInt_8
        -> coe MAlonzo.Code.Once.Spec.Type.C_Int_32
      MAlonzo.Code.Once.Arith.Type.C_NFloat_10
        -> coe MAlonzo.Code.Once.Spec.Type.C_Float_34
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Machine.IR.ArithBlock
d_ArithBlock_56 = ()
data T_ArithBlock_56
  = C_mk'45'block_70 MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8
                     MAlonzo.Code.Once.Arith.Type.T_NumType_6 T_MArithIR_10
-- Once.Arith.Machine.IR.ArithBlock.block-shape
d_block'45'shape_64 ::
  T_ArithBlock_56 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8
d_block'45'shape_64 v0
  = case coe v0 of
      C_mk'45'block_70 v1 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Machine.IR.ArithBlock.block-kind
d_block'45'kind_66 ::
  T_ArithBlock_56 -> MAlonzo.Code.Once.Arith.Type.T_NumType_6
d_block'45'kind_66 v0
  = case coe v0 of
      C_mk'45'block_70 v1 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Machine.IR.ArithBlock.block-body
d_block'45'body_68 :: T_ArithBlock_56 -> T_MArithIR_10
d_block'45'body_68 v0
  = case coe v0 of
      C_mk'45'block_70 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Machine.IR.leaf-count
d_leaf'45'count_76 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Type.T_NumType_6 ->
  T_MArithIR_10 -> Integer
d_leaf'45'count_76 ~v0 ~v1 v2 = du_leaf'45'count_76 v2
du_leaf'45'count_76 :: T_MArithIR_10 -> Integer
du_leaf'45'count_76 v0
  = case coe v0 of
      C_alit_14 v1 -> coe (1 :: Integer)
      C_aflit_16 v1 -> coe (1 :: Integer)
      C_ainput_20 v2 -> coe (1 :: Integer)
      C_aadd_24 v2 v3
        -> coe
             addInt (coe du_leaf'45'count_76 (coe v2))
             (coe du_leaf'45'count_76 (coe v3))
      C_asub_28 v2 v3
        -> coe
             addInt (coe du_leaf'45'count_76 (coe v2))
             (coe du_leaf'45'count_76 (coe v3))
      C_amul_32 v2 v3
        -> coe
             addInt (coe du_leaf'45'count_76 (coe v2))
             (coe du_leaf'45'count_76 (coe v3))
      C_adiv_36 v2 v3
        -> coe
             addInt (coe du_leaf'45'count_76 (coe v2))
             (coe du_leaf'45'count_76 (coe v3))
      C_amod_38 v1 v2
        -> coe
             addInt (coe du_leaf'45'count_76 (coe v1))
             (coe du_leaf'45'count_76 (coe v2))
      C_aneg_42 v2 -> coe du_leaf'45'count_76 (coe v2)
      C_ai2f_44 v1 -> coe du_leaf'45'count_76 (coe v1)
      C_acmp_46 v1 v2 v3
        -> coe
             addInt (coe du_leaf'45'count_76 (coe v2))
             (coe du_leaf'45'count_76 (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
