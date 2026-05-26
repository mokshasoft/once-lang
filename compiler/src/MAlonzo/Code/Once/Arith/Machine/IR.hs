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
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Data.Integer.Base
import qualified MAlonzo.Code.Once.Arith.Machine.AbsState
import qualified MAlonzo.Code.Once.Type

-- Once.Arith.Machine.IR.MArithIR
d_MArithIR_10 a0 = ()
data T_MArithIR_10
  = C_alit_14 Integer |
    C_ainput_16 [MAlonzo.Code.Once.Arith.Machine.AbsState.T_Side_22] |
    C_aadd_18 T_MArithIR_10 T_MArithIR_10 |
    C_asub_20 T_MArithIR_10 T_MArithIR_10 |
    C_amul_22 T_MArithIR_10 T_MArithIR_10 | C_aneg_24 T_MArithIR_10
-- Once.Arith.Machine.IR.eval-arith
d_eval'45'arith_28 ::
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_InputShape_8 ->
  T_MArithIR_10 -> AgdaAny -> Integer
d_eval'45'arith_28 v0 v1 v2
  = case coe v1 of
      C_alit_14 v3 -> coe v3
      C_ainput_16 v3
        -> let v4
                 = MAlonzo.Code.Once.Arith.Machine.AbsState.d_project_32
                     (coe v0) (coe v3) (coe v2) in
           coe
             (case coe v4 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5 -> coe v5
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe (0 :: Integer)
                _ -> MAlonzo.RTE.mazUnreachableError)
      C_aadd_18 v3 v4
        -> coe
             MAlonzo.Code.Data.Integer.Base.d__'43'__284
             (coe d_eval'45'arith_28 (coe v0) (coe v3) (coe v2))
             (coe d_eval'45'arith_28 (coe v0) (coe v4) (coe v2))
      C_asub_20 v3 v4
        -> coe
             MAlonzo.Code.Data.Integer.Base.d__'45'__302
             (coe d_eval'45'arith_28 (coe v0) (coe v3) (coe v2))
             (coe d_eval'45'arith_28 (coe v0) (coe v4) (coe v2))
      C_amul_22 v3 v4
        -> coe
             MAlonzo.Code.Data.Integer.Base.d__'42'__316
             (coe d_eval'45'arith_28 (coe v0) (coe v3) (coe v2))
             (coe d_eval'45'arith_28 (coe v0) (coe v4) (coe v2))
      C_aneg_24 v3
        -> coe
             MAlonzo.Code.Data.Integer.Base.d_'45'__260
             (coe d_eval'45'arith_28 (coe v0) (coe v3) (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Machine.IR.shape-as-type
d_shape'45'as'45'type_80 ::
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_InputShape_8 ->
  MAlonzo.Code.Once.Type.T_Type_108
d_shape'45'as'45'type_80 v0
  = case coe v0 of
      MAlonzo.Code.Once.Arith.Machine.AbsState.C_shape'45'unit_10
        -> coe MAlonzo.Code.Once.Type.C_Unit_118
      MAlonzo.Code.Once.Arith.Machine.AbsState.C_shape'45'int_12
        -> coe MAlonzo.Code.Once.Type.C_Int_132
      MAlonzo.Code.Once.Arith.Machine.AbsState.C_shape'45'pair_14 v1 v2
        -> coe
             MAlonzo.Code.Once.Type.C__'42'__122
             (coe d_shape'45'as'45'type_80 (coe v1))
             (coe d_shape'45'as'45'type_80 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Machine.IR.ArithBlock
d_ArithBlock_86 = ()
data T_ArithBlock_86
  = C_mk'45'block_96 MAlonzo.Code.Once.Arith.Machine.AbsState.T_InputShape_8
                     T_MArithIR_10
-- Once.Arith.Machine.IR.ArithBlock.block-shape
d_block'45'shape_92 ::
  T_ArithBlock_86 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_InputShape_8
d_block'45'shape_92 v0
  = case coe v0 of
      C_mk'45'block_96 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Machine.IR.ArithBlock.block-body
d_block'45'body_94 :: T_ArithBlock_86 -> T_MArithIR_10
d_block'45'body_94 v0
  = case coe v0 of
      C_mk'45'block_96 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Machine.IR.leaf-count
d_leaf'45'count_100 ::
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_InputShape_8 ->
  T_MArithIR_10 -> Integer
d_leaf'45'count_100 ~v0 v1 = du_leaf'45'count_100 v1
du_leaf'45'count_100 :: T_MArithIR_10 -> Integer
du_leaf'45'count_100 v0
  = case coe v0 of
      C_alit_14 v1 -> coe (1 :: Integer)
      C_ainput_16 v1 -> coe (1 :: Integer)
      C_aadd_18 v1 v2
        -> coe
             addInt (coe du_leaf'45'count_100 (coe v1))
             (coe du_leaf'45'count_100 (coe v2))
      C_asub_20 v1 v2
        -> coe
             addInt (coe du_leaf'45'count_100 (coe v1))
             (coe du_leaf'45'count_100 (coe v2))
      C_amul_22 v1 v2
        -> coe
             addInt (coe du_leaf'45'count_100 (coe v1))
             (coe du_leaf'45'count_100 (coe v2))
      C_aneg_24 v1 -> coe du_leaf'45'count_100 (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
