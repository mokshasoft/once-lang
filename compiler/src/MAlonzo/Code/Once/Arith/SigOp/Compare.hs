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

module MAlonzo.Code.Once.Arith.SigOp.Compare where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Once.Arith.CmpOp
import qualified MAlonzo.Code.Once.Arith.Machine.IR
import qualified MAlonzo.Code.Once.Arith.Machine.Shape
import qualified MAlonzo.Code.Once.Arith.Prim
import qualified MAlonzo.Code.Once.Arith.SigOp.Block
import qualified MAlonzo.Code.Once.Arith.Type
import qualified MAlonzo.Code.Once.SigOp.Info
import qualified MAlonzo.Code.Once.Spec.Type

-- Once.Arith.SigOp.Compare.CmpAt
d_CmpAt_8 a0 = ()
data T_CmpAt_8
  = C_int'45'c_10 MAlonzo.Code.Once.Arith.CmpOp.T_CmpOp_6 |
    C_flt'45'c_12 MAlonzo.Code.Once.Arith.CmpOp.T_FCmpOp_72
-- Once.Arith.SigOp.Compare.cmp-of
d_cmp'45'of_18 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpSem_74 -> Maybe T_CmpAt_8
d_cmp'45'of_18 ~v0 ~v1 v2 = du_cmp'45'of_18 v2
du_cmp'45'of_18 ::
  MAlonzo.Code.Once.SigOp.Info.T_SigOpSem_74 -> Maybe T_CmpAt_8
du_cmp'45'of_18 v0
  = let v1 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.SigOp.Info.C_primV_96 v2
           -> case coe v2 of
                MAlonzo.Code.Once.Arith.Prim.C_p'45'fcmp_256 v3 v4 v5
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe
                          C_flt'45'c_12
                          (coe
                             MAlonzo.Code.Once.Arith.CmpOp.C_fcmp_76 (coe v3) (coe v4)
                             (coe v5)))
                MAlonzo.Code.Once.Arith.Prim.C_p'45'cmp_258 v3
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe C_int'45'c_10 (coe v3))
                _ -> coe v1
         _ -> coe v1)
-- Once.Arith.SigOp.Compare.cmp-shape
d_cmp'45'shape_28 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  T_CmpAt_8 -> MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8
d_cmp'45'shape_28 ~v0 v1 = du_cmp'45'shape_28 v1
du_cmp'45'shape_28 ::
  T_CmpAt_8 -> MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8
du_cmp'45'shape_28 v0
  = case coe v0 of
      C_int'45'c_10 v1
        -> coe
             MAlonzo.Code.Once.Arith.Machine.Shape.C_shape'45'pair_16
             (coe MAlonzo.Code.Once.Arith.Machine.Shape.C_shape'45'int_12)
             (coe MAlonzo.Code.Once.Arith.Machine.Shape.C_shape'45'int_12)
      C_flt'45'c_12 v1
        -> coe
             MAlonzo.Code.Once.Arith.Machine.Shape.C_shape'45'pair_16
             (coe MAlonzo.Code.Once.Arith.Machine.Shape.C_shape'45'float_14)
             (coe MAlonzo.Code.Once.Arith.Machine.Shape.C_shape'45'float_14)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.SigOp.Compare.cmp-body
d_cmp'45'body_34 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  T_CmpAt_8 -> MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10
d_cmp'45'body_34 ~v0 v1 = du_cmp'45'body_34 v1
du_cmp'45'body_34 ::
  T_CmpAt_8 -> MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10
du_cmp'45'body_34 v0
  = case coe v0 of
      C_int'45'c_10 v1
        -> coe
             MAlonzo.Code.Once.Arith.Machine.IR.C_acmp_46 (coe v1)
             (coe
                MAlonzo.Code.Once.Arith.Machine.IR.C_ainput_20
                (coe
                   MAlonzo.Code.Once.Arith.Machine.Shape.C_go'45'fst_80
                   (coe MAlonzo.Code.Once.Arith.Machine.Shape.C_here'45'int_70)))
             (coe
                MAlonzo.Code.Once.Arith.Machine.IR.C_ainput_20
                (coe
                   MAlonzo.Code.Once.Arith.Machine.Shape.C_go'45'snd_88
                   (coe MAlonzo.Code.Once.Arith.Machine.Shape.C_here'45'int_70)))
      C_flt'45'c_12 v1
        -> coe
             MAlonzo.Code.Once.Arith.Machine.IR.C_afcmp_48 (coe v1)
             (coe
                MAlonzo.Code.Once.Arith.Machine.IR.C_ainput_20
                (coe
                   MAlonzo.Code.Once.Arith.Machine.Shape.C_go'45'fst_80
                   (coe MAlonzo.Code.Once.Arith.Machine.Shape.C_here'45'flt_72)))
             (coe
                MAlonzo.Code.Once.Arith.Machine.IR.C_ainput_20
                (coe
                   MAlonzo.Code.Once.Arith.Machine.Shape.C_go'45'snd_88
                   (coe MAlonzo.Code.Once.Arith.Machine.Shape.C_here'45'flt_72)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.SigOp.Compare.cmp-block
d_cmp'45'block_42 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  T_CmpAt_8 -> MAlonzo.Code.Once.Arith.Machine.IR.T_ArithBlock_58
d_cmp'45'block_42 ~v0 v1 = du_cmp'45'block_42 v1
du_cmp'45'block_42 ::
  T_CmpAt_8 -> MAlonzo.Code.Once.Arith.Machine.IR.T_ArithBlock_58
du_cmp'45'block_42 v0
  = coe
      MAlonzo.Code.Once.Arith.Machine.IR.C_mk'45'block_72
      (coe du_cmp'45'shape_28 (coe v0))
      (coe MAlonzo.Code.Once.Arith.Type.C_NInt_8)
      (coe du_cmp'45'body_34 (coe v0))
-- Once.Arith.SigOp.Compare.cmp-block-info
d_cmp'45'block'45'info_48 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  T_CmpAt_8 -> MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_102
d_cmp'45'block'45'info_48 ~v0 v1 = du_cmp'45'block'45'info_48 v1
du_cmp'45'block'45'info_48 ::
  T_CmpAt_8 -> MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_102
du_cmp'45'block'45'info_48 v0
  = case coe v0 of
      C_int'45'c_10 v1
        -> coe
             MAlonzo.Code.Once.Arith.SigOp.Block.d_block'45'info_128
             (coe
                MAlonzo.Code.Once.Arith.Machine.Shape.C_shape'45'pair_16
                (coe MAlonzo.Code.Once.Arith.Machine.Shape.C_shape'45'int_12)
                (coe MAlonzo.Code.Once.Arith.Machine.Shape.C_shape'45'int_12))
             (coe MAlonzo.Code.Once.Arith.Type.C_NInt_8)
             (coe du_cmp'45'body_34 (coe v0))
      C_flt'45'c_12 v1
        -> coe
             MAlonzo.Code.Once.Arith.SigOp.Block.d_block'45'info_128
             (coe
                MAlonzo.Code.Once.Arith.Machine.Shape.C_shape'45'pair_16
                (coe MAlonzo.Code.Once.Arith.Machine.Shape.C_shape'45'float_14)
                (coe MAlonzo.Code.Once.Arith.Machine.Shape.C_shape'45'float_14))
             (coe MAlonzo.Code.Once.Arith.Type.C_NInt_8)
             (coe du_cmp'45'body_34 (coe v0))
      _ -> MAlonzo.RTE.mazUnreachableError
