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
import qualified MAlonzo.Code.Once.Type

-- Once.Arith.SigOp.Compare.cmp-of
d_cmp'45'of_12 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpSem_142 ->
  Maybe MAlonzo.Code.Once.Arith.CmpOp.T_CmpOp_6
d_cmp'45'of_12 ~v0 ~v1 v2 = du_cmp'45'of_12 v2
du_cmp'45'of_12 ::
  MAlonzo.Code.Once.SigOp.Info.T_SigOpSem_142 ->
  Maybe MAlonzo.Code.Once.Arith.CmpOp.T_CmpOp_6
du_cmp'45'of_12 v0
  = let v1 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.SigOp.Info.C_primV_158 v2
           -> case coe v2 of
                MAlonzo.Code.Once.Arith.Prim.C_p'45'cmp_410 v3
                  -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v3)
                _ -> coe v1
         _ -> coe v1)
-- Once.Arith.SigOp.Compare.cmp-body
d_cmp'45'body_16 ::
  MAlonzo.Code.Once.Arith.CmpOp.T_CmpOp_6 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10
d_cmp'45'body_16 v0
  = coe
      MAlonzo.Code.Once.Arith.Machine.IR.C_acmp_46 (coe v0)
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
-- Once.Arith.SigOp.Compare.cmp-block
d_cmp'45'block_20 ::
  MAlonzo.Code.Once.Arith.CmpOp.T_CmpOp_6 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_ArithBlock_166
d_cmp'45'block_20 v0
  = coe
      MAlonzo.Code.Once.Arith.Machine.IR.C_mk'45'block_180
      (coe
         MAlonzo.Code.Once.Arith.Machine.Shape.C_shape'45'pair_16
         (coe MAlonzo.Code.Once.Arith.Machine.Shape.C_shape'45'int_12)
         (coe MAlonzo.Code.Once.Arith.Machine.Shape.C_shape'45'int_12))
      (coe MAlonzo.Code.Once.Arith.Type.C_NInt_8)
      (coe d_cmp'45'body_16 (coe v0))
-- Once.Arith.SigOp.Compare.cmp-block-info
d_cmp'45'block'45'info_24 ::
  MAlonzo.Code.Once.Arith.CmpOp.T_CmpOp_6 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164
d_cmp'45'block'45'info_24 v0
  = coe
      MAlonzo.Code.Once.Arith.SigOp.Block.d_block'45'info_554
      (coe
         MAlonzo.Code.Once.Arith.Machine.Shape.C_shape'45'pair_16
         (coe MAlonzo.Code.Once.Arith.Machine.Shape.C_shape'45'int_12)
         (coe MAlonzo.Code.Once.Arith.Machine.Shape.C_shape'45'int_12))
      (coe MAlonzo.Code.Once.Arith.Type.C_NInt_8)
      (coe d_cmp'45'body_16 (coe v0))
