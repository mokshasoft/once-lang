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

module MAlonzo.Code.Once.Arith.SigOp.AsBlock where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Once.Arith.Machine.IR
import qualified MAlonzo.Code.Once.Arith.Machine.Shape
import qualified MAlonzo.Code.Once.Arith.Prim
import qualified MAlonzo.Code.Once.Arith.SigOp.Block
import qualified MAlonzo.Code.Once.Arith.Type
import qualified MAlonzo.Code.Once.SigOp.Info
import qualified MAlonzo.Code.Once.Spec.Name
import qualified MAlonzo.Code.Once.Spec.Type

-- Once.Arith.SigOp.AsBlock.Lifted
d_Lifted_12 a0 a1 = ()
data T_Lifted_12
  = C_lifted_38 MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8
                MAlonzo.Code.Once.Arith.Type.T_NumType_6
                MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10
-- Once.Arith.SigOp.AsBlock.Lifted.sh
d_sh_28 ::
  T_Lifted_12 -> MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8
d_sh_28 v0
  = case coe v0 of
      C_lifted_38 v1 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.SigOp.AsBlock.Lifted.n
d_n_30 :: T_Lifted_12 -> MAlonzo.Code.Once.Arith.Type.T_NumType_6
d_n_30 v0
  = case coe v0 of
      C_lifted_38 v1 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.SigOp.AsBlock.Lifted.body
d_body_32 ::
  T_Lifted_12 -> MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10
d_body_32 v0
  = case coe v0 of
      C_lifted_38 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.SigOp.AsBlock.Lifted.eA
d_eA_34 ::
  T_Lifted_12 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_eA_34 = erased
-- Once.Arith.SigOp.AsBlock.Lifted.eB
d_eB_36 ::
  T_Lifted_12 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_eB_36 = erased
-- Once.Arith.SigOp.AsBlock.pII
d_pII_40 :: MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8
d_pII_40
  = coe
      MAlonzo.Code.Once.Arith.Machine.Shape.C_shape'45'pair_16
      (coe MAlonzo.Code.Once.Arith.Machine.Shape.C_shape'45'int_12)
      (coe MAlonzo.Code.Once.Arith.Machine.Shape.C_shape'45'int_12)
-- Once.Arith.SigOp.AsBlock.pFF
d_pFF_42 :: MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8
d_pFF_42
  = coe
      MAlonzo.Code.Once.Arith.Machine.Shape.C_shape'45'pair_16
      (coe MAlonzo.Code.Once.Arith.Machine.Shape.C_shape'45'float_14)
      (coe MAlonzo.Code.Once.Arith.Machine.Shape.C_shape'45'float_14)
-- Once.Arith.SigOp.AsBlock.prim-block
d_prim'45'block_48 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Arith.Prim.T_ArithPrim_228 -> Maybe T_Lifted_12
d_prim'45'block_48 ~v0 ~v1 v2 = du_prim'45'block_48 v2
du_prim'45'block_48 ::
  MAlonzo.Code.Once.Arith.Prim.T_ArithPrim_228 -> Maybe T_Lifted_12
du_prim'45'block_48 v0
  = case coe v0 of
      MAlonzo.Code.Once.Arith.Prim.C_p'45'add_230
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe
                C_lifted_38 d_pII_40 (coe MAlonzo.Code.Once.Arith.Type.C_NInt_8)
                (coe
                   MAlonzo.Code.Once.Arith.Machine.IR.C_aadd_24
                   (coe
                      MAlonzo.Code.Once.Arith.Machine.IR.C_ainput_20
                      (coe
                         MAlonzo.Code.Once.Arith.Machine.Shape.C_go'45'fst_80
                         (coe MAlonzo.Code.Once.Arith.Machine.Shape.C_here'45'int_70)))
                   (coe
                      MAlonzo.Code.Once.Arith.Machine.IR.C_ainput_20
                      (coe
                         MAlonzo.Code.Once.Arith.Machine.Shape.C_go'45'snd_88
                         (coe MAlonzo.Code.Once.Arith.Machine.Shape.C_here'45'int_70)))))
      MAlonzo.Code.Once.Arith.Prim.C_p'45'sub_232
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe
                C_lifted_38 d_pII_40 (coe MAlonzo.Code.Once.Arith.Type.C_NInt_8)
                (coe
                   MAlonzo.Code.Once.Arith.Machine.IR.C_asub_28
                   (coe
                      MAlonzo.Code.Once.Arith.Machine.IR.C_ainput_20
                      (coe
                         MAlonzo.Code.Once.Arith.Machine.Shape.C_go'45'fst_80
                         (coe MAlonzo.Code.Once.Arith.Machine.Shape.C_here'45'int_70)))
                   (coe
                      MAlonzo.Code.Once.Arith.Machine.IR.C_ainput_20
                      (coe
                         MAlonzo.Code.Once.Arith.Machine.Shape.C_go'45'snd_88
                         (coe MAlonzo.Code.Once.Arith.Machine.Shape.C_here'45'int_70)))))
      MAlonzo.Code.Once.Arith.Prim.C_p'45'mul_234
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe
                C_lifted_38 d_pII_40 (coe MAlonzo.Code.Once.Arith.Type.C_NInt_8)
                (coe
                   MAlonzo.Code.Once.Arith.Machine.IR.C_amul_32
                   (coe
                      MAlonzo.Code.Once.Arith.Machine.IR.C_ainput_20
                      (coe
                         MAlonzo.Code.Once.Arith.Machine.Shape.C_go'45'fst_80
                         (coe MAlonzo.Code.Once.Arith.Machine.Shape.C_here'45'int_70)))
                   (coe
                      MAlonzo.Code.Once.Arith.Machine.IR.C_ainput_20
                      (coe
                         MAlonzo.Code.Once.Arith.Machine.Shape.C_go'45'snd_88
                         (coe MAlonzo.Code.Once.Arith.Machine.Shape.C_here'45'int_70)))))
      MAlonzo.Code.Once.Arith.Prim.C_p'45'div_236
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe
                C_lifted_38 d_pII_40 (coe MAlonzo.Code.Once.Arith.Type.C_NInt_8)
                (coe
                   MAlonzo.Code.Once.Arith.Machine.IR.C_adiv_36
                   (coe
                      MAlonzo.Code.Once.Arith.Machine.IR.C_ainput_20
                      (coe
                         MAlonzo.Code.Once.Arith.Machine.Shape.C_go'45'fst_80
                         (coe MAlonzo.Code.Once.Arith.Machine.Shape.C_here'45'int_70)))
                   (coe
                      MAlonzo.Code.Once.Arith.Machine.IR.C_ainput_20
                      (coe
                         MAlonzo.Code.Once.Arith.Machine.Shape.C_go'45'snd_88
                         (coe MAlonzo.Code.Once.Arith.Machine.Shape.C_here'45'int_70)))))
      MAlonzo.Code.Once.Arith.Prim.C_p'45'mod_238
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe
                C_lifted_38 d_pII_40 (coe MAlonzo.Code.Once.Arith.Type.C_NInt_8)
                (coe
                   MAlonzo.Code.Once.Arith.Machine.IR.C_amod_38
                   (coe
                      MAlonzo.Code.Once.Arith.Machine.IR.C_ainput_20
                      (coe
                         MAlonzo.Code.Once.Arith.Machine.Shape.C_go'45'fst_80
                         (coe MAlonzo.Code.Once.Arith.Machine.Shape.C_here'45'int_70)))
                   (coe
                      MAlonzo.Code.Once.Arith.Machine.IR.C_ainput_20
                      (coe
                         MAlonzo.Code.Once.Arith.Machine.Shape.C_go'45'snd_88
                         (coe MAlonzo.Code.Once.Arith.Machine.Shape.C_here'45'int_70)))))
      MAlonzo.Code.Once.Arith.Prim.C_p'45'neg_240
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe
                C_lifted_38
                (coe MAlonzo.Code.Once.Arith.Machine.Shape.C_shape'45'int_12)
                (coe MAlonzo.Code.Once.Arith.Type.C_NInt_8)
                (coe
                   MAlonzo.Code.Once.Arith.Machine.IR.C_aneg_42
                   (coe
                      MAlonzo.Code.Once.Arith.Machine.IR.C_ainput_20
                      (coe MAlonzo.Code.Once.Arith.Machine.Shape.C_here'45'int_70))))
      MAlonzo.Code.Once.Arith.Prim.C_p'45'fadd_242
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe
                C_lifted_38 d_pFF_42 (coe MAlonzo.Code.Once.Arith.Type.C_NFloat_10)
                (coe
                   MAlonzo.Code.Once.Arith.Machine.IR.C_aadd_24
                   (coe
                      MAlonzo.Code.Once.Arith.Machine.IR.C_ainput_20
                      (coe
                         MAlonzo.Code.Once.Arith.Machine.Shape.C_go'45'fst_80
                         (coe MAlonzo.Code.Once.Arith.Machine.Shape.C_here'45'flt_72)))
                   (coe
                      MAlonzo.Code.Once.Arith.Machine.IR.C_ainput_20
                      (coe
                         MAlonzo.Code.Once.Arith.Machine.Shape.C_go'45'snd_88
                         (coe MAlonzo.Code.Once.Arith.Machine.Shape.C_here'45'flt_72)))))
      MAlonzo.Code.Once.Arith.Prim.C_p'45'fsub_244
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe
                C_lifted_38 d_pFF_42 (coe MAlonzo.Code.Once.Arith.Type.C_NFloat_10)
                (coe
                   MAlonzo.Code.Once.Arith.Machine.IR.C_asub_28
                   (coe
                      MAlonzo.Code.Once.Arith.Machine.IR.C_ainput_20
                      (coe
                         MAlonzo.Code.Once.Arith.Machine.Shape.C_go'45'fst_80
                         (coe MAlonzo.Code.Once.Arith.Machine.Shape.C_here'45'flt_72)))
                   (coe
                      MAlonzo.Code.Once.Arith.Machine.IR.C_ainput_20
                      (coe
                         MAlonzo.Code.Once.Arith.Machine.Shape.C_go'45'snd_88
                         (coe MAlonzo.Code.Once.Arith.Machine.Shape.C_here'45'flt_72)))))
      MAlonzo.Code.Once.Arith.Prim.C_p'45'fmul_246
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe
                C_lifted_38 d_pFF_42 (coe MAlonzo.Code.Once.Arith.Type.C_NFloat_10)
                (coe
                   MAlonzo.Code.Once.Arith.Machine.IR.C_amul_32
                   (coe
                      MAlonzo.Code.Once.Arith.Machine.IR.C_ainput_20
                      (coe
                         MAlonzo.Code.Once.Arith.Machine.Shape.C_go'45'fst_80
                         (coe MAlonzo.Code.Once.Arith.Machine.Shape.C_here'45'flt_72)))
                   (coe
                      MAlonzo.Code.Once.Arith.Machine.IR.C_ainput_20
                      (coe
                         MAlonzo.Code.Once.Arith.Machine.Shape.C_go'45'snd_88
                         (coe MAlonzo.Code.Once.Arith.Machine.Shape.C_here'45'flt_72)))))
      MAlonzo.Code.Once.Arith.Prim.C_p'45'fdiv_248
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe
                C_lifted_38 d_pFF_42 (coe MAlonzo.Code.Once.Arith.Type.C_NFloat_10)
                (coe
                   MAlonzo.Code.Once.Arith.Machine.IR.C_adiv_36
                   (coe
                      MAlonzo.Code.Once.Arith.Machine.IR.C_ainput_20
                      (coe
                         MAlonzo.Code.Once.Arith.Machine.Shape.C_go'45'fst_80
                         (coe MAlonzo.Code.Once.Arith.Machine.Shape.C_here'45'flt_72)))
                   (coe
                      MAlonzo.Code.Once.Arith.Machine.IR.C_ainput_20
                      (coe
                         MAlonzo.Code.Once.Arith.Machine.Shape.C_go'45'snd_88
                         (coe MAlonzo.Code.Once.Arith.Machine.Shape.C_here'45'flt_72)))))
      MAlonzo.Code.Once.Arith.Prim.C_p'45'i2f_250
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe
                C_lifted_38
                (coe MAlonzo.Code.Once.Arith.Machine.Shape.C_shape'45'int_12)
                (coe MAlonzo.Code.Once.Arith.Type.C_NFloat_10)
                (coe
                   MAlonzo.Code.Once.Arith.Machine.IR.C_ai2f_44
                   (coe
                      MAlonzo.Code.Once.Arith.Machine.IR.C_ainput_20
                      (coe MAlonzo.Code.Once.Arith.Machine.Shape.C_here'45'int_70))))
      MAlonzo.Code.Once.Arith.Prim.C_p'45'fneg_252
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe
                C_lifted_38
                (coe MAlonzo.Code.Once.Arith.Machine.Shape.C_shape'45'float_14)
                (coe MAlonzo.Code.Once.Arith.Type.C_NFloat_10)
                (coe
                   MAlonzo.Code.Once.Arith.Machine.IR.C_aneg_42
                   (coe
                      MAlonzo.Code.Once.Arith.Machine.IR.C_ainput_20
                      (coe MAlonzo.Code.Once.Arith.Machine.Shape.C_here'45'flt_72))))
      MAlonzo.Code.Once.Arith.Prim.C_p'45'fcmp_256 v1 v2 v3
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.Arith.Prim.C_p'45'cmp_258 v1
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.SigOp.AsBlock.block-of
d_block'45'of_60 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpSem_74 -> Maybe T_Lifted_12
d_block'45'of_60 ~v0 ~v1 v2 = du_block'45'of_60 v2
du_block'45'of_60 ::
  MAlonzo.Code.Once.SigOp.Info.T_SigOpSem_74 -> Maybe T_Lifted_12
du_block'45'of_60 v0
  = case coe v0 of
      MAlonzo.Code.Once.SigOp.Info.C_blockV_86 v1 v2 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe C_lifted_38 v1 v2 v3)
      MAlonzo.Code.Once.SigOp.Info.C_ffiV_88
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.SigOp.Info.C_callsV_90
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.SigOp.Info.C_emitsV_92
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.SigOp.Info.C_haltsV_94
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.SigOp.Info.C_primV_96 v1
        -> coe du_prim'45'block_48 (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.SigOp.AsBlock.name-at
d_name'45'at_78 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  Maybe T_Lifted_12 -> MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6
d_name'45'at_78 ~v0 ~v1 v2 v3 = du_name'45'at_78 v2 v3
du_name'45'at_78 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  Maybe T_Lifted_12 -> MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6
du_name'45'at_78 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> case coe v2 of
             C_lifted_38 v3 v4 v5
               -> coe
                    MAlonzo.Code.Once.Spec.Name.d_bare_14
                    (coe
                       MAlonzo.Code.Once.Arith.SigOp.Block.d_block'45'name_114 (coe v3)
                       (coe v4) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v0
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.SigOp.AsBlock.sem-at
d_sem'45'at_94 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpSem_74 ->
  Maybe T_Lifted_12 -> MAlonzo.Code.Once.SigOp.Info.T_SigOpSem_74
d_sem'45'at_94 ~v0 ~v1 v2 v3 = du_sem'45'at_94 v2 v3
du_sem'45'at_94 ::
  MAlonzo.Code.Once.SigOp.Info.T_SigOpSem_74 ->
  Maybe T_Lifted_12 -> MAlonzo.Code.Once.SigOp.Info.T_SigOpSem_74
du_sem'45'at_94 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> case coe v2 of
             C_lifted_38 v3 v4 v5
               -> coe MAlonzo.Code.Once.SigOp.Info.C_blockV_86 v3 v4 v5
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v0
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.SigOp.AsBlock.as-block
d_as'45'block_110 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_102 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_102
d_as'45'block_110 ~v0 ~v1 v2 = du_as'45'block_110 v2
du_as'45'block_110 ::
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_102 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_102
du_as'45'block_110 v0
  = coe
      MAlonzo.Code.Once.SigOp.Info.C_mk'45'info''_124
      (coe
         du_name'45'at_78
         (coe MAlonzo.Code.Once.SigOp.Info.d_name_116 (coe v0))
         (coe
            du_block'45'of_60
            (coe MAlonzo.Code.Once.SigOp.Info.d_sem_118 (coe v0))))
      (coe
         du_sem'45'at_94
         (coe MAlonzo.Code.Once.SigOp.Info.d_sem_118 (coe v0))
         (coe
            du_block'45'of_60
            (coe MAlonzo.Code.Once.SigOp.Info.d_sem_118 (coe v0))))
      (coe MAlonzo.Code.Once.SigOp.Info.d_baseA_120 (coe v0))
      (coe MAlonzo.Code.Once.SigOp.Info.d_conB_122 (coe v0))
-- Once.Arith.SigOp.AsBlock.CanonicalAt
d_CanonicalAt_118 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpSem_74 -> ()
d_CanonicalAt_118 = erased
-- Once.Arith.SigOp.AsBlock.Canonical
d_Canonical_148 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_102 -> ()
d_Canonical_148 = erased
-- Once.Arith.SigOp.AsBlock.canon-prim
d_canon'45'prim_160 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Arith.Prim.T_ArithPrim_228 -> AgdaAny
d_canon'45'prim_160 = erased
-- Once.Arith.SigOp.AsBlock.canon-at
d_canon'45'at_204 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpSem_74 -> AgdaAny
d_canon'45'at_204 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Once.SigOp.Info.C_blockV_86 v4 v5 v6 -> erased
      MAlonzo.Code.Once.SigOp.Info.C_ffiV_88
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.SigOp.Info.C_callsV_90
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.SigOp.Info.C_emitsV_92
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.SigOp.Info.C_haltsV_94
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.SigOp.Info.C_primV_96 v4
        -> coe d_canon'45'prim_160 v0 v1 v2 v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.SigOp.AsBlock.as-block-canonical
d_as'45'block'45'canonical_236 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_102 -> AgdaAny
d_as'45'block'45'canonical_236 v0 v1 v2
  = coe
      d_canon'45'at_204 (coe v0) (coe v1)
      (coe MAlonzo.Code.Once.SigOp.Info.d_name_116 (coe v2))
      (coe MAlonzo.Code.Once.SigOp.Info.d_sem_118 (coe v2))
