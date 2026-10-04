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

module MAlonzo.Code.Once.Arith.Machine.Rewrite where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Once.Arith.CmpOp
import qualified MAlonzo.Code.Once.Arith.Machine.IR
import qualified MAlonzo.Code.Once.Arith.Machine.Recognise
import qualified MAlonzo.Code.Once.Arith.Machine.Shape
import qualified MAlonzo.Code.Once.Arith.SigOp.Block
import qualified MAlonzo.Code.Once.Arith.SigOp.Compare
import qualified MAlonzo.Code.Once.Arith.Type
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.IRTy
import qualified MAlonzo.Code.Once.SigOp.Info
import qualified MAlonzo.Code.Once.Type

-- Once.Arith.Machine.Rewrite.shape-of
d_shape'45'of_12 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_shape'45'of_12 v0
  = let v1 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.IRTy.C_Unit_16
           -> coe
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                   (coe MAlonzo.Code.Once.Arith.Machine.Shape.C_shape'45'unit_10)
                   erased)
         MAlonzo.Code.Once.IRTy.C__'42'__20 v2 v3
           -> let v4 = d_shape'45'of_12 (coe v2) in
              coe
                (let v5 = d_shape'45'of_12 (coe v3) in
                 coe
                   (case coe v4 of
                      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                        -> case coe v6 of
                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                               -> case coe v5 of
                                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
                                      -> case coe v9 of
                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                                             -> coe
                                                  MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                     (coe
                                                        MAlonzo.Code.Once.Arith.Machine.Shape.C_shape'45'pair_16
                                                        (coe v7) (coe v10))
                                                     erased)
                                           _ -> MAlonzo.RTE.mazUnreachableError
                                    _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                             _ -> MAlonzo.RTE.mazUnreachableError
                      _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
         MAlonzo.Code.Once.IRTy.C_Int_30
           -> coe
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                   (coe MAlonzo.Code.Once.Arith.Machine.Shape.C_shape'45'int_12)
                   erased)
         _ -> coe v1)
-- Once.Arith.Machine.Rewrite.has-op
d_has'45'op_38 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Type.T_NumType_6 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 -> Bool
d_has'45'op_38 ~v0 ~v1 v2 = du_has'45'op_38 v2
du_has'45'op_38 ::
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 -> Bool
du_has'45'op_38 v0
  = case coe v0 of
      MAlonzo.Code.Once.Arith.Machine.IR.C_alit_14 v1
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Arith.Machine.IR.C_aflit_16 v1
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Arith.Machine.IR.C_ainput_20 v2
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Arith.Machine.IR.C_aadd_24 v2 v3
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      MAlonzo.Code.Once.Arith.Machine.IR.C_asub_28 v2 v3
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      MAlonzo.Code.Once.Arith.Machine.IR.C_amul_32 v2 v3
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      MAlonzo.Code.Once.Arith.Machine.IR.C_adiv_36 v2 v3
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      MAlonzo.Code.Once.Arith.Machine.IR.C_amod_38 v1 v2
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      MAlonzo.Code.Once.Arith.Machine.IR.C_aneg_42 v2
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      MAlonzo.Code.Once.Arith.Machine.IR.C_ai2f_44 v1
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      MAlonzo.Code.Once.Arith.Machine.IR.C_acmp_46 v1 v2 v3
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Machine.Rewrite.block-as-ir
d_block'45'as'45'ir_46 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Type.T_NumType_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.IR.T_IR_16
d_block'45'as'45'ir_46 ~v0 v1 v2 ~v3 v4
  = du_block'45'as'45'ir_46 v1 v2 v4
du_block'45'as'45'ir_46 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Type.T_NumType_6 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.IR.T_IR_16
du_block'45'as'45'ir_46 v0 v1 v2
  = coe
      MAlonzo.Code.Once.IR.C_SigOp_130
      (coe
         MAlonzo.Code.Once.Arith.Machine.IR.d_shape'45'as'45'type_158
         (coe v0))
      (coe
         MAlonzo.Code.Once.Arith.Machine.IR.d_numtype'45'as'45'type_164
         (coe v1))
      (coe
         MAlonzo.Code.Once.Arith.SigOp.Block.d_block'45'info_554 (coe v0)
         (coe v1) (coe v2))
-- Once.Arith.Machine.Rewrite.try-lift
d_try'45'lift_64 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_try'45'lift_64 v0 v1 v2
  = let v3 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
    coe
      (case coe v1 of
         MAlonzo.Code.Once.IRTy.C_Int_30
           -> let v4 = d_shape'45'of_12 (coe v0) in
              coe
                (case coe v4 of
                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
                     -> case coe v5 of
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                            -> let v8
                                     = MAlonzo.Code.Once.Arith.Machine.Recognise.d_rb'45'at_490
                                         (coe v6) (coe v0) (coe v1) (coe v2)
                                         (coe
                                            MAlonzo.Code.Once.Arith.Machine.Recognise.du_rb'45'view_402
                                            (coe v2)) in
                               coe
                                 (case coe v8 of
                                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
                                      -> let v10 = coe du_has'45'op_38 (coe v9) in
                                         coe
                                           (if coe v10
                                              then coe
                                                     MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                     (coe
                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                        (coe
                                                           du_block'45'as'45'ir_46 (coe v6)
                                                           (coe
                                                              MAlonzo.Code.Once.Arith.Type.C_NInt_8)
                                                           (coe v9))
                                                        (coe
                                                           MAlonzo.Code.Once.Arith.Machine.IR.C_mk'45'block_180
                                                           (coe v6)
                                                           (coe
                                                              MAlonzo.Code.Once.Arith.Type.C_NInt_8)
                                                           (coe v9)))
                                              else coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
                                    MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v8
                                    _ -> MAlonzo.RTE.mazUnreachableError)
                          _ -> MAlonzo.RTE.mazUnreachableError
                   MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v4
                   _ -> MAlonzo.RTE.mazUnreachableError)
         MAlonzo.Code.Once.IRTy.C_Float_32
           -> let v4 = d_shape'45'of_12 (coe v0) in
              coe
                (case coe v4 of
                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
                     -> case coe v5 of
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                            -> let v8
                                     = MAlonzo.Code.Once.Arith.Machine.Recognise.d_rbf'45'at_650
                                         (coe v6) (coe v0) (coe v1) (coe v2)
                                         (coe
                                            MAlonzo.Code.Once.Arith.Machine.Recognise.du_rb'45'view_402
                                            (coe v2)) in
                               coe
                                 (case coe v8 of
                                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
                                      -> let v10 = coe du_has'45'op_38 (coe v9) in
                                         coe
                                           (if coe v10
                                              then coe
                                                     MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                     (coe
                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                        (coe
                                                           du_block'45'as'45'ir_46 (coe v6)
                                                           (coe
                                                              MAlonzo.Code.Once.Arith.Type.C_NFloat_10)
                                                           (coe v9))
                                                        (coe
                                                           MAlonzo.Code.Once.Arith.Machine.IR.C_mk'45'block_180
                                                           (coe v6)
                                                           (coe
                                                              MAlonzo.Code.Once.Arith.Type.C_NFloat_10)
                                                           (coe v9)))
                                              else coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
                                    MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v8
                                    _ -> MAlonzo.RTE.mazUnreachableError)
                          _ -> MAlonzo.RTE.mazUnreachableError
                   MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v4
                   _ -> MAlonzo.RTE.mazUnreachableError)
         _ -> coe v3)
-- Once.Arith.Machine.Rewrite.sigop-blocks
d_sigop'45'blocks_198 ::
  Maybe MAlonzo.Code.Once.Arith.CmpOp.T_CmpOp_6 ->
  [MAlonzo.Code.Once.Arith.Machine.IR.T_ArithBlock_166]
d_sigop'45'blocks_198 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.Arith.SigOp.Compare.d_cmp'45'block_20 (coe v1))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Machine.Rewrite.bare-at
d_bare'45'at_208 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bare'45'at_208 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
        -> case coe v4 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v5)
                    (coe
                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v6)
                       (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe MAlonzo.Code.Once.IR.C_SigOp_130 (coe v0) (coe v1) (coe v2))
             (coe
                d_sigop'45'blocks_198
                (coe
                   MAlonzo.Code.Once.Arith.SigOp.Compare.du_cmp'45'of_12
                   (coe MAlonzo.Code.Once.SigOp.Info.d_sem_180 (coe v2))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Machine.Rewrite.rewrite-ir
d_rewrite'45'ir_222 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_rewrite'45'ir_222 v0 v1 v2
  = coe
      d_rw'45'at_228 (coe v0) (coe v1) (coe v2)
      (coe d_try'45'lift_64 (coe v0) (coe v1) (coe v2))
-- Once.Arith.Machine.Rewrite.rw-at
d_rw'45'at_228 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_rw'45'at_228 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
        -> case coe v4 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v5)
                    (coe
                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v6)
                       (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe d_walk_234 (coe v0) (coe v1) (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Machine.Rewrite.walk
d_walk_234 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_walk_234 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.IR.C_id_20
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe MAlonzo.Code.Once.IR.C_id_20)
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.IR.C__'8728'__28 v4 v6 v7
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Once.IR.C__'8728'__28 v4
                (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                   (coe d_rewrite'45'ir_222 (coe v4) (coe v1) (coe v6)))
                (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                   (coe d_rewrite'45'ir_222 (coe v0) (coe v4) (coe v7))))
             (coe
                MAlonzo.Code.Data.List.Base.du__'43''43'__32
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                   (coe d_rewrite'45'ir_222 (coe v4) (coe v1) (coe v6)))
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                   (coe d_rewrite'45'ir_222 (coe v0) (coe v4) (coe v7))))
      MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v6 v7
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v8 v9
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36
                       (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                          (coe d_rewrite'45'ir_222 (coe v0) (coe v8) (coe v6)))
                       (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                          (coe d_rewrite'45'ir_222 (coe v0) (coe v9) (coe v7))))
                    (coe
                       MAlonzo.Code.Data.List.Base.du__'43''43'__32
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                          (coe d_rewrite'45'ir_222 (coe v0) (coe v8) (coe v6)))
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                          (coe d_rewrite'45'ir_222 (coe v0) (coe v9) (coe v7))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_fst_42
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe MAlonzo.Code.Once.IR.C_fst_42)
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.IR.C_snd_48
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe MAlonzo.Code.Once.IR.C_snd_48)
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.IR.C_inl_54
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe MAlonzo.Code.Once.IR.C_inl_54)
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.IR.C_inr_60
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe MAlonzo.Code.Once.IR.C_inr_60)
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.IR.C_case_68 v6 v7
        -> case coe v0 of
             MAlonzo.Code.Once.IRTy.C__'43'__22 v8 v9
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       MAlonzo.Code.Once.IR.C_case_68
                       (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                          (coe d_rewrite'45'ir_222 (coe v8) (coe v1) (coe v6)))
                       (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                          (coe d_rewrite'45'ir_222 (coe v9) (coe v1) (coe v7))))
                    (coe
                       MAlonzo.Code.Data.List.Base.du__'43''43'__32
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                          (coe d_rewrite'45'ir_222 (coe v8) (coe v1) (coe v6)))
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                          (coe d_rewrite'45'ir_222 (coe v9) (coe v1) (coe v7))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_terminal_72
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe MAlonzo.Code.Once.IR.C_terminal_72)
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.IR.C_initial_76
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe MAlonzo.Code.Once.IR.C_initial_76)
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.IR.C_curry_84 v6
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C__'8667'__24 v7 v8
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       MAlonzo.Code.Once.IR.C_curry_84
                       (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                          (coe
                             d_rewrite'45'ir_222
                             (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v0) (coe v7)) (coe v8)
                             (coe v6))))
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                       (coe
                          d_rewrite'45'ir_222
                          (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v0) (coe v7)) (coe v8)
                          (coe v6)))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_apply_90
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe MAlonzo.Code.Once.IR.C_apply_90)
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.IR.C_In_94 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe MAlonzo.Code.Once.IR.C_In_94 v4)
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.IR.C_out'45'μ_98 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe MAlonzo.Code.Once.IR.C_out'45'μ_98 v4)
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.IR.C_Cata_106 v4 v7
        -> case coe v0 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v8 v9
               -> case coe v9 of
                    MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v10
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              MAlonzo.Code.Once.IR.C_Cata_106 v4
                              (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                 (coe
                                    d_rewrite'45'ir_222
                                    (coe
                                       MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v8)
                                       (coe
                                          MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_80 (coe v10)
                                          (coe v1)))
                                    (coe v1) (coe v7))))
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                              (coe
                                 d_rewrite'45'ir_222
                                 (coe
                                    MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v8)
                                    (coe
                                       MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_80 (coe v10)
                                       (coe v1)))
                                 (coe v1) (coe v7)))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_Out_110 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe MAlonzo.Code.Once.IR.C_Out_110 v4)
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.IR.C_in'45'ν_114 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe MAlonzo.Code.Once.IR.C_in'45'ν_114 v4)
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.IR.C_Ana_120 v4 v6
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C_ν'45'type_28 v7
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       MAlonzo.Code.Once.IR.C_Ana_120 v4
                       (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                          (coe
                             d_rewrite'45'ir_222 (coe v0)
                             (coe
                                MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_80 (coe v7) (coe v0))
                             (coe v6))))
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                       (coe
                          d_rewrite'45'ir_222 (coe v0)
                          (coe
                             MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_80 (coe v7) (coe v0))
                          (coe v6)))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_const_124 v4 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe MAlonzo.Code.Once.IR.C_const_124 v4 v5)
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.IR.C_SigOp_130 v3 v4 v5
        -> coe
             d_bare'45'at_208 (coe v3) (coe v4) (coe v5)
             (coe
                d_try'45'lift_64
                (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v3))
                (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v4))
                (coe
                   MAlonzo.Code.Once.IR.C__'8728'__28
                   (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v3)) v2
                   (coe MAlonzo.Code.Once.IR.C_id_20)))
      MAlonzo.Code.Once.IR.C_Call_136 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe MAlonzo.Code.Once.IR.C_Call_136 v5)
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      _ -> MAlonzo.RTE.mazUnreachableError
