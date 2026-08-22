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
import qualified MAlonzo.Code.Once.Arith.Machine.IR
import qualified MAlonzo.Code.Once.Arith.Machine.Recognise
import qualified MAlonzo.Code.Once.Arith.Machine.Shape
import qualified MAlonzo.Code.Once.Arith.SigOp.Block
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.IRTy
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
                                                        MAlonzo.Code.Once.Arith.Machine.Shape.C_shape'45'pair_14
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
d_has'45'op_36 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 -> Bool
d_has'45'op_36 ~v0 v1 = du_has'45'op_36 v1
du_has'45'op_36 ::
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 -> Bool
du_has'45'op_36 v0
  = case coe v0 of
      MAlonzo.Code.Once.Arith.Machine.IR.C_alit_14 v1
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Arith.Machine.IR.C_ainput_16 v1
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Arith.Machine.IR.C_aadd_18 v1 v2
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      MAlonzo.Code.Once.Arith.Machine.IR.C_asub_20 v1 v2
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      MAlonzo.Code.Once.Arith.Machine.IR.C_amul_22 v1 v2
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      MAlonzo.Code.Once.Arith.Machine.IR.C_adiv_24 v1 v2
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      MAlonzo.Code.Once.Arith.Machine.IR.C_amod_26 v1 v2
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      MAlonzo.Code.Once.Arith.Machine.IR.C_aneg_28 v1
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Machine.Rewrite.block-as-ir
d_block'45'as'45'ir_42 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.IR.T_IR_16
d_block'45'as'45'ir_42 ~v0 v1 ~v2 v3
  = du_block'45'as'45'ir_42 v1 v3
du_block'45'as'45'ir_42 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.IR.T_IR_16
du_block'45'as'45'ir_42 v0 v1
  = coe
      MAlonzo.Code.Once.IR.C_SigOp_154
      (coe
         MAlonzo.Code.Once.Arith.Machine.IR.d_shape'45'as'45'type_120
         (coe v0))
      (coe MAlonzo.Code.Once.Type.C_Int_136)
      (coe
         MAlonzo.Code.Once.Arith.SigOp.Block.d_block'45'info_394 (coe v0)
         (coe v1))
-- Once.Arith.Machine.Rewrite.try-lift
d_try'45'lift_58 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_try'45'lift_58 v0 v1 v2
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
                                     = coe
                                         MAlonzo.Code.Once.Arith.Machine.Recognise.du_recognise'45'body_44
                                         (coe v6) (coe v0) (coe v2) in
                               coe
                                 (case coe v8 of
                                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
                                      -> let v10 = coe du_has'45'op_36 (coe v9) in
                                         coe
                                           (if coe v10
                                              then coe
                                                     MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                     (coe
                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                        (coe
                                                           du_block'45'as'45'ir_42 (coe v6)
                                                           (coe v9))
                                                        (coe
                                                           MAlonzo.Code.Once.Arith.Machine.IR.C_mk'45'block_136
                                                           (coe v6) (coe v9)))
                                              else coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
                                    MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v8
                                    _ -> MAlonzo.RTE.mazUnreachableError)
                          _ -> MAlonzo.RTE.mazUnreachableError
                   MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v4
                   _ -> MAlonzo.RTE.mazUnreachableError)
         _ -> coe v3)
-- Once.Arith.Machine.Rewrite.rewrite-ir
d_rewrite'45'ir_130 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_rewrite'45'ir_130 v0 v1 v2
  = let v3 = d_try'45'lift_58 (coe v0) (coe v1) (coe v2) in
    coe
      (case coe v3 of
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
           -> coe du_walk_154 (coe v0) (coe v1) (coe v2)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Arith.Machine.Rewrite._.walk
d_walk_154 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_walk_154 ~v0 ~v1 ~v2 v3 v4 v5 = du_walk_154 v3 v4 v5
du_walk_154 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_walk_154 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.IR.C_id_22
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe MAlonzo.Code.Once.IR.C_id_22)
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.IR.C__'8728'__30 v4 v6 v7
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Once.IR.C__'8728'__30 v4
                (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                   (coe d_rewrite'45'ir_130 (coe v4) (coe v1) (coe v6)))
                (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                   (coe d_rewrite'45'ir_130 (coe v0) (coe v4) (coe v7))))
             (coe
                MAlonzo.Code.Data.List.Base.du__'43''43'__32
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                   (coe d_rewrite'45'ir_130 (coe v4) (coe v1) (coe v6)))
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                   (coe d_rewrite'45'ir_130 (coe v0) (coe v4) (coe v7))))
      MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_38 v6 v7 v8
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v9 v10
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_38
                       (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                          (coe d_rewrite'45'ir_130 (coe v0) (coe v9) (coe v6)))
                       (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                          (coe d_rewrite'45'ir_130 (coe v0) (coe v10) (coe v7)))
                       v8)
                    (coe
                       MAlonzo.Code.Data.List.Base.du__'43''43'__32
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                          (coe d_rewrite'45'ir_130 (coe v0) (coe v9) (coe v6)))
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                          (coe d_rewrite'45'ir_130 (coe v0) (coe v10) (coe v7))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_fst_44
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe MAlonzo.Code.Once.IR.C_fst_44)
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.IR.C_snd_50
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe MAlonzo.Code.Once.IR.C_snd_50)
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.IR.C_inl_56 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe MAlonzo.Code.Once.IR.C_inl_56 v5)
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.IR.C_inr_62 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe MAlonzo.Code.Once.IR.C_inr_62 v5)
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.IR.C_case_70 v6 v7
        -> case coe v0 of
             MAlonzo.Code.Once.IRTy.C__'43'__22 v8 v9
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       MAlonzo.Code.Once.IR.C_case_70
                       (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                          (coe d_rewrite'45'ir_130 (coe v8) (coe v1) (coe v6)))
                       (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                          (coe d_rewrite'45'ir_130 (coe v9) (coe v1) (coe v7))))
                    (coe
                       MAlonzo.Code.Data.List.Base.du__'43''43'__32
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                          (coe d_rewrite'45'ir_130 (coe v8) (coe v1) (coe v6)))
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                          (coe d_rewrite'45'ir_130 (coe v9) (coe v1) (coe v7))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_terminal_74
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe MAlonzo.Code.Once.IR.C_terminal_74)
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.IR.C_initial_78
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe MAlonzo.Code.Once.IR.C_initial_78)
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.IR.C_curry_86 v6 v7
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C__'8667'__24 v8 v9
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       MAlonzo.Code.Once.IR.C_curry_86
                       (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                          (coe
                             d_rewrite'45'ir_130
                             (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v0) (coe v8)) (coe v9)
                             (coe v6)))
                       v7)
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                       (coe
                          d_rewrite'45'ir_130
                          (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v0) (coe v8)) (coe v9)
                          (coe v6)))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_apply_92
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe MAlonzo.Code.Once.IR.C_apply_92)
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.IR.C_In_96 v4 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe MAlonzo.Code.Once.IR.C_In_96 v4 v5)
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.IR.C_out'45'μ_100 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe MAlonzo.Code.Once.IR.C_out'45'μ_100 v4)
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.IR.C_Cata_106 v4 v6
        -> case coe v0 of
             MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v7
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       MAlonzo.Code.Once.IR.C_Cata_106 v4
                       (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                          (coe
                             d_rewrite'45'ir_130
                             (coe
                                MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v7) (coe v1))
                             (coe v1) (coe v6))))
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                       (coe
                          d_rewrite'45'ir_130
                          (coe
                             MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v7) (coe v1))
                          (coe v1) (coe v6)))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_Para_112 v4 v6
        -> case coe v0 of
             MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v7
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       MAlonzo.Code.Once.IR.C_Para_112 v4
                       (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                          (coe
                             d_rewrite'45'ir_130
                             (coe
                                MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v7)
                                (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v0) (coe v1)))
                             (coe v1) (coe v6))))
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                       (coe
                          d_rewrite'45'ir_130
                          (coe
                             MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v7)
                             (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v0) (coe v1)))
                          (coe v1) (coe v6)))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_Out_116 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe MAlonzo.Code.Once.IR.C_Out_116 v4)
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.IR.C_in'45'ν_120 v4 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe MAlonzo.Code.Once.IR.C_in'45'ν_120 v4 v5)
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.IR.C_Ana_126 v4 v6
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C_ν'45'type_28 v7
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       MAlonzo.Code.Once.IR.C_Ana_126 v4
                       (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                          (coe
                             d_rewrite'45'ir_130 (coe v0)
                             (coe
                                MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v7) (coe v0))
                             (coe v6))))
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                       (coe
                          d_rewrite'45'ir_130 (coe v0)
                          (coe
                             MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v7) (coe v0))
                          (coe v6)))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_Hylo_134 v3 v5 v6 v8 v9
        -> case coe v0 of
             MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v10
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       MAlonzo.Code.Once.IR.C_Hylo_134 v3 v5 v6
                       (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                          (coe
                             d_rewrite'45'ir_130
                             (coe
                                MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v3) (coe v1))
                             (coe v1) (coe v8)))
                       (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                          (coe du_walk'45'nt_160 (coe v10) (coe v3) (coe v9))))
                    (coe
                       MAlonzo.Code.Data.List.Base.du__'43''43'__32
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                          (coe
                             d_rewrite'45'ir_130
                             (coe
                                MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v3) (coe v1))
                             (coe v1) (coe v8)))
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                          (coe du_walk'45'nt_160 (coe v10) (coe v3) (coe v9))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_Fuse_142 v3 v5 v6 v8 v9
        -> case coe v0 of
             MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v10
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       MAlonzo.Code.Once.IR.C_Fuse_142 v3 v5 v6
                       (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                          (coe
                             d_rewrite'45'ir_130
                             (coe
                                MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v3) (coe v1))
                             (coe v1) (coe v8)))
                       (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                          (coe du_walk'45'nt_160 (coe v10) (coe v3) (coe v9))))
                    (coe
                       MAlonzo.Code.Data.List.Base.du__'43''43'__32
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                          (coe
                             d_rewrite'45'ir_130
                             (coe
                                MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v3) (coe v1))
                             (coe v1) (coe v8)))
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                          (coe du_walk'45'nt_160 (coe v10) (coe v3) (coe v9))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_free'45'heap_144 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.IR.C_const_148 v4 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe MAlonzo.Code.Once.IR.C_const_148 v4 v5)
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.IR.C_SigOp_154 v3 v4 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Machine.Rewrite._.walk-nt
d_walk'45'nt_160 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IR.T_NatTr_18 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_walk'45'nt_160 ~v0 ~v1 ~v2 v3 v4 v5 = du_walk'45'nt_160 v3 v4 v5
du_walk'45'nt_160 ::
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IR.T_NatTr_18 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_walk'45'nt_160 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.IR.C_ntId_156
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.IR.C_ntK_162 v5
        -> case coe v0 of
             MAlonzo.Code.Once.IRTy.C_K_8 v6
               -> case coe v1 of
                    MAlonzo.Code.Once.IRTy.C_K_8 v7
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              MAlonzo.Code.Once.IR.C_ntK_162
                              (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                 (coe d_rewrite'45'ir_130 (coe v6) (coe v7) (coe v5))))
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                              (coe d_rewrite'45'ir_130 (coe v6) (coe v7) (coe v5)))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_ntFst_170 v6
        -> case coe v0 of
             MAlonzo.Code.Once.IRTy.C__'8855'__14 v7 v8
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       MAlonzo.Code.Once.IR.C_ntFst_170
                       (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                          (coe du_walk'45'nt_160 (coe v7) (coe v1) (coe v6))))
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                       (coe du_walk'45'nt_160 (coe v7) (coe v1) (coe v6)))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_ntSnd_178 v6
        -> case coe v0 of
             MAlonzo.Code.Once.IRTy.C__'8855'__14 v7 v8
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       MAlonzo.Code.Once.IR.C_ntSnd_178
                       (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                          (coe du_walk'45'nt_160 (coe v8) (coe v1) (coe v6))))
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                       (coe du_walk'45'nt_160 (coe v8) (coe v1) (coe v6)))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_ntCase_186 v6 v7
        -> case coe v0 of
             MAlonzo.Code.Once.IRTy.C__'8853'__12 v8 v9
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       MAlonzo.Code.Once.IR.C_ntCase_186
                       (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                          (coe du_walk'45'nt_160 (coe v8) (coe v1) (coe v6)))
                       (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                          (coe du_walk'45'nt_160 (coe v9) (coe v1) (coe v7))))
                    (coe
                       MAlonzo.Code.Data.List.Base.du__'43''43'__32
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                          (coe du_walk'45'nt_160 (coe v8) (coe v1) (coe v6)))
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                          (coe du_walk'45'nt_160 (coe v9) (coe v1) (coe v7))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_ntInl_194 v6
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C__'8853'__12 v7 v8
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       MAlonzo.Code.Once.IR.C_ntInl_194
                       (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                          (coe du_walk'45'nt_160 (coe v0) (coe v7) (coe v6))))
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                       (coe du_walk'45'nt_160 (coe v0) (coe v7) (coe v6)))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_ntInr_202 v6
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C__'8853'__12 v7 v8
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       MAlonzo.Code.Once.IR.C_ntInr_202
                       (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                          (coe du_walk'45'nt_160 (coe v0) (coe v8) (coe v6))))
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                       (coe du_walk'45'nt_160 (coe v0) (coe v8) (coe v6)))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_ntPair_210 v6 v7
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C__'8855'__14 v8 v9
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       MAlonzo.Code.Once.IR.C_ntPair_210
                       (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                          (coe du_walk'45'nt_160 (coe v0) (coe v8) (coe v6)))
                       (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                          (coe du_walk'45'nt_160 (coe v0) (coe v9) (coe v7))))
                    (coe
                       MAlonzo.Code.Data.List.Base.du__'43''43'__32
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                          (coe du_walk'45'nt_160 (coe v0) (coe v8) (coe v6)))
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                          (coe du_walk'45'nt_160 (coe v0) (coe v9) (coe v7))))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
