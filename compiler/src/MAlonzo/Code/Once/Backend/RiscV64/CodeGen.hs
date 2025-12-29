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

module MAlonzo.Code.Once.Backend.RiscV64.CodeGen where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Once.Backend.RiscV64.Syntax
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.Type

-- Once.Backend.RiscV64.CodeGen.neg16
d_neg16_8 :: Integer
d_neg16_8 = coe (-16 :: Integer)
-- Once.Backend.RiscV64.CodeGen.compile-length
d_compile'45'length_14 ::
  MAlonzo.Code.Once.Type.T_Type_4 ->
  MAlonzo.Code.Once.Type.T_Type_4 ->
  MAlonzo.Code.Once.IR.T_IR_4 -> Integer
d_compile'45'length_14 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.IR.C_id_10 -> coe (1 :: Integer)
      MAlonzo.Code.Once.IR.C__'8728'__20 v4 v6 v7
        -> coe
             addInt (coe d_compile'45'length_14 (coe v0) (coe v4) (coe v7))
             (coe d_compile'45'length_14 (coe v4) (coe v1) (coe v6))
      MAlonzo.Code.Once.IR.C_fst_28 -> coe (1 :: Integer)
      MAlonzo.Code.Once.IR.C_snd_36 -> coe (1 :: Integer)
      MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_46 v6 v7
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'42'__10 v8 v9
               -> coe
                    addInt
                    (coe
                       addInt (coe (6 :: Integer))
                       (coe d_compile'45'length_14 (coe v0) (coe v8) (coe v6)))
                    (coe d_compile'45'length_14 (coe v0) (coe v9) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_inl_54 -> coe (4 :: Integer)
      MAlonzo.Code.Once.IR.C_inr_62 -> coe (5 :: Integer)
      MAlonzo.Code.Once.IR.C_'91'_'44'_'93'_72 v6 v7
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'43'__12 v8 v9
               -> coe
                    addInt
                    (coe
                       addInt (coe (6 :: Integer))
                       (coe d_compile'45'length_14 (coe v8) (coe v1) (coe v6)))
                    (coe d_compile'45'length_14 (coe v9) (coe v1) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_terminal_78 -> coe (1 :: Integer)
      MAlonzo.Code.Once.IR.C_initial_84 -> coe (1 :: Integer)
      MAlonzo.Code.Once.IR.C_curry_94 v6
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'8658'__14 v7 v8
               -> coe
                    addInt (coe (14 :: Integer))
                    (coe
                       d_compile'45'length_14
                       (coe MAlonzo.Code.Once.Type.C__'42'__10 (coe v0) (coe v7)) (coe v8)
                       (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_apply_102 -> coe (7 :: Integer)
      MAlonzo.Code.Once.IR.C_fold_108 -> coe (1 :: Integer)
      MAlonzo.Code.Once.IR.C_unfold_114 -> coe (1 :: Integer)
      MAlonzo.Code.Once.IR.C_arr_122 -> coe (1 :: Integer)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Backend.RiscV64.CodeGen.compile-riscv
d_compile'45'riscv_34 ::
  MAlonzo.Code.Once.Type.T_Type_4 ->
  MAlonzo.Code.Once.Type.T_Type_4 ->
  MAlonzo.Code.Once.IR.T_IR_4 ->
  [MAlonzo.Code.Once.Backend.RiscV64.Syntax.T_Instr_86]
d_compile'45'riscv_34 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.IR.C_id_10
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_nop_178)
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.IR.C__'8728'__20 v4 v6 v7
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe d_compile'45'riscv_34 (coe v0) (coe v4) (coe v7))
             (coe d_compile'45'riscv_34 (coe v4) (coe v1) (coe v6))
      MAlonzo.Code.Once.IR.C_fst_28
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_ld_126
                (coe MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_a0_30)
                (coe (0 :: Integer))
                (coe MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_a0_30))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.IR.C_snd_36
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_ld_126
                (coe MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_a0_30)
                (coe (8 :: Integer))
                (coe MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_a0_30))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_46 v6 v7
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'42'__10 v8 v9
               -> coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                    (coe
                       MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_addi_108
                       (coe MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_sp_14)
                       (coe MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_sp_14)
                       (coe d_neg16_8))
                    (coe
                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                       (coe
                          MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_mv_170
                          (coe MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_s1_28)
                          (coe MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_a0_30))
                       (coe
                          MAlonzo.Code.Data.List.Base.du__'43''43'__32
                          (coe d_compile'45'riscv_34 (coe v0) (coe v8) (coe v6))
                          (coe
                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                             (coe
                                MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_sd_140
                                (coe MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_a0_30)
                                (coe (0 :: Integer))
                                (coe MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_sp_14))
                             (coe
                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                (coe
                                   MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_mv_170
                                   (coe MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_a0_30)
                                   (coe MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_s1_28))
                                (coe
                                   MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                   (coe d_compile'45'riscv_34 (coe v0) (coe v9) (coe v7))
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                      (coe
                                         MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_sd_140
                                         (coe MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_a0_30)
                                         (coe (8 :: Integer))
                                         (coe MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_sp_14))
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                         (coe
                                            MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_mv_170
                                            (coe MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_a0_30)
                                            (coe MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_sp_14))
                                         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_inl_54
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_addi_108
                (coe MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_sp_14)
                (coe MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_sp_14)
                (coe d_neg16_8))
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe
                   MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_sd_140
                   (coe MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_zero_10)
                   (coe (0 :: Integer))
                   (coe MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_sp_14))
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                   (coe
                      MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_sd_140
                      (coe MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_a0_30)
                      (coe (8 :: Integer))
                      (coe MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_sp_14))
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                      (coe
                         MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_mv_170
                         (coe MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_a0_30)
                         (coe MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_sp_14))
                      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
      MAlonzo.Code.Once.IR.C_inr_62
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_addi_108
                (coe MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_sp_14)
                (coe MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_sp_14)
                (coe d_neg16_8))
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe
                   MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_li_168
                   (coe MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_t0_20)
                   (coe (1 :: Integer)))
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                   (coe
                      MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_sd_140
                      (coe MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_t0_20)
                      (coe (0 :: Integer))
                      (coe MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_sp_14))
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                      (coe
                         MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_sd_140
                         (coe MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_a0_30)
                         (coe (8 :: Integer))
                         (coe MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_sp_14))
                      (coe
                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                         (coe
                            MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_mv_170
                            (coe MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_a0_30)
                            (coe MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_sp_14))
                         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))
      MAlonzo.Code.Once.IR.C_'91'_'44'_'93'_72 v6 v7
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'43'__12 v8 v9
               -> coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                    (coe
                       MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_ld_126
                       (coe MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_t0_20)
                       (coe (0 :: Integer))
                       (coe MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_a0_30))
                    (coe
                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                       (coe
                          MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_ld_126
                          (coe MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_a0_30)
                          (coe (8 :: Integer))
                          (coe MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_a0_30))
                       (coe
                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                          (coe
                             MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_bne_150
                             (coe MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_t0_20)
                             (coe MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_zero_10)
                             (coe
                                addInt (coe (2 :: Integer))
                                (coe d_compile'45'length_14 (coe v8) (coe v1) (coe v6))))
                          (coe
                             MAlonzo.Code.Data.List.Base.du__'43''43'__32
                             (coe d_compile'45'riscv_34 (coe v8) (coe v1) (coe v6))
                             (coe
                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                (coe
                                   MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_j_172
                                   (coe
                                      addInt (coe (2 :: Integer))
                                      (coe d_compile'45'length_14 (coe v9) (coe v1) (coe v7))))
                                (coe
                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                   (coe
                                      MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_label_182
                                      (coe
                                         addInt (coe (4 :: Integer))
                                         (coe d_compile'45'length_14 (coe v8) (coe v1) (coe v6))))
                                   (coe
                                      MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                      (coe d_compile'45'riscv_34 (coe v9) (coe v1) (coe v7))
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                         (coe
                                            MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_label_182
                                            (coe
                                               addInt
                                               (coe
                                                  addInt (coe (5 :: Integer))
                                                  (coe
                                                     d_compile'45'length_14 (coe v8) (coe v1)
                                                     (coe v6)))
                                               (coe
                                                  d_compile'45'length_14 (coe v9) (coe v1)
                                                  (coe v7))))
                                         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_terminal_78
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_li_168
                (coe MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_a0_30)
                (coe (0 :: Integer)))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.IR.C_initial_84
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_ebreak_180)
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.IR.C_curry_94 v6
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'8658'__14 v7 v8
               -> coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                    (coe
                       MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_addi_108
                       (coe MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_sp_14)
                       (coe MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_sp_14)
                       (coe d_neg16_8))
                    (coe
                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                       (coe
                          MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_sd_140
                          (coe MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_a0_30)
                          (coe (0 :: Integer))
                          (coe MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_sp_14))
                       (coe
                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                          (coe
                             MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_auipc_162
                             (coe MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_t0_20)
                             (coe (0 :: Integer)))
                          (coe
                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                             (coe
                                MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_addi_108
                                (coe MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_t0_20)
                                (coe MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_t0_20)
                                (coe (5 :: Integer)))
                             (coe
                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                (coe
                                   MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_sd_140
                                   (coe MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_t0_20)
                                   (coe (8 :: Integer))
                                   (coe MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_sp_14))
                                (coe
                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                   (coe
                                      MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_mv_170
                                      (coe MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_a0_30)
                                      (coe MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_sp_14))
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                      (coe
                                         MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_j_172
                                         (coe
                                            addInt (coe (7 :: Integer))
                                            (coe
                                               d_compile'45'length_14
                                               (coe
                                                  MAlonzo.Code.Once.Type.C__'42'__10 (coe v0)
                                                  (coe v7))
                                               (coe v8) (coe v6))))
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                         (coe
                                            MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_label_182
                                            (coe (7 :: Integer)))
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                            (coe
                                               MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_addi_108
                                               (coe
                                                  MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_sp_14)
                                               (coe
                                                  MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_sp_14)
                                               (coe d_neg16_8))
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                               (coe
                                                  MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_sd_140
                                                  (coe
                                                     MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_s0_26)
                                                  (coe (0 :: Integer))
                                                  (coe
                                                     MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_sp_14))
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                  (coe
                                                     MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_sd_140
                                                     (coe
                                                        MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_a0_30)
                                                     (coe (8 :: Integer))
                                                     (coe
                                                        MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_sp_14))
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                     (coe
                                                        MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_mv_170
                                                        (coe
                                                           MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_a0_30)
                                                        (coe
                                                           MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_sp_14))
                                                     (coe
                                                        MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                                        (coe
                                                           d_compile'45'riscv_34
                                                           (coe
                                                              MAlonzo.Code.Once.Type.C__'42'__10
                                                              (coe v0) (coe v7))
                                                           (coe v8) (coe v6))
                                                        (coe
                                                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                           (coe
                                                              MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_ret_176)
                                                           (coe
                                                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                              (coe
                                                                 MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_label_182
                                                                 (coe
                                                                    addInt (coe (13 :: Integer))
                                                                    (coe
                                                                       d_compile'45'length_14
                                                                       (coe
                                                                          MAlonzo.Code.Once.Type.C__'42'__10
                                                                          (coe v0) (coe v7))
                                                                       (coe v8) (coe v6))))
                                                              (coe
                                                                 MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))))))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_apply_102
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_ld_126
                (coe MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_t1_22)
                (coe (0 :: Integer))
                (coe MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_a0_30))
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe
                   MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_ld_126
                   (coe MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_t2_24)
                   (coe (8 :: Integer))
                   (coe MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_a0_30))
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                   (coe
                      MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_ld_126
                      (coe MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_s0_26)
                      (coe (0 :: Integer))
                      (coe MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_t1_22))
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                      (coe
                         MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_ld_126
                         (coe MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_t0_20)
                         (coe (8 :: Integer))
                         (coe MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_t1_22))
                      (coe
                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                         (coe
                            MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_mv_170
                            (coe MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_a0_30)
                            (coe MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_t2_24))
                         (coe
                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                            (coe
                               MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_jalr_166
                               (coe MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_ra_12)
                               (coe MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_t0_20)
                               (coe (0 :: Integer)))
                            (coe
                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                               (coe MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_nop_178)
                               (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))
      MAlonzo.Code.Once.IR.C_fold_108
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_nop_178)
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.IR.C_unfold_114
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_nop_178)
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.IR.C_arr_122
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_nop_178)
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      _ -> MAlonzo.RTE.mazUnreachableError
