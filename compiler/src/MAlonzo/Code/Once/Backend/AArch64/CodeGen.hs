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

module MAlonzo.Code.Once.Backend.AArch64.CodeGen where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Once.Backend.AArch64.Syntax
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.Type

-- Once.Backend.AArch64.CodeGen.compile-length
d_compile'45'length_12 ::
  MAlonzo.Code.Once.Type.T_Type_4 ->
  MAlonzo.Code.Once.Type.T_Type_4 ->
  MAlonzo.Code.Once.IR.T_IR_4 -> Integer
d_compile'45'length_12 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.IR.C_id_8 -> coe (1 :: Integer)
      MAlonzo.Code.Once.IR.C__'8728'__16 v4 v6 v7
        -> coe
             addInt
             (coe
                addInt (coe (1 :: Integer))
                (coe d_compile'45'length_12 (coe v0) (coe v4) (coe v7)))
             (coe d_compile'45'length_12 (coe v4) (coe v1) (coe v6))
      MAlonzo.Code.Once.IR.C_fst_22 -> coe (1 :: Integer)
      MAlonzo.Code.Once.IR.C_snd_28 -> coe (1 :: Integer)
      MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v6 v7
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'42'__10 v8 v9
               -> coe
                    addInt
                    (coe
                       addInt (coe (7 :: Integer))
                       (coe d_compile'45'length_12 (coe v0) (coe v8) (coe v6)))
                    (coe d_compile'45'length_12 (coe v0) (coe v9) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_inl_42 -> coe (4 :: Integer)
      MAlonzo.Code.Once.IR.C_inr_48 -> coe (5 :: Integer)
      MAlonzo.Code.Once.IR.C_'91'_'44'_'93'_56 v6 v7
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'43'__12 v8 v9
               -> coe
                    addInt
                    (coe
                       addInt (coe (8 :: Integer))
                       (coe d_compile'45'length_12 (coe v8) (coe v1) (coe v6)))
                    (coe d_compile'45'length_12 (coe v9) (coe v1) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_terminal_60 -> coe (1 :: Integer)
      MAlonzo.Code.Once.IR.C_initial_64 -> coe (1 :: Integer)
      MAlonzo.Code.Once.IR.C_curry_72 v6
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'8658'__14 v7 v8
               -> coe
                    addInt (coe (12 :: Integer))
                    (coe
                       d_compile'45'length_12
                       (coe MAlonzo.Code.Once.Type.C__'42'__10 (coe v0) (coe v7)) (coe v8)
                       (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_apply_78 -> coe (6 :: Integer)
      MAlonzo.Code.Once.IR.C_fold_82 -> coe (1 :: Integer)
      MAlonzo.Code.Once.IR.C_unfold_86 -> coe (1 :: Integer)
      MAlonzo.Code.Once.IR.C_arr_92 -> coe (1 :: Integer)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Backend.AArch64.CodeGen.compile-aarch64
d_compile'45'aarch64_32 ::
  MAlonzo.Code.Once.Type.T_Type_4 ->
  MAlonzo.Code.Once.Type.T_Type_4 ->
  MAlonzo.Code.Once.IR.T_IR_4 ->
  [MAlonzo.Code.Once.Backend.AArch64.Syntax.T_Instr_88]
d_compile'45'aarch64_32 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.IR.C_id_8
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe MAlonzo.Code.Once.Backend.AArch64.Syntax.C_nop_124)
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.IR.C__'8728'__16 v4 v6 v7
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe d_compile'45'aarch64_32 (coe v0) (coe v4) (coe v7))
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe MAlonzo.Code.Once.Backend.AArch64.Syntax.C_nop_124)
                (coe
                   MAlonzo.Code.Data.List.Base.du__'43''43'__32
                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                   (coe d_compile'45'aarch64_32 (coe v4) (coe v1) (coe v6))))
      MAlonzo.Code.Once.IR.C_fst_22
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.Backend.AArch64.Syntax.C_ldr_92
                (coe MAlonzo.Code.Once.Backend.AArch64.Syntax.C_x0_10)
                (coe
                   MAlonzo.Code.Once.Backend.AArch64.Syntax.C_base_74
                   (coe MAlonzo.Code.Once.Backend.AArch64.Syntax.C_x0_10)))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.IR.C_snd_28
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.Backend.AArch64.Syntax.C_ldr_92
                (coe MAlonzo.Code.Once.Backend.AArch64.Syntax.C_x0_10)
                (coe
                   MAlonzo.Code.Once.Backend.AArch64.Syntax.C_base'43'imm_76
                   (coe MAlonzo.Code.Once.Backend.AArch64.Syntax.C_x0_10)
                   (coe (8 :: Integer))))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v6 v7
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'42'__10 v8 v9
               -> coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                    (coe
                       MAlonzo.Code.Once.Backend.AArch64.Syntax.C_sub'45'sp_118
                       (coe (16 :: Integer)))
                    (coe
                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                       (coe
                          MAlonzo.Code.Once.Backend.AArch64.Syntax.C_mov'45'from'45'sp_122
                          (coe MAlonzo.Code.Once.Backend.AArch64.Syntax.C_x21_52))
                       (coe
                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                          (coe
                             MAlonzo.Code.Once.Backend.AArch64.Syntax.C_mov_90
                             (coe MAlonzo.Code.Once.Backend.AArch64.Syntax.C_x20_50)
                             (coe
                                MAlonzo.Code.Once.Backend.AArch64.Syntax.C_reg_82
                                (coe MAlonzo.Code.Once.Backend.AArch64.Syntax.C_x0_10)))
                          (coe
                             MAlonzo.Code.Data.List.Base.du__'43''43'__32
                             (coe d_compile'45'aarch64_32 (coe v0) (coe v8) (coe v6))
                             (coe
                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                (coe
                                   MAlonzo.Code.Once.Backend.AArch64.Syntax.C_str_94
                                   (coe MAlonzo.Code.Once.Backend.AArch64.Syntax.C_x0_10)
                                   (coe
                                      MAlonzo.Code.Once.Backend.AArch64.Syntax.C_base_74
                                      (coe MAlonzo.Code.Once.Backend.AArch64.Syntax.C_x21_52)))
                                (coe
                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                   (coe
                                      MAlonzo.Code.Once.Backend.AArch64.Syntax.C_mov_90
                                      (coe MAlonzo.Code.Once.Backend.AArch64.Syntax.C_x0_10)
                                      (coe
                                         MAlonzo.Code.Once.Backend.AArch64.Syntax.C_reg_82
                                         (coe MAlonzo.Code.Once.Backend.AArch64.Syntax.C_x20_50)))
                                   (coe
                                      MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                      (coe d_compile'45'aarch64_32 (coe v0) (coe v9) (coe v7))
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                         (coe
                                            MAlonzo.Code.Once.Backend.AArch64.Syntax.C_str_94
                                            (coe MAlonzo.Code.Once.Backend.AArch64.Syntax.C_x0_10)
                                            (coe
                                               MAlonzo.Code.Once.Backend.AArch64.Syntax.C_base'43'imm_76
                                               (coe
                                                  MAlonzo.Code.Once.Backend.AArch64.Syntax.C_x21_52)
                                               (coe (8 :: Integer))))
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                            (coe
                                               MAlonzo.Code.Once.Backend.AArch64.Syntax.C_mov_90
                                               (coe
                                                  MAlonzo.Code.Once.Backend.AArch64.Syntax.C_x0_10)
                                               (coe
                                                  MAlonzo.Code.Once.Backend.AArch64.Syntax.C_reg_82
                                                  (coe
                                                     MAlonzo.Code.Once.Backend.AArch64.Syntax.C_x21_52)))
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_inl_42
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.Backend.AArch64.Syntax.C_sub'45'sp_118
                (coe (16 :: Integer)))
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe
                   MAlonzo.Code.Once.Backend.AArch64.Syntax.C_str'45'zr_130
                   (coe
                      MAlonzo.Code.Once.Backend.AArch64.Syntax.C_sp'43'imm_78
                      (coe (0 :: Integer))))
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                   (coe
                      MAlonzo.Code.Once.Backend.AArch64.Syntax.C_str_94
                      (coe MAlonzo.Code.Once.Backend.AArch64.Syntax.C_x0_10)
                      (coe
                         MAlonzo.Code.Once.Backend.AArch64.Syntax.C_sp'43'imm_78
                         (coe (8 :: Integer))))
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                      (coe
                         MAlonzo.Code.Once.Backend.AArch64.Syntax.C_mov'45'from'45'sp_122
                         (coe MAlonzo.Code.Once.Backend.AArch64.Syntax.C_x0_10))
                      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
      MAlonzo.Code.Once.IR.C_inr_48
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.Backend.AArch64.Syntax.C_sub'45'sp_118
                (coe (16 :: Integer)))
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe
                   MAlonzo.Code.Once.Backend.AArch64.Syntax.C_mov_90
                   (coe MAlonzo.Code.Once.Backend.AArch64.Syntax.C_x9_28)
                   (coe
                      MAlonzo.Code.Once.Backend.AArch64.Syntax.C_imm_86
                      (coe (1 :: Integer))))
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                   (coe
                      MAlonzo.Code.Once.Backend.AArch64.Syntax.C_str_94
                      (coe MAlonzo.Code.Once.Backend.AArch64.Syntax.C_x9_28)
                      (coe
                         MAlonzo.Code.Once.Backend.AArch64.Syntax.C_sp'43'imm_78
                         (coe (0 :: Integer))))
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                      (coe
                         MAlonzo.Code.Once.Backend.AArch64.Syntax.C_str_94
                         (coe MAlonzo.Code.Once.Backend.AArch64.Syntax.C_x0_10)
                         (coe
                            MAlonzo.Code.Once.Backend.AArch64.Syntax.C_sp'43'imm_78
                            (coe (8 :: Integer))))
                      (coe
                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                         (coe
                            MAlonzo.Code.Once.Backend.AArch64.Syntax.C_mov'45'from'45'sp_122
                            (coe MAlonzo.Code.Once.Backend.AArch64.Syntax.C_x0_10))
                         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))
      MAlonzo.Code.Once.IR.C_'91'_'44'_'93'_56 v6 v7
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'43'__12 v8 v9
               -> coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                    (coe
                       MAlonzo.Code.Once.Backend.AArch64.Syntax.C_ldr_92
                       (coe MAlonzo.Code.Once.Backend.AArch64.Syntax.C_x9_28)
                       (coe
                          MAlonzo.Code.Once.Backend.AArch64.Syntax.C_base_74
                          (coe MAlonzo.Code.Once.Backend.AArch64.Syntax.C_x0_10)))
                    (coe
                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                       (coe
                          MAlonzo.Code.Once.Backend.AArch64.Syntax.C_cmp_104
                          (coe MAlonzo.Code.Once.Backend.AArch64.Syntax.C_x9_28)
                          (coe
                             MAlonzo.Code.Once.Backend.AArch64.Syntax.C_imm_86
                             (coe (0 :: Integer))))
                       (coe
                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                          (coe
                             MAlonzo.Code.Once.Backend.AArch64.Syntax.C_b'45'ne_110
                             (coe
                                addInt (coe (5 :: Integer))
                                (coe d_compile'45'length_12 (coe v8) (coe v1) (coe v6))))
                          (coe
                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                             (coe
                                MAlonzo.Code.Once.Backend.AArch64.Syntax.C_ldr_92
                                (coe MAlonzo.Code.Once.Backend.AArch64.Syntax.C_x0_10)
                                (coe
                                   MAlonzo.Code.Once.Backend.AArch64.Syntax.C_base'43'imm_76
                                   (coe MAlonzo.Code.Once.Backend.AArch64.Syntax.C_x0_10)
                                   (coe (8 :: Integer))))
                             (coe
                                MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                (coe d_compile'45'aarch64_32 (coe v8) (coe v1) (coe v6))
                                (coe
                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                   (coe
                                      MAlonzo.Code.Once.Backend.AArch64.Syntax.C_b_106
                                      (coe
                                         addInt
                                         (coe
                                            addInt (coe (7 :: Integer))
                                            (coe d_compile'45'length_12 (coe v8) (coe v1) (coe v6)))
                                         (coe d_compile'45'length_12 (coe v9) (coe v1) (coe v7))))
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                      (coe
                                         MAlonzo.Code.Once.Backend.AArch64.Syntax.C_label_132
                                         (coe
                                            addInt (coe (5 :: Integer))
                                            (coe
                                               d_compile'45'length_12 (coe v8) (coe v1) (coe v6))))
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                         (coe
                                            MAlonzo.Code.Once.Backend.AArch64.Syntax.C_ldr_92
                                            (coe MAlonzo.Code.Once.Backend.AArch64.Syntax.C_x0_10)
                                            (coe
                                               MAlonzo.Code.Once.Backend.AArch64.Syntax.C_base'43'imm_76
                                               (coe
                                                  MAlonzo.Code.Once.Backend.AArch64.Syntax.C_x0_10)
                                               (coe (8 :: Integer))))
                                         (coe
                                            MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                            (coe d_compile'45'aarch64_32 (coe v9) (coe v1) (coe v7))
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                               (coe
                                                  MAlonzo.Code.Once.Backend.AArch64.Syntax.C_label_132
                                                  (coe
                                                     addInt
                                                     (coe
                                                        addInt (coe (7 :: Integer))
                                                        (coe
                                                           d_compile'45'length_12 (coe v8) (coe v1)
                                                           (coe v6)))
                                                     (coe
                                                        d_compile'45'length_12 (coe v9) (coe v1)
                                                        (coe v7))))
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))))))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_terminal_60
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.Backend.AArch64.Syntax.C_mov_90
                (coe MAlonzo.Code.Once.Backend.AArch64.Syntax.C_x0_10)
                (coe
                   MAlonzo.Code.Once.Backend.AArch64.Syntax.C_imm_86
                   (coe (0 :: Integer))))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.IR.C_initial_64
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.Backend.AArch64.Syntax.C_brk_126
                (coe (0 :: Integer)))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.IR.C_curry_72 v6
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'8658'__14 v7 v8
               -> coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                    (coe
                       MAlonzo.Code.Once.Backend.AArch64.Syntax.C_sub'45'sp_118
                       (coe (16 :: Integer)))
                    (coe
                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                       (coe
                          MAlonzo.Code.Once.Backend.AArch64.Syntax.C_str_94
                          (coe MAlonzo.Code.Once.Backend.AArch64.Syntax.C_x0_10)
                          (coe
                             MAlonzo.Code.Once.Backend.AArch64.Syntax.C_sp'43'imm_78
                             (coe (0 :: Integer))))
                       (coe
                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                          (coe
                             MAlonzo.Code.Once.Backend.AArch64.Syntax.C_adr_128
                             (coe MAlonzo.Code.Once.Backend.AArch64.Syntax.C_x9_28)
                             (coe (4 :: Integer)))
                          (coe
                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                             (coe
                                MAlonzo.Code.Once.Backend.AArch64.Syntax.C_str_94
                                (coe MAlonzo.Code.Once.Backend.AArch64.Syntax.C_x9_28)
                                (coe
                                   MAlonzo.Code.Once.Backend.AArch64.Syntax.C_sp'43'imm_78
                                   (coe (8 :: Integer))))
                             (coe
                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                (coe
                                   MAlonzo.Code.Once.Backend.AArch64.Syntax.C_mov'45'from'45'sp_122
                                   (coe MAlonzo.Code.Once.Backend.AArch64.Syntax.C_x0_10))
                                (coe
                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                   (coe
                                      MAlonzo.Code.Once.Backend.AArch64.Syntax.C_b_106
                                      (coe
                                         addInt (coe (11 :: Integer))
                                         (coe
                                            d_compile'45'length_12
                                            (coe
                                               MAlonzo.Code.Once.Type.C__'42'__10 (coe v0) (coe v7))
                                            (coe v8) (coe v6))))
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                      (coe
                                         MAlonzo.Code.Once.Backend.AArch64.Syntax.C_label_132
                                         (coe (6 :: Integer)))
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                         (coe
                                            MAlonzo.Code.Once.Backend.AArch64.Syntax.C_sub'45'sp_118
                                            (coe (16 :: Integer)))
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                            (coe
                                               MAlonzo.Code.Once.Backend.AArch64.Syntax.C_stp_98
                                               (coe
                                                  MAlonzo.Code.Once.Backend.AArch64.Syntax.C_x19_48)
                                               (coe
                                                  MAlonzo.Code.Once.Backend.AArch64.Syntax.C_x0_10)
                                               (coe
                                                  MAlonzo.Code.Once.Backend.AArch64.Syntax.C_sp'43'imm_78
                                                  (coe (0 :: Integer))))
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                               (coe
                                                  MAlonzo.Code.Once.Backend.AArch64.Syntax.C_mov'45'from'45'sp_122
                                                  (coe
                                                     MAlonzo.Code.Once.Backend.AArch64.Syntax.C_x0_10))
                                               (coe
                                                  MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                                  (coe
                                                     d_compile'45'aarch64_32
                                                     (coe
                                                        MAlonzo.Code.Once.Type.C__'42'__10 (coe v0)
                                                        (coe v7))
                                                     (coe v8) (coe v6))
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                     (coe
                                                        MAlonzo.Code.Once.Backend.AArch64.Syntax.C_ret_116)
                                                     (coe
                                                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                        (coe
                                                           MAlonzo.Code.Once.Backend.AArch64.Syntax.C_label_132
                                                           (coe
                                                              addInt (coe (11 :: Integer))
                                                              (coe
                                                                 d_compile'45'length_12
                                                                 (coe
                                                                    MAlonzo.Code.Once.Type.C__'42'__10
                                                                    (coe v0) (coe v7))
                                                                 (coe v8) (coe v6))))
                                                        (coe
                                                           MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_apply_78
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.Backend.AArch64.Syntax.C_ldr_92
                (coe MAlonzo.Code.Once.Backend.AArch64.Syntax.C_x9_28)
                (coe
                   MAlonzo.Code.Once.Backend.AArch64.Syntax.C_base_74
                   (coe MAlonzo.Code.Once.Backend.AArch64.Syntax.C_x0_10)))
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe
                   MAlonzo.Code.Once.Backend.AArch64.Syntax.C_ldr_92
                   (coe MAlonzo.Code.Once.Backend.AArch64.Syntax.C_x10_30)
                   (coe
                      MAlonzo.Code.Once.Backend.AArch64.Syntax.C_base'43'imm_76
                      (coe MAlonzo.Code.Once.Backend.AArch64.Syntax.C_x0_10)
                      (coe (8 :: Integer))))
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                   (coe
                      MAlonzo.Code.Once.Backend.AArch64.Syntax.C_ldr_92
                      (coe MAlonzo.Code.Once.Backend.AArch64.Syntax.C_x19_48)
                      (coe
                         MAlonzo.Code.Once.Backend.AArch64.Syntax.C_base_74
                         (coe MAlonzo.Code.Once.Backend.AArch64.Syntax.C_x9_28)))
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                      (coe
                         MAlonzo.Code.Once.Backend.AArch64.Syntax.C_ldr_92
                         (coe MAlonzo.Code.Once.Backend.AArch64.Syntax.C_x9_28)
                         (coe
                            MAlonzo.Code.Once.Backend.AArch64.Syntax.C_base'43'imm_76
                            (coe MAlonzo.Code.Once.Backend.AArch64.Syntax.C_x9_28)
                            (coe (8 :: Integer))))
                      (coe
                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                         (coe
                            MAlonzo.Code.Once.Backend.AArch64.Syntax.C_mov_90
                            (coe MAlonzo.Code.Once.Backend.AArch64.Syntax.C_x0_10)
                            (coe
                               MAlonzo.Code.Once.Backend.AArch64.Syntax.C_reg_82
                               (coe MAlonzo.Code.Once.Backend.AArch64.Syntax.C_x10_30)))
                         (coe
                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                            (coe
                               MAlonzo.Code.Once.Backend.AArch64.Syntax.C_blr_114
                               (coe MAlonzo.Code.Once.Backend.AArch64.Syntax.C_x9_28))
                            (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))))
      MAlonzo.Code.Once.IR.C_fold_82
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe MAlonzo.Code.Once.Backend.AArch64.Syntax.C_nop_124)
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.IR.C_unfold_86
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe MAlonzo.Code.Once.Backend.AArch64.Syntax.C_nop_124)
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.IR.C_arr_92
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe MAlonzo.Code.Once.Backend.AArch64.Syntax.C_nop_124)
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      _ -> MAlonzo.RTE.mazUnreachableError
