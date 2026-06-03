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

module MAlonzo.Code.Once.CCC.Target.X86Z45Z64.CodeGen.Compile where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Once.CCC.IR
import qualified MAlonzo.Code.Once.CCC.SigOp.Info
import qualified MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax
import qualified MAlonzo.Code.Once.Target.Symbol
import qualified MAlonzo.Code.Once.Type

-- Once.CCC.Target.X86-64.CodeGen.Compile.id-instrs
d_id'45'instrs_12 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_62]
d_id'45'instrs_12
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mov_64
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_56
            (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rax_12))
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_56
            (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rdi_22)))
      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
-- Once.CCC.Target.X86-64.CodeGen.Compile.fst-instrs
d_fst'45'instrs_14 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_62]
d_fst'45'instrs_14
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mov_64
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_56
            (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rax_12))
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mem_58
            (coe
               MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_base_46
               (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rdi_22))))
      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
-- Once.CCC.Target.X86-64.CodeGen.Compile.snd-instrs
d_snd'45'instrs_16 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_62]
d_snd'45'instrs_16
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mov_64
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_56
            (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rax_12))
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mem_58
            (coe
               MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_base'43'disp_48
               (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rdi_22)
               (coe
                  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.d_slot'45'size_114))))
      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
-- Once.CCC.Target.X86-64.CodeGen.Compile.terminal-instrs
d_terminal'45'instrs_18 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_62]
d_terminal'45'instrs_18
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mov_64
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_56
            (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rax_12))
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_imm_60
            (coe (0 :: Integer))))
      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
-- Once.CCC.Target.X86-64.CodeGen.Compile.compose-bridge
d_compose'45'bridge_20 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_62]
d_compose'45'bridge_20
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mov_64
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_56
            (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rdi_22))
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_56
            (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rax_12)))
      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
-- Once.CCC.Target.X86-64.CodeGen.Compile.inl-instrs
d_inl'45'instrs_22 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_62]
d_inl'45'instrs_22
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mov_64
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_56
            (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rax_12))
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_56
            (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_r14_40)))
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mov_64
            (coe
               MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mem_58
               (coe
                  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_base_46
                  (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_r14_40)))
            (coe
               MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_imm_60
               (coe (0 :: Integer))))
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe
               MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mov_64
               (coe
                  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mem_58
                  (coe
                     MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_base'43'disp_48
                     (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_r14_40)
                     (coe
                        MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.d_slot'45'size_114)))
               (coe
                  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_56
                  (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rdi_22)))
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe
                  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_add_68
                  (coe
                     MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_56
                     (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_r14_40))
                  (coe
                     MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_imm_60
                     (coe
                        MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.d_slots_116
                        (coe (2 :: Integer)))))
               (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
-- Once.CCC.Target.X86-64.CodeGen.Compile.inr-instrs
d_inr'45'instrs_24 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_62]
d_inr'45'instrs_24
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mov_64
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_56
            (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rax_12))
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_56
            (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_r14_40)))
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mov_64
            (coe
               MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mem_58
               (coe
                  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_base_46
                  (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_r14_40)))
            (coe
               MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_imm_60
               (coe (1 :: Integer))))
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe
               MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mov_64
               (coe
                  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mem_58
                  (coe
                     MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_base'43'disp_48
                     (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_r14_40)
                     (coe
                        MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.d_slot'45'size_114)))
               (coe
                  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_56
                  (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rdi_22)))
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe
                  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_add_68
                  (coe
                     MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_56
                     (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_r14_40))
                  (coe
                     MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_imm_60
                     (coe
                        MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.d_slots_116
                        (coe (2 :: Integer)))))
               (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
-- Once.CCC.Target.X86-64.CodeGen.Compile.cata-loop-prefix
d_cata'45'loop'45'prefix_34 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_62]
d_cata'45'loop'45'prefix_34 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mov_64
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_56
            (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rbx_14))
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_imm_60
            (coe (0 :: Integer))))
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_label_98 (coe v0))
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe
               MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mov_64
               (coe
                  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_56
                  (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rcx_16))
               (coe
                  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mem_58
                  (coe
                     MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_base_46
                     (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rdi_22))))
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe
                  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_cmp_72
                  (coe
                     MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_56
                     (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rcx_16))
                  (coe
                     MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_imm_60
                     (coe (0 :: Integer))))
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe
                     MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_je_78 (coe v1))
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_add_68
                        (coe
                           MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_56
                           (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rbx_14))
                        (coe
                           MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_imm_60
                           (coe (1 :: Integer))))
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mov_64
                           (coe
                              MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_56
                              (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rdi_22))
                           (coe
                              MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mem_58
                              (coe
                                 MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_base'43'disp_48
                                 (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rdi_22)
                                 (coe
                                    MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.d_slot'45'size_114))))
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_jmp_76 (coe v0))
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_label_98 (coe v1))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mov_64
                                    (coe
                                       MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_56
                                       (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rdi_22))
                                    (coe
                                       MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_56
                                       (coe
                                          MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_r14_40)))
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mov_64
                                       (coe
                                          MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mem_58
                                          (coe
                                             MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_base_46
                                             (coe
                                                MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_r14_40)))
                                       (coe
                                          MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_imm_60
                                          (coe (0 :: Integer))))
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mov_64
                                          (coe
                                             MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mem_58
                                             (coe
                                                MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_base'43'disp_48
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_r14_40)
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.d_slot'45'size_114)))
                                          (coe
                                             MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_imm_60
                                             (coe (0 :: Integer))))
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                          (coe
                                             MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_add_68
                                             (coe
                                                MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_56
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_r14_40))
                                             (coe
                                                MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_imm_60
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.d_slots_116
                                                   (coe (2 :: Integer)))))
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                             (coe
                                                MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_jmp_76
                                                (coe v2))
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_label_98
                                                   (coe v3))
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                   (coe
                                                      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mov_64
                                                      (coe
                                                         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_56
                                                         (coe
                                                            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rdi_22))
                                                      (coe
                                                         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_56
                                                         (coe
                                                            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_r14_40)))
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                      (coe
                                                         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mov_64
                                                         (coe
                                                            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mem_58
                                                            (coe
                                                               MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_base_46
                                                               (coe
                                                                  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_r14_40)))
                                                         (coe
                                                            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_imm_60
                                                            (coe (1 :: Integer))))
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                         (coe
                                                            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mov_64
                                                            (coe
                                                               MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mem_58
                                                               (coe
                                                                  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_base'43'disp_48
                                                                  (coe
                                                                     MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_r14_40)
                                                                  (coe
                                                                     MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.d_slot'45'size_114)))
                                                            (coe
                                                               MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_56
                                                               (coe
                                                                  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rax_12)))
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                            (coe
                                                               MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_add_68
                                                               (coe
                                                                  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_56
                                                                  (coe
                                                                     MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_r14_40))
                                                               (coe
                                                                  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_imm_60
                                                                  (coe
                                                                     MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.d_slots_116
                                                                     (coe (2 :: Integer)))))
                                                            (coe
                                                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                               (coe
                                                                  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_label_98
                                                                  (coe v2))
                                                               (coe
                                                                  MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))))))))))))))))))
-- Once.CCC.Target.X86-64.CodeGen.Compile.cata-loop-suffix
d_cata'45'loop'45'suffix_48 ::
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_62]
d_cata'45'loop'45'suffix_48 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_cmp_72
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_56
            (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rbx_14))
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_imm_60
            (coe (0 :: Integer))))
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_je_78 (coe v1))
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe
               MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_sub_70
               (coe
                  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_56
                  (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rbx_14))
               (coe
                  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_imm_60
                  (coe (1 :: Integer))))
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe
                  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_jmp_76 (coe v0))
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe
                     MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_label_98 (coe v1))
                  (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))
-- Once.CCC.Target.X86-64.CodeGen.Compile.pair-setup
d_pair'45'setup_54 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_62]
d_pair'45'setup_54
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_sub_70
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_56
            (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rsp_26))
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_imm_60
            (coe
               MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.d_slots_116
               (coe (3 :: Integer)))))
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mov_64
            (coe
               MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mem_58
               (coe
                  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_base'43'disp_48
                  (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rsp_26)
                  (coe
                     MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.d_slots_116
                     (coe (2 :: Integer)))))
            (coe
               MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_56
               (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rdi_22)))
         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
-- Once.CCC.Target.X86-64.CodeGen.Compile.pair-middle
d_pair'45'middle_56 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_62]
d_pair'45'middle_56
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mov_64
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mem_58
            (coe
               MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_base_46
               (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rsp_26)))
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_56
            (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rax_12)))
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mov_64
            (coe
               MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_56
               (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rdi_22))
            (coe
               MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mem_58
               (coe
                  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_base'43'disp_48
                  (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rsp_26)
                  (coe
                     MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.d_slots_116
                     (coe (2 :: Integer))))))
         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
-- Once.CCC.Target.X86-64.CodeGen.Compile.pair-cleanup
d_pair'45'cleanup_58 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_62]
d_pair'45'cleanup_58
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mov_64
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mem_58
            (coe
               MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_base'43'disp_48
               (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rsp_26)
               (coe
                  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.d_slot'45'size_114)))
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_56
            (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rax_12)))
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mov_64
            (coe
               MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_56
               (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rax_12))
            (coe
               MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_56
               (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rsp_26)))
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe
               MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_add_68
               (coe
                  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_56
                  (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rsp_26))
               (coe
                  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_imm_60
                  (coe
                     MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.d_slots_116
                     (coe (3 :: Integer)))))
            (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
-- Once.CCC.Target.X86-64.CodeGen.Compile.curry-closure-setup
d_curry'45'closure'45'setup_60 ::
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_62]
d_curry'45'closure'45'setup_60 v0 ~v1
  = du_curry'45'closure'45'setup_60 v0
du_curry'45'closure'45'setup_60 ::
  Integer ->
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_62]
du_curry'45'closure'45'setup_60 v0
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_sub_70
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_56
            (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rsp_26))
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_imm_60
            (coe
               MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.d_slots_116
               (coe (2 :: Integer)))))
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mov_64
            (coe
               MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mem_58
               (coe
                  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_base_46
                  (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rsp_26)))
            (coe
               MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_56
               (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rdi_22)))
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe
               MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_lea_66
               (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_r9_30)
               (coe
                  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rip'43'disp_50
                  (coe (4 :: Integer))))
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe
                  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mov_64
                  (coe
                     MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mem_58
                     (coe
                        MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_base'43'disp_48
                        (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rsp_26)
                        (coe
                           MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.d_slot'45'size_114)))
                  (coe
                     MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_56
                     (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_r9_30)))
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe
                     MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mov_64
                     (coe
                        MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_56
                        (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rax_12))
                     (coe
                        MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_56
                        (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rsp_26)))
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_jmp_76
                        (coe addInt (coe (1 :: Integer)) (coe v0)))
                     (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))))
-- Once.CCC.Target.X86-64.CodeGen.Compile.curry-thunk-setup'
d_curry'45'thunk'45'setup''_66 ::
  Integer ->
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_62]
d_curry'45'thunk'45'setup''_66 v0
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_label_98 (coe v0))
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_push_88
            (coe
               MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_56
               (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_r15_42)))
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe
               MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_sub_70
               (coe
                  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_56
                  (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rsp_26))
               (coe
                  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_imm_60
                  (coe
                     MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.d_slots_116
                     (coe (2 :: Integer)))))
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe
                  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mov_64
                  (coe
                     MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mem_58
                     (coe
                        MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_base_46
                        (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rsp_26)))
                  (coe
                     MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_56
                     (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_r12_36)))
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe
                     MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mov_64
                     (coe
                        MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mem_58
                        (coe
                           MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_base'43'disp_48
                           (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rsp_26)
                           (coe
                              MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.d_slot'45'size_114)))
                     (coe
                        MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_56
                        (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rdi_22)))
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mov_64
                        (coe
                           MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_56
                           (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rdi_22))
                        (coe
                           MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_56
                           (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rsp_26)))
                     (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))))
-- Once.CCC.Target.X86-64.CodeGen.Compile.curry-thunk-cleanup'
d_curry'45'thunk'45'cleanup''_70 ::
  Integer ->
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_62]
d_curry'45'thunk'45'cleanup''_70 v0
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_add_68
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_56
            (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rsp_26))
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_imm_60
            (coe
               MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.d_slots_116
               (coe (2 :: Integer)))))
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_pop_90
            (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_r15_42))
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_ret_86)
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe
                  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_label_98
                  (coe addInt (coe (1 :: Integer)) (coe v0)))
               (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
-- Once.CCC.Target.X86-64.CodeGen.Compile.curry-thunk-setup
d_curry'45'thunk'45'setup_74 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_62]
d_curry'45'thunk'45'setup_74
  = coe d_curry'45'thunk'45'setup''_66 (coe (0 :: Integer))
-- Once.CCC.Target.X86-64.CodeGen.Compile.curry-thunk-cleanup
d_curry'45'thunk'45'cleanup_76 ::
  Integer ->
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_62]
d_curry'45'thunk'45'cleanup_76 ~v0
  = du_curry'45'thunk'45'cleanup_76
du_curry'45'thunk'45'cleanup_76 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_62]
du_curry'45'thunk'45'cleanup_76
  = coe d_curry'45'thunk'45'cleanup''_70 (coe (0 :: Integer))
-- Once.CCC.Target.X86-64.CodeGen.Compile.apply-instrs
d_apply'45'instrs_78 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_62]
d_apply'45'instrs_78
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_push_88
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_56
            (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_r15_42)))
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mov_64
            (coe
               MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_56
               (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_r15_42))
            (coe
               MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mem_58
               (coe
                  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_base_46
                  (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rdi_22))))
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe
               MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mov_64
               (coe
                  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_56
                  (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rsi_20))
               (coe
                  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mem_58
                  (coe
                     MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_base'43'disp_48
                     (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rdi_22)
                     (coe
                        MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.d_slot'45'size_114))))
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe
                  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mov_64
                  (coe
                     MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_56
                     (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_r12_36))
                  (coe
                     MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mem_58
                     (coe
                        MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_base_46
                        (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_r15_42))))
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe
                     MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mov_64
                     (coe
                        MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_56
                        (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_r15_42))
                     (coe
                        MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mem_58
                        (coe
                           MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_base'43'disp_48
                           (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_r15_42)
                           (coe
                              MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.d_slot'45'size_114))))
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mov_64
                        (coe
                           MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_56
                           (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rdi_22))
                        (coe
                           MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_56
                           (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rsi_20)))
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_call_82
                           (coe
                              MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_56
                              (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_r15_42)))
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_pop_90
                              (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_r15_42))
                           (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))))))
-- Once.CCC.Target.X86-64.CodeGen.Compile.compile-sigOp
d_compile'45'sigOp_80 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_62]
d_compile'45'sigOp_80 v0
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_call'45'sym_84
         (coe MAlonzo.Code.Once.Target.Symbol.d_once'45'symbol_8 (coe v0)))
      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
-- Once.CCC.Target.X86-64.CodeGen.Compile.compile-sigOp-size
d_compile'45'sigOp'45'size_84 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Integer
d_compile'45'sigOp'45'size_84 ~v0 = du_compile'45'sigOp'45'size_84
du_compile'45'sigOp'45'size_84 :: Integer
du_compile'45'sigOp'45'size_84 = coe (1 :: Integer)
-- Once.CCC.Target.X86-64.CodeGen.Compile.compile-sigOp-length
d_compile'45'sigOp'45'length_88 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_compile'45'sigOp'45'length_88 = erased
-- Once.CCC.Target.X86-64.CodeGen.Compile.compile-const
d_compile'45'const_92 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_188 ->
  AgdaAny ->
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_62]
d_compile'45'const_92 ~v0 v1 v2 = du_compile'45'const_92 v1 v2
du_compile'45'const_92 ::
  MAlonzo.Code.Once.Type.T_FitsInReg_188 ->
  AgdaAny ->
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_62]
du_compile'45'const_92 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Type.C_fits'45'int_190
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mov_64
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_56
                   (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rax_12))
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_imm_60 (coe v1)))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.Type.C_fits'45'float_192
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_ud2_94)
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-64.CodeGen.Compile.compile-const-size
d_compile'45'const'45'size_98 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_188 -> Integer
d_compile'45'const'45'size_98 ~v0 v1
  = du_compile'45'const'45'size_98 v1
du_compile'45'const'45'size_98 ::
  MAlonzo.Code.Once.Type.T_FitsInReg_188 -> Integer
du_compile'45'const'45'size_98 v0
  = coe seq (coe v0) (coe (1 :: Integer))
-- Once.CCC.Target.X86-64.CodeGen.Compile.compile-const-length
d_compile'45'const'45'length_106 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_188 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_compile'45'const'45'length_106 = erased
-- Once.CCC.Target.X86-64.CodeGen.Compile.case-dispatch
d_case'45'dispatch_108 ::
  Integer ->
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_62]
d_case'45'dispatch_108 v0
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mov_64
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_56
            (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rcx_16))
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mem_58
            (coe
               MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_base_46
               (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rdi_22))))
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mov_64
            (coe
               MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_56
               (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rdi_22))
            (coe
               MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mem_58
               (coe
                  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_base'43'disp_48
                  (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rdi_22)
                  (coe
                     MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.d_slot'45'size_114))))
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe
               MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_cmp_72
               (coe
                  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_56
                  (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rcx_16))
               (coe
                  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_imm_60
                  (coe (0 :: Integer))))
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe
                  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_jne_80 (coe v0))
               (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
-- Once.CCC.Target.X86-64.CodeGen.Compile.case-middle
d_case'45'middle_112 ::
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_62]
d_case'45'middle_112 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_jmp_76 (coe v0))
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_label_98 (coe v1))
         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
-- Once.CCC.Target.X86-64.CodeGen.Compile.case-suffix
d_case'45'suffix_118 ::
  Integer ->
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_62]
d_case'45'suffix_118 v0
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_label_98 (coe v0))
      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
-- Once.CCC.Target.X86-64.CodeGen.Compile.compile-length
d_compile'45'length_126 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274 -> Integer
d_compile'45'length_126 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.CCC.IR.C_id_278
        -> coe MAlonzo.Code.Data.List.Base.du_length_268 d_id'45'instrs_12
      MAlonzo.Code.Once.CCC.IR.C__'8728'__286 v4 v6 v7
        -> coe
             addInt
             (coe
                addInt
                (coe
                   MAlonzo.Code.Data.List.Base.du_length_268 d_compose'45'bridge_20)
                (coe d_compile'45'length_126 (coe v0) (coe v4) (coe v7)))
             (coe d_compile'45'length_126 (coe v4) (coe v1) (coe v6))
      MAlonzo.Code.Once.CCC.IR.C_'10216'_'44'_'10217'_294 v6 v7 v8
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'42'__122 v9 v10
               -> coe
                    addInt
                    (coe
                       addInt
                       (coe
                          addInt
                          (coe
                             addInt
                             (coe
                                MAlonzo.Code.Data.List.Base.du_length_268 d_pair'45'cleanup_58)
                             (coe
                                MAlonzo.Code.Data.List.Base.du_length_268 d_pair'45'middle_56))
                          (coe MAlonzo.Code.Data.List.Base.du_length_268 d_pair'45'setup_54))
                       (coe d_compile'45'length_126 (coe v0) (coe v9) (coe v6)))
                    (coe d_compile'45'length_126 (coe v0) (coe v10) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_fst_300
        -> coe MAlonzo.Code.Data.List.Base.du_length_268 d_fst'45'instrs_14
      MAlonzo.Code.Once.CCC.IR.C_snd_306
        -> coe MAlonzo.Code.Data.List.Base.du_length_268 d_snd'45'instrs_16
      MAlonzo.Code.Once.CCC.IR.C_inl_312 v5
        -> coe MAlonzo.Code.Data.List.Base.du_length_268 d_inl'45'instrs_22
      MAlonzo.Code.Once.CCC.IR.C_inr_318 v5
        -> coe MAlonzo.Code.Data.List.Base.du_length_268 d_inr'45'instrs_24
      MAlonzo.Code.Once.CCC.IR.C_case_326 v6 v7
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'43'__124 v8 v9
               -> coe
                    addInt
                    (coe
                       addInt
                       (coe
                          addInt
                          (coe
                             addInt
                             (coe
                                MAlonzo.Code.Data.List.Base.du_length_268
                                (d_case'45'suffix_118 (coe (0 :: Integer))))
                             (coe
                                MAlonzo.Code.Data.List.Base.du_length_268
                                (d_case'45'middle_112 (coe (0 :: Integer)) (coe (0 :: Integer)))))
                          (coe
                             MAlonzo.Code.Data.List.Base.du_length_268
                             (d_case'45'dispatch_108 (coe (0 :: Integer)))))
                       (coe d_compile'45'length_126 (coe v8) (coe v1) (coe v6)))
                    (coe d_compile'45'length_126 (coe v9) (coe v1) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_terminal_330
        -> coe
             MAlonzo.Code.Data.List.Base.du_length_268 d_terminal'45'instrs_18
      MAlonzo.Code.Once.CCC.IR.C_initial_334 -> coe (1 :: Integer)
      MAlonzo.Code.Once.CCC.IR.C_curry_344 v7 v8
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v9 v10 v11
               -> coe
                    addInt
                    (coe
                       addInt
                       (coe
                          addInt
                          (coe
                             MAlonzo.Code.Data.List.Base.du_length_268
                             (d_curry'45'thunk'45'cleanup''_70 (coe (0 :: Integer))))
                          (coe
                             MAlonzo.Code.Data.List.Base.du_length_268
                             (coe du_curry'45'closure'45'setup_60 (coe (0 :: Integer)))))
                       (coe
                          MAlonzo.Code.Data.List.Base.du_length_268
                          d_curry'45'thunk'45'setup_74))
                    (coe
                       d_compile'45'length_126
                       (coe MAlonzo.Code.Once.Type.C__'42'__122 (coe v0) (coe v9))
                       (coe v11) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_apply_352
        -> coe
             MAlonzo.Code.Data.List.Base.du_length_268 d_apply'45'instrs_78
      MAlonzo.Code.Once.CCC.IR.C_arr_360
        -> coe MAlonzo.Code.Data.List.Base.du_length_268 d_id'45'instrs_12
      MAlonzo.Code.Once.CCC.IR.C_In_364 v4 v5 -> coe (1 :: Integer)
      MAlonzo.Code.Once.CCC.IR.C_out'45'μ_368 v4 -> coe (1 :: Integer)
      MAlonzo.Code.Once.CCC.IR.C_Cata_374 v4 v6
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C_μ'45'type_128 v7
               -> coe
                    addInt
                    (coe
                       addInt
                       (coe
                          MAlonzo.Code.Data.List.Base.du_length_268
                          (d_cata'45'loop'45'suffix_48
                             (coe (0 :: Integer)) (coe (0 :: Integer))))
                       (coe
                          MAlonzo.Code.Data.List.Base.du_length_268
                          (d_cata'45'loop'45'prefix_34
                             (coe (0 :: Integer)) (coe (0 :: Integer)) (coe (0 :: Integer))
                             (coe (0 :: Integer)))))
                    (coe
                       d_compile'45'length_126
                       (coe
                          MAlonzo.Code.Once.Type.d_'10214'_'10215'T_158 (coe v7) (coe v1))
                       (coe v1) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_Para_380 v4 v6 -> coe (1 :: Integer)
      MAlonzo.Code.Once.CCC.IR.C_Out_384 v4 -> coe (1 :: Integer)
      MAlonzo.Code.Once.CCC.IR.C_in'45'ν_388 v4 v5 -> coe (1 :: Integer)
      MAlonzo.Code.Once.CCC.IR.C_Ana_394 v4 v6 -> coe (1 :: Integer)
      MAlonzo.Code.Once.CCC.IR.C_Hylo_402 v3 v5 v6 v8 v9
        -> coe (1 :: Integer)
      MAlonzo.Code.Once.CCC.IR.C_Fuse_410 v3 v5 v6 v8 v9
        -> coe (1 :: Integer)
      MAlonzo.Code.Once.CCC.IR.C_free'45'heap_412 v3
        -> coe (0 :: Integer)
      MAlonzo.Code.Once.CCC.IR.C_const_416 v4 v5 v6
        -> coe du_compile'45'const'45'size_98 (coe v4)
      MAlonzo.Code.Once.CCC.IR.C_SigOp_422 v5
        -> coe du_compile'45'sigOp'45'size_84
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-64.CodeGen.Compile.compile-ir'
d_compile'45'ir''_152 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  Integer ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_compile'45'ir''_152 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Once.CCC.IR.C_id_278
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe d_id'45'instrs_12)
             (coe v2)
      MAlonzo.Code.Once.CCC.IR.C__'8728'__286 v5 v7 v8
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Data.List.Base.du__'43''43'__32
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                   (coe d_compile'45'ir''_152 (coe v0) (coe v5) (coe v2) (coe v8)))
                (coe
                   MAlonzo.Code.Data.List.Base.du__'43''43'__32
                   (coe d_compose'45'bridge_20)
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                      (coe
                         d_compile'45'ir''_152 (coe v5) (coe v1)
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                            (coe d_compile'45'ir''_152 (coe v0) (coe v5) (coe v2) (coe v8)))
                         (coe v7)))))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                (coe
                   d_compile'45'ir''_152 (coe v5) (coe v1)
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                      (coe d_compile'45'ir''_152 (coe v0) (coe v5) (coe v2) (coe v8)))
                   (coe v7)))
      MAlonzo.Code.Once.CCC.IR.C_'10216'_'44'_'10217'_294 v7 v8 v9
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'42'__122 v10 v11
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       MAlonzo.Code.Data.List.Base.du__'43''43'__32
                       (coe d_pair'45'setup_54)
                       (coe
                          MAlonzo.Code.Data.List.Base.du__'43''43'__32
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                             (coe d_compile'45'ir''_152 (coe v0) (coe v10) (coe v2) (coe v7)))
                          (coe
                             MAlonzo.Code.Data.List.Base.du__'43''43'__32
                             (coe d_pair'45'middle_56)
                             (coe
                                MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                   (coe
                                      d_compile'45'ir''_152 (coe v0) (coe v11)
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                         (coe
                                            d_compile'45'ir''_152 (coe v0) (coe v10) (coe v2)
                                            (coe v7)))
                                      (coe v8)))
                                (coe d_pair'45'cleanup_58)))))
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                       (coe
                          d_compile'45'ir''_152 (coe v0) (coe v11)
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                             (coe d_compile'45'ir''_152 (coe v0) (coe v10) (coe v2) (coe v7)))
                          (coe v8)))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_fst_300
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe d_fst'45'instrs_14) (coe v2)
      MAlonzo.Code.Once.CCC.IR.C_snd_306
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe d_snd'45'instrs_16) (coe v2)
      MAlonzo.Code.Once.CCC.IR.C_inl_312 v6
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe d_inl'45'instrs_22) (coe v2)
      MAlonzo.Code.Once.CCC.IR.C_inr_318 v6
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe d_inr'45'instrs_24) (coe v2)
      MAlonzo.Code.Once.CCC.IR.C_case_326 v7 v8
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'43'__124 v9 v10
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       MAlonzo.Code.Data.List.Base.du__'43''43'__32
                       (coe
                          d_case'45'dispatch_108
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                             (coe
                                d_compile'45'ir''_152 (coe v10) (coe v1)
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                   (coe d_compile'45'ir''_152 (coe v9) (coe v1) (coe v2) (coe v7)))
                                (coe v8))))
                       (coe
                          MAlonzo.Code.Data.List.Base.du__'43''43'__32
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                             (coe d_compile'45'ir''_152 (coe v9) (coe v1) (coe v2) (coe v7)))
                          (coe
                             MAlonzo.Code.Data.List.Base.du__'43''43'__32
                             (coe
                                d_case'45'middle_112
                                (coe
                                   addInt (coe (1 :: Integer))
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                      (coe
                                         d_compile'45'ir''_152 (coe v10) (coe v1)
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                            (coe
                                               d_compile'45'ir''_152 (coe v9) (coe v1) (coe v2)
                                               (coe v7)))
                                         (coe v8))))
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                   (coe
                                      d_compile'45'ir''_152 (coe v10) (coe v1)
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                         (coe
                                            d_compile'45'ir''_152 (coe v9) (coe v1) (coe v2)
                                            (coe v7)))
                                      (coe v8))))
                             (coe
                                MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                   (coe
                                      d_compile'45'ir''_152 (coe v10) (coe v1)
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                         (coe
                                            d_compile'45'ir''_152 (coe v9) (coe v1) (coe v2)
                                            (coe v7)))
                                      (coe v8)))
                                (coe
                                   d_case'45'suffix_118
                                   (coe
                                      addInt (coe (1 :: Integer))
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                         (coe
                                            d_compile'45'ir''_152 (coe v10) (coe v1)
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                               (coe
                                                  d_compile'45'ir''_152 (coe v9) (coe v1) (coe v2)
                                                  (coe v7)))
                                            (coe v8)))))))))
                    (coe
                       addInt (coe (2 :: Integer))
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                          (coe
                             d_compile'45'ir''_152 (coe v10) (coe v1)
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                (coe d_compile'45'ir''_152 (coe v9) (coe v1) (coe v2) (coe v7)))
                             (coe v8))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_terminal_330
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe d_terminal'45'instrs_18) (coe v2)
      MAlonzo.Code.Once.CCC.IR.C_initial_334
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_ud2_94)
                (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
             (coe v2)
      MAlonzo.Code.Once.CCC.IR.C_curry_344 v8 v9
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v10 v11 v12
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       MAlonzo.Code.Data.List.Base.du__'43''43'__32
                       (coe du_curry'45'closure'45'setup_60 (coe v2))
                       (coe
                          MAlonzo.Code.Data.List.Base.du__'43''43'__32
                          (coe d_curry'45'thunk'45'setup''_66 (coe v2))
                          (coe
                             MAlonzo.Code.Data.List.Base.du__'43''43'__32
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                (coe
                                   d_compile'45'ir''_152
                                   (coe MAlonzo.Code.Once.Type.C__'42'__122 (coe v0) (coe v10))
                                   (coe v12) (coe addInt (coe (2 :: Integer)) (coe v2)) (coe v8)))
                             (coe d_curry'45'thunk'45'cleanup''_70 (coe v2)))))
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                       (coe
                          d_compile'45'ir''_152
                          (coe MAlonzo.Code.Once.Type.C__'42'__122 (coe v0) (coe v10))
                          (coe v12) (coe addInt (coe (2 :: Integer)) (coe v2)) (coe v8)))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_apply_352
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe d_apply'45'instrs_78) (coe v2)
      MAlonzo.Code.Once.CCC.IR.C_arr_360
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe d_id'45'instrs_12)
             (coe v2)
      MAlonzo.Code.Once.CCC.IR.C_In_364 v5 v6
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe d_id'45'instrs_12)
             (coe v2)
      MAlonzo.Code.Once.CCC.IR.C_out'45'μ_368 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe d_id'45'instrs_12)
             (coe v2)
      MAlonzo.Code.Once.CCC.IR.C_Cata_374 v5 v7
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C_μ'45'type_128 v8
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       MAlonzo.Code.Data.List.Base.du__'43''43'__32
                       (coe
                          d_cata'45'loop'45'prefix_34
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                             (coe
                                d_compile'45'ir''_152
                                (coe
                                   MAlonzo.Code.Once.Type.d_'10214'_'10215'T_158 (coe v8) (coe v1))
                                (coe v1) (coe v2) (coe v7)))
                          (coe
                             addInt (coe (1 :: Integer))
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                (coe
                                   d_compile'45'ir''_152
                                   (coe
                                      MAlonzo.Code.Once.Type.d_'10214'_'10215'T_158 (coe v8)
                                      (coe v1))
                                   (coe v1) (coe v2) (coe v7))))
                          (coe
                             addInt (coe (2 :: Integer))
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                (coe
                                   d_compile'45'ir''_152
                                   (coe
                                      MAlonzo.Code.Once.Type.d_'10214'_'10215'T_158 (coe v8)
                                      (coe v1))
                                   (coe v1) (coe v2) (coe v7))))
                          (coe
                             addInt (coe (3 :: Integer))
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                (coe
                                   d_compile'45'ir''_152
                                   (coe
                                      MAlonzo.Code.Once.Type.d_'10214'_'10215'T_158 (coe v8)
                                      (coe v1))
                                   (coe v1) (coe v2) (coe v7)))))
                       (coe
                          MAlonzo.Code.Data.List.Base.du__'43''43'__32
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                             (coe
                                d_compile'45'ir''_152
                                (coe
                                   MAlonzo.Code.Once.Type.d_'10214'_'10215'T_158 (coe v8) (coe v1))
                                (coe v1) (coe v2) (coe v7)))
                          (coe
                             d_cata'45'loop'45'suffix_48
                             (coe
                                addInt (coe (3 :: Integer))
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                   (coe
                                      d_compile'45'ir''_152
                                      (coe
                                         MAlonzo.Code.Once.Type.d_'10214'_'10215'T_158 (coe v8)
                                         (coe v1))
                                      (coe v1) (coe v2) (coe v7))))
                             (coe
                                addInt (coe (4 :: Integer))
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                   (coe
                                      d_compile'45'ir''_152
                                      (coe
                                         MAlonzo.Code.Once.Type.d_'10214'_'10215'T_158 (coe v8)
                                         (coe v1))
                                      (coe v1) (coe v2) (coe v7)))))))
                    (coe
                       addInt (coe (5 :: Integer))
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                          (coe
                             d_compile'45'ir''_152
                             (coe
                                MAlonzo.Code.Once.Type.d_'10214'_'10215'T_158 (coe v8) (coe v1))
                             (coe v1) (coe v2) (coe v7))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_Para_380 v5 v7
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_ud2_94)
                (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
             (coe v2)
      MAlonzo.Code.Once.CCC.IR.C_Out_384 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe d_id'45'instrs_12)
             (coe v2)
      MAlonzo.Code.Once.CCC.IR.C_in'45'ν_388 v5 v6
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe d_id'45'instrs_12)
             (coe v2)
      MAlonzo.Code.Once.CCC.IR.C_Ana_394 v5 v7
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_ud2_94)
                (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
             (coe v2)
      MAlonzo.Code.Once.CCC.IR.C_Hylo_402 v4 v6 v7 v9 v10
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_ud2_94)
                (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
             (coe v2)
      MAlonzo.Code.Once.CCC.IR.C_Fuse_410 v4 v6 v7 v9 v10
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_ud2_94)
                (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
             (coe v2)
      MAlonzo.Code.Once.CCC.IR.C_free'45'heap_412 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16) (coe v2)
      MAlonzo.Code.Once.CCC.IR.C_const_416 v5 v6 v7
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe du_compile'45'const_92 (coe v5) (coe v7)) (coe v2)
      MAlonzo.Code.Once.CCC.IR.C_SigOp_422 v6
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                d_compile'45'sigOp_80
                (coe MAlonzo.Code.Once.CCC.SigOp.Info.d_name_290 (coe v6)))
             (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-64.CodeGen.Compile.compile-ir
d_compile'45'ir_278 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274 ->
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_62]
d_compile'45'ir_278 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe
         d_compile'45'ir''_152 (coe v0) (coe v1) (coe (0 :: Integer))
         (coe v2))
-- Once.CCC.Target.X86-64.CodeGen.Compile.compile-ir'-length
d_compile'45'ir'''45'length_290 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  Integer ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_compile'45'ir'''45'length_290 = erased
-- Once.CCC.Target.X86-64.CodeGen.Compile.compile-ir-length
d_compile'45'ir'45'length_544 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_compile'45'ir'45'length_544 = erased
