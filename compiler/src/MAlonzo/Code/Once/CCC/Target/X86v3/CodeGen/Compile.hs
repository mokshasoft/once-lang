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

module MAlonzo.Code.Once.CCC.Target.X86v3.CodeGen.Compile where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Once.CCC.IR
import qualified MAlonzo.Code.Once.Target.X86.Syntax
import qualified MAlonzo.Code.Once.Type

-- Once.CCC.Target.X86v3.CodeGen.Compile.id-instrs
d_id'45'instrs_12 ::
  [MAlonzo.Code.Once.Target.X86.Syntax.T_Instr_58]
d_id'45'instrs_12
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe
         MAlonzo.Code.Once.Target.X86.Syntax.C_mov_60
         (coe
            MAlonzo.Code.Once.Target.X86.Syntax.C_reg_52
            (coe MAlonzo.Code.Once.Target.X86.Syntax.C_rax_10))
         (coe
            MAlonzo.Code.Once.Target.X86.Syntax.C_reg_52
            (coe MAlonzo.Code.Once.Target.X86.Syntax.C_rdi_20)))
      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
-- Once.CCC.Target.X86v3.CodeGen.Compile.fst-instrs
d_fst'45'instrs_14 ::
  [MAlonzo.Code.Once.Target.X86.Syntax.T_Instr_58]
d_fst'45'instrs_14
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe
         MAlonzo.Code.Once.Target.X86.Syntax.C_mov_60
         (coe
            MAlonzo.Code.Once.Target.X86.Syntax.C_reg_52
            (coe MAlonzo.Code.Once.Target.X86.Syntax.C_rax_10))
         (coe
            MAlonzo.Code.Once.Target.X86.Syntax.C_mem_54
            (coe
               MAlonzo.Code.Once.Target.X86.Syntax.C_base_44
               (coe MAlonzo.Code.Once.Target.X86.Syntax.C_rdi_20))))
      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
-- Once.CCC.Target.X86v3.CodeGen.Compile.snd-instrs
d_snd'45'instrs_16 ::
  [MAlonzo.Code.Once.Target.X86.Syntax.T_Instr_58]
d_snd'45'instrs_16
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe
         MAlonzo.Code.Once.Target.X86.Syntax.C_mov_60
         (coe
            MAlonzo.Code.Once.Target.X86.Syntax.C_reg_52
            (coe MAlonzo.Code.Once.Target.X86.Syntax.C_rax_10))
         (coe
            MAlonzo.Code.Once.Target.X86.Syntax.C_mem_54
            (coe
               MAlonzo.Code.Once.Target.X86.Syntax.C_base'43'disp_46
               (coe MAlonzo.Code.Once.Target.X86.Syntax.C_rdi_20)
               (coe MAlonzo.Code.Once.Target.X86.Syntax.d_slot'45'size_106))))
      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
-- Once.CCC.Target.X86v3.CodeGen.Compile.terminal-instrs
d_terminal'45'instrs_18 ::
  [MAlonzo.Code.Once.Target.X86.Syntax.T_Instr_58]
d_terminal'45'instrs_18
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe
         MAlonzo.Code.Once.Target.X86.Syntax.C_mov_60
         (coe
            MAlonzo.Code.Once.Target.X86.Syntax.C_reg_52
            (coe MAlonzo.Code.Once.Target.X86.Syntax.C_rax_10))
         (coe
            MAlonzo.Code.Once.Target.X86.Syntax.C_imm_56 (coe (0 :: Integer))))
      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
-- Once.CCC.Target.X86v3.CodeGen.Compile.compose-bridge
d_compose'45'bridge_20 ::
  [MAlonzo.Code.Once.Target.X86.Syntax.T_Instr_58]
d_compose'45'bridge_20
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe
         MAlonzo.Code.Once.Target.X86.Syntax.C_mov_60
         (coe
            MAlonzo.Code.Once.Target.X86.Syntax.C_reg_52
            (coe MAlonzo.Code.Once.Target.X86.Syntax.C_rdi_20))
         (coe
            MAlonzo.Code.Once.Target.X86.Syntax.C_reg_52
            (coe MAlonzo.Code.Once.Target.X86.Syntax.C_rax_10)))
      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
-- Once.CCC.Target.X86v3.CodeGen.Compile.pair-setup
d_pair'45'setup_22 ::
  [MAlonzo.Code.Once.Target.X86.Syntax.T_Instr_58]
d_pair'45'setup_22
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe
         MAlonzo.Code.Once.Target.X86.Syntax.C_push_82
         (coe
            MAlonzo.Code.Once.Target.X86.Syntax.C_reg_52
            (coe MAlonzo.Code.Once.Target.X86.Syntax.C_r14_38)))
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe
            MAlonzo.Code.Once.Target.X86.Syntax.C_push_82
            (coe
               MAlonzo.Code.Once.Target.X86.Syntax.C_reg_52
               (coe MAlonzo.Code.Once.Target.X86.Syntax.C_r15_40)))
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe
               MAlonzo.Code.Once.Target.X86.Syntax.C_push_82
               (coe
                  MAlonzo.Code.Once.Target.X86.Syntax.C_reg_52
                  (coe MAlonzo.Code.Once.Target.X86.Syntax.C_rbp_22)))
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe
                  MAlonzo.Code.Once.Target.X86.Syntax.C_mov_60
                  (coe
                     MAlonzo.Code.Once.Target.X86.Syntax.C_reg_52
                     (coe MAlonzo.Code.Once.Target.X86.Syntax.C_rbp_22))
                  (coe
                     MAlonzo.Code.Once.Target.X86.Syntax.C_reg_52
                     (coe MAlonzo.Code.Once.Target.X86.Syntax.C_rsp_24)))
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe
                     MAlonzo.Code.Once.Target.X86.Syntax.C_sub_66
                     (coe
                        MAlonzo.Code.Once.Target.X86.Syntax.C_reg_52
                        (coe MAlonzo.Code.Once.Target.X86.Syntax.C_rsp_24))
                     (coe
                        MAlonzo.Code.Once.Target.X86.Syntax.C_imm_56
                        (coe
                           MAlonzo.Code.Once.Target.X86.Syntax.d_slots_108
                           (coe (2 :: Integer)))))
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.Target.X86.Syntax.C_mov_60
                        (coe
                           MAlonzo.Code.Once.Target.X86.Syntax.C_reg_52
                           (coe MAlonzo.Code.Once.Target.X86.Syntax.C_r15_40))
                        (coe
                           MAlonzo.Code.Once.Target.X86.Syntax.C_reg_52
                           (coe MAlonzo.Code.Once.Target.X86.Syntax.C_rsp_24)))
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.Target.X86.Syntax.C_mov_60
                           (coe
                              MAlonzo.Code.Once.Target.X86.Syntax.C_reg_52
                              (coe MAlonzo.Code.Once.Target.X86.Syntax.C_r14_38))
                           (coe
                              MAlonzo.Code.Once.Target.X86.Syntax.C_reg_52
                              (coe MAlonzo.Code.Once.Target.X86.Syntax.C_rdi_20)))
                        (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))
-- Once.CCC.Target.X86v3.CodeGen.Compile.pair-middle
d_pair'45'middle_24 ::
  [MAlonzo.Code.Once.Target.X86.Syntax.T_Instr_58]
d_pair'45'middle_24
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe
         MAlonzo.Code.Once.Target.X86.Syntax.C_mov_60
         (coe
            MAlonzo.Code.Once.Target.X86.Syntax.C_mem_54
            (coe
               MAlonzo.Code.Once.Target.X86.Syntax.C_base_44
               (coe MAlonzo.Code.Once.Target.X86.Syntax.C_r15_40)))
         (coe
            MAlonzo.Code.Once.Target.X86.Syntax.C_reg_52
            (coe MAlonzo.Code.Once.Target.X86.Syntax.C_rax_10)))
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe
            MAlonzo.Code.Once.Target.X86.Syntax.C_mov_60
            (coe
               MAlonzo.Code.Once.Target.X86.Syntax.C_reg_52
               (coe MAlonzo.Code.Once.Target.X86.Syntax.C_rdi_20))
            (coe
               MAlonzo.Code.Once.Target.X86.Syntax.C_reg_52
               (coe MAlonzo.Code.Once.Target.X86.Syntax.C_r14_38)))
         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
-- Once.CCC.Target.X86v3.CodeGen.Compile.pair-cleanup
d_pair'45'cleanup_26 ::
  [MAlonzo.Code.Once.Target.X86.Syntax.T_Instr_58]
d_pair'45'cleanup_26
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe
         MAlonzo.Code.Once.Target.X86.Syntax.C_mov_60
         (coe
            MAlonzo.Code.Once.Target.X86.Syntax.C_mem_54
            (coe
               MAlonzo.Code.Once.Target.X86.Syntax.C_base'43'disp_46
               (coe MAlonzo.Code.Once.Target.X86.Syntax.C_r15_40)
               (coe MAlonzo.Code.Once.Target.X86.Syntax.d_slot'45'size_106)))
         (coe
            MAlonzo.Code.Once.Target.X86.Syntax.C_reg_52
            (coe MAlonzo.Code.Once.Target.X86.Syntax.C_rax_10)))
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe
            MAlonzo.Code.Once.Target.X86.Syntax.C_mov_60
            (coe
               MAlonzo.Code.Once.Target.X86.Syntax.C_reg_52
               (coe MAlonzo.Code.Once.Target.X86.Syntax.C_rax_10))
            (coe
               MAlonzo.Code.Once.Target.X86.Syntax.C_reg_52
               (coe MAlonzo.Code.Once.Target.X86.Syntax.C_r15_40)))
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe
               MAlonzo.Code.Once.Target.X86.Syntax.C_mov_60
               (coe
                  MAlonzo.Code.Once.Target.X86.Syntax.C_reg_52
                  (coe MAlonzo.Code.Once.Target.X86.Syntax.C_rsp_24))
               (coe
                  MAlonzo.Code.Once.Target.X86.Syntax.C_reg_52
                  (coe MAlonzo.Code.Once.Target.X86.Syntax.C_rbp_22)))
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe
                  MAlonzo.Code.Once.Target.X86.Syntax.C_pop_84
                  (coe MAlonzo.Code.Once.Target.X86.Syntax.C_rbp_22))
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe
                     MAlonzo.Code.Once.Target.X86.Syntax.C_pop_84
                     (coe MAlonzo.Code.Once.Target.X86.Syntax.C_r15_40))
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.Target.X86.Syntax.C_pop_84
                        (coe MAlonzo.Code.Once.Target.X86.Syntax.C_r14_38))
                     (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))))
-- Once.CCC.Target.X86v3.CodeGen.Compile.curry-closure-setup
d_curry'45'closure'45'setup_28 ::
  Integer -> [MAlonzo.Code.Once.Target.X86.Syntax.T_Instr_58]
d_curry'45'closure'45'setup_28 v0
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe
         MAlonzo.Code.Once.Target.X86.Syntax.C_sub_66
         (coe
            MAlonzo.Code.Once.Target.X86.Syntax.C_reg_52
            (coe MAlonzo.Code.Once.Target.X86.Syntax.C_rsp_24))
         (coe
            MAlonzo.Code.Once.Target.X86.Syntax.C_imm_56
            (coe
               MAlonzo.Code.Once.Target.X86.Syntax.d_slots_108
               (coe (2 :: Integer)))))
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe
            MAlonzo.Code.Once.Target.X86.Syntax.C_mov_60
            (coe
               MAlonzo.Code.Once.Target.X86.Syntax.C_mem_54
               (coe
                  MAlonzo.Code.Once.Target.X86.Syntax.C_base_44
                  (coe MAlonzo.Code.Once.Target.X86.Syntax.C_rsp_24)))
            (coe
               MAlonzo.Code.Once.Target.X86.Syntax.C_reg_52
               (coe MAlonzo.Code.Once.Target.X86.Syntax.C_rdi_20)))
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe
               MAlonzo.Code.Once.Target.X86.Syntax.C_lea_62
               (coe MAlonzo.Code.Once.Target.X86.Syntax.C_r9_28)
               (coe
                  MAlonzo.Code.Once.Target.X86.Syntax.C_rip'43'disp_48
                  (coe (4 :: Integer))))
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe
                  MAlonzo.Code.Once.Target.X86.Syntax.C_mov_60
                  (coe
                     MAlonzo.Code.Once.Target.X86.Syntax.C_mem_54
                     (coe
                        MAlonzo.Code.Once.Target.X86.Syntax.C_base'43'disp_46
                        (coe MAlonzo.Code.Once.Target.X86.Syntax.C_rsp_24)
                        (coe MAlonzo.Code.Once.Target.X86.Syntax.d_slot'45'size_106)))
                  (coe
                     MAlonzo.Code.Once.Target.X86.Syntax.C_reg_52
                     (coe MAlonzo.Code.Once.Target.X86.Syntax.C_r9_28)))
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe
                     MAlonzo.Code.Once.Target.X86.Syntax.C_mov_60
                     (coe
                        MAlonzo.Code.Once.Target.X86.Syntax.C_reg_52
                        (coe MAlonzo.Code.Once.Target.X86.Syntax.C_rax_10))
                     (coe
                        MAlonzo.Code.Once.Target.X86.Syntax.C_reg_52
                        (coe MAlonzo.Code.Once.Target.X86.Syntax.C_rsp_24)))
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.Target.X86.Syntax.C_jmp_72
                        (coe addInt (coe (12 :: Integer)) (coe v0)))
                     (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))))
-- Once.CCC.Target.X86v3.CodeGen.Compile.curry-thunk-setup
d_curry'45'thunk'45'setup_32 ::
  [MAlonzo.Code.Once.Target.X86.Syntax.T_Instr_58]
d_curry'45'thunk'45'setup_32
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe
         MAlonzo.Code.Once.Target.X86.Syntax.C_label_90
         (coe (6 :: Integer)))
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe
            MAlonzo.Code.Once.Target.X86.Syntax.C_push_82
            (coe
               MAlonzo.Code.Once.Target.X86.Syntax.C_reg_52
               (coe MAlonzo.Code.Once.Target.X86.Syntax.C_r15_40)))
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe
               MAlonzo.Code.Once.Target.X86.Syntax.C_push_82
               (coe
                  MAlonzo.Code.Once.Target.X86.Syntax.C_reg_52
                  (coe MAlonzo.Code.Once.Target.X86.Syntax.C_rbp_22)))
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe
                  MAlonzo.Code.Once.Target.X86.Syntax.C_mov_60
                  (coe
                     MAlonzo.Code.Once.Target.X86.Syntax.C_reg_52
                     (coe MAlonzo.Code.Once.Target.X86.Syntax.C_rbp_22))
                  (coe
                     MAlonzo.Code.Once.Target.X86.Syntax.C_reg_52
                     (coe MAlonzo.Code.Once.Target.X86.Syntax.C_rsp_24)))
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe
                     MAlonzo.Code.Once.Target.X86.Syntax.C_sub_66
                     (coe
                        MAlonzo.Code.Once.Target.X86.Syntax.C_reg_52
                        (coe MAlonzo.Code.Once.Target.X86.Syntax.C_rsp_24))
                     (coe
                        MAlonzo.Code.Once.Target.X86.Syntax.C_imm_56
                        (coe
                           MAlonzo.Code.Once.Target.X86.Syntax.d_slots_108
                           (coe (2 :: Integer)))))
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.Target.X86.Syntax.C_mov_60
                        (coe
                           MAlonzo.Code.Once.Target.X86.Syntax.C_mem_54
                           (coe
                              MAlonzo.Code.Once.Target.X86.Syntax.C_base_44
                              (coe MAlonzo.Code.Once.Target.X86.Syntax.C_rsp_24)))
                        (coe
                           MAlonzo.Code.Once.Target.X86.Syntax.C_reg_52
                           (coe MAlonzo.Code.Once.Target.X86.Syntax.C_r12_34)))
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.Target.X86.Syntax.C_mov_60
                           (coe
                              MAlonzo.Code.Once.Target.X86.Syntax.C_mem_54
                              (coe
                                 MAlonzo.Code.Once.Target.X86.Syntax.C_base'43'disp_46
                                 (coe MAlonzo.Code.Once.Target.X86.Syntax.C_rsp_24)
                                 (coe MAlonzo.Code.Once.Target.X86.Syntax.d_slot'45'size_106)))
                           (coe
                              MAlonzo.Code.Once.Target.X86.Syntax.C_reg_52
                              (coe MAlonzo.Code.Once.Target.X86.Syntax.C_rdi_20)))
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.Target.X86.Syntax.C_mov_60
                              (coe
                                 MAlonzo.Code.Once.Target.X86.Syntax.C_reg_52
                                 (coe MAlonzo.Code.Once.Target.X86.Syntax.C_rdi_20))
                              (coe
                                 MAlonzo.Code.Once.Target.X86.Syntax.C_reg_52
                                 (coe MAlonzo.Code.Once.Target.X86.Syntax.C_rsp_24)))
                           (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))))))
-- Once.CCC.Target.X86v3.CodeGen.Compile.curry-thunk-cleanup
d_curry'45'thunk'45'cleanup_34 ::
  Integer -> [MAlonzo.Code.Once.Target.X86.Syntax.T_Instr_58]
d_curry'45'thunk'45'cleanup_34 v0
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe
         MAlonzo.Code.Once.Target.X86.Syntax.C_mov_60
         (coe
            MAlonzo.Code.Once.Target.X86.Syntax.C_reg_52
            (coe MAlonzo.Code.Once.Target.X86.Syntax.C_rsp_24))
         (coe
            MAlonzo.Code.Once.Target.X86.Syntax.C_reg_52
            (coe MAlonzo.Code.Once.Target.X86.Syntax.C_rbp_22)))
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe
            MAlonzo.Code.Once.Target.X86.Syntax.C_pop_84
            (coe MAlonzo.Code.Once.Target.X86.Syntax.C_rbp_22))
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe
               MAlonzo.Code.Once.Target.X86.Syntax.C_pop_84
               (coe MAlonzo.Code.Once.Target.X86.Syntax.C_r15_40))
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe MAlonzo.Code.Once.Target.X86.Syntax.C_ret_80)
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe
                     MAlonzo.Code.Once.Target.X86.Syntax.C_label_90
                     (coe addInt (coe (18 :: Integer)) (coe v0)))
                  (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))
-- Once.CCC.Target.X86v3.CodeGen.Compile.apply-instrs
d_apply'45'instrs_38 ::
  [MAlonzo.Code.Once.Target.X86.Syntax.T_Instr_58]
d_apply'45'instrs_38
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe
         MAlonzo.Code.Once.Target.X86.Syntax.C_push_82
         (coe
            MAlonzo.Code.Once.Target.X86.Syntax.C_reg_52
            (coe MAlonzo.Code.Once.Target.X86.Syntax.C_r15_40)))
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe
            MAlonzo.Code.Once.Target.X86.Syntax.C_mov_60
            (coe
               MAlonzo.Code.Once.Target.X86.Syntax.C_reg_52
               (coe MAlonzo.Code.Once.Target.X86.Syntax.C_r15_40))
            (coe
               MAlonzo.Code.Once.Target.X86.Syntax.C_mem_54
               (coe
                  MAlonzo.Code.Once.Target.X86.Syntax.C_base_44
                  (coe MAlonzo.Code.Once.Target.X86.Syntax.C_rdi_20))))
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe
               MAlonzo.Code.Once.Target.X86.Syntax.C_mov_60
               (coe
                  MAlonzo.Code.Once.Target.X86.Syntax.C_reg_52
                  (coe MAlonzo.Code.Once.Target.X86.Syntax.C_rsi_18))
               (coe
                  MAlonzo.Code.Once.Target.X86.Syntax.C_mem_54
                  (coe
                     MAlonzo.Code.Once.Target.X86.Syntax.C_base'43'disp_46
                     (coe MAlonzo.Code.Once.Target.X86.Syntax.C_rdi_20)
                     (coe MAlonzo.Code.Once.Target.X86.Syntax.d_slot'45'size_106))))
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe
                  MAlonzo.Code.Once.Target.X86.Syntax.C_mov_60
                  (coe
                     MAlonzo.Code.Once.Target.X86.Syntax.C_reg_52
                     (coe MAlonzo.Code.Once.Target.X86.Syntax.C_r12_34))
                  (coe
                     MAlonzo.Code.Once.Target.X86.Syntax.C_mem_54
                     (coe
                        MAlonzo.Code.Once.Target.X86.Syntax.C_base_44
                        (coe MAlonzo.Code.Once.Target.X86.Syntax.C_r15_40))))
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe
                     MAlonzo.Code.Once.Target.X86.Syntax.C_mov_60
                     (coe
                        MAlonzo.Code.Once.Target.X86.Syntax.C_reg_52
                        (coe MAlonzo.Code.Once.Target.X86.Syntax.C_r15_40))
                     (coe
                        MAlonzo.Code.Once.Target.X86.Syntax.C_mem_54
                        (coe
                           MAlonzo.Code.Once.Target.X86.Syntax.C_base'43'disp_46
                           (coe MAlonzo.Code.Once.Target.X86.Syntax.C_r15_40)
                           (coe MAlonzo.Code.Once.Target.X86.Syntax.d_slot'45'size_106))))
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.Target.X86.Syntax.C_mov_60
                        (coe
                           MAlonzo.Code.Once.Target.X86.Syntax.C_reg_52
                           (coe MAlonzo.Code.Once.Target.X86.Syntax.C_rdi_20))
                        (coe
                           MAlonzo.Code.Once.Target.X86.Syntax.C_reg_52
                           (coe MAlonzo.Code.Once.Target.X86.Syntax.C_rsi_18)))
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.Target.X86.Syntax.C_call_78
                           (coe
                              MAlonzo.Code.Once.Target.X86.Syntax.C_reg_52
                              (coe MAlonzo.Code.Once.Target.X86.Syntax.C_r15_40)))
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.Target.X86.Syntax.C_pop_84
                              (coe MAlonzo.Code.Once.Target.X86.Syntax.C_r15_40))
                           (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))))))
-- Once.CCC.Target.X86v3.CodeGen.Compile.compile-length
d_compile'45'length_44 ::
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_12 -> Integer
d_compile'45'length_44 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.CCC.IR.C_id_16
        -> coe MAlonzo.Code.Data.List.Base.du_length_268 d_id'45'instrs_12
      MAlonzo.Code.Once.CCC.IR.C__'8728'__24 v4 v6 v7
        -> coe
             addInt
             (coe
                addInt
                (coe
                   MAlonzo.Code.Data.List.Base.du_length_268 d_compose'45'bridge_20)
                (coe d_compile'45'length_44 (coe v0) (coe v4) (coe v7)))
             (coe d_compile'45'length_44 (coe v4) (coe v1) (coe v6))
      MAlonzo.Code.Once.CCC.IR.C_'10216'_'44'_'10217'__32 v6 v7 v8
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'42'__38 v9 v10
               -> coe
                    addInt
                    (coe
                       addInt
                       (coe
                          addInt
                          (coe
                             addInt
                             (coe
                                MAlonzo.Code.Data.List.Base.du_length_268 d_pair'45'cleanup_26)
                             (coe
                                MAlonzo.Code.Data.List.Base.du_length_268 d_pair'45'middle_24))
                          (coe MAlonzo.Code.Data.List.Base.du_length_268 d_pair'45'setup_22))
                       (coe d_compile'45'length_44 (coe v0) (coe v9) (coe v6)))
                    (coe d_compile'45'length_44 (coe v0) (coe v10) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_fst'45'ir_38
        -> coe MAlonzo.Code.Data.List.Base.du_length_268 d_fst'45'instrs_14
      MAlonzo.Code.Once.CCC.IR.C_snd'45'ir_44
        -> coe MAlonzo.Code.Data.List.Base.du_length_268 d_snd'45'instrs_16
      MAlonzo.Code.Once.CCC.IR.C_inl'45'ir_50 v5 -> coe (1 :: Integer)
      MAlonzo.Code.Once.CCC.IR.C_inr'45'ir_56 v5 -> coe (1 :: Integer)
      MAlonzo.Code.Once.CCC.IR.C_case'45'ir_64 v6 v7
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'43'__40 v8 v9
               -> coe
                    addInt (coe d_compile'45'length_44 (coe v8) (coe v1) (coe v6))
                    (coe d_compile'45'length_44 (coe v9) (coe v1) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_terminal_68
        -> coe
             MAlonzo.Code.Data.List.Base.du_length_268 d_terminal'45'instrs_18
      MAlonzo.Code.Once.CCC.IR.C_initial_72 -> coe (1 :: Integer)
      MAlonzo.Code.Once.CCC.IR.C_curry_82 v7 v8
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__42 v9 v10 v11
               -> coe
                    addInt
                    (coe
                       addInt (coe (11 :: Integer))
                       (coe
                          MAlonzo.Code.Data.List.Base.du_length_268
                          d_curry'45'thunk'45'setup_32))
                    (coe
                       d_compile'45'length_44
                       (coe MAlonzo.Code.Once.Type.C__'42'__38 (coe v0) (coe v9))
                       (coe v11) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_apply_90
        -> coe
             MAlonzo.Code.Data.List.Base.du_length_268 d_apply'45'instrs_38
      MAlonzo.Code.Once.CCC.IR.C_arr_98
        -> coe MAlonzo.Code.Data.List.Base.du_length_268 d_id'45'instrs_12
      MAlonzo.Code.Once.CCC.IR.C_fold'45'ir_102 v4 -> coe (1 :: Integer)
      MAlonzo.Code.Once.CCC.IR.C_unfold'45'ir_106 -> coe (1 :: Integer)
      MAlonzo.Code.Once.CCC.IR.C_free'45'heap_108 v3
        -> coe (0 :: Integer)
      MAlonzo.Code.Once.CCC.IR.C_Prim_114 v5 -> coe (1 :: Integer)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86v3.CodeGen.Compile.compile-ir
d_compile'45'ir_64 ::
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_12 ->
  [MAlonzo.Code.Once.Target.X86.Syntax.T_Instr_58]
d_compile'45'ir_64 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.CCC.IR.C_id_16 -> coe d_id'45'instrs_12
      MAlonzo.Code.Once.CCC.IR.C__'8728'__24 v4 v6 v7
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe d_compile'45'ir_64 (coe v0) (coe v4) (coe v7))
             (coe
                MAlonzo.Code.Data.List.Base.du__'43''43'__32
                (coe d_compose'45'bridge_20)
                (coe d_compile'45'ir_64 (coe v4) (coe v1) (coe v6)))
      MAlonzo.Code.Once.CCC.IR.C_'10216'_'44'_'10217'__32 v6 v7 v8
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'42'__38 v9 v10
               -> coe
                    MAlonzo.Code.Data.List.Base.du__'43''43'__32
                    (coe d_pair'45'setup_22)
                    (coe
                       MAlonzo.Code.Data.List.Base.du__'43''43'__32
                       (coe d_compile'45'ir_64 (coe v0) (coe v9) (coe v6))
                       (coe
                          MAlonzo.Code.Data.List.Base.du__'43''43'__32
                          (coe d_pair'45'middle_24)
                          (coe
                             MAlonzo.Code.Data.List.Base.du__'43''43'__32
                             (coe d_compile'45'ir_64 (coe v0) (coe v10) (coe v7))
                             (coe d_pair'45'cleanup_26))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_fst'45'ir_38 -> coe d_fst'45'instrs_14
      MAlonzo.Code.Once.CCC.IR.C_snd'45'ir_44 -> coe d_snd'45'instrs_16
      MAlonzo.Code.Once.CCC.IR.C_inl'45'ir_50 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe MAlonzo.Code.Once.Target.X86.Syntax.C_ud2_88)
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.IR.C_inr'45'ir_56 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe MAlonzo.Code.Once.Target.X86.Syntax.C_ud2_88)
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.IR.C_case'45'ir_64 v6 v7
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'43'__40 v8 v9
               -> coe
                    MAlonzo.Code.Data.List.Base.du__'43''43'__32
                    (coe d_compile'45'ir_64 (coe v8) (coe v1) (coe v6))
                    (coe d_compile'45'ir_64 (coe v9) (coe v1) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_terminal_68
        -> coe d_terminal'45'instrs_18
      MAlonzo.Code.Once.CCC.IR.C_initial_72
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe MAlonzo.Code.Once.Target.X86.Syntax.C_ud2_88)
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.IR.C_curry_82 v7 v8
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__42 v9 v10 v11
               -> coe
                    MAlonzo.Code.Data.List.Base.du__'43''43'__32
                    (coe
                       d_curry'45'closure'45'setup_28
                       (coe
                          d_compile'45'length_44
                          (coe MAlonzo.Code.Once.Type.C__'42'__38 (coe v0) (coe v9))
                          (coe v11) (coe v7)))
                    (coe
                       MAlonzo.Code.Data.List.Base.du__'43''43'__32
                       (coe d_curry'45'thunk'45'setup_32)
                       (coe
                          MAlonzo.Code.Data.List.Base.du__'43''43'__32
                          (coe
                             d_compile'45'ir_64
                             (coe MAlonzo.Code.Once.Type.C__'42'__38 (coe v0) (coe v9))
                             (coe v11) (coe v7))
                          (coe
                             d_curry'45'thunk'45'cleanup_34
                             (coe
                                d_compile'45'length_44
                                (coe MAlonzo.Code.Once.Type.C__'42'__38 (coe v0) (coe v9))
                                (coe v11) (coe v7)))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_apply_90 -> coe d_apply'45'instrs_38
      MAlonzo.Code.Once.CCC.IR.C_arr_98 -> coe d_id'45'instrs_12
      MAlonzo.Code.Once.CCC.IR.C_fold'45'ir_102 v4
        -> coe d_id'45'instrs_12
      MAlonzo.Code.Once.CCC.IR.C_unfold'45'ir_106
        -> coe d_id'45'instrs_12
      MAlonzo.Code.Once.CCC.IR.C_free'45'heap_108 v3
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      MAlonzo.Code.Once.CCC.IR.C_Prim_114 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe MAlonzo.Code.Once.Target.X86.Syntax.C_ud2_88)
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      _ -> MAlonzo.RTE.mazUnreachableError
