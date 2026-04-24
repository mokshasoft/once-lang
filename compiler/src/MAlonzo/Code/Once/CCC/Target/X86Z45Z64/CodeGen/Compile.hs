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
import qualified MAlonzo.Code.Agda.Builtin.Char
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.Nat.Properties
import qualified MAlonzo.Code.Data.Nat.Show
import qualified MAlonzo.Code.Data.String.Properties
import qualified MAlonzo.Code.Once.CCC.IR
import qualified MAlonzo.Code.Once.CCC.SigOp.Info
import qualified MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Once.CCC.Target.X86-64.CodeGen.Compile.id-instrs
d_id'45'instrs_12 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_60]
d_id'45'instrs_12
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mov_62
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_54
            (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rax_12))
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_54
            (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rdi_22)))
      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
-- Once.CCC.Target.X86-64.CodeGen.Compile.fst-instrs
d_fst'45'instrs_14 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_60]
d_fst'45'instrs_14
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mov_62
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_54
            (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rax_12))
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mem_56
            (coe
               MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_base_46
               (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rdi_22))))
      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
-- Once.CCC.Target.X86-64.CodeGen.Compile.snd-instrs
d_snd'45'instrs_16 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_60]
d_snd'45'instrs_16
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mov_62
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_54
            (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rax_12))
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mem_56
            (coe
               MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_base'43'disp_48
               (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rdi_22)
               (coe
                  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.d_slot'45'size_110))))
      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
-- Once.CCC.Target.X86-64.CodeGen.Compile.terminal-instrs
d_terminal'45'instrs_18 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_60]
d_terminal'45'instrs_18
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mov_62
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_54
            (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rax_12))
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_imm_58
            (coe (0 :: Integer))))
      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
-- Once.CCC.Target.X86-64.CodeGen.Compile.compose-bridge
d_compose'45'bridge_20 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_60]
d_compose'45'bridge_20
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mov_62
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_54
            (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rdi_22))
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_54
            (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rax_12)))
      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
-- Once.CCC.Target.X86-64.CodeGen.Compile.pair-setup
d_pair'45'setup_22 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_60]
d_pair'45'setup_22
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_sub_68
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_54
            (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rsp_26))
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_imm_58
            (coe
               MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.d_slots_112
               (coe (3 :: Integer)))))
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mov_62
            (coe
               MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mem_56
               (coe
                  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_base'43'disp_48
                  (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rsp_26)
                  (coe
                     MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.d_slots_112
                     (coe (2 :: Integer)))))
            (coe
               MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_54
               (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rdi_22)))
         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
-- Once.CCC.Target.X86-64.CodeGen.Compile.pair-middle
d_pair'45'middle_24 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_60]
d_pair'45'middle_24
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mov_62
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mem_56
            (coe
               MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_base_46
               (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rsp_26)))
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_54
            (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rax_12)))
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mov_62
            (coe
               MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_54
               (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rdi_22))
            (coe
               MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mem_56
               (coe
                  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_base'43'disp_48
                  (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rsp_26)
                  (coe
                     MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.d_slots_112
                     (coe (2 :: Integer))))))
         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
-- Once.CCC.Target.X86-64.CodeGen.Compile.pair-cleanup
d_pair'45'cleanup_26 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_60]
d_pair'45'cleanup_26
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mov_62
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mem_56
            (coe
               MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_base'43'disp_48
               (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rsp_26)
               (coe
                  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.d_slot'45'size_110)))
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_54
            (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rax_12)))
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mov_62
            (coe
               MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_54
               (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rax_12))
            (coe
               MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_54
               (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rsp_26)))
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe
               MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_add_66
               (coe
                  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_54
                  (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rsp_26))
               (coe
                  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_imm_58
                  (coe
                     MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.d_slots_112
                     (coe (3 :: Integer)))))
            (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
-- Once.CCC.Target.X86-64.CodeGen.Compile.curry-closure-setup
d_curry'45'closure'45'setup_28 ::
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_60]
d_curry'45'closure'45'setup_28 v0 ~v1
  = du_curry'45'closure'45'setup_28 v0
du_curry'45'closure'45'setup_28 ::
  Integer ->
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_60]
du_curry'45'closure'45'setup_28 v0
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_sub_68
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_54
            (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rsp_26))
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_imm_58
            (coe
               MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.d_slots_112
               (coe (2 :: Integer)))))
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mov_62
            (coe
               MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mem_56
               (coe
                  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_base_46
                  (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rsp_26)))
            (coe
               MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_54
               (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rdi_22)))
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe
               MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_lea_64
               (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_r9_30)
               (coe
                  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rip'43'disp_50
                  (coe (10 :: Integer))))
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe
                  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mov_62
                  (coe
                     MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mem_56
                     (coe
                        MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_base'43'disp_48
                        (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rsp_26)
                        (coe
                           MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.d_slot'45'size_110)))
                  (coe
                     MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_54
                     (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_r9_30)))
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe
                     MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mov_62
                     (coe
                        MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_54
                        (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rax_12))
                     (coe
                        MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_54
                        (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rsp_26)))
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_jmp_74
                        (coe addInt (coe (1 :: Integer)) (coe v0)))
                     (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))))
-- Once.CCC.Target.X86-64.CodeGen.Compile.curry-thunk-setup'
d_curry'45'thunk'45'setup''_34 ::
  Integer ->
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_60]
d_curry'45'thunk'45'setup''_34 v0
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_label_94 (coe v0))
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_push_84
            (coe
               MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_54
               (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_r15_42)))
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe
               MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_push_84
               (coe
                  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_54
                  (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rbp_24)))
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe
                  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mov_62
                  (coe
                     MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_54
                     (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rbp_24))
                  (coe
                     MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_54
                     (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rsp_26)))
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe
                     MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_sub_68
                     (coe
                        MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_54
                        (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rsp_26))
                     (coe
                        MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_imm_58
                        (coe
                           MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.d_slots_112
                           (coe (2 :: Integer)))))
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mov_62
                        (coe
                           MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mem_56
                           (coe
                              MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_base_46
                              (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rsp_26)))
                        (coe
                           MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_54
                           (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_r12_36)))
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mov_62
                           (coe
                              MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mem_56
                              (coe
                                 MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_base'43'disp_48
                                 (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rsp_26)
                                 (coe
                                    MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.d_slot'45'size_110)))
                           (coe
                              MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_54
                              (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rdi_22)))
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mov_62
                              (coe
                                 MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_54
                                 (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rdi_22))
                              (coe
                                 MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_54
                                 (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rsp_26)))
                           (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))))))
-- Once.CCC.Target.X86-64.CodeGen.Compile.curry-thunk-cleanup'
d_curry'45'thunk'45'cleanup''_38 ::
  Integer ->
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_60]
d_curry'45'thunk'45'cleanup''_38 v0
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mov_62
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_54
            (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rsp_26))
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_54
            (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rbp_24)))
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_pop_86
            (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rbp_24))
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe
               MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_pop_86
               (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_r15_42))
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_ret_82)
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe
                     MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_label_94
                     (coe addInt (coe (1 :: Integer)) (coe v0)))
                  (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))
-- Once.CCC.Target.X86-64.CodeGen.Compile.curry-thunk-setup
d_curry'45'thunk'45'setup_42 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_60]
d_curry'45'thunk'45'setup_42
  = coe d_curry'45'thunk'45'setup''_34 (coe (0 :: Integer))
-- Once.CCC.Target.X86-64.CodeGen.Compile.curry-thunk-cleanup
d_curry'45'thunk'45'cleanup_44 ::
  Integer ->
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_60]
d_curry'45'thunk'45'cleanup_44 ~v0
  = du_curry'45'thunk'45'cleanup_44
du_curry'45'thunk'45'cleanup_44 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_60]
du_curry'45'thunk'45'cleanup_44
  = coe d_curry'45'thunk'45'cleanup''_38 (coe (0 :: Integer))
-- Once.CCC.Target.X86-64.CodeGen.Compile.apply-instrs
d_apply'45'instrs_46 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_60]
d_apply'45'instrs_46
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_push_84
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_54
            (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_r15_42)))
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mov_62
            (coe
               MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_54
               (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_r15_42))
            (coe
               MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mem_56
               (coe
                  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_base_46
                  (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rdi_22))))
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe
               MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mov_62
               (coe
                  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_54
                  (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rsi_20))
               (coe
                  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mem_56
                  (coe
                     MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_base'43'disp_48
                     (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rdi_22)
                     (coe
                        MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.d_slot'45'size_110))))
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe
                  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mov_62
                  (coe
                     MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_54
                     (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_r12_36))
                  (coe
                     MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mem_56
                     (coe
                        MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_base_46
                        (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_r15_42))))
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe
                     MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mov_62
                     (coe
                        MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_54
                        (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_r15_42))
                     (coe
                        MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mem_56
                        (coe
                           MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_base'43'disp_48
                           (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_r15_42)
                           (coe
                              MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.d_slot'45'size_110))))
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mov_62
                        (coe
                           MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_54
                           (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rdi_22))
                        (coe
                           MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_54
                           (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rsi_20)))
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_call_80
                           (coe
                              MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_54
                              (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_r15_42)))
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_pop_86
                              (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_r15_42))
                           (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))))))
-- Once.CCC.Target.X86-64.CodeGen.Compile.strip-chars
d_strip'45'chars_48 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  Maybe [MAlonzo.Code.Agda.Builtin.Char.T_Char_6]
d_strip'45'chars_48 v0 v1
  = case coe v0 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v1)
      (:) v2 v3
        -> case coe v1 of
             [] -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             (:) v4 v5
               -> let v6
                        = coe
                            MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                            erased erased
                            (coe
                               MAlonzo.Code.Data.Nat.Properties.d__'8799'__2796
                               (coe MAlonzo.Code.Agda.Builtin.Char.d_primCharToNat_28 v2)
                               (coe MAlonzo.Code.Agda.Builtin.Char.d_primCharToNat_28 v4)) in
                  coe
                    (case coe v6 of
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v7 v8
                         -> if coe v7
                              then coe seq (coe v8) (coe d_strip'45'chars_48 (coe v3) (coe v5))
                              else coe
                                     seq (coe v8) (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-64.CodeGen.Compile.lit-int-prefix
d_lit'45'int'45'prefix_80 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6]
d_lit'45'int'45'prefix_80
  = coe
      MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
      ("lit.int." :: Data.Text.Text)
-- Once.CCC.Target.X86-64.CodeGen.Compile.parse-lit-int
d_parse'45'lit'45'int_82 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe Integer
d_parse'45'lit'45'int_82 v0
  = let v1
          = d_strip'45'chars_48
              (coe
                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe 'l')
                 (coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe 'i')
                    (coe
                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe 't')
                       (coe
                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe '.')
                          (coe
                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe 'i')
                             (coe
                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe 'n')
                                (coe
                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe 't')
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe '.')
                                      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))
              (coe MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12 v0) in
    coe
      (case coe v1 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
           -> coe
                MAlonzo.Code.Data.Nat.Show.du_readMaybe_10 (coe (10 :: Integer))
                (coe MAlonzo.Code.Agda.Builtin.String.d_primStringFromList_14 v2)
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v1
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.CCC.Target.X86-64.CodeGen.Compile.exit-instrs
d_exit'45'instrs_96 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_60]
d_exit'45'instrs_96
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mov_62
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_54
            (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rax_12))
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_imm_58
            (coe (60 :: Integer))))
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_syscall_92)
         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
-- Once.CCC.Target.X86-64.CodeGen.Compile.compile-sigOp
d_compile'45'sigOp_98 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_60]
d_compile'45'sigOp_98 v0
  = let v1
          = coe
              MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
              erased
              (\ v1 ->
                 coe
                   MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                   (coe v0))
              (coe
                 MAlonzo.Code.Data.String.Properties.d__'8776''63'__28 (coe v0)
                 (coe ("exit" :: Data.Text.Text))) in
    coe
      (case coe v1 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v2 v3
           -> if coe v2
                then coe seq (coe v3) (coe d_exit'45'instrs_96)
                else coe
                       seq (coe v3)
                       (let v4
                              = d_strip'45'chars_48
                                  (coe
                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe 'l')
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe 'i')
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe 't')
                                           (coe
                                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe '.')
                                              (coe
                                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                 (coe 'i')
                                                 (coe
                                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                    (coe 'n')
                                                    (coe
                                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                       (coe 't')
                                                       (coe
                                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                          (coe '.')
                                                          (coe
                                                             MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))
                                  (coe MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12 v0) in
                        coe
                          (case coe v4 of
                             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
                               -> let v6
                                        = coe
                                            MAlonzo.Code.Data.Nat.Show.du_readMaybe_10
                                            (coe (10 :: Integer))
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.String.d_primStringFromList_14
                                               v5) in
                                  coe
                                    (case coe v6 of
                                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
                                         -> coe
                                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                              (coe
                                                 MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mov_62
                                                 (coe
                                                    MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_54
                                                    (coe
                                                       MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rax_12))
                                                 (coe
                                                    MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_imm_58
                                                    (coe v7)))
                                              (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                                       MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                         -> coe
                                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                              (coe
                                                 MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_ud2_90)
                                              (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                                       _ -> MAlonzo.RTE.mazUnreachableError)
                             MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                               -> case coe v4 of
                                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
                                      -> coe
                                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                           (coe
                                              MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mov_62
                                              (coe
                                                 MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_54
                                                 (coe
                                                    MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rax_12))
                                              (coe
                                                 MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_imm_58
                                                 (coe v5)))
                                           (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                                    MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                      -> coe
                                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                           (coe
                                              MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_ud2_90)
                                           (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                                    _ -> MAlonzo.RTE.mazUnreachableError
                             _ -> MAlonzo.RTE.mazUnreachableError))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.CCC.Target.X86-64.CodeGen.Compile.compile-sigOp-size
d_compile'45'sigOp'45'size_120 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Integer
d_compile'45'sigOp'45'size_120 v0
  = let v1
          = coe
              MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
              erased
              (\ v1 ->
                 coe
                   MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                   (coe v0))
              (coe
                 MAlonzo.Code.Data.String.Properties.d__'8776''63'__28 (coe v0)
                 (coe ("exit" :: Data.Text.Text))) in
    coe
      (case coe v1 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v2 v3
           -> if coe v2
                then coe seq (coe v3) (coe (2 :: Integer))
                else coe seq (coe v3) (coe (1 :: Integer))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.CCC.Target.X86-64.CodeGen.Compile.compile-sigOp-length
d_compile'45'sigOp'45'length_134 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_compile'45'sigOp'45'length_134 = erased
-- Once.CCC.Target.X86-64.CodeGen.Compile.compile-length
d_compile'45'length_158 ::
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_12 -> Integer
d_compile'45'length_158 v0 v1 v2
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
                (coe d_compile'45'length_158 (coe v0) (coe v4) (coe v7)))
             (coe d_compile'45'length_158 (coe v4) (coe v1) (coe v6))
      MAlonzo.Code.Once.CCC.IR.C_'10216'_'44'_'10217'_32 v6 v7 v8
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'42'__140 v9 v10
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
                       (coe d_compile'45'length_158 (coe v0) (coe v9) (coe v6)))
                    (coe d_compile'45'length_158 (coe v0) (coe v10) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_fst_38
        -> coe MAlonzo.Code.Data.List.Base.du_length_268 d_fst'45'instrs_14
      MAlonzo.Code.Once.CCC.IR.C_snd_44
        -> coe MAlonzo.Code.Data.List.Base.du_length_268 d_snd'45'instrs_16
      MAlonzo.Code.Once.CCC.IR.C_inl_50 v5 -> coe (1 :: Integer)
      MAlonzo.Code.Once.CCC.IR.C_inr_56 v5 -> coe (1 :: Integer)
      MAlonzo.Code.Once.CCC.IR.C_case_64 v6 v7
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'43'__142 v8 v9
               -> coe
                    addInt (coe d_compile'45'length_158 (coe v8) (coe v1) (coe v6))
                    (coe d_compile'45'length_158 (coe v9) (coe v1) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_terminal_68
        -> coe
             MAlonzo.Code.Data.List.Base.du_length_268 d_terminal'45'instrs_18
      MAlonzo.Code.Once.CCC.IR.C_initial_72 -> coe (1 :: Integer)
      MAlonzo.Code.Once.CCC.IR.C_curry_82 v7 v8
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__144 v9 v10 v11
               -> coe
                    addInt
                    (coe
                       addInt (coe (11 :: Integer))
                       (coe
                          MAlonzo.Code.Data.List.Base.du_length_268
                          d_curry'45'thunk'45'setup_42))
                    (coe
                       d_compile'45'length_158
                       (coe MAlonzo.Code.Once.Type.C__'42'__140 (coe v0) (coe v9))
                       (coe v11) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_apply_90
        -> coe
             MAlonzo.Code.Data.List.Base.du_length_268 d_apply'45'instrs_46
      MAlonzo.Code.Once.CCC.IR.C_arr_98
        -> coe MAlonzo.Code.Data.List.Base.du_length_268 d_id'45'instrs_12
      MAlonzo.Code.Once.CCC.IR.C_In_102 v4 v5 -> coe (1 :: Integer)
      MAlonzo.Code.Once.CCC.IR.C_out'45'μ_106 v4 -> coe (1 :: Integer)
      MAlonzo.Code.Once.CCC.IR.C_Cata_112 v4 v6 -> coe (1 :: Integer)
      MAlonzo.Code.Once.CCC.IR.C_Para_118 v4 v6 -> coe (1 :: Integer)
      MAlonzo.Code.Once.CCC.IR.C_Out_122 v4 -> coe (1 :: Integer)
      MAlonzo.Code.Once.CCC.IR.C_in'45'ν_126 v4 v5 -> coe (1 :: Integer)
      MAlonzo.Code.Once.CCC.IR.C_Ana_132 v4 v6 -> coe (1 :: Integer)
      MAlonzo.Code.Once.CCC.IR.C_Hylo_140 v3 v5 v6 v8 v9
        -> coe (1 :: Integer)
      MAlonzo.Code.Once.CCC.IR.C_Fuse_148 v3 v5 v6 v8 v9
        -> coe (1 :: Integer)
      MAlonzo.Code.Once.CCC.IR.C_free'45'heap_150 v3
        -> coe (0 :: Integer)
      MAlonzo.Code.Once.CCC.IR.C_SigOp_156 v5
        -> coe
             d_compile'45'sigOp'45'size_120
             (coe MAlonzo.Code.Once.CCC.SigOp.Info.d_name_276 (coe v5))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-64.CodeGen.Compile.compile-ir'
d_compile'45'ir''_180 ::
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  Integer ->
  MAlonzo.Code.Once.CCC.IR.T_IR_12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_compile'45'ir''_180 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Once.CCC.IR.C_id_16
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe d_id'45'instrs_12)
             (coe v2)
      MAlonzo.Code.Once.CCC.IR.C__'8728'__24 v5 v7 v8
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Data.List.Base.du__'43''43'__32
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                   (coe d_compile'45'ir''_180 (coe v0) (coe v5) (coe v2) (coe v8)))
                (coe
                   MAlonzo.Code.Data.List.Base.du__'43''43'__32
                   (coe d_compose'45'bridge_20)
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                      (coe
                         d_compile'45'ir''_180 (coe v5) (coe v1)
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                            (coe d_compile'45'ir''_180 (coe v0) (coe v5) (coe v2) (coe v8)))
                         (coe v7)))))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                (coe
                   d_compile'45'ir''_180 (coe v5) (coe v1)
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                      (coe d_compile'45'ir''_180 (coe v0) (coe v5) (coe v2) (coe v8)))
                   (coe v7)))
      MAlonzo.Code.Once.CCC.IR.C_'10216'_'44'_'10217'_32 v7 v8 v9
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'42'__140 v10 v11
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       MAlonzo.Code.Data.List.Base.du__'43''43'__32
                       (coe d_pair'45'setup_22)
                       (coe
                          MAlonzo.Code.Data.List.Base.du__'43''43'__32
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                             (coe d_compile'45'ir''_180 (coe v0) (coe v10) (coe v2) (coe v7)))
                          (coe
                             MAlonzo.Code.Data.List.Base.du__'43''43'__32
                             (coe d_pair'45'middle_24)
                             (coe
                                MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                   (coe
                                      d_compile'45'ir''_180 (coe v0) (coe v11)
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                         (coe
                                            d_compile'45'ir''_180 (coe v0) (coe v10) (coe v2)
                                            (coe v7)))
                                      (coe v8)))
                                (coe d_pair'45'cleanup_26)))))
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                       (coe
                          d_compile'45'ir''_180 (coe v0) (coe v11)
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                             (coe d_compile'45'ir''_180 (coe v0) (coe v10) (coe v2) (coe v7)))
                          (coe v8)))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_fst_38
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe d_fst'45'instrs_14) (coe v2)
      MAlonzo.Code.Once.CCC.IR.C_snd_44
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe d_snd'45'instrs_16) (coe v2)
      MAlonzo.Code.Once.CCC.IR.C_inl_50 v6
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_ud2_90)
                (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
             (coe v2)
      MAlonzo.Code.Once.CCC.IR.C_inr_56 v6
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_ud2_90)
                (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
             (coe v2)
      MAlonzo.Code.Once.CCC.IR.C_case_64 v7 v8
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'43'__142 v9 v10
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       MAlonzo.Code.Data.List.Base.du__'43''43'__32
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                          (coe d_compile'45'ir''_180 (coe v9) (coe v1) (coe v2) (coe v7)))
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                          (coe
                             d_compile'45'ir''_180 (coe v10) (coe v1)
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                (coe d_compile'45'ir''_180 (coe v9) (coe v1) (coe v2) (coe v7)))
                             (coe v8))))
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                       (coe
                          d_compile'45'ir''_180 (coe v10) (coe v1)
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                             (coe d_compile'45'ir''_180 (coe v9) (coe v1) (coe v2) (coe v7)))
                          (coe v8)))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_terminal_68
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe d_terminal'45'instrs_18) (coe v2)
      MAlonzo.Code.Once.CCC.IR.C_initial_72
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_ud2_90)
                (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
             (coe v2)
      MAlonzo.Code.Once.CCC.IR.C_curry_82 v8 v9
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__144 v10 v11 v12
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       MAlonzo.Code.Data.List.Base.du__'43''43'__32
                       (coe du_curry'45'closure'45'setup_28 (coe v2))
                       (coe
                          MAlonzo.Code.Data.List.Base.du__'43''43'__32
                          (coe d_curry'45'thunk'45'setup''_34 (coe v2))
                          (coe
                             MAlonzo.Code.Data.List.Base.du__'43''43'__32
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                (coe
                                   d_compile'45'ir''_180
                                   (coe MAlonzo.Code.Once.Type.C__'42'__140 (coe v0) (coe v10))
                                   (coe v12) (coe addInt (coe (2 :: Integer)) (coe v2)) (coe v8)))
                             (coe d_curry'45'thunk'45'cleanup''_38 (coe v2)))))
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                       (coe
                          d_compile'45'ir''_180
                          (coe MAlonzo.Code.Once.Type.C__'42'__140 (coe v0) (coe v10))
                          (coe v12) (coe addInt (coe (2 :: Integer)) (coe v2)) (coe v8)))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_apply_90
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe d_apply'45'instrs_46) (coe v2)
      MAlonzo.Code.Once.CCC.IR.C_arr_98
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe d_id'45'instrs_12)
             (coe v2)
      MAlonzo.Code.Once.CCC.IR.C_In_102 v5 v6
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe d_id'45'instrs_12)
             (coe v2)
      MAlonzo.Code.Once.CCC.IR.C_out'45'μ_106 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe d_id'45'instrs_12)
             (coe v2)
      MAlonzo.Code.Once.CCC.IR.C_Cata_112 v5 v7
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_ud2_90)
                (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
             (coe v2)
      MAlonzo.Code.Once.CCC.IR.C_Para_118 v5 v7
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_ud2_90)
                (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
             (coe v2)
      MAlonzo.Code.Once.CCC.IR.C_Out_122 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe d_id'45'instrs_12)
             (coe v2)
      MAlonzo.Code.Once.CCC.IR.C_in'45'ν_126 v5 v6
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe d_id'45'instrs_12)
             (coe v2)
      MAlonzo.Code.Once.CCC.IR.C_Ana_132 v5 v7
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_ud2_90)
                (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
             (coe v2)
      MAlonzo.Code.Once.CCC.IR.C_Hylo_140 v4 v6 v7 v9 v10
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_ud2_90)
                (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
             (coe v2)
      MAlonzo.Code.Once.CCC.IR.C_Fuse_148 v4 v6 v7 v9 v10
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_ud2_90)
                (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
             (coe v2)
      MAlonzo.Code.Once.CCC.IR.C_free'45'heap_150 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16) (coe v2)
      MAlonzo.Code.Once.CCC.IR.C_SigOp_156 v6
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                d_compile'45'sigOp_98
                (coe MAlonzo.Code.Once.CCC.SigOp.Info.d_name_276 (coe v6)))
             (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-64.CodeGen.Compile.compile-ir
d_compile'45'ir_280 ::
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_12 ->
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_60]
d_compile'45'ir_280 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe
         d_compile'45'ir''_180 (coe v0) (coe v1) (coe (0 :: Integer))
         (coe v2))
-- Once.CCC.Target.X86-64.CodeGen.Compile.compile-ir'-length
d_compile'45'ir'''45'length_292 ::
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  Integer ->
  MAlonzo.Code.Once.CCC.IR.T_IR_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_compile'45'ir'''45'length_292 = erased
-- Once.CCC.Target.X86-64.CodeGen.Compile.compile-ir-length
d_compile'45'ir'45'length_492 ::
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_compile'45'ir'45'length_492 = erased
